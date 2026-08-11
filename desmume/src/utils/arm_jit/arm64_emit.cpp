/*
	Copyright (C) 2022 Patrick Herlihy - https://byte4byte.com
	Copyright (C) 2022 DeSmuME team

	This file is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 2 of the License, or
	(at your option) any later version.

	This file is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with the this software.  If not, see <http://www.gnu.org/licenses/>.
*/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#if defined(_WIN32) && ! defined(__ANDROID__)
typedef uint32_t u_int;
#else
#include <sys/mman.h>
#endif

#define R11 11
#define R10 10
#define FP 11
#define LR 14
#define PC 15
#define SP 13
#define R0 0
#define R1 1
#define R2 2
#define R3 3
#define R4 4
#define R5 5
#define R6 6
#define R7 7
#define R8 8
#define R9 9

#define X0_REG      0
#define X1_REG      1
#define X2_REG      2
#define X3_REG      3
#define X4_REG      4
#define X5_REG      5
#define X6_REG      6
#define X7_REG      7
#define X8_REG      8
#define X9_REG      9
#define X10_REG     10
#define X11_REG     11
#define X12_REG     12
#define X13_REG     13
#define X14_REG     14
#define X15_REG     15 
#define X16_REG     16
#define X17_REG     17
#if (defined(_WIN32) || defined(__APPLE__) || defined(__ANDROID__))
#define X18_REG     23 // x18 is reserved on windows on arm, macos, and android, so we use x23 instead
#else
#define X18_REG     18
#endif
#define X19_REG     19
#define X20_REG     20
#define X21_REG     21
#define X22_REG     22
#define X23_REG     23
#define X24_REG     24
#define X25_REG     25
#define X26_REG     26
#define X27_REG     27
#define X28_REG     28
#define x29_REG     29
#define X30_REG     30
#define X31_REG     31

#define SHIFT_REG R0

#define WZR 31
#define XZR WZR

struct s_bytes;
typedef struct s_bytes t_bytes;

typedef unsigned int (*JittedFunc)();

static void output_w32(t_bytes *bytes, unsigned int word);
uint64_t genlabel();

static u_int genimm(u_int imm,u_int *encoded)
{
  if(imm==0) {*encoded=0;return 1;}
  int i=32;
  while(i>0)
  {
    if(imm<256) {
      *encoded=((i&30)<<7)|imm;
      return 1;
    }
    imm=(imm>>2)|(imm<<30);i-=2;
  }
  return 0;
}


// This function returns true if the argument is a non-empty
// sequence of ones starting at the least significant bit with the remainder
// zero.
static uint32_t is_mask(uint64_t value) {
  return value && ((value + 1) & value) == 0;
}

// This function returns true if the argument contains a
// non-empty sequence of ones with the remainder zero.
static uint32_t is_shifted_mask(uint64_t Value) {
  return Value && is_mask((Value - 1) | Value);
}

uint32_t count_leading_zeros(uint64_t value)
{
#ifdef _MSC_VER
  uint32_t leading_zero_low = 0;
  uint32_t leading_zero_high = 0;
  if(!_BitScanReverse(&leading_zero_low, (uint32_t)value))
    leading_zero_low = 32;
  else
    leading_zero_low = 31 - leading_zero_low;

  if(!_BitScanReverse(&leading_zero_high, (uint32_t)(value>>32)))
    leading_zero_high = 32;
  else
    leading_zero_high = 31 - leading_zero_high;

  if(leading_zero_high == 32)
    return leading_zero_low + leading_zero_high;
  else
    return leading_zero_high;
#else /* ARM64 */
  return __builtin_clzll(value);
#endif
}

static void emit_cmp(t_bytes *out, int rs,int rt);

uint32_t count_trailing_zeros(uint64_t value)
{
#ifdef _MSC_VER
  uint32_t trailing_zero_low = 0;
  uint32_t trailing_zero_high = 0;
  if(!_BitScanForward(&trailing_zero_low, (uint32_t)value))
    trailing_zero_low = 32;

  if(!_BitScanForward(&trailing_zero_high, (uint32_t)(value>>32)))
    trailing_zero_high = 32;

  if(trailing_zero_low == 32)
    return trailing_zero_low + trailing_zero_high;
  else
    return trailing_zero_low;
#else /* ARM64 */
  return __builtin_ctzll(value);
#endif
}

// Determine if an immediate value can be encoded
// as the immediate operand of a logical instruction for the given register
// size. If so, return 1 with "encoding" set to the encoded value in
// the form N:immr:imms.
static uint32_t genimm2(uint64_t imm, uint32_t regsize, uint32_t * encoded) {
  // First, determine the element size.
  uint32_t size = regsize;
  do {
    size /= 2;
    uint64_t mask = (1ULL << size) - 1;

    if ((imm & mask) != ((imm >> size) & mask)) {
      size *= 2;
      break;
    }
  } while (size > 2);

  // Second, determine the rotation to make the element be: 0^m 1^n.
  uint32_t trailing_one, trailing_zero;
  uint64_t mask = ((uint64_t)-1LL) >> (64 - size);
  imm &= mask;

  if (is_shifted_mask(imm)) {
    trailing_zero = count_trailing_zeros(imm);
    assert(trailing_zero < 64);
    trailing_one = count_trailing_zeros(~(imm >> trailing_zero));
  } else {
    imm |= ~mask;
    if (!is_shifted_mask(~imm))
      return 0;
  
    uint32_t leading_one = count_leading_zeros(~imm);
    trailing_zero = 64 - leading_one;
    trailing_one = leading_one + count_trailing_zeros(~imm) - (64 - size);
  }

  // Encode in immr the number of RORs it would take to get *from* 0^m 1^n
  // to our target value, where trailing_zero is the number of RORs to go the opposite
  // direction.
  assert(size > trailing_zero);
  uint32_t immr = (size - trailing_zero) & (size - 1);

  // If size has a 1 in the n'th bit, create a value that has zeroes in
  // bits [0, n] and ones above that.
  uint64_t Nimms = ~(size-1) << 1;

  // Or the trailing_one value into the low bits, which must be below the Nth bit
  // bit mentioned above.
  Nimms |= (trailing_one-1);

  // Extract the seventh bit and toggle it to create the N field.
  uint32_t N = ((Nimms >> 6) & 1) ^ 1;

  *encoded = (N << 12) | (immr << 6) | (Nimms & 0x3f);
  return 1;
}

static void emit_branch_label(t_bytes *out, uint64_t id, int cond);
static void emit_test(t_bytes *out, int rs, int rt);
static void emit_cmpimm(t_bytes *out, int reg, int val);
static void set_carry_flag(t_bytes *out);
static void clear_carry_flag(t_bytes *out);
static void emit_andimm(t_bytes *out,int rs,int imm,int rt);
static void emit_label(t_bytes *bytes, uint64_t id);
static void get_carry_flag(t_bytes *out, int reg);

static void emit_lsls_reg(t_bytes *out, int reg, int nreg);
static void emit_lsrs_reg(t_bytes *out, int reg, int nreg);
static void emit_asrs_reg(t_bytes *out, int reg, int nreg);
static void emit_rors_reg(t_bytes *out, int reg, int nreg);
static void emit_rrxs_reg(t_bytes *out, int reg, int nreg);
static void emit_rrx_reg(t_bytes *out, int reg, int nreg);
static void emit_ror_reg(t_bytes *out, int reg, int nreg);

static void emit_andimm(t_bytes *out,int rs,int imm,int rt);

static void emit_lsr_reg(t_bytes *out, int reg, int nreg);
static void emit_testimm(t_bytes *out, int rs,int imm);

static void output_w32_FROM_PC(t_bytes *bytes, unsigned int word);
static void emit_movimm(t_bytes *out, uintptr_t imm,u_int rt);
static void emit_movimm2pad(t_bytes *out, u_int imm,u_int rt);
static void emit_addnop(t_bytes *out, u_int r);

static void emit_setc(t_bytes *out, int reg);
static void emit_or(t_bytes *out, u_int rs1,u_int rs2,u_int rt);

static void output_w32(t_bytes *bytes, unsigned int word);

static void output_w32_full(t_bytes *bytes, unsigned int word, int type, int label_id, int cond);

static void emit_lsr_reg_quick(t_bytes *out, int reg, int nreg);

static void emit_mul(t_bytes *out, u_int rs1,u_int rs2);


static void emit_setnz(t_bytes *out, int reg);
static void emit_setz(t_bytes *out, int reg);
static void emit_movimm(t_bytes *out, uintptr_t imm,u_int rt);
static void emit_mov(t_bytes *out, int rs,int rt);
static void emit_jmpreg(t_bytes *out, u_int r);

static void emit_brk(t_bytes *out);

static void emit_lsl(t_bytes *out, int reg, int n) {
		emit_movimm(out, n, SHIFT_REG);
    output_w32(out, 0x1AC02000|SHIFT_REG<<16|reg<<5|reg);
}

static void emit_lsr(t_bytes *out, int reg, int n) {
	if (n < 32) {
		output_w32(out, 0x53000000|n<<16|0x1f<<10|reg<<5|reg);
	}
	else {
		emit_movimm(out, n, SHIFT_REG);
		output_w32(out, 0x1ac02400|SHIFT_REG<<16|reg<<5|reg);
	}
}

static void emit_lsr64(t_bytes *out, int reg, int n) {
	if (n < 32) {
		output_w32(out, 0xD340FC00|n<<16|reg<<5|reg);
	}
	else {
		emit_movimm(out, n, SHIFT_REG);
		output_w32(out, 0x9AC02400|SHIFT_REG<<16|reg<<5|reg);
	}
}

static void emit_asr(t_bytes *out, int reg, int num)
{
  if (num < 32) {
    output_w32(out, 0x13000000|num<<16|0x1f<<10|reg<<5|reg);
  }
  else {
    emit_movimm(out, num, SHIFT_REG);
	  output_w32(out, 0x1ac02800|SHIFT_REG<<16|reg<<5|reg);
  }
}

static void emit_asr64(t_bytes *out, int reg, int num)
{
  if (num < 32) {
	output_w32(out, 0x9340FC00|num<<16|reg<<5|reg);
  }
  else {
	emit_movimm(out, num, SHIFT_REG);
	  output_w32(out, 0x9AC02800|SHIFT_REG<<16|reg<<5|reg);
  }
}

static void emit_asr_reg(t_bytes *out, int reg, int nreg) {

    uint64_t done=genlabel();
	uint64_t setb=genlabel();
	emit_andimm(out, nreg, 0xff, nreg);

    emit_cmpimm(out, nreg, 0);
	emit_branch_label(out, done, 0); // eq 0
	emit_cmpimm(out, nreg, 32);
	emit_branch_label(out, setb, 10); // greater than or equal to 32
    

    output_w32(out, 0x1ac02800|nreg<<16|reg<<5|reg); // do shift
	
	emit_branch_label(out, done, 0xE);
	
	emit_label(out, setb);
	emit_movimm(out, 1<<31, X22_REG);
	emit_test(out, reg, X22_REG); // test BIT31(reg 22) of original reg 20
	emit_setnz(out, reg);
	emit_movimm(out, 0xFFFFFFFF, X22_REG);
	emit_mul(out, reg, X22_REG);

    emit_label(out, done);
}


static void emit_ror(t_bytes *out, int reg, int n) {
	if (n < 32) {
		output_w32(out, 0x13800000|reg<<16|n<<10|reg<<5|reg);
	}
	else {
		emit_movimm(out, n, SHIFT_REG);
		emit_ror_reg(out, reg, SHIFT_REG);
	}
}
static void emit_rrx(t_bytes *out, int reg, int n) {
	emit_setc(out, 13);
	output_w32(out, 0x530101AD); // lsl w13, w13, #31
	emit_andimm(out, reg, 1, X5_REG);

	emit_movimm(out, n, SHIFT_REG);
	emit_ror_reg(out, reg, SHIFT_REG);
	emit_andimm(out, reg, 0x7fffffff, reg);
	emit_or(out, reg, 13, reg);
}
static void emit_lsl_reg(t_bytes *out, int reg, int nreg) {
    uint64_t setb=genlabel();
    uint64_t done=genlabel();
	
	emit_andimm(out, nreg, 0xff, nreg);

    emit_cmpimm(out, nreg, 32);
    emit_branch_label(out, setb, 10); // greater than or equal to 32

    output_w32(out, 0x1ac02000|nreg<<16|reg<<5|reg); // do shift
    emit_branch_label(out, done, 0xE);
    
    emit_label(out, setb);
    emit_movimm(out, 0, reg);

    emit_label(out, done);
}

static void emit_lsl_reg_quick(t_bytes *out, int reg, int nreg) {
  output_w32(out, 0x1ac02000|nreg<<16|reg<<5|reg);
}

static void emit_lsr_reg_quick(t_bytes *out, int reg, int nreg) {
  output_w32(out, 0x1ac02400|nreg<<16|reg<<5|reg);
}

static void emit_lsr_reg(t_bytes *out, int reg, int nreg)
{
    uint64_t setb=genlabel();
    uint64_t done=genlabel();
	
	emit_andimm(out, nreg, 0xff, nreg);

    emit_cmpimm(out, nreg, 32);
    emit_branch_label(out, setb, 10); // greater than or equal to 32

    output_w32(out, 0x1ac02400|nreg<<16|reg<<5|reg); // do shift
    emit_branch_label(out, done, 0xE);
    
    emit_label(out, setb);
    emit_movimm(out, 0, reg);

    emit_label(out, done);
}

static void emit_andsimm(t_bytes *out,int rs,int imm,int rt);
static void emit_ror_reg(t_bytes *out, int reg, int nreg) {

    uint64_t done=genlabel();
	
	emit_andimm(out, nreg, 0xff, nreg);

    emit_cmpimm(out, nreg, 0);
    emit_branch_label(out, done, 0); // 0
    emit_andsimm(out, nreg, 0x1F, nreg);
    emit_branch_label(out, done, 0); // 0

    output_w32(out, 0x1AC02C00|reg|reg<<5|nreg<<16); // do shift

    emit_label(out, done);
}

static void emit_lsls(t_bytes *out, int reg, int n) {
		emit_movimm(out, n, SHIFT_REG);
    emit_lsls_reg(out, reg, SHIFT_REG);
}
static void emit_lsrs(t_bytes *out, int reg, int n) {
		emit_movimm(out, n, SHIFT_REG);
    emit_lsrs_reg(out, reg, SHIFT_REG);
}
static void emit_asrs(t_bytes *out, int reg, int n) {
		emit_movimm(out, n, SHIFT_REG);
    emit_asrs_reg(out, reg, SHIFT_REG);
}
static void emit_rors(t_bytes *out, int reg, int n) {
		emit_movimm(out, n, SHIFT_REG);
    emit_rors_reg(out, reg, SHIFT_REG);
}
static void emit_rrxs(t_bytes *out, int reg, int n) {
	
	emit_setc(out, 13);
	output_w32(out, 0x530101AD); // lsl w13, w13, #31
	emit_andimm(out, reg, 1, X5_REG);

	emit_movimm(out, n, SHIFT_REG);
	emit_ror_reg(out, reg, SHIFT_REG);
	emit_andimm(out, reg, 0x7fffffff, reg);
	emit_or(out, reg, 13, reg);
}
static void emit_lsls_reg(t_bytes *out, int reg, int nreg) {


    uint64_t nonzero=genlabel();
    uint64_t done=genlabel();
    uint64_t eq32=genlabel();
    uint64_t gt32=genlabel();
	
	emit_andimm(out, nreg, 0xff, nreg);

    emit_cmpimm(out, nreg, 0);
    emit_branch_label(out, nonzero, 0x1);

    /* eq 0 */

	get_carry_flag(out, 5);
    emit_branch_label(out, done, 0xE);

    /* end eq 0 */

    emit_label(out, nonzero);
	
	emit_mov(out, nreg, X19_REG);
    emit_mov(out, reg, X20_REG);

   /* non zero */
    emit_cmpimm(out, nreg, 32);
    emit_branch_label(out, eq32, 0x0); // nreg == 32
    emit_branch_label(out, gt32, 12); // gt 32

    // get last shifted bit
    emit_movimm(out, 32, X18_REG);
    output_w32(out, 0x4B000000 | (X19_REG << 16) | (X18_REG << 5) | X18_REG);

    // perform shifft
    output_w32(out, 0x1AC02000|nreg<<16|reg<<5|reg);

    //emit_test(out, 20, X18_REG);
    emit_movimm(out, 1, X22_REG);
    emit_lsl_reg_quick(out, X22_REG, X18_REG);
    emit_test(out, X20_REG, X22_REG);

    emit_setnz(out, X5_REG);
    emit_branch_label(out, done, 0xE);

    /* end non zero */

    emit_label(out, eq32);

    /* equal 32 */

    emit_movimm(out, 1, X22_REG);
    emit_test(out, X20_REG, X22_REG); // test BIT0(reg 22) of original reg 20

    emit_setnz(out, X5_REG);
	emit_movimm(out, 0, reg);
    emit_branch_label(out, done, 0xE);

    /* end equal 32 */

    emit_label(out, gt32);

    /* gt 32 */

    emit_movimm(out, 0, reg);
    emit_movimm(out, 0, X5_REG);

     /* end gt 32 */

    emit_label(out, done);
    emit_cmpimm(out, reg, 0);
}
static void emit_lsrs_reg(t_bytes *out, int reg, int nreg) {

    uint64_t nonzero=genlabel();
    uint64_t done=genlabel();
    uint64_t eq32=genlabel();
    uint64_t gt32=genlabel();
	
	emit_andimm(out, nreg, 0xff, nreg);

    emit_cmpimm(out, nreg, 0);
    emit_branch_label(out, nonzero, 0x1);

    /* eq 0 */

    get_carry_flag(out, X5_REG);
    emit_branch_label(out, done, 0xE);

    /* end eq 0 */

    emit_label(out, nonzero);
	
	//emit_andimm(out, nreg, 0xff, nreg);
	emit_mov(out, nreg, X19_REG);
    emit_mov(out, reg, X20_REG);

   /* non zero */
    emit_cmpimm(out, nreg, 32);
    emit_branch_label(out, eq32, 0x0); // nreg == 32
    emit_branch_label(out, gt32, 12); // gt 32

	// get last shifted bit
    emit_movimm(out, 1, X18_REG);
    output_w32(out, 0x4B000000 | (X18_REG << 16) | (X19_REG << 5) | X18_REG);

    // perform shifft
    output_w32(out, 0x1AC02400|nreg<<16|reg<<5|reg);

    emit_movimm(out, 1, X22_REG);
    emit_lsl_reg_quick(out, X22_REG, X18_REG);
    emit_test(out, X20_REG, X22_REG);

    emit_setnz(out, X5_REG);
    emit_branch_label(out, done, 0xE);

    /* end non zero */

    emit_label(out, eq32);

    /* equal 32 */

    emit_movimm(out, 1<<31, X22_REG);
    emit_test(out, X20_REG, X22_REG); // test BIT31(reg 22) of original reg 20

    emit_setnz(out, X5_REG);
	emit_movimm(out, 0, reg);
	
    emit_branch_label(out, done, 0xE);

    /* end equal 32 */

    emit_label(out, gt32);

    /* gt 32 */

    emit_movimm(out, 0, reg);
	emit_movimm(out, 0, X5_REG);
    // fall into clrb

     /* end gt 32 */

    emit_label(out, done);

    emit_cmpimm(out, reg, 0);
}
static void emit_asrs_reg(t_bytes *out, int reg, int nreg) {

    uint64_t nonzero=genlabel();
    uint64_t done=genlabel();
    uint64_t gteq32=genlabel();

	emit_andimm(out, nreg, 0xff, nreg);
	
	emit_cmpimm(out, nreg, 0);
    emit_branch_label(out, nonzero, 0x1);

    /* eq 0 */

    get_carry_flag(out, X5_REG);
    emit_branch_label(out, done, 0xE);

    /* end eq 0 */

    emit_label(out, nonzero);
	
	emit_mov(out, nreg, X19_REG);
    emit_mov(out, reg, X20_REG);

	/* non zero */
    emit_cmpimm(out, nreg, 32);
    emit_branch_label(out, gteq32, 10); // gteq 32

	// get last shifted bit
    emit_movimm(out, 1, X18_REG);
    output_w32(out, 0x4B000000 | (X18_REG << 16) | (X19_REG << 5) | X18_REG);

    // perform shifft
    output_w32(out, 0x1AC02800|nreg<<16|reg<<5|reg);

    emit_movimm(out, 1, X22_REG);
    emit_lsl_reg_quick(out, X22_REG, X18_REG);
    emit_test(out, X20_REG, X22_REG);

    emit_setnz(out, X5_REG);
    emit_branch_label(out, done, 0xE);

    /* end non zero */

    emit_label(out, gteq32);

    /* equal 32 */

    // perform shifft
    output_w32(out, 0x1AC02800|nreg<<16|reg<<5|reg);

    emit_movimm(out, 1<<31, X22_REG);
    emit_test(out, X20_REG, X22_REG); // test BIT31(reg 22) of original reg 20

    emit_setnz(out, X5_REG);
	
	emit_mov(out, X5_REG, reg);
	emit_movimm(out, 0xFFFFFFFF, X22_REG);
	emit_mul(out, reg, X22_REG);

    emit_label(out, done);

    emit_cmpimm(out, reg, 0);
}
static void emit_rors_reg(t_bytes *out, int reg, int nreg) {

    uint64_t nonzero=genlabel();
    uint64_t done=genlabel();
    uint64_t and0=genlabel();

    emit_mov(out, reg, X20_REG);
	
	emit_andimm(out, nreg, 0xff, nreg);

    emit_cmpimm(out, nreg, 0);
    emit_branch_label(out, nonzero, 0x1);

	get_carry_flag(out, 5);
    emit_branch_label(out, done, 0xE);

    /* eq 0 */

    /* end eq 0 */

    emit_label(out, nonzero);

   /* non zero */
    emit_andimm(out, nreg, 0x1F, nreg);
	emit_mov(out, nreg, X19_REG);
    emit_cmpimm(out, X19_REG, 0);
    emit_branch_label(out, and0, 0x0); // eq 0

	// get last shifted bit
    emit_movimm(out, 1, X18_REG);
    //output_w32(out, 0x4B120272); // sub w18, w19, w18
    output_w32(out, 0x4B000000 | (X18_REG << 16) | (X19_REG << 5) | X18_REG);

    // perform shifft
    output_w32(out, 0x1AC02C00|nreg<<16|reg<<5|reg);

    //emit_test(out, 20, X18_REG);
    emit_movimm(out, 1, X22_REG);
    emit_lsl_reg_quick(out, X22_REG, X18_REG);
    emit_test(out, X20_REG, X22_REG);

    emit_setnz(out, X5_REG);
    emit_branch_label(out, done, 0xE);

    /* end non zero */

    emit_label(out, and0);

    /* equal 32 */

    // perform shifft
    emit_mov(out, X20_REG, reg);

    emit_movimm(out, 1<<31, X22_REG);
    emit_test(out, X20_REG, X22_REG); // test BIT31(reg 22) of original reg 20

	emit_setnz(out, X5_REG);
    emit_branch_label(out, done, 0xE);

    emit_label(out, done);
    emit_cmpimm(out, reg, 0);
}
static void emit_rrxs_reg(t_bytes *out, int reg, int nreg) {
	emit_rors_reg(out, reg, nreg);
}

static void emit_mov(t_bytes *out, int rs,int rt)
{
  output_w32(out, 0x2a000000|rs<<16|WZR<<5|rt);
}

static void emit_mov64(t_bytes *out, int rs,int rt)
{
  output_w32(out, 0xaa000000|rs<<16|WZR<<5|rt);
}

static void emit_add(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x0b000000|rs2<<16|rs1<<5|rt);
}

static void emit_adds(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x2b000000|rs2<<16|rs1<<5|rt);
}

static void emit_add64(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x8b000000|rs2<<16|rs1<<5|rt);
}

static void emit_adc(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x1a000000|rs2<<16|rs1<<5|rt);
}

static void emit_adcs(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x3a000000|rs2<<16|rs1<<5|rt);
}

static void emit_sub(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x4b000000|rs2<<16|rs1<<5|rt);
}

static void emit_subs(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x6b000000|rs2<<16|rs1<<5|rt);
}

static void emit_sbc(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x5a000000|rs2<<16|rs1<<5|rt);
}

static void emit_sbcs(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x7a000000|rs2<<16|rs1<<5|rt);
}

static void emit_neg(t_bytes *out, int rs, int rt)
{
  output_w32(out, 0x4b000000|rs<<16|WZR<<5|rt);
}

static void emit_negs(t_bytes *out, int rs, int rt)
{
  output_w32(out, 0x6b000000|rs<<16|WZR<<5|rt);
}

static void emit_mvns(t_bytes *out, int rs,int rt)
{
	output_w32(out, 0x2A2003E0|rs<<16|WZR<<5|rt);
	emit_cmpimm(out, rt, 0);
}

static void emit_zeroreg(t_bytes *out, int rt)
{
  output_w32(out, 0x52800000|rt);
}
static void emit_movn(t_bytes *out, u_int imm,u_int rt)
{
  output_w32(out, 0x12800000|imm<<5|rt);
}

static void emit_movimms(t_bytes *out, u_int imm,u_int rt)
{
	emit_movimm(out, imm, rt);
  emit_cmpimm(out, rt, 0);
}

static void emit_movz(t_bytes *out, u_int imm,u_int rt)
{
  output_w32(out, 0x52800000|imm<<5|rt);
}
static void emit_movn_lsl16(t_bytes *out, u_int imm,u_int rt)
{
  output_w32(out, 0x12a00000|imm<<5|rt);
}
static void emit_movz_lsl16(t_bytes *out, u_int imm,u_int rt)
{
  output_w32(out, 0x52a00000|imm<<5|rt);
}
static void emit_movk(t_bytes *out, u_int imm,u_int rt)
{
  output_w32(out, 0x72800000|imm<<5|rt);
}
static void emit_movk_lsl16(t_bytes *out, u_int imm,u_int rt)
{
  output_w32(out, 0x72a00000|imm<<5|rt);
}

static void emit_movs(t_bytes *out, int rs,int rt) {
  output_w32(out, 0x2A0003E0|rs<<5|rt);
  emit_cmp(out, rt, rt);
}

static void emit_mov_cond(t_bytes *out, int rs,int rt, int cond)
{
  uint64_t setb=genlabel();
	uint64_t done=genlabel();

  emit_branch_label(out, setb, cond);
  emit_branch_label(out, done, 0xE);
  emit_label(out, setb);
  emit_mov(out, rs, rt);
  emit_label(out, done);
}

static void emit_movk_lslnum(t_bytes *out, u_int imm,u_int rt, int lsl)
{
  uint32_t lsl_bit;

  switch (lsl) {
    case 16:
      lsl_bit = 0x200000;
      break;
    case 32:
      lsl_bit = 0x400000;
      break;
    case 48:
      lsl_bit = 0x600000;
      break;
    default:
      lsl_bit = 0;
      break;
  }

  output_w32(out, 0x72800000|imm<<5|rt|lsl_bit);
}

static void emit_movk_lslnum64(t_bytes *out, u_int imm,u_int rt, int lsl)
{
  uint32_t lsl_bit;

  switch (lsl) {
    case 16:
      lsl_bit = 0x200000;
      break;
    case 32:
      lsl_bit = 0x400000;
      break;
    case 48:
      lsl_bit = 0x600000;
      break;
    default:
      lsl_bit = 0;
      break;
  }

  output_w32(out, 0x80000000|0x72800000|imm<<5|rt|lsl_bit);
}

static void emit_movz64(t_bytes *out, u_int imm,u_int rt)
{
  output_w32(out, 0x80000000|0x52800000|imm<<5|rt);
}

static void emit_ptr(t_bytes *out, uintptr_t ptr, u_int rt) {
  emit_movz64(out, ptr&0xffff,rt);
  if ((ptr>>16)&0xffff) emit_movk_lslnum64(out, (ptr>>16)&0xffff,rt, 16);
  if ((ptr>>32)&0xffff) emit_movk_lslnum64(out, (ptr>>32)&0xffff,rt, 32);
  if ((ptr>>48)&0xffff) emit_movk_lslnum64(out, (ptr>>48)&0xffff,rt, 48);
}

static void emit_movimm(t_bytes *out, uintptr_t imm,u_int rt)
{
  uint32_t armval=0;
  if(imm<65536) {
    emit_movz(out, imm,rt);
  }else if((~imm)<65536) {
    emit_movn(out, ~imm,rt);
  }else if((imm&0xffff)==0) {
    emit_movz_lsl16(out, (imm>>16)&0xffff,rt);
  }else if(((~imm)&0xffff)==0) {
    emit_movn_lsl16(out, (~imm>>16)&0xffff,rt);
  }else if(genimm2((uint64_t)imm,32,&armval)) {
    output_w32(out, 0x32000000|armval<<10|WZR<<5|rt);
  }else{
    emit_movz_lsl16(out, (imm>>16)&0xffff,rt);
    emit_movk(out, imm&0xffff,rt);
  }
}

static void emit_test(t_bytes *out, int rs, int rt)
{
  output_w32(out, 0x6a000000|rt<<16|rs<<5|WZR);
}

static void emit_not(t_bytes *out, int rs,int rt)
{
  output_w32(out, 0x2a200000|rs<<16|WZR<<5|rt);
}

static void emit_and(t_bytes *out, u_int rs1,u_int rs2,u_int rt)
{
  output_w32(out, 0x0a000000|rs2<<16|rs1<<5|rt);
}

static void emit_or(t_bytes *out, u_int rs1,u_int rs2,u_int rt)
{
  output_w32(out, 0x2a000000|rs2<<16|rs1<<5|rt);
}

static void emit_or64(t_bytes *out, u_int rs1,u_int rs2,u_int rt)
{
  output_w32(out, 0xAA000000|rs2<<16|rs1<<5|rt);
}

static void emit_or_and_set_flags(t_bytes *out, int rs1,int rs2,int rt)
{
  output_w32(out, 0x2A000000|rs2<<16|rs1<<5|rt);
  emit_cmpimm(out, rt, 0);
}

static void emit_xor(t_bytes *out, u_int rs1,u_int rs2,u_int rt)
{
  output_w32(out, 0x4a000000|rs2<<16|rs1<<5|rt);
}

static void emit_ands(t_bytes *out, u_int rs1,u_int rs2,u_int rt)
{
  output_w32(out, 0x6a000000|rs2<<16|rs1<<5|rt);
}

static void emit_ors(t_bytes *out, u_int rs1,u_int rs2,u_int rt)
{
 emit_or_and_set_flags(out, rs1,rs2,rt);
}
static void emit_xors(t_bytes *out, u_int rs1,u_int rs2,u_int rt)
{
  output_w32(out, 0x4a000000|rs2<<16|rs1<<5|rt);
  emit_cmpimm(out, rt, 0);
}

static void emit_addimm64(t_bytes *out, u_int rs,int imm,u_int rt)
{
  emit_movimm(out, imm, 16);
  emit_add64(out, rs, 16, rt);
}


static void emit_addimm(t_bytes *out, u_int rs,int imm,u_int rt)
{
  if(imm!=0) {
    //assert(imm>-16777216&&imm<16777216);
    if(imm<0&&imm>-4096) {
      output_w32(out, 0x51000000|((-imm)&0xfff)<<10|rs<<5|rt);
    }else if(imm>0&&imm<4096) {
      output_w32(out, 0x11000000|(imm&0xfff)<<10|rs<<5|rt);
    }else if(imm<0) {
      output_w32(out, 0x51400000|(((-imm)>>12)&0xfff)<<10|rs<<5|rt);
      if((-imm&0xfff)!=0) {
        output_w32(out, 0x51000000|((-imm)&0xfff)<<10|rt<<5|rt);
      }
    }else {
      output_w32(out, 0x11400000|((imm>>12)&0xfff)<<10|rs<<5|rt);
      if((imm&0xfff)!=0) {
        output_w32(out, 0x11000000|(imm&0xfff)<<10|rt<<5|rt);
      }
    }
  }
  else if(rs!=rt) emit_mov(out, rs,rt);
}

static void emit_addsimm(t_bytes *out, u_int rs,int imm,u_int rt)
{
  emit_movimm(out, imm, X16_REG);
  emit_adds(out, rs, X16_REG, rt);
}

static void emit_cmp(t_bytes *out, int rs,int rt)
{
  output_w32(out, 0x6b000000|rt<<16|rs<<5|WZR);
}

static void emit_smulbb(t_bytes *out, u_int rs1, u_int rs2) {
  output_w32(out, 0x93403C00 | (rs1 << 5) | X17_REG); // SBFX x17, x0, #0, #16
  output_w32(out, 0x93403C00 | (rs2 << 5) | X18_REG); // SBFX x18, x0, #0, #16

  // mul
  output_w32(out, 0x9B207C00|(X18_REG<<16)|(X17_REG<<5)|rs1);
}

static void emit_smulbt(t_bytes *out, u_int rs1, u_int rs2) {
  output_w32(out, 0x93403C00 | (rs1 << 5) | X17_REG); // SBFX x17, x0, #0, #16
  output_w32(out, 0x93507C00 | (rs2 << 5) | X18_REG); // SBFX x18, x0, #16, #16

  // mul
  output_w32(out, 0x9B207C00|(X18_REG<<16)|(X17_REG<<5)|rs1);
}

static void emit_smultb(t_bytes *out, u_int rs1, u_int rs2) {
  output_w32(out, 0x93507C00 | (rs1 << 5) | X17_REG); //SBFX x17, rs1, #16, #16
  output_w32(out, 0x93403C00 | (rs2 << 5) | X18_REG); // SBFX x18, x0, #0, #16

  // mul
  output_w32(out, 0x9B207C00|(X18_REG<<16)|(X17_REG<<5)|rs1);
}

static void emit_smultt(t_bytes *out, u_int rs1, u_int rs2) {
  output_w32(out, 0x93507C00 | (rs1 << 5) | X17_REG); // SBFX x17, rs1, #16, #16
  output_w32(out, 0x93507C00 | (rs2 << 5) | X18_REG); // SBFX x18, rs2, #16, #16

  // mul
  output_w32(out, 0x9B207C00|(X18_REG<<16)|(X17_REG<<5)|rs1);
}


static void emit_smulwt(t_bytes *out, u_int rs1, u_int rs2) {
  output_w32(out, 0x93507C00 | (rs1 << 5) | X18_REG); // SBFX x18, x0, #16, #16

  // mul
  output_w32(out, 0x9B207C00|(X18_REG<<16)|(rs2<<5)|rs1);
  emit_asr64(out, rs1, 16);
}
static void emit_smulwb(t_bytes *out, u_int rs1, u_int rs2) {
  output_w32(out, 0x93403C00 | (rs1 << 5) | X18_REG); // SBFX x18, x0, #0, #16

  // mul
  output_w32(out, 0x9B207C00|(X18_REG<<16)|(rs2<<5)|rs1);
  
  emit_asr64(out, rs1, 16);
}

static void emit_smlawb(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x93403C00 | (rs1 << 5) | X18_REG); // SBFX x18, x0, #0, #16

  output_w32(out, 0x9B207C00|(X18_REG<<16)|(rs2<<5)|14);
  emit_asr64(out, X14_REG, 16);
  emit_adds(out, X14_REG, lo, hi); // sets carry flag - need to use in SET_Q
}
static void emit_smlawt(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x93403C00 | (rs1 << 5) | X18_REG); // SBFX x18, x0, #0, #16

  output_w32(out, 0x9B207C00|(X18_REG<<16)|(rs2<<5)|14);
  emit_asr64(out, X14_REG, 16);
  emit_adds(out, X14_REG, lo, hi); // sets carry flag - need to use in SET_Q
}

static void emit_smlabb(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x93403C00 | (rs1 << 5) | X17_REG); // SBFX x17, x0, #0, #16 
  output_w32(out, 0x93403C00 | (rs2 << 5) | X18_REG); // SBFX x18, x0, #0, #16

  output_w32(out, 0x9B207C00|(X18_REG<<16)|(X17_REG<<5)|hi);
  emit_adds(out, hi, lo, hi); // sets carry flag - need to use in SET_Q
}
static void emit_smlabt(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x93403C00 | (rs1 << 5) | X17_REG); // SBFX x17, x0, #0, #16
  output_w32(out, 0x93507C00 | (rs2 << 5) | X18_REG); // SBFX x18, x0, #16, #16

  output_w32(out, 0x9B207C00|(X18_REG<<16)|(X17_REG<<5)|hi);
  emit_adds(out, hi, lo, hi); // sets carry flag - need to use in SET_Q
}
static void emit_smlatb(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x93507C00 | (rs1 << 5) | X17_REG); // SBFX x17, x0, #16, #16
  output_w32(out, 0x93403C00 | (rs2 << 5) | X18_REG); // sbfx x18, x0, #0, #16

  output_w32(out, 0x9B207C00|(X18_REG<<16)|(X17_REG<<5)|hi);
  emit_adds(out, hi, lo, hi); // sets carry flag - need to use in SET_Q
}
static void emit_smlatt(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x93507C00 | (rs1 << 5) | X17_REG); // SBFX x17, rs1, #16, #16
  output_w32(out, 0x93507C00 | (rs2 << 5) | X18_REG); // SBFX x18, rs2, #16, #16

  output_w32(out, 0x9B207C00|(X18_REG<<16)|(X17_REG<<5)|hi);
  emit_adds(out, hi, lo, hi); // sets carry flag - need to use in SET_Q
}

static void emit_smlalbb(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  emit_mov(out, hi, X17_REG);   
  output_w32(out, 0xB3607C00 | (lo << 5) | X17_REG); // BFI x17, xhi, #32, #32

  output_w32(out, 0x93403C00 | (rs1 << 5) | X19_REG); //SBFX x19, rs1, #0, #16
  output_w32(out, 0x93403C00 | (rs2 << 5) | X20_REG); //SBFX x20, rs2, #0, #16

  output_w32(out, 0x9B200000 | (X20_REG << 16) | (X19_REG << 5) | (X17_REG << 10) | X17_REG); // SMADDL x17, w#, w#, x17
  
  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}
static void emit_smlalbt(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  emit_mov(out, hi, X17_REG); 
      
  output_w32(out, 0xB3607C00 | (lo << 5) | X17_REG); // BFI x17, xhi, #32, #32

  output_w32(out, 0x93403C00 | (rs1 << 5) | X19_REG); //SBFX x19, rs1, #0, #16
  output_w32(out, 0x93507C00 | (rs2 << 5) | X20_REG); //SBFX x20, rs2, #16, #16

  output_w32(out, 0x9B200000 | (X20_REG << 16) | (X19_REG << 5) | (X17_REG << 10) | X17_REG); // SMADDL x17, w#, w#, x17

  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32

  emit_mov(out, X17_REG, hi);
}
static void emit_smlaltb(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  emit_mov(out, hi, X17_REG);     
  output_w32(out, 0xB3607C00 | (lo << 5) | X17_REG); // BFI x17, xhi, #32, #32

  output_w32(out, 0x93507C00 | (rs1 << 5) | X19_REG); //sbfx x19, rs1, #16, #16
  output_w32(out, 0x93403C00 | (rs2 << 5) | X20_REG); //sbfx x20, rs2, #0, #16

  output_w32(out, 0x9B200000 | (X20_REG << 16) | (X19_REG << 5) | (X17_REG << 10) | X17_REG); // SMADDL x17, w#, w#, x17
  
  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32

  emit_mov(out, X17_REG, hi);
}
static void emit_smlaltt(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  emit_mov(out, hi, X17_REG); 
 
  output_w32(out, 0xB3607C00 | (lo << 5) | X17_REG); // BFI x17, xhi, #32, #32

  output_w32(out, 0x93507C00 | (rs1 << 5) | X19_REG); //sbfx x19, rs1, #16, #16
  output_w32(out, 0x93507C00 | (rs2 << 5) | X20_REG); //sbfx x20, rs2, #16, #16

  output_w32(out, 0x9B200000 | (X20_REG << 16) | (X19_REG << 5) | (X17_REG << 10) | X17_REG); // SMADDL x17, w#, w#, x17
  
  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}

static void emit_mul(t_bytes *out, u_int rs1,u_int rs2)
{
  output_w32(out, 0x1B007C00|(rs2<<16)|(rs1<<5)|rs1);
}
static void emit_muls(t_bytes *out, u_int rs1,u_int rs2)
{
  output_w32(out, 0x1B007C00|(rs2<<16)|(rs1<<5)|rs1);
  emit_cmpimm(out, rs1, 0);
}

static void emit_mla(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x1B000000|(lo<<10)|(rs2<<16)|(rs1<<5)|hi);
}
static void emit_mlas(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x1B000000|(lo<<10)|(rs2<<16)|(rs1<<5)|hi);
  emit_cmpimm(out, hi, 0);
}
static void emit_cmpx64(t_bytes *out, int rs) {
  output_w32(out, 0xF100001F|rs<<5);
}
static void emit_umull(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x9BA07C00 | (rs2 << 16) | (rs1 << 5) | X17_REG); // UMADDL x17, w#, w#, XZR
  
  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}
static void emit_umulls(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x9BA07C00 | (rs2 << 16) | (rs1 << 5) | X17_REG); // UMADDL x17, w#, w#, XZR
  emit_cmpx64(out, X17_REG);

  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}
static void emit_umlal(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  emit_mov(out, hi, X17_REG); 
 
  output_w32(out, 0xB3607C00 | (lo << 5) | X17_REG); // BFI x17, xhi, #32, #32

  output_w32(out, 0x9B200000 | (rs2 << 16) | (rs1 << 5) | (X17_REG << 10) | X17_REG); // UMADDL x17, w#, w#, x17

  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}
static void emit_umlals(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  emit_mov(out, hi, X17_REG); 

  output_w32(out, 0xB3607C00 | (lo << 5) | X17_REG); // BFI x17, xhi, #32, #32

  output_w32(out, 0x9B200000 | (rs2 << 16) | (rs1 << 5) | (X17_REG << 10) | X17_REG); // UMADDL x17, w#, w#, x17
  emit_cmpx64(out, X17_REG);
  
  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}
static void emit_smull(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x9B207C00 | (rs2 << 16) | (rs1 << 5) | X17_REG); // SMADDL x17, w#, w#, XZR

  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}
static void emit_smulls(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  output_w32(out, 0x9B207C00 | (rs2 << 16) | (rs1 << 5) | X17_REG); // SMADDL x17, w#, w#, XZR
  emit_cmpx64(out, X17_REG);

  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}

static void emit_smlal(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  emit_mov(out, hi, X17_REG); 
 
  output_w32(out, 0xB3607C00 | (lo << 5) | X17_REG); // BFI x17, xhi, #32, #32

  output_w32(out, 0x9B200000 | (rs2 << 16) | (rs1 << 5) | (X17_REG << 10) | X17_REG); // SMADDL x17, w#, w#, x17

  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi);
}
static void emit_smlals(t_bytes *out, u_int hi, u_int lo, u_int rs1, u_int rs2)
{
  emit_mov(out, hi, X17_REG); 
     
  output_w32(out, 0xB3607C00 | (lo << 5) | X17_REG); // BFI x17, xhi, #32, #32

  output_w32(out, 0x9B200000 | (rs2 << 16) | (rs1 << 5) | (X17_REG << 10) | X17_REG); // SMADDL x17, w#, w#, x17
  emit_cmpx64(out, X17_REG);

  output_w32(out, 0xD360FC00 | (X17_REG << 5) | lo); // lsr lo, x17, #32
  emit_mov(out, X17_REG, hi); 
}

static void emit_clz(t_bytes *out, int rs,int rt)
{
  output_w32(out,0x5AC01000|rs<<5|rt);
}

static void emit_teq(t_bytes *out, int rs, int rt)
{
  output_w32(out, 0x4A000000|16|rs<<5|rt<<16);
  emit_cmpimm(out, X16_REG, 0);
}

static u_int gencondjmp(intptr_t offset)
{
  return (offset>>2)&0x7ffff;
}

#define MOD_JUMP(ptr, cond, lbl_bytes, jmp_bytes) *(ptr) = 0x54000000|gencondjmp(lbl_bytes - jmp_bytes)<<5|(cond);
#include "emit_core.cpp"

static void myfunc(const char *str) {
	puts(str);
}

static void emit_ldr(t_bytes *out, int rs, int rt) {
	output_w32(out, 0xB9400000|rs<<5|rt);
}

static void emit_ldr64(t_bytes *out, int rs, int rt) {
	output_w32(out, 0xF9400000|rs<<5|rt);
}

static void emit_str(t_bytes *out, int rs, int rt) {
	output_w32(out, 0xB9000000|rs<<5|rt);
}

static void emit_str64(t_bytes *out, int rs, int rt) {
	output_w32(out, 0x40000000|0xB9000000|rs<<5|rt);
}

static void emit_str_cond(t_bytes *out, int rs, int rt, int cond) {
  uint64_t setb=genlabel();
	uint64_t done=genlabel();

		emit_branch_label(out, setb, cond);
		emit_branch_label(out, done, 0xE);
		
    emit_label(out, setb);
    emit_str(out, rs, rt);

		emit_label(out, done);
}

static void emit_ldrb(t_bytes *out, int rs, int rt) {
	output_w32(out, 0x39400000|rs<<5|rt); // LDRB	R0, [R0]
}

static void emit_ldrsb(t_bytes *out, int rs, int rt) {
	output_w32(out, 0x39C00000|rs<<5|rt); // LDRSB	R0, [R0]
}

static void emit_strb(t_bytes *out, int rs, int rt) {
	output_w32(out, 0x39000000|rs<<5|rt);
}

static void emit_ldrsw(t_bytes *out, int rs, int rt) {
	output_w32(out, 0x79C00000|rs<<5|rt); // LDRSB	R0, [R0]
}

static void emit_ldrs(t_bytes *out, int rs, int rt) {
	emit_ldr(out, rs, rt);
}

static void emit_ldrw(t_bytes *out, int rs, int rt) {
	output_w32(out, 0x79400000|rs<<5|rt); // LDRB	R0, [R0]
}

static void emit_strw(t_bytes *out, int rs, int rt) {
	output_w32(out, 0x79000000|rs<<5|rt);
}

static void emit_str_ptr_cond(t_bytes *out, uintptr_t ptr, int reg, int cond) {
	emit_ptr(out, (uintptr_t)ptr, X10_REG);
	emit_str_cond(out, X10_REG, reg, cond);
}

static void emit_write_ptr32(t_bytes *out, uintptr_t ptr, u_int val) {
  emit_ptr(out, (uintptr_t)ptr, X2_REG);
	emit_movimm(out, val, X4_REG);
	emit_str(out, X2_REG, X4_REG);
}

static void emit_write_ptr(t_bytes *out, uintptr_t ptr, uintptr_t val) {
  emit_ptr(out, ptr, X2_REG);
	emit_ptr(out, val, X4_REG);
	emit_str64(out, X2_REG, X4_REG);
}

static void emit_write_ptr32_regptrTO_immFROM(t_bytes *out, int regptr, int val) { /* reg contains ptr */
	emit_movimm(out, (uintptr_t)val, X10_REG);
	emit_str(out, regptr, X10_REG);
}
static void emit_write_ptr32_regptrTO_regFROM(t_bytes *out, int regptr, int reg) { /* reg contains ptr */
	emit_str(out, regptr, reg);
}
static void emit_write_ptr32_regptrTO_regptrFROM(t_bytes *out, int regptrto, int regptrfrom) { /* reg contains ptr */
	emit_ldr(out, regptrfrom, regptrfrom);
	emit_str(out, regptrto, regptrfrom);
}
static void emit_read_ptr32_regptrFROM_regTO(t_bytes *out, int regptr, int regout) {
	emit_ldr(out, regptr, regout);
}

static void emit_write_ptr32_reg(t_bytes *out, uintptr_t ptr, int reg) {
	emit_ptr(out, (uintptr_t)ptr, X8_REG);
	emit_str(out, X8_REG, reg);
}

static void emit_writeBYTE_ptr32_regptrTO_immFROM(t_bytes *out, int regptr, int val) { /* reg contains ptr */
	emit_movimm(out, (uintptr_t)val, X9_REG);
	emit_strb(out, regptr, X9_REG);
}
static void emit_writeBYTE_ptr32_regptrTO_regFROM(t_bytes *out, int regptr, int reg) { /* reg contains ptr */
	emit_strb(out, regptr, reg);
}

static void emit_writeBYTE_ptr32_regptrTO_regptrFROM(t_bytes *out, int regptrto, int regptrfrom) { /* reg contains ptr */
	emit_ldrb(out, regptrfrom, regptrfrom);
	emit_strb(out, regptrto, regptrfrom);
}
static void emit_readBYTE_ptr32_regptrFROM_regTO(t_bytes *out, int regptr, int regout) {
	emit_ldrb(out, regptr, regout);
}

static void emit_writeWORD_ptr32_regptrTO_immFROM(t_bytes *out, int regptr, int val) { /* reg contains ptr */
	emit_movimm(out, (uintptr_t)val, X9_REG);
	emit_strw(out, regptr, X9_REG);
}
static void emit_writeWORD_ptr32_regptrTO_regFROM(t_bytes *out, int regptr, int reg) { /* reg contains ptr */
	emit_strw(out, regptr, reg);
}
static void emit_writeWORD_ptr32_regptrTO_regptrFROM(t_bytes *out, int regptrto, int regptrfrom) { /* reg contains ptr */
	emit_ldrw(out, regptrfrom, regptrfrom);
	emit_strw(out, regptrto, regptrfrom);
}
static void emit_readWORD_ptr32_regptrFROM_regTO(t_bytes *out, int regptr, int regout) {
	emit_ldrw(out, regptr, regout);
}

static void emit_add_ptr32_regptrTO_regFROM(t_bytes *out, int regptr, int reg) { /* reg contains ptr */
	emit_ldr(out, regptr, X10_REG);
	emit_add(out, X10_REG, reg, X10_REG);
	emit_str(out, regptr, X10_REG);
}
static void emit_adds_ptr32_regptrTO_regFROM(t_bytes *out, int regptr, int reg) { /* reg contains ptr */
	emit_ldr(out, regptr, X10_REG);
	emit_adds(out, X10_REG, reg, X10_REG);
	emit_str(out, regptr, X10_REG);
}
static void emit_add_ptr32_regptrTO_immFROM(t_bytes *out, int regptr, int val) { /* reg contains ptr */
	emit_movimm(out, (uintptr_t)val, X9_REG);
	emit_ldr(out, regptr, X10_REG);
	emit_add(out, X10_REG, X9_REG, X10_REG);
	emit_str(out, regptr, X10_REG);
}

static void emit_adds_ptr32_regptrTO_immFROM(t_bytes *out, int regptr, int val) { /* reg contains ptr */
	emit_movimm(out, (uintptr_t)val, X9_REG);
	emit_ldr(out, regptr, X10_REG);
	emit_adds(out, X10_REG, X9_REG, X10_REG);
	emit_str(out, regptr, X10_REG);
}

static void emit_sub_ptr32_regptrTO_regFROM(t_bytes *out, int regptr, int reg) { /* reg contains ptr */
	emit_ldr(out, regptr, X10_REG);
	emit_sub(out, X10_REG, reg, X10_REG);
	emit_str(out, regptr, X10_REG);
}
static void emit_subs_ptr32_regptrTO_regFROM(t_bytes *out, int regptr, int reg) { /* reg contains ptr */
	emit_ldr(out, regptr, X10_REG);
	emit_subs(out, X10_REG, reg, X10_REG);
	emit_str(out, regptr, X10_REG);
}
static void emit_sub_ptr32_regptrTO_immFROM(t_bytes *out, int regptr, int val) { /* reg contains ptr */
	emit_movimm(out, (uintptr_t)val, X9_REG);
	emit_ldr(out, regptr, X10_REG);
	emit_sub(out, X10_REG, X9_REG, X10_REG);
	emit_str(out, regptr, X10_REG);
}
static void emit_subs_ptr32_regptrTO_immFROM(t_bytes *out, int regptr, int val) { /* reg contains ptr */
	emit_movimm(out, (uintptr_t)val, X9_REG);
	emit_ldr(out, regptr, X10_REG);
	emit_subs(out, X10_REG, X9_REG, X10_REG);
	emit_str(out, regptr, X10_REG);
}

static void emit_neg_ptr32_regptr(t_bytes *out, int regptr) { /* reg contains ptr */
	emit_ldr(out, regptr, X10_REG);
	emit_neg(out, X10_REG, X10_REG);
	emit_str(out, regptr, X10_REG);
}

static void emit_negs_ptr32_regptr(t_bytes *out, int regptr) { /* reg contains ptr */
	emit_ldr(out, regptr, X10_REG);
	emit_negs(out, X10_REG, X10_REG);
	emit_str(out, regptr, X10_REG);
}

static void emit_ror_ptr32_regptr(t_bytes *out, int regptr, int shift) {
	emit_ldr(out, regptr, X10_REG);
	emit_ror(out, X10_REG, shift);
	emit_str(out, regptr, X10_REG);
}

static void emit_rors_ptr32_regptr(t_bytes *out, int regptr, int shift) {
	emit_ldr(out, regptr, X10_REG);
	emit_rors(out, X10_REG, shift);
	emit_str(out, regptr, X10_REG);
}

static void emit_rors_ptr32_regptr_reg(t_bytes *out, int regptr, int regimm) {
	emit_ldr(out, regptr, X10_REG);
	emit_rors_reg(out, X10_REG, regimm);
	emit_str(out, regptr, X10_REG);
}

static void emit_ror_ptr32_regptr_reg(t_bytes *out, int regptr, int regimm) {
	emit_ldr(out, regptr, X10_REG);
	emit_ror_reg(out, X10_REG, regimm);
	emit_str(out, regptr, X10_REG);
}

static void emit_cmpimm(t_bytes *out, int rs,int imm)
{
  if (imm == 0) {
    output_w32(out, 0x7100001F|rs<<5); // cmp w#, #0
  }
  else { 
    emit_movimm(out, imm, X16_REG);
    emit_cmp(out, rs, X16_REG);
  }
}

static void emit_testimm(t_bytes *out, int rs,int imm)
{
  u_int armval, ret;
  ret=genimm2(imm,32,&armval);
  output_w32(out, 0x72000000|armval<<10|rs<<5|WZR);
}

static void emit_testimm64(t_bytes * out, int rs,int64_t imm)
{
  u_int armval, ret;
  ret=genimm2(imm,64,&armval);
  output_w32(out, 0xf2000000|armval<<10|rs<<5|WZR);
}

static void emit_orimm(t_bytes *out, int rs,int imm,int rt)
{
  u_int armval;
  if(imm==0) {
    if(rs!=rt) emit_mov(out, rs,rt);
  }else if(false && genimm2(imm,32,&armval)) {
    output_w32(out, 0x32000000|armval<<10|rs<<5|rt);
  }else{
    emit_movimm(out, imm,X9_REG);
    output_w32(out, 0x2a000000|X9_REG<<16|rs<<5|rt);
  }
}

static void emit_xorimm(t_bytes *out, int reg, int val, int rt) {
		emit_movimm(out, val, X10_REG);
		emit_xor(out, reg, X10_REG, rt);
}

static void emit_andimm(t_bytes *out,int rs,int imm,int rt)
{
  u_int armval;
  if(imm==0) {
    emit_zeroreg(out, rt);
  }else if(false && genimm2((uint64_t)imm,32,&armval)) {
    output_w32(out, 0x12000000|armval<<10|rs<<5|rt);
  }else{
    emit_movimm(out, imm,X10_REG);
    output_w32(out, 0x0a000000|X10_REG<<16|rs<<5|rt);
  }
}

static void emit_andsimm(t_bytes *out,int rs,int imm,int rt)
{
  u_int armval;
  if(imm==0) {
    emit_zeroreg(out, rt);
    emit_cmp(out, rt, rt);
  }else if(genimm2((uint64_t)imm,32,&armval)) {
    output_w32(out, 0x72000000|armval<<10|rs<<5|rt);
  }else{
    emit_movz(out, imm,X10_REG);
    output_w32(out, 0x6a000000|X10_REG<<16|rs<<5|rt);
  }
}

static void emit_subimm(t_bytes *out, int reg, int val, int rt) {
	emit_movimm(out, val, X10_REG);
	emit_sub(out, reg, X10_REG, rt);
}

static void emit_subsimm(t_bytes *out, int reg, int val, int rt) {
	emit_movimm(out, val, X10_REG);
	emit_subs(out, reg, X10_REG, rt);
}

static void emit_and_ptr32_regptr(t_bytes *out, int regptr, int bits) {
	emit_ldr(out, regptr, X13_REG);
	emit_andimm(out, X13_REG, bits, X13_REG);
	emit_str(out, regptr, X13_REG);
}

static void emit_or_ptr32_regptr(t_bytes *out, int regptr, int bits) {
	emit_ldr(out, regptr, X13_REG);
	emit_orimm(out, X13_REG, bits, X13_REG);
	emit_str(out, regptr, X13_REG);
}

static void emit_or_ptr8_regptr_reg(t_bytes *out, int regptr, int reg) {
	emit_ldrb(out, regptr, X13_REG);
	emit_or(out, X13_REG, reg, X13_REG);
	emit_strb(out, regptr, X13_REG);
}
static void emit_or_ptr8_regptr_imm(t_bytes *out, int regptr, int imm) {
	emit_ldrb(out, regptr, X13_REG);
	emit_orimm(out, X13_REG, imm, X13_REG);
	emit_strb(out, regptr, X13_REG);
}

static void emit_or_ptr32_regptr_reg(t_bytes *out, int regptr, int reg) {
	emit_ldr(out, regptr, X13_REG);
	emit_or(out, X13_REG, reg, X13_REG);
	emit_str(out, regptr, X13_REG);
}

static void emit_and_ptr32_regptr_reg(t_bytes *out, int regptr, int reg) {
	emit_ldr(out, regptr, X13_REG);
	emit_and(out, X13_REG, reg, X13_REG);
	emit_str(out, regptr, X13_REG);
}

#define Z 0
#define NE 1
#define CS 2
#define CC 3 
#define SS 4
#define O 6

static void emit_setc(t_bytes *out, int reg) {
  output_w32(out, 0x1A9F37E0|reg);
}

static void emit_sets(t_bytes *out, int reg) {
  output_w32(out, 0x1A9F57E0|reg);
}

static void emit_setz(t_bytes *out, int reg) {
  output_w32(out, 0x1A9F17E0|reg);
}

static void emit_setnz(t_bytes *out, int reg) {
  output_w32(out, 0x1A9F07E0|reg);
}

static void emit_setnc(t_bytes *out, int reg) {
  output_w32(out, 0x1A9F27E0|reg);
}
static void emit_seto(t_bytes *out, int reg) {
  output_w32(out, 0x1A9F77E0|reg);
}

static void emit_write_ptr32_reg_byte(t_bytes *out, uintptr_t ptr, int reg) {
	emit_movimm(out, (uintptr_t)ptr, X8_REG);

	emit_strb(out, X8_REG, reg);
}

static void emit_lea_reg_reg(t_bytes *out, int reg1, int reg, int scale, int outreg) {
	if (scale == 2)      emit_lsl(out, reg, 1);  // MOV r10, r10, LSL #1 (multiple by 2)
	else if (scale == 4) emit_lsl(out, reg, 2);  // MOV r10, r10, LSL #2 (multiple by 4)
	else if (scale == 8) emit_lsl(out, reg, 3);  // MOV r10, r10, LSL #3 (multiple by 8)
	
	emit_add(out, reg, reg1, X10_REG);
	emit_mov(out,  X10_REG,outreg );
}

static void emit_lea_ptr_reg(t_bytes *out, int ptr, int reg, int scale, int outreg) {
	emit_movimm(out, ptr, X10_REG);
	
	if (scale == 2)      emit_lsl(out, reg, 1);  // MOV r10, r10, LSL #1 (multiple by 2)
	else if (scale == 4) emit_lsl(out, reg, 2);  // MOV r10, r10, LSL #2 (multiple by 4)
	else if (scale == 8) emit_lsl(out, reg, 3);  // MOV r10, r10, LSL #3 (multiple by 8)	
	
	emit_add(out, reg, X10_REG, X10_REG);
	emit_mov(out, X10_REG, outreg);
}

static void emit_lea_ptr_val(t_bytes *out, int ptr, int val, int scale, int outreg) {
	emit_movimm(out, ptr, X10_REG);
	emit_movimm(out, val, X9_REG);
	
	if (scale == 2)      emit_lsl(out, X9_REG, 2);  // MOV r10, r10, LSL #1 (multiple by 2)
	else if (scale == 4) emit_lsl(out, X9_REG, 4);  // MOV r10, r10, LSL #2 (multiple by 4)
	else if (scale == 8) emit_lsl(out, X9_REG, 8);  // MOV r10, r10, LSL #3 (multiple by 8)
	
	emit_add(out, X9_REG, X10_REG, X10_REG);

	emit_mov(out, outreg, X10_REG);
}

static void clear_carry_flag(t_bytes *out) {
  output_w32(out, 0xD53B4200 | X19_REG); /* mrs x19, nzcv */
  output_w32(out, 0x9262FA00 | (X19_REG << 5) | X19_REG); // bic x19, x19, #(1<<29)
  output_w32(out, 0xD51B4200 | X19_REG); // msr    nzcv, x19
}

static void set_carry_flag(t_bytes *out) {
  output_w32(out, 0xD53B4200 | X19_REG); /* mrs x19, nzcv */
  output_w32(out, 0xB2630200 | (X19_REG << 5) | X19_REG); // orr x19, x19, #(1<<29)
  output_w32(out, 0xD51B4200 | X19_REG); // msr    nzcv, x19
}

static void get_flags(int reg, int v);

static void get_carry_flag(t_bytes *out, int reg) {
  get_flags(reg, VALUE_NO_CACHE);
  output_w32(out, 0x121B0000|reg|reg<<5); // and w0, w0, #(1<<5)
  output_w32(out, 0x53057C00|reg|reg<<5); // lsr w0, w0, #5
}

static void emit_read_ptr32_reg(t_bytes *out, uintptr_t ptr, int rs) {
	emit_ptr(out, (uintptr_t)ptr, X10_REG);	
	emit_ldr(out, X10_REG, rs);
}

static void emit_read_ptr64_reg(t_bytes *out, uintptr_t ptr, int rs) {
	emit_ptr(out, (uintptr_t)ptr, X10_REG);	
	emit_ldr64(out, X10_REG, rs);
}

static void emit_read_ptr32_reg_byte(t_bytes *out, uintptr_t ptr, int rs) {
	emit_ptr(out, (uintptr_t)ptr, X8_REG);
	emit_ldrb(out, X8_REG, rs);
}


static void emit_var_copy32(t_bytes *out, uintptr_t from, uintptr_t to) {
	emit_ptr(out, (uintptr_t)from, X7_REG);
	emit_ptr(out, (uintptr_t)to, X7_REG);
}

static void emit_var_copy32_reg(t_bytes *out, int from, int to) {
	emit_str(out, to, from);
}

static void emit_set_ptr_imm(t_bytes *out, uintptr_t ptr, int set) {
	emit_movimm(out, set, X10_REG);
	emit_write_ptr32_reg(out, ptr, X10_REG);
}

static void emit_inc_ptr_imm(t_bytes *out, uintptr_t ptr, int add) {
	emit_read_ptr32_reg(out, ptr, X10_REG);
	if (add > 0) {
		emit_movimm(out, add, X9_REG);
		emit_add(out, X10_REG, X9_REG, X10_REG);
	}
	else {
		emit_movimm(out, add*-1, X9_REG);
		emit_sub(out, X10_REG, X9_REG, X10_REG);
	}
	emit_write_ptr32_reg(out, ptr, X10_REG);
}

static void emit_sub_ptr_imm(t_bytes *out, uintptr_t ptr, int minus) {
	emit_read_ptr32_reg(out, ptr, X10_REG);
	emit_movimm(out, minus, X9_REG);
	emit_sub(out, X10_REG, X9_REG, X10_REG);
	emit_write_ptr32_reg(out, ptr, X10_REG);
}

static void emit_inc_ptr(t_bytes *out, uintptr_t ptr, uintptr_t ptr2) {
	emit_read_ptr32_reg(out, ptr, X2_REG);
	emit_read_ptr32_reg(out, ptr2, X3_REG);
	emit_add(out, X2_REG, X3_REG, X2_REG);
	emit_write_ptr32_reg(out, ptr, X2_REG);
}

static void emit_inc_ptr_reg(t_bytes *out, uintptr_t ptr, uintptr_t ptr2, int reg) {
	emit_read_ptr32_reg(out, ptr, X7_REG);
	emit_read_ptr32_reg(out, ptr2, X9_REG);
	emit_add(out, reg, X9_REG, X7_REG);
}

static void emit_inc_reg(t_bytes *out, uintptr_t ptr, int reg) {
	emit_read_ptr32_reg(out, ptr, X9_REG);
	emit_add(out, reg, X9_REG, reg);
}

static void emit_brk(t_bytes *out) {
  output_w32(out, 0xD4200000);
}

static void save(t_bytes *out) {
  output_w32(out, 0xA9BF53F3);   // stp x19, x20, [sp, #-16]!
  output_w32(out, 0xA9BF5BF5);   // stp x21, x22, [sp, #-16]!
  output_w32(out, 0xA9BF63F7);   // stp x23, x24, [sp, #-16]!
}

static void restore(t_bytes *out) {
  output_w32(out, 0xA8C163F7);   // ldp x23, x24, [sp], #16
  output_w32(out, 0xA8C15BF5);   // ldp x21, x22, [sp], #16
  output_w32(out, 0xA8C153F3);   // ldp x19, x20, [sp], #16
}

static void emit_startfunc(t_bytes *out) {
  output_w32(out, 0xA9BF77FE); // stp lr, fp, [SP, #-16]!
  save(out);
}

static void emit_endfunc(t_bytes *out) {
  restore(out);

	output_w32(out, 0xA8C177FE); // ldp lr, fp, [sp], #16
  output_w32(out, 0xD65F03C0); // ret
}

static void save_call(t_bytes *out) {
  output_w32(out, 0xA9BF0BE1);   // stp x1, x2, [sp, #-16]!
  output_w32(out, 0xA9BF13E3);   // stp x3, x4, [sp, #-16]!
  output_w32(out, 0xA9BF1BE5);   // stp x5, x6, [sp, #-16]!
  output_w32(out, 0xA9BF23E7);   // stp x7, x8, [sp, #-16]!
  output_w32(out, 0xA9BF2BE9);   // stp x9, x10, [sp, #-16]!
  output_w32(out, 0xA9BF33EB);   // stp x11, x12, [sp, #-16]!
  
  #if (defined(_WIN32) || defined(__APPLE__) || defined(__ANDROID__))
  output_w32(out, 0xF81F0FF7);   // str x23, [sp, #-16]!
  #endif
}

static void restore_call(t_bytes *out) {
  #if (defined(_WIN32) || defined(__APPLE__) || defined(__ANDROID__))
  output_w32(out, 0xF84107F7);   // ldr x23, [sp], #16
  #endif

  output_w32(out, 0xA8C133EB);   // ldp x11, x12, [sp], #16
  output_w32(out, 0xA8C12BE9);   // ldp x9, x10, [sp], #16
  output_w32(out, 0xA8C123E7);   // ldp x7, x8, [sp], #16
  output_w32(out, 0xA8C11BE5);   // ldp x5, x6, [sp], #16
  output_w32(out, 0xA8C113E3);   // ldp x3, x4, [sp], #16
  output_w32(out, 0xA8C10BE1);   // ldp x1, x2, [sp], #16
}

static void callR3(t_bytes *out) {
  save_call(out);
	output_w32(out, 0xD63F0060); // blr x3
  restore_call(out);
}
static void callR9(t_bytes *out) {
  save_call(out);
	output_w32(out, 0xD63F0120); // blr x9
  restore_call(out);
}
static void callR7(t_bytes *out) {
  save_call(out);
	output_w32(out, 0xD63F00E0); // blr x7
  restore_call(out);
}
static void callR6(t_bytes *out) {
  save_call(out);
	output_w32(out, 0xD63F00C0); // blr x6
  restore_call(out);
}
static void callR8(t_bytes *out) {
  save_call(out);
	output_w32(out, 0xD63F0100); // blr x8
  restore_call(out);
}

//-----------------------------------------------------------------------------
//   Shifting macros
//-----------------------------------------------------------------------------
#define SET_NZCV(sign) { \
	JIT_COMMENT("SET_NZCV"); \
	output_w32(g_out, 0xD53B4200 | X1_REG); /* mrs x1, nzcv */ \
	flags_ptr(y_reg, VALUE); \
	output_w32(g_out, 0xD358FC00 | (X1_REG << 5) | X1_REG); /* lsr x1, x1, #0x18 */\
	output_w32(g_out, 0x927C0C00 | (X1_REG << 5) | X1_REG); /* and x1, x1, #0xf0 */ \
	output_w32(g_out, 0x92400D00 | (X9_REG << 5) | X9_REG); /* and x9, x9, #0xf */ \
	emit_or64(g_out, X1_REG, y_reg, X1_REG); \
	emit_writeBYTE_ptr32_regptrTO_regFROM(g_out, CACHED_PTR(flags_ptr(X0_REG, ADDRESS)), X1_REG); \
}

#define SET_NZC { \
	JIT_COMMENT("SET_NZC"); \
	output_w32(g_out, 0xD53B4200 | X1_REG); /* mrs x1, nzcv */ \
	flags_ptr(y_reg, VALUE); \
	output_w32(g_out, 0xD358FC00 | (X1_REG << 5) | X1_REG); /* lsr x1, x1, #0x18 */\
	output_w32(g_out, 0x927A0400 | (X1_REG << 5) | X1_REG); /* and x1, x1, #0xc0 */ \
	if (cf_change) {  output_w32(g_out, 0xAA000000 | (X5_REG << 16) | (X5_REG << 10) | (X1_REG << 5) | X1_REG); /* orr x1, x1, x5, lsl #5  - x5 == rcf */ }   \
  output_w32(g_out, (cf_change ? 0x92401100 : 0x92401500) | (X9_REG << 5) | X9_REG); \
	emit_or64(g_out, X1_REG, y_reg, X1_REG); \
	emit_writeBYTE_ptr32_regptrTO_regFROM(g_out, CACHED_PTR(flags_ptr(X0_REG, ADDRESS)), X1_REG); \
}

#define SET_NZC_SHIFTS_ZERO(cf) { \
	JIT_COMMENT("SET_NZC_SHIFTS_ZERO"); \
	flags_ptr(R3, VALUE); \
	emit_and_ptr32_regptr(g_out, CACHED_PTR(flags_ptr(X1_REG, ADDRESS)), 0x1F); \
	if(cf) \
	{ \
		emit_lsl(g_out, rcf_reg, 5); \
		emit_orimm(g_out,rcf_reg, (1<<6), rcf_reg); \
		emit_or_ptr32_regptr_reg(g_out, CACHED_PTR(flags_ptr(X1_REG, ADDRESS)), rcf_reg); \
	} \
	else \
		emit_or_ptr32_regptr(g_out, CACHED_PTR(flags_ptr(X1_REG, ADDRESS)), (1<<6)); \
}

#define SET_NZ(clear_cv) { \
	output_w32(g_out, 0xD53B4200 | X1_REG); /* mrs x1, nzcv */ \
	flags_ptr(y_reg, VALUE); \
	output_w32(g_out, 0xD358FC00 | (X1_REG << 5) | X1_REG); /* lsr x1, x1, #0x18 */ \
	output_w32(g_out, 0x927A0400 | (X1_REG << 5) | X1_REG); /* and x1, x1, #0xc0 */ \
  output_w32(g_out, (clear_cv ? 0x92400D00 : 0x92401500) | (X9_REG << 5) | X9_REG); \
	emit_or64(g_out, X1_REG, y_reg, X1_REG); \
	emit_writeBYTE_ptr32_regptrTO_regFROM(g_out, CACHED_PTR(flags_ptr(X0_REG, ADDRESS)), X1_REG); \
}

#define SET_N { \
	output_w32(g_out, 0xD53B4200 | X1_REG); /* mrs x1, nzcv */ \
	flags_ptr(y_reg, VALUE); \
	output_w32(g_out, 0xD358FC00 | (X1_REG << 5) | X1_REG); /* lsr x1, x1, #0x18 */\
	output_w32(g_out, 0x92790000 | (X1_REG << 5) | X1_REG); /* and x1, x1, #0x80 */ \
	output_w32(g_out, 0x92401900 | (X9_REG << 5) | X9_REG); /* and x9, x9, #0x7f */ \
	emit_or64(g_out, R1, y_reg, R1); \
	emit_writeBYTE_ptr32_regptrTO_regFROM(g_out, CACHED_PTR(flags_ptr(X0_REG, ADDRESS)), X1_REG); \
}

#define SET_Z { \
	output_w32(g_out, 0xD53B4200 | X1_REG);/* mrs x1, nzcv */ \
	flags_ptr(y_reg, VALUE); \
	output_w32(g_out, 0xD358FC21); /* lsr x1, x1, #0x18 */\
	output_w32(g_out, 0xD358FC00 | (X1_REG << 5) | X1_REG); /* and x1, x1, #0x40 */  \
	emit_andimm(g_out, X9_REG, 0xbf, X9_REG); /* and sb, sb, #0xbf */ \
	emit_or64(g_out, X1_REG, y_reg, X1_REG); \
	emit_writeBYTE_ptr32_regptrTO_regFROM(g_out, CACHED_PTR(flags_ptr(X0_REG, ADDRESS)), X1_REG); \
}

#define SET_Q { \
  flags_ptr(y_reg, VALUE); \
	emit_seto(g_out, y_reg); \
	emit_lsl(g_out, y_reg, 3); \
	emit_or_ptr32_regptr_reg(g_out, CACHED_PTR(flags_ptr(X1_REG, ADDRESS)), y_reg); \
}

#define GET_CARRY(invert) { \
	flags_ptr(X2_REG, VALUE); \
	uint64_t setb=genlabel(); \
	uint64_t done=genlabel(); \
		output_w32(g_out, 0x721B0040 | (X2_REG << 5)); /* ands w2, w2, #0x20 */ \
		emit_branch_label(g_out, setb, 0x1); \
		clear_carry_flag(g_out); \
		emit_branch_label(g_out, done, 0xE); \
		emit_label(g_out, setb); \
		set_carry_flag(g_out); \
		emit_label(g_out, done); \
}
