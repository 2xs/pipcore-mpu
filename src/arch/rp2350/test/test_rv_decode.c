/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2025)                */
/*  Copyright (C) 2020-2025 Orange                                             */
/*                                                                             */
/*  This software is a computer program whose purpose is to run a minimal,     */
/*  hypervisor relying on proven properties such as memory isolation.          */
/*                                                                             */
/*  This software is governed by the CeCILL license under French law and       */
/*  abiding by the rules of distribution of free software.  You can  use,      */
/*  modify and/ or redistribute the software under the terms of the CeCILL     */
/*  license as circulated by CEA, CNRS and INRIA at the following URL          */
/*  "http://www.cecill.info".                                                  */
/*                                                                             */
/*  As a counterpart to the access to the source code and  rights to copy,     */
/*  modify and redistribute granted by the license, users are provided only    */
/*  with a limited warranty  and the software's author,  the holder of the     */
/*  economic rights,  and the successive licensors  have only  limited         */
/*  liability.                                                                 */
/*                                                                             */
/*  In this respect, the user's attention is drawn to the risks associated     */
/*  with loading,  using,  modifying and/or developing or reproducing the      */
/*  software by the user in light of its specific status of free software,     */
/*  that may mean  that it is complicated to manipulate,  and  that  also      */
/*  therefore means  that it is reserved for developers  and  experienced      */
/*  professionals having in-depth computer knowledge. Users are therefore      */
/*  encouraged to load and test the software's suitability as regards their    */
/*  requirements in conditions enabling the security of their systems and/or   */
/*  data to be ensured and,  more generally, to use and operate it in the      */
/*  same conditions as regards security.                                       */
/*                                                                             */
/*  The fact that you are presently reading this means that you have had       */
/*  knowledge of the CeCILL license and that you accept its terms.             */
/*******************************************************************************/

/*!
 * \file test_rv_decode.c
 * \brief Host unit test of the instruction decoder (rung 0).
 *
 * Every encoding below was produced by
 *
 *     riscv64-elf-as -march=rv32imac_zicsr_zifencei_zcb -mabi=ilp32
 *
 * and read back with "objdump -d -M no-aliases", so the base register and
 * the offset in each case are the assembler's, not a hand derivation. The
 * expected address is then computed here from them, which is what catches a
 * decoder that picks the wrong register or scales an immediate wrongly.
 */

#include "rv_decode.h"
#include "test.h"

/*!
 * \struct decodeCase_t
 * \brief One instruction the decoder must handle.
 */
typedef struct decodeCase_s {
	const char *name;	/*!< The instruction, as the disassembler prints it. */
	uint32_t insn;		/*!< Its encoding, halfwords in little-endian order. */
	uint32_t rs1;		/*!< The base register it addresses through. */
	int32_t offset;		/*!< The offset it adds to that register. */
} decodeCase_t;

static const decodeCase_t decodeCases[] = {
	// I-type loads, including both extremes of the 12-bit immediate.
	{ "lw a0,16(s0)",            0x01042503,  8,    16 },
	{ "lw t0,-1(ra)",            0xfff0a283,  1,    -1 },
	{ "lw a5,0(zero)",           0x00002783,  0,     0 },
	{ "lb a1,-4(sp)",            0xffc10583,  2,    -4 },
	{ "lb a4,4(a5)",             0x00478703, 15,     4 },
	{ "lh a2,2047(t0)",          0x7ff29603,  5,  2047 },
	{ "lh a6,-6(a7)",            0xffa89803, 17,    -6 },
	{ "lbu a0,1(a1)",            0x0015c503, 11,     1 },
	{ "lbu a3,-2048(t1)",        0x80034683,  6, -2048 },
	{ "lhu a4,0(s2)",            0x00095703, 18,     0 },
	{ "lhu a2,-3(a3)",           0xffd6d603, 13,    -3 },
	// S-type stores, whose immediate is split across two fields.
	{ "sw a5,32(s1)",            0x02f4a023,  9,    32 },
	{ "sw t1,2047(t2)",          0x7e63afa3,  7,  2047 },
	{ "sb t3,-2048(t4)",         0x81ce8023, 29, -2048 },
	{ "sb a6,-1(s2)",            0xff090fa3, 18,    -1 },
	{ "sh s2,7(s3)",             0x012993a3, 19,     7 },
	{ "sh a7,1234(s3)",          0x4d199923, 19,  1234 },
	// Atomics address rs1 with no offset.
	{ "lr.w t2,(a2)",            0x100623af, 12,     0 },
	{ "sc.w t3,t4,(a3)",         0x19d6ae2f, 13,     0 },
	{ "amoadd.w t5,t6,(a4)",     0x01f72f2f, 14,     0 },
	{ "amoswap.w a0,a1,(a2)",    0x08b6252f, 12,     0 },
	// Compressed word accesses through x8 to x15, offsets 0 to 124 by 4.
	{ "c.lw a0,16(s0)",          0x00004808,  8,    16 },
	{ "c.lw a0,4(s0)",           0x00004048,  8,     4 },
	{ "c.lw a1,0(a2)",           0x0000420c, 12,     0 },
	{ "c.lw a2,124(a5)",         0x00005ff0, 15,   124 },
	{ "c.sw a5,32(s1)",          0x0000d09c,  9,    32 },
	{ "c.sw a1,124(a2)",         0x0000de6c, 12,   124 },
	{ "c.sw a3,8(s1)",           0x0000c494,  9,     8 },
	// Compressed word accesses through sp, offsets 0 to 252 by 4.
	{ "c.lwsp a0,8(sp)",         0x00004522,  2,     8 },
	{ "c.lwsp t0,252(sp)",       0x000052fe,  2,   252 },
	{ "c.swsp a1,12(sp)",        0x0000c62e,  2,    12 },
	{ "c.swsp ra,0(sp)",         0x0000c006,  2,     0 },
	// Zcb, which a third-party toolchain may emit.
	{ "c.lbu a0,1(s0)",          0x00008048,  8,     1 },
	{ "c.lbu a1,3(a2)",          0x0000826c, 12,     3 },
	{ "c.lhu a2,2(s1)",          0x000084b0,  9,     2 },
	{ "c.lhu a3,0(a4)",          0x00008714, 14,     0 },
	{ "c.lh a4,2(a0)",           0x00008578, 10,     2 },
	{ "c.sb a3,3(s0)",           0x00008874,  8,     3 },
	{ "c.sb a4,0(a1)",           0x00008998, 11,     0 },
	{ "c.sh a4,2(s1)",           0x00008cb8,  9,     2 },
	{ "c.sh a5,0(a3)",           0x00008e9c, 13,     0 },
};

/*!
 * \struct rejectCase_t
 * \brief One instruction the decoder must refuse to decode.
 */
typedef struct rejectCase_s {
	const char *name;	/*!< The instruction, as text. */
	uint32_t insn;		/*!< Its encoding. */
} rejectCase_t;

static const rejectCase_t rejectCases[] = {
	/*
	 * Zcmp. These perform several stack accesses each, so one effective
	 * address cannot describe them and the fault must be propagated to the
	 * parent partition rather than refilled. The project toolchain leaves
	 * Zcmp out of -march, and partition binaries must do the same.
	 */
	{ "cm.push {ra,s0-s2},-32",  0x0000b876 },
	{ "cm.pop {ra,s0-s2},32",    0x0000ba76 },
	{ "cm.popret {ra},16",       0x0000be42 },
	// Compressed instructions that touch no memory.
	{ "c.addi4spn a0,sp,16",     0x00000808 },
	{ "c.mv a0,a1",              0x0000852e },
	{ "c.li a0,5",               0x00004515 },
	{ "c.jr a0",                 0x00008502 },
	// Uncompressed instructions that touch no memory.
	{ "fence iorw,iorw",         0x0ff0000f },
	{ "csrrs a0,mstatus,zero",   0x30002573 },
	/*
	 * RV64-only widths, assembled with -march=rv64imac. Hazard3 traps these
	 * as illegal instructions, so the decoder never has to guess a width it
	 * cannot support.
	 */
	{ "ld a0,16(s0)",            0x01043503 },
	{ "sd a5,32(s1)",            0x02f4b023 },
	{ "lwu a1,8(s2)",            0x00896583 },
	{ "amoadd.d a2,a3,(a4)",     0x00d7362f },
	// An encoding longer than 32 bits, whose low five bits are all set.
	{ "a 48-bit encoding",       0x0000401f },
};

/*!
 * \fn uint32_t registerValue(uint32_t reg)
 * \brief The value the test puts in x<reg>.
 *
 * Distinct per register, so a decoder reading the wrong one is caught, and
 * far enough from zero that a negative offset does not wrap.
 *
 * \param reg A register number in [0, 31].
 * \return The value of x<reg>.
 */
static uint32_t registerValue(uint32_t reg)
{
	if (reg == 0) {
		return 0;	// x0 is hardwired zero
	}
	return 0x20001000 + reg * 0x40;
}

/*!
 * \fn void fillContext(stackedContext_t *context)
 * \brief Fills a context with the test's register values.
 * \param context The context to fill.
 */
static void fillContext(stackedContext_t *context)
{
	context->isBasicFrame = 1;
	context->pipflags = 0;
	context->mepc = 0x10000100;
	context->mstatus = 0;
	for (uint32_t reg = 1; reg <= CONTEXT_REGS_NB; reg++) {
		context->regs[reg - 1] = registerValue(reg);
	}
}

/*!
 * \fn void testContextReadRegister(void)
 * \brief Checks the x0 special case and the x1 to x31 mapping.
 */
static void testContextReadRegister(void)
{
	stackedContext_t context;

	fillContext(&context);
	CHECK(contextReadRegister(&context, 0), 0);
	CHECK(contextReadRegister(&context, 1), registerValue(1));
	CHECK(contextReadRegister(&context, 2), registerValue(2));
	CHECK(contextReadRegister(&context, 31), registerValue(31));
}

/*!
 * \fn void testInstructionWidth(void)
 * \brief Checks the test the fault handler uses before fetching mepc + 2.
 */
static void testInstructionWidth(void)
{
	CHECK(rv_insn_is_32bit(0x2503), 1);	// low halfword of lw a0,16(s0)
	CHECK(rv_insn_is_32bit(0x4808), 0);	// c.lw a0,16(s0)
	CHECK(rv_insn_is_32bit(0x0808), 0);	// c.addi4spn, quadrant 0
	CHECK(rv_insn_is_32bit(0x4515), 0);	// c.li, quadrant 1
	CHECK(rv_insn_is_32bit(0xb876), 0);	// cm.push, quadrant 2
}

/*!
 * \fn void testDecodedAddresses(void)
 * \brief Checks the effective address of every supported encoding.
 */
static void testDecodedAddresses(void)
{
	stackedContext_t context;

	fillContext(&context);
	for (unsigned i = 0; i < sizeof(decodeCases) / sizeof(*decodeCases); i++) {
		const decodeCase_t *c = &decodeCases[i];
		uint32_t expected = registerValue(c->rs1) + (uint32_t)c->offset;
		uint32_t address = 0xdeadbeef;
		bool decoded = rv_effective_address(&context,
		                                    (uint16_t)c->insn,
		                                    (uint16_t)(c->insn >> 16),
		                                    &address);

		CHECK_AT(c->name, decoded, 1);
		CHECK_AT(c->name, address, expected);
	}
}

/*!
 * \fn void testRejectedEncodings(void)
 * \brief Checks that unsupported encodings are reported, not guessed at.
 */
static void testRejectedEncodings(void)
{
	stackedContext_t context;

	fillContext(&context);
	for (unsigned i = 0; i < sizeof(rejectCases) / sizeof(*rejectCases); i++) {
		const rejectCase_t *c = &rejectCases[i];
		uint32_t address = 0xdeadbeef;
		bool decoded = rv_effective_address(&context,
		                                    (uint16_t)c->insn,
		                                    (uint16_t)(c->insn >> 16),
		                                    &address);

		CHECK_AT(c->name, decoded, 0);
		// A refused decode must leave the output alone.
		CHECK_AT(c->name, address, 0xdeadbeef);
	}
}

/*!
 * \fn void testAddressWrapsAround(void)
 * \brief Checks that the address arithmetic wraps like the hardware's.
 *
 * The address is computed modulo 2^32, so a positive offset from the top of
 * the address space lands at the bottom. Such an access is a genuine fault,
 * but it is the virtual MPU lookup that must decide that, not the decoder.
 */
static void testAddressWrapsAround(void)
{
	stackedContext_t context;
	uint32_t address = 0;

	fillContext(&context);
	context.regs[8 - 1] = 0xfffffff8;	// s0
	CHECK(rv_effective_address(&context, 0x4808, 0, &address), 1);
	CHECK(address, 0x00000008);		// c.lw a0,16(s0)

	context.regs[1 - 1] = 0x00000000;	// ra
	CHECK(rv_effective_address(&context, 0xa283, 0xfff0, &address), 1);
	CHECK(address, 0xffffffff);		// lw t0,-1(ra)
}

int main(void)
{
	testContextReadRegister();
	testInstructionWidth();
	testDecodedAddresses();
	testRejectedEncodings();
	testAddressWrapsAround();
	return testReport("test_rv_decode");
}
