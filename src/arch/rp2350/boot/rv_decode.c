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
 * \file rv_decode.c
 * \brief Effective address of the memory access of an RV32IMAC instruction.
 *
 * Every field position below was checked against the output of
 * riscv64-elf-as, not taken from memory. The host tests in
 * src/arch/rp2350/test/test_rv_decode.c carry the assembled encodings they
 * came from.
 */

#include "rv_decode.h"

/* The 32-bit opcodes that access memory. */
#define OPCODE_LOAD  UINT32_C(0x03)
#define OPCODE_STORE UINT32_C(0x23)
#define OPCODE_AMO   UINT32_C(0x2f)

/* funct3 of the word-wide atomics. A value of 3 is doubleword, i.e. RV64. */
#define FUNCT3_AMO_W UINT32_C(2)

/*!
 * \fn uint32_t signExtend(uint32_t value, uint32_t bits)
 * \brief Sign-extends the low bits of a value to 32 bits.
 * \param value The value to extend.
 * \param bits The number of significant low bits of value.
 * \return The sign-extended value.
 */
static uint32_t signExtend(uint32_t value, uint32_t bits)
{
	uint32_t sign = UINT32_C(1) << (bits - 1);

	return ((value & ((sign << 1) - 1)) ^ sign) - sign;
}

/*!
 * \fn bool effectiveAddress32(const stackedContext_t *context, uint32_t insn,
 *                             uint32_t *effectiveAddress)
 * \brief Computes the accessed address of a 32-bit instruction.
 * \param context The context saved by the trap stub.
 * \param insn The instruction.
 * \param effectiveAddress Where the address is written on success.
 * \return true when the instruction was decoded, false otherwise.
 */
static bool effectiveAddress32(const stackedContext_t *context, uint32_t insn,
                               uint32_t *effectiveAddress)
{
	uint32_t funct3 = (insn >> 12) & UINT32_C(0x7);
	uint32_t offset;

	switch (insn & UINT32_C(0x7f)) {
	case OPCODE_LOAD:
		// LB, LH, LW, LBU, LHU. A funct3 of 3 or 6 is LD or LWU, i.e. RV64.
		if (funct3 == 3 || funct3 > 5) {
			return false;
		}
		offset = signExtend(insn >> 20, 12);
		break;
	case OPCODE_STORE:
		// SB, SH, SW. A funct3 of 3 is SD, i.e. RV64.
		if (funct3 > 2) {
			return false;
		}
		offset = signExtend((((insn >> 25) & UINT32_C(0x7f)) << 5)
		                    | ((insn >> 7) & UINT32_C(0x1f)), 12);
		break;
	case OPCODE_AMO:
		// LR.W, SC.W and the AMOs address rs1 with no offset.
		if (funct3 != FUNCT3_AMO_W) {
			return false;
		}
		offset = 0;
		break;
	default:
		/*
		 * Also rejects the 48-bit and 64-bit encodings, whose low 7 bits
		 * are 0x3f and 0x7f, and the floating-point loads and stores,
		 * which Hazard3 traps as illegal instructions before any access
		 * fault since it implements neither F nor D.
		 */
		return false;
	}
	*effectiveAddress = contextReadRegister(context,
	                                        (insn >> 15) & UINT32_C(0x1f))
	                    + offset;
	return true;
}

/*!
 * \fn bool effectiveAddress16(const stackedContext_t *context, uint32_t insn,
 *                             uint32_t *effectiveAddress)
 * \brief Computes the accessed address of a compressed instruction.
 *
 * Compressed offsets are zero-extended, and their bits are scattered through
 * the encoding in an order that differs per instruction.
 *
 * \param context The context saved by the trap stub.
 * \param insn The instruction, in the low 16 bits.
 * \param effectiveAddress Where the address is written on success.
 * \return true when the instruction was decoded, false otherwise.
 */
static bool effectiveAddress16(const stackedContext_t *context, uint32_t insn,
                               uint32_t *effectiveAddress)
{
	uint32_t funct3 = (insn >> 13) & UINT32_C(0x7);
	uint32_t rs1;
	uint32_t offset;

	switch (insn & UINT32_C(0x3)) {
	case 0:
		// Quadrant 0 addresses through one of x8 to x15.
		rs1 = 8 + ((insn >> 7) & UINT32_C(0x7));
		switch (funct3) {
		case 2:	// C.LW
		case 6:	// C.SW
			offset = (((insn >> 10) & UINT32_C(0x7)) << 3)
			       | (((insn >> 6) & UINT32_C(0x1)) << 2)
			       | (((insn >> 5) & UINT32_C(0x1)) << 6);
			break;
		case 4:	// Zcb
			switch ((insn >> 10) & UINT32_C(0x7)) {
			case 0:	// C.LBU
			case 2:	// C.SB
				offset = (((insn >> 5) & UINT32_C(0x1)) << 1)
				       | ((insn >> 6) & UINT32_C(0x1));
				break;
			case 1:	// C.LHU when bit 6 is clear, C.LH when it is set
				offset = ((insn >> 5) & UINT32_C(0x1)) << 1;
				break;
			case 3:	// C.SH, which requires bit 6 clear
				if ((insn >> 6) & UINT32_C(0x1)) {
					return false;
				}
				offset = ((insn >> 5) & UINT32_C(0x1)) << 1;
				break;
			default:
				return false;
			}
			break;
		default:
			/*
			 * C.ADDI4SPN accesses no memory, and the remaining funct3
			 * values are the floating-point and RV64 widths.
			 */
			return false;
		}
		break;
	case 2:
		// Quadrant 2 addresses through sp.
		rs1 = RV_REG_SP;
		switch (funct3) {
		case 2:	// C.LWSP
			offset = (((insn >> 4) & UINT32_C(0x7)) << 2)
			       | (((insn >> 12) & UINT32_C(0x1)) << 5)
			       | (((insn >> 2) & UINT32_C(0x3)) << 6);
			break;
		case 6:	// C.SWSP
			offset = (((insn >> 9) & UINT32_C(0xf)) << 2)
			       | (((insn >> 7) & UINT32_C(0x3)) << 6);
			break;
		default:
			// Includes Zcmp, funct3 5. See rv_decode.h.
			return false;
		}
		break;
	default:
		// Quadrant 1 holds no memory access.
		return false;
	}
	*effectiveAddress = contextReadRegister(context, rs1) + offset;
	return true;
}

bool rv_effective_address(const stackedContext_t *context, uint16_t lo,
                          uint16_t hi, uint32_t *effectiveAddress)
{
	if (rv_insn_is_32bit(lo)) {
		return effectiveAddress32(context,
		                          (uint32_t)lo | ((uint32_t)hi << 16),
		                          effectiveAddress);
	}
	return effectiveAddress16(context, lo, effectiveAddress);
}
