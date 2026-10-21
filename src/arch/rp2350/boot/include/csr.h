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
 * \file csr.h
 * \brief Control and status registers of the Hazard3 core of the RP2350.
 *
 * As in rp2350.h, the constants are transcribed from the pico-sdk register
 * header src/rp2350/hardware_regs/include/hardware/regs/rvcsr.h under their
 * vendor names, so that checking them is a grep and not a reading of the
 * specification. That matters most for the pmpcfg permission bits, which
 * erratum RP2350-E6 transposes: see pmp.h.
 *
 * The accessors name their register the way the assembler does, which keeps
 * the mnemonic readable. The CSR numbers below are for the few places that
 * need a number instead, and for the Hazard3 custom registers the assembler
 * does not know.
 *
 * The constants are plain literals rather than UINT32_C(), and the accessors
 * are hidden from the assembler, so that the trap stub can include this
 * header instead of restating the bit positions it tests.
 */

#ifndef CSR_H
#define CSR_H

#if !defined(__ASSEMBLER__)
#include <stdint.h>
#endif

/* --- rvcsr.h: register numbers ------------------------------------------ */

#define RVCSR_MSTATUS_OFFSET  0x00000300
#define RVCSR_MIE_OFFSET      0x00000304
#define RVCSR_MTVEC_OFFSET    0x00000305
#define RVCSR_MSCRATCH_OFFSET 0x00000340
#define RVCSR_MEPC_OFFSET     0x00000341
#define RVCSR_MCAUSE_OFFSET   0x00000342
#define RVCSR_MTVAL_OFFSET    0x00000343
#define RVCSR_MIP_OFFSET      0x00000344
#define RVCSR_PMPCFG0_OFFSET  0x000003a0
#define RVCSR_PMPCFG1_OFFSET  0x000003a1
#define RVCSR_PMPADDR0_OFFSET 0x000003b0

/* --- rvcsr.h: mstatus --------------------------------------------------- */

#define RVCSR_MSTATUS_MIE_BITS  0x00000008
#define RVCSR_MSTATUS_MIE_LSB   3
#define RVCSR_MSTATUS_MPIE_BITS 0x00000080
#define RVCSR_MSTATUS_MPIE_LSB  7
#define RVCSR_MSTATUS_MPP_BITS  0x00001800
#define RVCSR_MSTATUS_MPP_LSB   11

/*!
 * \brief The two privilege modes mstatus.MPP can hold.
 *
 * Hazard3 implements M-mode and U-mode only; any other value written to MPP
 * rounds to one of these two.
 */
#define RVCSR_MSTATUS_MPP_VALUE_U 0
#define RVCSR_MSTATUS_MPP_VALUE_M 3

/* --- rvcsr.h: mtvec ---------------------------------------------------- */

#define RVCSR_MTVEC_BASE_BITS 0xfffffffc
#define RVCSR_MTVEC_BASE_LSB  2
#define RVCSR_MTVEC_MODE_BITS 0x00000003
#define RVCSR_MTVEC_MODE_LSB  0

/*!
 * \brief mtvec.MODE values.
 *
 * Pip uses direct mode: every trap enters one stub, which demuxes on mcause.
 * Vectored mode only dispatches the three interrupt causes and still funnels
 * every exception to the base, so it would buy nothing and cost a 64-byte
 * aligned table.
 */
#define RVCSR_MTVEC_MODE_VALUE_DIRECT   0
#define RVCSR_MTVEC_MODE_VALUE_VECTORED 1

/* --- rvcsr.h: mcause --------------------------------------------------- */

#define RVCSR_MCAUSE_INTERRUPT_BITS 0x80000000
#define RVCSR_MCAUSE_INTERRUPT_LSB  31
#define RVCSR_MCAUSE_CODE_BITS      0x0000000f
#define RVCSR_MCAUSE_CODE_LSB       0

#define RVCSR_MCAUSE_CODE_VALUE_INSTR_ALIGN   0x0
#define RVCSR_MCAUSE_CODE_VALUE_INSTR_FAULT   0x1
#define RVCSR_MCAUSE_CODE_VALUE_ILLEGAL_INSTR 0x2
#define RVCSR_MCAUSE_CODE_VALUE_BREAKPOINT    0x3
#define RVCSR_MCAUSE_CODE_VALUE_LOAD_ALIGN    0x4
#define RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT    0x5
#define RVCSR_MCAUSE_CODE_VALUE_STORE_ALIGN   0x6
#define RVCSR_MCAUSE_CODE_VALUE_STORE_FAULT   0x7
#define RVCSR_MCAUSE_CODE_VALUE_U_ECALL       0x8
#define RVCSR_MCAUSE_CODE_VALUE_M_ECALL       0xb

/* --- rvcsr.h: pmpcfg byte fields --------------------------------------- */

/*!
 * \brief Field positions inside a pmpcfg byte, for region 0 of pmpcfg0.
 *
 * Every pmpcfg byte has this layout. Note R=2 and X=0: erratum RP2350-E6
 * transposes them with respect to the specification, and these are the
 * silicon positions. pmp.h derives its PMPCFG_* encoding from them.
 */
#define RVCSR_PMPCFG0_R0_L_BITS 0x00000080
#define RVCSR_PMPCFG0_R0_L_LSB  7
#define RVCSR_PMPCFG0_R0_A_BITS 0x00000018
#define RVCSR_PMPCFG0_R0_A_LSB  3
#define RVCSR_PMPCFG0_R0_R_BITS 0x00000004
#define RVCSR_PMPCFG0_R0_R_LSB  2
#define RVCSR_PMPCFG0_R0_W_BITS 0x00000002
#define RVCSR_PMPCFG0_R0_W_LSB  1
#define RVCSR_PMPCFG0_R0_X_BITS 0x00000001
#define RVCSR_PMPCFG0_R0_X_LSB  0

#define RVCSR_PMPCFG0_R0_A_VALUE_OFF   0x0
#define RVCSR_PMPCFG0_R0_A_VALUE_NA4   0x2
#define RVCSR_PMPCFG0_R0_A_VALUE_NAPOT 0x3

/* --- Hazard3 custom registers ------------------------------------------ */

/*!
 * \brief Hazard3 custom CSR numbers, for the registers GNU as does not name.
 *
 * h3.pmpcfgm0 makes a PMP region apply to M-mode without locking it, which
 * is the opposite of what Pip wants and must never be written: see pmp.h.
 * The Xh3irq registers belong to the interrupt controller and are unused
 * until interrupts are brought up.
 */
#define RVCSR_PMPCFGM0_OFFSET   0x00000bd0
#define RVCSR_MEIEA_OFFSET      0x00000be0
#define RVCSR_MEIPA_OFFSET      0x00000be1
#define RVCSR_MEIFA_OFFSET      0x00000be2
#define RVCSR_MEIPRA_OFFSET     0x00000be3
#define RVCSR_MEINEXT_OFFSET    0x00000be4
#define RVCSR_MEICONTEXT_OFFSET 0x00000be5

/* --- Accessors --------------------------------------------------------- */

#if !defined(__ASSEMBLER__)

/*!
 * \brief Reads the CSR named \p name.
 *
 * \p name is an assembler CSR mnemonic, not a number: CSR_READ(mcause).
 */
#define CSR_READ(name)                                                        \
	__extension__ ({                                                      \
		uint32_t csrValue_;                                            \
		__asm__ volatile ("csrr %0, " #name                            \
		                  : "=r" (csrValue_));                         \
		csrValue_;                                                     \
	})

/*! \brief Writes \p value to the CSR named \p name. */
#define CSR_WRITE(name, value)                                                \
	__asm__ volatile ("csrw " #name ", %0"                                 \
	                  :                                                    \
	                  : "r" ((uint32_t) (value))                           \
	                  : "memory")

/*! \brief Sets in the CSR named \p name the bits set in \p value. */
#define CSR_SET(name, value)                                                  \
	__asm__ volatile ("csrs " #name ", %0"                                 \
	                  :                                                    \
	                  : "r" ((uint32_t) (value))                           \
	                  : "memory")

/*! \brief Clears in the CSR named \p name the bits set in \p value. */
#define CSR_CLEAR(name, value)                                                \
	__asm__ volatile ("csrc " #name ", %0"                                 \
	                  :                                                    \
	                  : "r" ((uint32_t) (value))                           \
	                  : "memory")

/*!
 * \brief Writes \p value to the CSR named \p name and returns its old value.
 */
#define CSR_READ_WRITE(name, value)                                           \
	__extension__ ({                                                      \
		uint32_t csrValue_;                                            \
		__asm__ volatile ("csrrw %0, " #name ", %1"                    \
		                  : "=r" (csrValue_)                           \
		                  : "r" ((uint32_t) (value))                   \
		                  : "memory");                                 \
		csrValue_;                                                     \
	})

/*!
 * \brief Orders the preceding memory accesses before the following ones.
 *
 * This is the substitute for the ARM target's DSB.
 */
static inline void fenceRw(void)
{
	__asm__ volatile ("fence rw, rw" ::: "memory");
}

/*!
 * \brief Makes the preceding stores visible to instruction fetch.
 *
 * Required after a PMP write that changes an executable region, because
 * Hazard3 has a prefetch buffer. This is the substitute for the ARM target's
 * ISB, which fenceRw() alone does not provide.
 */
static inline void fenceI(void)
{
	__asm__ volatile ("fence.i" ::: "memory");
}

#endif /* !__ASSEMBLER__ */

#endif /* CSR_H */
