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
 * \file context.h
 * \brief Saved partition context for the Hazard3 core of the RP2350.
 *
 * Hazard3 has no FPU, so the basicFrame_t / extendedFrame_t duality of the
 * ARM target disappears and there is a single frame layout. Nothing is
 * stacked by hardware either, so every field below is written by the trap
 * stub and the saved sp is the pre-trap sp, with no frame-size arithmetic to
 * undo.
 *
 * This header is pure data, so it is also compiled by the host unit tests
 * (src/arch/rp2350/test).
 */

#ifndef CONTEXT_H
#define CONTEXT_H

/*! \brief Number of saved general-purpose registers: x1 to x31. */
#define CONTEXT_REGS_NB 31

/*!
 * \brief Indices into stackedContext_t.regs of the registers the kernel
 *        reads or writes by name.
 *
 * The syscall ABI is the Linux/RISC-V one: service number in a7, arguments
 * in a0 to a4, return value written back to the saved a0.
 */
#define RV_REG_RA 1
#define RV_REG_SP 2
#define RV_REG_A0 10
#define RV_REG_A1 11
#define RV_REG_A2 12
#define RV_REG_A3 13
#define RV_REG_A4 14
#define RV_REG_A7 17

/*
 * Byte offsets into stackedContext_t, for trap_entry.S, which cannot see the
 * struct. The layout check at the end of this header asserts that each one
 * still matches what the compiler lays out, so the stub and the C code cannot
 * drift apart silently.
 */
#define CONTEXT_OFFSET_IS_BASIC_FRAME 0
#define CONTEXT_OFFSET_PIPFLAGS       4
#define CONTEXT_OFFSET_REGS           8
#define CONTEXT_OFFSET_MEPC           132
#define CONTEXT_OFFSET_MSTATUS        136
#define CONTEXT_SIZE                  140

/*!
 * \brief The byte offset of x<n> within a saved context, for n in [1, 31].
 *
 * Encodes the regs[n - 1] == x<n> correspondence in one place, so the trap
 * stub can name registers numerically and stay auditable against it.
 */
#define CONTEXT_REG_OFFSET(n) (CONTEXT_OFFSET_REGS + ((n) - 1) * 4)

#if !defined(__ASSEMBLER__)

#include <stddef.h>
#include <stdint.h>

/*!
 * \struct stackedContext_s
 * \brief The context of an interrupted partition.
 */
typedef struct stackedContext_s {
	/*!
	 * Always 1 on this target, which has no extended frame. The field is
	 * kept so that the arch-neutral part of the yield chain, the VIDT
	 * consumers and the root partition's crt0 need no RISC-V variant.
	 */
	uint32_t isBasicFrame;
	/*! Pip flags, unchanged semantics. */
	uint32_t pipflags;
	/*! x1 to x31: regs[n - 1] holds x<n>. x0 is hardwired zero. */
	uint32_t regs[CONTEXT_REGS_NB];
	/*! The address to resume at. */
	uint32_t mepc;
	/*! Saved mstatus; only MPP and MPIE are restored. */
	uint32_t mstatus;
} stackedContext_t;

/*!
 * \fn uint32_t contextReadRegister(const stackedContext_t *context, uint32_t reg)
 * \brief Reads register x<reg> from a saved context.
 * \param context The saved context.
 * \param reg A register number in [0, 31].
 * \return The saved value of x<reg>, or zero for x0.
 */
static inline uint32_t contextReadRegister(const stackedContext_t *context,
                                           uint32_t reg)
{
	if (reg == 0) {
		return 0;	// x0 is hardwired zero and is not stored
	}
	return context->regs[reg - 1];
}

/*!
 * \fn void contextWriteRegister(stackedContext_t *context, uint32_t reg, uint32_t value)
 * \brief Writes register x<reg> of a saved context.
 *
 * Hides the same regs[n - 1] offset as contextReadRegister(). Writing x0 is
 * silently dropped rather than corrupting regs[-1].
 *
 * \param context The saved context.
 * \param reg A register number in [0, 31].
 * \param value The value to store.
 */
static inline void contextWriteRegister(stackedContext_t *context,
                                        uint32_t reg, uint32_t value)
{
	if (reg == 0) {
		return;		// x0 is hardwired zero and is not stored
	}
	context->regs[reg - 1] = value;
}

/*
 * The offsets above are what trap_entry.S indexes the frame with, so a change
 * to the struct that did not reach them would corrupt every saved context.
 * This turns that into a compile error. Spelled as a negative array bound
 * rather than _Static_assert, which is C11: the kernel builds at -std=gnu99.
 */
typedef char contextLayoutCheck[
	(CONTEXT_OFFSET_IS_BASIC_FRAME
		== (int) offsetof(stackedContext_t, isBasicFrame)
	 && CONTEXT_OFFSET_PIPFLAGS
		== (int) offsetof(stackedContext_t, pipflags)
	 && CONTEXT_OFFSET_REGS
		== (int) offsetof(stackedContext_t, regs)
	 && CONTEXT_OFFSET_MEPC
		== (int) offsetof(stackedContext_t, mepc)
	 && CONTEXT_OFFSET_MSTATUS
		== (int) offsetof(stackedContext_t, mstatus)
	 && CONTEXT_SIZE == (int) sizeof(stackedContext_t)
	 && CONTEXT_REG_OFFSET(CONTEXT_REGS_NB)
		== (int) offsetof(stackedContext_t, regs)
		   + (CONTEXT_REGS_NB - 1) * 4) ? 1 : -1];

#endif /* !__ASSEMBLER__ */

#endif /* CONTEXT_H */
