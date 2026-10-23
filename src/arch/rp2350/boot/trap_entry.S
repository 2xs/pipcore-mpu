/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2024)                */
/*  Copyright (C) 2020-2024 Orange                                             */
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
 * \file trap_entry.S
 * \brief Trap entry and context restore for the Hazard3 core of the RP2350.
 *
 * Replaces the ARM target's exception_entrypoints.S, and its crt.S vector
 * table has no analogue: mtvec.MODE is 0, so every cause arrives at the one
 * stub below and trapHandlerC() demuxes on mcause.
 *
 * Three things are different enough from ARM to state plainly.
 *
 * Nothing is stacked by hardware. ARM's hardware pushed the exception frame
 * on whichever stack was active, which for a partition meant the PSP, i.e.
 * partition memory -- hence its MUNSTKERR path for a partition that had
 * corrupted its own sp. Here the frame is built by hand on Pip's own kernel
 * stack, so a hostile sp is a non-event: it is captured as data, out of
 * mscratch, and never dereferenced. It also means the saved sp *is* the
 * pre-trap sp, so ARM's resetInitialSp() and its CCR.STKALIGN / 0x20 / 0x68
 * frame arithmetic disappear entirely.
 *
 * There is one stack pointer, so mscratch holds Pip's. The invariant is that
 * mscratch is __pipStackTop while a partition runs and zero while Pip runs,
 * which makes a single csrrw do two jobs: it yields a usable register even
 * when every one of them is live, and the value it yields distinguishes a
 * partition fault from a Pip fault. That replaces ARM's "tst lr, #4" on
 * EXC_RETURN, which asked the same question as MSP versus PSP.
 *
 * Trap entry clears mstatus.MIE in hardware, so ARM's cpsid i at the top of
 * EXCEPTION_ENTRYPOINT, and its UNIT_TESTS guard, are simply gone.
 */

#include "context.h"
#include "csr.h"

/*
 * Linker relaxation would let the assembler reach globals through gp, and gp
 * belongs to the interrupted partition until this stub has saved it. Pip is
 * built with -mno-relax for the same reason; check-image.sh greps the linked
 * image to make sure no gp-relative access survives anywhere.
 */
.option norelax

.section .text.trap_entry, "ax", @progbits

/*
 * The trap stub.
 *
 * The alignment is load-bearing, not tidiness: mtvec.BASE is bits 31:2 and
 * mtvec.MODE is bits 1:0, so start.S writing a trapEntry whose low two bits
 * are not zero selects a reserved mode instead of direct. With the C
 * extension a preceding function ending on a compressed instruction leaves
 * the next label 2-byte aligned, which is how this was first found; masking
 * at the write site would have been the wrong fix, pointing mtvec two bytes
 * short of the stub. check-image.sh checks the alignment of the linked
 * symbol.
 */
.p2align 2
.globl trapEntry
.type trapEntry, @function
trapEntry:
	/* sp <- Pip's kernel stack, mscratch <- the partition's sp. */
	csrrw	sp, mscratch, sp

	/* mscratch held zero, so Pip itself trapped. sp now holds zero and
	 * Pip's real sp is in mscratch; .LpipFaulted puts it back. */
	beqz	sp, .LpipFaulted

	addi	sp, sp, -CONTEXT_SIZE

	/* x1 and x3 to x31. x0 is hardwired zero and x2 is the sp that the
	 * csrrw above moved into mscratch, stored further down. Named
	 * numerically on purpose: it is the regs[n - 1] == x<n> contract from
	 * context.h, and this way it can be read straight off against it. */
	sw	x1,  CONTEXT_REG_OFFSET(1)(sp)		/* ra */
	sw	x3,  CONTEXT_REG_OFFSET(3)(sp)		/* gp */
	sw	x4,  CONTEXT_REG_OFFSET(4)(sp)		/* tp */
	sw	x5,  CONTEXT_REG_OFFSET(5)(sp)		/* t0 */
	sw	x6,  CONTEXT_REG_OFFSET(6)(sp)		/* t1 */
	sw	x7,  CONTEXT_REG_OFFSET(7)(sp)		/* t2 */
	sw	x8,  CONTEXT_REG_OFFSET(8)(sp)		/* s0 */
	sw	x9,  CONTEXT_REG_OFFSET(9)(sp)		/* s1 */
	sw	x10, CONTEXT_REG_OFFSET(10)(sp)		/* a0 */
	sw	x11, CONTEXT_REG_OFFSET(11)(sp)		/* a1 */
	sw	x12, CONTEXT_REG_OFFSET(12)(sp)		/* a2 */
	sw	x13, CONTEXT_REG_OFFSET(13)(sp)		/* a3 */
	sw	x14, CONTEXT_REG_OFFSET(14)(sp)		/* a4 */
	sw	x15, CONTEXT_REG_OFFSET(15)(sp)		/* a5 */
	sw	x16, CONTEXT_REG_OFFSET(16)(sp)		/* a6 */
	sw	x17, CONTEXT_REG_OFFSET(17)(sp)		/* a7 */
	sw	x18, CONTEXT_REG_OFFSET(18)(sp)		/* s2 */
	sw	x19, CONTEXT_REG_OFFSET(19)(sp)		/* s3 */
	sw	x20, CONTEXT_REG_OFFSET(20)(sp)		/* s4 */
	sw	x21, CONTEXT_REG_OFFSET(21)(sp)		/* s5 */
	sw	x22, CONTEXT_REG_OFFSET(22)(sp)		/* s6 */
	sw	x23, CONTEXT_REG_OFFSET(23)(sp)		/* s7 */
	sw	x24, CONTEXT_REG_OFFSET(24)(sp)		/* s8 */
	sw	x25, CONTEXT_REG_OFFSET(25)(sp)		/* s9 */
	sw	x26, CONTEXT_REG_OFFSET(26)(sp)		/* s10 */
	sw	x27, CONTEXT_REG_OFFSET(27)(sp)		/* s11 */
	sw	x28, CONTEXT_REG_OFFSET(28)(sp)		/* t3 */
	sw	x29, CONTEXT_REG_OFFSET(29)(sp)		/* t4 */
	sw	x30, CONTEXT_REG_OFFSET(30)(sp)		/* t5 */
	sw	x31, CONTEXT_REG_OFFSET(31)(sp)		/* t6 */

	/* t0 is saved now, so it is free. Recover the partition's sp from
	 * mscratch and give it its slot, exactly as the ARM stub captured the
	 * pre-exception SP explicitly in r2 rather than trusting the frame. */
	csrr	t0, mscratch
	sw	t0, CONTEXT_REG_OFFSET(2)(sp)		/* sp */

	/* Pip is running from here on, so restore the other half of the
	 * invariant. A trap taken from now until loadContext() finds zero in
	 * mscratch and is correctly treated as a Pip fault. */
	csrw	mscratch, zero

	csrr	t0, mepc
	sw	t0, CONTEXT_OFFSET_MEPC(sp)
	csrr	t0, mstatus
	sw	t0, CONTEXT_OFFSET_MSTATUS(sp)

	/* isBasicFrame is always 1 here: Hazard3 has no FPU, so there is no
	 * extended frame for it to distinguish. pipflags is zero on trap
	 * entry, as it is on ARM, and only means anything on a context saved
	 * for a yield. */
	li	t0, 1
	sw	t0, CONTEXT_OFFSET_IS_BASIC_FRAME(sp)
	sw	zero, CONTEXT_OFFSET_PIPFLAGS(sp)

	/* a0 = the context, the same convention as ARM's R0. The handler does
	 * not return: it finishes through loadContext(). */
	mv	a0, sp
	tail	trapHandlerC

.LpipFaulted:
	/* Pip trapped, which is a kernel bug and not survivable. Undo the
	 * csrrw so sp is Pip's own again -- the stack is still good, only the
	 * instruction that used it was wrong -- and report. Nothing is saved:
	 * there is no partition context here to preserve and nothing to
	 * return to. */
	csrrw	sp, mscratch, sp
	csrr	a0, mcause
	csrr	a1, mepc
	tail	pipFault
.size trapEntry, . - trapEntry

/*
 * void loadContext(stackedContext_t *context)
 *
 * Enters U-mode with the given context. Does not return.
 *
 * The replacement for ARM's loadBasicContext/loadExtendedContext, which had
 * to hand-rebuild the hardware exception frame at sp-0x20 or sp-0x68 and
 * honour CCR.STKALIGN. Nothing is stacked by hardware here, so restoring a
 * context is just the reverse of saving one.
 */
.p2align 2
.globl loadContext
.type loadContext, @function
loadContext:
	lw	t0, CONTEXT_OFFSET_MEPC(a0)
	csrw	mepc, t0

	/* MPP = 0 so that mret enters U-mode, MPIE = 1 so that interrupts are
	 * enabled once it does, and MPRV = 0 so that M-mode's own loads and
	 * stores are never reinterpreted with U-mode privilege. The rest of
	 * the saved mstatus is carried through unchanged. */
	lw	t0, CONTEXT_OFFSET_MSTATUS(a0)
	li	t1, ~(RVCSR_MSTATUS_MPP_BITS | RVCSR_MSTATUS_MPRV_BITS)
	and	t0, t0, t1
	li	t1, RVCSR_MSTATUS_MPIE_BITS
	or	t0, t0, t1
	csrw	mstatus, t0

	/* Pip never nests kernel entries -- the ARM target reloads
	 * msp = __pipStackTop on every context load for the same reason -- so
	 * mscratch can be reset unconditionally rather than unwound. This is
	 * also what re-arms the trap stub: from here a trap is a partition
	 * fault again. */
	la	t0, __pipStackTop
	csrw	mscratch, t0

	/* x1 and x3 to x31 except x10, mirroring the save above. x2 and x10
	 * come last: a0 is still the only pointer to the context, so it has
	 * to stay live until every load that uses it as a base is done. */
	lw	x1,  CONTEXT_REG_OFFSET(1)(a0)		/* ra */
	lw	x3,  CONTEXT_REG_OFFSET(3)(a0)		/* gp */
	lw	x4,  CONTEXT_REG_OFFSET(4)(a0)		/* tp */
	lw	x5,  CONTEXT_REG_OFFSET(5)(a0)		/* t0 */
	lw	x6,  CONTEXT_REG_OFFSET(6)(a0)		/* t1 */
	lw	x7,  CONTEXT_REG_OFFSET(7)(a0)		/* t2 */
	lw	x8,  CONTEXT_REG_OFFSET(8)(a0)		/* s0 */
	lw	x9,  CONTEXT_REG_OFFSET(9)(a0)		/* s1 */
	lw	x11, CONTEXT_REG_OFFSET(11)(a0)		/* a1 */
	lw	x12, CONTEXT_REG_OFFSET(12)(a0)		/* a2 */
	lw	x13, CONTEXT_REG_OFFSET(13)(a0)		/* a3 */
	lw	x14, CONTEXT_REG_OFFSET(14)(a0)		/* a4 */
	lw	x15, CONTEXT_REG_OFFSET(15)(a0)		/* a5 */
	lw	x16, CONTEXT_REG_OFFSET(16)(a0)		/* a6 */
	lw	x17, CONTEXT_REG_OFFSET(17)(a0)		/* a7 */
	lw	x18, CONTEXT_REG_OFFSET(18)(a0)		/* s2 */
	lw	x19, CONTEXT_REG_OFFSET(19)(a0)		/* s3 */
	lw	x20, CONTEXT_REG_OFFSET(20)(a0)		/* s4 */
	lw	x21, CONTEXT_REG_OFFSET(21)(a0)		/* s5 */
	lw	x22, CONTEXT_REG_OFFSET(22)(a0)		/* s6 */
	lw	x23, CONTEXT_REG_OFFSET(23)(a0)		/* s7 */
	lw	x24, CONTEXT_REG_OFFSET(24)(a0)		/* s8 */
	lw	x25, CONTEXT_REG_OFFSET(25)(a0)		/* s9 */
	lw	x26, CONTEXT_REG_OFFSET(26)(a0)		/* s10 */
	lw	x27, CONTEXT_REG_OFFSET(27)(a0)		/* s11 */
	lw	x28, CONTEXT_REG_OFFSET(28)(a0)		/* t3 */
	lw	x29, CONTEXT_REG_OFFSET(29)(a0)		/* t4 */
	lw	x30, CONTEXT_REG_OFFSET(30)(a0)		/* t5 */
	lw	x31, CONTEXT_REG_OFFSET(31)(a0)		/* t6 */
	lw	x2,  CONTEXT_REG_OFFSET(2)(a0)		/* sp */
	lw	x10, CONTEXT_REG_OFFSET(10)(a0)		/* a0, last */
	mret
.size loadContext, . - loadContext
