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

/*
 * The bringup harness's U-mode excursion mechanism and its trap stub.
 *
 * This is NOT the port's trap stub. It saves no context: a probe runs, traps,
 * and the harness reports what happened, so the only state that has to
 * survive is M-mode's. The real trap_entry.S has to save all 31 registers
 * and is a separate piece of work.
 *
 * What it does share with the real one, deliberately, is the two mechanisms
 * the port rests on and that are worth proving on silicon early:
 *
 *   - the mscratch swap, with the invariant that mscratch is non-zero while
 *     U-mode runs and zero while M-mode does, so that one csrrw both finds a
 *     usable stack and tells the two cases apart;
 *   - advancing mepc past an ecall before mret, without which the ecall
 *     re-executes forever.
 */

#include "csr.h"
#include "bringup.h"

.option norelax

.section .text.bringup, "ax", @progbits
.p2align 2

/*
 * uint32_t bringupRunInUser(uint32_t entry, uint32_t stack, uint32_t argument)
 *
 * Drops to U-mode and comes back through trapEntry below, which returns to
 * this function's caller directly: the frame pushed here is what the trap
 * stub recovers sp and ra from, and mscratch is how it finds it.
 */
.globl bringupRunInUser
.type bringupRunInUser, @function
bringupRunInUser:
	addi	sp, sp, -16
	sw	ra, 12(sp)

	/* mscratch now points at this frame, which is both the stack the trap
	 * stub switches to and the non-zero marker saying U-mode is running. */
	csrw	mscratch, sp

	csrw	mepc, a0
	li	t0, RVCSR_MSTATUS_MPP_BITS
	csrc	mstatus, t0		/* MPP = 0, so mret enters U-mode */

	/* Give a7 a value that does not ask to be resumed, so that a trap
	 * taken before the probe sets it -- an instruction access fault on
	 * the probe's own first fetch, say -- still comes back here. */
	li	a7, BRINGUP_A7_DONE

	mv	t0, a1
	mv	a0, a2
	mv	sp, t0
	mret
.size bringupRunInUser, . - bringupRunInUser

/*
 * The trap stub. mtvec.MODE is 0, so every cause arrives here.
 *
 * The alignment is load-bearing: mtvec.BASE is bits 31:2 and mtvec.MODE is
 * bits 1:0, so start.S writing an address whose low two bits are not zero
 * would select a reserved mode rather than direct. Compressed instructions
 * make a preceding function an odd multiple of two bytes long often enough
 * that this is not hypothetical, and check-image.sh checks it.
 */
.p2align 2
.globl trapEntry
.type trapEntry, @function
trapEntry:
	/* Swap in the stack mscratch holds. Doing it with csrrw yields a
	 * usable register even when every one of them is live, which is why
	 * the real stub will start the same way. */
	csrrw	sp, mscratch, sp
	beqz	sp, .LmachineTrap

	/* An ecall carrying BRINGUP_A7_RESUME is the syscall return path:
	 * step over the ecall and go straight back to U-mode. a7 is still the
	 * partition's, since nothing above has been saved or restored. */
	li	t0, BRINGUP_A7_RESUME
	bne	a7, t0, .LreturnToMachine
	csrr	t0, mcause
	li	t1, RVCSR_MCAUSE_CODE_VALUE_U_ECALL
	bne	t0, t1, .LreturnToMachine

	csrr	t0, mepc
	addi	t0, t0, 4		/* ecall is 4 bytes and uncompressed */
	csrw	mepc, t0

	/* Undo the swap: U-mode's sp back into sp, the harness's frame back
	 * into mscratch, so the next trap finds it again. */
	csrrw	sp, mscratch, sp
	mret

.LreturnToMachine:
	/* M-mode is running from here on, so restore the invariant. */
	csrw	mscratch, zero

	la	t0, bringupTrapA7
	sw	a7, 0(t0)
	csrr	t1, mepc
	la	t0, bringupTrapMepc
	sw	t1, 0(t0)

	csrr	a0, mcause
	lw	ra, 12(sp)
	addi	sp, sp, 16
	ret				/* returns into bringupRunInUser's caller */

.LmachineTrap:
	/* mscratch was zero, so the trap came from M-mode: the harness itself
	 * faulted. There is no context worth keeping, only a report to make. */
	la	sp, __pipStackTop
	csrr	a0, mcause
	csrr	a1, mepc
	tail	bringupMachineTrap
.size trapEntry, . - trapEntry

/*
 * The U-mode probes. Each is a leaf that touches no stack, so a probe needs
 * no PMP region of its own beyond the one under test and an executable one
 * over this code.
 */

.globl bringupProbeLoad
.type bringupProbeLoad, @function
bringupProbeLoad:
	lw	a0, 0(a0)
	ecall
.size bringupProbeLoad, . - bringupProbeLoad

.globl bringupProbeStore
.type bringupProbeStore, @function
bringupProbeStore:
	sw	a0, 0(a0)
	ecall
.size bringupProbeStore, . - bringupProbeStore

.globl bringupProbeEcall
.type bringupProbeEcall, @function
bringupProbeEcall:
	ecall
.size bringupProbeEcall, . - bringupProbeEcall

.globl bringupProbeResume
.type bringupProbeResume, @function
bringupProbeResume:
	li	a7, BRINGUP_A7_RESUME
	ecall
	li	a7, BRINGUP_A7_DONE
	ecall
.size bringupProbeResume, . - bringupProbeResume
