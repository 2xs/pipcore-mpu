/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
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

.syntax unified

.text
.thumb
.thumb_func

/*!
 * \def EXCEPTION_ENTRYPOINT
 *
 * \brief An assembler macro to prepare the call to the C
 *        handler corresponding to the exception raised.
 *
 * \param entrypointLabel The label of the assembler entry point.
 * \param mspHandlerLabel The label of the MSP C handler.
 * \param pspHandlerLabel The label of the PSP C handler.
 */
.macro EXCEPTION_ENTRYPOINT entryPointLabel mspHandlerLabel pspHandlerLabel

	.global   \entryPointLabel
	.type     \entryPointLabel, %function
	.section  .text

	/* The basic frame, stacked on exception entry, is the
	 * following:
	 *
	 *     +----------------+
	 *     |                | <- Original SP
	 *     +----------------+
	 *     |    Reserved    | <- Only if original SP is not
	 *     +----------------+    8-byte aligned
	 *     |      xPSR      |
	 *     +----------------+
	 *     |  ReturnAddress |
	 *     +----------------+
	 *     |       LR       |
	 *     +----------------+
	 *     |       R12      |
	 *     +----------------+
	 *     |       R3       |
	 *     +----------------+
	 *     |       R2       |
	 *     +----------------+
	 *     |       R1       |
	 *     +----------------+
	 *     |       R0       | <- New 8-byte aligned SP
	 *     +----------------+
	 *
	 * The extended frame, stacked on exception entry, is
	 * the following:
	 *
	 *     +----------------+
	 *     |                | <- Original SP
	 *     +----------------+
	 *     |    Reserved    | <- Only if original SP is not
	 *     +----------------+    8-byte aligned
	 *     |    Reserved    |
	 *     +----------------+
	 *     |      FPSCR     |
	 *     +----------------+
	 *     |       S15      |
	 *     +----------------+
	 *     |       S14      |
	 *     +----------------+
	 *     |       ...      |
	 *     +----------------+
	 *     |       S0       |
	 *     +----------------+
	 *     |      xPSR      |
	 *     +----------------+
	 *     |  ReturnAddress |
	 *     +----------------+
	 *     |       LR       |
	 *     +----------------+
	 *     |       R12      |
	 *     +----------------+
	 *     |       R3       |
	 *     +----------------+
	 *     |       R2       |
	 *     +----------------+
	 *     |       R1       |
	 *     +----------------+
	 *     |       R0       | <- New 8-byte aligned SP
	 *     +----------------+
	 */
	\entryPointLabel:

#if !defined(UNIT_TESTS)

		/* Disable interrupts, by setting the PRIMASK
		 * register to 1, if unit tests are not
		 * executed. */
		cpsid i

#endif

		/* Test the SPSEL bit of the EXC_RETURN value,
		 * stored in the register LR, to find out on
		 * which stack the frame was stacked. */
		tst lr, #4

		/* Execute either the first two instructions of
		 * the IT block if the frame was stacked on the
		 * MSP, or the last two instructions of the IT
		 * block if the frame was stacked on the PSP. */
		ittee eq

		/* If the frame was stacked on the MSP, it means
		 * that the fault occurred when we were in the
		 * code of PIP. The value of the stack is saved
		 * in register R0 because its value before the
		 * exception was saved on the exception frame. */
		mrseq r0, msp

		/* Load the address of the MSP C handler into
		 * the register R1. The address of the handler
		 * is saved in register R1 because its value
		 * before the exception was saved on the
		 * exception frame. */
		ldreq r1, =\mspHandlerLabel

		/* If the frame was stacked on the PSP, it means
		 * that the fault occurred when we were in the
		 * code of a partition. The value of the stack
		 * is saved in register R0 because its value
		 * before the exception was saved on the
		 * exception frame. */
		mrsne r0, psp

		/* Load the address of the PSP C handler into
		 * the register R1. The address of the handler
		 * is saved in register R1 because its value
		 * before the exception was saved on the
		 * exception frame. */
		ldrne r1, =\pspHandlerLabel

		/* Copy the stack pointer, stored in the
		 * register R0, into the register R2. Otherwise,
		 * the stmdb writeback cannot be used when R0 is
		 * both in rn and reglist. The value of the
		 * stack pointer is saved in register R2 because
		 * its value before the exception was saved on
		 * the exception frame. */
		mov r2, r0

		/* Push the remaining registers R4 to R11, as
		 * well as the top of the stack, saved in the
		 * register R2. */
		stmdb r0!, {r2, r4-r11}

		/* Extract the FPCA bit of the EXC_RETURN value,
		 * stored in the register LR, to find out if the
		 * stacked frame is a basic frame or an extended
		 * frame. */
		ubfx r2, lr, #4, #1

		/* Test if the FPCA bit, stored in the register
		 * R2, is equal to zero. */
		cmp r2, #0

		/* Execute the next instruction only if the FPCA
		 * bit is equal to zero. */
		it eq

		/* Push the remaining registers S16 to S31 if
		 * the FPCA bit is equal to zero. */
		vstmdbeq r0!, {s16-s31}

		/* Store zero to the register R3 in order to
		 * fill the pipflags field of the structure. */
		movs r3, #0

		/* Fill the isBasicFrame and pipflags fields of
		 * the structure with the value contained in the
		 * registers R2 and R3. */
		strd r2, r3, [r0, #-8]!

		/* Branch to the C handler. The register R0
		 * contains the address of the context stacked
		 * on the MSP or PSP. The register LR contains
		 * the value EXC_RETURN so that the current
		 * context can be restored if the C handler
		 * returns. */
		mov pc, r1

.endm

/*
 * Declaration of the entry points.
 */

.global   Reset_Handler
.type     Reset_Handler, %function
.section  .text
Reset_Handler:
	b _start

EXCEPTION_ENTRYPOINT PendSV_Handler     Boot_Handler  Interrupt_Handler_C

EXCEPTION_ENTRYPOINT Interrupt_Handler  Kernel_Panic  Interrupt_Handler_C

EXCEPTION_ENTRYPOINT MemManage_Handler  Kernel_Panic  MemManage_Handler_C

EXCEPTION_ENTRYPOINT Fault_Handler      Kernel_Panic  Fault_Handler_C

EXCEPTION_ENTRYPOINT SVC_Handler        Kernel_Panic  SVC_Handler_C

.end
