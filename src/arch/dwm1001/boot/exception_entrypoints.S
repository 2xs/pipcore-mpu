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
 * \param entrypointName The name of the assembler entry point.
 * \param mspHandlerName The name of the MSP C handler.
 * \param pspHandlerName The name of the PSP C handler.
 */
.macro EXCEPTION_ENTRYPOINT entrypointName mspHandlerName pspHandlerName

	.global   \entrypointName
	.type     \entrypointName, %function
	.section  .text

	/* The frame of information pushed onto the stack on
	 * exception entry is the following:
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
	 */
	\entrypointName:

#if !defined(UNIT_TESTS)

		/* If we don't run the unit tests, we disable
		 * interrupts by setting the PRIMASK register
		 * to 1. */
		cpsid i

#endif

		/* Test the third bit of the EXC_RETURN value in
		 * the register LR, to find out on which stack
		 * the frame was pushed. */
		tst lr, #4

		/* Branch to 1f if the third bit of the
		 * EXC_RETURN value is set. */
		bne 1f

		/* If the frame has been saved on the MSP, it
		 * means that the fault occurred when we were in
		 * the code of PIP. The value of the stack is
		 * saved in register R0 because its value before
		 * the exception was saved on the MSP. */
		mrs r0, msp

		/* We have to copy the value of R0 into R3,
		 * otherwise we cannot use the writeback when
		 * R0 is both in rn and reglist. */
		mov r3, r0

		/* Push the initial value of the MSP and
		 * registers R3 to R11 to the MSP. */
		stmdb r0!, {r3-r11}

		/* Without storing the return address in the
		 * register LR, we branch to the MSP C handler
		 * corresponding to the exception with the
		 * pointer in R0 to the context stored on the
		 * stack as a parameter. */
		b \mspHandlerName

		1:

		/* If the frame has been saved on the PSP, it
		 * means that the fault occurred when we were in
		 * the code of a child partition. The value of
		 * the stack is saved in register R0 because its
		 * value before the exception was saved on the
		 * PSP. */
		mrs r0, psp

		/* We have to copy the value of R0 into R3,
		 * otherwise we cannot use the writeback when
		 * R0 is both in rn and reglist. */
		mov r3, r0

		/* Push the initial value of the PSP and
		 * registers R3 to R11 to the PSP. */
		stmdb r0!, {r3-r11}

		/* Without storing the return address in the
		 * register LR, we branch to the PSP C handler
		 * corresponding to the exception with the
		 * pointer in R0 to the context stored on the
		 * stack as a parameter. */
		b \pspHandlerName

.endm

/*
 * Declaration of the entry points.
 */

.global   Reset_Handler
.type     Reset_Handler, %function
.section  .text
Reset_Handler:
    bl _start

EXCEPTION_ENTRYPOINT PendSV_Handler     Boot_Handler  Interrupt_Handler_C

EXCEPTION_ENTRYPOINT Interrupt_Handler  Kernel_Panic  Interrupt_Handler_C

EXCEPTION_ENTRYPOINT MemManage_Handler  Kernel_Panic  MemManage_Handler_C

EXCEPTION_ENTRYPOINT Fault_Handler      Kernel_Panic  Fault_Handler_C

EXCEPTION_ENTRYPOINT SVC_Handler        Kernel_Panic  SVC_Handler_C

.end
