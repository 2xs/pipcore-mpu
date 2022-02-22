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

#include <stdio.h>

#include "nrf52.h"
#include "semihosting.h"
#include "trace.h"
#include "context.h"
#include "yield_c.h"
#include "pip_interrupt_calls.h"
#include "mal.h"
#include "scs.h"
#include "mpu.h"
#include "pip_debug.h"

/*!
 * \def UNREACHABLE_ADDRESS
 *
 * \brief An unreachable address in ARMv7-M.
 */
#define UNREACHABLE_ADDRESS 0xffffffff

/*!
 * \def MMFSR_CLEAR_MASK
 *
 * \brief A mask to clear all flags of the MMFSR register.
 */
#define MMFSR_CLEAR_MASK 0xbb

/*!
 * \brief The generic interrupt handler propagates an interrupt to the
 *        root partition.
 *
 * \param stackedContext The context stacked by the Interrupt_Handler
 *        entry point.
 *
 * \see The calling code is in the exception_entry.S file.
 */
void __attribute__((section(".after_vectors"), noreturn))
Interrupt_Handler_C(stacked_context_t *stackedContext)
{
	user_context_t context;

	/* Copy of the context stacked by the entry point. */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		context.registers[i] = stackedContext->registers[i];
	}

	debug_printf("DEBUG: [Interrupt_Handler] at PC=%x\n", context.registers[PC]);

	/* Save the value of the stack before the interrupt. */
	uint32_t forceAlign   = CCR.STKALIGN;
	uint32_t spMask       = ((context.registers[XPSR] >> 9) & forceAlign) << 2;
	context.registers[SP] = (context.registers[SP] + FRAME_SIZE) | spMask;
	context.valid         = CONTEXT_VALID_VALUE;

	paddr rootPartDesc = getRootPartition();
	paddr interruptedPartDesc = getCurPartition();
	int_mask_t interruptedPartIntState = getSelfIntState();
	uint32_t saveIndex;

	if (interruptedPartIntState == 0)
	{
		saveIndex = CLI_SAVE_INDEX;
	}
	else
	{
		saveIndex = STI_SAVE_INDEX;
	}

	/* We try to propagate the interrupt to the root partition by
	 * saving the context of the interrupted partition at the address
	 * found at the saveIndex in its VIDT. Then, we restore the
	 * context pointed to by the address found at the index
	 * corresponding to the interrupt number in the VIDT of the
	 * root partition. */
	yield_return_code_t yieldErrorCode = getSourcePartVidtCont(
		rootPartDesc,
		interruptedPartDesc,
		ICSR.VECTACTIVE,
		saveIndex,
		interruptedPartIntState,
		interruptedPartIntState,
		&context
	);

	switch (yieldErrorCode)
	{
		case CALLER_VIDT_IS_NULL:
		case CALLER_VIDT_IS_NOT_PRESENT:
		case CALLER_VIDT_IS_NOT_ACCESSIBLE:
		case CALLER_VIDT_BLOCK_TOO_SMALL:
		case CALLER_CONTEXT_BLOCK_NOT_FOUND:
		case CALLER_CONTEXT_BLOCK_IS_NOT_PRESENT:
		case CALLER_CONTEXT_BLOCK_IS_NOT_ACCESSIBLE:
		case CALLER_CONTEXT_BLOCK_IS_NOT_WRITABLE:
		case CALLER_CONTEXT_EXCEED_BLOCK_END:
		case CALLER_CONTEXT_MISALIGNED:
		{
			/* An error occurred while saving the
			 * interrupted context. This is either due to a
			 * problem with the block containing the VIDT or
			 * to an invalid save address. In both cases,
			 * the save of the interrupted context is
			 * abandoned and the context of the root
			 * partition corresponding to the interrupt
			 * number is restored. */
			getTargetPartVidtCont(
				rootPartDesc,
				interruptedPartDesc,
				NULL,
				ICSR.VECTACTIVE,
				0,
				0,
				NULL
			);

			break;
		}
		default:
		{
			break;
		}
	}

	/* We end up here if PIP is in an unrecoverable state. */
	printf("PIP: UNRECOVERABLE ERROR!\n");
	for (;;);
}

/*!
 * \brief This function propagate the fault of a partition to its
 *        parent.
 *
 * \param currentPartDesc The partition descriptor of the faulted
 *        partition.
 *
 * \param targetInterrupt The fault number.
 *
 * \param saveIndex The index in the VIDT of the faulted partition where
 *        to save its context.
 *
 * \param flagOnYield The state the faulted partition wishes to be on
 *        yield.
 *
 * \param flagOnWake The state the faulted partition wishes to be on
 *        wake.
 *
 * \param context The context of the faulted partition.
 */
void __attribute__((section(".after_vectors"), noreturn))
propagateFault(
	paddr          currentPartDesc,
	unsigned       targetInterrupt,
	unsigned       saveIndex,
	int_mask_t     flagOnYield,
	int_mask_t     flagOnWake,
	user_context_t *context
) {
	/* We try to propagate the fault to the parent partition of the
	 * one that has faulted by saving its context at the address
	 * found at the saveIndex in its VIDT. Then, we restore the
	 * context pointed to by the address found at the index
	 * corresponding to the fault number in the VIDT of the parent
	 * partition. */
	yield_return_code_t yieldErrorCode = getParentPartDescCont(
		currentPartDesc,
		targetInterrupt,
		saveIndex,
		flagOnYield,
		flagOnWake,
		context
	);

	switch (yieldErrorCode)
	{
		case CALLER_VIDT_IS_NULL:
		case CALLER_VIDT_IS_NOT_PRESENT:
		case CALLER_VIDT_IS_NOT_ACCESSIBLE:
		case CALLER_VIDT_BLOCK_TOO_SMALL:
		case CALLER_CONTEXT_BLOCK_NOT_FOUND:
		case CALLER_CONTEXT_BLOCK_IS_NOT_PRESENT:
		case CALLER_CONTEXT_BLOCK_IS_NOT_ACCESSIBLE:
		case CALLER_CONTEXT_BLOCK_IS_NOT_WRITABLE:
		case CALLER_CONTEXT_EXCEED_BLOCK_END:
		case CALLER_CONTEXT_MISALIGNED:
		{
			/* An error occurred while saving the
			 * interrupted context. This is either due to a
			 * problem with the block containing the VIDT or
			 * to an invalid save address. In both cases,
			 * the save of the interrupted context is
			 * abandoned and the context of the parent
			 * partition corresponding to the fault number
			 * is restored. */
			getTargetPartVidtCont(
				readPDParent(currentPartDesc),
				currentPartDesc,
				NULL,
				targetInterrupt,
				flagOnYield,
				flagOnWake,
				NULL
			);

			break;
		}
		case CALLEE_IS_PARENT_OF_ROOT:
		{
			/* We tried to propagate the fault to the parent
			 * partition of the root partition. This means
			 * that either the root partition has faulted,
			 * or that one of its children has faulted and
			 * could not handle the fault. */
			printf("PIP: The root partition has faulted!\n");

			break;
		}
		default:
		{
			paddr parentPartDec = readPDParent(currentPartDesc);

			printf("The parent partition (%p) cannot handle "
				"the fault.\n Propagating a double "
				"fault...", parentPartDec);

			/* The parent partition of the faulted partition
			 * could not manage the fault. Propagation of a
			 * double fault to the grandparent. */
			propagateFault(
				parentPartDec,
				targetInterrupt,
				DOUBLE_FAULT_LEVEL,
				flagOnYield,
				flagOnWake,
				context
			);

			break;
		}
	}

	/* We end up here if PIP is in an unrecoverable state. */
	printf("PIP: UNRECOVERABLE ERROR!\n");
	for (;;);
}

/*!
 * \brief The generic fault handler propagates the fault of a partition
 *        to its parent. If the index corresponding to the fault number
 *        in the parent's VIDT contains a null value or a pointer to an
 *        invalid context, the fault is propagated to the grandparent,
 *        up to the root partition. If the root partition cannot handle
 *        the fault, PIP is in an unrecoverable state.
 *
 * \param stackedContext The context stacked by the Fault_Handler entry
 *        point.
 *
 * \see The calling code is in the exception_entry.S file.
 */
void __attribute__((section(".after_vectors"), noreturn))
Fault_Handler_C(stacked_context_t *stackedContext)
{
	user_context_t context;

	/* Copy of the context stacked by the entry point. */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		context.registers[i] = stackedContext->registers[i];
	}

	/* Save the value of the stack before the fault. */
	uint32_t forceAlign   = CCR.STKALIGN;
	uint32_t spMask       = ((context.registers[XPSR] >> 9) & forceAlign) << 2;
	context.registers[SP] = (context.registers[SP] + FRAME_SIZE) | spMask;
	context.valid         = CONTEXT_VALID_VALUE;

	paddr currentPartDesc = getCurPartition();
	int_mask_t interruptedPartIntState = getSelfIntState();
	uint32_t saveIndex;

	if (interruptedPartIntState == 0)
	{
		saveIndex = CLI_SAVE_INDEX;
	}
	else
	{
		saveIndex = STI_SAVE_INDEX;
	}

	printf("The current partition (%p) has faulted...\n", currentPartDesc);

	/* Propagate the fault to the parent of the faulted partition. */
	propagateFault(currentPartDesc, ICSR.VECTACTIVE, saveIndex,
		interruptedPartIntState, interruptedPartIntState, &context);

	/* We should never end up here because the propagateFault never
	 * return to the caller. */
	__builtin_unreachable();
}

/*!
 * \brief Although the MemManage exception is a fault, it has its own
 *        handler. The reason for this is that a MemManage exception can
 *        be legitimately raised as part of the MPU partial block
 *        configuration. In the case of an illegal access, the
 *        Fault_Handler is called.
 *
 * \param stackedContext The context stacked by the MemManage_Handler
 *        entry point.
 *
 * \see The calling code is in the exception_entry.S file.
 */
void __attribute__((section(".after_vectors")))
MemManage_Handler_C(stacked_context_t *stackedContext)
{
	uint32_t faultedAddress;

	if (CFSR.MMFSR.DACCVIOL && CFSR.MMFSR.MMARVALID)
	{
		/* The MemManage fault was triggered because of an MPU
		 * violation or fault caused by an explicit memory
		 * access. The faulted address is stored in the MMFAR
		 * register because the MMARVALID bit is set. */
		faultedAddress = MMFAR.ADDRESS;
	}
	else if (CFSR.MMFSR.IACCVIOL)
	{
		/* The MemManage fault was triggered because of an MPU
		 * violation or fault caused by an instruction fetch,
		 * or an instruction fetch from XN memory when there is
		 * no MPU. The faulted address is stored in the PC
		 * register of the stacked context. */
		faultedAddress = stackedContext->registers[PC];
	}
	else
	{
		/* All other MemManage faults are not due to partial
		 * block configuration. We set the faultedAddress to an
		 * inaccessible address to avoid searching for a valid
		 * block in the MPU. */
		faultedAddress = UNREACHABLE_ADDRESS;
	}

	/* Clear all MMFSR flags by writing ones. */
	CFSR.MMFSR.as_uint8_t &= MMFSR_CLEAR_MASK;

	if (faultedAddress != UNREACHABLE_ADDRESS)
	{
		PDTable_t *currentPartDesc = (PDTable_t *) getCurPartition();

		for (size_t i = 0; i < MPU_NUM_REGIONS; i++)
		{
			BlockEntry_t *currentBlock = currentPartDesc->mpu[i];

			if (!currentBlock->present)
			{
				/* We go to the next MPU block if the
				 * current block has not the present
				 * flag. */
				continue;
			}

			block_t *currentBlockRange = &currentBlock->blockrange;

			uint32_t startAddress = (uint32_t) currentBlockRange->startAddr;
			uint32_t endAddress   = (uint32_t) currentBlockRange->endAddr;

			if (startAddress > faultedAddress)
			{
				/* We go to the next MPU block if the
				 * current block start address is
				 * greater than or equal the faulted
				 * address. */
				continue;
			}

			if (faultedAddress > endAddress)
			{
				/* We go to the next MPU block if the
				 * current block end address is less
				 * than or equal the faulted address. */
				continue;
			}

			uint32_t physicalMpuStartAddress =
					(uint32_t) readPhysicalMPUStartAddr(i);

			uint32_t physicalMpuEndAddress =
					(uint32_t) readPhysicalMPUEndAddr(i);

			if (physicalMpuStartAddress <= faultedAddress &&
				faultedAddress <= physicalMpuEndAddress)
			{
				/* The address that caused a fault was
				 * in a physical MPU block. This is a
				 * real MPU fault. */
				break;
			}
			else
			{
				/* The address that caused a fault was
				 * not in a physical MPU block. We must
				 * reconfigure the MPU regions to allow
				 * access to the faulty address. */

				configure_LUT_entry(currentPartDesc->LUT, i,
					currentBlock, (uint32_t *) faultedAddress);

				mpu_configure_from_LUT(currentPartDesc->LUT);

				__enable_irq();

				/* Return to the instruction that
				 * caused the fault. */
				return;
			}
		}
	}

#if !defined(UNIT_TESTS)

	/* Call the fault handler if it is a real MemManage fault. */
	Fault_Handler_C(stackedContext);

	/* We should never end up here because the Fault_Handler_C never
	 * return to the caller. */
	__builtin_unreachable();

#else

	uint32_t* canary = (uint32_t*) 0x20001500;

	*canary = 0xDEADBEEF;

	printf("\r\nNew canary=%x\n", *canary);

	stackedContext->registers[PC] += 2;

	printf("\r\nBranch to PC=%x\r\n", stackedContext->registers[PC]);

#endif
}
 // Exception Stack Frame of the Cortex-M3 or Cortex-M4 processor.
  typedef struct
  {
    uint32_t r0;
    uint32_t r1;
    uint32_t r2;
    uint32_t r3;
    uint32_t r12;
    uint32_t lr;
    uint32_t pc;
    uint32_t psr;
#if  defined(__ARM_ARCH_7EM__)
    uint32_t s[16];
#endif
  } ExceptionStackFrame;

  void dumpExceptionStack(ExceptionStackFrame *frame,
						  uint32_t cfsr, uint32_t mmfar, uint32_t bfar,
						  uint32_t lr)
  {
#if defined(TRACE)
#if defined(DUMP)
	trace_printf("Stack frame:\n");
	trace_printf(" R0 =  %08X\n", frame->r0);
	trace_printf(" R1 =  %08X\n", frame->r1);
	trace_printf(" R2 =  %08X\n", frame->r2);
	trace_printf(" R3 =  %08X\n", frame->r3);
	trace_printf(" R12 = %08X\n", frame->r12);
	trace_printf(" LR =  %08X\n", frame->lr);
	trace_printf(" PC =  %08X\n", frame->pc);
	trace_printf(" PSR = %08X\n", frame->psr);

	trace_printf(" PSRb = ");// BYTE_TO_BINARY_PATTERN, BYTE_TO_BINARY(frame->psr));
	binprintf(frame->psr);
	trace_printf("\n");
	trace_printf("FSR/FAR:\n");
	trace_printf(" CFSR =  %08X\n", cfsr);
	trace_printf(" HFSR =  %08X\n", SCB->HFSR);
	trace_printf(" DFSR =  %08X\n", SCB->DFSR);
	trace_printf(" AFSR =  %08X\n", SCB->AFSR);

	if (cfsr & (1UL << 7))
	{
		trace_printf(" MMFAR = %08X\n", mmfar);
	}
	if (cfsr & (1UL << 15))
	{
		trace_printf(" BFAR =  %08X\n", bfar);
	}
	trace_printf("Misc\n");
	trace_printf(" LR/EXC_RETURN= %08X\n", lr);
#endif
#endif
}



// ----------------------------------------------------------------------------

#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)

#if defined(OS_USE_SEMIHOSTING) || defined(OS_USE_TRACE_SEMIHOSTING_STDOUT) || defined(OS_USE_TRACE_SEMIHOSTING_DEBUG)

int isSemihosting(ExceptionStackFrame *frame, uint16_t opCode);

/**
 * This function provides the minimum functionality to make a semihosting program execute even without the debugger present.
 * @param frame pointer to an exception stack frame.
 * @param opCode the 16-bin word of the BKPT instruction.
 * @return 1 if the instruction was a valid semihosting call; 0 otherwise.
 */
int isSemihosting(ExceptionStackFrame *frame, uint16_t opCode)
{
	uint16_t *pw = (uint16_t *)frame->pc;
	if (*pw == opCode)
	{
		uint32_t r0 = frame->r0;
#if defined(OS_DEBUG_SEMIHOSTING_FAULTS) || defined(OS_USE_SEMIHOSTING) || defined(OS_USE_TRACE_SEMIHOSTING_STDOUT)
		uint32_t r1 = frame->r1;
#endif
#if defined(OS_USE_SEMIHOSTING) || defined(OS_USE_TRACE_SEMIHOSTING_STDOUT)
		uint32_t *blk = (uint32_t *)r1;
#endif

#if defined(OS_DEBUG_SEMIHOSTING_FAULTS)
		// trace_printf ("sh r0=%d\n", r0);
#endif

		switch (r0)
		{

#if defined(OS_USE_SEMIHOSTING)

		case SEMIHOSTING_SYS_CLOCK:
		case SEMIHOSTING_SYS_ELAPSED:
		case SEMIHOSTING_SYS_FLEN:
		case SEMIHOSTING_SYS_GET_CMDLINE:
		case SEMIHOSTING_SYS_REMOVE:
		case SEMIHOSTING_SYS_RENAME:
		case SEMIHOSTING_SYS_SEEK:
		case SEMIHOSTING_SYS_SYSTEM:
		case SEMIHOSTING_SYS_TICKFREQ:
		case SEMIHOSTING_SYS_TMPNAM:
		case SEMIHOSTING_SYS_ISTTY:
			frame->r0 = (uint32_t)-1; // the call is not successful or not supported
			break;

		case SEMIHOSTING_SYS_CLOSE:
			frame->r0 = 0; // call is successful
			break;

		case SEMIHOSTING_SYS_ERRNO:
			frame->r0 = 0; // the value of the C library errno variable.
			break;

		case SEMIHOSTING_SYS_HEAPINFO:
			blk[0] = 0; // heap_base
			blk[1] = 0; // heap_limit
			blk[2] = 0; // stack_base
			blk[3] = 0; // stack_limit
			break;

		case SEMIHOSTING_SYS_ISERROR:
			frame->r0 = 0; // 0 if the status word is not an error indication
			break;

		case SEMIHOSTING_SYS_READ:
			// If R0 contains the same value as word 3, the call has
			// failed and EOF is assumed.
			frame->r0 = blk[2];
			break;

		case SEMIHOSTING_SYS_READC:
			frame->r0 = '\0'; // the byte read from the console.
			break;

		case SEMIHOSTING_SYS_TIME:
			frame->r0 = 0; // the number of seconds since 00:00 January 1, 1970.
			break;

		case SEMIHOSTING_ReportException:

			NVIC_SystemReset();
			// Should not reach here
			return 0;

#endif // defined(OS_USE_SEMIHOSTING)

#if defined(OS_USE_SEMIHOSTING) || defined(OS_USE_TRACE_SEMIHOSTING_STDOUT)

#define HANDLER_STDIN (1)
#define HANDLER_STDOUT (2)
#define HANDLER_STDERR (3)

		case SEMIHOSTING_SYS_OPEN:
			// Process only standard io/out/err and return 1/2/3
			if (strcmp((char *)blk[0], ":tt") == 0)
			{
				if ((blk[1] == 0))
				{
					frame->r0 = HANDLER_STDIN;
					break;
				}
				else if (blk[1] == 4)
				{
					frame->r0 = HANDLER_STDOUT;
					break;
				}
				else if (blk[1] == 8)
				{
					frame->r0 = HANDLER_STDERR;
					break;
				}
			}
			frame->r0 = (uint32_t)-1; // the call is not successful or not supported
			break;

		case SEMIHOSTING_SYS_WRITE:
			// Silently ignore writes to stdout/stderr, fail on all other handler.
			if ((blk[0] == HANDLER_STDOUT) || (blk[0] == HANDLER_STDERR))
			{
#if defined(OS_DEBUG_SEMIHOSTING_FAULTS)
				frame->r0 = (uint32_t)blk[2] - trace_write((char *)blk[1], blk[2]);
#else
				frame->r0 = 0; // all sent, no more.
#endif // defined(OS_DEBUG_SEMIHOSTING_FAULTS)
			}
			else
			{
				// If other handler, return the total number of bytes
				// as the number of bytes that are not written.
				frame->r0 = blk[2];
			}
			break;

#endif // defined(OS_USE_SEMIHOSTING) || defined(OS_USE_TRACE_SEMIHOSTING_STDOUT)

#if defined(OS_USE_SEMIHOSTING) || defined(OS_USE_TRACE_SEMIHOSTING_STDOUT) || defined(OS_USE_TRACE_SEMIHOSTING_DEBUG)

		case SEMIHOSTING_SYS_WRITEC:
#if defined(OS_DEBUG_SEMIHOSTING_FAULTS)
		{
			char ch = *((char *)r1);
			trace_write(&ch, 1);
		}
#endif
		// Register R0 is corrupted.
		break;

		case SEMIHOSTING_SYS_WRITE0:
#if defined(OS_DEBUG_SEMIHOSTING_FAULTS)
		{
			char *p = ((char *)r1);
			trace_write(p, strlen(p));
		}
#endif
		// Register R0 is corrupted.
		break;

#endif

		default:
			return 0;
		}

		// Alter the PC to make the exception returns to
		// the instruction after the faulty BKPT.
		frame->pc += 2;
		return 1;
	}
	return 0;
}

#endif
void __attribute__((section(".after_vectors"), weak, naked))
SysTick_Handler(void)
{
	asm volatile(
		" tst lr,#4       \n"
		" ite eq          \n"
		" mrseq r0,msp    \n"
		" mrsne r0,psp    \n"
		" mov r1,lr       \n"
		" ldr r2,=SysTick_Handler_C \n"
		" bx r2"

		: /* Outputs */
		: /* Inputs */
		: /* Clobbers */
	);
}

void __attribute__((section(".after_vectors"), weak, used))
SysTick_Handler_C(ExceptionStackFrame *frame __attribute__((unused)),
					uint32_t lr __attribute__((unused)))
{
#if defined(TRACE)
	uint32_t mmfar = MMFAR.ADDRESS; // MemManage Fault Address
	uint32_t bfar = BFAR.ADDRESS;	 // Bus Fault Address
	uint32_t *cfsr_pt = (0xe000ed28);
	uint32_t cfsr = *cfsr_pt; // Configurable Fault Status Registers
#endif

#if defined(OS_USE_SEMIHOSTING) || defined(OS_USE_TRACE_SEMIHOSTING_STDOUT) || defined(OS_USE_TRACE_SEMIHOSTING_DEBUG)

	// If the BKPT instruction is executed with C_DEBUGEN == 0 and MON_EN == 0,
	// it will cause the processor to enter a HardFault exception, with DEBUGEVT
	// in the Hard Fault Status register (HFSR) set to 1, and BKPT in the
	// Debug Fault Status register (DFSR) also set to 1.

	if (((SCB->DFSR & SCB_DFSR_BKPT_Msk) != 0) && ((SCB->HFSR & SCB_HFSR_DEBUGEVT_Msk) != 0))
	{
		if (isSemihosting(frame, 0xBE00 + (AngelSWI & 0xFF)))
		{
			// Clear the exception cause in exception status.
			SCB->HFSR = SCB_HFSR_DEBUGEVT_Msk;

			// Continue after the BKPT
			return;
		}
	}

#endif

#if defined(TRACE)
	debug_printf("[SysTick_Handler]%c\n", ' ');
	dumpExceptionStack(frame, cfsr, mmfar, bfar, lr);
#endif // defined(TRACE)
}

/*#if defined BENCHMARK_BASELINE
// Assumes a fixed clock rate
void __attribute__((section(".after_vectors"), weak))
SysTick_Handler(void)
{
	// DO NOT loop, just return.
	// Useful in case someone (like STM HAL) inadvertently enables SysTick.
	// printf("Current SysTick value:%d\n", SysTick->VAL);
	;
}
#endif*/ /* BENCHMARK_BASELINE */




#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)

// The values of BFAR and MMFAR stay unchanged if the BFARVALID or
// MMARVALID is set. However, if a new fault occurs during the
// execution of this fault handler, the value of the BFAR and MMFAR
// could potentially be erased. In order to ensure the fault addresses
// accessed are valid, the following procedure should be used:
// 1. Read BFAR/MMFAR.
// 2. Read CFSR to get BFARVALID or MMARVALID. If the value is 0, the
//    value of BFAR or MMFAR accessed can be invalid and can be discarded.
// 3. Optionally clear BFARVALID or MMARVALID.
// (See Joseph Yiu's book).
#define BYTE_TO_BINARY_PATTERN "%c%c%c%c%c%c%c%c\n"
#define BYTE_TO_BINARY(byte)       \
	(byte & 0x80 ? '1' : '0'),     \
		(byte & 0x40 ? '1' : '0'), \
		(byte & 0x20 ? '1' : '0'), \
		(byte & 0x10 ? '1' : '0'), \
		(byte & 0x08 ? '1' : '0'), \
		(byte & 0x04 ? '1' : '0'), \
		(byte & 0x02 ? '1' : '0'), \
		(byte & 0x01 ? '1' : '0')

  void binprintf(int v)
  {
	  unsigned int mask = 1 << ((sizeof(int) << 3) - 1);
	  while (mask)
	  {
		  printf("%d", (v & mask ? 1 : 0));
		  mask >>= 1;
	  }
  }

  #endif

// Hard Fault handler wrapper in assembly.
// It extracts the location of stack frame and passes it to handler
// in C as a pointer. We also pass the LR value as second
// parameter.
// (Based on Joseph Yiu's, The Definitive Guide to ARM Cortex-M3 and
// Cortex-M4 Processors, Third Edition, Chap. 12.8, page 402).

void __attribute__((section(".after_vectors"), weak, naked))
HardFault_Handler(void)
{
	asm volatile(
		" tst lr,#4       \n"
		" ite eq          \n"
		" mrseq r0,msp    \n"
		" mrsne r0,psp    \n"
		" mov r1,lr       \n"
		" ldr r2,=HardFault_Handler_C \n"
		" bx r2"

		: /* Outputs */
		: /* Inputs */
		: /* Clobbers */
	);
}

void __attribute__((section(".after_vectors"), weak, used))
HardFault_Handler_C(ExceptionStackFrame *frame __attribute__((unused)),
					uint32_t lr __attribute__((unused)))
{
#if defined(TRACE)
	uint32_t mmfar = MMFAR.ADDRESS; // MemManage Fault Address
	uint32_t bfar = BFAR.ADDRESS;	 // Bus Fault Address
	uint32_t *cfsr_pt = (0xe000ed28);
	uint32_t cfsr = *cfsr_pt; // Configurable Fault Status Registers
#endif

#if defined(OS_USE_SEMIHOSTING) || defined(OS_USE_TRACE_SEMIHOSTING_STDOUT) || defined(OS_USE_TRACE_SEMIHOSTING_DEBUG)

	// If the BKPT instruction is executed with C_DEBUGEN == 0 and MON_EN == 0,
	// it will cause the processor to enter a HardFault exception, with DEBUGEVT
	// in the Hard Fault Status register (HFSR) set to 1, and BKPT in the
	// Debug Fault Status register (DFSR) also set to 1.

	if (((SCB->DFSR & SCB_DFSR_BKPT_Msk) != 0) && ((SCB->HFSR & SCB_HFSR_DEBUGEVT_Msk) != 0))
	{
		if (isSemihosting(frame, 0xBE00 + (AngelSWI & 0xFF)))
		{
			// Clear the exception cause in exception status.
			SCB->HFSR = SCB_HFSR_DEBUGEVT_Msk;

			// Continue after the BKPT
			return;
		}
	}

#endif

#if defined(TRACE)
	trace_printf("[HardFault]\n");
	dumpExceptionStack(frame, cfsr, mmfar, bfar, lr);
#endif // defined(TRACE)

#if defined(DEBUG)
	__DEBUG_BKPT();
#endif
	while (1)
	{
	}
}
#endif // defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)

#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)

void __attribute__((section(".after_vectors"), weak, naked))
BusFault_Handler(void)
{
	asm volatile(
		" tst lr,#4       \n"
		" ite eq          \n"
		" mrseq r0,msp    \n"
		" mrsne r0,psp    \n"
		" mov r1,lr       \n"
		" ldr r2,=BusFault_Handler_C \n"
		" bx r2"

		: /* Outputs */
		: /* Inputs */
		: /* Clobbers */
	);
}

void __attribute__((section(".after_vectors"), weak, used))
BusFault_Handler_C(ExceptionStackFrame *frame __attribute__((unused)),
				   uint32_t lr __attribute__((unused)))
{
#if defined(TRACE)
	uint32_t mmfar = MMFAR.ADDRESS; // MemManage Fault Address
	uint32_t bfar = BFAR.ADDRESS; // Bus Fault Address
	uint32_t* cfsr_pt = (0xe000ed28);
	uint32_t cfsr = *cfsr_pt; // Configurable Fault Status Registers

	trace_printf("[BusFault]\n");
	dumpExceptionStack(frame, cfsr, mmfar, bfar, lr);
#endif // defined(TRACE)

#if defined(DEBUG)
	__DEBUG_BKPT();
#endif
	while (1)
	{
	}
}

void __attribute__((section(".after_vectors"), weak, naked))
UsageFault_Handler(void)
{
	asm volatile(
		" tst lr,#4       \n"
		" ite eq          \n"
		" mrseq r0,msp    \n"
		" mrsne r0,psp    \n"
		" mov r1,lr       \n"
		" ldr r2,=UsageFault_Handler_C \n"
		" bx r2"

		: /* Outputs */
		: /* Inputs */
		: /* Clobbers */
	);
}

void __attribute__((section(".after_vectors"), weak, used))
UsageFault_Handler_C(ExceptionStackFrame *frame __attribute__((unused)),
					 uint32_t lr __attribute__((unused)))
{
#if defined(TRACE)
	uint32_t mmfar = MMFAR.ADDRESS; // MemManage Fault Address
	uint32_t bfar = BFAR.ADDRESS;	 // Bus Fault Address
	uint32_t *cfsr_pt = (0xe000ed28);
	uint32_t cfsr = *cfsr_pt; // Configurable Fault Status Registers
#endif

#if defined(OS_DEBUG_SEMIHOSTING_FAULTS)

	if ((cfsr & (1UL << 16)) != 0) // UNDEFINSTR
	{
		// For testing purposes, instead of BKPT use 'setend be'.
		if (isSemihosting(frame, AngelSWITestFaultOpCode))
		{
			return;
		}
	}

#endif

#if defined(TRACE)
	trace_printf("[UsageFault]\n");
	dumpExceptionStack(frame, cfsr, mmfar, bfar, lr);
#endif // defined(TRACE)

#if defined(DEBUG)
	__DEBUG_BKPT();
#endif
	while (1)
	{
	}
}

#endif

#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)

void __attribute__((section(".after_vectors"), weak))
DebugMon_Handler(void)
{
#if defined(DEBUG)
	__DEBUG_BKPT();
#endif
	while (1)
	{
	}
}

#endif
