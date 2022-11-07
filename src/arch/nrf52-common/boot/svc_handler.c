/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
/*  Copyright (C) 2020-2022 Orange                                             */
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
#include "Services.h"
#if defined(NRF52840_XXAA)
#include "nrf52840.h"
#else
#include "nrf52.h"
#endif
#include "core_cm4.h"
#include "pip_debug.h"
#include "context.h"
#include "yield_c.h"
#include "pip_interrupt_calls.h"
#include "ADT.h"
#ifdef BENCHMARK
#include "scs.h"
#include "benchmark_helpers.h"
#endif // BENCHMARK

	/*!
	 * \brief Enumeration of the SVC numbers
	 */
	typedef enum svc_number_e {
		SVC_NUMBER_CREATE_PARTITION = 0,	/*!< The createPartition SVC number. */
		SVC_NUMBER_CUT_MEMORY_BLOCK = 1,	/*!< The cutMemoryBlock SVC number. */
		SVC_NUMBER_MERGE_MEMORY_BLOCK = 2,	/*!< The mergeMemoryBlocks SVC number. */
		SVC_NUMBER_PREPARE = 3,				/*!< The prepare SVC number. */
		SVC_NUMBER_ADD_MEMORY_BLOCK = 4,	/*!< The addMemoryBlock SVC number. */
		SVC_NUMBER_REMOVE_MEMORY_BLOCK = 5, /*!< The removeMemoryBlock SVC number. */
		SVC_NUMBER_DELETE_PARTITION = 6,	/*!< The deletePartition SVC number. */
		SVC_NUMBER_COLLECT = 7,				/*!< The collect SVC number. */
		SVC_NUMBER_MAP_MPU = 8,				/*!< The mapMPU SVC number. */
		SVC_NUMBER_READ_MPU = 9,			/*!< The readMPU SVC number. */
		SVC_NUMBER_FIND_BLOCK = 10,			/*!< The findBlock SVC number. */
		SVC_NUMBER_SET_VIDT = 11,			/*!< The setVIDT SVC number. */
		SVC_NUMBER_YIELD = 12,				/*!< The yield SVC number. */
		SVC_NUMBER_GET_INT_STATE = 13,		/*!< The getIntState SVC number. */
		SVC_NUMBER_SET_INT_STATE = 14		/*!< The setIntState SVC number. */
	} svc_number_t;

/*!
 * \brief Call the PIP service associated with the SVC number.
 * \param svc_number The SVC number associated with the service to be
 *        called.
 * \param context The context stacked on the caller's stack.
 */
__attribute__((section(".text_pip")))
void SVC_Handler_C(stacked_context_t *stackedContext)
{
#if defined BENCHMARK
	cycles.handler_start_timestamp = GetCycleCounter();
	//dump_partition(rootid);
#endif
	/* Retrieve the SVC number encoded on the second byte of the
	 * SVC instruction. */
	uint32_t pc = stackedContext->registers[PC];
	uint32_t svc_number = ((uint8_t *) pc)[-2];

	switch (svc_number)
	{
		case SVC_NUMBER_CREATE_PARTITION:
			debug_printf("Create %x \n", stackedContext->registers[R0]);
			stackedContext->registers[R0] = (uint32_t) createPartition(
				(paddr) stackedContext->registers[R0]
			);
			break;

		case SVC_NUMBER_CUT_MEMORY_BLOCK:
			debug_printf("Cut in %x \n", getCurPartition());
			stackedContext->registers[R0] = (uint32_t) cutMemoryBlock(
				(paddr) stackedContext->registers[R0],
				(paddr) stackedContext->registers[R1],
				(Coq_index) stackedContext->registers[R2]
			);
			break;

		case SVC_NUMBER_MERGE_MEMORY_BLOCK:
			debug_printf("Merge in %x \n", getCurPartition());
			stackedContext->registers[R0] = (uint32_t) mergeMemoryBlocks(
				(paddr) stackedContext->registers[R0],
				(paddr) stackedContext->registers[R1],
				(Coq_index) stackedContext->registers[R2]
			);
			break;

		case SVC_NUMBER_PREPARE:
			debug_printf("Prepare %x \n", stackedContext->registers[R0]);
			stackedContext->registers[R0] = (uint32_t) prepare(
				(paddr) stackedContext->registers[R0],
				(Coq_index) stackedContext->registers[R1],
				(paddr) stackedContext->registers[R2]
			);
			break;

		case SVC_NUMBER_ADD_MEMORY_BLOCK:
			debug_printf("Add in %x \n", stackedContext->registers[R0]);
			uint32_t r2 = stackedContext->registers[R2];
			stackedContext->registers[R0] = (uint32_t) addMemoryBlock(
				(paddr) stackedContext->registers[R0],
				(paddr) stackedContext->registers[R1],
				(bool) ((/*stackedContext->registers[R2]*/ r2 >> 2) & 1),
				(bool) ((/*stackedContext->registers[R2]*/ r2  >> 1) & 1),
				(bool) ((/*stackedContext->registers[R2]*/ r2 >> 0) & 1)
			);
			break;

		case SVC_NUMBER_REMOVE_MEMORY_BLOCK:
			debug_printf("Remove in child %c", ' ');
			stackedContext->registers[R0] = (uint32_t) removeMemoryBlock(
				(paddr) stackedContext->registers[R0]
			);
			break;

		case SVC_NUMBER_DELETE_PARTITION:
			debug_printf("Delete %x \n", stackedContext->registers[R0]);
			stackedContext->registers[R0] = (uint32_t) deletePartition(
				(paddr) stackedContext->registers[R0]
			);
			break;

		case SVC_NUMBER_COLLECT:
			debug_printf("Collect %x \n", stackedContext->registers[R0]);
			stackedContext->registers[R0] = (uint32_t) collect(
				(paddr) stackedContext->registers[R0]
			);
			break;

		case SVC_NUMBER_MAP_MPU:
			debug_printf("Map MPU in %x \n", stackedContext->registers[R0]);
			stackedContext->registers[R0] = (uint32_t) mapMPU(
				(paddr) stackedContext->registers[R0],
				(paddr) stackedContext->registers[R1],
				(Coq_index) stackedContext->registers[R2]
			);
			break;

		case SVC_NUMBER_READ_MPU:
			debug_printf("Read MPU in %x \n", stackedContext->registers[R0]);
			stackedContext->registers[R0] = (uint32_t) readMPU(
				(paddr) stackedContext->registers[R0],
				(Coq_index) stackedContext->registers[R1]
			);
			break;

		case SVC_NUMBER_FIND_BLOCK:
		{
			debug_printf("Find block in %x \n", stackedContext->registers[R0]);
			// Note as the result is in memory, the parameters are passed with R1 and R2, not RO
			blockOrError block_found = findBlock(
				(paddr) stackedContext->registers[R0],
				(paddr) stackedContext->registers[R1]
			);

			// Fill R0-R3: the access permissions and accessible bit are squeezed into R3
			stackedContext->registers[R0] = (uint32_t) block_found.blockAttr.blockentryaddr;
			stackedContext->registers[R1] = (uint32_t) block_found.blockAttr.blockrange.startAddr; // displays start and end
			stackedContext->registers[R2] = (uint32_t) block_found.blockAttr.blockrange.endAddr;
			stackedContext->registers[R3] = (uint32_t) block_found.blockAttr.read |
						 (uint32_t) block_found.blockAttr.write << 1 |
						 (uint32_t) block_found.blockAttr.exec << 2 |
						 (uint32_t) block_found.blockAttr.accessible << 3;
			break;
		}

		case SVC_NUMBER_SET_VIDT:
			debug_printf("Set VIDT %x \n", stackedContext->registers[R0]);
			stackedContext->registers[R0] = setVIDT(
				(paddr)stackedContext->registers[R0],
				(paddr)stackedContext->registers[R1]);
			break;

		case SVC_NUMBER_YIELD:
			debug_printf("Yield %x \n ", stackedContext->registers[R0]);
			stackedContext->registers[R0] = (uint32_t) yieldGlue(
				stackedContext,
				(paddr) stackedContext->registers[R0],
				stackedContext->registers[R1],
				stackedContext->registers[R2],
				stackedContext->registers[R3],
				stackedContext->registers[R4]
			);
			break;

		case SVC_NUMBER_GET_INT_STATE:
			debug_printf("Get int state %x \n", stackedContext->registers[R0]);
			stackedContext->registers[R0] = (uint32_t) getIntState(
				(paddr) stackedContext->registers[R0]
			);
			break;

		case SVC_NUMBER_SET_INT_STATE:
			debug_printf("set int state %x \n", stackedContext->registers[R0]);
			setIntState(
				stackedContext->registers[R0]
			);
			break;

#ifdef UNIT_TESTS
		case 127: // Enable Privileged mode !TODO!: to remove with system calls in SVC instead
			__set_CONTROL( __get_CONTROL( ) & ~CONTROL_nPRIV_Msk ) ;
			break;

		case 128: // Disable Privileged mode !TODO!: to remove with system calls in SVC instead
			__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk ); // switch to unprivileged Thread Mode
			__DMB();
			__ISB();
			__DSB();
			break;
#endif // UNIT_TESTS

#ifdef BENCHMARK
    case 129: // Stop benchmark (end_cycles_counting)
		cycles.global_counter = GetCycleCounter(); // get cycle counter
		DisableCycleCounter();			   // disable counting if not used
		// end benchmark phase in privileged thread mode with irq enabled

		// prepare stack frame on the MSP to not pollute PSP
		// However, since the MSP is used to check Pip corruption and would
		// stop the program in exception_entrypoints, we are moving
		// the PSP pointer to MSP. Also, the PSP points to the top of MSP
		// since this part has already been used and thus the benchmark stack
		// won't add any length -> MSP and PSP are not usuable to retrieve information
		// after this operation
		uint32_t forceAlign = CCR.STKALIGN; // align to 8 bytes if necessary
		uint32_t spMask = ~(forceAlign << 2);
		uint32_t msp_top = &__StackTop;
		uint32_t framePtrAlign = (msp_top >> 2) & forceAlign;
		uint32_t frame = (msp_top - FRAME_SIZE) & spMask;

		uint32_t *framePtr = (uint32_t *)frame;
		framePtr[0] = stackedContext->registers[R0]; // retrieve r0 parameter
		framePtr[1] = stackedContext->registers[R1]; // retrieve r1 parameter
		framePtr[2] = stackedContext->registers[R2]; // retrieve r2 parameter
		framePtr[3] = 0;
		framePtr[4] = 0;
		framePtr[5] = 0;
		framePtr[6] = END_BENCHMARK;
		framePtr[7] = 0 | (framePtrAlign << 9) | (1 << 24);

		// Remove interrupts masking to allow Timer0
		__set_BASEPRI(0);

		// Stop SysTick
		SYST_CSR.ENABLE = 0;
		NVIC_ClearPendingIRQ(SysTick_IRQn);

		// Switch to Thread mode PRIV (0)
		__set_CONTROL(__get_CONTROL() & (0 << CONTROL_nPRIV_Pos));

		asm volatile("cpsie   i;"
					 "msr     psp, %0;" // set PSP to MSP top
					 //"msr msp, %1;"
					 "bx      %1;"
					 /* Output operands */
					 :

					 /* Input operands */
					 : "r"(frame),
					"r"(0xFFFFFFFD) // Use PSP

					 /* Clobbers */
					 : "memory");
		break;
	case 130: // benchmark initialisation phase ended
		debug_printf("Init ended:%d\n", GetCycleCounter());
		cycles.init_end_timestamp = GetCycleCounter(); // get cycle counter
		// keep privileged counter value after init (global + time in this handler)
		cycles.init_end_privileged_counter = cycles.global_privileged_counter + (GetCycleCounter() - cycles.handler_start_timestamp);
		break;
	case 131: // Print cycles
		printf("%d\n", GetCycleCounter());
		break;
	case 132: // Printf number
		printf("%d %d\n", stackedContext->registers[R0], GetCycleCounter());
		break;
	case 133: // Dump ancestors
		dump_ancestors(stackedContext->registers[R0]);
		break;
#endif // BENCHMARK
    default:
			/* Unknown SVC */
      break;
	}
#if defined BENCHMARK
	cycles.global_privileged_counter += GetCycleCounter() - cycles.handler_start_timestamp;
#endif
	__enable_irq();
}
