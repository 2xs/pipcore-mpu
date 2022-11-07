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
#include <stdlib.h>

#include "maldefines.h"
#if defined(NRF52840_XXAA)
#include "nrf52840.h"
#else
#include "nrf52.h"
#endif
#include "pip_debug.h"
#include "context.h"
#include "yield_c.h"
#include "scs.h"
#include "pip_interface.h"
#include "userconstants.h"

#if defined(UART_DEBUG)
#include "uart_debug_init.h"
#endif // UART_DEBUG

#if defined(TRACE)
#include "trace.h"
#endif // TRACE

#if defined(BENCHMARK)
#include "benchmark_helpers.h"
extern void main_benchmark();//int argc, uint32_t **argv);
#endif // BENCHMARK

/*!
 * \def SYSTEM_CLOCK_SOURCE_HZ
 *
 * \brief The system clock frequency in Hertz.
 */
#ifndef BENCHMARK
#define CPU_MHZ 8 /* 8MHz */
#endif			  /* BENCHMARK */
#define SYSTEM_CLOCK_SOURCE_HZ CPU_MHZ*1000000

/*!
 * \def SYSTICK_DELAY_SECOND
 *
 * \brief The delay between two SysTick in second.
 */
#define SYSTICK_DELAY_SECOND 0.01 /* 10 ms */

/*!
 * \def SYST_RVR_RELOAD_VALUE
 *
 * \brief The reload value for the SYST_RVR register.
 */
#define SYST_RVR_RELOAD_VALUE \
	(((SYSTEM_CLOCK_SOURCE_HZ) * (SYSTICK_DELAY_SECOND)) - 1)

// Stack end address for the user section; defined in linker script
extern uint32_t user_stack_top;

extern void *__multiplexer;
extern void *user_alloc_pos;

extern uint32_t unused_RAM_start;

extern void *_erom;
extern void *_eram;

extern void main_yield(int argc, uint32_t **argv);

/*!
 * \brief Enable the SysTick timer.
 */
static void
systick_timer_enable(void)
{
	/* Reset the SYST_CSR register */
	SYST_CSR.as_uint32_t = 0;

	/* Set the reload value of the SYST_CVR register. */
	SYST_RVR.RELOAD = SYST_RVR_RELOAD_VALUE;

	/* SysTick uses the processor clock. */
	SYST_CSR.CLKSOURCE = 1;

	/* Count to 0 changes the SysTick exception status to
	 * pending. */
	SYST_CSR.TICKINT = 1;

	/* Counter is operating. */
	SYST_CSR.ENABLE = 1;
}

/**
 * Pip's main entry point.
 * If UART_DEBUG, sends printf messages on UART
 * If -DTRACE -DOS_USE_TRACE_SEMIHOSTING_DEBUG flags are set, send printf messages on the semihosting debug channel
 * We are in PRIV Thread Mode and we want to switch to the root partition
 * The root partition should be in Unprivileged Thread Mode using PSP.
 * However, switching to the unprivileged root partition is not possible yet, since the current location is in Pip's protected region.
 * Hence, a direct switch would trigger a MemFault.
 * Instead, we enter the Handler Mode with PendSV and launches the root partition (UNPRIV/PSP) as an exception return.
 */
__attribute__((section(".text_pip_init"), noreturn))
void pip_main (void)
{
#if defined(UART_DEBUG)
	init_uart();
#endif // UART_DEBUG

	trace_printf("Test1\n");
	puts("Test2\n");
	printf("Test3\n");
#if defined BENCHMARK
	START_BENCHMARK();

#endif // BENCHMARK

#if defined BENCHMARK_BASELINE_PRIV
	systick_timer_enable();
	main_benchmark();
	/* We should never end up here because the benchmark ended */
	__builtin_unreachable();
#endif

	// In order to launch the root partition in unprivileged mode,
	// we need to get into Handler mode, here by triggering the PENDSV

	/* Set the PendSV exception as pending by writing 1 to the
	 * PENDSVSET bit. */
	ICSR.PENDSVSET = 1;

	/* Trigger the PendSV exception immediately by synchronizing the
	 * execution stream with memory accesses. */
	__DSB();

	/* We should never end up here because the DSB instruction must
	 * immediately trigger the PendSV exception. */
	__builtin_unreachable();
}

#if !defined BENCHMARK_BASELINE_PRIV

/**
 * PendSV Handler
 * Handler mode: launch the root partition during exception return.
 */
__attribute__((section(".text_pip_init"), noreturn))
void PendSV_Handler(void)
{

	int externalIrqNumber = 32 * (SCnSCB->ICTR + 1);

	/* At reset, all priorities are equal to zero. Here, we want to mask
	 * interrupt using BASEPRI=1 below DebugMonitor. So set PendSV,
	 * SysTick and external interrupts at priority 1. */
	for (int irq = PendSV_IRQn; irq < externalIrqNumber; irq++)
	{
		NVIC_SetPriority(irq, 1);
	}

#if !defined BENCHMARK_WO_SYSTICK
	/* Enable the SysTick timer. */
	systick_timer_enable();
#endif

	/* Get the top of the PSP */
	uint32_t sp = (uint32_t)&user_stack_top;

#if defined BENCHMARK_BASELINE_UNPRIV

	// Version wo Pip / wo MPU / with app running in unprivileged mode
	uint32_t frame = (uint32_t) sp - 0x20; // Build benchmark frame
	__set_PSP(frame);
	// Thread mode is unprivileged
	__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk );
	__DMB(); __ISB(); __DSB();

	// exception return/exit frame
	// Stack frame when starting the benchmark
	uint32_t *framePtr = (uint32_t *)frame;
	framePtr[0] = 0;
	framePtr[1] = 0;
	framePtr[2] = 0;
	framePtr[3] = 0;
	framePtr[4] = 0;
	framePtr[5] = 0;
	framePtr[6] = (uint32_t)main_benchmark;
	framePtr[7] = 0 | (1 << 24);// T bit mandatroy: ARM Cortex M only supports Thumb instruction execution

	asm volatile("cpsie   i;" // enable interrupts (CLOCK)
				 " bx %0; "	  // branch to main in UNPRIV mode with PSP (EXC_RETURN=0xFFFFFFFD)

				 // Output operands
				 :

				 // Input operands
				 : "r"(0xFFFFFFFD)

				 // Clobbers
				 : "memory");
#elif !defined BENCHMARK_EMPTY

	// Initialize the root partition and init the MPU
	mal_init();

	/* Reserve on the stack the space necessary for structure. */
	sp -= sizeof(pip_interface_t);

	/* Retrive the root partition descriptor structure. */
	PDTable_t *rootPartitionDescriptor = getRootPartition();

	/* Copy the ID of the block containing the partition descriptor
	 * of the root partition. */
	pip_interface_t *pip_interface = (pip_interface_t *) sp;
	pip_interface->partDescId = (uint32_t *) rootPartitionDescriptor;

	/* Copy the block attributes of the block entries. */
	for (size_t i = 0; i < MPU_REGIONS_NB; i++)
	{
		BlockEntry_t *currentBlockEntry = rootPartitionDescriptor->mpu[i];

		if (currentBlockEntry != NULL)
		{
			pip_interface->mpu[i].blockentryaddr = (uint32_t *) currentBlockEntry;
			pip_interface->mpu[i].blockrange.startAddr = currentBlockEntry->blockrange.startAddr;
			pip_interface->mpu[i].blockrange.endAddr = currentBlockEntry->blockrange.endAddr;
			pip_interface->mpu[i].read = currentBlockEntry->read;
			pip_interface->mpu[i].write = currentBlockEntry->write;
			pip_interface->mpu[i].exec = currentBlockEntry->exec;
			pip_interface->mpu[i].accessible = currentBlockEntry->accessible;
		}
		else
		{
			pip_interface->mpu[i].blockentryaddr = NULL;
			pip_interface->mpu[i].blockrange.startAddr = 0;
			pip_interface->mpu[i].blockrange.endAddr = 0;
			pip_interface->mpu[i].read = 0;
			pip_interface->mpu[i].write = 0;
			pip_interface->mpu[i].exec = 0;
			pip_interface->mpu[i].accessible = 0;
		}
	}

	/* Copy the start and end address of the ROM. */
	pip_interface->romUnusedStart = (uint32_t) &__multiplexer;
	pip_interface->romEnd = (uint32_t) &_erom;

	/* Copy the start and end address of the RAM. */
	pip_interface->ramUnusedStart = (uint32_t) /*user_alloc_pos*/ unused_RAM_start;
	pip_interface->ramEnd = (uint32_t) &_eram;

	/* Reset the structure to ensure that the restored registers do
	 * not contain undefined value */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		pip_interface->context.registers[i] = 0;
	}

	/* Initialize the root partition context. */
	pip_interface->context.registers[R0]  = sp;
	pip_interface->context.registers[PC]  = (uint32_t) &__multiplexer;
	pip_interface->context.registers[SP]  = sp;
	pip_interface->context.pipflags       = 0;
	pip_interface->context.valid          = CONTEXT_VALID_VALUE;

	/* Switch to unprivileged Thread mode. */
	__set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk );
	__DMB(); __ISB(); __DSB();

	/* Yield to the root partition. */
	switchContextCont(getRootPartition(), 0, &pip_interface->context);
#endif // BENCHMARK_BASELINE_UNPRIV


		/* We should never end up here because the switchContextCont
	 * function never returns to the caller. */
		__builtin_unreachable();
}

#endif // BENCHMARK_BASELINE_PRIV
