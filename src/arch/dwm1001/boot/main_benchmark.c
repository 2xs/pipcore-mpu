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
#if defined BENCHMARK
#include <stdio.h>
#include "context.h"
#include "user_ADT.h"
#include "nrf52.h"
//#include "scb.h"
#include "svc.h"
#include "benchmark.h"
#include "nrf_gpio.h"



/* The address of the VIDT of the root partition. */
#define ROOT_PARTITION_VIDT  ((user_context_t **) 0x20003000)
/* The address of the VIDT of the child partition. */
#define CHILD_PARTITION_VIDT ((user_context_t **) 0x20006000)

static void child_partition(int argc, uint32_t **argv)
{
	/* Unstacking arguments from the stack. */
	uint32_t *childStackBlockLocalId    = argv[0];
	uint32_t *childFreeRamBlockLocalId  = argv[1];
	uint32_t *childFlashBlockLocalId    = argv[2];
	uint32_t *childPeriphBlockLocalId   = argv[3];
	uint32_t *childRam0BlockLocalId     = argv[4];

	printf("argc.....................: %d\n", argc);
	printf("childStackBlockLocalId...: %p\n", (void *) childStackBlockLocalId);
	printf("childFreeRamBlockLocalId.: %p\n", (void *) childFreeRamBlockLocalId);
	printf("childFlashBlockLocalId...: %p\n", (void *) childFlashBlockLocalId);
	printf("childPeriphBlockLocalId..: %p\n", (void *) childPeriphBlockLocalId);
	printf("childRam0BlockLocalId....: %p\n", (void *) childRam0BlockLocalId);

	for (;;)
	{
		puts("Hello world from the child partition!\n");

		/* Yield to the parent partition by saving the current context
		 * at the address at index 1 of the child partition's VIDT and
		 * restoring the context of the parent at the address at index
		 * 0 of the parent partition's VIDT. The flagOnYield and
		 * flagOnWake are left at zero. */
		Pip_yield(0, 0, 1, 0, 0);
	}
}

/*
 * Simple computation.
 * Minimal code letting a SysTick interrupt to happen.
 */
void witness(){
	for(int i = 0; i<10000;i++);
}

void print_benchmark_msg(){
	// Start benchmark initialisation
	printf(BENCH_MSG_INIT);
#if defined BENCHMARK_BASELINE
	printf(BENCH_MSG_BASELINE);
#endif
#if defined BENCHMARK_WITNESS_ONLY
	printf(BENCH_MSG_WITNESS);
#endif
}

/**
 *	Fills the memory region [lower_addr, upper_addr] with a specific mark value.
 *	From lower address to upper address.
 **/
int32_t prepare_stack_usage_measurement(uint32_t *lower_addr, uint32_t *upper_addr)
{
	if (upper_addr < lower_addr)
		return -1;
	uint32_t *p = lower_addr;
	while (p < upper_addr)
		*p++ = STACK_INIT_MARK;
	return 0;
}

/**
 *	Computes the memory region [lower_addr, upper_addr] usage.
 *	Check from lower to upper addresses in case some bytes have been jumped off.
 **/
uint32_t finish_stack_usage_measurement(uint32_t *lower_addr, uint32_t *upper_addr)
{
	if (upper_addr < lower_addr)
		return false;

	uint32_t *p = lower_addr;
	while (p < upper_addr)
		if (*p++ == STACK_INIT_MARK)
			continue;
		else
		{
			// real stack limit hit
			break;
		}
	if (p <= lower_addr + 1){
		printf("Warning: probable stack overflow at lower_addr 0x%x\n", lower_addr);
		return 0;
	}
	return (upper_addr - p + 1)*4; // stack is descending so base is top + convert number to bytes
}

/**
 *	Triggers the cycle counting using the DWT unit only accessible as privileged.
	*	From ARM documentation: PPB = [0xE0000000 - 0xE0100000]
	*	Unprivileged access to the PPB causes BusFault errors unless otherwise stated.
	**/
void
start_cycles_counting()
	{
		// Enable cycle counting
		InitCycleCounter();	 // enable DWT
		ResetCycleCounter(); // reset DWT cycle counter
		// Enable SysTick interrupt: value can't be too low else it will interrupt in the SysTick_Handler itself and loop forever
		/*if (SysTick_Config(SystemCoreClock / 1000)) // Generate interrupt each 1 ms: SystemCoreClock is the nb of ticks in a second
		{
			printf("Benchmark Init error: can't load SysTick\n");
			while (1)
				;
		}*/
		// Trigger External benchmark start
		nrf_gpio_pin_dir_set(13, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(13, 1);
		EnableCycleCounter(); // start counting
	}

void BENCHMARK_INITIALISE()
{
#if defined BENCHMARK_IN_PIP_CHILD
		// empty vs empty pip root = Cost of Pip root partition set up
#else

#endif
		initialise_benchmark(); // embench init
		// warm_caches(WARMUP_HEAT);
}

void BENCHMARK_FINALISE()
{
#if defined BENCHMARK_IN_PIP_CHILD
	// empty vs empty pip root = Cost of Pip root partition set up
#endif
}
// - BENCHMARK_EMPTY_PIP_ROOT
// empty vs empty pip root = Cost of Pip root partition set up
// - BENCHMARK_BASELINE_IN_PIP_ROOT
// baseline wo Pip vs baseline in pip root = Total pip cost
// empty pip root vs baseline in pip root = Cost of root virtualisation
// BENCH
// - BENCHMARK_EMPTY_PIP_CHILD
//  empty root vs empty child = Cost of Pip child set up
// Child set up
// Yield root
// Child tear down
// - BENCHMARK_BASELINE_IN_PIP_CHILD
// empty child vs baseline in child = Cost of child virtualisation
// baseline in root vs baseline in child = Cost of child virtualisation + set up
// baseline wo root vs baseline in child = Total cost of protection in child
// Child set up
// BENCH
// Yield root
// Child tear down
void main_benchmark() // int argc, uint32_t **argv)
{
#ifndef BENCHMARK_EMPTY /* Don't launch benchmark with empty flag */
	// Benchmark execution
#if defined BENCHMARK_WITNESS_ONLY
	// Witness
	witness();
#else
	BENCHMARK_INITIALISE(); // do nothing or prepare child
	volatile int result;
	int correct;
	result = benchmark();
	correct = verify_benchmark(result);
	if (!correct)
	{
		printf("***ERROR***\nBad result\n");
	}
	// benchmark();
	BENCHMARK_FINALISE(); // do nothing or destruct child
#endif // BENCHMARK_WITNESS_ONLY
#endif // BENCHMARK_EMPTY
		END_BENCHMARK();
		printf("***ERROR***\nShould never be reached\n");
		while (1);
}
#endif
