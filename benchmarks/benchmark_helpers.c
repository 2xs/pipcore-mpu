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
#include "nrf52.h"
#include "benchmark_helpers.h"
#include "nrf_gpio.h"
#include "scs.h"

cycles_t cycles = {.init_end_timestamp = 0, .handler_start_timestamp = 0, .global_privileged_counter = 0, .init_end_privileged_counter = 0, .global_counter = 0};
uint32_t main_stack_top;
uint32_t app_stack_top;
/* TODO: these variables are not accepted as extern */
#if defined BENCHMARK_PIP_CHILD
uint32_t *childStackBlockStart;
uint32_t *childStackBlockEnd;
#endif

void START_BENCHMARK(){
	print_benchmark_msg();
	register int RSP __asm("sp");
	main_stack_top = RSP;
	prepare_stack_usage_measurement(&__StackLimit, main_stack_top);	 /* pip stack: don't erase previous stacked values */
	prepare_stack_usage_measurement(&user_mem_start, &user_mem_end); /* mark RAM */
	__DMB();
	__ISB();
	__DSB();
	start_cycles_counting();
}

void shutoff(){
	//__WFE();
	while(1);
}

void BENCHMARK_SINK(){
	//__WFE();
	//NRF_POWER->SYSTEMOFF = 1;
	//NRF_POWER->TASKS_LOWPWR = 1;
	// Enter System ON sleep mode
	//nrf_pwr_mgmt_shutdown(NRF_PWR_MGMT_SHUTDOWN_GOTO_DFU);
	/*__WFI();
	__SEV();
	__WFI();
	__DSB();*/

	/* Solution for simulated System OFF in debug mode */
	while (true)
	{
		shutoff();
	}
	// sd_power_system_off() ;
	while (1);
}

void print_benchmark_msg(){
	// Start benchmark initialisation
	printf(BENCH_MSG_INIT);
	printf("WARNING: Monitor stack usage on: RAM is erased from user_mem_start and up\n");
#if defined BENCHMARK_BASELINE_PRIV
	printf(BENCH_MSG_BASELINE_PRIV);
#elif defined BENCHMARK_BASELINE_UNPRIV
	printf(BENCH_MSG_BASELINE_UNPRIV);
#elif defined BENCHMARK_WITNESS_ONLY
	printf(BENCH_MSG_WITNESS);
#elif defined BENCHMARK_PIP_ROOT
	printf(BENCH_MSG_PIP_ROOT);
#elif defined BENCHMARK_PIP_CHILD
	printf(BENCH_MSG_PIP_CHILD);
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
	return (upper_addr - p)*4; // stack is descending so base is top + convert number to bytes
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
	// Trigger External benchmark start
	nrf_gpio_pin_dir_set(13, NRF_GPIO_PIN_DIR_OUTPUT);
	nrf_gpio_pin_write(13, 1);
	nrf_gpio_pin_dir_set(LED_0, NRF_GPIO_PIN_DIR_OUTPUT);
	nrf_gpio_pin_write(LED_0, 0); // 0 = Light the LED
	nrf_gpio_pin_dir_set(LED_1, NRF_GPIO_PIN_DIR_OUTPUT);
	nrf_gpio_pin_write(LED_1, 0); // 0 = Light the LED
	nrf_gpio_pin_dir_set(LED_2, NRF_GPIO_PIN_DIR_OUTPUT);
	nrf_gpio_pin_write(LED_2, 0); // 0 = Light the LED
	nrf_gpio_pin_dir_set(LED_3, NRF_GPIO_PIN_DIR_OUTPUT);
	nrf_gpio_pin_write(LED_3, 0); // 0 = Light the LED*/
	/*
	int j = 0, i = 0;
	for (int k = 0 ; k < 5 ; k++){
		for (i = 0; i < 10000000; i++)
			j += i;
		nrf_gpio_pin_dir_set(13, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(13, 1);
		nrf_gpio_pin_dir_set(LED_0, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(LED_0, 0); // 0 = Light the LED
		nrf_gpio_pin_dir_set(LED_1, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(LED_1, 0); // 0 = Light the LED
		nrf_gpio_pin_dir_set(LED_2, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(LED_2, 0); // 0 = Light the LED
		nrf_gpio_pin_dir_set(LED_3, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(LED_3, 0); // 0 = Light the LED
		j = 0;
		for(i = 0 ; i<10000000;i++)
			j += i;
		nrf_gpio_pin_dir_set(13, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(13, j&1);
		nrf_gpio_pin_dir_set(LED_0, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(LED_0, 1); // 0 = Light the LED
		nrf_gpio_pin_dir_set(LED_1, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(LED_1, 1); // 0 = Light the LED
		nrf_gpio_pin_dir_set(LED_2, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(LED_2, 1); // 0 = Light the LED
		nrf_gpio_pin_dir_set(LED_3, NRF_GPIO_PIN_DIR_OUTPUT);
		nrf_gpio_pin_write(LED_3, 1); // 0 = Light the LED
	}*/
	EnableCycleCounter(); // start counting
}

void benchmark_results(uint32_t benchmark_data1, uint32_t benchmark_data2)
{
	uint32_t priv_counter = cycles.global_privileged_counter;
	uint32_t priv_counter_after_init = cycles.init_end_privileged_counter;
	// Stack usage measurements
	app_stack_top = benchmark_data1;
	uint32_t main_stack_usage = finish_stack_usage_measurement(&__StackLimit, main_stack_top); /* main (Pip) stack */
#if defined BENCHMARK_BASELINE_UNPRIV
	uint32_t app_stack_usage = finish_stack_usage_measurement(&user_stack_limit, app_stack_top); /* app stack */
#elif defined BENCHMARK_PIP_ROOT
	uint32_t app_stack_usage = finish_stack_usage_measurement(0x20008000, app_stack_top); /* app stack */
#elif defined BENCHMARK_PIP_CHILD
	childStackBlockStart = benchmark_data2;
	uint32_t app_stack_usage = finish_stack_usage_measurement(childStackBlockStart, app_stack_top); /* app stack */
#else // stack is priv, only main stack exists and all ticks are privileged
	uint32_t app_stack_usage = finish_stack_usage_measurement(&__StackLimit, app_stack_top); /* app stack */
	main_stack_usage = app_stack_usage;
	priv_counter = cycles.global_counter;
	priv_counter_after_init = cycles.init_end_timestamp;
#endif
	printf("Benchmark results after %d runs:\n", RUNS);
	printf("Ticks:%d\n", cycles.global_counter);
	printf("Init end counter:%d\n", cycles.init_end_timestamp);
	printf("Privileged counter:%d\n", priv_counter);
	printf("Privileged counter after init:%d\n", priv_counter_after_init);
	printf("Main stack usage:%d\n", main_stack_usage);
	printf("App stack usage:%d\n", app_stack_usage);
	// Trigger External benchmark end
	nrf_gpio_pin_dir_set(13, NRF_GPIO_PIN_DIR_OUTPUT);
	nrf_gpio_pin_write(13, 0);
	nrf_gpio_pin_dir_set(LED_0, NRF_GPIO_PIN_DIR_OUTPUT);
	nrf_gpio_pin_write(LED_0, 1); // 0 = Light the LED
	//dump_partition(rootid);
	//dump_partition(child1PartDescBlock.address);
	BENCHMARK_SINK();
}

#endif /* BENCHMARK */
