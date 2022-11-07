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

#ifndef __BENCHMARK_HELPERS_H__
#define __BENCHMARK_HELPERS_H__

#include "nrf_gpio.h"

#if defined(NRF52840_XXAA)
#include "pca10056.h"
#endif

extern uint32_t __StackTop;
extern uint32_t __StackLimit;
extern uint32_t user_stack_limit;
extern uint32_t user_stack_top;
extern uint32_t user_mem_start;
extern uint32_t user_mem_end;
extern uint32_t main_stack_top;
extern uint32_t app_stack_top;


#if defined BENCHMARK_PIP
extern uint32_t rootSysTickStackBlockStart;
extern uint32_t rootSysTickStackBlockEnd;
extern uint32_t* rootid;
#endif

static uint32_t nbinterrupts = 0;

#define STACK_INIT_MARK 0xcafebeef

/* DWT (Data Watchpoint and Trace) registers, only exists on ARM Cortex with a DWT unit */
#define DWT_CONTROL (*((volatile uint32_t *)0xE0001000))
/*!< DWT Control register */
#define DWT_CYCCNTENA_BIT (1UL << 0)
/*!< CYCCNTENA bit in DWT_CONTROL register */
#define DWT_CYCCNT (*((volatile uint32_t *)0xE0001004))
/*!< DWT Cycle Counter register */
#define DEMCR (*((volatile uint32_t *)0xE000EDFC))
/*!< DEMCR: Debug Exception and Monitor Control Register */
#define TRCENA_BIT (1UL << 24)
/*!< Trace enable bit in DEMCR register */

#define InitCycleCounter() \
    DEMCR |= TRCENA_BIT
/*!< TRCENA: Enable trace and debug block DEMCR (Debug Exception and Monitor Control Register */

#define ResetCycleCounter() \
    DWT_CYCCNT = 0
/*!< Reset cycle counter */

#define EnableCycleCounter() \
    DWT_CONTROL |= DWT_CYCCNTENA_BIT
/*!< Enable cycle counter */

#define DisableCycleCounter() \
    DWT_CONTROL &= ~DWT_CYCCNTENA_BIT
/*!< Disable cycle counter */

#define GetCycleCounter() \
    DWT_CYCCNT
/*!< Read cycle counter register */

typedef struct cycles
{
    uint32_t init_end_timestamp;
    uint32_t handler_start_timestamp;
    uint32_t global_privileged_counter;
    uint32_t init_end_privileged_counter;
    uint32_t global_counter;
} cycles_t;

extern cycles_t cycles;

// DWM1001 User LEDs
#ifndef NRF52840_XXAA
#define LED_0 30 // Green
#define LED_1 31 // Blue
#define LED_2 22 // Red
#define LED_3 14 // Red

#define LEDS_NUMBER 4

#define LEDS_ACTIVE_STATE 0

#define LEDS_LIST                  \
    {                              \
        LED_0, LED_1, LED_2, LED_3 \
    }
#endif

#define BENCH_MSG_BASELINE_PRIV "********* BASELINE BENCHMARK APP IS PRIVILEGED ********\n"
#define BENCH_MSG_BASELINE_UNPRIV "********* BASELINE BENCHMARK APP IS UNPRIVILEGED ********\n"
#define BENCH_MSG_WITNESS "********* WITNESS ONLY **************\n"
#define BENCH_MSG_PIP_ROOT "********* PIP ROOT **************\n"
#define BENCH_MSG_PIP_CHILD "********* PIP CHILD **************\n"
#define BENCH_MSG_INIT                     \
    "\r\n\n"                               \
    "App   :  Pip-MPU\n\r"                 \
    "Built :  " __DATE__ " " __TIME__ "\n" \
    "CPU   :  %d MHz\n"                        \
    "\n"                                   \
    "\r\n",                                \
    CPU_MHZ

    int32_t
    prepare_stack_usage_measurement(uint32_t *lower_addr, uint32_t *upper_addr);
uint32_t finish_stack_usage_measurement(uint32_t *lower_addr, uint32_t *upper_addr);
void start_cycles_counting();
void run_benchmark();
void print_benchmark_msg();
void BENCHMARK_SINK();
void benchmark_results(uint32_t benchmark_data1, uint32_t benchmark_data2);

void init_timer0();

/*!
 * \brief Launches the benchmark init sequence procedure
*/
void START_BENCHMARK();

/*!
 * \brief System call that triggers the benchmark end sequence procedure
 */
// no SVC when privileged
void END_BENCHMARK(uint32_t user_stack_top, uint32_t childStackBlockStart, uint32_t child_partition_id);

#endif /* __BENCHMARK_HELPERS_H__ */
