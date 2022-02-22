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

.cpu cortex-m4
.thumb

    .section .isr_vector, "ax"
    .align 2
    .globl __isr_vector

__isr_vector:
    .long   __StackTop         /* Top of Stack */
    .long   Reset_Handler      /* Reset        */
    .long   Interrupt_Handler  /* NMI          */
    .long   HardFault_Handler      /* HardFault    */
    .long   MemManage_Handler  /* MemManage */
    .long   BusFault_Handler      /* BusFault */
    .long   UsageFault_Handler      /* UsageFault */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   SVC_Handler        /* SVCall */
    .long   DebugMon_Handler      /* DebugMonitor */
    .long   0                  /* Reserved */
    .long   PendSV_Handler     /* PendSV */
#if defined BENCHMARK_BASELINE
    .long   SysTick_Handler    /* Systick */
#else
    .long   Interrupt_Handler  /* SysTick */
#endif /* BENCHMARK_BASELINE */

    /* External Interrupts */
    .long   Interrupt_Handler  /* POWER_CLOCK_IRQHandler */
    .long   Interrupt_Handler  /* RADIO_IRQHandler       */
    .long   Interrupt_Handler  /* UARTE0_UART0_IRQHandler */
    .long   Interrupt_Handler  /* SPIM0_SPIS0_TWIM0_TWIS0_SPI0_TWI0_IRQHandler */
    .long   Interrupt_Handler  /* SPIM1_SPIS1_TWIM1_TWIS1_SPI1_TWI1_IRQHandler */
    .long   Interrupt_Handler  /* NFCT_IRQHandler */
    .long   Interrupt_Handler  /* GPIOTE_IRQHandler */
    .long   Interrupt_Handler  /* SAADC_IRQHandler */
    .long   Interrupt_Handler  /* TIMER0_IRQHandler */
    .long   Interrupt_Handler  /* TIMER1_IRQHandler */
    .long   Interrupt_Handler  /* TIMER2_IRQHandler */
    .long   Interrupt_Handler  /* RTC0_IRQHandler */
    .long   Interrupt_Handler  /* TEMP_IRQHandler */
    .long   Interrupt_Handler  /* RNG_IRQHandler */
    .long   Interrupt_Handler  /* ECB_IRQHandler */
    .long   Interrupt_Handler  /* CCM_AAR_IRQHandler */
    .long   Interrupt_Handler  /* WDT_IRQHandler */
    .long   Interrupt_Handler  /* RTC1_IRQHandler */
    .long   Interrupt_Handler  /* QDEC_IRQHandler */
    .long   Interrupt_Handler  /* COMP_LPCOMP_IRQHandler */
    .long   Interrupt_Handler  /* SWI0_EGU0_IRQHandler */
    .long   Interrupt_Handler  /* SWI1_EGU1_IRQHandler */
    .long   Interrupt_Handler  /* SWI2_EGU2_IRQHandler */
    .long   Interrupt_Handler  /* SWI3_EGU3_IRQHandler */
    .long   Interrupt_Handler  /* SWI4_EGU4_IRQHandler */
    .long   Interrupt_Handler  /* SWI5_EGU5_IRQHandler */
    .long   Interrupt_Handler  /* TIMER3_IRQHandler */
    .long   Interrupt_Handler  /* TIMER4_IRQHandler */
    .long   Interrupt_Handler  /* PWM0_IRQHandler */
    .long   Interrupt_Handler  /* PDM_IRQHandler */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   Interrupt_Handler  /* MWU_IRQHandler */
    .long   Interrupt_Handler  /* PWM1_IRQHandler */
    .long   Interrupt_Handler  /* PWM2_IRQHandler */
    .long   Interrupt_Handler  /* SPIM2_SPIS2_SPI2_IRQHandler */
    .long   Interrupt_Handler  /* RTC2_IRQHandler */
    .long   Interrupt_Handler  /* I2S_IRQHandler */
    .long   Interrupt_Handler  /* FPU_IRQHandler */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */
    .long   0                  /* Reserved */

    .size __isr_vector, . - __isr_vector

.end
