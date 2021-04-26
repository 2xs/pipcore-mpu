.cpu cortex-m4
.thumb


    .section .isr_vector, "ax"
    .align 2
    .globl __isr_vector
__isr_vector:
    .long   __StackTop                  /* Top of Stack */
    .long   Reset_Handler
    .long   NMI_Handler
    .long   HardFault_Handler
    .long   MemoryManagement_Handler
    .long   BusFault_Handler
    .long   UsageFault_Handler
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   SVC_Handler
    .long   DebugMon_Handler
    .long   0                           /*Reserved */
    .long   PendSV_Handler
    .long   SysTick_Handler

  /* External Interrupts */
    .long   POWER_CLOCK_IRQHandler
    .long   RADIO_IRQHandler
    .long   UARTE0_UART0_IRQHandler
    .long   SPIM0_SPIS0_TWIM0_TWIS0_SPI0_TWI0_IRQHandler
    .long   SPIM1_SPIS1_TWIM1_TWIS1_SPI1_TWI1_IRQHandler
    .long   NFCT_IRQHandler
    .long   GPIOTE_IRQHandler
    .long   SAADC_IRQHandler
    .long   TIMER0_IRQHandler
    .long   TIMER1_IRQHandler
    .long   TIMER2_IRQHandler
    .long   RTC0_IRQHandler
    .long   TEMP_IRQHandler
    .long   RNG_IRQHandler
    .long   ECB_IRQHandler
    .long   CCM_AAR_IRQHandler
    .long   WDT_IRQHandler
    .long   RTC1_IRQHandler
    .long   QDEC_IRQHandler
    .long   COMP_LPCOMP_IRQHandler
    .long   SWI0_EGU0_IRQHandler
    .long   SWI1_EGU1_IRQHandler
    .long   SWI2_EGU2_IRQHandler
    .long   SWI3_EGU3_IRQHandler
    .long   SWI4_EGU4_IRQHandler
    .long   SWI5_EGU5_IRQHandler
    .long   TIMER3_IRQHandler
    .long   TIMER4_IRQHandler
    .long   PWM0_IRQHandler
    .long   PDM_IRQHandler
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   MWU_IRQHandler
    .long   PWM1_IRQHandler
    .long   PWM2_IRQHandler
    .long   SPIM2_SPIS2_SPI2_IRQHandler
    .long   RTC2_IRQHandler
    .long   I2S_IRQHandler
    .long   FPU_IRQHandler
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */
    .long   0                           /*Reserved */

    .size __isr_vector, . - __isr_vector

/* Reset Handler */
    .text
    .thumb
    .thumb_func
    .align 1
    .globl Reset_Handler
    .type Reset_Handler, %function
Reset_Handler:
    bl _start

NMI_Handler:
    nop
BusFault_Handler:
    nop
UsageFault_Handler:
    nop
SVC_Handler:
    nop
DebugMon_Handler:
    nop
PendSV_Handler:
    nop
SysTick_Handler:
    nop

/* IRQ Handlers */

    .globl  Default_Handler
    .type   Default_Handler, %function
Default_Handler:
    b       .
    .size   Default_Handler, . - Default_Handler

    .macro  IRQ handler
    .weak   \handler
    .set    \handler, Default_Handler
    .endm

    IRQ  POWER_CLOCK_IRQHandler
    IRQ  RADIO_IRQHandler
    IRQ  UARTE0_UART0_IRQHandler
    IRQ  SPIM0_SPIS0_TWIM0_TWIS0_SPI0_TWI0_IRQHandler
    IRQ  SPIM1_SPIS1_TWIM1_TWIS1_SPI1_TWI1_IRQHandler
    IRQ  NFCT_IRQHandler
    IRQ  GPIOTE_IRQHandler
    IRQ  SAADC_IRQHandler
    IRQ  TIMER0_IRQHandler
    IRQ  TIMER1_IRQHandler
    IRQ  TIMER2_IRQHandler
    IRQ  RTC0_IRQHandler
    IRQ  TEMP_IRQHandler
    IRQ  RNG_IRQHandler
    IRQ  ECB_IRQHandler
    IRQ  CCM_AAR_IRQHandler
    IRQ  WDT_IRQHandler
    IRQ  RTC1_IRQHandler
    IRQ  QDEC_IRQHandler
    IRQ  COMP_LPCOMP_IRQHandler
    IRQ  SWI0_EGU0_IRQHandler
    IRQ  SWI1_EGU1_IRQHandler
    IRQ  SWI2_EGU2_IRQHandler
    IRQ  SWI3_EGU3_IRQHandler
    IRQ  SWI4_EGU4_IRQHandler
    IRQ  SWI5_EGU5_IRQHandler
    IRQ  TIMER3_IRQHandler
    IRQ  TIMER4_IRQHandler
    IRQ  PWM0_IRQHandler
    IRQ  PDM_IRQHandler
    IRQ  MWU_IRQHandler
    IRQ  PWM1_IRQHandler
    IRQ  PWM2_IRQHandler
    IRQ  SPIM2_SPIS2_SPI2_IRQHandler
    IRQ  RTC2_IRQHandler
    IRQ  I2S_IRQHandler
    IRQ  FPU_IRQHandler

  .end
