#include <sys/coproc.h>

.extern kernel_start
.extern ial_svc_handler
.extern ial_undef_handler
.extern ial_prefetch_abort_handler
.extern ial_data_abort_handler
.extern ial_irq_handler_s
.extern ial_fiq_handler_s
.extern ial_resume_ctx

.set MASK_BITS, CPSR_FIQ|CPSR_IRQ|CPSR_A

.code 32
.section .text.start
.global int_vector
int_vector:
	ldr pc, =boot_reset
	ldr pc, =ial_undef_handler
	ldr pc, =ial_svc_handler
	ldr pc, =ial_prefetch_abort_handler
	ldr pc, =ial_data_abort_handler
	ldr pc, =boot_reserved
	ldr pc, =ial_irq_handler_s
	ldr pc, =ial_fiq_handler_s

boot_reserved:
	b .

boot_reset:
	/* TODO: when SE available, should we run everything in normal world ? */

	/* TODO: SMP */
.if(0)
	READ_CP_ASM(r5, ID_MPIDR)
	dsb
	ands r5, #0xff
	bne loop
.endif

.core0:
	/* Go supervisor, interrupt masked */
	ldr r5, =(ARM_MODE_SVC|MASK_BITS)
	msr cpsr, r5

	ldr r5, =int_vector						@ Setup VBAR
	WRITE_CP_ASM(r5, ID_VBAR)

	ldr sp, =svc_stack						@ Setup SVC stack

	ldr r5, =(ARM_MODE_ABORT|MASK_BITS)	@ Set Abort stack
	msr cpsr_fc, r5
	ldr sp, =abort_stack

	ldr r5, =(ARM_MODE_UNDEF|MASK_BITS)	@ Set undef stack
	msr cpsr_fc, r5
	ldr sp, =undef_stack

	ldr r5, =(ARM_MODE_IRQ|MASK_BITS)		@ Set irq stack
	msr cpsr_fc, r5
	ldr sp, =irq_stack

	ldr r5, =(ARM_MODE_FIQ|MASK_BITS)		@ Set fiq stack
	msr cpsr_fc, r5
	ldr sp, =fiq_stack

	ldr r5, =(ARM_MODE_SVC|MASK_BITS)		@ back to SVC
	msr cpsr_fc, r5

	bl kernel_start
	b ial_resume_ctx
loop:
	wfe
	b loop

.section .bss.kstack
.align(4)
stack_base:
.org .+0x1000
.global svc_stack
svc_stack:
/* Fake stacks for 5 registers */
abort_stack:
.org .+20
undef_stack:
.org .+20
irq_stack:
.org .+20
fiq_stack:
.org .+20
