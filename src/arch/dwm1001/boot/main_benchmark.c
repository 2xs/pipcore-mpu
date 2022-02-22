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
#include "svc.h"
#include "benchmark.h"
#include "nrf_gpio.h"
#include "allocator.h"


void BENCHMARK_SINK(){
	while (1);
}
/*
 * Simple sleep.
 * Minimal code letting a SysTick interrupt to happen.
 */
void witness(){
	for (int i = 0; i < 0x2000000; i++)
	{
		__asm__("nop");
	}
}

void print_benchmark_msg(){
	// Start benchmark initialisation
	printf(BENCH_MSG_INIT);
	printf("WARNING: Monitor stack usage on: RAM is erased from user_mem_start and up");
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
	EnableCycleCounter(); // start counting
}

/*!
 * \def PD_BLOCK_SIZE
 *
 * \brief Size of a partition descriptor block.
 */
#define PD_BLOCK_SIZE 120

/*!
 * \def KS_BLOCK_SIZE
 *
 * \brief Size of a kernel structure block.
 */
#define KS_BLOCK_SIZE 512

/*!
 * \def VIDT_BLOCK_SIZE
 *
 * \brief Size of a VIDT block.
 */
#define VIDT_BLOCK_SIZE  512

/*!
 * \def CONTEXT_BLOCK_SIZE
 *
 * \brief Size of a context block.
 */
#define CONTEXT_BLOCK_SIZE 76

/*!
 * \def DISABLE_INTERRUPTS
 *
 * \brief Value used to disable interrupts with Pip_setIntState.
 */
#define DISABLE_INTERRUPTS 0

/*!
 * \def ENABLE_INTERRUPTS
 *
 * \brief Value used to enable interrupts with Pip_setIntState.
 */
#define ENABLE_INTERRUPTS 1

/*!
 * \def ROOT_PARTITION_VIDT
 *
 * \brief The address of the VIDT of the root partition.
 */
#define ROOT_PARTITION_VIDT \
	((user_context_t **) rootVidtBlock.address)

/*!
 * \def CHILD_PARTITION_VIDT
 *
 * \brief The address of the VIDT of the child partition.
 */
/*#define CHILD_PARTITION_VIDT \
	((user_context_t **) childVidtBlock.address)
*/
/*!
 * \def PANIC
 *
 * \brief Print a message and loop forever.
 */
#define PANIC(...) \
	do \
	{ \
		printf(__VA_ARGS__); \
		for (;;); \
	} while (0)


/*!
 * \brief Enumeration of some VIDT index.
 */
typedef  enum vidt_index_e
{
	/*!
	 * \brief The default index of the main context of the
	 *        partition.
	 */
	DEFAULT_INDEX = 0,

	/*!
	 * \brief The index containing a pointer to the address at which
	 *        the interrupted context is stored if its pipflags has a
	 *        value equal to 0.
	 */
	CLI_SAVE_INDEX = 8,

	/*!
	 * \brief The index containing a pointer to the address at which
	 *        the interrupted context is stored if its pipflags has a
	 *        value other than 0.
	 */
	STI_SAVE_INDEX = 9,

	/*!
	 * \brief The index containing a pointer to the context loaded
	 *        during a SysTick interrupt.
	 */
	SYSTICK_INDEX = 15
} vidt_index_t;

/*!
 * \brief The start address of the RAM 1 block.
 */
extern void *user_alloc_pos;

uint32_t rootSysTickStackBlockStart;
uint32_t rootSysTickStackBlockEnd;

block_t rootKernStructBlock;
block_t rootVidtBlock;
uint32_t ram1_printf;
uint32_t rootid;

/*!
 * \brief Initialize a VIDT with NULL addresses.
 *
 * \param context A VIDT as an array of pointers.
 */
static void
initializeVidt(user_context_t **vidt, size_t blockSize)
{
	size_t vidtEntryNumber = blockSize / sizeof(void *);

	for (size_t i = 0; i < vidtEntryNumber; i++)
	{
		vidt[i] = NULL;
	}
}

/*!
	* \brief Initialize a context with zeros.
	*
	* \param context A pointer to the context to initialize.
	*/
static void
initializeContext(user_context_t *context)
{
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		context->registers[i] = 0;
	}

	context->pipflags = 0;
	context->valid = 0;
}


/*!
 * \brief This handler is a simple round-robin scheduler called at
 *        each SysTick interrupt.
 */
static void
systick_handler(void)
{
	// Restore interrupted context
	/*uint32_t reg = ROOT_PARTITION_VIDT[DEFAULT_INDEX]->registers[PC];
	uint32_t reg0 = ROOT_PARTITION_VIDT[DEFAULT_INDEX]->registers[SP];
	printf("%d", reg);// = (uint32_t)scheduler;
	printf("%d", reg0);// = sp;
	printf(ROOT_PARTITION_VIDT[DEFAULT_INDEX]->valid);// = CONTEXT_VALID_VALUE;
	*/
	// printf
	/*if (!Pip_mapMPU(rootid, ram1_printf, 7))
	{
		PANIC("Failed to map ram1_printf...\n");
	}*/

	//printf("Hello");
	//printf("Hello");

	if (!Pip_mapMPU(rootid, rootVidtBlock.id, 4))
	{
		PANIC("Failed to map rootVidtBlock...\n");
	}

	user_context_t *ctx = (user_context_t *)((user_context_t **)rootVidtBlock.address)[STI_SAVE_INDEX];

	/*for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		uint32_t t = ctx->registers[i];
		printf("%x", t);
	}*/

		uint32_t frame = (ctx->registers[SP]) - 15*sizeof(uint32_t); // Build benchmark frame FRAME_SIZE);

		// Copy registers R0 to R3, R12, LR, PC and xPSR to the stack of
		 // the callee.
		uint32_t *framePtr = (uint32_t *)frame;
		framePtr[0] = ctx->registers[PC];
		//framePtr[0] = ctx->registers[R1];
		framePtr[1] = ctx->registers[R2];
		framePtr[2] = ctx->registers[R3];
		framePtr[3] = ctx->registers[R4];
		framePtr[4] = ctx->registers[R5];
		framePtr[5] = ctx->registers[R6];
		//framePtr[7] = ctx->registers[XPSR];// | (1 << 24);*/
		framePtr[6] = ctx->registers[R7];
		framePtr[7] = ctx->registers[R8];
		framePtr[8] = ctx->registers[R9];
		framePtr[9] = ctx->registers[R10];
		framePtr[10] = ctx->registers[R11];
		framePtr[11] = ctx->registers[R12];
		framePtr[12] = ctx->registers[LR];
		framePtr[13] = ctx->registers[R0];
		//printf("PC set at: %x\n", ctx->registers[PC]);
		framePtr[14] = ctx->registers[PC] | (1 << 0);
		//printf("PC set at: %x\n", framePtr[14]);

			/*asm inline volatile(
				"msr     psr, %0;"
				// Output operands
				:
				// Input operands
				: "r"(ctx->registers[XPSR])

				// Clobbers
				: "memory");*/

			/*stmdb sp !, { r4, r5, r6, r7, r8, lr }
			000004b0 : sub sp, #8*/

			__asm__ inline __volatile__("mov     sp, %0;"
										:
										: "r"(frame)
										: "sp", "memory");

		__asm__ inline __volatile__(
			"pop     {r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr};"
			"mov r0, #1;"
			"svc #14;" // Enable interrupt again now
			"pop     {r0};"
			:
			:
			: "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11", "r12", "lr");
		__asm__ inline __volatile__(
			//"add sp,#1;"
			//"ldmia.w sp !,{pc}; "
			"pop     {pc};"
			//"bx sp;"
			//"b %0;"
			:
			: //"r"(ctx->registers[PC])
			: "pc");

		/*asm inline __volatile__("BX %0"
			:
			: "r"(ctx->registers[PC]));*/

}

void BENCHMARK_INITIALISE(int argc, uint32_t **argv)
{
#if defined BENCHMARK_PIP_ROOT
	/* Global ID of the block containing the partition descriptor
	 * of the root partition. */
	uint32_t *rootPartDescBlockId = argv[0];

	/* Block 0: FLASH, from 0x00000000 to 0x00080000, RX */
	uint32_t *rootFlashBlockLocalId = argv[1];

	/* Block 1: RAM, from 0x20000000 to user_alloc_pos-1, RW */
	uint32_t *rootRam0BlockLocalId = argv[2];

	/* Block 2: RAM, from user_alloc_pos to 0x20007FFF, RW */
	uint32_t *rootRam1BlockLocalId = argv[3];

	/* Block 3: RAM, from 0x20008000 to _eram, RW */
	uint32_t *rootRam2BlockLocalId = argv[4];

	/* Block 4: PERIPH, from 0x40000000 to 0x5FFFFFFF, RWX */
	uint32_t *rootPeriphBlockLocalId = argv[5];

	//puts("Hello world from the root partition!");

	/* Not used. */
	(void)rootPeriphBlockLocalId;
	(void)rootRam2BlockLocalId;
	(void)argc;
	ram1_printf = rootRam1BlockLocalId;
	rootid = rootPartDescBlockId;

		/*
		 * Initialization of the block allocator.
		 */

	allocatorInitialize(rootRam1BlockLocalId, user_alloc_pos);

	/*
	 * Create blocks for the kernel structures of the root
	 * partition.
	 */

	if (!allocatorAllocateBlock(&rootKernStructBlock, KS_BLOCK_SIZE, 0))
	{
		PANIC("Failed to allocate rootKernStructBlock...\n");
	}

	if (!Pip_prepare(rootPartDescBlockId, -1, rootKernStructBlock.id))
	{
		PANIC("Failed to prepare rootPartDescBlockId...\n");
	}

	if (!allocatorAllocateBlock(&rootKernStructBlock, KS_BLOCK_SIZE, 0))
	{
		PANIC("Failed to allocate rootKernStructBlock...\n");
	}

	if (!Pip_prepare(rootPartDescBlockId, -1, rootKernStructBlock.id))
	{
		PANIC("Failed to prepare rootPartDescBlockId...\n");
	}

	if (!allocatorAllocateBlock(&rootKernStructBlock, KS_BLOCK_SIZE, 1))
	{
		PANIC("Failed to allocate rootKernStructBlock...\n");
	}

	if (!Pip_prepare(rootPartDescBlockId, -1, rootKernStructBlock.id))
	{
		PANIC("Failed to prepare rootPartDescBlockId...\n");
	}

	/*
	 * Create a block for the VIDT of the root partition.
	 */


	if (!allocatorAllocateBlock(&rootVidtBlock, VIDT_BLOCK_SIZE, 0))
	{
		PANIC("Failed to allocate rootVidtBlock...\n");
	}

	block_t rootSysTickStackBlock;

	if (!allocatorAllocateBlock(&rootSysTickStackBlock, 1024, 0))
	{
		PANIC("Failed to allocate rootSysTickStackBlock...\n");
	}
	rootSysTickStackBlockStart = rootSysTickStackBlock.address;
	rootSysTickStackBlockEnd = rootSysTickStackBlock.address + rootSysTickStackBlock.size;

	block_t rootSysTickContextBlock;

	if (!allocatorAllocateBlock(&rootSysTickContextBlock, CONTEXT_BLOCK_SIZE, 0))
	{
		PANIC("Failed to allocate rootSysTickContextBlock...\n");
	}

	/*
	 * Add the block containing the root's VIDT and the block
	 * containing the root's context into the physical MPU
	 * of the root partition since we need to write in it.
	 */

	if (!Pip_mapMPU(rootPartDescBlockId, rootVidtBlock.id, 5))
	{
		PANIC("Failed to map rootVidtBlock...\n");
	}

	if (!Pip_mapMPU(rootPartDescBlockId, rootSysTickContextBlock.id, 6))
	{
		PANIC("Failed to map rootFlashBlockGlobalId...\n");
	}

	/*
	 * Calculate the stack address from the stack block.
	 */

	uint32_t sp =
		rootSysTickStackBlock.address + rootSysTickStackBlock.size - 8;

	/*
	 * Initialize the VIDT of the root with NULL pointer.
	 */

	initializeVidt(ROOT_PARTITION_VIDT, rootVidtBlock.size);

	/*
	 * Set the context address at index SYSTICK_INDEX
	 * in the VIDT of the root partition.
	 */

	ROOT_PARTITION_VIDT[SYSTICK_INDEX] =
		(user_context_t *)rootSysTickContextBlock.address;

	/*
	 * Initialize the context with zero.
	 */

	initializeContext(ROOT_PARTITION_VIDT[SYSTICK_INDEX]);

	block_t stiBlock;

	// Init context for STI
	if (!allocatorAllocateBlock(&stiBlock, CONTEXT_BLOCK_SIZE, 0))
	{
		PANIC("Failed to allocate rootKernStructBlock...\n");
	}

	/*
	 * Set the context address at index SYSTICK_INDEX
	 * in the VIDT of the root partition.
	 */

	ROOT_PARTITION_VIDT[STI_SAVE_INDEX] =
		(user_context_t *)stiBlock.address;

	ROOT_PARTITION_VIDT[CLI_SAVE_INDEX] =
		(user_context_t *)stiBlock.address;

	if (!Pip_mapMPU(rootPartDescBlockId, stiBlock.id, 7))
	{
		PANIC("Failed to map rootTimerStackBlock...\n");
	}

	initializeContext(ROOT_PARTITION_VIDT[STI_SAVE_INDEX]);

	/*
	 * Initialize the context that will be restore when
	 * a SysTick interrupt will be triggered.
	 */

	ROOT_PARTITION_VIDT[SYSTICK_INDEX]->registers[PC] = (uint32_t)systick_handler;
	ROOT_PARTITION_VIDT[SYSTICK_INDEX]->registers[SP] = sp;
	ROOT_PARTITION_VIDT[SYSTICK_INDEX]->valid = CONTEXT_VALID_VALUE;

 /*
  * Set the VIDT block of the root partition.
  */

	if (!Pip_setVIDT(rootPartDescBlockId, rootVidtBlock.id))
	{
		PANIC("Failed to set the VIDT of the root partition...\n");
	}

	/*
	 * The block containing the SysTick stack must be mapped in the
	 * physical MPU of the root partition.
	 */

	if (!Pip_mapMPU(rootPartDescBlockId, rootSysTickStackBlock.id, 5))
	{
		PANIC("Failed to map rootTimerStackBlock...\n");
	}

	/*
	 * Enable interrupts.
	 */
	if (!Pip_mapMPU(rootid, rootVidtBlock.id, 4))
	{
		PANIC("Failed to map rootVidtBlock...\n");
	}
	Pip_setIntState(ENABLE_INTERRUPTS);

	// empty vs empty pip root = Cost of Pip root partition set up
#endif
#if defined BENCHMARK_PIP_CHILD

	/*
	 * Creation of the three child partitions.
	 */

	/*if (!createChildPartition(&child1PartDescBlock, childPartition,
							  rootPartDescBlockId, rootFlashBlockLocalId, rootRam0BlockLocalId))
	{
		PANIC("Failed to create the child partition 1...\n");
	}

	if (!createChildPartition(&child2PartDescBlock, childPartition,
							  rootPartDescBlockId, rootFlashBlockLocalId, rootRam0BlockLocalId))
	{
		PANIC("Failed to create the child partition 2...\n");
	}

	if (!createChildPartition(&child3PartDescBlock, childPartition,
							  rootPartDescBlockId, rootFlashBlockLocalId, rootRam0BlockLocalId))
	{
		PANIC("Failed to create the child partition 3...\n");
	}*/

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

/*!
 * \brief Main benchmark user program.
 *
 * \param argc Number of blocks given to the root partition.
 *
 * \param argv An array of blocks given to the root partition.
 */
void main_benchmark(int argc, uint32_t **argv)
{
#ifndef BENCHMARK_EMPTY /* Don't launch benchmark with empty flag */
	// Benchmark execution
#if defined BENCHMARK_WITNESS_ONLY
	// Witness
	witness();
	__asm__ __volatile__(
		"push     {pc};"
		:
		:
		: "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11", "r12");
	__asm__ __volatile__(
		"push     {lr, r12, r11, r10,r9,r8,r7,r6,r5,r4,r3,r2,r1,r0};"
		:
		:
		: "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11", "r12");

	__asm__ __volatile__(
		"pop     {r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, lr};"
		:
		:
		: "r0", "r1", "r2", "r3", "r4", "r5", "r6", "r7", "r8", "r9", "r10", "r11", "r12");
	__asm__ __volatile__(
		"pop     {pc};"
		:
		:
		:);
#else
	BENCHMARK_INITIALISE(argc, argv); // do nothing or prepare child
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
