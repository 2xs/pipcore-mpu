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
#include "scs.h"

cycles_t cycles;
uint32_t main_stack_top;
uint32_t app_stack_top;

void shutoff(){
	__WFE();
}

void BENCHMARK_SINK(){
	//__WFE();
	NRF_POWER->SYSTEMOFF = 1;
	NRF_POWER->TASKS_LOWPWR = 1;
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

#if defined BENCHMARK_PIP

/*!
 * \def PD_BLOCK_SIZE
 *
 * \brief Size of a partition descriptor block.
 */
#define PD_BLOCK_SIZE 128

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
#define CHILD_PARTITION_VIDT \
	((user_context_t **) childVidtBlock.address)

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
typedef enum vidt_index_e
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
	SYSTICK_INDEX = 15,

	/*!
	 * \brief The index containing a NULL pointer to not save
	 *	      the context.
	 */
	NO_SAVE_INDEX = 16
} vidt_index_t;

/*!
 * \brief The start address of the RAM 1 block.
 */
extern void *user_alloc_pos;


block_t rootKernStructBlock;
block_t rootVidtBlock;
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

#if defined BENCHMARK_PIP_CHILD
uint32_t childStackBlockStart;
uint32_t childStackBlockEnd;

/*!
 * \brief The block containing the partition descriptor of the child partition.
 */
block_t child1PartDescBlock;

void child_main(int argc, uint32_t **argv)
{
	run_benchmark();
	// Benchmark ended, go back to root
	Pip_yield(0, DEFAULT_INDEX, DEFAULT_INDEX, 1, 1);
}

	/*!
	 * \brief Create a new child partition
	 *
	 * \param childPartDescBlock A block that will contain the
	 *        partition descriptor of the child partition.
	 *
	 * \param entrypoint An entry point for the child partition.
	 *
	 * \param rootPartDescBlockId A block containing the root
	 *        partition descriptor.
	 *
	 * \param flashBlockId A block containing the flash block.
	 *
	 * \param ram0BlockId A block containing the RAM0 block.
	 *
	 * \return 1 in case of success, 0 otherwise.
	 */
	static int createChildPartition(
		block_t *childPartDescBlock,
		void *entrypoint,
		void *rootPartDescBlockId,
		void *flashBlockId,
		void *ram0BlockId)
{
	/*
	 * Allocation of a block for the creation of the partition
	 * descriptor of the child partition.
	 */

	if (!allocatorAllocateBlock(childPartDescBlock, PD_BLOCK_SIZE, 1))
	{
		return 0;
	}

	if (!Pip_createPartition(childPartDescBlock->id))
	{
		return 0;
	}

	/*
	 * Allocation of a block for the creation of the kernel
	 * structure of the child partition.
	 */

	block_t childKernStructBlock;

	if (!allocatorAllocateBlock(&childKernStructBlock, KS_BLOCK_SIZE, 1))
	{
		return 0;
	}

	if (!Pip_prepare(childPartDescBlock->id, -1, childKernStructBlock.id))
	{
		return 0;
	}

	/*
	 * Allocation of blocks for the stack, the VIDT and the context
	 * of the child partition.
	 */

	block_t childStackBlock;

	if (!allocatorAllocateBlock(&childStackBlock, 4096, 0))
	{
		return 0;
	}

	block_t childVidtBlock;

	if (!allocatorAllocateBlock(&childVidtBlock, VIDT_BLOCK_SIZE, 1))
	{
		return 0;
	}

	block_t childContextBlock;

	if (!allocatorAllocateBlock(&childContextBlock, CONTEXT_BLOCK_SIZE, 0))
	{
		return 0;
	}

	block_t childSTIBlock;

	if (!allocatorAllocateBlock(&childSTIBlock, CONTEXT_BLOCK_SIZE, 0))
	{
		return 0;
	}

	/*
	 * Add the blocks in the child partition descriptor.
	 */

	uint32_t *stackBlockIdInChild;

	if ((stackBlockIdInChild = Pip_addMemoryBlock(
			 childPartDescBlock->id, childStackBlock.id, 1, 1, 0)) == NULL)
	{
		return 0;
	}

	uint32_t *vidtBlockIdInChild;

	if ((vidtBlockIdInChild = Pip_addMemoryBlock(
			 childPartDescBlock->id, childVidtBlock.id, 1, 1, 0)) == NULL)
	{
		return 0;
	}

	uint32_t *contextBlockIdInChild;

	if ((contextBlockIdInChild = Pip_addMemoryBlock(
			 childPartDescBlock->id, childContextBlock.id, 1, 1, 0)) == NULL)
	{
		return 0;
	}

	uint32_t *flashBlockIdInChild;

	if ((flashBlockIdInChild = Pip_addMemoryBlock(
			 childPartDescBlock->id, flashBlockId, 1, 0, 1)) == NULL)
	{
		return 0;
	}

	uint32_t *ram0BlockIdInChild;

	if ((ram0BlockIdInChild = Pip_addMemoryBlock(
			 childPartDescBlock->id, ram0BlockId, 1, 1, 0)) == NULL)
	{
		return 0;
	}

	/*
	 * Add the blocks in the physical MPU structure of the
	 * child partition.
	 */

	if (!Pip_mapMPU(childPartDescBlock->id, stackBlockIdInChild, 0))
	{
		return 0;
	}

	if (!Pip_mapMPU(childPartDescBlock->id, vidtBlockIdInChild, 1))
	{
		return 0;
	}

	if (!Pip_mapMPU(childPartDescBlock->id, contextBlockIdInChild, 2))
	{
		return 0;
	}

	if (!Pip_mapMPU(childPartDescBlock->id, flashBlockIdInChild, 3))
	{
		return 0;
	}

	if (!Pip_mapMPU(childPartDescBlock->id, ram0BlockIdInChild, 4))
	{
		return 0;
	}

	/*
	 * Add the block containing the child's stack into the physical
	 * MPU of the root partition since we need to write in it.
	 */

	if (!Pip_mapMPU(rootPartDescBlockId, childStackBlock.id, 5))
	{
		return 0;
	}

	/*
	 * Calculate the stack address from the stack block.
	 */

	uint32_t childArgc = 7;
	uint32_t sp = childStackBlock.address + childStackBlock.size - 8;
	block_t *childArgv = ((block_t *)sp) - childArgc;

	/*
	 * Push arguments onto the stack of the child.
	 */

	childArgv[0].id = childPartDescBlock->id;
	childArgv[0].address = childPartDescBlock->address;
	childArgv[0].size = childPartDescBlock->size;

	childArgv[1].id = childKernStructBlock.id;
	childArgv[1].address = childKernStructBlock.address;
	childArgv[1].size = childKernStructBlock.size;

	childArgv[2].id = stackBlockIdInChild;
	childArgv[2].address = childStackBlock.address;
	childArgv[2].size = childStackBlock.size;

	childArgv[3].id = vidtBlockIdInChild;
	childArgv[3].address = childVidtBlock.address;
	childArgv[3].size = childVidtBlock.size;

	childArgv[4].id = contextBlockIdInChild;
	childArgv[4].address = childContextBlock.address;
	childArgv[4].size = childContextBlock.size;

	childArgv[5].id = flashBlockIdInChild;
	childArgv[5].address = 0;
	childArgv[5].size = 0;

	childArgv[6].id = ram0BlockIdInChild;
	childArgv[6].address = 0;
	childArgv[6].size = 0;

	childStackBlockStart = childStackBlock.address;
	childStackBlockEnd = (uint32_t*) childArgv - 16; /* the arguments pushed by loadContext*/

	/*
	 * Add the block containing the child's VIDT and the block
	 * containing the child's context into the physical MPU
	 * of the root partition since we need to write in it.
	 */

	if (!Pip_mapMPU(rootPartDescBlockId, childVidtBlock.id, 5))
	{
		return 0;
	}

	/*
	 * Initialize the VIDT of the child with NULL pointer.
	 */

	initializeVidt(CHILD_PARTITION_VIDT, childVidtBlock.size);


	/*
	 * Set the context address at indexes DEFAULT_INDEX,
	 * CLI_SAVE_INDEX and STI_SAVE_INDEX in the VIDT of
	 * the child partition.
	 */

	CHILD_PARTITION_VIDT[DEFAULT_INDEX] =
		(user_context_t *)childContextBlock.address;

	CHILD_PARTITION_VIDT[CLI_SAVE_INDEX] =
		(user_context_t *)childContextBlock.address;

	CHILD_PARTITION_VIDT[STI_SAVE_INDEX] =
		(user_context_t *)childContextBlock.address;

	/*
	 * Initialize the context with zero.
	 */

	if (!Pip_mapMPU(rootPartDescBlockId, childContextBlock.id, 6))
	{
		return 0;
	}

	/*if (!Pip_mapMPU(rootPartDescBlockId, childSTIBlock.id, 7))
	{
		return 0;
	}*/

	initializeContext(CHILD_PARTITION_VIDT[DEFAULT_INDEX]);
	//initializeContext(CHILD_PARTITION_VIDT[STI_SAVE_INDEX]);

	// remove STI from MPU
	/*if (!Pip_mapMPU(rootPartDescBlockId, 0, 7))
	{
		return 0;
	}*/

	/*
	 * Fill the context of the child partition.
	 */

	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->registers[R0] = childArgc;
	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->registers[R1] = (uint32_t)childArgv;
	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->registers[PC] = (uint32_t)entrypoint;
	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->registers[SP] = (uint32_t)childArgv;
	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->valid = CONTEXT_VALID_VALUE;

	/*
	 * Set the VIDT of the child partition.
	 */

	if (!Pip_setVIDT(childPartDescBlock->id, vidtBlockIdInChild))
	{
		return 0;
	}

	return 1;
}

#endif // BENCHMARK_PIP_CHILD

/*!
 * \brief This handler is a simple round-robin scheduler called at
 *        each SysTick interrupt.
 */
static void
systick_handler(void)
{
#if defined BENCHMARK_PIP_ROOT
	// Restore interrupted context
	Pip_yield(rootid, STI_SAVE_INDEX, NO_SAVE_INDEX, 1, 1);
#elif defined BENCHMARK_PIP_CHILD
	// Restore the child's interrupted context
	Pip_yield(child1PartDescBlock.id, CLI_SAVE_INDEX, NO_SAVE_INDEX, 0, 0);

#endif
	printf("Should never be reached\n");
}

#endif // BENCHMARK_PIP

/*!
 * \brief This handler is a simple round-robin scheduler called at
 *        each SysTick interrupt.
 */
/*static void
systick_handler_child(void)
{
	// Restore interrupted context
	Pip_yield(child1PartDescBlock.id, STI_SAVE_INDEX, NO_SAVE_INDEX, 1, 1);
	printf("Should never be reached\n");
}*/

void BENCHMARK_INITIALISE(int argc, uint32_t **argv)
{
#if defined BENCHMARK_PIP
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
	rootid = rootPartDescBlockId;

	/*
	* Initialization of the block allocator.
	*/
	/*blockOrError bt;
	if (!Pip_findBlock(rootPartDescBlockId, 0x20007FF0, &bt))
	{
		printf("Block not found\n");
	}
	else
		printf("Available RAM: %x - %x\n", bt.blockAttr.blockstartaddr, bt.blockAttr.blockendaddr);
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





	// empty vs empty pip root = Cost of Pip root partition set up



#if defined BENCHMARK_PIP_CHILD

	// Init context for DEFAULT_BLOCK -> holds the root partition context when yielding
	block_t defaultBlock;

	if (!allocatorAllocateBlock(&defaultBlock, CONTEXT_BLOCK_SIZE, 0))
	{
		PANIC("Failed to allocate rootKernStructBlock...\n");
	}

	// Set the context address at index DEFAULT_INDEX
	// in the VIDT of the root partition.
	//

		ROOT_PARTITION_VIDT[DEFAULT_INDEX] =
			(user_context_t *)defaultBlock.address;

	if (!Pip_readMPU(rootPartDescBlockId, 4) == 0)
	{
		PANIC("No space left in MPU region 4...\n");
	}

	if (!Pip_mapMPU(rootPartDescBlockId, defaultBlock.id, 4))
	{
		PANIC("Failed to map defaultBlock...\n");
	}

	initializeContext(ROOT_PARTITION_VIDT[DEFAULT_INDEX]);

	if (!Pip_mapMPU(rootPartDescBlockId, 0, 4))
	{
		PANIC("Failed to UNmap defaultBlock of region 4...\n");
	}

	/*
	 * Creation of the child partition and launch the benchmark.
	 */

	if (!createChildPartition(&child1PartDescBlock, child_main,
							  rootPartDescBlockId, rootFlashBlockLocalId, rootRam0BlockLocalId))
	{
		PANIC("Failed to create the child partition 1...\n");
	}
#endif /* BENCHMARK_PIP_CHILD */

	/*
	 * The block containing the SysTick stack must be mapped in the
	 * physical MPU of the root partition.
	 */

	if (!Pip_mapMPU(rootPartDescBlockId, rootSysTickStackBlock.id, 5))
	{
		PANIC("Failed to map rootTimerStackBlock...\n");
	}

	/*
	 * Set the VIDT block of the root partition.
	 */

	if (!Pip_setVIDT(rootPartDescBlockId, rootVidtBlock.id))
	{
		PANIC("Failed to set the VIDT of the root partition...\n");
	}
#endif
	initialise_benchmark(); // embench init
	// warm_caches(WARMUP_HEAT);
}

void BENCHMARK_FINALISE()
{
#if defined BENCHMARK_PIP
	/*
	 * Disable interrupts.
	 */
	Pip_setIntState(DISABLE_INTERRUPTS);
#endif /* BENCHMARK_PIP */

#if defined BENCHMARK_PIP_CHILD
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
void run_benchmark()
{
	register int RSP __asm("sp");
	app_stack_top = RSP; // Could be main for privileged app
	volatile int result = 0;
	int correct;
	for (int i= 0 ; i<RUNS ; i++){
		result = result | benchmark();
	}

	correct = verify_benchmark(result);
	if (!correct)
	{
		printf("***ERROR***\nBad result\n");
	}
}

void BENCHMARK_RUN()
{
	END_INITIALISATION();
#if defined BENCHMARK_PIP_ROOT
	/*
	 * Enable interrupts.
	 */
	Pip_setIntState(ENABLE_INTERRUPTS);
	run_benchmark();
	//Pip_yield(rootid, DEFAULT_INDEX, DEFAULT_INDEX, 1, 1); // run_benchmark is not prepared here

#elif defined BENCHMARK_PIP_CHILD
	/*
	 * Enable interrupts.
	 */
	// Pip_setIntState(ENABLE_INTERRUPTS);
	Pip_yield(child1PartDescBlock.id, DEFAULT_INDEX, DEFAULT_INDEX, 1, 1);
#else
	run_benchmark();
#endif /* BENCHMARK_PIP_ROOT  BENCHMARK_PIP_CHILD */
}

void benchmark_results()
{
	cycles.global_counter = GetCycleCounter(); // get cycle counter
	DisableCycleCounter();	// disable counting if not used
	uint32_t priv_counter = cycles.global_privileged_counter;
	uint32_t priv_counter_after_init = cycles.init_end_privileged_counter;
	// Stack usage measurements
	uint32_t main_stack_usage = finish_stack_usage_measurement(&__StackLimit, main_stack_top); /* main (Pip) stack */
#if defined BENCHMARK_BASELINE_UNPRIV
	uint32_t app_stack_usage = finish_stack_usage_measurement(&user_stack_limit, app_stack_top); /* app stack */
#elif defined BENCHMARK_PIP_ROOT
	uint32_t app_stack_usage = finish_stack_usage_measurement(0x20008000, app_stack_top); /* app stack */
#elif defined BENCHMARK_PIP_CHILD
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
	dump_partition(rootid);
	dump_partition(child1PartDescBlock.address);
	BENCHMARK_SINK();
}

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
#else
	BENCHMARK_INITIALISE(argc, argv); // do nothing or prepare child
	BENCHMARK_RUN();
	BENCHMARK_FINALISE(); // do nothing or destruct child
#endif // BENCHMARK_WITNESS_ONLY
#endif // BENCHMARK_EMPTY
	END_BENCHMARK();
	printf("***ERROR***\nShould never be reached\n");
	while (1);
}
#endif /* BENCHMARK */
