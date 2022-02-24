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
#if !defined BENCHMARK

#include <stdio.h>
#include <stdint.h>

#include "allocator.h"
#include "context.h"
#include "svc.h"

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
#define CHILD_PARTITION_VIDT \
	((user_context_t **) childVidtBlock.address)

/*!
 * \def PANIC
 *
 * \brief Print a message and loop forever.
 */
#define PANIC(...)                   \
	do                           \
	{                            \
		printf(__VA_ARGS__); \
		for (;;);            \
	} while (0)

/*!
 * \brief Enumeration of some VIDT index.
 */
enum vidt_index_e
{
	/*!
	 * \brief The default index of the main context of the
	 *        partition.
	 */
	DEFAULT_INDEX  = 0,

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
extern void* user_alloc_pos;

/*!
 * \brief The block containing the partition descriptor of the child 1.
 */
block_t child1PartDescBlock;

/*!
 * \brief The block containing the partition descriptor of the child 2.
 */
block_t child2PartDescBlock;

/*!
 * \brief The block containing the partition descriptor of the child 3.
 */
block_t child3PartDescBlock;

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
	context->valid    = 0;
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
static int
createChildPartition(
	block_t *childPartDescBlock,
	void *entrypoint,
	void *rootPartDescBlockId,
	void *flashBlockId,
	void *ram0BlockId
) {
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

	if (!allocatorAllocateBlock(&childStackBlock, 1024, 0))
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
	block_t *childArgv = ((block_t *) sp) - childArgc;

	/*
	 * Push arguments onto the stack of the child.
	 */

	childArgv[0].id      = childPartDescBlock->id;
	childArgv[0].address = childPartDescBlock->address;
	childArgv[0].size    = childPartDescBlock->size;

	childArgv[1].id      = childKernStructBlock.id;
	childArgv[1].address = childKernStructBlock.address;
	childArgv[1].size    = childKernStructBlock.size;

	childArgv[2].id      = stackBlockIdInChild;
	childArgv[2].address = childStackBlock.address;
	childArgv[2].size    = childStackBlock.size;

	childArgv[3].id      = vidtBlockIdInChild;
	childArgv[3].address = childVidtBlock.address;
	childArgv[3].size    = childVidtBlock.size;

	childArgv[4].id      = contextBlockIdInChild;
	childArgv[4].address = childContextBlock.address;
	childArgv[4].size    = childContextBlock.size;

	childArgv[5].id      = flashBlockIdInChild;
	childArgv[5].address = 0;
	childArgv[5].size    = 0;

	childArgv[6].id      = ram0BlockIdInChild;
	childArgv[6].address = 0;
	childArgv[6].size    = 0;

	/*
	 * Add the block containing the child's VIDT and the block
	 * containing the child's context into the physical MPU
	 * of the root partition since we need to write in it.
	 */

	if (!Pip_mapMPU(rootPartDescBlockId, childVidtBlock.id, 5))
	{
		return 0;
	}

	if (!Pip_mapMPU(rootPartDescBlockId, childContextBlock.id, 6))
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
			(user_context_t *) childContextBlock.address;

	CHILD_PARTITION_VIDT[CLI_SAVE_INDEX] =
			(user_context_t *) childContextBlock.address;

	CHILD_PARTITION_VIDT[STI_SAVE_INDEX] =
			(user_context_t *) childContextBlock.address;

	/*
	 * Initialize the context with zero.
	 */

	initializeContext(CHILD_PARTITION_VIDT[DEFAULT_INDEX]);

	/*
	 * Fill the context of the child partition.
	 */

	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->registers[R0] = childArgc;
	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->registers[R1] = (uint32_t) childArgv;
	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->registers[PC] = (uint32_t) entrypoint;
	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->registers[SP] = (uint32_t) childArgv;
	CHILD_PARTITION_VIDT[DEFAULT_INDEX]->valid         = CONTEXT_VALID_VALUE;

	/*
	 * Set the VIDT of the child partition.
	 */

	if (!Pip_setVIDT(childPartDescBlock->id, vidtBlockIdInChild))
	{
		return 0;
	}

	return 1;
}

/*!
 * \brief The entry point of the child partitions.
 *
 * \param argc Number of blocks given to the child partition.
 *
 * \param argv An array of blocks given to the child partition.
 */
static void
childPartition(uint32_t argc, block_t *argv)
{
	(void) argc;

	for (;;)
	{
		printf("Hello world from partition %p!\n", (void *) argv[0].id);
	}
}

/*!
 * \brief This handler is a simple round-robin scheduler called at
 *        each SysTick interrupt.
 */
static void
scheduler(void)
{
	for (;;)
	{
		Pip_yield(child1PartDescBlock.id, DEFAULT_INDEX, SYSTICK_INDEX, 0, 0);
		Pip_yield(child2PartDescBlock.id, DEFAULT_INDEX, SYSTICK_INDEX, 0, 0);
		Pip_yield(child3PartDescBlock.id, DEFAULT_INDEX, SYSTICK_INDEX, 0, 0);
	}
}

/*!
 * \brief The entry point of the root partition.
 *
 * \param argc Number of blocks given to the root partition.
 *
 * \param argv An array of blocks given to the root partition.
 */
void main_yield(int argc, uint32_t **argv)
{
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

	puts("Hello world from the root partition!");

	/* Not used. */
	(void) rootPeriphBlockLocalId;
	(void) rootRam2BlockLocalId;
	(void) argc;

	/*
	 * Initialization of the block allocator.
	 */

	allocatorInitialize(rootRam1BlockLocalId, user_alloc_pos);

	/*
	 * Create blocks for the kernel structures of the root
	 * parititon.
	 */

	block_t rootKernStructBlock;

	if (!allocatorAllocateBlock(&rootKernStructBlock, KS_BLOCK_SIZE, 1))
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

	block_t rootVidtBlock;

	if (!allocatorAllocateBlock(&rootVidtBlock, VIDT_BLOCK_SIZE, 1))
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
	 * in the VIDT of he root partition.
	 */

	ROOT_PARTITION_VIDT[SYSTICK_INDEX] =
			(user_context_t *) rootSysTickContextBlock.address;

	/*
	 * Initialize the context with zero.
	 */

	initializeContext(ROOT_PARTITION_VIDT[SYSTICK_INDEX]);

	/*
	 * Initialize the context that will be restore when
	 * a SysTick interrupt will be triggered.
	 */

	ROOT_PARTITION_VIDT[SYSTICK_INDEX]->registers[PC] = (uint32_t) scheduler;
	ROOT_PARTITION_VIDT[SYSTICK_INDEX]->registers[SP] = sp;
	ROOT_PARTITION_VIDT[SYSTICK_INDEX]->valid         = CONTEXT_VALID_VALUE;

	/*
	 * Set the VIDT block of the root partition.
	 */

	if (!Pip_setVIDT(rootPartDescBlockId, rootVidtBlock.id))
	{
		PANIC("Failed to set the VIDT of the root partition...\n");
	}

	/*
	 * Creation of the three child partitions.
	 */

	if (!createChildPartition(&child1PartDescBlock, childPartition,
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

	Pip_setIntState(ENABLE_INTERRUPTS);

	/*
	 * Wait for the SysTick exception to be raised.
	 */

	for (;;);
}

#endif // BENCHMARK
