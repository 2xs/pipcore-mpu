/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2021)                */
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
#include "context.h"
#include "svc.h"
#include "user_ADT.h"

/* The address of the VIDT of the root partition. */
#define ROOT_PARTITION_VIDT  ((user_context_t **) 0x20003000)
/* The address of the VIDT of the child partition. */
#define CHILD_PARTITION_VIDT ((user_context_t **) 0x20006000)

void child_partition(int argc, uint32_t **argv)
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

void main_yield(int argc, uint32_t **argv)
{
	/* Global ID of the block containing the partition descriptor
	 * of the root partition. */
	uint32_t *rootPartDescBlockGlobalId = argv[0];

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

	/* Not used. */
	(void) rootRam2BlockLocalId;
	(void) argc;

	/* Cut a block that will contain an additional kernel structure so
	 * that the root partition can have more than 8 blocks. */
	uint32_t *rootKernStructBlockLocalId =
		Pip_cutMemoryBlock(rootRam1BlockLocalId, (uint32_t *) 0x20002000, -1);

	if (rootKernStructBlockLocalId == NULL)
	{
		printf("Failed to cut block for rootKernStructBlockLocalId...\n");
		for (;;);
	}

	/* Cut a block that will contain the VIDT of the root partition and
	 * add it to its physical MPU at index 5. */
	uint32_t *rootVidtBlockLocalId =
		Pip_cutMemoryBlock(rootKernStructBlockLocalId, (uint32_t *) 0x20003000, 5);

	if (rootVidtBlockLocalId == NULL)
	{
		printf("Failed to cut block for rootVidtBlockLocalId...\n");
		for (;;);
	}

	/* Prepare the kernel structure with the kernel structure block of
	 * the the root partition. The -1 as an argument indicates that we
	 * want to force the addition of the kernel structure even if there
	 * are still free slots. */
	if (!Pip_prepare(rootPartDescBlockGlobalId, -1, rootKernStructBlockLocalId))
	{
		printf("Failed to prepare rootKernStructBlockLocalId...\n");
		for (;;);
	}

	/* Set the previously cut block as the VIDT of the root partition. */
	if (!Pip_setVIDT(rootPartDescBlockGlobalId, rootVidtBlockLocalId))
	{
		printf("Failed to set VIDT rootVidtBlockLocalId...\n");
		for (;;);
	}

	/* Cut a block that will contain the context of the root partition
	 * saved by the yield system call . */
	uint32_t *rootCtxSavedBlockLocalId =
		Pip_cutMemoryBlock(rootVidtBlockLocalId, (uint32_t *) 0x20003080, -1);

	if (rootCtxSavedBlockLocalId == NULL)
	{
		printf("Failed to cut block for rootCtxSavedBlockLocalId...\n");
		for (;;);
	}

	/* Specifies in the root partition VIDT that the context is to be
	 * stored at the address at index 0. */
	ROOT_PARTITION_VIDT[0] = (user_context_t *) 0x20003080;

	/* Cut a block that will contain the partition descriptor of the
	 * child partition. */
	uint32_t *childPartDescBlockLocalId =
		Pip_cutMemoryBlock(rootCtxSavedBlockLocalId, (uint32_t *) 0x20003100, -1);

	if (childPartDescBlockLocalId == NULL)
	{
		printf("Failed to cut block for childPartDescBlockLocalId...\n");
		for (;;);
	}

	/* Cut a block that will contain the kernel structure of the child
	 * partition. */
	uint32_t *childKernStructBlockLocalId =
		Pip_cutMemoryBlock(childPartDescBlockLocalId, (uint32_t *) 0x20004000, -1);

	if (childKernStructBlockLocalId == NULL)
	{
		printf("Failed to cut block for childKernStructBlockLocalId...\n");
		for (;;);
	}

	/* Cut a block that will contain the remaining free RAM of the
	 * child partition and add it to the physical MPU of the root
	 * partition at index 5. */
	uint32_t *childFreeRamBlockLocalId =
		Pip_cutMemoryBlock(childKernStructBlockLocalId, (uint32_t *) 0x20005000, 5);

	if (childFreeRamBlockLocalId == NULL)
	{
		printf("Failed to cut block for childFreeRamBlockLocalId...\n");
		for (;;);
	}

	/* Cut a block that will contain the VIDT of the child partition
	 * and add it to the physical MPU of the root partition at index
	 * 6. */
	uint32_t *childVidtBlockLocalId =
		Pip_cutMemoryBlock(childFreeRamBlockLocalId, (uint32_t *) 0x20006000, 6);

	if (childVidtBlockLocalId == NULL)
	{
		printf("Failed to cut block for childVidtBlockLocalId...\n");
		for (;;);
	}

	/* The stack block is the only block that must comply with MPU
	 * constraints. Here we want to provide the child partition with
	 * 1024 bytes of stack. The block containing this stack must
	 * therefore start at an address aligned to 1024 bytes. For this
	 * reason, it is necessary to cut two dummy blocks in addition to
	 * the stack block. The first dummy cut leaves 128 bytes for the
	 * VIDT.*/
	uint32_t *dummy1 =
		Pip_cutMemoryBlock(childVidtBlockLocalId, (uint32_t *) 0x20006080, -1);

	if (dummy1 == NULL)
	{
		printf("Failed to cut block for dummy1...\n");
		for (;;);
	}

	/* Cut the stack of the child partition at an address aligned to
	 * 1024 bytes and add it to the physical MPU of the root partition
	 * at index 7. */
	uint32_t *childStackBlockLocalId =
		Pip_cutMemoryBlock(dummy1, (uint32_t *) 0x20006400, 7);

	if (childStackBlockLocalId == NULL)
	{
		printf("Failed to cut block for childStackBlockLocalId...\n");
		for (;;);
	}

	/* The second dummy cut makes the stack block equal to 1024
	 * bytes. */
	uint32_t *dummy2 =
		Pip_cutMemoryBlock(childStackBlockLocalId, (uint32_t *) 0x20006800, -1);

	if (dummy2 == NULL)
	{
		printf("Failed to cut block for dummy2...\n");
		for (;;);
	}

	/* Create a new partition with the child partition descriptor
	 * block. */
	if (!Pip_createPartition(childPartDescBlockLocalId))
	{
		printf("Failed to create childPartDescBlockLocalId...\n");
		for (;;);
	}

	/* Prepare the kernel structure with the kernel structure block of
	 * the child. The -1 as an argument indicates that we want to force
	 * the addition of the kernel structure even if there are still
	 * free slots.*/
	if (!Pip_prepare(childPartDescBlockLocalId, 1, childKernStructBlockLocalId))
	{
		printf("Failed to prepare childKernStructBlockLocalId...\n");
		for (;;);
	}

	/* Add the block that will contain the VIDT of the child to the
	 * child partition. */
	uint32_t *childVidtBlockGlobalId =
		Pip_addMemoryBlock(childPartDescBlockLocalId, childVidtBlockLocalId, 1, 1, 0);

	if (childVidtBlockGlobalId == NULL)
	{
		printf("Failed to add block for childVidtBlockLocalId...\n");
		for (;;);
	}

	/* Add the block that will contain the stack of the child to the
	 * child partition. */
	uint32_t *childStackBlockGlobalId =
		Pip_addMemoryBlock(childPartDescBlockLocalId, childStackBlockLocalId, 1, 1, 0);

	if (childStackBlockGlobalId == NULL)
	{
		printf("Failed to add block for childStackBlockLocalId...\n");
		for (;;);
	}

	/* Add the block that will contain the free RAM of the child to the
	 * child partition. */
	uint32_t *childFreeRamBlockGlobalId =
		Pip_addMemoryBlock(childPartDescBlockLocalId, childFreeRamBlockLocalId, 1, 1, 0);

	if (childFreeRamBlockGlobalId == NULL)
	{
		printf("Failed to add block for childFreeRamBlockLocalId...\n");
		for (;;);
	}

	/* Add the block containing the FLASH to the child partition. */
	uint32_t *rootFlashBlockGlobalId =
		Pip_addMemoryBlock(childPartDescBlockLocalId, rootFlashBlockLocalId, 1, 0, 1);

	if (rootFlashBlockGlobalId == NULL)
	{
		printf("Failed to add block for rootFlashBlockLocalId...\n");
		for (;;);
	}

	/* Add the block containing the peripheral to the child partition. */
	uint32_t *rootPeriphBlockGlobalId =
		Pip_addMemoryBlock(childPartDescBlockLocalId, rootPeriphBlockLocalId, 1, 1, 0);

	if (rootPeriphBlockGlobalId == NULL)
	{
		printf("Failed to add block for rootPeriphBlockLocalId...\n");
		for (;;);
	}

	/* Add the block containing the first block of RAM to the child
	 * partition. This is necessary because the heap used by printf
	 * is in this block. */
	uint32_t *rootRam0BlockGlobalId =
		Pip_addMemoryBlock(childPartDescBlockLocalId, rootRam0BlockLocalId, 1, 1, 0);

	if (rootRam0BlockGlobalId == NULL)
	{
		printf("Failed to add block for rootRam0BlockLocalId...\n");
		for (;;);
	}

	/* Set the previously cut block as the VIDT of the child
	 * partition. */
	if (!Pip_setVIDT(childPartDescBlockLocalId, childVidtBlockGlobalId))
	{
		printf("Failed to set VIDT childVidtBlockGlobalId...\n");
		for (;;);
	}

	/* Map the child's stack block to its physical MPU list at
	 * index 0. */
	if (!Pip_mapMPU(childPartDescBlockLocalId, childStackBlockGlobalId, 0))
	{
		printf("Failed to map childStackBlockGlobalId...\n");
		for (;;);
	}

	/* Map the child's free RAM block to its physical MPU list at
	 * index 1. */
	if (!Pip_mapMPU(childPartDescBlockLocalId, childFreeRamBlockGlobalId, 1))
	{
		printf("Failed to map childFreeRamBlockGlobalId...\n");
		for (;;);
	}

	/* Map the FLASH block to the child's physical MPU list at
	 * index 2. */
	if (!Pip_mapMPU(childPartDescBlockLocalId, rootFlashBlockGlobalId, 2))
	{
		printf("Failed to map rootFlashBlockGlobalId...\n");
		for (;;);
	}

	/* Map the peripheral block to the child's physical MPU list at
	 * index 3. */
	if (!Pip_mapMPU(childPartDescBlockLocalId, rootPeriphBlockGlobalId, 3))
	{
		printf("Failed to map rootPeriphBlockGlobalId...\n");
		for (;;);
	}

	/* Map the first RAM block to the child's physical MPU list at
	 * index 4. */
	if (!Pip_mapMPU(childPartDescBlockLocalId, rootRam0BlockGlobalId, 4))
	{
		printf("Failed to map rootRam0BlockGlobalId...\n");
		for (;;);
	}

	/* Create the child's context at the start address of the child's
	 * context block. This address is accessible from the root
	 * partition because it is mapped in its MPU.
	 */
	user_context_t *childContext = (user_context_t *) 0x20005000;

	/* Zeroing the context. */
	for (size_t i = 0; i < CONTEXT_REGISTER_NUMBER; i++)
	{
		childContext->registers[i] = 0;
	}

	childContext->valid    = 0;
	childContext->pipflags = 0;

	/* Create the child's stack at the end address, aligned with an
	 * 8-byte boundary, of the child's stack block. This address is
	 * accessible from the root partition because it is mapped in its
	 * MPU.
	 */
	uint32_t *sp = (uint32_t*) 0x200067f8;
	uint32_t childArgc = 5;
	uint32_t *childArgv = sp - childArgc;

	/* Stacking arguments onto the stack of the child. */
	childArgv[0] = (uint32_t) childStackBlockGlobalId;
	childArgv[1] = (uint32_t) childFreeRamBlockGlobalId;
	childArgv[2] = (uint32_t) rootFlashBlockGlobalId;
	childArgv[3] = (uint32_t) rootPeriphBlockGlobalId;
	childArgv[4] = (uint32_t) rootRam0BlockGlobalId;

	/* Initialize the contexte of the child. */
	childContext->valid           = 0;
	childContext->registers[R0]   = childArgc;
	childContext->registers[R1]   = (uint32_t) childArgv;
	childContext->registers[PC]   = (uint32_t) child_partition;
	childContext->registers[SP]   = (uint32_t) childArgv;
	childContext->valid           = 1;

	/* Specifies in the child partition VIDT that the context is to be
	 * restored at the address contained in index 1. */
	CHILD_PARTITION_VIDT[1] = (user_context_t *) childContext;

	for (;;)
	{
		puts("Hello world from the root partition!\n");

		/* Yield to the child partition by saving the current context
		 * at the address at index 0 of the root partition's VIDT and
		 * restoring the context of the child at the address at index 1
		 * of the child partition's VIDT. The flagOnYield and
		 * flagOnWake are left at zero. */
		Pip_yield(childPartDescBlockLocalId, 1, 0, 0, 0);
	}
}
