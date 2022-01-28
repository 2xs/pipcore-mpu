#include <stdint.h>
#include <stddef.h>

#include "allocator.h"
#include "svc.h"

/*!
 * \brief The current first free block of the allocator.
 */
static block_t firstFreeBlock;

/*!
 * \brief Returns the next power of two of the value.
 *
 * \param value The value to from which to get the next power of two.
 *
 * \return The next power of two of the value.
 */
static uint32_t
getNextPowerOfTwo(
	uint32_t value
) {
	value--;
	value |= value >>  1;
	value |= value >>  2;
	value |= value >>  4;
	value |= value >>  8;
	value |= value >> 16;
	return value + 1;
}

void allocatorInitialize(
	uint32_t *blockId,
	void     *blockAddress
) {
	firstFreeBlock.address = (uint32_t) blockAddress;
	firstFreeBlock.id = blockId;
	firstFreeBlock.size = 0;
}

int allocatorAllocateBlock(
	block_t  *block,
	uint32_t blockSize,
	uint32_t usePartialConfiguration
) {
	uint32_t modulus, addressToCut, *cuttedBlockId;

	if (!usePartialConfiguration)
	{
		/* The user does not want to use the partial block
		 * configuration for performance reasons. In this case,
		 * the MPU constraints for ARMv7-M must be met, namely
		 * that the size of a MPU region must be a power of 2
		 * greater than or equal to 32 bytes, and that it must
		 * start at an address that is a multiple of its size. */

		/* We start by making sure that the size of the block to
		 * be cut is a power of 2 by calculating the next power
		 * of 2. */
		blockSize = getNextPowerOfTwo(blockSize);

		/* We check that the start address of the first free
		 * block of the allocator is aligned with the size of
		 * the block to be cut. */
		modulus = firstFreeBlock.address & (blockSize - 1);

		if (modulus != 0)
		{
			/* We calculate the next address aligned with
			 * the size of the block to cut. */
			addressToCut = firstFreeBlock.address + blockSize - modulus;

			/* We align the address with the size of the
			 * block to be cut by cutting a dummy block.
			 * This operation is memory consuming. */
			if ((cuttedBlockId = Pip_cutMemoryBlock(firstFreeBlock.id,
				(uint32_t *) addressToCut, -1)) == NULL)
			{
				return 0;
			}

			/* The first free block of the allocator is now
			 * the correctly aligned dummy block that was
			 * just cut out. */
			firstFreeBlock.id      = cuttedBlockId;
			firstFreeBlock.address = addressToCut;
		}
	}
	else
	{
		/* The user wants to use a partial block configuration
		 * to save memory. In this case, we just need to make
		 * sure that the block size is a multiple of 32, the
		 * smallest valid MPU region for ARMv7-M. */

		/* We make sure that the size of the block to be cut is
		 * a multiple of 32. */
		modulus = blockSize & 31;

		if (modulus != 0)
		{
			/* We align the block size to the next multiple
			 * of 32. */
			blockSize = blockSize + 32 - modulus;
		}
	}

	/* The address where to cut the block to allocate is calculated
	 * from its size and the address of the first free block of the
	 * allocator. */
	addressToCut = firstFreeBlock.address + blockSize;

	/* The first free block of the allocator is cut out at the
	 * previously calculated address. */
	if ((cuttedBlockId = Pip_cutMemoryBlock(firstFreeBlock.id,
			(uint32_t *) addressToCut, -1)) == NULL)
	{
		return 0;
	}

	/* The allocated block corresponds to the first free block of
	 * the allocator. */
	block->id      = firstFreeBlock.id;
	block->address = firstFreeBlock.address;
	block->size    = blockSize;

	/* Now, the new cut block is the first free block of the
	 * allocator. */
	firstFreeBlock.id      = cuttedBlockId;
	firstFreeBlock.address = addressToCut;
	firstFreeBlock.size    = 0;

	return 1;
}
