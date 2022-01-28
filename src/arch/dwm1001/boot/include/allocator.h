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

#ifndef __ALLOCATOR_H__
#define __ALLOCATOR_H__

#include <stdint.h>

/*!
 * \brief Structure representing an MPU block.
 */
typedef struct block_s
{
	/*!
	 * \brief The ID of the block.
	 */
        uint32_t *id;

	/*!
	 * \brief The start address of the block.
	 */
        uint32_t address;

	/*!
	 * \brief The size of the block.
	 */
        uint32_t size;
} block_t;

/*!
 * \brief Initialize the block allocator.
 *
 * \param blockId The id of the block from which to cut new sub blocks.
 *
 * \param blockAddress The start address of the block to cut.
 */
void allocatorInitialize(
	uint32_t *blockId,
	void     *blockAddress
);

/*!
 * \brief Allocates a new memory block whose size is greater than or
 *        equal to the requested one, taking into account the MPU
 *        constraints.
 *
 * \param block A pointer to a structure that will contain informations
 *        about the allocated block.
 *
 * \param blockSize The requested size of the block to be allocated.
 *
 * \param usePartialConfiguration This parameter tells the block
 *        allocator whether or not to use the partial block
 *        configuration. A value of 0 disables the use of the partial
 *        block configuration, while a value other than 0 enables it.
 *
 *        Partial block configuration saves memory at the cost of
 *        performance. This is because accessing the address of a
 *        partially configured block in the MPU can raise a MemManage
 *        fault that requires the MPU regions to be reconfigured.
 *
 *        Not using the partial block configuration increases
 *        performance at the cost of memory. This is because if the
 *        address of the block to be cut is not aligned with the size
 *        of the block, additional cutting is required.
 *
 * \warning The block containing the stack of a partition must be
 *          allocated without partial configuration.
 *
 * \return 1 if the allocator has successfully allocate the requested
 *         block, 0 otherwise.
 */
int allocatorAllocateBlock(
	block_t  *block,
	uint32_t blockSize,
	uint32_t usePartialConfiguration
);

#endif /* __ALLOCATOR_H__ */
