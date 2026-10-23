/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2024)                */
/*  Copyright (C) 2020-2024 Orange                                             */
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

/*!
 * \file malinit.c
 *
 * \brief RP2350 memory abstraction layer initializer.
 *
 * Ports from the ARM target's malinit.c. The structural difference is the
 * number of static root blocks: ARM tiles 60 KiB of RAM into four descending
 * powers of two plus one ROM region, because 60 KiB was all it had and no
 * single power-of-two region fits it. This target has 512 KiB, so link.ld
 * carves exactly two regions that are already powers of two and naturally
 * aligned -- 256 KiB of RAM and 64 KiB of flash at __root -- which spends two
 * of the five partition-visible PMP entries instead of five of six, and
 * leaves the rest for blocks the root partition cuts at runtime.
 *
 * Both regions being exact also means neither needs the fault-driven refill
 * of section 6: largest_covering_MPU_region() maps each of them in one NAPOT
 * entry with nothing left over. That is why rungs 5 and 6 can be reached
 * before the refill handler exists.
 */

#include <stdint.h>

#include "Internal.h"
#include "mal.h"
#include "memlayout.h"
#include "stdio.h"

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
 * \brief Initialize the root partition descriptor structure.
 *
 * \param rootPartDesc The root partition structure to initialize.
 */
static inline void
initializeRootPartitionDescriptor(paddr rootPartDesc)
{
	paddr rootPartDescEndAddr = ((PDTable_t *) rootPartDesc) + 1;

	if (!eraseBlock(rootPartDesc, rootPartDescEndAddr))
	{
		PANIC("PIP: Failed to erase the root partition "
			"descriptor structure...\n");
	}

	initPDTable(rootPartDesc);
}

/*!
 * \brief Initialize the root kernel structure.
 *
 * \param rootKernStruct The root kernel structure to initialize.
 */
static inline void
initializeRootKernelStructure(paddr rootKernStruct)
{
	paddr rootKernStructEndAddr = ((KStructure_t *) rootKernStruct) + 1;

	if (!initStructure(rootKernStruct, rootKernStructEndAddr))
	{
		PANIC("PIP: Failed to initialize the root partition "
			"kernel structure...\n");
	}
}

/*!
 * \brief Prepare the root partition with a kernel structure.
 *
 * \param rootPartDesc The root partition to prepare.
 *
 * \param rootKernStruct The root kernel structure.
 */
static inline void
prepareRootPartition(paddr rootPartDesc, paddr rootKernStruct)
{
	writePDStructurePointer(rootPartDesc, rootKernStruct);
	writePDFirstFreeSlotPointer(rootPartDesc, rootKernStruct);
	writePDNbFreeSlots(rootPartDesc, KERNELSTRUCTUREENTRIESNB);
	writePDNbPrepare(rootPartDesc, 1);
}

/*!
 * \brief Create a new partition and register it as the root partition.
 */
static inline void
createAndRegisterRootPartition(void)
{
	/* Allocate space in the .data section for the root
	 * partition descriptor structure. */
	static PDTable_t rootPartDesc;

	/* Allocate space in the .data section for the root
	 * kernel structure. */
	static KStructure_t rootKernStruct;

	paddr mpuRegion0Id;
	paddr mpuRegion1Id;

	/* Initialize the root partition structures. */
	initializeRootPartitionDescriptor(&rootPartDesc);
	initializeRootKernelStructure(&rootKernStruct);
	prepareRootPartition(&rootPartDesc, &rootKernStruct);

	/*
	 * The end addresses passed below are the linker's, which are
	 * exclusive -- __mpuRegion0End is __mpuRegion0Start + the size. That
	 * is what the ARM target passes too, and it is kept deliberately
	 * rather than corrected here, because the convention is inconsistent
	 * upstream and this is not the place to change it:
	 *
	 *   - src/model/ADT.v's block record documents [startAddr ; endAddr],
	 *     "the MPU region end address IS included in the region";
	 *   - largest_covering_MPU_region() agrees, taking endAddr + 1 as the
	 *     exclusive top;
	 *   - but sizeOfBlock() is endAddr - startAddr, in the model as well
	 *     as in C, which is the *exclusive* reading.
	 *
	 * Feeding it the exclusive end is what makes sizeOfBlock() return the
	 * true size, and it is the only combination the existing port has ever
	 * been exercised with. Passing an inclusive end would make every
	 * service see these blocks one byte short instead. The ARM malinit.c
	 * still carries a never-called addressMinusOne() helper, which is
	 * someone having noticed and stopped. Reported separately; see
	 * KNOWLEDGE.md section 8.
	 */

	mpuRegion0Id = insertNewEntry(
		(paddr) &rootPartDesc,
		(paddr) &__mpuRegion0Start,
		(paddr) &__mpuRegion0End,
		(paddr) &__mpuRegion0Start,
		(bool) true,
		(bool) true,
		(bool) false,
		readPDNbFreeSlots(&rootPartDesc)
	);

	/*
	 * The root partition's code: readable and executable, and
	 * deliberately NOT writable.
	 *
	 * This is the one place the permissions diverge from the ARM target,
	 * whose equivalent ROM region is RWX. Nothing can write to the XIP
	 * flash window anyway, so the W there granted nothing, and an
	 * isolation kernel should not hand out a permission that has no use:
	 * PMP has independent R, W and X, so there is no reason to round up
	 * the way ARM's two-valued AP sometimes forced.
	 *
	 * Nothing needs it. The root partition's crt0 reads this region and
	 * writes only RAM -- .data is copied out of flash into region 0, and
	 * any GOT relocation lands there too. A child can still be given a
	 * read-or-execute sub-block of it; only a writable one is refused,
	 * which is the correct answer for flash.
	 */
	mpuRegion1Id = insertNewEntry(
		(paddr) &rootPartDesc,
		(paddr) &__mpuRegion1Start,
		(paddr) &__mpuRegion1End,
		(paddr) &__mpuRegion1Start,
		(bool) true,
		(bool) false,
		(bool) true,
		readPDNbFreeSlots(&rootPartDesc)
	);

	/* Map both blocks previously inserted into the kernel structure to
	 * the physical PMP. Slots 0 and 1 of the five partition-visible
	 * entries; 5 and 6 are the refill slots and 7 is the deny-all
	 * background, none of which a partition may touch. */
	enableBlockInMPU(&rootPartDesc, mpuRegion0Id, 0);
	enableBlockInMPU(&rootPartDesc, mpuRegion1Id, 1);

	/* Set the root partition's VIDT region in the partition descriptor
	 * structure. */
	rootPartDesc.vidtAddr = (void *) &__rootVidtStart;

	/* Register the root partition to PIP. */
	updateRootPartition(&rootPartDesc);
}

/*!
 * \brief Initialize the Memory Abstraction Layer (MAL).
 */
extern void
malInit(void)
{
	/* The order of these two is load-bearing. checkMPU() probes every
	 * writable region and leaves them all turned off, the deny-all
	 * background included; initMPU() is what installs that background.
	 * Reversing them would clear it again, and U-mode would reach the
	 * boot ROM, every peripheral and SIO through the hardwired PMP
	 * entries 8 to 10, which cannot be disabled. */
	if (checkMPU() < 0)
	{
		PANIC("PIP: No PMP found...\n");
	}

	if (initMPU() < 0)
	{
		PANIC("PIP: Failed to clear the PMP...\n");
	}

	createAndRegisterRootPartition();
}
