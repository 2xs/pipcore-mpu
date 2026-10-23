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

/**
 * \file malinternal.c
 * \brief This file contains some internal defines for MAL interface with Coq.
 * \warning These functions are roughly documented as their signification is quite straightforward. See mal.h for more information.
 */

#include <stdint.h>
#include "mal.h"
#include <stddef.h>
#include "pmp.h"

uint32_t N = 1000;

uint32_t maxNbPrepare = MAXNBPREPARE;
uint32_t maxNbPreparePlusOne = MAXNBPREPAREP1;

paddr nullAddr = NULL;

/*!
 * \fn paddr getNullAddr(void)
 * \brief Returns the default null address.
 * \return The null address.
 */
paddr getNullAddr(void)
{
	return NULL;
}

/*!
 * \fn uint32_t zero(void)
 * \brief Returns zero.
 * \return zero.
 */
uint32_t zero(void)
{
	return 0;
}

/*!
 * \fn uint32_t one(void)
 * \brief Returns one.
 * \return one.
 */
uint32_t one(void)
{
	return 1;
}


/*!
 * \fn uint32_t addressEquals(uint32_t addr, uint32_t addr2)
 * \param addr Address to check
 * \param addr2 Address to compare to
 * \brief Checks if an address given is equal to another given.
 * \return 0 is not equal, 1 otherwise.
 */
uint32_t addressEquals(uint32_t addr, uint32_t addr2)
{
	return (addr == addr2);
}

/*!
 * \fn int32_t leb()
 * \brief the first parameter is less than or equal to the second one.
 * \return the comparison.
 */
int leb(const int32_t a, const int32_t b)
{
	return a <= b;
}

/*!
 * \fn int32_t ltb()
 * \brief the first parameter is less than the second one.
 * \return the comparison.
 */
int ltb(const int32_t a, const int32_t b)
{
	return a < b;
}

/*!
 * \fn int32_t eqb()
 * \brief the first parameter is equal to the second one.
 * \return the comparison.
 */
int eqb(const int32_t a, const int32_t b)
{
	return a == b;
}

/*!
 * \brief increment an index
 * \return the incremented value.
 */
Coq_index indexSuccM(Coq_index val)
{
	return ++val;
}

/*!
 * \brief decrement index
 * \return the decremented value.
 */
Coq_index indexPredM(Coq_index val)
{
	return --val;
}

/*!
 * \brief substracts the second index from the first.
 * \return the result of the substraction.
 */
Coq_index indexSubM(Coq_index a, Coq_index b)
{
	return a-b;
}

/*!
 * \brief adds the first index to the second.
 * \return the result of the addition.
 */
Coq_index indexAddM(Coq_index a, Coq_index b)
{
	return a+b;
}

/*!
 * \fn uint32_t mul()
 * \brief multiples the first value with the second.
 * \return the result of the multiplication.
 */
uint32_t mul(uint32_t a, uint32_t b)
{
	return a*b;
}

/*!
 * \fn uint32_t getKernelStructureEntriesNb(void)
 * \brief Returns the kernel structure entries number.
 * \return The kernel structure entries number.
 */
uint32_t getKernelStructureEntriesNb(void)
{
	return KERNELSTRUCTUREENTRIESNB;
}

/*!
 * \fn uint32_t getMaxNbPrepare(void)
 * \brief Returns the maximum number of allowed prepare.
 * \return The maximum number of prepare.
 */
uint32_t getMaxNbPrepare(void)
{
	return MAXNBPREPARE;
}

/*!
 * \fn uint32_t getMPURegionsNb(void)
 * \brief Returns the maximum number of available regions in the physical MPU.
 *
 * Three of the eight writable PMP entries are not the user's to set. Two are
 * the refill slots the fault handler rewrites on a partially mapped block,
 * exactly as on ARMv7-M; the third is the permanent deny-all background that
 * shadows the hardwired entries 8, 9 and 10, which would otherwise grant
 * U-mode full access to the boot ROM, every peripheral and SIO.
 *
 * Note the index polarity is the mirror of ARM's. The ARM MPU is
 * highest-region-wins, so its reserved slots are the last two; PMP is
 * lowest-matching-entry-wins, so the reserved ones are the *highest* indices
 * (5, 6 and 7) and the partition-visible ones are 0 to 4, which lets a
 * partition-visible entry win over a refill slot on overlap.
 *
 * \warning These last three PMP entries MUST NOT be set by users, otherwise
 *          the refill policy would overwrite them, or the deny-all background
 *          would be lost.
 * \see src/arch/rp2350/boot/include/pmp.h for the index budget
 * \return The maximum number of available physical MPU regions.
 */
uint32_t getMPURegionsNb(void)
{
	return MPU_REGIONS_NB - 3;
}


/*!
 * \fn uint32_t next_pow2(uint32_t v)
 * \brief  	Rounds up to the next highest power of 2 of 32-bit
 * 			https://graphics.stanford.edu/~seander/bithacks.html#RoundUpPowerOf2
 * \param v The original value
 * \return The next highest power of 2 of v.
 */
uint32_t next_pow2(uint32_t v)
{
	v--;
	v |= v >> 1;
	v |= v >> 2;
	v |= v >> 4;
	v |= v >> 8;
	v |= v >> 16;
	v++;
	return v;
}

/*!
 * \fn uint32_t powlog2(uint32_t v)
 * \brief  	Finds the log base 2 of a 32-bit integer with the MSB N set in O(N) operations (the obvious way)
 * 			https://graphics.stanford.edu/~seander/bithacks.html#IntegerLogObvious
 *			We expect small integers (a high number of leading zeroes) so the naive approach is acceptable
 * \param v The 32-bit integer
 * \return The position of the highest bit of v.
 */
uint32_t powlog2(uint32_t v)
{
	unsigned r = 0;

	while (v >>= 1) { // shifts to the right until the highest bit disappears
		r++;
	}
	return r;
}

/*!
 * \fn uint32_t max_powlog2_alignment(uint32_t v)
 * \brief Computes the highest pow2 alignment of an address (min is 2^(5)=32-bytes alignment).
 * \return The highest pow2 alignment.
 */
uint32_t max_powlog2_alignment(uint32_t v)
{
	if(v==0) return 31;
	// Counts the number of trailing zeroes after the minimum 32 bytes so 2⁽5)
	unsigned r = 4;
	v = v >> r;
	do{
		r++;
	}
	while (((v >>= 1) & 0x1) != 1); // shifts to the right until the first bit appears
	return r;
}

/*!
 * \fn bool is_power_of_two(uint32_t v)
 * \brief Checks that a value is a power of two.
 *        https://graphics.stanford.edu/~seander/bithacks.html#DetermineIfPowerOf2
 * \return true when v is a power of two, false otherwise.
 */
bool is_power_of_two(uint32_t v)
{
	return v && !(v & (v - 1));
}

/*!
 * \fn uint32_t roundUpTo32(uint32_t v)
 * \brief Rounds up value to the next multiple of 32
 * \return the value round up to the next multiple of 32,
 * or the value itself if it is already a multiple of 32.
 */
uint32_t roundUpTo32(uint32_t v)
{
	return (((v) + 31) & (~31));
}

/*!
 * \fn uint32_t getMinBlockSize(void)
 * \brief Returns the minimum size of a block in bytes (MPU region constraint).
 *
 * 32 bytes, which on this target is exactly the PMP granule rather than a
 * conservative over-estimate: pmpaddr[1:0] are unimplemented, so a NAPOT
 * region smaller than 32 bytes cannot be expressed and would be matched as
 * 32 -- granting more than was asked for. Keeping this at 32 is what makes
 * every partition-visible region expressible.
 *
 * \see PMP_NAPOT_HW_MIN_LOG2 in src/arch/rp2350/boot/include/pmp.h
 * \return The minimum size in bytes of an MPU region.
 */
uint32_t getMinBlockSize(void)
{
	return 32;//TODO : not hard-coded
}

/*!
 * \brief Returns the minimum size of a VIDT block in bytes.
 * \return The minimum size of a VIDT block in bytes.
 */
uint32_t getVidtSize(void)
{
	/*
	 * sizeof(vidt_t), which the VIDT index map of ADT.h deliberately keeps
	 * at 4 + 56*4 so that this value matches the ARM target's.
	 *
	 * TODO: Do not hard-code the value.
	 */
	return 228;
}

/*!
 * \brief Returns the size of a PD structure expanded to fill an MPU region.
 * \return The size in bytes of a PD structure (matching a power of 2).
 */
uint32_t getPDStructureTotalLength(void)
{
	return roundUpTo32(sizeof(PDTable_t));
}

/*!
 * \brief Returns the size of a kernel structure expanded to fill an MPU region.
 * \return The size in bytes of a kernel structure (matching a power of 2).
 */
uint32_t getKernelStructureTotalLength(void)
{
	return roundUpTo32(sizeof(KStructure_t));
}

/*!
 * \fn bool checkMPUEntryZero(paddr addr, uint32_t size)
 * \brief Checks that an address is valid regarding to MPU entry 0.
 *
 * \param addr Address of the memory block to be checked
 * \param size Size of the memory block to be checked
 *
 * \retval false when size is less than getMinBlockSize or not a power of two
 *               or addr % size is different from 0
 * \retval true otherwise.
 */

bool checkMPUEntryZero(paddr addr, uint32_t size) {
	if (size < getMinBlockSize() || (is_power_of_two(size) == false))
		return false;

    uintptr_t start_addr = (uintptr_t)((block_t *)addr)->startAddr;

	return ( (((uintptr_t)start_addr) % size) == 0 );
}

/*!
 * \fn bool beqAddr(paddr a, paddr b)
 * \brief Compare two addresses
 * \return 1 if same address, 0 if not
 */
bool beqAddr(paddr a, paddr b)
{
	return (a == b);
}

/*!
 * \fn uint32_t subPaddr(paddr a, paddr b)
 * \brief substracts the first paddr to the second.
 * \return the result of the substraction.
 */
uint32_t subPaddr(paddr a, paddr b)
{
	return a - b;
}

/*!
 * \fn paddr paddrPredM(paddr a)
 * \brief decrements the given address.
 * \return the previous address.
 */
paddr paddrPredM(paddr a)
{
	return --a;
}

/*!
 * \fn bool lebPaddr(const paddr a, const paddr b)
 * \brief the first parameter is less than or equal to the second one.
 * \return the comparison.
 */
bool lebPaddr(const paddr a, const paddr b)
{
	return a <= b;
}

/*!
 * \fn paddr getAddr(paddr addr);
 * \brief returns the address
 * \return the address.
 */
paddr getAddr(paddr addr)
{
	return addr;
}

/*!
 * \fn block_t largest_covering_MPU_region(paddr blockentryaddr, paddr addrtocover)
 * \brief 	Computes the largest MPU region possible within the block <blockentryaddr>'s bounds
 *			and covering the <addrtocover>.
 *			The algorithm starts with the smallest 32-bytes MPU region around the address to cover
 *			(within the bounds because the start or end addresses of a block are 32-bytes aligned).
 *			It then finds the largest covering MPU region by looking for the best aligned address
 *			out of the initial small MPU region, and then compute the MPU region with this alignment.
 *			If the new MPU region is within the bounds, it continues like this until the MPU region grows too large.
 *			The largest covering MPU region is the one just before beeing too large.
 *
 *			Ported unchanged from the ARMv7-M target. Its contract -- a returned
 *			{bottom, top} with top exclusive, top - bottom a power of two and
 *			bottom aligned on that size -- is exactly what PMP NAPOT requires,
 *			because this core supports neither TOR nor a granule below 32 bytes.
 *
 * \return the largest MPU region covering the address and within the block
 */
block_t largest_covering_MPU_region(paddr blockentryaddr, paddr addrtocover)
{
	BlockEntry_t* blockentry = (BlockEntry_t*) blockentryaddr;
	uint32_t startAddr = (uint32_t) blockentry->blockrange.startAddr;
	uint32_t endAddr = (uint32_t) blockentry->blockrange.endAddr + 1;

	// Find the largest region containing the address and within the bounds of the block
	uint32_t bottom = (uint32_t) addrtocover & 0xFFFFFFE0; // align to previous 32 bytes
	uint32_t top = bottom + 32*sizeof(char); // align to next 32 bytes

	// the largest region ever is 2^(32) bytes large
	for(int i=0; i<32; i++){
		// compute the pow2 alignment of the top and bottom MPU region
		uint32_t top_maxpow2 = max_powlog2_alignment(top);
		uint32_t bottom_maxpow2 = max_powlog2_alignment(bottom);

		// find the best alignment
		if(top_maxpow2 > bottom_maxpow2){
			// Top has a better alignment: compute the bottom address with this alignment
			bottom = top - (1 << top_maxpow2);
			// Settle top and find alignment suiting bottom as well
			if(bottom < startAddr){
				// Bottom became too large, settle top and adjust bottom by decreasing pow2
				// until tucking the block's bounds
				uint32_t tmp_maxpow2 = top_maxpow2;
				do{
					tmp_maxpow2 = tmp_maxpow2 - 1; // previous pow2
					bottom = top - (1 << tmp_maxpow2);
				}
				while(bottom < startAddr);
				// block is largest possible, stop
				break;
			}
			else{// else block can still grow with better aligment, continue search
				continue;
			}
		}
		else{
			// Bottom has better alignment: compute the top address with this alignment
			top = bottom + (1 << bottom_maxpow2);
			if(top > endAddr){
				// Top became too large, settle bottom and adjust top by decreasing pow2
				// until tucking the block's bounds
				uint32_t tmp_maxpow2 = bottom_maxpow2;
				do{
					tmp_maxpow2 = tmp_maxpow2 - 1; // previous pow2
					top = bottom + (1 << tmp_maxpow2);
				}
				while(top>endAddr);
				// block is largest possible, stop
				break;
			}
			else{// else block can still grow with better aligment, continue search
				continue;
			}
		}
	}
	return (block_t){(paddr) bottom , (paddr) top};
}

/*!
 * \fn void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr blockentryaddr, paddr addrtocover)
 * \brief  	Configures the LUT entry at given index with the given MPU entry
 *
 * The LUT keeps the shape it has on ARMv7-M -- two words per region -- but
 * both change meaning: LUT[2i] is a pmpaddr value and LUT[2i+1] a pmpcfg
 * byte, zero-extended, where zero means the region is off. activate() packs
 * them into the pmpaddr and pmpcfg CSRs.
 *
 * \param LUT The LUT to configure at the given index
 * \param entryindex The index where to configure
 * \param blockentryaddr The block to configure
 * \param addrtocover An address that should be covered by the active PMP region
 * \return void
 */
void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr blockentryaddr, paddr addrtocover)
{
	if (blockentryaddr == NULL){
		// Turn the region off. Unlike ARM's RBAR, a pmpaddr carries no
		// valid bit and no region index, so a cleared entry is just zero.
		LUT[entryindex*2] = 0;
		LUT[entryindex*2+1] = 0; // A = OFF, matches nothing
		return;
	}
	else {
		// Block should be mapped in the PMP
		// the BlockEntry already respects the minimum PMP region size
		BlockEntry_t* blockentry = (BlockEntry_t*) blockentryaddr;

		// This core has no TOR, so an arbitrary block is never mappable
		// exactly and the solver is always needed. On ARM this was behind
		// an #if on __ARM_ARCH_7M__, with the whole block mapped otherwise.
		block_t covering_block = largest_covering_MPU_region(blockentryaddr, addrtocover);

		// top is exclusive, so this is the region size: a power of two,
		// at least 32, with startAddr aligned on it
		uint32_t size = (uint32_t) covering_block.endAddr - (uint32_t) covering_block.startAddr;

		// PMP has no privileged/unprivileged attribute pair like ARM's AP,
		// because an L=0 entry does not constrain M-mode at all -- which is
		// what ARM needed PRIVDEFENA for. So AP=2 vs AP=3 collapses to the
		// W bit alone, and L is never set.
		//
		// R is set unconditionally: the model checks readability before
		// mapping, as the ARM version also assumed. PMP does have
		// independent R, so a later milestone can honour blockentry->read
		// directly, which ARM's two-valued AP could not express.
		LUT[entryindex*2] = pmp_napot((uint32_t) covering_block.startAddr,
		                              powlog2(size));
		LUT[entryindex*2+1] = PMPCFG_A_NAPOT | PMPCFG_R |
		                      (blockentry->write ? PMPCFG_W : 0) |
		                      (blockentry->exec ? PMPCFG_X : 0);
	}
}

/*!
 * \fn void clear_LUT(uint32_t* LUT)
 * \brief  Defaults all LUT entries
 * \param LUT The LUT where to clear the entries
 * \return void
 */
void clear_LUT(uint32_t* LUT)
{
	for (int i=0 ; i < MPU_REGIONS_NB ; i++)
	{
		configure_LUT_entry(LUT, i, NULL, NULL);
	}
}

/*!
 * \fn int checkMPU()
 * \brief  	Checks that there is a PMP and that it is the one this port assumes
 *
 * There is no register holding a region count to compare against, the way
 * ARM's MPU_TYPE did, so this probes instead: every writable entry must
 * accept and return a configuration byte, and entry 8 must read back as the
 * hardwired full-access window it is documented to be.
 *
 * \warning It leaves every region off, the deny-all background included, so
 *          initMPU() must run after it and before any U-mode entry.
 * \return -1 if the physical PMP doesn't match expectations of the code
 */
int checkMPU()
{
	return pmpCheck() ? 0 : -1;
}

/*!
 * \fn int initMPU()
 * \brief  	Defaults all PMP regions and installs the deny-all background
 * \return 0
 */
int initMPU()
{
	pmpInit();
	return 0;
}
