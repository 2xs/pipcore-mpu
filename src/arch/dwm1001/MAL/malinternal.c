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

/**
 * \file malinternal.c
 * \brief This file contains some internal defines for MAL interface with Coq.
 * \warning These functions are roughly documented as their signification is quite straightforward. See mal.h for more information.
 */

#include <stdint.h>
#include <math.h>
#include "mal.h"
#include <stddef.h>
#include "mpu.h"

 uint32_t min_mpu_region;

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
 * \fn int32_t geb()
 * \brief the first parameter is greater than or equal to the second one.
 * \return the comparison.
 */
int geb(const int32_t a, const int32_t b)
{
	return a >= b;
}

/*!
 * \fn int32_t gtb()
 * \brief the first parameter is greater than the second one.
 * \return the comparison.
 */
int gtb(const int32_t a, const int32_t b)
{
	return a > b;
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
 * \fn uint32_t inc()
 * \brief incremet the value.
 * \return the incremented value.
 */
uint32_t inc(uint32_t val)
{
	return ++val;
}

/*!
 * \fn uint32_t dec()
 * \brief decrement value.
 * \return the decremented value.
 */
uint32_t dec(uint32_t val)
{
	return --val;
}


/*!
 * \fn uint32_t sub()
 * \brief substracts the second value from the first.
 * \return the result of the substraction.
 */
uint32_t sub(uint32_t a, uint32_t b)
{
	return a-b;
}

/*!
 * \fn uint32_t add()
 * \brief adds the first value to the second.
 * \return the result of the addition.
 */
uint32_t add(uint32_t a, uint32_t b)
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
 * \brief Returns the maximum number of regions in the physical MPU.
 * \return The maximum number of physical MPU regions.
 */
uint32_t getMPURegionsNb(void)
{
	return MPU_REGIONS_NB;
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
 * \fn uint32_t getMinBlockSize(void)
 * \brief Returns the minimum size of a block in bytes (MPU region constraint).
 * \return The minimum size in bytes of an MPU region.
 */
uint32_t MINBLOCKSIZE(void)
{
	return 32;//TODO : not hard-coded
}

/*!
 * \brief Returns the minimum size of a VIDT block in bytes.
 * \return The minimum size of a VIDT block in bytes.
 */
uint32_t MINVIDTBLOCKSIZE(void)
{
	/*
	 * The VIDT is an array of 128 pointers of 4 bytes. This
	 * requires a block of at least 512 bytes.
	 *
	 * TODO: Do not hard-code this value because on some
	 * architectures, a pointer is not necessarily equal to 4
	 * bytes.
	 */
	return 512;
}

/*!
 * \fn uint32_t PDSTRUCTURETOTALLENGTH(void)
 * \brief Returns the size of a PD structure expanded to fill an MPU region.
 * \return The size in bytes of a PD structure (matching a power of 2).
 */
uint32_t PDSTRUCTURETOTALLENGTH(void)
{
	return fit_mpu_region(sizeof(PDTable_t));
}

/*!
 * \fn uint32_t KERNELSTRUCTURETOTALLENGTH(void)
 * \brief Returns the size of a kernel structure expanded to fill an MPU region.
 * \return The size in bytes of a kernel structure (matching a power of 2).
 */
uint32_t KERNELSTRUCTURETOTALLENGTH(void)
{
	return fit_mpu_region(sizeof(KStructure_t));
}


/*!
 * \fn uint32_t fit_mpu_region(uint32_t block_size)
 * \brief  	Adapts to the MPU region size constraints (in bytes)
 * \param block_size The original size in bytes of the memory block
 * \return The next highest power of 2 of the given block size,
 			or the minimim MPU region size if too small.
 */
uint32_t fit_mpu_region(uint32_t block_size)
{
	uint32_t highest_pow2 = next_pow2(block_size);
	return min_mpu_region < highest_pow2 ? highest_pow2 : min_mpu_region;
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
 * \fn bool beqIdx(uint32_t a, uint32_t b)
 * \brief Compare two indexes
 * \return 1 if same index, 0 if not
 */
bool beqIdx(uint32_t a, uint32_t b)
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
 * \fn paddr predPaddr(paddr a)
 * \brief decrements the given address.
 * \return the previous address.
 */
paddr predPaddr(paddr a)
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
 * \fn paddr addPaddrIdxBytes(paddr a, uint32_t b)
 * \brief adds an offset in bytes to a paddr
 * \param a Address to offset
 * \param b the offset in bytes
 * \return the offseted address.
 */
paddr addPaddrIdxBytes(paddr a, uint32_t b)
{
	return (paddr) ((uint8_t*) a + b);
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
 * \fn void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr blockentryaddr)
 * \brief  	Configures the LUT entry at given index with the given MPU entry
 * \param LUT The LUT to configure at the given index
 * \param entryindex The index where to configure
 * \param blockentryaddr The block to configure
 * \param addrtocover ARMv7: An address that should be covered by the active MPU region
 * \return void
 */
void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr blockentryaddr, paddr addrtocover)
{
	if (blockentryaddr == NULL){
		// clear MPU entry
		LUT[entryindex*2] = (entryindex & 0xF) | MPU_RBAR_VALID_Msk;
		LUT[entryindex*2+1] = 0; // disable region
		return;
	}
	else {
		// Block should be mapped in the MPU
		// the BlockEntry already respects the minimum MPU size
		BlockEntry_t* blockentry = (BlockEntry_t*) blockentryaddr;

		#if defined(__ARM_ARCH_7M__) || defined(__ARM_ARCH_7EM__)
		// if ARMv7, find the largest MPU region matching the MPU aligment constraints
		block_t covering_block = largest_covering_MPU_region(blockentryaddr, addrtocover);
		#else
		// else configure the whole block
		block_t covering_block = blockentry->blockrange;
		#endif

		// MPU region size = 2^(regionsize +1) on 5 bits
		uint32_t size =  (uint32_t) covering_block.endAddr - (uint32_t)covering_block.startAddr;
		uint8_t regionsize = (uint8_t) powlog2(size) - 1;
		uint32_t AP = 2U; // PRIV RW/UNPRIV RO, region always readable checked before
		if (blockentry->write == 1)
		{
			AP = 3U; // PRIV/UNPRIV RW Full access
		}
		uint32_t XNbit = !blockentry->exec; // Execute Never 0 = executable, 1 = not executable
		LUT[entryindex*2] = (uint32_t) covering_block.startAddr | MPU_RBAR_VALID_Msk | entryindex;
		LUT[entryindex*2+1] = 	MPU_RASR_ENABLE_Msk |
								(regionsize << MPU_RASR_SIZE_Pos) | //& MPU_RASR_SIZE_Msk) |
								(AP << MPU_RASR_AP_Pos)  |  // R/W Priv/UnPriv
								(XNbit << MPU_RASR_XN_Pos) | // 0 = executable, 1 = not executable
								// ARM_MPU_ACCESS_(0U, 1U, 1U, 1U)     TEX  = b000,  C =  1, B =  1 -> Write back, no write allocate
								(0U << MPU_RASR_TEX_Pos) | //TypeExtField
								// TODO Do not use an instruction that generates a sequence of accesses to access Strongly-ordered memory
								// if the instruction might restart after an exception and repeat any write accesses, see Exceptions in Load
								// Multiple and Store Multiple operations on page B1-599 for more information
								(0U << MPU_RASR_S_Pos)| //IsShareable = 0 No data shared between seevral processors
								(0U << MPU_RASR_C_Pos)| //IsCacheable
								(0U << MPU_RASR_B_Pos) //| //IsBufferable
							;
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
 * \brief  	Checks that there is an MPU and that the compiled version matches the MPU attributes
 * \return -1 if the physical MPU doesn't match expectations of the code
 */
int checkMPU()
{
	if (MPU_NUM_REGIONS != MPU_REGIONS_NB) return -1;
	else return 0;
}

/*!
 * \fn int initMPU()
 * \brief  	Defaults all MPU regions
 * \return
 */
int initMPU()
{
	return mpu_init();
}
