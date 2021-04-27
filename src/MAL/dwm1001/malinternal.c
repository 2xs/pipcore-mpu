/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2021)                 */
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

 uint32_t mpuoffset;
 uint32_t sh1offset;
 uint32_t scoffset;
 uint32_t nextoffset;
 uint32_t mpuentrylength;
 uint32_t sh1entrylength;
 uint32_t scentrylength;
 uint32_t kernelstructureentriesnb;
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
 * \fn uint32_t geb()
 * \brief the first parameter is greater than or equal to the second one.
 * \return the comparison.
 */
int geb(const uint32_t a, const uint32_t b)
{
	return a >= b;
}

/*!
 * \fn uint32_t gtb()
 * \brief the first parameter is greater than the second one.
 * \return the comparison.
 */
int gtb(const uint32_t a, const uint32_t b)
{
	return a > b;
}

/*!
 * \fn uint32_t leb()
 * \brief the first parameter is less than or equal to the second one.
 * \return the comparison.
 */
int leb(const uint32_t a, const uint32_t b)
{
	return a <= b;
}

/*!
 * \fn uint32_t ltb()
 * \brief the first parameter is less than the second one.
 * \return the comparison.
 */
int ltb(const uint32_t a, const uint32_t b)
{
	return a < b;
}

/*!
 * \fn uint32_t eqb()
 * \brief the first parameter is equal to the second one.
 * \return the comparison.
 */
int eqb(const uint32_t a, const uint32_t b)
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
 * \fn uint32_t KERNELSTRUCTUREENTRIESNB(void)
 * \brief Returns the maximum number of entries in a kernel structure.
 * \return The number of entries in a kernel structure.
 */
uint32_t KERNELSTRUCTUREENTRIESNB(void)
{
	return pow(2,KERNELSTRUCTUREENTRIESBITS);
}

/*!
 * \fn uint32_t MAXNBPREPARE(void)
 * \brief Returns the maximum number of times a partition can be prepared.
 * \return The maximum number of times a partition can be prepared.
 */
uint32_t MAXNBPREPARE(void)
{
	return pow(2,NBPREPAREMAXBITS);
}

/*!
 * \fn uint32_t MPUENTRYLENGTH(void)
 * \brief Returns the size of an MPU entry.
 * \return The MPU entry size.
 */
uint32_t MPUENTRYLENGTH(void)
{
	return sizeof(MPUEntry_t);
}

/*!
 * \fn uint32_t SH1ENTRYLENGTH(void)
 * \brief Returns the size of a shadow 1 entry.
 * \return The shadow 1 entry size.
 */
uint32_t SH1ENTRYLENGTH(void)
{
	return sizeof(Sh1Entry_t);
}

/*!
 * \fn uint32_t SCENTRYLENGTH(void)
 * \brief Returns the size of a shadow cut entry.
 * \return The shadow cut entry size.
 */
uint32_t SCENTRYLENGTH(void)
{
	return sizeof(SCEntry_t);
}


/*!
 * \fn uint32_t MPUOFFSET()
 * \brief Returns the MPU structure offset.
 * \return The MPU structure offset.
 */
uint32_t MPUOFFSET(void)
{
	return 0;
}

/*!
 * \fn uint32_t SH1OFFSET()
 * \brief Returns the shadow 1 offset.
 * \return The shadow 1 offset.
 */
uint32_t SH1OFFSET(void)
{
	return mpuoffset + (kernelstructureentriesnb*mpuentrylength);
}

/*!
 * \fn uint32_t SCOFFSET()
 * \brief Returns the shadow cut offset.
 * \return The shadow cut offset.
 */
uint32_t SCOFFSET(void)
{
	return sh1offset + (kernelstructureentriesnb*sh1entrylength);
}

/*!
 * \fn uint32_t nextoffset(void)
 * \brief Returns the next structure pointer offset.
 * \return The next structure pointer offset.
 */
uint32_t NEXTOFFSET(void)
{
	return scoffset + (kernelstructureentriesnb*scentrylength);
}


/*!
 * \fn paddr getKernelStructureStartAddr(paddr mpuentryaddr, uint32_t mpuentryindex)
 * \brief Gets the kernel structure start address from the MPU entry.
 * \param mpuentryaddr The address of the MPU entry
 * \param mpuentryindex The index of the MPU entry
 * \return The start of the kernel structure frame
 */
paddr getKernelStructureStartAddr(paddr mpuentryaddr, uint32_t mpuentryindex)
{
	return mpuentryaddr-(mpuentryindex*mpuentrylength); // TODO: Over/underflow ?
}

/*!
 * \fn paddr getMPUEntryAddrFromKernelStructureStart(paddr kernelstartaddr, uint32_t mpuentryindex)
 * \brief Gets the address where to find the MPU entry corresponding to the given index.
 * \param kernelstartaddr The address where the kernel structure starts
 * \param mpuentryindex The index of the MPU entry
 * \return The address of the MPU entry
 */
paddr getMPUEntryAddrFromKernelStructureStart(paddr kernelstartaddr, uint32_t mpuentryindex)
{
	return kernelstartaddr + mpuoffset + (mpuentryindex*mpuentrylength); // TODO: Over/underflow ?
}

/*!
 * \fn paddr getSh1EntryAddrFromKernelStructureStart(paddr kernelstartaddr, uint32_t mpuentryindex)
 * \brief Gets the address where to find the Shadow 1 entry corresponding to the given index.
 * \param kernelstartaddr The address where the kernel structure starts
 * \param mpuentryindex The index of the MPU entry
 * \return The address of the shadow 1 entry
 */
paddr getSh1EntryAddrFromKernelStructureStart(paddr kernelstartaddr, uint32_t mpuentryindex)
{
	return kernelstartaddr + sh1offset + (mpuentryindex*sh1entrylength); // TODO: Over/underflow ?
}

/*!
 * \fn paddr getSCEntryAddrFromKernelStructureStart(paddr kernelstartaddr, uint32_t mpuentryindex)
 * \brief Gets the address where to find the Shadow Cut entry corresponding to the given index.
 * \param kernelstartaddr The address where the kernel structure starts
 * \param mpuentryindex The index of the MPU entry
 * \return The address of the shadow cut entry
 */
paddr getSCEntryAddrFromKernelStructureStart(paddr kernelstartaddr, uint32_t mpuentryindex)
{
	return kernelstartaddr + scoffset + (mpuentryindex*scentrylength); // TODO: Over/underflow ?
}

/*!
 * \fn paddr* getNextAddrFromKernelStructureStart(paddr kernelstartaddr)
 * \brief Gets the address where to find the next structure pointer.
 * \param kernelstartaddr The address where the kernel structure starts
 * \return The address of the next structure pointer
 */
paddr* getNextAddrFromKernelStructureStart(paddr kernelstartaddr)
{
	return (paddr*) kernelstartaddr + nextoffset;
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
 * \fn uint32_t getMinBlockSize(void)
 * \brief Returns the minimum size of a block (MPU constraint).
 * \return The minimum size of an MPU block.
 */
uint32_t MINBLOCKSIZE(void)
{
	return 32;//TODO : not hard-coded
}

/*!
 * \fn uint32_t PDSTRUCTURETOTALLENGTH(void)
 * \brief Returns the size of a PD structure expanded to fill an MPU region.
 * \return The size of a PD structure (matching a power of 2).
 */
uint32_t PDSTRUCTURETOTALLENGTH(void)
{
	return fit_mpu_region(sizeof(PDTable_t));
}

/*!
 * \fn uint32_t KERNELSTRUCTURETOTALLENGTH(void)
 * \brief Returns the size of a kernel structure expanded to fill an MPU region.
 * \return The size of a kernel structure (matching a power of 2).
 */
uint32_t KERNELSTRUCTURETOTALLENGTH(void)
{
	return fit_mpu_region(kernelstructureentriesnb*mpuentrylength + kernelstructureentriesnb*sh1entrylength + kernelstructureentriesnb*scentrylength + sizeof(uint32_t));
}


/*!
 * \fn uint32_t fit_mpu_region(uint32_t block_size)
 * \brief  	Adapts to the MPU region size constraints
 * \param v The original size of the memory block
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
 * \fn paddr subPaddr(paddr a, paddr b)
 * \brief substracts the first paddr to the second.
 * \return the result of the substraction.
 */
uint32_t subPaddr(paddr a, paddr b)
{
	return a-b;
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
 * \fn paddr addPaddrIdx(paddr a, uint32_t b)
 * \brief adds an offset to a paddr
 * \return the offseted address.
 */
paddr addPaddrIdx(paddr a, uint32_t b)
{
	return a + b;
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
 * \fn void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr mpuentryaddr)
 * \brief  	Configures the LUT entry at given index with the given MPU entry
 * \param LUT The LUT to configure at the given index
 * \param entryindex The index where to configure
 * \param mpuentryaddr The block to configure
 * \return void
 */
void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr mpuentryaddr)
{
	// the MPUEntry already respects the minimum MPU size
	MPUEntry_t* mpuentry = (MPUEntry_t*) mpuentryaddr;
	// MPU region size = 2^(regionsize +1) on 5 bits
	uint32_t size =  (uint32_t) (mpuentry->mpublock).endAddr - (uint32_t)(mpuentry->mpublock).startAddr;
	uint8_t regionsize = (uint8_t) powlog2(size) - 1;
	uint32_t XNbit = 0;
	LUT[entryindex*2] = ((uint32_t)(mpuentry->mpublock).startAddr | MPU_RBAR_VALID_Msk | entryindex);
	LUT[entryindex*2+1] = 	MPU_RASR_ENABLE_Msk |
							(regionsize << MPU_RASR_SIZE_Pos) | //& MPU_RASR_SIZE_Msk) |
							(3U << MPU_RASR_AP_Pos)  |  //full access R/W Priv/UnPriv TODO: restrict to permissions set to the block
							//(1U << MPU_RASR_SRD_Pos) | // subregion SRD disabled (=1)
							(XNbit << MPU_RASR_XN_Pos) | // 0 = executable, 1 = not executable
							// ARM_MPU_ACCESS_(0U, 1U, 1U, 1U)     TEX  = b000,  C =  1, B =  1 -> Write back, no write allocate
							(0U << MPU_RASR_TEX_Pos) | //TypeExtField
							(1U << MPU_RASR_S_Pos)| //IsShareable = 0 No data shared between seevral processors
							(1U << MPU_RASR_C_Pos)| //IsCacheable
							(1U << MPU_RASR_B_Pos) //| //IsBufferable
						;
}

/*!
 * \fn void clear_LUT_entry(uint32_t* LUT, uint32_t entryindex)
 * \brief  Defaults the LUT entry at the given index
 * \param LUT The LUT where to erase the entry
 * \param entryindex The entry to erase
 * \return void
 */
void clear_LUT_entry(uint32_t* LUT, uint32_t entryindex)
{
	LUT[entryindex*2] = (entryindex & 0xF) | MPU_RBAR_VALID_Msk;
	LUT[entryindex*2+1] = 0; // disable region
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
		clear_LUT_entry(LUT, i);
	}
}

/*!
 * \fn int checkMPU()
 * \brief  	Checks that there is an MPU and that the compiled version matches the MPU attributes
 * \return -1 if the physical MPU doesn't match expectations of the code
 */
int checkMPU()
{
	if (MPU_NUM_REGIONS < 0 || MPU_NUM_REGIONS != MPU_REGIONS_NB) return -1;
	else return 0;
}