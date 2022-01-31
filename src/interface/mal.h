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

/**
 * \file mal.h
 * \brief Memory Abstraction Layer common interface
 */

#ifndef __MAL__
#define __MAL__
#include "ADT.h"

#include <stddef.h>


/* Activate : deprecated */
void activate(paddr dir);

/* Current page directory */
extern paddr root_partition;
paddr getCurPartition(void); //!< Interface to get the current Page Directory
void updateCurPartition (paddr descriptor);

paddr getRootPartition(void); //!< Interface to get the current Page Directory
void updateRootPartition (paddr descriptor);

uint32_t getTableSize(void); //!< Table size
uint32_t getMaxIndex(void); //!< Table size
uint32_t addressEquals(uint32_t addr, uint32_t addr2); //!< Checks whether an address is equal to another.
void cleanPage(uint32_t paddr); //!< Cleans a given page, filling it with zero
uint32_t toAddr(uint32_t input); //!< Converts a given uint32_t to an address (only for Haskell FFI purposes)

/* Coq related stuff */
int geb(const int32_t a, const int32_t b); //!< Greater or equal
int gtb(const int32_t a, const int32_t b); //!< Greater than
int leb(const int32_t a, const int32_t b); //!< Lower or equal
int ltb(const int32_t a, const int32_t b); //!< Lower than
int eqb(const int32_t a, const int32_t b); //!< Equals
uint32_t mul3(uint32_t v); //!< Multiply an integer with 3
uint32_t inc(uint32_t val); //!< Increment an integer
uint32_t dec(uint32_t val); //!< Decrement an integer
uint32_t zero(); //!< Zero. That's it.
uint32_t one(); //!< One.

void mal_init(void);

/* ARM */
/* MALInternal */
uint32_t mul(uint32_t a, uint32_t b); //!< Multiply two integers
uint32_t sub(uint32_t a, uint32_t b); //!< Substract two integers
uint32_t add(uint32_t a, uint32_t b); //!< Add two integers
uint32_t getKernelStructureEntriesNb(); //!< The kernel structure entries number
uint32_t getMaxNbPrepare(); //!<  The maximum number of prepare
uint32_t getMPURegionsNb(void); //! The maximum number of physical MPU regions
uint32_t KERNELSTRUCTURETOTALLENGTH(void);
uint32_t PDSTRUCTURETOTALLENGTH(void);
extern uint32_t min_mpu_region;
uint32_t MINBLOCKSIZE(void);

paddr getKernelStructureStartAddr(paddr blockentryaddr, uint32_t blockentryindex); //!< The start of the kernel structure frame
paddr getBlockEntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex); //!< The address of the block entry given the index and the KS
paddr getSh1EntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex); //!< The address of the shadow 1 entry
paddr getSCEntryAddrFromKernelStructureStart(paddr blockentryaddr, uint32_t blockentryindex); //!< The address of the shadow cut entry
paddr getNextAddrFromKernelStructureStart(paddr structureaddr); //!< The address of the next pointer
uint32_t fit_mpu_region(uint32_t block_size);
uint32_t next_pow2(uint32_t v);
uint32_t powlog2(uint32_t v);
uint32_t max_powlog2_alignment(uint32_t v);
block_t largest_covering_MPU_region(paddr blockentryaddr, paddr addrtocover); //!< Computes the largest MPU region mathing the ARMv7 MPU alignment constraints while covering the target address

paddr getNullAddr(void); //!< Returns the default null address.
bool beqAddr(paddr a, paddr b); //!< Compare two addresses
bool beqIdx(uint32_t a, uint32_t b); //!< Compare two indexes
paddr addPaddrIdxBytes(paddr a, uint32_t b); //!< adds an offset to a paddr
uint32_t subPaddr(paddr a, paddr b); //!< substracts the first paddr to the second.
bool lebPaddr(const paddr a, const paddr b); //!< the first parameter is less than or equal to the second one.
paddr predPaddr(paddr a); //!< decrements the given address.
paddr getAddr(paddr addr); //!< returns the address //TODO to remove


/* MAL */
PDTable_t readPDTable(paddr pdaddr); //!< Gets the Partition Descriptor (PD)
paddr readPDStructurePointer(paddr pdaddr); //!< Gets the first kernel structure
void writePDStructurePointer(paddr pdaddr, paddr value); //!< Sets the first kernel structure
paddr readPDFirstFreeSlotPointer(paddr pdaddr); //!< Gets the first free slot's address
void writePDFirstFreeSlotPointer(paddr pdaddr, paddr value); //!< Sets the first free slot's address
uint32_t readPDNbFreeSlots(paddr pdaddr); //!< Gets the number of free slots left
void writePDNbFreeSlots(paddr pdaddr, uint32_t value); //!< Sets the number of free slots left
uint32_t readPDNbPrepare(paddr pdaddr); //!< Gets the number of prepare done util then.
void writePDNbPrepare(paddr pdaddr, uint32_t value); //!< Sets the number of prepare done util then
paddr readPDParent(paddr pdaddr); //!< Gets the parent PD's address
void writePDParent(paddr pdaddr, paddr value); //!< Sets the parent PD's address
paddr readPDVidt(paddr pdaddr); //!< Read the VIDT block from the partition descriptor structure.
void writePDVidt(paddr pdaddr, paddr value); //!< Write the VIDT block to the partition descriptor structure.
paddr readBlockStartFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the block's start address from the given entry
void writeBlockStartFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the block's start address
paddr readBlockEndFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the block's end address from the given entry
void writeBlockEndFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the block's end address
bool readBlockAccessibleFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the Accessible flag from the given entry
void writeBlockAccessibleFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets a memory block as accessible or not
bool readBlockPresentFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the Present flag from the given entry
void writeBlockPresentFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets a memory block as present or not
uint32_t readBlockIndexFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the block index from the given entry
void writeBlockIndexFromBlockEntryAddr(paddr blockentryaddr, uint32_t value); //!< Sets the block index
bool readBlockRFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the read flag
void writeBlockRFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the read flag
bool readBlockWFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the write flag
void writeBlockWFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the write flag
bool readBlockXFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the exec flag
void writeBlockXFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the exec flag
BlockEntry_t readBlockEntryFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the block entry
void writeBlockEntryFromBlockEntryAddr(paddr blockentryaddr, BlockEntry_t value); //!< Sets the block entry
void writeBlockEntryWithIndexFromBlockEntryAddr(paddr blockentryaddr, uint32_t index, BlockEntry_t value); //!< Sets the block entry with given index
paddr getSh1EntryAddrFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the Sh1 entry from the block entry
paddr readSh1PDChildFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the child's PD from the given entry
void writeSh1PDChildFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!< Sets the entry's child PD
bool readSh1PDFlagFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the child's PD from the given entry
void writeSh1PDFlagFromBlockEntryAddr(paddr blockentryaddr, bool value); //!< Sets the entry's PD flag
paddr readSh1InChildLocationFromBlockEntryAddr(paddr blockentryaddr); //!< Gets the location of the block in the child
void writeSh1InChildLocationFromBlockEntryAddr(paddr blockentryaddr, paddr value); //!<Sets the block's location in the child
void writeSh1EntryFromBlockEntryAddr(paddr blockentryaddr, Sh1Entry_t newsh1entry);//! Sets the block's Sh1 entry
paddr getSCEntryAddrFromBlockEntryAddr(paddr blockentryaddr); //! Gets the SC entry from the block entry
paddr readSCOriginFromBlockEntryAddr(paddr blockentryaddr); //! Gets the block's origin
void writeSCOriginFromBlockEntryAddr(paddr blockentryaddr, paddr value); //! Sets the block's origin
paddr readSCNextFromBlockEntryAddr(paddr blockentryaddr); //! Gets the block's next subblock
void writeSCNextFromBlockEntryAddr(paddr blockentryaddr, paddr value); //! Sets the block's next subblock
void writeSCEntryFromBlockEntryAddr(paddr blockentryaddr, SCEntry_t newscentry); //! Sets the block's SC entry
paddr readNextFromKernelStructureStart(paddr structureaddr); //! Gets the block's next subblock
void writeNextFromKernelStructureStart(paddr structureaddr, paddr newnextstructure); //! Sets the block's SC entry
bool eraseBlock (paddr startAddr, paddr endAddr); //! Erases the memory block defined by (startAddr, endAddr).
void writePDTable(paddr addr, PDTable_t newpdtable); //! Sets a new PD Table at the given address
PDTable_t getDefaultPDTable(); //! Returns the default PD Table without initialisation
PDTable_t getEmptyPDTable(); //! Returns the default PD Table with initialisation
BlockEntry_t getDefaultBlockEntry(); //! Returns the default block entry
Sh1Entry_t getDefaultSh1Entry(); //! Returns the default Sh1 entry
SCEntry_t getDefaultSCEntry(); //! Returns the default SC entry
BlockEntry_t buildBlockEntry(paddr startaddr, paddr endaddr, bool accessiblebit, bool presentbit); //! Constructs a block entry given the attributes
paddr getPDStructurePointerAddrFromPD(paddr pdaddr); //! Gets the structure pointer of the given PD
bool checkEntry(paddr kstructurestart, paddr blockentryaddr); //! Checks a block entry is valid in the kernel structure
bool checkBlockInRAM(paddr blockentryaddr); //! Checks whether the block is entirely in RAM
bool check32Aligned(paddr addrToCheck); //! Checks whether the address is 32-bytes aligned
blockOrError blockAttr(paddr blockentryaddr, BlockEntry_t blockentry); //! Wrapper to create a block and its attributes

paddr readBlockFromPhysicalMPU(paddr pd, uint32_t MPURegionNb);  //! Reads the block configured at the given region of the physical MPU.
void removeBlockFromPhysicalMPU(paddr pd, paddr blockentryaddr); //! Removes a block from the physical MPU.
void removeBlockFromPhysicalMPUIfNotAccessible (paddr pd, paddr idblock, bool accessiblebit); //! Removes a block from the physical MPU if not accessible.
void replaceBlockInPhysicalMPU(paddr pd, paddr blockblockentryaddr, uint32_t MPURegionNb); //! Replaces a block in the physical MPU.
uint32_t findBlockIdxInPhysicalMPU(paddr pd, paddr blockToFind, uint32_t defaultnb); //! Returns the MPU region number where the block is configured

void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr blockentryaddr, paddr addrtocover); //! Configures the LUT entry at given index with the given MPU entry
void clear_LUT(uint32_t* LUT); //! Defaults all LUT entries
int checkMPU(); //! Checks the MPU
int initMPU(); //! Inits the MPU
#endif
