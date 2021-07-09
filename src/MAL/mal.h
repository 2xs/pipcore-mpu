/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2018)                 */
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

bool compatibleRight(bool originalright, bool newright); //!< Checks the compatibility of a right to another
bool checkRights(paddr originalmpuentryaddr, bool read, bool write, bool exec); //!< Checks whether the asked rights are compatible with the original block

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

paddr getKernelStructureStartAddr(paddr mpuentryaddr, uint32_t mpuentryindex); //!< The start of the kernel structure frame
paddr getMPUEntryAddrFromKernelStructureStart(paddr mpuentryaddr, uint32_t mpuentryindex); //!< The address of the MPU entry
paddr getSh1EntryAddrFromKernelStructureStart(paddr mpuentryaddr, uint32_t mpuentryindex); //!< The address of the shadow 1 entry
paddr getSCEntryAddrFromKernelStructureStart(paddr mpuentryaddr, uint32_t mpuentryindex); //!< The address of the shadow cut entry
paddr getNextAddrFromKernelStructureStart(paddr structureaddr); //!< The address of the next pointer
uint32_t fit_mpu_region(uint32_t block_size);
uint32_t next_pow2(uint32_t v);
uint32_t powlog2(uint32_t v);

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
paddr readMPUStartFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the block's start address from the given entry
void writeMPUStartFromMPUEntryAddr(paddr mpuentryaddr, paddr value); //!< Sets the block's start address
paddr readMPUEndFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the block's end address from the given entry
void writeMPUEndFromMPUEntryAddr(paddr mpuentryaddr, paddr value); //!< Sets the block's end address
bool readMPUAccessibleFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the Accessible flag from the given entry
void writeMPUAccessibleFromMPUEntryAddr(paddr mpuentryaddr, bool value); //!< Sets a memory block as accessible or not
bool readMPUPresentFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the Present flag from the given entry
void writeMPUPresentFromMPUEntryAddr(paddr mpuentryaddr, bool value); //!< Sets a memory block as present or not
uint32_t readMPUIndexFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the MPU index from the given entry
void writeMPUIndexFromMPUEntryAddr(paddr mpuentryaddr, uint32_t value); //!< Sets the MPU index
bool readMPURFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the read flag
void writeMPURFromMPUEntryAddr(paddr mpuentryaddr, bool value); //!< Sets the read flag
bool readMPUWFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the write flag
void writeMPUWFromMPUEntryAddr(paddr mpuentryaddr, bool value); //!< Sets the write flag
bool readMPUXFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the exec flag
void writeMPUXFromMPUEntryAddr(paddr mpuentryaddr, bool value); //!< Sets the exec flag
MPUEntry_t readMPUEntryFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the MPU entry
void writeMPUEntryFromMPUEntryAddr(paddr mpuentryaddr, MPUEntry_t value); //!< Sets the MPU entry
void writeMPUEntryWithIndexFromMPUEntryAddr(paddr mpuentryaddr, uint32_t index, MPUEntry_t value); //!< Sets the MPU entry with given index
paddr getSh1EntryAddrFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the Sh1 entry from the MPU entry
paddr readSh1PDChildFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the child's PD from the given entry
void writeSh1PDChildFromMPUEntryAddr(paddr mpuentryaddr, paddr value); //!< Sets the entry's child PD
bool readSh1PDFlagFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the child's PD from the given entry
void writeSh1PDFlagFromMPUEntryAddr(paddr mpuentryaddr, bool value); //!< Sets the entry's PD flag
paddr readSh1InChildLocationFromMPUEntryAddr(paddr mpuentryaddr); //!< Gets the location of the block in the child
void writeSh1InChildLocationFromMPUEntryAddr(paddr mpuentryaddr, paddr value); //!<Sets the block's location in the child
void writeSh1EntryFromMPUEntryAddr(paddr mpuentryaddr, Sh1Entry_t newsh1entry);//! Sets the block's Sh1 entry
paddr getSCEntryAddrFromMPUEntryAddr(paddr mpuentryaddr); //! Gets the SC entry from the MPU entry
paddr readSCOriginFromMPUEntryAddr(paddr mpuentryaddr); //! Gets the block's origin
void writeSCOriginFromMPUEntryAddr(paddr mpuentryaddr, paddr value); //! Sets the block's origin
paddr readSCNextFromMPUEntryAddr(paddr mpuentryaddr); //! Gets the block's next subblock
void writeSCNextFromMPUEntryAddr(paddr mpuentryaddr, paddr value); //! Sets the block's next subblock
void writeSCEntryFromMPUEntryAddr(paddr mpuentryaddr, SCEntry_t newscentry); //! Sets the block's SC entry
paddr readNextFromKernelStructureStart(paddr structureaddr); //! Gets the block's next subblock
void writeNextFromKernelStructureStart(paddr structureaddr, paddr newnextstructure); //! Sets the block's SC entry
void eraseAddr(uint8_t* addr); //! Sets the address to NULL
bool eraseBlock (paddr startAddr, paddr endAddr); //! Erases the memory block defined by (startAddr, endAddr).
void writePDTable(paddr addr, PDTable_t newpdtable); //! Sets a new PD Table at the given address
PDTable_t getDefaultPDTable(); //! Returns the default PD Table without initialisation
PDTable_t getEmptyPDTable(); //! Returns the default PD Table with initialisation
MPUEntry_t getDefaultMPUEntry(); //! Returns the default MPU entry
Sh1Entry_t getDefaultSh1Entry(); //! Returns the default Sh1 entry
SCEntry_t getDefaultSCEntry(); //! Returns the default SC entry
MPUEntry_t buildMPUEntry(paddr startaddr, paddr endaddr, bool accessiblebit, bool presentbit); //! Constructs an MPU entry given the attributes
paddr getPDStructurePointerAddrFromPD(paddr pdaddr); //! Gets the structure pointer of the given PD
bool checkEntry(paddr kstructurestart, paddr mpuentryaddr); //! Checks an MPU entry is valid in the kernel structure
blockOrError blockAttr(paddr mpuentryaddr, MPUEntry_t mpuentry); //! Wrapper to create a block and its attributes

paddr readBlockFromPhysicalMPU(paddr pd, uint32_t MPURegionNb);  //! Reads the block configured at the given region of the physical MPU.
void removeBlockFromPhysicalMPU(paddr pd, paddr mpuentryaddr); //! Removes a block from the physical MPU.
void removeBlockFromPhysicalMPUIfNotAccessible (paddr pd, paddr idblock, bool accessiblebit); //! Removes a block from the physical MPU if not accessible.
void replaceBlockInPhysicalMPU(paddr pd, paddr blockmpuentryaddr, uint32_t MPURegionNb); //! Replaces a block in the physical MPU.

void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr mpuentryaddr); //! Configures the LUT entry at given index with the given MPU entry
void clear_LUT(uint32_t* LUT); //! Defaults all LUT entries
int checkMPU(); //! Checks the MPU
int initMPU(); //! Inits the MPU
#endif
