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

#include <stdbool.h>
#include <stddef.h>


/* Activate : deprecated */
void activate(paddr dir);

/* Current page directory */
paddr getCurPartition(void); //!< Interface to get the current Page Directory
void updateCurPartition (paddr descriptor);

paddr getRootPartition(void); //!< Interface to get the current Page Directory
void updateRootPartition (paddr descriptor);

//uint32_t defaultAddr(void); //!< Default address, should be 0x00000000
//extern const uint32_t defaultVAddr; //!< Default address, should be 0x00000000
uint32_t getTableSize(void); //!< Table size
uint32_t getMaxIndex(void); //!< Table size
uint32_t addressEquals(uint32_t addr, uint32_t addr2); //!< Checks whether an address is equal to another.
void cleanPage(uint32_t paddr); //!< Cleans a given page, filling it with zero

uint32_t checkRights(uint32_t read, uint32_t write, uint32_t execute); //!< Checks whether the asked rights are applicable to the architecture or not
uint32_t applyRights(uint32_t table, uint32_t index, uint32_t read, uint32_t write, uint32_t execute); //!< Apply the asked rights to the given entry

uint32_t toAddr(uint32_t input); //!< Converts a given uint32_t to an address (only for Haskell FFI purposes)
//extern const uint32_t nbLevel;

/* Amount of pages available, meh */
/*extern uint32_t maxPages;
#define nbPage maxPages*/

/* Coq related stuff */
int geb(const uint32_t a, const uint32_t b); //!< Greater or equal
int gtb(const uint32_t a, const uint32_t b); //!< Greater than
int leb(const uint32_t a, const uint32_t b); //!< Lower or equal
int ltb(const uint32_t a, const uint32_t b); //!< Lower than
int eqb(const uint32_t a, const uint32_t b); //!< Equals
uint32_t mul3(uint32_t v); //!< Multiply an integer with 3
uint32_t inc(uint32_t val); //!< Increment an integer
uint32_t dec(uint32_t val); //!< Decrement an integer
uint32_t zero(); //!< Zero. That's it.


/*uint32_t indexPR(void); //!< Partiton descriptor index into itself
uint32_t indexPD(void); //!< Page directory index within partition descriptor
uint32_t indexSh1(void); //!< Shadow 1 index within partition descriptor
uint32_t indexSh2(void); //!< Shadow 2 index within partition descriptor
uint32_t indexSh3(void); //!< Configuration tables linked list index within partition descriptor
uint32_t PPRidx(void); //!< Parent partition index within partition descriptor
uint32_t kernelIndex(void); //!< Index of kernel's page directory entry
void writePhysicalWithLotsOfFlags(uint32_t table, uint32_t index, uint32_t addr, uint32_t present, uint32_t user, uint32_t read, uint32_t write, uint32_t execute); //!< Write a physical entry with all the possible flags we might need
void writeKPhysicalWithLotsOfFlags(uint32_t table, uint32_t index, uint32_t addr, uint32_t present, uint32_t user, uint32_t read, uint32_t write, uint32_t execute); //!< Write a physical entry with all the possible flags we might need
uint32_t extractPreIndex(uint32_t vaddr, uint32_t index);*/
void mal_init(void);

/* ARM */
/* MALInternal */
uint32_t mul(uint32_t a, uint32_t b); //!< Multiply two integers
uint32_t sub(uint32_t a, uint32_t b); //!< Substract two integers
uint32_t add(uint32_t a, uint32_t b); //!< Add two integers

extern uint32_t kernelstructureentriesnb;
uint32_t KERNELSTRUCTUREENTRIESNB(void); //!< The number of entries in a kernel structure
uint32_t MAXNBPREPARE(void);//!< The maximum number of times a partition can be prepared.
uint32_t KERNELSTRUCTURETOTALLENGTH(void);
uint32_t PDSTRUCTURETOTALLENGTH(void);
extern uint32_t min_mpu_region;
uint32_t MINBLOCKSIZE(void);

extern uint32_t mpuentrylength;
extern uint32_t sh1entrylength;
extern uint32_t scentrylength;
uint32_t MPUENTRYLENGTH(void); //!< The MPU entry size.
uint32_t SH1ENTRYLENGTH(void); //!< The shadow 1 entry size.
uint32_t SCENTRYLENGTH(void); //!< The shadow cut entry size.

extern uint32_t mpuoffset;
extern uint32_t sh1offset;
extern uint32_t scoffset;
extern uint32_t nextoffset;
uint32_t MPUOFFSET(void); //!< The MPU structure offset.
uint32_t SH1OFFSET(void); //!< The Shadow 1 structure offset.
uint32_t SCOFFSET(void); //!< The Shadow Cut structure offset.
uint32_t NEXTOFFSET(void); //!< The next structure pointer offset.

paddr getKernelStructureStartAddr(paddr mpuentryaddr, uint32_t mpuentryindex); //!< The start of the kernel structure frame
paddr getMPUEntryAddrFromKernelStructureStart(paddr mpuentryaddr, uint32_t mpuentryindex); //!< The address of the MPU entry
paddr getSh1EntryAddrFromKernelStructureStart(paddr mpuentryaddr, uint32_t mpuentryindex); //!< The address of the shadow 1 entry
paddr getSCEntryAddrFromKernelStructureStart(paddr mpuentryaddr, uint32_t mpuentryindex); //!< The address of the shadow cut entry
paddr* getNextAddrFromKernelStructureStart(paddr kernelstartaddr); //!< The address of the next structure pointer
uint32_t fit_mpu_region(uint32_t block_size);
uint32_t next_pow2(uint32_t v);
uint32_t powlog2(uint32_t v);

paddr getNullAddr(void); //!< Returns the default null address.
bool beqAddr(paddr a, paddr b); //!< Compare two addresses
bool beqIdx(uint32_t a, uint32_t b); //!< Compare two indexes
paddr addPaddrIdx(paddr a, uint32_t b); //!< adds an offset to a paddr
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
void eraseAddr(paddr addr); //! Sets the address to NULL
bool eraseBlock (paddr startAddr, paddr endAddr); //! Erases the memory block defined by (startAddr, endAddr).
void writePDTable(paddr addr, PDTable_t newpdtable); //! Sets a new PD Table at the given address
PDTable_t getDefaultPDTable(); //! Returns the default PD Table without initialisation
PDTable_t getEmptyPDTable(); //! Returns the default PD Table with initialisation
MPUEntry_t getDefaultMPUEntry(); //! Returns the default MPU entry
Sh1Entry_t getDefaultSh1Entry(); //! Returns the default Sh1 entry
SCEntry_t getDefaultSCEntry(); //! Returns the default SC entry
MPUEntry_t buildMPUEntry(paddr startaddr, paddr endaddr, bool accessiblebit, bool presentbit); //! Constructs an MPU entry given the attributes
paddr getPDStructurePointerAddrFromPD(paddr pdaddr); //! Gets the structure pointer of the given PD

void removeBlockFromPhysicalMPUIfNotAccessible (paddr pd, paddr idblock, bool accessiblebit); //! Removes a block from the physical MPU.

void configure_LUT_entry(uint32_t* LUT, uint32_t entryindex, paddr mpuentryaddr); //! Configures the LUT entry at given index with the given MPU entry
void clear_LUT_entry(uint32_t* LUT, uint32_t entryindex); //! Defaults the LUT entry at the given index
void clear_LUT(uint32_t* LUT); //! Defaults all LUT entries
int checkMPU(); //! Checks the MPU
#endif
