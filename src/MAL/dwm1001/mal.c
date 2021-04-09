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
 * \file mal.c
 * \brief ARM memory abstraction layer
 */

#include <stdint.h>
#include "mal.h"
#include <stddef.h>
//#include "debug.h"

/*#ifdef DEBUG_MAL
#define MALDBG(fmt,...) DEBUG(ERROR, fmt, ##__VA_ARGS__)
#else
#define MALDBG(...)
#endif*/
#include <stdio.h>

paddr current_partition = NULL; /* Current partition, default root */
paddr root_partition = NULL; /* Multiplexer's partition descriptor, default 0*/

static const PDTable_t DEFAULT_PD_TABLE = {NULL, NULL, 0, 0, NULL};
static const block_t DEFAULT_BLOCK = {0, 0};
static const MPUIndex_t DEFAULT_MPU_INDEX = {-1};
static const MPUEntry_t DEFAULT_MPU_ENTRY = {DEFAULT_BLOCK, DEFAULT_MPU_INDEX, false, false, false, false, false};
static const Sh1Entry_t DEFAULT_SH1_ENTRY = {NULL, false, NULL};
static const SCEntry_t DEFAULT_SC_ENTRY = {NULL, NULL};

/*!
 * \fn PDTable_t readPDTable(paddr pdaddr)
 * \brief Gets the Partition Descriptor (PD).
 * \param pdaddr The address where to find PD
 * \return the PD table
 */
PDTable_t readPDTable(paddr pdaddr)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr; // TODO: Exception ? Only called with current partition

	// Return the pd table
	return *pd;
}

/*!
 * \fn paddr* readPDStructurePointer(paddr pdaddr)
 * \brief Gets the first kernel structure.
 * \param pdaddr The address of the PD
 * \return the pointer to the first kernel structure
 */
paddr readPDStructurePointer(paddr pdaddr)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr; // TODO: Exception ? Only called with current partition

	//MALDBG("readPDStructurePointer(%d) -> %d\r\n", pdaddr, pd);
	printf("readPDStructurePointer(%d) -> %d\r\n", pdaddr, pd);

	// Return the pointer to the first kernel structure
	return pd->structure;
}

/*!
 * \fn void writePDStructurePointer(paddr pdaddr, paddr value)
 * \brief Sets the first kernel structure.
 * \param pdaddr The address of the PD
 * \param value The new value
 * \return void
 */
void writePDStructurePointer(paddr pdaddr, paddr value)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr;

	// write the structure pointer
	pd->structure = value;
	return;
}

/*!
 * \fn paddr readPDFirstFreeSlotPointer(paddr pdaddr)
 * \brief Gets the first free slot's address
 * \param pdaddr The address of the PD
 * \return the pointer to the first free slot
 */
paddr readPDFirstFreeSlotPointer(paddr pdaddr)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr; // TODO: Exception ? Only called with current partition

	// Return the pointer to the first free slot
	return pd->firstfreeslot;
}

/*!
 * \fn void writePDFirstFreeSlotPointer(paddr pdaddr, paddr value)
 * \brief Sets the first free slot's address.
 * \param pdaddr The address of the PD
 * \param value The new value
 * \return void
 */
void writePDFirstFreeSlotPointer(paddr pdaddr, paddr value)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr;

	// write the first free slot pointer
	pd->firstfreeslot = value;
	return;
}

/*!
 * \fn uint32_t readPDNbFreeSlots(paddr pdaddr)
 * \brief Gets the number of free slots left.
 * \param pdaddr The address of the PD
 * \return the number of free slots left
 */
uint32_t readPDNbFreeSlots(paddr pdaddr)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr;

	// Return the number of free slots left
	return pd->nbfreeslots;
}

/*!
 * \fn void writePDNbFreeSlots(paddr pdaddr, uint32_t value)
 * \brief Sets the number of free slots left.
 * \param pdaddr The address of the PD
 * \param value The new value
 * \return void
 */
void writePDNbFreeSlots(paddr pdaddr, uint32_t value)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr;

	// write the number of free slots left
	pd->nbfreeslots = value;
	return;
}

/*!
 * \fn uint32_t readPDNbPrepare(paddr pdaddr)
 * \brief Gets the number of prepare done util then.
 * \param pdaddr The address of the PD
 * \return the number of prepare
 */
uint32_t readPDNbPrepare(paddr pdaddr)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr;

	// Return the number of prepare
	return pd->nbprepare;
}

/*!
 * \fn void writePDNbPrepare(paddr pdaddr, uint32_t value)
 * \brief Sets the number of prepare done util then.
 * \param pdaddr The address of the PD
 * \param value The new value
 * \return void
 */
void writePDNbPrepare(paddr pdaddr, uint32_t value)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr;

	// write the number of prepare
	pd->nbprepare = value;
	return;
}

/*!
 * \fn paddr readPDParent(paddr pdaddr)
 * \brief Gets the parent PD's address.
 * \param pdaddr The address of the PD
 * \return the pointer to the parent
 */
paddr readPDParent(paddr pdaddr)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr;

	// Return the parent
	return pd->parent;
}

/*!
 * \fn void writePDParent(paddr pdaddr, paddr value)
 * \brief Sets the parent PD's address.
 * \param pdaddr The address of the PD
 * \param value The new value
 * \return void
 */
void writePDParent(paddr pdaddr, paddr value)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pd = (PDTable_t*)pdaddr;

	// write the number of prepare
	pd->parent = value;
	return;
}

/*!
 * \fn paddr readMPUStartFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the block's start address from the given entry.
 * \param mpuentryaddr The address of the MPU entry to read from
 * \return the block's start address
 */
paddr readMPUStartFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// Return the start address
	return (mpuentry->mpublock).startAddr;
}

/*!
 * \fn void writeMPUStartFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
 * \brief Sets the block's start address.
 * \param mpuentryaddr The address of the MPU entry to write in
 * \param value The new value
 * \return void
 */
void writeMPUStartFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// write the block's start address
	(mpuentry->mpublock).startAddr = value;
	return;
}

/*!
 * \fn paddr readMPUEndFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the block's end address from the given entry.
 * \param mpuentryaddr The address of the MPU entry to read from
 * \return the block's end address
 */
paddr readMPUEndFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// Return the end address
	return (mpuentry->mpublock).endAddr;
}

/*!
 * \fn void writeMPUEndFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
 * \brief Sets the block's end address.
 * \param mpuentryaddr The address of the MPU entry to write in
 * \param value The new value
 * \return void
 */
void writeMPUEndFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// write the block's end address
	(mpuentry->mpublock).endAddr = value;
	return;
}

/*!
 * \fn bool readMPUAccessibleFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the Accessible flag from the given entry.
 * \param mpuentryaddr The address of the MPU entry to read from
 * \return 1 if the page is user-mode accessible, 0 else
 */
bool readMPUAccessibleFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	//MALDBG("readMPUAccessibleFromMPUEntryAddr(%d) -> %d\r\n", mpuentryaddr, mpuentry->accessible);
	printf("readMPUAccessibleFromMPUEntryAddr(%d) -> %d\r\n", mpuentryaddr, mpuentry->accessible);

	// Return the accessible flag
	return mpuentry->accessible;
}

/*!
 * \fn void writeMPUAccessibleFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Sets a memory block as accessible or not.
 * \param mpuentryaddr The address of the MPU entry to write in
 * \param value The new value
 * \return void
 */
void writeMPUAccessibleFromMPUEntryAddr(paddr mpuentryaddr, bool value)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// write the flag
	mpuentry->accessible = value;
	return;
}

/*!
 * \fn bool readMPUPresentFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the Present flag from the given entry.
 * \param mpuentryaddr The address of the MPU entry to read from
 * \return 1 if the page is present, 0 else
 */
bool readMPUPresentFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	//MALDBG("readMPUPresentFromMPUEntryAddr(%d) -> %d\r\n", mpuentryaddr, mpuentry->present);
	printf("readMPUPresentFromMPUEntryAddr(%d) -> %d\r\n", mpuentryaddr, mpuentry->present);

	// Return the present flag
	return mpuentry->present;
}

/*!
 * \fn void writeMPUPresentFromMPUEntryAddr(paddr mpuentryaddr, bool value)
 * \brief Sets a memory block as present or not.
 * \param mpuentryaddr The address of the MPU entry to write in
 * \param value The new value
 * \return void
 */
void writeMPUPresentFromMPUEntryAddr(paddr mpuentryaddr, bool value)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// write the flag
	mpuentry->present = value;
	return;
}

/*!
 * \fn uint32_t readMPUIndexFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the MPU index from the given entry.
 * \param mpuentryaddr The address of the MPU entry to read from
 * \return the MPU index
 */
uint32_t readMPUIndexFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// Return the MPU index
	return (uint32_t) (mpuentry->mpuindex).MPUi;
}

/*!
 * \fn void writeMPUIndexFromMPUEntryAddr(paddr mpuentryaddr, uint32_t value)
 * \brief Sets the MPU index.
 * \param mpuentryaddr The address of the MPU entry to write in
 * \param value The new value
 * \return void
 */
void writeMPUIndexFromMPUEntryAddr(paddr mpuentryaddr, uint32_t value)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// write the MPU index
	(mpuentry->mpuindex).MPUi = value;
	return;
}

/*!
 * \fn void writeMPUEntryFromMPUEntryAddr(paddr mpuentryaddr, MPUEntry_t value)
 * \brief Sets the MPU entry.
 * \param mpuentryaddr The address of the MPU entry to write in
 * \param value The new value
 * \return void
 */
void writeMPUEntryFromMPUEntryAddr(paddr mpuentryaddr, MPUEntry_t value)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// write the MPU entry
	*mpuentry = value;
	return;
}

/*!
 * \fn void writeMPUEntryWithIndexFromMPUEntryAddr(paddr mpuentryaddr, uint32_t index, MPUEntry_t value)
 * \brief Sets the MPU entry with given index.
 * \param mpuentryaddr The address of the MPU entry to write in
 * \param value The new value
 * \param index The index to set
 * \return void
 */
void writeMPUEntryWithIndexFromMPUEntryAddr(paddr mpuentryaddr, uint32_t index, MPUEntry_t value)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	// write the MPU entry
	(value.mpuindex).MPUi = index;
	*mpuentry = value;
	return;
}

/*!
 * \fn paddr getSh1EntryAddrFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the Sh1 entry from the MPU entry.
 * \param mpuentryaddr The address of the reference MPU entry
 * \return the corresponding SH1 entry address to the given MPU entry
 */
paddr getSh1EntryAddrFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	uint32_t entryindex = (mpuentry->mpuindex).MPUi;// TODO protect from NULL access ?

	paddr kernelStartAddr = getKernelStructureStartAddr(mpuentryaddr, entryindex);

	// Return the SH1 entry address
	return getSh1EntryAddrFromKernelStructureStart(kernelStartAddr, entryindex);
}

/*!
 * \fn paddr readSh1PDChildFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the child's PD from the given entry.
 * \param mpuentryaddr The address of the reference MPU entry
 * \return the child PD if shared, NULL otherwise
 */
paddr readSh1PDChildFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Get the corresponding Sh1 entry addres
	paddr sh1entryaddr = getSh1EntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a Sh1Entry_t structure
	Sh1Entry_t* sh1entry = (Sh1Entry_t*)sh1entryaddr;

	// Return the child PD
	return sh1entry->PDchild;
}

/*!
 * \fn void writeSh1PDChildFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
 * \brief Sets the entry's child PD.
 * \param mpuentryaddr The address of the reference MPU entry
 * \param value The new value
 * \return void
 */
void writeSh1PDChildFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
{
	// Get the corresponding Sh1 entry addres
	paddr sh1entryaddr = getSh1EntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a Sh1Entry_t structure
	Sh1Entry_t* sh1entry = (Sh1Entry_t*)sh1entryaddr;

	// write the child PD
	sh1entry->PDchild = value;
	return;
}

/*!
 * \fn bool readSh1PDFlagFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the child's PD from the given entry.
 * \param mpuentryaddr The address of the reference MPU entry
 * \return 1 if child is PD, NULL otherwise
 */
bool readSh1PDFlagFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Get the corresponding Sh1 entry addres
	paddr sh1entryaddr = getSh1EntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a Sh1Entry_t structure
	Sh1Entry_t* sh1entry = (Sh1Entry_t*)sh1entryaddr;

	// Return the PD flag
	return sh1entry->PDflag;
}

/*!
 * \fn void writeSh1PDFlagFromMPUEntryAddr(paddr mpuentryaddr, bool value)
 * \brief Sets the entry's PD flag.
 * \param mpuentryaddr The address of the reference MPU entry
 * \param value The new value
 * \return void
 */
void writeSh1PDFlagFromMPUEntryAddr(paddr mpuentryaddr, bool value)
{
	// Get the corresponding Sh1 entry addres
	paddr sh1entryaddr = getSh1EntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a Sh1Entry_t structure
	Sh1Entry_t* sh1entry = (Sh1Entry_t*)sh1entryaddr;

	// write the flag
	sh1entry->PDflag = value;
	return;
}

/*!
 * \fn paddr readSh1InChildLocationFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the location of the block in the child.
 * \param mpuentryaddr The address of the reference MPU entry
 * \return the location of the block in the child if shared, NULL otherwise
 */
paddr readSh1InChildLocationFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Get the corresponding Sh1 entry addres
	paddr sh1entryaddr = getSh1EntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a Sh1Entry_t structure
	Sh1Entry_t* sh1entry = (Sh1Entry_t*)sh1entryaddr;

	// Return the location in the child
	return sh1entry->inChildLocation;
}

/*!
 * \fn void writeSh1InChildLocationFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
 * \brief Sets the block's location in the child.
 * \param mpuentryaddr The address of the reference MPU entry
 * \param value The new value
 * \return void
 */
void writeSh1InChildLocationFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
{
	// Get the corresponding Sh1 entry addres
	paddr sh1entryaddr = getSh1EntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a Sh1Entry_t structure
	Sh1Entry_t* sh1entry = (Sh1Entry_t*)sh1entryaddr;

	// write the block's location in the child
	sh1entry->inChildLocation = value;
	return;
}

/*!
 * \fn void writeSh1EntryFromMPUEntryAddr(paddr mpuentryaddr, Sh1Entry_t newsh1entry)
 * \brief Sets the block's SH1 entry.
 * \param mpuentryaddr The address of the reference MPU entry
 * \param newsh1entry The new Sh1 entry
 * \return void
 */
void writeSh1EntryFromMPUEntryAddr(paddr mpuentryaddr, Sh1Entry_t newsh1entry)
{
	writeSh1PDChildFromMPUEntryAddr(mpuentryaddr, newsh1entry.PDchild);
	writeSh1PDFlagFromMPUEntryAddr(mpuentryaddr, newsh1entry.PDflag);
	writeSh1InChildLocationFromMPUEntryAddr(mpuentryaddr, newsh1entry.inChildLocation);

	return;
}

/*!
 * \fn paddr getSCEntryAddrFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the SC entry from the MPU entry.
 * \param mpuentryaddr The address of the reference MPU entry
 * \return the corresponding SC entry address to the given MPU entry
 */
paddr getSCEntryAddrFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Cast it into a MPUEntry_t structure
	MPUEntry_t* mpuentry = (MPUEntry_t*)mpuentryaddr;

	uint32_t entryindex = (mpuentry->mpuindex).MPUi;// TODO protect from NULL access ?

	paddr kernelStartAddr = getKernelStructureStartAddr(mpuentryaddr, entryindex);

	// Return the SC entry address
	return getSCEntryAddrFromKernelStructureStart(kernelStartAddr, entryindex);
}

/*!
 * \fn paddr readSCOriginFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the block's origin.
 * \param mpuentryaddr The address of the reference MPU entry
 * \return the block origin if block is present, NULL otherwise
 */
paddr readSCOriginFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Get the corresponding SC entry addres
	paddr scentryaddr = getSCEntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a SCEntry_t structure
	SCEntry_t* scentry = (SCEntry_t*)scentryaddr;

	// Return the block's origin
	return scentry->origin;
}

/*!
 * \fn void writeSCOriginFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
 * \brief Sets the block's origin.
 * \param mpuentryaddr The address of the reference MPU entry
 * \param value The new value
 * \return void
 */
void writeSCOriginFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
{
	// Get the corresponding SC entry addres
	paddr scentryaddr = getSCEntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a SCEntry_t structure
	SCEntry_t* scentry = (SCEntry_t*)scentryaddr;

	// write the block's origin
	scentry->origin = value;
	return;
}

/*!
 * \fn paddr readSCNextFromMPUEntryAddr(paddr mpuentryaddr)
 * \brief Gets the block's next subblock.
 * \param mpuentryaddr The address of the reference MPU entry
 * \return the block origin if block is present, NULL otherwise
 */
paddr readSCNextFromMPUEntryAddr(paddr mpuentryaddr)
{
	// Get the corresponding SC entry addres
	paddr scentryaddr = getSCEntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a SCEntry_t structure
	SCEntry_t* scentry = (SCEntry_t*)scentryaddr;

	// Return the block's next subblock
	return scentry->next;
}

/*!
 * \fn void writeSCNextFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
 * \brief Sets the block's next subblock.
 * \param mpuentryaddr The address of the reference MPU entry
 * \param value The new value
 * \return void
 */
void writeSCNextFromMPUEntryAddr(paddr mpuentryaddr, paddr value)
{
	// Get the corresponding SC entry addres
	paddr scentryaddr = getSCEntryAddrFromMPUEntryAddr(mpuentryaddr);

	// Cast it into a SCEntry_t structure
	SCEntry_t* scentry = (SCEntry_t*)scentryaddr;

	// write the block's next subblock
	scentry->next = value;
	return;
}

/*!
 * \fn void writeSCEntryFromMPUEntryAddr(paddr mpuentryaddr, SCEntry_t newscentry)
 * \brief Sets the block's SC entry.
 * \param mpuentryaddr The address of the reference MPU entry
 * \param newscentry The new SC entry
 * \return void
 */
void writeSCEntryFromMPUEntryAddr(paddr mpuentryaddr, SCEntry_t newscentry)
{
	writeSCOriginFromMPUEntryAddr(mpuentryaddr, newscentry.origin);
	writeSCNextFromMPUEntryAddr(mpuentryaddr, newscentry.next);

	return;
}

/*!
 * \fn paddr readNextFromKernelStructureStart(paddr structureaddr)
 * \brief Gets the block's next subblock.
 * \param mpuentryaddr The address of the kernel structure
 * \return the pointer to the next structure, NULL otherwise
 */
paddr readNextFromKernelStructureStart(paddr structureaddr)
{
	// Get the structure next entry address
	paddr nextstructureaddr = getNextAddrFromKernelStructureStart(structureaddr);

	//MALDBG("readNextFromKernelStructureStart(%d) -> %d\r\n", structureaddr, nextstructureaddr);
	printf("readNextFromKernelStructureStart(%d) -> %d\r\n", structureaddr, nextstructureaddr);

	// Return the pointer to the next structure
	return nextstructureaddr;
}

/*!
 * \fn void writeNextFromKernelStructureStart(paddr structureaddr, paddr newnextstructure)
 * \brief Sets the block's SC entry.
 * \param structureaddr The address of the kernel structure
 * \param newnextstructure The new next structure pointer
 * \return void
 */
void writeNextFromKernelStructureStart(paddr structureaddr, paddr newnextstructure)
{
	// Get the structure next entry address
	paddr nextstructureaddr = getNextAddrFromKernelStructureStart(structureaddr);

	*nextstructureaddr = newnextstructure;

	return;
}


/*!
 * \fn void eraseAddr(paddr addr)
 * \brief Sets the address to NULL.
 * \param addr The address of the reference MPU entry
 * \return void
 */
void eraseAddr(paddr addr)
{
	*addr = NULL;

	return;
}

/*!
 * \fn void writePDTable(paddr addr, PDTable_t newpdtable)
 * \brief Sets a new PD Table at the given address.
 * \param addr The address where to set the PD Table
 * \param newpdtable The new PD Table
 * \return void
 */
void writePDTable(paddr addr, PDTable_t newpdtable)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pdtable = (PDTable_t*)addr;
	*pdtable = newpdtable;

	return;
}

/*!
 * \fn PDTable_t getEmptyPDTable()
 * \brief Returns the default PD Table.
 * \return default PD Table
 */
PDTable_t getEmptyPDTable()
{
	//DEFAULT_PD_TABLE(emptyPD);
	//return emptyPD;
	return DEFAULT_PD_TABLE;
}

/*!
 * \fn MPUEntry_t getDefaultMPUEntry()
 * \brief Returns the default MPU entry.
 * \return default MPU entry
 */
MPUEntry_t getDefaultMPUEntry()
{
	//DEFAULT_MPU_ENTRY(emptyMPUE);
	//return emptyMPUE;
	return DEFAULT_MPU_ENTRY;
}

/*!
 * \fn Sh1Entry_t getDefaultSh1Entry()
 * \brief Returns the default Sh1 entry.
 * \return default Sh1 entry
 */
Sh1Entry_t getDefaultSh1Entry()
{
	//DEFAULT_SH1_ENTRY(emptySH1E);
	//return emptySH1E;
	return DEFAULT_SH1_ENTRY;
}

/*!
 * \fn SCEntry_t getDefaultSCEntry()
 * \brief Returns the default SC entry.
 * \return default SC entry
 */
SCEntry_t getDefaultSCEntry()
{
	//DEFAULT_SC_ENTRY(emptySCE);
	//return emptySCE;
	return DEFAULT_SC_ENTRY;
}

/*!
 * \fn MPUEntry_t buildMPUEntry(startaddr, endaddr, accessiblebit, presentbit)
 * \brief Constructs an MPU entry given the attributes.
 * \param startaddr The block's start address
 * \param endaddr The block's end address
 * \param endaddr The block's end address
 * \param accessiblebit The block's accessible bit
 * \param presentbit The block's present bit
 * \return default SC entry
 */
MPUEntry_t buildMPUEntry(paddr startaddr, paddr endaddr, bool accessiblebit, bool presentbit)
{
	//DEFAULT_MPU_ENTRY(MPUE);
	MPUEntry_t MPUE = DEFAULT_MPU_ENTRY;
	block_t block = {startaddr, endaddr};
	MPUE.mpublock = block;
	MPUE.accessible = accessiblebit;
	MPUE.present = presentbit;
	return MPUE;
}

/*!
 * \fn paddr getPDStructurePointerAddrFromPD(paddr pdaddr)
 * \brief Gets the structure pointer of the given PD.
 * \param pdaddr The PD where to find the structure pointer
 * \return the kernel structure pointer if exists, otherwise NULL
 */
paddr getPDStructurePointerAddrFromPD(paddr pdaddr)
{
	// Cast it into a PDTable_t structure
	PDTable_t* pdtable = (PDTable_t*)pdaddr;
	return &(pdtable->structure);
}

/*! \fn paddr getCurPartition()
 	\brief get the current page directory
	\return the current page directory
 */
paddr getCurPartition(void)
{
	return current_partition;
}

/*! \fn void updateCurPartition()
 \brief Set current partition paddr
 \param partition Current partition paddr
 */
void
updateCurPartition (paddr descriptor)
{
	current_partition = descriptor;
	//DEBUG(TRACE, "Registered partition descriptor %x.\n", descriptor);
	printf("DEBUG: Registered partition descriptor %x.\n", descriptor);
}

/*! \fn paddr getRootPartition()
 \brief get the root partition
	\return the root partition
 */
paddr getRootPartition(void)
{
	return root_partition;
}

/*! \fn paddr updateRootPartition(paddr partition)
 \brief Set new root partition
 \param partition Root partition
 */
void
updateRootPartition(paddr partition)
{
	root_partition = partition;
}

/*!
 * \fn uint32_t checkRights(uint32_t read, uint32_t write, uint32_t execute)
 * \param read The read right
 * \param write The write right
 * \param execute The execute right
 * \brief Checks whether we can apply the given rights on the target architecture
 * \return 1 if we can, 0 if we can't
 */
uint32_t checkRights(uint32_t read, uint32_t write, uint32_t execute)
{
	// Read has to be 1 (only user/kernel in x86)
	if(read==0)
		return 0;

	// No XD bit on i386
	if(execute==0)
		return 0;

	// Well the complier will complain about a unused parameter thing so...
	if(write==0 || write == 1)
		return 1;
	else return 0;
}

/* activate:
 * switch to given partition address space
 * the partition must already be validated */
void activate(paddr desc)
{
	if (desc == getCurPartition())
	{
		//DEBUG(TRACE, "activate %08x\r\n", desc);
		//enable_paging();
		printf("DEBUG: activate %08x\r\n", desc);
		return;
	}
	//DEBUG(TRACE, "activate %08x: activating\r\n", desc);
	printf("DEBUG: activate %08x: activating\r\n", desc);

	/* switch to partition va */
	/*activate_s(mmu_make_ttbr(
		((void**)desc)[getPDidx()+1],// Translation Table
		RGN_NOCACHE,	// FIXME: No cache
		RGN_NOCACHE,	// FIXME: No cache
		0, 1					// Non shareable
	));*/

	updateCurPartition(desc);
}
