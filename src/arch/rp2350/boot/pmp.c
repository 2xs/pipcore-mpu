/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2025)                */
/*  Copyright (C) 2020-2025 Orange                                             */
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

/*
 * The PMP driver: the CSR half of what pmp.h encodes.
 *
 * This replaces the ARM target's boot/mpu.c. Three pieces of that file are
 * deliberately absent rather than ported, because they were already dead
 * there: MPU_ATTR() and the subregion-disable plumbing, whose 's' parameter
 * shifted into RASR.S and whose SRD bits were never populated; the
 * mpu_configure_region() that mpu.h declared under a different name and
 * nothing called; and the ARMv8-M branches.
 *
 * pmpaddr and pmpcfg are CSRs, and a CSR number is an instruction field, not
 * an operand, so an indexed access is a switch rather than a computed
 * address. The switches below are the price of that and the reason this file
 * exists at all.
 */

#include <stddef.h>
#include <stdint.h>

#include "csr.h"
#include "pmp.h"

/*! \brief Number of pmpcfg bytes packed into one pmpcfg CSR. */
#define PMPCFG_REGIONS_PER_CSR 4

/*! \brief Mask of one pmpcfg byte. */
#define PMPCFG_BYTE_MASK UINT32_C(0xff)

/*!
 * \brief Writes pmpaddr<index>.
 * \param index A region index below PMP_WRITABLE_REGIONS_NB.
 * \param pmpaddr The value to write, as encoded by pmp_napot().
 */
static void pmpWriteAddress(uint32_t index, uint32_t pmpaddr)
{
	switch (index) {
	case 0: CSR_WRITE(pmpaddr0, pmpaddr); break;
	case 1: CSR_WRITE(pmpaddr1, pmpaddr); break;
	case 2: CSR_WRITE(pmpaddr2, pmpaddr); break;
	case 3: CSR_WRITE(pmpaddr3, pmpaddr); break;
	case 4: CSR_WRITE(pmpaddr4, pmpaddr); break;
	case 5: CSR_WRITE(pmpaddr5, pmpaddr); break;
	case 6: CSR_WRITE(pmpaddr6, pmpaddr); break;
	case 7: CSR_WRITE(pmpaddr7, pmpaddr); break;
	default: break;
	}
}

/*!
 * \brief Reads pmpaddr<index>.
 * \param index A region index below PMP_WRITABLE_REGIONS_NB.
 * \return The value of pmpaddr<index>, or zero if the index is out of range.
 */
static uint32_t pmpReadAddress(uint32_t index)
{
	switch (index) {
	case 0: return CSR_READ(pmpaddr0);
	case 1: return CSR_READ(pmpaddr1);
	case 2: return CSR_READ(pmpaddr2);
	case 3: return CSR_READ(pmpaddr3);
	case 4: return CSR_READ(pmpaddr4);
	case 5: return CSR_READ(pmpaddr5);
	case 6: return CSR_READ(pmpaddr6);
	case 7: return CSR_READ(pmpaddr7);
	default: return 0;
	}
}

/*!
 * \brief Reads the pmpcfg CSR holding the byte of region \p index.
 * \param index A region index below PMP_WRITABLE_REGIONS_NB.
 * \return The whole CSR, four region bytes packed low to high.
 */
static uint32_t pmpReadConfigCsr(uint32_t index)
{
	if (index < PMPCFG_REGIONS_PER_CSR) {
		return CSR_READ(pmpcfg0);
	}
	return CSR_READ(pmpcfg1);
}

/*!
 * \brief Writes the pmpcfg CSR holding the byte of region \p index.
 * \param index A region index below PMP_WRITABLE_REGIONS_NB.
 * \param value The whole CSR to write.
 */
static void pmpWriteConfigCsr(uint32_t index, uint32_t value)
{
	if (index < PMPCFG_REGIONS_PER_CSR) {
		CSR_WRITE(pmpcfg0, value);
	} else {
		CSR_WRITE(pmpcfg1, value);
	}
}

/*! \brief Bit position of region \p index's byte inside its pmpcfg CSR. */
static uint32_t pmpConfigShift(uint32_t index)
{
	return 8 * (index % PMPCFG_REGIONS_PER_CSR);
}

uint32_t pmpReadConfig(uint32_t index)
{
	if (index >= PMP_WRITABLE_REGIONS_NB) {
		return 0;
	}
	return (pmpReadConfigCsr(index) >> pmpConfigShift(index))
	       & PMPCFG_BYTE_MASK;
}

uint32_t pmpReadRegionAddress(uint32_t index)
{
	if (index >= PMP_WRITABLE_REGIONS_NB) {
		return 0;
	}
	return pmpReadAddress(index);
}

void pmpWriteConfig(uint32_t index, uint32_t pmpcfg)
{
	uint32_t shift;
	uint32_t csr;

	if (index >= PMP_WRITABLE_REGIONS_NB) {
		return;
	}

	shift = pmpConfigShift(index);
	csr = pmpReadConfigCsr(index) & ~(PMPCFG_BYTE_MASK << shift);
	pmpWriteConfigCsr(index, csr | ((pmpcfg & PMPCFG_BYTE_MASK) << shift));
}

void pmpWriteRegion(uint32_t index, uint32_t pmpaddr, uint32_t pmpcfg)
{
	if (index >= PMP_WRITABLE_REGIONS_NB) {
		return;
	}

	/* Turn the region off before moving it, so that no intermediate state
	 * grants the old permissions over the new range or the other way
	 * round. The deny-all background at PMP_IDX_BACKGROUND is what the
	 * address space falls back to meanwhile. */
	pmpWriteConfig(index, PMPCFG_A_OFF);
	pmpWriteAddress(index, pmpaddr);
	pmpWriteConfig(index, pmpcfg);
}

void pmpInit(void)
{
	uint32_t index;

	/* Regions 8, 9 and 10 are hardwired read-only and regions 11 to 15
	 * read as zero, so pmpcfg2 and pmpcfg3 are not written at all. */
	CSR_WRITE(pmpcfg0, 0);
	CSR_WRITE(pmpcfg1, 0);

	for (index = 0; index < PMP_WRITABLE_REGIONS_NB; index++) {
		pmpWriteAddress(index, 0);
	}

	pmpWriteRegion(PMP_IDX_BACKGROUND, PMP_BACKGROUND_ADDR,
	               PMP_BACKGROUND_CFG);

	/* The background entry denies execute as well, so instruction fetch
	 * is affected and the prefetch buffer has to be flushed. */
	fenceI();
}

int pmpCheck(void)
{
	uint32_t index;

	/* Assert that this silicon is the one the port assumes: regions 0 to 7
	 * accept a configuration byte, and region 8 reads back as the
	 * hardwired full-access window over the boot ROM. */
	for (index = 0; index < PMP_WRITABLE_REGIONS_NB; index++) {
		pmpWriteConfig(index, PMPCFG_A_NAPOT | PMPCFG_R);

		if (pmpReadConfig(index) != (PMPCFG_A_NAPOT | PMPCFG_R)) {
			return 0;
		}

		pmpWriteConfig(index, PMPCFG_A_OFF);
	}

	if ((CSR_READ(pmpcfg2) & PMPCFG_BYTE_MASK)
	    != (PMPCFG_A_NAPOT | PMPCFG_R | PMPCFG_W | PMPCFG_X)) {
		return 0;
	}

	return 1;
}

int pmp_configure_from_LUT(uint32_t *LUT)
{
	uint32_t index;
	uint32_t cfg0;
	uint32_t cfg1;

	if (LUT == NULL) {
		return -1;
	}

	/* Pack the per-region configuration bytes. pmpcfg0 holds regions 0 to
	 * 3 and pmpcfg1 regions 4 to 7, low byte first. Region 7's byte comes
	 * from PMP_BACKGROUND_CFG and never from the LUT: a partition must not
	 * be able to displace the deny-all entry that shadows the hardwired
	 * regions 8 to 10. */
	cfg0 = (LUT[1] & PMPCFG_BYTE_MASK)
	     | ((LUT[3] & PMPCFG_BYTE_MASK) << 8)
	     | ((LUT[5] & PMPCFG_BYTE_MASK) << 16)
	     | ((LUT[7] & PMPCFG_BYTE_MASK) << 24);
	cfg1 = (LUT[9] & PMPCFG_BYTE_MASK)
	     | ((LUT[11] & PMPCFG_BYTE_MASK) << 8)
	     | ((LUT[13] & PMPCFG_BYTE_MASK) << 16)
	     | ((PMP_BACKGROUND_CFG & PMPCFG_BYTE_MASK) << 24);

	/* Turn every dynamic region off before touching any address, keeping
	 * only the background. Writing addresses first would leave the
	 * outgoing partition's permissions applied to the incoming
	 * partition's address ranges for the duration of the update. PMP has
	 * no global enable to bracket the update with, the way the ARM driver
	 * disabled the MPU around it, so the configuration bytes are what has
	 * to be cleared. */
	CSR_WRITE(pmpcfg0, 0);
	CSR_WRITE(pmpcfg1, (PMP_BACKGROUND_CFG & PMPCFG_BYTE_MASK) << 24);

	/* pmpaddr7 is not written: pmpInit() sets it once and it stays. */
	for (index = 0; index < PMP_IDX_BACKGROUND; index++) {
		pmpWriteAddress(index, LUT[index * 2]);
	}

	/* Configurations last, so no intermediate state grants anything the
	 * final one does not. */
	CSR_WRITE(pmpcfg0, cfg0);
	CSR_WRITE(pmpcfg1, cfg1);

	/* A region change can alter execute permission, and Hazard3 has a
	 * prefetch buffer, so the fetch path has to be flushed. The ARM
	 * driver's ISB/DSB pair is not a substitute for this. */
	fenceI();

	return 0;
}
