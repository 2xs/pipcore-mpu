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

/*!
 * \file pmp.h
 * \brief RISC-V PMP region encoding for the Hazard3 core of the RP2350.
 *
 * Encoding only: no CSR access lives here, so this header is also compiled
 * by the host unit tests (src/arch/rp2350/test).
 *
 * Bit positions come from the pico-sdk register header
 * src/rp2350/hardware_regs/include/hardware/regs/rvcsr.h, which encodes the
 * silicon rather than the specification. Erratum RP2350-E6 transposes R and
 * X inside each pmpcfg byte, so the spec order X=2, W=1, R=0 is wrong here.
 */

#ifndef PMP_H
#define PMP_H

#include <stdint.h>

/*!
 * \brief Number of software-writable PMP regions.
 *
 * The core has 16 pmpcfg slots, but only 0-7 are writable. Regions 8, 9 and
 * 10 are hardwired read-only to A=NAPOT, R=W=X=1 over the boot ROM, the
 * system peripherals and the core-local SIO respectively, and regions 11-15
 * are hardwired to zero.
 */
#define PMP_WRITABLE_REGIONS_NB 8

/*!
 * \brief Index of the permanent deny-all background region.
 *
 * PMP is lowest-matching-entry-wins, the opposite polarity of the ARM MPU.
 * A single matching entry below index 8 therefore makes the three hardwired
 * entries unreachable, restoring the architectural default-deny for U-mode
 * over the whole address space. This is the reason regions 8-10 are not a
 * hole in the isolation.
 */
#define PMP_IDX_BACKGROUND 7

/*!
 * \brief Indices of the two regions reserved for the fault-driven refill.
 *
 * They sit above the partition-visible regions 0-4 so that a
 * partition-visible entry wins on overlap. This is the mirror image of the
 * ARM target, where the reserved slots are the two highest-numbered ones
 * because the ARM MPU is highest-region-wins.
 */
#define PMP_IDX_REFILL_INSTR 5
#define PMP_IDX_REFILL_DATA  6

/*! \brief Number of partition-visible regions, the value getMPURegionsNb() returns. */
#define PMP_PARTITION_REGIONS_NB PMP_IDX_REFILL_INSTR

/*!
 * \brief pmpcfg byte fields, with the RP2350-E6 positions of R and X.
 */
#define PMPCFG_X        (UINT32_C(1) << 0)	/*!< E6: transposed with R. */
#define PMPCFG_W        (UINT32_C(1) << 1)
#define PMPCFG_R        (UINT32_C(1) << 2)	/*!< E6: transposed with X. */
#define PMPCFG_A_OFF    (UINT32_C(0) << 3)
#define PMPCFG_A_NA4    (UINT32_C(2) << 3)
#define PMPCFG_A_NAPOT  (UINT32_C(3) << 3)
#define PMPCFG_A_MASK   (UINT32_C(3) << 3)
#define PMPCFG_L        (UINT32_C(1) << 7)	/*!< Never set: see below. */

/*!
 * \brief Smallest and largest region size the NAPOT *encoding* expresses.
 *
 * NAPOT encodes a size of 2^n bytes as (n - 3) trailing one-bits in pmpaddr,
 * so the format covers 8 bytes upwards. These are properties of the encoding
 * and are what the decoding helpers below invert; what the silicon honours is
 * PMP_NAPOT_HW_MIN_LOG2, which is larger.
 */
#define PMP_NAPOT_MIN_LOG2 3
#define PMP_NAPOT_MAX_LOG2 32

/*!
 * \brief The smallest NAPOT region this silicon actually honours, as a log2.
 *
 * Measured on the part, not taken from a datasheet: pmpaddr[1:0] are
 * unimplemented and read as ones by the matcher, so the least-significant
 * zero bit -- which is what sets the region size -- can never sit below bit
 * 2. A region encoded as 2^3 or 2^4 is therefore *matched as 2^5*, and
 * A=NA4 grants nothing at all. The Hazard3 manual's pmpaddr section states
 * the matching rule this follows from; see KNOWLEDGE.md section 7.1 for the
 * measurements.
 *
 * Asking pmp_napot() for less than this widens the region silently, which is
 * the dangerous direction, so callers must not. Pip's minBlockSize is 32
 * bytes and check32Aligned enforces the matching alignment, so the model
 * already keeps every partition-visible region at or above this bound --
 * on this target that constraint is load-bearing, not merely conservative.
 */
#define PMP_NAPOT_HW_MIN_LOG2 5

/*!
 * \fn uint32_t pmp_napot(uint32_t base, uint32_t log2size)
 * \brief Encodes a naturally-aligned power-of-two region as a pmpaddr value.
 *
 * pmpaddr holds the address in units of four bytes, and NAPOT marks the size
 * with trailing one-bits in the low part of that shifted address.
 *
 * \param base The base address of the region, which must be aligned on
 *        2^log2size.
 * \param log2size The log2 of the region size, in [PMP_NAPOT_HW_MIN_LOG2,
 *        PMP_NAPOT_MAX_LOG2]. Below PMP_NAPOT_HW_MIN_LOG2 the encoding is
 *        still correct but the silicon matches a larger region than asked
 *        for, so do not.
 * \return The value to write to pmpaddr<i>.
 */
static inline uint32_t pmp_napot(uint32_t base, uint32_t log2size)
{
	return (base >> 2) | ((UINT32_C(1) << (log2size - 3)) - 1);
}

/*!
 * \fn uint32_t pmp_napot_log2size(uint32_t pmpaddr)
 * \brief Recovers the region size from a NAPOT pmpaddr value.
 *
 * Only for a value pmp_napot() produced, never for one read back out of the
 * CSR. On this silicon a pmpaddr written while A = NAPOT reads back with bits
 * 1:0 cleared, at every size, so a readback carries two fewer trailing
 * one-bits than it was given and decodes to a quarter of the real size.
 * Matching uses the written value, so only the readback is affected. Measured
 * at every size from 2^5 to 2^32; see KNOWLEDGE.md section 7.1.
 *
 * \param pmpaddr A pmpaddr value encoded by pmp_napot().
 * \return The log2 of the region size.
 */
static inline uint32_t pmp_napot_log2size(uint32_t pmpaddr)
{
	uint32_t log2size = PMP_NAPOT_MIN_LOG2;

	while (pmpaddr & UINT32_C(1)) {	// counts the trailing one-bits
		log2size++;
		pmpaddr >>= 1;
	}
	return log2size;
}

/*!
 * \fn uint32_t pmp_napot_base(uint32_t pmpaddr)
 * \brief Recovers the base address of a region from a NAPOT pmpaddr value.
 *
 * Same restriction as pmp_napot_log2size(): a value read back out of the CSR
 * is not a faithful encoding and must not be passed here.
 *
 * \param pmpaddr A pmpaddr value encoded by pmp_napot().
 * \return The base address of the region.
 */
static inline uint32_t pmp_napot_base(uint32_t pmpaddr)
{
	uint32_t log2size = pmp_napot_log2size(pmpaddr);

	if (log2size >= PMP_NAPOT_MAX_LOG2) {
		return 0;	// the whole address space: shifting by 32 is undefined
	}
	return (pmpaddr << 2) & ~((UINT32_C(1) << log2size) - 1);
}

/*!
 * \brief The deny-all background entry installed at PMP_IDX_BACKGROUND.
 *
 * NAPOT over the whole 2^32 address space at base 0, with no permission bit
 * set. L stays 0, which is what makes this entry apply to U-mode only: a
 * region with L=0 does not constrain M-mode at all, which is exactly the
 * ARM target's MPU_CTRL_PRIVDEFENA=1. Never set L, and never mirror a region
 * into h3.pmpcfgm0 either, since both make the entry apply to Pip itself.
 */
#define PMP_BACKGROUND_ADDR pmp_napot(0, PMP_NAPOT_MAX_LOG2)
#define PMP_BACKGROUND_CFG  PMPCFG_A_NAPOT

/*
 * The driver, defined in pmp.c. These touch CSRs, so the host unit tests
 * declare them without linking them.
 */

/*!
 * \fn void pmpWriteRegion(uint32_t index, uint32_t pmpaddr, uint32_t pmpcfg)
 * \brief Points region \p index at \p pmpaddr with configuration \p pmpcfg.
 *
 * The region is turned off while its address changes, so no intermediate
 * state grants the old permissions over the new range.
 *
 * \param index A region index below PMP_WRITABLE_REGIONS_NB. A larger one is
 *        ignored, since regions 8 and above are not writable.
 * \param pmpaddr A value encoded by pmp_napot().
 * \param pmpcfg A configuration byte built from the PMPCFG_* macros.
 */
void pmpWriteRegion(uint32_t index, uint32_t pmpaddr, uint32_t pmpcfg);

/*!
 * \fn void pmpWriteConfig(uint32_t index, uint32_t pmpcfg)
 * \brief Replaces region \p index's configuration byte, leaving its address.
 * \param index A region index below PMP_WRITABLE_REGIONS_NB.
 * \param pmpcfg A configuration byte built from the PMPCFG_* macros.
 */
void pmpWriteConfig(uint32_t index, uint32_t pmpcfg);

/*!
 * \fn uint32_t pmpReadConfig(uint32_t index)
 * \brief Reads region \p index's configuration byte.
 * \param index A region index below PMP_WRITABLE_REGIONS_NB.
 * \return The configuration byte, or zero if the index is out of range.
 */
uint32_t pmpReadConfig(uint32_t index);

/*!
 * \fn uint32_t pmpReadRegionAddress(uint32_t index)
 * \brief Reads pmpaddr of region \p index.
 * \param index A region index below PMP_WRITABLE_REGIONS_NB.
 * \return The pmpaddr value, or zero if the index is out of range.
 */
uint32_t pmpReadRegionAddress(uint32_t index);

/*!
 * \fn void pmpInit(void)
 * \brief Turns every writable region off and installs the deny-all background.
 *
 * Until this has run, the hardwired regions 8 to 10 grant U-mode full access
 * to the boot ROM, every system peripheral and the core-local SIO.
 */
void pmpInit(void);

/*!
 * \fn int pmpCheck(void)
 * \brief Checks that the PMP is the one this port assumes.
 *
 * Replaces the ARM target's compile-time MPU_NUM_REGIONS comparison with a
 * runtime probe, since the region count is not the only assumption being
 * made: regions 0 to 7 must accept a configuration byte, and region 8 must
 * read back as the hardwired full-access window.
 *
 * \return 1 if the silicon matches, 0 otherwise.
 */
int pmpCheck(void);

/*!
 * \fn int pmp_configure_from_LUT(uint32_t *LUT)
 * \brief Loads a partition's LUT into the PMP CSRs.
 *
 * The replacement for the ARM target's mpu_configure_from_LUT(). Per region
 * i, LUT[2i] is a pmpaddr value and LUT[2i+1] a pmpcfg byte; the regions are
 * written address-first and configuration-last, with every dynamic region
 * turned off beforehand, so no intermediate state grants anything the final
 * one does not.
 *
 * Region 7's configuration byte always comes from PMP_BACKGROUND_CFG and
 * pmpaddr7 is never written, so a partition cannot displace the deny-all
 * background that shadows the hardwired regions 8 to 10.
 *
 * \param LUT The MPU_REGIONS_NB*2 word LUT of the partition to activate.
 * \return 0 on success, a negative value on failure.
 */
int pmp_configure_from_LUT(uint32_t *LUT);

#endif /* PMP_H */
