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
 * \file test_pmp.c
 * \brief Host unit test of the PMP NAPOT encoding (rung 0).
 *
 * Checks pmp_napot() against a table of hand-computed values, that the
 * decoding helpers invert it, and that the pmpcfg field positions still
 * match the pico-sdk register header, which encodes erratum RP2350-E6.
 */

#include "pmp.h"
#include "test.h"

/*!
 * \struct napotCase_t
 * \brief One expected NAPOT encoding.
 */
typedef struct napotCase_s {
	const char *name;	/*!< The case, as text. */
	uint32_t base;		/*!< The region base address. */
	uint32_t log2size;	/*!< The log2 of the region size. */
	uint32_t pmpaddr;	/*!< The expected pmpaddr value. */
} napotCase_t;

static const napotCase_t napotCases[] = {
	// The smallest size the NAPOT encoding expresses. The silicon does not
	// honour it -- pmpaddr[1:0] are unimplemented, so this is matched as a
	// 32-byte region -- but the encoding is still what it should be.
	{ "8 B at 0x20000008",   0x20000008, 3,  0x08000002 },
	// Pip's minBlockSize, the smallest a partition-visible region can be.
	{ "32 B at 0x20000000",  0x20000000, 5,  0x08000003 },
	{ "32 B at 0x20000020",  0x20000020, 5,  0x0800000b },
	{ "4 KiB in XIP flash",  0x10001000, 12, 0x040005ff },
	// The root partition's code region, per the planned linker script.
	{ "64 KiB in XIP flash", 0x10010000, 16, 0x04005fff },
	// The root partition's single RAM region, per the planned linker script.
	{ "256 KiB of SRAM",     0x20000000, 18, 0x08007fff },
	{ "4 KiB of SCRATCH_X",  0x20080000, 12, 0x080201ff },
	// The deny-all background entry, where log2size is at its maximum.
	{ "the whole 4 GiB",     0x00000000, 32, 0x1fffffff },
};

/*!
 * \fn void testNapotEncoding(void)
 * \brief Checks pmp_napot() against the table.
 */
static void testNapotEncoding(void)
{
	for (unsigned i = 0; i < sizeof(napotCases) / sizeof(*napotCases); i++) {
		const napotCase_t *c = &napotCases[i];

		CHECK_AT(c->name, pmp_napot(c->base, c->log2size), c->pmpaddr);
	}
}

/*!
 * \fn void testNapotDecoding(void)
 * \brief Checks that the decoding helpers invert pmp_napot().
 */
static void testNapotDecoding(void)
{
	for (unsigned i = 0; i < sizeof(napotCases) / sizeof(*napotCases); i++) {
		const napotCase_t *c = &napotCases[i];

		CHECK_AT(c->name, pmp_napot_log2size(c->pmpaddr), c->log2size);
		/*
		 * The base of a region covering the whole address space is zero,
		 * which is also what the encoding of base zero gives back.
		 */
		CHECK_AT(c->name, pmp_napot_base(c->pmpaddr), c->base);
	}
}

/*!
 * \fn void testConfigBits(void)
 * \brief Pins the pmpcfg field positions of the silicon.
 *
 * The expected values are those of RVCSR_PMPCFG0_R0_*_BITS in
 * src/rp2350/hardware_regs/include/hardware/regs/rvcsr.h. R is bit 2 and X
 * is bit 0, transposed from the specification order by erratum RP2350-E6, so
 * a well-meaning "fix" towards the spec has to fail here.
 */
static void testConfigBits(void)
{
	CHECK(PMPCFG_X, 0x00000001);
	CHECK(PMPCFG_W, 0x00000002);
	CHECK(PMPCFG_R, 0x00000004);
	CHECK(PMPCFG_A_OFF, 0x00000000);
	CHECK(PMPCFG_A_NA4, 0x00000010);
	CHECK(PMPCFG_A_NAPOT, 0x00000018);
	CHECK(PMPCFG_L, 0x00000080);
	// A pmpcfg byte must fit in a byte, since eight of them pack per CSR.
	CHECK((PMPCFG_L | PMPCFG_A_NAPOT | PMPCFG_R | PMPCFG_W | PMPCFG_X)
	      & ~UINT32_C(0xff), 0);
}

/*!
 * \fn void testBackgroundEntry(void)
 * \brief Checks the deny-all background entry of region 7.
 */
static void testBackgroundEntry(void)
{
	// Covers every address, so it shadows the hardwired regions 8 to 10.
	CHECK(PMP_BACKGROUND_ADDR, 0x1fffffff);
	CHECK(pmp_napot_log2size(PMP_BACKGROUND_ADDR), 32);
	// Enabled, but grants nothing. L stays clear so Pip keeps full access.
	CHECK(PMP_BACKGROUND_CFG & PMPCFG_A_MASK, PMPCFG_A_NAPOT);
	CHECK(PMP_BACKGROUND_CFG & (PMPCFG_R | PMPCFG_W | PMPCFG_X), 0);
	CHECK(PMP_BACKGROUND_CFG & PMPCFG_L, 0);
}

/*!
 * \fn void testRegionBudget(void)
 * \brief Checks the region budget of section 3 of the port plan.
 */
static void testRegionBudget(void)
{
	// Five partition-visible, two for the refill, one deny-all background.
	CHECK(PMP_WRITABLE_REGIONS_NB, 8);
	CHECK(PMP_PARTITION_REGIONS_NB, 5);
	CHECK(PMP_PARTITION_REGIONS_NB + 2 + 1, PMP_WRITABLE_REGIONS_NB);
	/*
	 * The refill slots sit above the partition-visible ones, so that a
	 * partition-visible entry wins on overlap: PMP is lowest-matching-wins,
	 * the opposite of the ARM MPU, where the reserved slots are the two
	 * highest-numbered instead.
	 */
	CHECK(PMP_IDX_REFILL_INSTR, 5);
	CHECK(PMP_IDX_REFILL_DATA, 6);
	CHECK(PMP_IDX_BACKGROUND, 7);
}

int main(void)
{
	testNapotEncoding();
	testNapotDecoding();
	testConfigBits();
	testBackgroundEntry();
	testRegionBudget();
	return testReport("test_pmp");
}
