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
 * Rungs 1 to 3 of the bring-up ladder, on real silicon:
 *
 *   1. the image boots at all, which means the bootrom accepted the picobin
 *      block, and UART0 says so;
 *   2. the PMP denies and grants what it is told to, U-mode is reachable, and
 *      a denied access arrives as the mcause it should;
 *   3. an ecall round trip: the handler steps over the ecall and the
 *      partition makes progress past it.
 *
 * Rung 2 also settles a question the datasheet does not answer. Erratum
 * RP2350-E6 transposes R and X inside each pmpcfg byte; the pico-sdk's field
 * macros say so, and pmp.h follows them. What is unconfirmed is whether the
 * transposition reaches the permission *check* as well as the register
 * layout -- a forum report claims a U-mode load needs X rather than R. The
 * permission matrix below answers it by experiment, which is the only way to.
 */

#include <stdint.h>

#include "bringup.h"
#include "csr.h"
#include "memlayout.h"
#include "pmp.h"
#include "stdio.h"
#include "uart.h"

/*! \brief The region granting U-mode the right to execute the probes. */
#define PMP_IDX_PROBE_CODE 0

/*! \brief The region under test. */
#define PMP_IDX_PROBE_DATA 1

/*! \brief A region used only to interrogate the silicon, never to grant. */
#define PMP_IDX_PROBE_SCRATCH 4

/*! \brief log2 of the XIP flash window, which holds the probes. */
#define FLASH_LOG2_SIZE 22

/*! \brief log2 of the size of the region under test. Pip's minBlockSize. */
#define PROBE_LOG2_SIZE 5

/*!
 * \brief The target of the data probes.
 *
 * Naturally aligned on its own NAPOT region size, and in .data rather than
 * .bss so that a successful load has something recognisable to return.
 */
static volatile uint32_t probeTarget[8]
	__attribute__((aligned(1 << PROBE_LOG2_SIZE))) = {
	0xc0ffee00, 0xc0ffee01, 0xc0ffee02, 0xc0ffee03,
	0xc0ffee04, 0xc0ffee05, 0xc0ffee06, 0xc0ffee07,
};

volatile uint32_t bringupTrapMepc;
volatile uint32_t bringupTrapA7;

void Boot_Handler(void);

/*! \brief The mcause codes the probes can come back with, as text. */
static const char *mcauseName(uint32_t mcause)
{
	switch (mcause) {
	case RVCSR_MCAUSE_CODE_VALUE_INSTR_FAULT:
		return "instruction access fault";
	case RVCSR_MCAUSE_CODE_VALUE_ILLEGAL_INSTR:
		return "illegal instruction";
	case RVCSR_MCAUSE_CODE_VALUE_LOAD_ALIGN:
		return "load address misaligned";
	case RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT:
		return "load access fault";
	case RVCSR_MCAUSE_CODE_VALUE_STORE_ALIGN:
		return "store access misaligned";
	case RVCSR_MCAUSE_CODE_VALUE_STORE_FAULT:
		return "store access fault";
	case RVCSR_MCAUSE_CODE_VALUE_U_ECALL:
		return "ecall from U-mode";
	default:
		return "other";
	}
}

/*! \brief Renders a pmpcfg byte's permission bits as "rwx". */
static void printPermissions(uint32_t pmpcfg)
{
	printf("%c%c%c",
	       (pmpcfg & PMPCFG_R) != 0 ? 'r' : '-',
	       (pmpcfg & PMPCFG_W) != 0 ? 'w' : '-',
	       (pmpcfg & PMPCFG_X) != 0 ? 'x' : '-');
}

/*!
 * \brief Runs one probe against one configuration of the region under test.
 *
 * \param label What the line of output should call the probe.
 * \param probe The U-mode probe to run.
 * \param pmpcfg The configuration byte to give the region under test.
 * \param expected The mcause the probe should come back with.
 * \return 1 if it did, 0 otherwise.
 */
static int runProbe(const char *label, void (*probe)(void), uint32_t pmpcfg,
                    uint32_t expected)
{
	uint32_t mcause;
	int passed;

	pmpWriteRegion(PMP_IDX_PROBE_DATA,
	               pmp_napot((uint32_t) (uintptr_t) probeTarget,
	                         PROBE_LOG2_SIZE),
	               pmpcfg);
	fenceI();

	mcause = bringupRunInUser((uint32_t) (uintptr_t) probe,
	                          (uint32_t) (uintptr_t) &__rootStackTop,
	                          (uint32_t) (uintptr_t) probeTarget);

	passed = mcause == expected;

	printf("  %-6s region=", label);
	printPermissions(pmpcfg);
	if ((pmpcfg & PMPCFG_A_MASK) == PMPCFG_A_OFF) {
		printf(" (off)");
	} else {
		printf("      ");
	}
	printf("  mcause=%lu %-26s %s\n", (unsigned long) mcause,
	       mcauseName(mcause), passed ? "ok" : "UNEXPECTED");

	return passed;
}

/*!
 * \brief Reports the PMP granularity the silicon actually implements.
 *
 * The spec fixes G as the index of the lowest set bit left after writing all
 * ones to a pmpaddr whose A is OFF; the smallest supported region is then
 * 2^(G+2) bytes, and NA4 exists only when G is zero. pmp.h assumes G == 0 on
 * the strength of the SDK header, which is worth checking against the part.
 */
static void reportGranularity(void)
{
	uint32_t readback;
	uint32_t g;

	pmpWriteRegion(PMP_IDX_PROBE_SCRATCH, UINT32_C(0xffffffff),
	               PMPCFG_A_OFF);
	readback = pmpReadRegionAddress(PMP_IDX_PROBE_SCRATCH);
	pmpWriteRegion(PMP_IDX_PROBE_SCRATCH, 0, PMPCFG_A_OFF);

	for (g = 0; g < 32 && (readback & (UINT32_C(1) << g)) == 0; g++) {
		// the lowest writable pmpaddr bit is G
	}

	printf("  granular   all-ones reads 0x%08lx  G=%lu  min region %lu"
	       " bytes  NA4 %s\n",
	       (unsigned long) readback, (unsigned long) g,
	       (unsigned long) (UINT32_C(1) << (g + 2)),
	       g == 0 ? "usable" : "absent");
}

/*!
 * \brief Reports which NAPOT sizes pmpaddr reads back bit-exactly.
 *
 * The deny-all background is written as 0x1fffffff and reads back as
 * 0x1ffffffc on this part, while still matching the whole address space.
 * Whether that is specific to the 2^32 case decides whether a pmpaddr
 * readback can be used to verify a region at all, and whether
 * pmp_napot_log2size() may ever be pointed at one.
 */
static void reportNapotReadback(void)
{
	static const uint32_t log2sizes[] = {
		5, 8, 12, 16, 20, 24, 28, 30, 31, 32,
	};
	uint32_t i;

	printf("  napot readback at base 0:\n");

	for (i = 0; i < sizeof(log2sizes) / sizeof(log2sizes[0]); i++) {
		uint32_t wrote = pmp_napot(0, log2sizes[i]);
		uint32_t reads;

		pmpWriteRegion(PMP_IDX_PROBE_SCRATCH, wrote, PMPCFG_A_NAPOT);
		reads = pmpReadRegionAddress(PMP_IDX_PROBE_SCRATCH);

		printf("    2^%-2lu  wrote 0x%08lx  reads 0x%08lx  %s\n",
		       (unsigned long) log2sizes[i], (unsigned long) wrote,
		       (unsigned long) reads,
		       reads == wrote ? "exact" : "DIFFERS");
	}

	/* Leave nothing matching behind: this entry is lower-numbered than
	 * the background, so an A=NAPOT leftover would shadow it. */
	pmpWriteRegion(PMP_IDX_PROBE_SCRATCH, 0, PMPCFG_A_OFF);
}

/*!
 * \brief Probes a U-mode load from a window a hardwired region covers.
 *
 * Regions 8, 9 and 10 are hardwired to A=NAPOT, R=W=X=1 over the boot ROM,
 * the system peripherals and SIO, and cannot be turned off. Section 3 of the
 * plan closes that hole with the deny-all entry 7, relying on PMP being
 * lowest-matching-entry-wins. Nothing else here tests it: probeTarget lives
 * in SRAM, which regions 8 to 10 do not cover, so the A=OFF probes above are
 * denied by RISC-V's default-deny whether entry 7 works or not.
 *
 * \param label What the line of output should call the window.
 * \param address A word-aligned address to load from in U-mode.
 * \param expected The mcause the probe should come back with. A denied load
 *        reports LOAD_FAULT; one that got through runs on into the probe's
 *        own ecall and reports U_ECALL instead.
 * \return 1 if it did, 0 otherwise.
 */
static uint32_t loadMcause(uint32_t address)
{
	return bringupRunInUser((uint32_t) (uintptr_t) bringupProbeLoad,
	                        (uint32_t) (uintptr_t) &__rootStackTop,
	                        address);
}

/*!
 * \brief Reports the smallest NAPOT region the *matcher* honours.
 *
 * The readback cannot answer this. It follows neither of the spec's
 * conventions for the ignored low bits -- with A=NAPOT they read as zero
 * where the spec says ones, and with A=OFF they read as written where the
 * spec says zeros -- so the value it returns says nothing about G. Ask the
 * matcher instead: give it a region declared smaller than 32 bytes and see
 * how far the grant actually reaches.
 *
 * If pmpaddr[1:0] are unimplemented and forced to ones in the matcher, every
 * one of 2^3, 2^4 and 2^5 is really 32 bytes and all three admit a load at
 * +16. If the granule is genuinely 4 bytes, 2^3 and 2^4 stop short of it.
 */
static void reportNapotGranule(void)
{
	static const uint32_t log2sizes[] = { 3, 4, 5 };
	uint32_t base = (uint32_t) (uintptr_t) probeTarget;
	uint32_t i;

	printf("  napot granule, r-- region at 0x%08lx:\n",
	       (unsigned long) base);

	for (i = 0; i < sizeof(log2sizes) / sizeof(log2sizes[0]); i++) {
		uint32_t at0;
		uint32_t at16;

		pmpWriteRegion(PMP_IDX_PROBE_DATA,
		               pmp_napot(base, log2sizes[i]),
		               PMPCFG_A_NAPOT | PMPCFG_R);
		fenceI();
		at0 = loadMcause(base);
		at16 = loadMcause(base + 16);

		printf("    2^%-2lu  +0 mcause=%lu  +16 mcause=%lu  %s\n",
		       (unsigned long) log2sizes[i], (unsigned long) at0,
		       (unsigned long) at16,
		       at16 == RVCSR_MCAUSE_CODE_VALUE_U_ECALL
		               ? "reaches +16, so >= 32 bytes"
		               : "stops short of +16");
	}

	/* NA4 is a separate A encoding, and the Hazard3 manual says it matches
	 * the entire 30-bit address. If it works, +0 is admitted and +4 is
	 * not. */
	pmpWriteRegion(PMP_IDX_PROBE_DATA, base >> 2,
	               PMPCFG_A_NA4 | PMPCFG_R);
	fenceI();
	{
		uint32_t at0 = loadMcause(base);
		uint32_t at4 = loadMcause(base + 4);

		printf("    NA4   +0 mcause=%lu  +4 mcause=%lu  %s\n",
		       (unsigned long) at0, (unsigned long) at4,
		       at0 == RVCSR_MCAUSE_CODE_VALUE_U_ECALL
		       && at4 == RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT
		               ? "a true 4-byte region"
		               : "not a 4-byte region");
	}

	pmpWriteRegion(PMP_IDX_PROBE_DATA, 0, PMPCFG_A_OFF);
	fenceI();
}

static int runLoadProbe(const char *label, uint32_t address, uint32_t expected)
{
	uint32_t mcause;
	int passed;

	mcause = loadMcause(address);
	passed = mcause == expected;

	printf("  load   %-10s at 0x%08lx  mcause=%lu %-26s %s\n", label,
	       (unsigned long) address, (unsigned long) mcause,
	       mcauseName(mcause), passed ? "ok" : "UNEXPECTED");

	return passed;
}

/*!
 * \brief Rung 1: the image booted and can talk.
 */
static void rungOne(void)
{
	printf("\n");
	printf("pip-mpu rp2350 bring-up\n");
	printf("rung 1: the bootrom accepted the image and UART0 is up\n");
	printf("  mvendorid  0x%08lx\n", (unsigned long) CSR_READ(mvendorid));
	printf("  marchid    0x%08lx\n", (unsigned long) CSR_READ(marchid));
	printf("  mimpid     0x%08lx\n", (unsigned long) CSR_READ(mimpid));
	printf("  misa       0x%08lx\n", (unsigned long) CSR_READ(misa));
	printf("  mtval      0x%08lx  (hardwired to zero on this core)\n",
	       (unsigned long) CSR_READ(mtval));
	printf("  mtvec      0x%08lx\n", (unsigned long) CSR_READ(mtvec));
	printf("  probes at  0x%08lx, target at 0x%08lx\n",
	       (unsigned long) (uintptr_t) bringupProbeEcall,
	       (unsigned long) (uintptr_t) probeTarget);
}

/*!
 * \brief Rung 2: the PMP, U-mode, and the extent of erratum E6.
 * \return The number of probes that came back with an unexpected mcause.
 */
static int rungTwo(void)
{
	int failures = 0;

	printf("rung 2: PMP and U-mode\n");

	if (!pmpCheck()) {
		printf("  pmpCheck FAILED: this is not the PMP the port"
		       " assumes\n");
		failures++;
	}

	pmpInit();

	/* Dump what the hardwired regions actually read back, since the whole
	 * region budget rests on their being what the header says. */
	printf("  pmpcfg2    0x%08lx  (regions 8-11, hardwired)\n",
	       (unsigned long) CSR_READ(pmpcfg2));
	printf("  pmpaddr7   wrote 0x%08lx reads 0x%08lx  cfg 0x%02lx"
	       "  (deny-all background)\n",
	       (unsigned long) PMP_BACKGROUND_ADDR,
	       (unsigned long) pmpReadRegionAddress(PMP_IDX_BACKGROUND),
	       (unsigned long) pmpReadConfig(PMP_IDX_BACKGROUND));

	reportGranularity();
	reportNapotReadback();

	/* U-mode needs to be able to fetch the probes. This region is not the
	 * one under test. */
	pmpWriteRegion(PMP_IDX_PROBE_CODE,
	               pmp_napot((uint32_t) (uintptr_t) &__romStart,
	                         FLASH_LOG2_SIZE),
	               PMPCFG_A_NAPOT | PMPCFG_R | PMPCFG_X);
	fenceI();

	/* With no region at all over it, the probe target is matched by no
	 * entry, so RISC-V's default-deny for U-mode has to refuse it. This
	 * says nothing about entries 8 to 10, which do not cover SRAM; the
	 * shadow probes below are what test those. */
	failures += !runProbe("ecall", bringupProbeEcall, PMPCFG_A_OFF,
	                      RVCSR_MCAUSE_CODE_VALUE_U_ECALL);
	failures += !runProbe("load", bringupProbeLoad, PMPCFG_A_OFF,
	                      RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT);
	failures += !runProbe("store", bringupProbeStore, PMPCFG_A_OFF,
	                      RVCSR_MCAUSE_CODE_VALUE_STORE_FAULT);

	/* The permission matrix. R alone must admit a load and refuse a
	 * store; W alone must refuse the load. If instead X is what admits
	 * the load, erratum E6 reaches the permission check and the HAL's
	 * mapping of the model's read flag has to follow suit. */
	failures += !runProbe("load", bringupProbeLoad,
	                      PMPCFG_A_NAPOT | PMPCFG_R,
	                      RVCSR_MCAUSE_CODE_VALUE_U_ECALL);
	failures += !runProbe("load", bringupProbeLoad,
	                      PMPCFG_A_NAPOT | PMPCFG_W,
	                      RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT);
	failures += !runProbe("load", bringupProbeLoad,
	                      PMPCFG_A_NAPOT | PMPCFG_X,
	                      RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT);
	failures += !runProbe("store", bringupProbeStore,
	                      PMPCFG_A_NAPOT | PMPCFG_R,
	                      RVCSR_MCAUSE_CODE_VALUE_STORE_FAULT);
	failures += !runProbe("store", bringupProbeStore,
	                      PMPCFG_A_NAPOT | PMPCFG_R | PMPCFG_W,
	                      RVCSR_MCAUSE_CODE_VALUE_U_ECALL);

	printf("  probeTarget[0] after the stores: 0x%08lx\n",
	       (unsigned long) probeTarget[0]);

	/* The region budget of section 3 stands or falls here: entry 7 is
	 * lower-numbered than the hardwired 8 to 10, so it must shadow all
	 * three. A load that gets through is U-mode reading the boot ROM, a
	 * peripheral or SIO, which is the hole the deny-all exists to close. */
	failures += !runLoadProbe("boot ROM", UINT32_C(0x00000000),
	                          RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT);
	failures += !runLoadProbe("peripheral", UINT32_C(0x40000000),
	                          RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT);
	failures += !runLoadProbe("SIO", UINT32_C(0xd0000000),
	                          RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT);

	/* The readback drops two bits of NAPOT size, so confirm that matching
	 * honours the size that was *written*: a 32-byte region has to cover
	 * its last word, not just the 8 bytes its readback decodes to. This
	 * is the size Pip's minBlockSize actually asks for. */
	pmpWriteRegion(PMP_IDX_PROBE_DATA,
	               pmp_napot((uint32_t) (uintptr_t) probeTarget,
	                         PROBE_LOG2_SIZE),
	               PMPCFG_A_NAPOT | PMPCFG_R);
	fenceI();
	failures += !runLoadProbe("last word",
	                          (uint32_t) (uintptr_t) &probeTarget[7],
	                          RVCSR_MCAUSE_CODE_VALUE_U_ECALL);

	reportNapotGranule();

	return failures;
}

/*!
 * \brief Rung 3: an ecall round trip.
 * \return 0 if the partition made progress past its first ecall.
 */
static int rungThree(void)
{
	uint32_t mcause;
	int failures = 0;

	printf("rung 3: ecall round trip\n");

	mcause = bringupRunInUser((uint32_t) (uintptr_t) bringupProbeResume,
	                          (uint32_t) (uintptr_t) &__rootStackTop, 0);

	if (mcause != RVCSR_MCAUSE_CODE_VALUE_U_ECALL) {
		printf("  mcause=%lu %s  UNEXPECTED\n",
		       (unsigned long) mcause, mcauseName(mcause));
		failures++;
	} else if (bringupTrapA7 != BRINGUP_A7_DONE) {
		printf("  came back on the first ecall: mepc was not"
		       " advanced  UNEXPECTED\n");
		failures++;
	} else {
		printf("  resumed past the first ecall and reached the"
		       " second  ok\n");
	}

	return failures;
}

void bringupMachineTrap(uint32_t mcause, uint32_t mepc)
{
	printf("\nM-MODE TRAP: mcause=%lu %s mepc=0x%08lx\n",
	       (unsigned long) mcause, mcauseName(mcause),
	       (unsigned long) mepc);

	while (1) {
		// the harness itself faulted, so there is nothing to go back to
	}
}

void Boot_Handler(void)
{
	int failures;

	rungOne();
	failures = rungTwo();
	failures += rungThree();

	if (failures == 0) {
		printf("bring-up rungs 1-3 PASSED\n");
	} else {
		printf("bring-up rungs 1-3 FAILED: %d unexpected results\n",
		       failures);
	}

	while (1) {
		// nothing follows the ladder
	}
}
