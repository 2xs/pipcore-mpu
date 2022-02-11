#include <stdint.h>

#include "svc.h"

__attribute__((noinline))
uint32_t Pip_createPartition(
	uint32_t *blockLocalId
) {
	register uint32_t r0 asm("r0");

	r0 = (uint32_t) blockLocalId;

	asm volatile
	(
		"svc #0"
		: "+r" (r0)
		:
		: "memory"
	);

	return r0;
}

__attribute__((noinline))
uint32_t *Pip_cutMemoryBlock(
	uint32_t *blockToCutLocalId,
	uint32_t *cutAddr,
	int32_t  mpuRegionNb
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");
	register uint32_t r2 asm("r2");

	r0 = (uint32_t) blockToCutLocalId;
	r1 = (uint32_t) cutAddr;
	r2 = (uint32_t) mpuRegionNb;

	asm volatile
	(
		"svc #1"
		: "+r" (r0)
		: "r"  (r1),
		  "r"  (r2)
		: "memory"
	);

	return (uint32_t *) r0;
}

__attribute__((noinline))
uint32_t *Pip_mergeMemoryBlocks(
	uint32_t *blockToMerge1LocalId,
	uint32_t *blockToMerge2LocalId,
	int32_t  mpuRegionNb
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");
	register uint32_t r2 asm("r2");

	r0 = (uint32_t) blockToMerge1LocalId;
	r1 = (uint32_t) blockToMerge2LocalId;
	r2 = (uint32_t) mpuRegionNb;

	asm volatile
	(
		"svc #2"
		: "+r" (r0)
		: "r"  (r1),
		  "r"  (r2)
		: "memory"
	);

	return (uint32_t *) r0;
}

__attribute__((noinline))
uint32_t Pip_prepare(
	uint32_t *partDescBlockId,
	int32_t  projectedSlotsNb,
	uint32_t *requisitionedBlockLocalId
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");
	register uint32_t r2 asm("r2");

	r0 = (uint32_t) partDescBlockId;
	r1 = (uint32_t) projectedSlotsNb;
	r2 = (uint32_t) requisitionedBlockLocalId;

	asm volatile
	(
		"svc #3"
		: "+r" (r0)
		: "r"  (r1),
		  "r"  (r2)
		: "memory"
	);

	return r0;
}

__attribute__((noinline))
uint32_t* Pip_addMemoryBlock(
	uint32_t *childPartDescBlockLocalId,
	uint32_t *blockToShareLocalId,
	uint32_t r,
	uint32_t w,
	uint32_t e
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");
	register uint32_t r2 asm("r2");

	r0 = (uint32_t) childPartDescBlockLocalId;
	r1 = (uint32_t) blockToShareLocalId;
	r2 = ((r & 1) << 2) | ((w & 1) << 1) | (e & 1);

	asm volatile
	(
		"svc #4"
		: "+r" (r0)
		: "r"  (r1),
		  "r"  (r2)
		: "memory"
	);

	return (uint32_t *) r0;
}

__attribute__((noinline))
uint32_t Pip_removeMemoryBlock(
        uint32_t *blockToRemoveLocalId
) {
	register uint32_t r0 asm("r0");

	r0 = (uint32_t) blockToRemoveLocalId;

	asm volatile
	(
		"svc #5"
		: "+r" (r0)
		:
		: "memory"
	);

	return r0;
}

__attribute__((noinline))
uint32_t Pip_deletePartition(
	uint32_t *childPartDescBlockLocalId
) {
	register uint32_t r0 asm("r0");

	r0 = (uint32_t) childPartDescBlockLocalId;

	asm volatile
	(
		"svc #6"
		: "+r" (r0)
		:
		: "memory"
	);

	return r0;
}

__attribute__((noinline))
uint32_t *Pip_collect(
	uint32_t *partDescBlockId
) {
	register uint32_t r0 asm("r0");

	r0 = (uint32_t) partDescBlockId;

	asm volatile
	(
		"svc #7"
		: "+r" (r0)
		:
		: "memory"
	);

	return (uint32_t *) r0;
}

__attribute__((noinline))
uint32_t Pip_mapMPU(
	uint32_t *partDescBlockId,
	uint32_t *blockToMapLocalId,
	int32_t  mpuRegionNb
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");
	register uint32_t r2 asm("r2");

	r0 = (uint32_t) partDescBlockId;
	r1 = (uint32_t) blockToMapLocalId;
	r2 = (uint32_t) mpuRegionNb;

	asm volatile
	(
		"svc #8"
		: "+r" (r0)
		: "r"  (r1),
		  "r"  (r2)
		: "memory"
	);

	return r0;
}

__attribute__((noinline))
uint32_t *Pip_readMPU(
	uint32_t *partDescBlockId,
	int32_t   mpuRegionNb
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");

	r0 = (uint32_t) partDescBlockId;
	r1 = (uint32_t) mpuRegionNb;

	asm volatile
	(
		"svc #9"
		: "+r" (r0)
		: "r"  (r1)
		: "memory"
	);

	return (uint32_t *) r0;
}

__attribute__((noinline))
int32_t Pip_findBlock(
	uint32_t     *partDescBlockId,
	uint32_t     *addrInBlock,
	blockOrError *blockAddr
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");
	register uint32_t r2 asm("r2");
	register uint32_t r3 asm("r3");

	r0 = (uint32_t) partDescBlockId;
	r1 = (uint32_t) addrInBlock;

	asm volatile
	(
		"svc #10"
		: "+r" (r0),
		  "+r" (r1),
		  "=r" (r2),
		  "=r" (r3)
		:
		: "memory"
	);

	blockAddr->blockAttr.blockentryaddr = (uint32_t *) r0;
	blockAddr->blockAttr.blockstartaddr = (uint32_t *) r1;
	blockAddr->blockAttr.blockendaddr   = (uint32_t *) r2;
	blockAddr->blockAttr.read           = (r3 & 1);
	blockAddr->blockAttr.write          = ((r3 >> 1) & 1);
	blockAddr->blockAttr.exec           = ((r3 >> 2) & 1);
	blockAddr->blockAttr.accessible     = ((r3 >> 3) & 1);

	return (int32_t) blockAddr->error;
}

__attribute__((noinline))
uint32_t Pip_setVIDT(
	uint32_t *partDescBlockId,
	uint32_t *vidtBlockLocalId
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");

	r0 = (uint32_t) partDescBlockId;
	r1 = (uint32_t) vidtBlockLocalId;

	asm volatile
	(
		"svc #11"
		: "+r" (r0)
		: "r"  (r1)
		: "memory"
	);

	return r0;
}

__attribute__((noinline))
uint32_t Pip_yield(
	uint32_t *calleePartDescBlockId,
	uint32_t userTargetInterrupt,
	uint32_t userCallerContextSaveIndex,
	uint32_t flagsOnYield,
	uint32_t flagsOnWake
) {
	register uint32_t r0 asm("r0");
	register uint32_t r1 asm("r1");
	register uint32_t r2 asm("r2");
	register uint32_t r3 asm("r3");
	register uint32_t r4 asm("r4");

	r0 = (uint32_t) calleePartDescBlockId;
	r1 = userTargetInterrupt;
	r2 = userCallerContextSaveIndex;
	r3 = flagsOnYield;
	r4 = flagsOnWake;

	asm volatile
	(
		"svc #12"
		: "+r" (r0)
		: "r"  (r1),
		  "r"  (r2),
		  "r"  (r3),
		  "r"  (r4)
		: "memory"
	);

	return r0;
}
