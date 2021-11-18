/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2021)                */
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

#include "user_ADT.h"

__attribute__ ((noinline)) int Pip_createPartition(uint32_t* idBlock)
{
  __asm("SVC #0");
}

__attribute__ ((noinline)) uint32_t* Pip_cutMemoryBlock(uint32_t* idBlockToCut,
                                                    uint32_t* cutAddr,
                                                    int32_t mPURegionNb)
{
  __asm("SVC #1");
}

__attribute__ ((noinline)) uint32_t* Pip_mergeMemoryBlocks( uint32_t* idBlockToMerge1,
                                                        uint32_t* idBlockToMerge2,
                                                        int32_t mPURegionNb)
{
  __asm("SVC #2");
}


__attribute__ ((noinline)) int Pip_prepare( uint32_t* idPD,
                                            int32_t projectedSlotsNb,
                                            uint32_t* idRequisitionedBlock)
{
  __asm("SVC #3");
}

__attribute__((noinline))
uint32_t* Pip_addMemoryBlock(
	uint32_t *childPartDescBlockLocalId,
	uint32_t *blockToShareLocalId,
	uint32_t  r,
	uint32_t  w,
	uint32_t  e
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

__attribute__ ((noinline)) uint32_t Pip_removeMemoryBlock(uint32_t* idPDchild,
                                                          uint32_t* idBlockToRemove)
{
  __asm("SVC #5");
}

__attribute__ ((noinline)) uint32_t Pip_deletePartition(uint32_t* idPDchildToDelete)
{
  __asm("SVC #6");
}

__attribute__ ((noinline)) uint32_t* Pip_collect(uint32_t* idPD)
{
  __asm("SVC #7");
}

__attribute__ ((noinline)) uint32_t Pip_mapMPU( uint32_t* idPD,
                                                uint32_t* idBlockToEnable,
                                                int32_t mPURegionNb)
{
  __asm("SVC #8");
}

__attribute__ ((noinline)) uint32_t* Pip_readMPU( uint32_t* idPD,
                                                  int32_t mPURegionNb)
{
  __asm("SVC #9");
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
