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

#include "ExceptionHandlers.h"
#include "Services.h"
#include "nrf52.h"
#include "core_cm4.h"
#include <stdio.h>
#include "pip_debug.h"

extern void
  SVC_Handler (void);


void __attribute__ ((section(".after_vectors"),weak))
SVC_Handler (void)
{
  __asm(
    ".global SVC_Handler_Main\n"
    "TST lr, #4\n"
    "ITE EQ\n"
    "MRSEQ r0, MSP\n"
    "MRSNE r0, PSP\n"
    "B SVC_Handler_Main\n"
  ) ;
}

void SVC_Handler_Main( unsigned int *svc_args )
{
#if defined(DEBUG)
  __DEBUG_BKPT();
#endif

  unsigned int svc_number;
  /*
  * Stack contains:
  * r0, r1, r2, r3, r12, r14, the return address and xPSR
  * First argument (r0) is svc_args[0]
  */
  svc_number = ( ( char * )svc_args[ 6 ] )[ -2 ] ;
  uint32_t * sp = (uint32_t*) svc_args;
  uint32_t * orig_sp = NULL;
  uint32_t psr = sp[7];  /* Program status register. */
  /* Reconstruct original stack pointer before fault occurred */
  orig_sp = sp + 8;
#ifdef SCB_CCR_STKALIGN_Msk
  if (psr & SCB_CCR_STKALIGN_Msk) {
      /* Stack was not 8-byte aligned */
      orig_sp += 1;
      debug_puts("SVC: Stack was not 8-byte aligned\r\n");
  }
#endif /* SCB_CCR_STKALIGN_Msk */

  // disable interrupts...
  __disable_irq();
  switch( svc_number )
  {
    case 0:
      sp[0] = (uint32_t) createPartition((uint32_t *)svc_args[0]); //paddr idBlock
      break;
    case 1:
      sp[0] = (uint32_t) cutMemoryBlock((uint32_t *)svc_args[0], //paddr idBlockToCut,
                                        (uint32_t *)svc_args[1], //paddr cutAddr,
                                        svc_args[2] //index mPURegionNb)
                                        );
      break;
    case 2:
      sp[0] = (uint32_t) mergeMemoryBlocks((uint32_t *)svc_args[0], //paddr idBlockToMerge1,
                                            (uint32_t *)svc_args[1], //paddr idBlockToMerge2,
                                            svc_args[2] //index mPURegionNb)
                                            );
      break;
    case 3:
      sp[0] = (uint32_t) prepare((uint32_t *)svc_args[0], //paddr idPD,
                                  svc_args[1], //index projectedSlotsNb,
                                  (uint32_t *)svc_args[2] //paddr idRequisitionedBlock
                                  );
    break;

    case 4:
      sp[0] = (uint32_t) addMemoryBlock((uint32_t *)svc_args[0], //paddr idPDchild,
                                        (uint32_t *)svc_args[1], //paddr idBlockToShare,
                                        (uint32_t)svc_args[2], //bool r,
                                        (uint32_t)svc_args[3], //bool w,
                                        (uint32_t)orig_sp[0] //bool e)
                                        );
      break;
    case 5:
      sp[0] = removeMemoryBlock((uint32_t *)svc_args[0], //paddr idPDchild,
                                (uint32_t *)svc_args[1] //paddr idBlockToRemove
                                );
      break;

    case 6:
      sp[0] = deletePartition((uint32_t *)svc_args[0]); //paddr idPDchildToDelete
    break;

    case 7:
      sp[0] = (uint32_t) collect((uint32_t *)svc_args[0]); //paddr idPD
      break;
    case 8:
      sp[0] = mapMPU( (uint32_t *)svc_args[0], //paddr idPD
                      (uint32_t *)svc_args[1], //paddr idBlockToEnable,
                      svc_args[2] // index mPURegionNb
                      );
      break;
    case 9:
      sp[0] = (uint32_t) readMPU((uint32_t *)svc_args[0], //paddr idPD
                                  svc_args[1] // index mPURegionNb
                                  );
      break;
    case 10:
    {
      // Note as the result is in memory, the parameters are passed with R1 and R2, not RO
      blockOrError block_found = findBlock( (uint32_t *)svc_args[1], //paddr idPD
                                            (uint32_t *)svc_args[2] // paddr addrInBlock)
                                            );
      // Fill R0-R3: the access permissions and accessible bit are squeezed into R3
      sp[0] = (uint32_t) block_found.blockAttr.blockentryaddr;
      sp[1] = (uint32_t) block_found.blockAttr.blockrange.startAddr; // displays start and end
      sp[2] = (uint32_t) block_found.blockAttr.blockrange.endAddr;
      sp[3] = (uint32_t) block_found.blockAttr.read |
              (uint32_t) block_found.blockAttr.write << 1 |
              (uint32_t) block_found.blockAttr.exec << 2 |
              (uint32_t) block_found.blockAttr.accessible << 3;
#ifdef DEBUG
      if(block_found.error ==1){
        debug_printf("error: %d\n", block_found.error);
      }
      else debug_printf("block found: %d\n", block_found.blockAttr.blockentryaddr);

#endif
      break;
    }
#ifdef UNIT_TESTS
    case 127: // Enable Privileged mode !TODO!: to remove with system calls in SVC instead
      __set_CONTROL( __get_CONTROL( ) & ~CONTROL_nPRIV_Msk ) ;
      break;
    case 128: // Disable Privileged mode !TODO!: to remove with system calls in SVC instead
      __set_CONTROL(__get_CONTROL() | CONTROL_nPRIV_Msk ); // switch to unprivileged Thread Mode
      __DMB();
      __ISB();
      __DSB();
      break;
#endif // UNIT_TESTS
    default:    // unknown SVC
      break;
  }
  // ...enable interrupts back
  __enable_irq();
}
