/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
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

#include <stdint.h>

#include "accessor.h"
#include "context.h"
#include "nrf52.h"
#include "register.h"
#include "regid.h"
#include "mal.h"

#define MEMMANAGE_IRQ_NUMBER 4

extern void
Fault_Handler_C_Irq(
	stackedContext_t *ctx,
	uint32_t irq
) __attribute__((noreturn));

extern int
registerAccessRead(
	registerAccessType_t type,
	volatile uint32_t *reg,
	uint32_t *val
) {
	if (type != REGISTER_ACCESS_READ)
	{
		return 0;
	}

	*val = *reg;
	/*
	 * To guarantee that the side effects of a previous SCS access
	 * are visible, software can execute a DSB instruction followed
	 * by an ISB instruction.
	 */
	__DSB();
	__ISB();

	return 1;
}

extern int
registerAccessWrite(
	registerAccessType_t type,
	volatile uint32_t *reg,
	uint32_t *val
) {
	if (type != REGISTER_ACCESS_WRITE)
	{
		return 0;
	}

	*reg = *val;
	/*
	 * To guarantee that the side effects of a previous SCS access
	 * are visible, software can execute a DSB instruction followed
	 * by an ISB instruction.
	 */
	__DSB();
	__ISB();

	return 1;
}

extern int
registerAccessReadWrite(
	registerAccessType_t type,
	volatile uint32_t *reg,
	uint32_t *val
) {
	switch (type)
	{
		case REGISTER_ACCESS_READ:
		{
			*val = *reg;
			/*
			 * To guarantee that the side effects of a
			 * previous SCS access are visible, software can
			 * execute a DSB instruction followed by an ISB
			 * instruction.
			 */
			__DSB();
			__ISB();
			break;
		}
		case REGISTER_ACCESS_WRITE:
		{
			*reg = *val;
			/*
			 * To guarantee that the side effects of a
			 * previous SCS access are visible, software can
			 * execute a DSB instruction followed by an ISB
			 * instruction.
			 */
			__DSB();
			__ISB();
			break;
		}
		default:
		{
			return 0;
		}
	}

	return 1;
}

static void
doAccess(
	stackedContext_t *ctx,
	registerAccessType_t type,
	uint32_t id,
	uint32_t *val
) {
	registerAccessor_t accessor;
	volatile uint32_t *reg;

	if (getRootPartition() != getCurPartition())
	{
		goto fault;
	}

	if (id >= ARRAY_SIZE)
	{
		goto fault;
	}

	accessor = REGISTER_ID_TO_ACCESSOR[id].accessor;
	reg      = REGISTER_ID_TO_ACCESSOR[id].address;

	if (accessor(type, reg, val) == 0)
	{
		goto fault;
	}

	return;

fault:
	Fault_Handler_C_Irq(ctx, MEMMANAGE_IRQ_NUMBER);
}

extern void
in(stackedContext_t *ctx, uint32_t id, uint32_t *val)
{
	doAccess(ctx, REGISTER_ACCESS_READ, id, val);
}

extern void
out(stackedContext_t *ctx, uint32_t id, uint32_t *val)
{
	doAccess(ctx, REGISTER_ACCESS_WRITE, id, val);
}
