/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2024)                */
/*  Copyright (C) 2020-2024 Orange                                             */
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

#include "pip_interrupt_calls.h"
#include "Internal.h"
#include "nrf52.h"
#include "mal.h"

int_mask_t getIntState(
	void *childPartDescBlockLocalId
) {
	/* Retrieve the current partition descriptor block. */
	paddr currentPartDescBlockGlobalId = getCurPartition();

	/* Check that the child is a child of the current partition. */
	if (!(checkChildOfCurrPart(currentPartDescBlockGlobalId, childPartDescBlockLocalId)))
	{
		return ~0;
	}

	/* Return the interrupt state of the child partition. */
	return ((PDTable_t *) childPartDescBlockLocalId)->interruptState;
}

int_mask_t getSelfIntState(
	void
) {
	/* Retrieve the current partition descriptor block. */
	paddr currentPartDescBlockGlobalId = getCurPartition();

	/* Return the interrupt state of the current partition. */
	return ((PDTable_t *) currentPartDescBlockGlobalId)->interruptState;
}

void kernel_set_int_state(
	int_mask_t interruptState
) {
	/* Retrieve the current partition descriptor block. */
	paddr currentPartDescBlockGlobalId = getCurPartition();

	/* Set the interrupt state of the current partition. */
	((PDTable_t *) currentPartDescBlockGlobalId)->interruptState
		= interruptState;
}

void setIntState(
	int_mask_t interruptState
) {
	/* Retrieve the current partition descriptor block. */
	paddr currentPartDescBlockGlobalId = getCurPartition();

	/* Set the interrupt state of the current partition. */
	((PDTable_t *) currentPartDescBlockGlobalId)->interruptState
		= interruptState;

	if (getCurPartition() == getRootPartition())
	{
		if (interruptState == 0)
		{
			/* Enable BASEPRI masking. All interrupts lower
			 * or equal to the priority 1, i.e. interrupts
			 * below the SVCall in the vector table, are
			 * disabled. */
			__set_BASEPRI(1 << (8 - __NVIC_PRIO_BITS));
		}
		else
		{
			/* Disable BASEPRI masking. */
			__set_BASEPRI(0);
		}
	}
}
