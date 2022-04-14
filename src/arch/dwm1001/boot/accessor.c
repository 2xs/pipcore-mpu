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
#include "register_range.h"
#include "mal.h"

/*!
 * \brief Retrieve the register accessor from the register ID.
 *
 * \param registerId The register ID.
 *
 * \param registerAccessor The retrieved register accessor.
 *
 * \param registerAddress The retrieved register address.
 *
 * \return 1 if the function succeed, 0 otherwise.
 */
static uint32_t
retrieveRegisterAccessor(
	uint32_t           registerId,
	registerAccessor_t *registerAccessor,
	volatile uint32_t  **registerAddress
) {
	/* Check that the caller is the root partition. */
	if (getCurPartition() != getRootPartition())
	{
		return 0;
	}

	/* Retrieve the register range from the register ID. The
	 * register range is coded on the 16 most significant bits. */
	uint32_t registerRange = (registerId >> 16) & 0xffff;

	/* Check that the register range is not greater than or equal to
	 * the size of the register accessor ranges. */
	if (registerRange >= REGISTER_RANGE_NUMBER)
	{
		return 0;
	}

	/* Retrieve the register accessor range from the register range. */
	registerAccessorRange_t *registerAccessorRange =
		&registerAccessorRanges[registerRange];

	/* Retrieve the register index from the register ID. The
	 * register index is coded on the 16 least significant bits. */
	uint32_t registerIndex = registerId & 0x0000ffff;

	/* Check that the register index is not greater than or equal to
	 * the size of the register accessors. */
	if (registerIndex >= registerAccessorRange->registerAccessorSize)
	{
		return 0;
	}

	/* Calculation of the register address from the base address of
	 * its range and its index. */
	*registerAddress = (volatile uint32_t *)(registerAccessorRange->
		baseAddress + (registerIndex * sizeof(void *)));

	/* Retrieve the register accessor corresponding to the register
	 * index. */
	*registerAccessor =
		registerAccessorRange->registerAccessors[registerIndex];

	return 1;
}

extern uint32_t
in(uint32_t registerId, uint32_t *valueAddress)
{
	registerAccessor_t registerAccessor;
	volatile uint32_t  *registerAddress;
	uint32_t           success;

	success = retrieveRegisterAccessor
	(
		registerId,
		&registerAccessor,
		&registerAddress
	);

	if (!success)
	{
		return 0;
	}

	return registerAccessor
	(
		REGISTER_ACCESS_READ,
		registerAddress,
		valueAddress
	);
}

extern uint32_t
out(uint32_t registerId, uint32_t *valueAddress)
{
	registerAccessor_t registerAccessor;
	volatile uint32_t  *registerAddress;
	uint32_t           success;

	success = retrieveRegisterAccessor
	(
		registerId,
		&registerAccessor,
		&registerAddress
	);

	if (!success)
	{
		return 0;
	}

	return registerAccessor
	(
		REGISTER_ACCESS_WRITE,
		registerAddress,
		valueAddress
	);
}
