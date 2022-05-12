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

#ifndef __ACCESSOR_H__
#define __ACCESSOR_H__

#include <stdint.h>

#include "register.h"

/*!
 * \brief Read only accessor.
 *
 * \param registerAccessType The type of access requested by the
 *        caller.
 *
 * \param registerAddress The address from which to read the
 *        value to write to valueAddress.
 *
 * \param valueAddress The address where to write the value read
 *        from registerAddress.
 *
 * \return 1 if the read or the write succeed, 0 otherwise.
 */
extern uint32_t
registerAccessRead(
	registerAccessType_t registerAccessType,
	volatile uint32_t *registerAddress,
	uint32_t *valueAddress
);

/*!
 * \brief Write only accessor.
 *
 * \param registerAccessType The type of access requested by the
 *        caller.
 *
 * \param registerAddress The address where to write the value
 *        read from valueAddress.
 *
 * \param valueAddress The address from which to read the value
 *        to write to registerAddress.
 *
 * \return 1 if the read or the write succeed, 0 otherwise.
 */
extern uint32_t
registerAccessWrite(
	registerAccessType_t registerAccessType,
	volatile uint32_t *registerAddress,
	uint32_t *valueAddress
);

/*!
 * \brief Read/Write accessor.
 *
 * \param registerAccessType The type of access requested by the
 *        caller.
 *
 * \param registerAddress The address where to write the value
 *        read from valueAddress or the address from which to
 *        read the value to write to valueAddress.
 *
 * \param valueAddress The address where to write the value read
 *        from registerAddress or the address from which to read
 *        the value to write to registerAddress.
 *
 * \return 1 if the read or the write succeed, 0 otherwise.
 */
extern uint32_t
registerAccessReadWrite(
	registerAccessType_t registerAccessType,
	volatile uint32_t *registerAddress,
	uint32_t *valueAddress
);

/*!
 * \brief The in SVC writes the value of the register designated
 *        by its ID to the valueAddress address.
 *
 * \param registerId The ID of the register to read.
 *
 * \param valueAddress The address where to write the value
 *        read.
 *
 * \param 1 if the read succeed, 0 otherwise.
 */
extern uint32_t
in(
	uint32_t registerId,
	uint32_t *valueAddress
);

/*!
 * \brief The out SVC writes the value at valueAddress address
 *        to the register designated by its ID.
 *
 * \param registerId The ID of the register to write.
 *
 * \param valueAddress The address where the value to be written
 *        is located.
 *
 * \param 1 if the read succeed, 0 otherwise.
 */
extern uint32_t
out(
	uint32_t registerId,
	uint32_t *valueAddress
);

#endif /* __ACCESSOR_H__ */
