/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2022)                */
/*  Copyright (C) 2020-2022 Orange                                             */
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

#ifndef __PIP_INTERFACE_H__
#define __PIP_INTERFACE_H__

#include <stdint.h>
#include <stddef.h>

#include "userconstants.h"
#include "context.h"
#include "ADT.h"

/*!
 * \brief This structure defines the interface that PIP provides to the
 *        root partition.
 */
typedef struct pip_interface_s
{
	/*!
	 * \brief The ID of the block containing the partition
	 *        descriptor of the root partition.
	 */
	uint32_t *partDescId;

	/*!
	 * \brief The initial context of the root partition.
	 */
	user_context_t context;

	/*!
	 * \brief List containing the attributes of the MPU blocks.
	 */
	blockAttr_t mpu[MPU_REGIONS_NB];

	/*!
	 * \brief The start of the unused ROM.
	 */
	uint32_t romUnusedStart;

	/*!
	 * \brief The end of the ROM.
	 */
	uint32_t romEnd;

	/*!
	 * \brief The start of the unused RAM.
	 */
	uint32_t ramUnusedStart;

	/*!
	 * \brief The end of the RAM.
	 */
	uint32_t ramEnd;

} pip_interface_t;

#endif /* __PIP_INTERFACE_H__ */
