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

#ifndef __CONTEXT_H__
#define __CONTEXT_H__

#include <stdint.h>

/*!
 * \def CONTEXT_REGISTER_NUMBER
 *
 * \brief The register number of a context.
 */
#define CONTEXT_REGISTER_NUMBER 17

/*!
 * \def CONTEXT_VALID_VALUE
 *
 * \brief An arbitrary value used to identify a valid context.
 */
#define CONTEXT_VALID_VALUE 0x41b06b8a

/*!
 * \brief Enumeration of registers to be stored for a context.
 *
 * \warning Do not change the register number in the enumeration.
 */
typedef enum context_register_e
{
	SP   = 0  , /*!< PSP register  */
	R4   = 1  , /*!< R4 register   */
	R5   = 2  , /*!< R5 register   */
	R6   = 3  , /*!< R6 register   */
	R7   = 4  , /*!< R7 register   */
	R8   = 5  , /*!< R8 register   */
	R9   = 6  , /*!< R9 register   */
	R10  = 7  , /*!< R10 register  */
	R11  = 8  , /*!< R11 register  */
	R0   = 9  , /*!< R0 register   */
	R1   = 10 , /*!< R1 register   */
	R2   = 11 , /*!< R2 register   */
	R3   = 12 , /*!< R3 register   */
	R12  = 13 , /*!< R12 register  */
	LR   = 14 , /*!< LR register   */
	PC   = 15 , /*!< PC register   */
	XPSR = 16   /*!< xPSR register */
} context_register_t;

/*!
 * \brief Structure representing a context as stacked by an assembly
 *        entry point.
 */
typedef struct stacked_context_s
{
	/*!
	 * \brief Registers stacked by an assembly entry point.
	 */
	uint32_t registers[CONTEXT_REGISTER_NUMBER];
} stacked_context_t;

/*!
 * \brief Structure representing a context as stored by the yield
 *        system call.
 */
typedef struct user_context_s
{
	/*!
	 * \brief The validity of the structure: a zero value indicates
	 *        an invalid structure, a non-zero value indicates a
	 *        valid structure.
	 */
	uint32_t valid;

	/*!
	 * \brief The state in which the partition wishes to be at the
	 *        next yield.
	 */
	uint32_t pipflags;

	/*!
	 * \brief All stored registers by the SVC handler.
	 */
	uint32_t registers[CONTEXT_REGISTER_NUMBER];
} user_context_t;

#endif /* __CONTEXT_H__ */
