/*******************************************************************************/
/*  © Université Lille 1, The Pip Development Team (2015-2021)                 */
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

/**
 * \file ADT.h
 * \brief ARM MAL structures
 */

#ifndef ADT_H
#define ADT_H

#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>
#include "userconstants.h"

/* Paddr */
typedef uint32_t* paddr;

/**
 * \struct block
 * \brief Block structure
 */
typedef struct block
{
	uint32_t* startAddr ; //!< The block's start address
	uint32_t* endAddr   ; //!< The block's end address (or pointer to the next free slot if it is one)
}__attribute__((packed)) block_t;


/**
 * \struct MPUIndex
 * \brief MPU index structure
 */
typedef struct MPUIndex
{
	uint32_t MPUi; //!< Index of the slot in the kernel structure containing it // TODO : compute index size
}__attribute__((packed)) MPUIndex_t;

/**
 * \struct MPUEntry
 * \brief MPU entry structure
 */
typedef struct MPUEntry
{
    block_t mpublock        ;   //!< Block present in memory
    MPUIndex_t mpuindex     ;   //!< Slot index in its kernel structure
    bool read               ;   //!< Read permission
    bool write              ;   //!< Write permission
    bool exec               ;   //!< Exec permission
    bool present            ;   //!< Block present
    bool accessible         ;   //!< block accessible
}__attribute__((packed)) MPUEntry_t;

/**
 * \struct Sh1Entry
 * \brief Sh1 entry structure
 */
typedef struct Sh1Entry
{
    uint32_t* PDchild          ;   //!< Pointer to the child the block is shared with // TODO: PDTable_t ?
    bool PDflag                ;   //!< Block content is a PD
    uint32_t* inChildLocation  ;   //!< Pointer to the slot where the block lies in the child partition
}__attribute__((packed)) Sh1Entry_t;

/**
 * \struct SCEntry
 * \brief SC entry structure
 */
typedef struct SCEntry
{
    uint32_t* origin  ;   //!< Pointer to the original (sub)block // TODO: MPUEntry_t
    uint32_t* next    ;   //!< Pointer to the next subblock // TODO: MPUEntry_t
}__attribute__((packed)) SCEntry_t;

/**
 * \struct PDTable
 * \brief PDTable structure
 */
typedef struct PDTable
{
    uint32_t* structure     ;   //!< Pointer to the first kernel structure of the structure linked list
    uint32_t* firstfreeslot ;   //!< Pointer to the first free slot in one of the kernel structures (if any)
    uint32_t nbfreeslots    ;   //!< Number of free slots left
    uint32_t nbprepare      ;   //!< Number of Prepare done on this partition
    uint32_t* parent        ;   //!< Pointer to the parent partition
    MPUEntry_t* blocks[MPU_REGIONS_NB]   ;   //!< List of pointers to enabled blocks
    uint32_t LUT[MPU_REGIONS_NB*2]    ;   //!< MPU registers' configuration sequence
}__attribute__((packed)) PDTable_t;

#endif /* ADT_H */
