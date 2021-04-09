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
/*****************************************/
//TODOs: write descriptions in structures
/*****************************************/
/* bool */
/*typedef uint32_t bool;

#define true    1
#define false   0*/

/* Paddr */
//typedef uintptr_t paddr;
typedef uint32_t* paddr;

/* Index */
//typedef uint32_t index;

/**
 * \struct PDTable
 * \brief PDTable structure
 */
typedef struct PDTable
{
    uint32_t* structure    ;   //!< Page present in memory
    uint32_t* firstfreeslot    ;   //!< Page present in memory
    uint32_t nbfreeslots    ;   //!< Page present in memory
    uint32_t nbprepare    ;   //!< Page present in memory
    uint32_t* parent    ;   //!< Page present in memory
}__attribute__((packed)) PDTable_t;

//#define DEFAULT_PD_TABLE(X) PDTable_t X = {NULL, NULL, 0, 0, NULL}
//static const PDTable_t DEFAULT_PD_TABLE = {NULL, NULL, 0, 0, NULL};

/**
 * \struct block
 * \brief Block structure
 */
typedef struct block
{
	uint32_t* startAddr;
	uint32_t* endAddr;
}__attribute__((packed)) block_t;
//} block_t;
//#define DEFAULT_BLOCK(X) block_t X = {0, 0}
//static const block_t DEFAULT_BLOCK = {0, 0};


/**
 * \struct MPUIndex
 * \brief MPU index structure
 */
typedef struct MPUIndex
{
	uint32_t MPUi; // TODO : compute index size
}__attribute__((packed)) MPUIndex_t;

//#define DEFAULT_MPU_INDEX(X) MPUIndex_t X = {-1}// will fail TODO: set max kernel entries + 1
//static const MPUIndex_t DEFAULT_MPU_INDEX = {-1};

/**
 * \struct MPUEntry
 * \brief MPU entry structure
 */
typedef struct MPUEntry
{
    block_t mpublock    ;   //!< Page present in memory
    MPUIndex_t mpuindex    ;   //!< Page present in memory
    bool read         ;   //!< Read-only if clear, readwrite if set
    bool write       ;   //!< Supervisor level only if clear
    bool exec   ;   //!< Has the page been accessed since last refresh?
    bool present      ;   //!< Has the page been written to since last refresh?
    bool accessible     ;   //!< Amalgamation of unused and reserved bits
}__attribute__((packed)) MPUEntry_t;

//#define DEFAULT_MPU_ENTRY(X) MPUEntry_t X = {DEFAULT_BLOCK(B), DEFAULT_MPU_INDEX(I), false, false, false, false, false}
//static const MPUEntry_t DEFAULT_MPU_ENTRY = {DEFAULT_BLOCK, DEFAULT_MPU_INDEX, false, false, false, false, false};

/**
 * \struct Sh1Entry
 * \brief Sh1 entry structure
 */
typedef struct Sh1Entry
{
    uint32_t* PDchild    ;   //!< Page present in memory // TODO: PDTable_t ?
    bool PDflag    ;   //!< Page present in memory
    uint32_t* inChildLocation         ;   //!< Read-only if clear, readwrite if set
}__attribute__((packed)) Sh1Entry_t;

//#define DEFAULT_SH1_ENTRY(X) Sh1Entry_t X = {NULL, false, NULL} // TODO: fail because not pointer
//static const Sh1Entry_t DEFAULT_SH1_ENTRY = {NULL, false, NULL}; // TODO: fail because not pointer

/**
 * \struct SCEntry
 * \brief SC entry structure
 */
typedef struct SCEntry
{
    uint32_t* origin    ;   //!< Page present in memory // TODO: MPUEntry_t
    uint32_t* next    ;   //!< Page present in memory // TODO: MPUEntry_t
}__attribute__((packed)) SCEntry_t;

//#define DEFAULT_SC_ENTRY(X) SCEntry_t X = {NULL, NULL} // TODO: fail because not pointers
//static const SCEntry_t DEFAULT_SC_ENTRY = {NULL, NULL}; // TODO: fail because not pointer

#endif /* ADT_H */
