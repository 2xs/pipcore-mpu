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

/**
 * \file ADT.h
 * \brief RP2350 MAL structures
 */

#ifndef ADT_H
#define ADT_H

#include <stdint.h>
#include <stddef.h>

#include "pip_interrupt_calls.h"
#include "userconstants.h"
#include "context.h"

/* bool */
typedef _Bool boolean;
#define true    1
#define false   0
#define bool boolean

/*
 * The VIDT index map.
 *
 * On ARMv7-M this was dictated by hardware: a VIDT index was the ARM vector
 * number, read out of ICSR.VECTACTIVE, which is why CLI_SAVE_INDEX,
 * STI_SAVE_INDEX and DOUBLE_FAULT_LEVEL had to squat on reserved vector
 * slots. RISC-V in direct mode has no hardware vector table, so the map is
 * Pip's to choose, and it is chosen to total exactly 56 -- the same as the
 * ARM target. That keeps sizeof(vidt_t) at 4 + 56*4 = 228, so getVidtSize()
 * and the model's vidtSize both keep the values they have today.
 *
 *     0-51   external IRQ i -> index i, read from h3.meinext
 *     52     CLI_SAVE_INDEX      (was 8)
 *     53     STI_SAVE_INDEX      (was 9)
 *     54     DOUBLE_FAULT_LEVEL  (was 10)
 *     55     FAULT_INDEX, every propagated synchronous fault
 *
 * Collapsing all fault classes onto one vector matches what propagateFault
 * already does.
 */

/*!
 * \def RP2350_IRQ_NUMBER
 *
 * \brief The number of external interrupts on the RP2350.
 */
#define RP2350_IRQ_NUMBER 52

/*!
 * \def RISCV_EXCEPTION_NUMBER
 *
 * \brief The number of synchronous fault entries: one generic vector.
 */
#define RISCV_EXCEPTION_NUMBER 1

/*!
 * \def SOFT_INTERRUPT_NUMBER
 *
 * \brief The number of software interrupts: CLI_SAVE, STI_SAVE and
 *        DOUBLE_FAULT.
 */
#define SOFT_INTERRUPT_NUMBER 3

/*!
 * \def VIDT_INTERRUPT_NUMBER
 *
 * \brief The number of exception entries in the VIDT.
 *
 * Parenthesised, unlike the ARM definition it replaces, which expanded to a
 * bare sum.
 */
#define VIDT_INTERRUPT_NUMBER \
	(RP2350_IRQ_NUMBER + RISCV_EXCEPTION_NUMBER + SOFT_INTERRUPT_NUMBER)

/* Paddr */
typedef void* paddr;

/* index */
typedef uint32_t Coq_index;

/* Require for the Sh1Entry_t structure. */
struct PDTable;

/**
 * \struct block
 * \brief Block structure
 */
typedef struct block
{
	void *startAddr ; //!< The block's start address
	void *endAddr   ; //!< The block's end address (or pointer to the next free slot if it is one)
}__attribute__((packed)) block_t;

/**
 * \struct BlockIndex
 * \brief MPU index structure
 */
typedef struct BlockIndex
{
	uint32_t i; //!< Index of the slot in the kernel structure containing it // TODO : compute index size
}__attribute__((packed)) BlockIndex_t;

/**
 * \struct BlockEntry
 * \brief MPU entry structure
 */
typedef struct BlockEntry
{
	block_t blockrange      ;   //!< Block present in memory
	BlockIndex_t blockindex ;   //!< Slot index in its kernel structure
	bool read               ;   //!< Read permission
	bool write              ;   //!< Write permission
	bool exec               ;   //!< Exec permission
	bool present            ;   //!< Block present
	bool accessible         ;   //!< block accessible
} BlockEntry_t;

/**
 * \struct Sh1Entry
 * \brief Sh1 entry structure
 */
typedef struct Sh1Entry
{
	struct PDTable *PDchild    ;   //!< Pointer to the child the block is shared with
	uint32_t *inChildLocation  ;   //!< Pointer to the slot where the block lies in the child partition
	bool PDflag                ;   //!< Block content is a PD
}__attribute__((packed)) Sh1Entry_t;

/**
 * \struct SCEntry
 * \brief SC entry structure
 */
typedef struct SCEntry
{
	struct BlockEntry *origin  ;   //!< Pointer to the original (sub)block
	struct BlockEntry *next    ;   //!< Pointer to the next subblock
}__attribute__((packed)) SCEntry_t;

/**
 * \struct KStructure
 * \brief A kernel structure
 */
typedef struct KStructure
{
	BlockEntry_t blocks[KERNELSTRUCTUREENTRIESNB]   ;  //!< BLK structure
	Sh1Entry_t sh1[KERNELSTRUCTUREENTRIESNB]        ;  //!< Sh1 structure
	SCEntry_t sc[KERNELSTRUCTUREENTRIESNB]          ;  //!< SC structure
	struct KStructure *next                         ;  //!< Pointer to the next kernel structure
} KStructure_t;

typedef struct vidt_s
{
	uint32_t currentInterrupt;
	stackedContext_t *contexts[VIDT_INTERRUPT_NUMBER];
} vidt_t;

/**
 * \struct PDTable
 * \brief PDTable structure
 */
typedef struct PDTable
{
	struct KStructure *structure        ;   //!< Pointer to the first kernel structure of the structure linked list
	void* firstfreeslot                 ;   //!< Pointer to the first free slot in one of the kernel structures (if any)
	uint32_t nbfreeslots                ;   //!< Number of free slots left
	uint32_t nbprepare                  ;   //!< Number of Prepare done on this partition
	struct PDTable *parent              ;   //!< Pointer to the parent partition
	BlockEntry_t *mpu[MPU_REGIONS_NB]   ;   //!< List of pointers to enabled blocks
	uint32_t LUT[MPU_REGIONS_NB*2]      ;   //!< MPU registers' configuration sequence
	BlockEntry_t *vidtAddr              ;   //!< Address of the VIDT.
	int_mask_t interruptState           ;   //!< The interrupt state of the partition.
} PDTable_t;

/**
 * \struct blockAttr
 * \brief blockAttr structure
 */
typedef struct blockAttr
{
	uint32_t *blockentryaddr    ;   //!< Pointer to the block's address
	block_t blockrange          ;   //!< Block present in memory
	bool read                   ;   //!< Read permission
	bool write                  ;   //!< Write permission
	bool exec                   ;   //!< Exec permission
	bool accessible             ;   //!< block accessible
}__attribute__((packed)) blockAttr_t;

/**
 * \struct blockOrError
 * \brief blockOrError union structure
 *          When the block is empty, the error flag is set to -1,
 *          otherwise contains a block's public attributes
 */
typedef union blockOrError_t
{
	int32_t error               ;   //!< Error -1 for an empty block
	blockAttr_t blockAttr       ;   //!< A block's publicly exposed attributes
}__attribute__((packed)) blockOrError;

#endif /* ADT_H */
