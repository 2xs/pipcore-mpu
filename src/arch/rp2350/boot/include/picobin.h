/*******************************************************************************/
/*  © Université de Lille, The Pip Development Team (2015-2025)                */
/*  Copyright (C) 2020-2025 Orange                                             */
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

/*!
 * \file picobin.h
 * \brief The part of the RP2350 picobin image format Pip's image header needs.
 *
 * The bootrom refuses to start an image that does not carry a block loop with
 * an IMAGE_DEF block in its first 4K; there is no RP2040-style second stage
 * and a bare vector table is not accepted. start.S emits that block.
 *
 * Transcribed, under the vendor names, from the pico-sdk header
 * src/common/boot_picobin_headers/include/boot/picobin.h. The values are
 * plain literals with no type suffix, so that this header is also usable from
 * assembly.
 */

#ifndef PICOBIN_H
#define PICOBIN_H

#define PICOBIN_BLOCK_MARKER_START 0xffffded3
#define PICOBIN_BLOCK_MARKER_END   0xab123579

#define PICOBIN_BLOCK_ITEM_1BS_IMAGE_TYPE  0x42
#define PICOBIN_BLOCK_ITEM_1BS_ENTRY_POINT 0x44
#define PICOBIN_BLOCK_ITEM_2BS_LAST        (0x80 | 0x7f)

#define PICOBIN_IMAGE_TYPE_IMAGE_TYPE_LSB 0
#define PICOBIN_IMAGE_TYPE_IMAGE_TYPE_EXE 0x1

#define PICOBIN_IMAGE_TYPE_EXE_CPU_LSB   8
#define PICOBIN_IMAGE_TYPE_EXE_CPU_RISCV 1

#define PICOBIN_IMAGE_TYPE_EXE_CHIP_LSB    12
#define PICOBIN_IMAGE_TYPE_EXE_CHIP_RP2350 1

/*!
 * \brief The IMAGE_TYPE item payload for this target.
 *
 * EXE_SECURITY is deliberately left UNSPECIFIED, as the pico-sdk's own
 * RISC-V variant does in embedded_start_block.inc.S: the security states are
 * an Arm notion and a Hazard3 core is always Secure.
 */
#define PIP_PICOBIN_IMAGE_TYPE                                                \
	((PICOBIN_IMAGE_TYPE_IMAGE_TYPE_EXE                                    \
	  << PICOBIN_IMAGE_TYPE_IMAGE_TYPE_LSB) |                              \
	 (PICOBIN_IMAGE_TYPE_EXE_CPU_RISCV                                     \
	  << PICOBIN_IMAGE_TYPE_EXE_CPU_LSB) |                                 \
	 (PICOBIN_IMAGE_TYPE_EXE_CHIP_RP2350                                   \
	  << PICOBIN_IMAGE_TYPE_EXE_CHIP_LSB))

#endif /* PICOBIN_H */
