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

/*
 * The image header the RP2350 bootrom requires, and the reset path.
 *
 * This file replaces both exception_entrypoints.S's Reset_Handler and crt.S's
 * 128-entry ARM vector table, which has no analogue here: RISC-V traps go
 * through mtvec, and mtvec is set below.
 */

#include "picobin.h"

/* Linker relaxation would let the assembler reach the symbols below through
 * gp. gp is a general-purpose register that also appears in a partition's
 * saved context, so Pip never addresses anything relative to it: see the
 * -mno-relax rationale in the build configuration. */
.option norelax

/*
 * The picobin IMAGE_DEF block.
 *
 * The bootrom searches the first 4K of the image for a block loop and refuses
 * to boot without one; link.ld therefore places this section first. A single
 * block whose link word is zero is a loop of one, which is what the pico-sdk
 * emits for an image that is not hashed or signed.
 *
 * The ENTRY_POINT item is not optional on this architecture. The bootrom's
 * default RISC-V entry point is the first byte of the image, which here is
 * this block rather than code, so the entry address has to be stated. The
 * item also carries the initial sp, which Reset_Handler sets again anyway.
 *
 * Layout and item encodings follow the pico-sdk's own
 * src/rp2_common/pico_crt0/embedded_start_block.inc.S.
 */
.section .picobin_block, "a"
.p2align 2
picobinBlock:
	.word PICOBIN_BLOCK_MARKER_START

	.byte PICOBIN_BLOCK_ITEM_1BS_IMAGE_TYPE
	.byte 1					/* 1 word of payload */
	.hword PIP_PICOBIN_IMAGE_TYPE

	.byte PICOBIN_BLOCK_ITEM_1BS_ENTRY_POINT
	.byte 3					/* 3 words to the next item */
	.byte 0					/* padding */
	.byte 0					/* padding */
	.word Reset_Handler
	.word __pipStackTop

	.byte PICOBIN_BLOCK_ITEM_2BS_LAST
	.hword ( picobinBlockEnd - picobinBlock - 16 ) / 4
	.byte 0
	.word 0					/* the loop points back here */
	.word PICOBIN_BLOCK_MARKER_END
picobinBlockEnd:

/*
 * The reset path.
 *
 * M-mode at reset already is the privileged context, so there is nothing like
 * the ARM target's PendSV self-trigger, whose only purpose was to reach an
 * exception context for Boot_Handler.
 */
.section .text.Reset_Handler, "ax", @progbits
.p2align 2
.globl Reset_Handler
.type Reset_Handler, @function
Reset_Handler:
	/* The stack has to be valid before any call. */
	la	sp, __pipStackTop

	/* mtvec.MODE = 0, direct: every trap enters one stub, which demuxes
	 * on mcause. mtvec.BASE is bits 31:2 and MODE is bits 1:0, so this
	 * relies on trapEntry being 4-byte aligned, which it declares and
	 * check-image.sh checks. Masking here instead would silently point
	 * mtvec two bytes short of the stub. */
	la	t0, trapEntry
	csrw	mtvec, t0

	/* mscratch holds Pip's kernel stack top while a partition runs, and
	 * zero while Pip runs. The trap stub swaps sp with it and tests the
	 * result, which is how a trap taken inside Pip is told apart from a
	 * trap taken in a partition. */
	csrw	mscratch, zero

	/* Clear MIE, and with it MPRV: nothing is enabled yet. A trap entry
	 * clears MIE in hardware too, which is why the ARM target's cpsid i
	 * at every exception entry has no counterpart here. */
	csrw	mstatus, zero
	csrw	mie, zero

	tail	_start
.size Reset_Handler, . - Reset_Handler
