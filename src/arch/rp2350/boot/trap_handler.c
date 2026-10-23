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

/*!
 * \file trap_handler.c
 * \brief The mcause demux, and the report for a trap taken inside Pip.
 *
 * Replaces the ARM target's exception_handlers.c, which could dispatch on the
 * vector number because the hardware had a vector table. mtvec.MODE is 0
 * here, so every cause arrives at the one stub in trap_entry.S and the
 * demultiplexing is done below, on mcause.
 *
 * The "was it Pip or a partition?" question has already been answered before
 * anything here runs: the stub tests mstatus.MPP and only calls
 * trapHandlerC() for a trap taken in U-mode. That is the direct analogue of
 * the ARM entry point's "tst lr, #4" choosing between Kernel_Panic and the
 * real C handler.
 *
 * Milestone 1 scope. Only the ecall path is live. The access faults are
 * reported rather than serviced: the PMP refill of section 6 of the plan is
 * rung 4's work and belongs in its own fault_handler.c, together with
 * propagateFault(). The root partition's static regions are deliberately
 * exact powers of two (see link.ld), so nothing in rungs 5 and 6 should
 * fault at all -- and if something does, the report below says what and
 * where, which is the useful behaviour until the refill exists.
 */

#include <stdint.h>

#include "context.h"
#include "csr.h"
#include "rv_decode.h"
#include "stdio.h"
#include "trap_handler.h"

/*!
 * \brief The bit of mcause that distinguishes an interrupt from an exception.
 */
#define MCAUSE_INTERRUPT_BIT UINT32_C(0x80000000)

/*! \brief The mcause exception code, with the interrupt bit masked off. */
#define MCAUSE_CODE(mcause) ((mcause) & ~MCAUSE_INTERRUPT_BIT)

/*!
 * \brief The width of an ecall, which mepc has to be advanced past.
 *
 * ecall has no compressed form, so this is always four. Getting it wrong, or
 * omitting it, makes the ecall re-execute forever; ARM got the equivalent for
 * free from EXC_RETURN. The bring-up harness proved this path on silicon
 * before any of the rest of the port existed.
 */
#define ECALL_SIZE 4

/*!
 * \fn const char *mcauseName(uint32_t mcause)
 * \brief Renders an mcause value as text, for the fault reports.
 * \param mcause The value to render.
 * \return A static string naming the cause.
 */
static const char *mcauseName(uint32_t mcause)
{
	if ((mcause & MCAUSE_INTERRUPT_BIT) != 0) {
		switch (MCAUSE_CODE(mcause)) {
		case 3:  return "machine software interrupt";
		case 7:  return "machine timer interrupt";
		case 11: return "machine external interrupt";
		default: return "interrupt";
		}
	}

	switch (mcause) {
	case RVCSR_MCAUSE_CODE_VALUE_INSTR_ALIGN:
		return "instruction address misaligned";
	case RVCSR_MCAUSE_CODE_VALUE_INSTR_FAULT:
		return "instruction access fault";
	case RVCSR_MCAUSE_CODE_VALUE_ILLEGAL_INSTR:
		return "illegal instruction";
	case RVCSR_MCAUSE_CODE_VALUE_BREAKPOINT:
		return "breakpoint";
	case RVCSR_MCAUSE_CODE_VALUE_LOAD_ALIGN:
		return "load address misaligned";
	case RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT:
		return "load access fault";
	case RVCSR_MCAUSE_CODE_VALUE_STORE_ALIGN:
		return "store/AMO address misaligned";
	case RVCSR_MCAUSE_CODE_VALUE_STORE_FAULT:
		return "store/AMO access fault";
	case RVCSR_MCAUSE_CODE_VALUE_U_ECALL:
		return "ecall from U-mode";
	case RVCSR_MCAUSE_CODE_VALUE_M_ECALL:
		return "ecall from M-mode";
	default:
		return "unknown cause";
	}
}

/*!
 * \fn bool faultingAddress(const stackedContext_t *context, uint32_t *address)
 * \brief Works out the address a faulting access was aimed at.
 *
 * mtval is hardwired to zero on this core, so unlike ARM -- which read
 * MMFAR.ADDRESS -- there is nothing to read and the address has to be
 * recovered from the instruction. An instruction fetch fault needs no work:
 * mepc *is* the address. A load or store fault needs the instruction at mepc
 * decoded and its effective address computed.
 *
 * \param context The faulting partition's context.
 * \param address Where to store the address. Untouched unless true is
 *        returned.
 * \return true when an address could be determined.
 */
static bool faultingAddress(const stackedContext_t *context, uint32_t *address)
{
	const uint16_t *insn;
	uint16_t lo;
	uint16_t hi;

	insn = (const uint16_t *) (uintptr_t) context->mepc;
	lo = insn[0];

	/* The second halfword is read only once the first says there is one.
	 * On a compressed instruction at the very end of a block, reading it
	 * anyway could leave the block -- and this code runs in M-mode, where
	 * that would be a Pip fault rather than a partition one. */
	hi = 0;
	if (rv_insn_is_32bit(lo)) {
		hi = insn[1];
	}

	return rv_effective_address(context, lo, hi, address);
}

/*!
 * \fn void reportPartitionFault(const stackedContext_t *context, uint32_t mcause)
 * \brief Reports a partition trap that milestone 1 cannot service.
 *
 * What section 6 replaces with the PMP refill, and what the fault
 * propagation chain replaces with a walk up the parent partitions. Until
 * either exists, the useful thing is to say exactly what happened.
 *
 * \param context The faulting partition's context.
 * \param mcause The cause of the trap.
 */
static void reportPartitionFault(const stackedContext_t *context,
                                 uint32_t mcause)
{
	uint32_t address;

	printf("PIP: unhandled partition trap: mcause=%lu %s\n",
	       (unsigned long) mcause, mcauseName(mcause));
	printf("     mepc=0x%08lx sp=0x%08lx ra=0x%08lx\n",
	       (unsigned long) context->mepc,
	       (unsigned long) contextReadRegister(context, RV_REG_SP),
	       (unsigned long) contextReadRegister(context, RV_REG_RA));

	switch (mcause) {
	case RVCSR_MCAUSE_CODE_VALUE_INSTR_FAULT:
		/* mepc is the faulting address itself. */
		printf("     faulting fetch at 0x%08lx\n",
		       (unsigned long) context->mepc);
		break;
	case RVCSR_MCAUSE_CODE_VALUE_LOAD_FAULT:
	case RVCSR_MCAUSE_CODE_VALUE_STORE_FAULT:
		if (faultingAddress(context, &address)) {
			printf("     faulting access at 0x%08lx\n",
			       (unsigned long) address);
		} else {
			/* An encoding rv_effective_address() refuses, Zcmp
			 * among them. Section 6 treats this as a genuine
			 * fault to propagate rather than a refill. */
			printf("     effective address not decodable from"
			       " the instruction at mepc\n");
		}
		break;
	default:
		break;
	}
}

void trapHandlerC(stackedContext_t *context)
{
	uint32_t mcause = CSR_READ(mcause);

	if ((mcause & MCAUSE_INTERRUPT_BIT) != 0) {
		/* Nothing enables an interrupt in milestone 1: mie is zeroed
		 * in the reset path and no Xh3irq window is ever opened. One
		 * arriving means that is no longer true, so say so rather
		 * than resume and lose it. Section 7 is the design. */
		printf("PIP: unexpected interrupt: mcause=0x%08lx %s\n",
		       (unsigned long) mcause, mcauseName(mcause));
		for (;;) {
			// milestone 2 routes this to the root partition
		}
	}

	switch (mcause) {
	case RVCSR_MCAUSE_CODE_VALUE_U_ECALL:
		/* Step over the ecall before anything else can go wrong. Were
		 * this left until after the service ran, an early return out
		 * of the dispatch would resume on the ecall and loop. */
		context->mepc += ECALL_SIZE;

		/* The service number is in a7 and the arguments in a0 to a4,
		 * the Linux/RISC-V convention. ARM recovered the number from
		 * the instruction stream instead -- ((uint8_t *) pc)[-2] --
		 * which ecall cannot do, since it carries no immediate.
		 * ecall_handler.c is the next piece: it validates a7 against
		 * the service enum and writes the result back to the saved
		 * a0. */
		ecallHandler(context);
		break;

	default:
		reportPartitionFault(context, mcause);
		for (;;) {
			// section 6 refills a PMP region and retries here;
			// a genuine fault goes to propagateFault()
		}
	}

	loadContext(context);
}

void pipFault(uint32_t mcause, uint32_t mepc)
{
	/* Pip trapped. Nothing above this is recoverable: the kernel stack is
	 * intact but the instruction that used it was wrong, and there is no
	 * partition context to fall back to. */
	printf("PIP: UNRECOVERABLE ERROR!\n");
	printf("     trap in M-mode: mcause=0x%08lx %s mepc=0x%08lx\n",
	       (unsigned long) mcause, mcauseName(mcause),
	       (unsigned long) mepc);

	for (;;) {
		// deliberately no return path
	}
}
