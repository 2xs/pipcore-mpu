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

#ifndef __STACK_H__
#define __STACK_H__

#include <stdint.h>

#include "context.h"
#include "scs.h"

/*!
 * \brief Resets the context stack pointer register to the stack
 *        address before an exception.
 *
 * \param context A stacked context in which to reset the stack
 *        pointer register.
 *
 * \warning After calling this function, the interrupt handler
 *          cannot return from an exception.
 *
 * \see Armv7-M Architecture - Reference Manual
 *      B1.5.8 Exception return behavior
 */
static inline void
resetInitialSp(stackedContext_t *context)
{
	if (context->isBasicFrame)
	{
		basicFrame_t *frame = &context->basicFrame;
		uint32_t frameSize = 0x20;
		uint32_t forceAlign = CCR.STKALIGN;
		uint32_t spMask = ((frame->xpsr >> 9) & forceAlign) << 2;
		frame->sp = (frame->sp + frameSize) | spMask;
	}
	else
	{
		extendedFrame_t *frame = &context->extendedFrame;
		uint32_t frameSize = 0x68;
		uint32_t forceAlign = 1;
		uint32_t spMask = ((frame->xpsr >> 9) & forceAlign) << 2;
		frame->sp = (frame->sp + frameSize) | spMask;
	}
}

#endif /* __STACK_H__ */
