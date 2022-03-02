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

#ifndef __PIP_INTERRUPT_CALLS__
#define __PIP_INTERRUPT_CALLS__

#include <stdint.h>

typedef uint32_t int_mask_t;

/*!
 * \brief Retrieves the interrupt state of one of the current
 *        partition's children.
 *
 * \param childPartDescBlockLocalId The ID of the block containing the
 *        partition descriptor structure of one of the current
 *        partition's children.
 *
 * \return The interrupt state of one of the current partition's
 *         children, ~0 otherwise.
 */
int_mask_t __attribute__((section(".text_pip")))
getIntState(
	void *childPartDescBlockLocalId);

/*!
 * \brief Retrieves the interrupt state of the current partition.
 *
 * \return The interrupt state of the current partition.
 */
int_mask_t __attribute__((section(".text_pip")))
getSelfIntState(
	void);

/*!
 * \brief Sets the interrupt state of the current partition.
 *
 * \param interruptState The interrupt state to set for the current
 *        partition. A value of 0 indicates that the current partition
 *        does not wish to be interrupted, while a value other than 0
 *        indicates that the current partition wishes to be interrupted.
 *        If the current partition is the root partition, exceptions are
 *        enabled or disabled accordingly.
 */
void __attribute__((section(".text_pip")))
setIntState(
	int_mask_t interruptState);

/*!
 * \brief Sets the interrupt state of the current partition.
 *
 * \param interruptState The interrupt state to set for the current
 *        partition. A value of 0 indicates that the current partition
 *        does not wish to be interrupted, while a value other than 0
 *        indicates that the current partition wishes to be interrupted.
 */
void __attribute__((section(".text_pip")))
kernel_set_int_state(
	int_mask_t interruptState);

#endif /* __PIP_INTERRUPT_CALLS__ */
