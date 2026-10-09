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
 * \file test.h
 * \brief Minimal check harness for the host unit tests.
 *
 * Header-only and dependency-free: each test is a single translation unit
 * with its own main(), and its exit status is what gates the build.
 */

#ifndef TEST_H
#define TEST_H

#include <stdint.h>
#include <stdio.h>

static unsigned testChecks = 0;
static unsigned testFailures = 0;

/*!
 * \fn void testCheck(const char *file, int line, const char *what, const char *context, uint32_t actual, uint32_t expected)
 * \brief Records one check and reports it when it fails.
 * \param file The file the check comes from.
 * \param line The line the check comes from.
 * \param what The source text of the checked expression.
 * \param context A caller-supplied label, or NULL.
 * \param actual The value obtained.
 * \param expected The value expected.
 */
static inline void testCheck(const char *file, int line, const char *what,
                             const char *context, uint32_t actual,
                             uint32_t expected)
{
	testChecks++;
	if (actual == expected) {
		return;
	}
	testFailures++;
	printf("%s:%d: FAIL: %s", file, line, what);
	if (context != NULL) {
		printf(" [%s]", context);
	}
	printf(": got 0x%08x, expected 0x%08x\n", actual, expected);
}

/*!
 * \fn int testReport(const char *name)
 * \brief Prints the summary of a test and yields its exit status.
 * \param name The name of the test.
 * \return 0 when every check passed, 1 otherwise.
 */
static inline int testReport(const char *name)
{
	if (testFailures != 0) {
		printf("%s: %u of %u checks FAILED\n", name, testFailures,
		       testChecks);
		return 1;
	}
	printf("%s: %u checks passed\n", name, testChecks);
	return 0;
}

/*! \brief Checks that an expression equals an expected value. */
#define CHECK(actual, expected) \
	testCheck(__FILE__, __LINE__, #actual, NULL, (uint32_t)(actual), \
	          (uint32_t)(expected))

/*! \brief Same as CHECK, with a label naming the case. */
#define CHECK_AT(context, actual, expected) \
	testCheck(__FILE__, __LINE__, #actual, (context), (uint32_t)(actual), \
	          (uint32_t)(expected))

#endif /* TEST_H */
