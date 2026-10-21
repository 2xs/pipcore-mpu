###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2025)                #
#  Copyright (C) 2020-2025 Orange                                             #
#                                                                             #
#  This software is a computer program whose purpose is to run a minimal,     #
#  hypervisor relying on proven properties such as memory isolation.          #
#                                                                             #
#  This software is governed by the CeCILL license under French law and       #
#  abiding by the rules of distribution of free software.  You can  use,      #
#  modify and/ or redistribute the software under the terms of the CeCILL     #
#  license as circulated by CEA, CNRS and INRIA at the following URL          #
#  "http://www.cecill.info".                                                  #
#                                                                             #
#  As a counterpart to the access to the source code and  rights to copy,     #
#  modify and redistribute granted by the license, users are provided only    #
#  with a limited warranty  and the software's author,  the holder of the     #
#  economic rights,  and the successive licensors  have only  limited         #
#  liability.                                                                 #
#                                                                             #
#  In this respect, the user's attention is drawn to the risks associated     #
#  with loading,  using,  modifying and/or developing or reproducing the      #
#  software by the user in light of its specific status of free software,     #
#  that may mean  that it is complicated to manipulate,  and  that  also      #
#  therefore means  that it is reserved for developers  and  experienced      #
#  professionals having in-depth computer knowledge. Users are therefore      #
#  encouraged to load and test the software's suitability as regards their    #
#  requirements in conditions enabling the security of their systems and/or   #
#  data to be ensured and,  more generally, to use and operate it in the      #
#  same conditions as regards security.                                       #
#                                                                             #
#  The fact that you are presently reading this means that you have had       #
#  knowledge of the CeCILL license and that you accept its terms.             #
###############################################################################

# Host unit tests for the parts of the rp2350 target that are pure
# computation: the PMP NAPOT encoding and the instruction decoder the PMP
# refill handler needs because mtval is hardwired to zero on this silicon.
#
# These are the only pieces of the port that are cheaply testable off-target,
# so they are tested here rather than on hardware. Nothing in this directory
# needs a cross toolchain or a configured toolchain.mk: it builds and runs
# with the host compiler alone.
#
#     make -C src/arch/rp2350/test check

HERE := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
BOOT_DIR := $(HERE)../boot
BUILD_DIR := $(HERE)build

CC ?= cc
# The boot include directory goes in with -iquote, not -I: it holds the
# target's own stdio.h, and on the <> search path that would shadow the host's.
CFLAGS := -std=c11 -O2 -Wall -Wextra -Werror\
          -iquote $(BOOT_DIR)/include -iquote $(HERE)

# One test binary per source file, each with its own main().
TESTS := test_pmp test_rv_decode
TEST_BINARIES := $(addprefix $(BUILD_DIR)/,$(TESTS))

check: $(TEST_BINARIES)
	@status=0; \
	for test in $(TEST_BINARIES); do \
		$$test || status=1; \
	done; \
	exit $$status

$(BUILD_DIR)/test_pmp: $(HERE)test_pmp.c $(HERE)test.h\
                       $(BOOT_DIR)/include/pmp.h | $(BUILD_DIR)
	$(CC) $(CFLAGS) $< -o $@

$(BUILD_DIR)/test_rv_decode: $(HERE)test_rv_decode.c $(HERE)test.h\
                             $(BOOT_DIR)/rv_decode.c\
                             $(BOOT_DIR)/include/rv_decode.h\
                             $(BOOT_DIR)/include/context.h | $(BUILD_DIR)
	$(CC) $(CFLAGS) $< $(BOOT_DIR)/rv_decode.c -o $@

$(BUILD_DIR):
	mkdir -p $@

# Checks the register and CSR constants transcribed into the two boot headers
# against the pico-sdk they were taken from. Not part of "check": it needs a
# pico-sdk checkout, which CI does not have.
#
#     make -C src/arch/rp2350/test sdkcheck PICO_SDK=<path>
sdkcheck:
	@test -n "$(PICO_SDK)" || { \
		echo 'set PICO_SDK to a pico-sdk checkout' >&2; exit 2; }
	$(HERE)check-sdk-regs.sh $(PICO_SDK)

clean:
	rm -rf $(BUILD_DIR)

.PHONY: check sdkcheck clean
