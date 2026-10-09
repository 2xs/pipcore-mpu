###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2025)                #
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
include ../../toolchain.mk


# The toolchain and the machine flags come from toolchain.mk, which
# configure.sh generates for the selected target. Note that this invokes ld
# directly rather than linking through GCC, hence TOOL_PREFIX rather than
# toolchain.mk's LD. ARCH_CRT0_CFLAGS holds the machine flags only: the crt0
# is a separate binary and must not inherit Pip's own definitions.

CC      := $(TOOL_PREFIX)gcc
LD      := $(TOOL_PREFIX)ld
OBJCOPY := $(TOOL_PREFIX)objcopy
RM      := rm

CFLAGS          = -Wall
CFLAGS         += -Wextra
CFLAGS         += -Werror
CFLAGS         += $(ARCH_CRT0_CFLAGS)
CFLAGS         += -I $(FAE_INCLUDE_DIRECTORY)
ifdef DEBUG
CFLAGS         += -Og
CFLAGS         += -ggdb
else
CFLAGS         += -Os
endif

LDFLAGS         = -T link.$(TARGET).ld

OBJCOPYFLAGS    = $(ARCH_BIFLAGS)

BUILD_DIR      := build/$(TARGET)

all: $(BUILD_DIR)/crt0.fae

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/crt0.fae: $(BUILD_DIR)/crt0.elf
	$(OBJCOPY) $(OBJCOPYFLAGS) $< $@
	@chmod 644 $@

$(BUILD_DIR)/crt0.elf: $(BUILD_DIR)/crt0.o link.$(TARGET).ld
	$(LD) $(LDFLAGS) $< -o $@

$(BUILD_DIR)/crt0.o: crt0.c | $(BUILD_DIR)
	$(CC) $(CFLAGS) -c $< -o $@

realclean: clean
	$(RM) -rf build

clean:
	$(RM) -f $(BUILD_DIR)/crt0.o

.PHONY: all realclean clean
