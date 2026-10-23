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

# Builds the bring-up harness: rungs 1 to 3 of the ladder on real silicon.
#
# It links the target's own boot layer -- the same start.S, link.ld, clock,
# UART and PMP code the port will use -- against a main() and a trap stub of
# its own, because the MAL and the C translated from Rocq do not exist for
# this target yet and pip.elf cannot be linked. The point is that everything
# under boot/ here is the real thing, not a mock.
#
#     ./configure.sh --architecture=rp2350 ...
#     make -C src/arch/rp2350/bringup            # bringup.elf, .bin and .uf2
#     make -C src/arch/rp2350/bringup check      # the checks that need no board
#     make -C src/arch/rp2350/bringup uart       # watch UART0, in its own shell
#     make -C src/arch/rp2350/bringup swdflash   # flash over the Debug Probe
#     make -C src/arch/rp2350/bringup flash      # or over a BOOTSEL connection
#     make -C src/arch/rp2350/bringup rescue     # recover a wedged board
#
# With one USB cable the probe is the only way in, so the usual loop is `uart`
# in one shell and `swdflash` in another.
#
# Delete this directory once rung 4 needs the real boot/main.c and
# boot/trap_entry.S.

HERE := $(dir $(abspath $(lastword $(MAKEFILE_LIST))))
TARGET_DIR := $(HERE)..
BOOT_DIR := $(TARGET_DIR)/boot
BUILD_DIR := $(HERE)build

include $(TARGET_DIR)/../../../toolchain.mk

ifneq ($(TARGET),rp2350)
    $(error toolchain.mk is configured for '$(TARGET)': run\
            ./configure.sh --architecture=rp2350)
endif

CFLAGS := -Wall -Wextra -Werror -std=gnu99 $(ARCH_CFLAGS)
CFLAGS += $(if $(DEBUG), $(DEBUG_CFLAGS))
CFLAGS += -I $(BOOT_DIR)/include -I $(HERE)
ASFLAGS := $(ARCH_ASFLAGS) -I $(BOOT_DIR)/include -I $(HERE)
LDFLAGS := $(ARCH_LDFLAGS)

# How to reach the board. Overridable, since none of this is configured by
# ./configure.sh -- toolchain.mk knows about GDB but not about OpenOCD.
OPENOCD        ?= openocd
OPENOCD_IFACE  ?= interface/cmsis-dap.cfg
OPENOCD_TARGET ?= target/rp2350.cfg
ADAPTER_SPEED  ?= 5000
UART_PORT      ?= /dev/ttyACM0
UART_BAUD      ?= 115200

OPENOCD_BASE   := $(OPENOCD) -f $(OPENOCD_IFACE)\
                             -c 'adapter speed $(ADAPTER_SPEED)'
OPENOCD_ARM    := $(OPENOCD_BASE) -f $(OPENOCD_TARGET)
OPENOCD_RESCUE := $(OPENOCD_BASE) -c 'set RESCUE 1' -f $(OPENOCD_TARGET)\
                                  -c 'shutdown'

# The boot sources the harness needs, listed rather than wildcarded so that
# the boot layer growing does not quietly pull new code in here. Note this
# list is NOT what keeps the kernel's own main.c and trap_entry.S out of the
# harness -- both directories have files of those names, so the collision is
# between the pattern rules below, and their order is what resolves it.
BOOT_SRC := initialize_hardware.c kernel.c pmp.c stdio.c string.c uart.c
OBJ := $(addprefix $(BUILD_DIR)/,$(BOOT_SRC:.c=.o))
OBJ += $(BUILD_DIR)/main.o $(BUILD_DIR)/trap.o
# start.o must come first, as in the root Makefile's link line.
OBJ := $(BUILD_DIR)/start.o $(OBJ)

HEADERS := $(wildcard $(BOOT_DIR)/include/*.h) $(HERE)bringup.h

all: $(BUILD_DIR)/bringup.uf2

$(BUILD_DIR)/bringup.elf: $(OBJ) $(TARGET_DIR)/link.ld
	$(LD) $(OBJ) -T $(TARGET_DIR)/link.ld -o $@ $(LDFLAGS)

$(BUILD_DIR)/bringup.bin: $(BUILD_DIR)/bringup.elf
	$(BI) $(ARCH_BIFLAGS) $< $@

$(BUILD_DIR)/bringup.uf2: $(BUILD_DIR)/bringup.elf
	picotool uf2 convert --family rp2350-riscv $< $@

# The harness's own sources come first, and the order is what matters rather
# than a nicety. The boot layer now has a main.c of its own, so both the
# $(HERE) and the $(BOOT_DIR) rule match main.o with the same stem; make takes
# the first that matches and whose prerequisite exists, so listing $(HERE)
# first is what keeps the harness compiling its main.c and not the kernel's.
# With the rules the other way round the harness silently built boot/main.c
# and failed on an include it has no path for.
#
# The boot rules still apply to every other object, because bringup/ has no
# file of that name for their stems to match.
$(BUILD_DIR)/%.o: $(HERE)%.c $(HEADERS) | $(BUILD_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

$(BUILD_DIR)/%.o: $(HERE)%.S $(HEADERS) | $(BUILD_DIR)
	$(AS) $(ASFLAGS) -o $@ $<

$(BUILD_DIR)/%.o: $(BOOT_DIR)/%.c $(HEADERS) | $(BUILD_DIR)
	$(CC) $(CFLAGS) -c -o $@ $<

$(BUILD_DIR)/%.o: $(BOOT_DIR)/%.S $(HEADERS) | $(BUILD_DIR)
	$(AS) $(ASFLAGS) -o $@ $<

$(BUILD_DIR):
	mkdir -p $@

# Everything about the image that can be checked without a board.
check: $(BUILD_DIR)/bringup.bin $(BUILD_DIR)/bringup.elf
	$(HERE)check-image.sh $(BUILD_DIR)/bringup.elf\
	                      $(BUILD_DIR)/bringup.bin\
	                      $(TOOL_PREFIX)

# Needs the board in BOOTSEL mode and its own USB cable. The bootrom does the
# ARCHSEL switch for us, which makes this the simpler route when a second cable
# is to hand.
flash: $(BUILD_DIR)/bringup.uf2
	picotool load -x $<

# Hand the chip back to ARM debug control, undoing the bootrom's switch to
# RISC-V. swdflash does this itself; run it on its own to recover a board that
# a bad image has left unreachable, or before attaching to the Cortex-M33s.
rescue:
	$(OPENOCD_RESCUE)

# Flash over SWD through the Debug Probe. Needs no second cable, since the same
# probe carries UART0 -- see the uart target.
#
# Programming goes through the *ARM* config even though the image is RISC-V,
# for two reasons. This OpenOCD cannot reach the RISC-V core at all: its riscv
# target type rejects -dap, so rp2350.cfg aborts under 'set USE_CORE {rv0}'.
# And it does not need to -- the flash is architecture-neutral, and `reset run`
# hands control to the bootrom, which finds the RISC-V image, sets ARCHSEL and
# resets into it. OpenOCD reporting
#
#     Error: [rp2350.cm1] DP initialisation failed
#
# immediately after the reset is that switch happening, and is the sign it
# worked: the Cortex-M33 access ports have just gone away.
#
# Which is why the reset is a step of its own, and the only one allowed to
# fail. OpenOCD cannot help but error as the access ports disappear underneath
# it -- measured: this step exits 2 exactly when it works -- so its status here
# says nothing. Programming and verification keep theirs, and a real failure to
# write flash still stops the build. What the reset achieved is read on the
# UART, not from $$?.
#
# It needs its own explicit init, which the programming step got for free from
# `program`. Without it `reset` is not yet a command, and the `-` below would
# hide that: a silent no-op flash that leaves the old image running.
#
# The rescue first is what makes this repeatable. Once the chip is running
# RISC-V those access ports no longer answer, so a second flash would have
# nothing to program through. It costs one extra chip reset and is harmless
# when the chip is already under ARM debug control.
swdflash: $(BUILD_DIR)/bringup.elf rescue
	$(OPENOCD_ARM) -c 'program $< verify' -c 'shutdown'
	-$(OPENOCD_ARM) -c 'init' -c 'reset run' -c 'shutdown'

# Read the harness's output over the probe's CDC-UART bridge. Ctrl-C to stop.
# Start it in another terminal *before* `make swdflash`, since the harness
# prints once at reset and then idles.
uart:
	stty -F $(UART_PORT) $(UART_BAUD) cs8 -cstopb -parenb raw -echo
	cat $(UART_PORT)

clean:
	rm -rf $(BUILD_DIR)

.PHONY: all check flash swdflash rescue uart clean
