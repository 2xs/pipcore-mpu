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

# Build fragment for the rp2350 target (Hazard3, RV32IMAC, RISC-V PMP).
#
# Vendored third-party code, as subdirectory names under boot/thirdparty/.
# Deliberately empty: this target needs no imported vendor tree. The Hazard3
# CSR numbers and field positions live in a trimmed, hand-maintained header
# under boot/include/ rather than a copy of the pico-sdk, so that erratum
# RP2350-E6 (R and X transposed in each pmpcfg byte) is handled in one place.
TARGET_THIRDPARTY_NAMES :=

# The target triple for clang tooling, used only by the compile_commands.json
# target. clangd infers its target from the driver name and never passes
# --target itself, so without this every -march/-mabi flag in the database is
# rejected with "unsupported option '-mabi=' for target 'x86_64-...'".
# riscv32, not riscv64: the toolchain's default is 64-bit and the build pins
# rv32/ilp32 through -march and -mabi.
TARGET_CLANG_TRIPLE := riscv32-unknown-elf
