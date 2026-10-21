#!/usr/bin/env sh

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

# Everything about a built image that can be checked without a board.
#
#     ./check-image.sh <elf> <bin> <tool-prefix>
#
# The picobin block is checked twice over: picotool is asked to parse it, and
# the raw words are compared against what the format says they should be. The
# block is the most likely cause of a silent no-boot, and picotool accepting
# a block is not quite the same as the bootrom accepting it.

set -eu

if [ $# -ne 3 ]; then
    printf 'usage: %s <elf> <bin> <tool-prefix>\n' "$0" >&2
    exit 2
fi

elf="$1"
bin="$2"
prefix="$3"

failures=0

# equal <description> <actual> <expected>
equal() {
    if [ "$2" = "$3" ]; then
        printf '  ok        %s\n' "$1"
    else
        printf '  FAILED    %s: got %s, want %s\n' "$1" "$2" "$3"
        failures=$((failures + 1))
    fi
}

# absent <description> <extended-regexp>
#
# Fails if the disassembly contains a match, and shows the offending lines.
absent() {
    if "${prefix}objdump" -d "${elf}" | grep -qE "$2"; then
        printf '  FAILED    %s\n' "$1"
        "${prefix}objdump" -d "${elf}" | grep -E "$2" | sed 's/^/            /'
        failures=$((failures + 1))
    else
        printf '  ok        %s\n' "$1"
    fi
}

# header <field-name>, as readelf -h prints it
header() {
    "${prefix}readelf" -h "${elf}" \
        | sed -n "s/^[[:space:]]*$1:[[:space:]]*//p"
}

# symbol <name>, as nm prints its address
symbol() {
    "${prefix}nm" "${elf}" | sed -n "s/^\([0-9a-fA-F]*\) . $1\$/\1/p"
}

printf 'image checks\n'

# --- The ELF is for the right machine ------------------------------------

equal 'ELF machine' "$(header Machine)" 'RISC-V'
equal 'ELF class' "$(header Class)" 'ELF32'

# --- The picobin block is first, and says what it should -----------------

# od rather than a hexdump dialect: eight words, little-endian, as the bootrom
# reads them.
# shellcheck disable=SC2046 # the words are the point of the split
set -- $(od -A n -t x4 -N 32 "${bin}" | tr -s ' ')

equal 'picobin start marker' "0x$1" '0xffffded3'

# IMAGE_TYPE item: type 0x42, 1 word, payload EXE | RISCV | RP2350 = 0x1101.
equal 'IMAGE_TYPE item (EXE, RISC-V, RP2350)' "0x$2" '0x11010142'

# ENTRY_POINT item: type 0x44, 3 words to the next item, two pad bytes. The
# item is not optional here: the bootrom's default RISC-V entry point is the
# first byte of the image, which is this block.
equal 'ENTRY_POINT item header' "0x$3" '0x00000344'
equal 'ENTRY_POINT item address is the ELF entry point' "0x$4" \
      "0x$(printf '%08x' "0x$(header 'Entry point address' | sed 's/^0x//')")"

# LAST item: type 0xff, then the item word count, which is 1 + 3 here.
equal 'LAST item (4 words of items)' "0x$6" '0x000004ff'
equal 'block link word (a loop of one points at itself)' "0x$7" '0x00000000'
equal 'picobin end marker' "0x$8" '0xab123579'

# --- picotool's own reading of it ---------------------------------------

if command -v picotool > /dev/null; then
    info="$(picotool info -a "${bin}" 2>&1 || true)"
    if printf '%s' "${info}" | grep -q 'RISC-V'; then
        equal 'picotool reports a RISC-V image' yes yes
    else
        equal 'picotool reports a RISC-V image' no yes
    fi
    printf '%s\n' "${info}" | sed 's/^/            /'
else
    printf '  skipped   picotool is not installed\n'
fi

# --- The trap vector is where mtvec can point at it ---------------------

# start.S writes trapEntry's address straight into mtvec, whose low two bits
# are the MODE field. An address that is only 2-byte aligned would select a
# reserved mode, and compressed instructions make a preceding function an odd
# multiple of two bytes long readily enough that this has happened once.
trap="$(symbol trapEntry)"
if [ -z "${trap}" ]; then
    equal 'trapEntry is defined' no yes
else
    equal "trapEntry at 0x${trap} is 4-byte aligned, so mtvec.MODE is 0" \
          "$((0x${trap} & 3))" '0'
fi

# --- No gp-relative addressing -----------------------------------------

# Linker relaxation would address globals through gp, making every global
# access depend on a register that also lives in a partition's saved context.
# -mno-relax removes the question, but one relaxed translation unit, or one
# prebuilt libgcc object, would quietly bring it back.
absent 'no gp-relative access in the linked image' '\((gp|x3)\)'

# --- The compressed extensions the decoder refuses are absent ----------

# Zcmp's cm.push, cm.pop and cm.popret make several memory accesses per
# instruction, which a refill driven by one effective address cannot satisfy,
# so rv_decode rejects them and the toolchain must not emit them.
absent 'no Zcmp instruction in the linked image' '[[:space:]]cm\.(push|pop|popret)'

if [ "${failures}" -eq 0 ]; then
    printf 'image checks passed\n'
else
    printf 'image checks FAILED: %s\n' "${failures}" >&2
    exit 1
fi
