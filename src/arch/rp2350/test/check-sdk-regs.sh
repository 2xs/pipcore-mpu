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

# Checks the register, CSR and image-format constants transcribed into
# src/arch/rp2350/boot/include/{rp2350,csr,picobin}.h against the pico-sdk
# headers they were taken from.
#
#     ./check-sdk-regs.sh <path-to-pico-sdk>
#
# Both headers keep the vendor macro names, so the check is mechanical: every
# name that also exists in the SDK is compiled on both sides and the two sets
# of values are compared. A name that does not exist in the SDK is reported
# rather than ignored, which is also what catches a misspelled one.
#
# This is not part of "make check": it needs a pico-sdk checkout, which CI
# does not have. Run it when touching either header.

set -eu

if [ $# -ne 1 ]; then
    printf 'usage: %s <path-to-pico-sdk>\n' "$0" >&2
    exit 2
fi

sdk="$1"
regs="${sdk}/src/rp2350/hardware_regs/include"
boot="${sdk}/src/common/boot_picobin_headers/include"

if [ ! -d "${regs}/hardware/regs" ] || [ ! -d "${boot}/boot" ]; then
    printf '%s: no RP2350 headers under %s\n' "$0" "${sdk}" >&2
    exit 2
fi

here="$(cd "$(dirname "$0")" && pwd)"
include="${here}/../boot/include"
work="$(mktemp -d)"
trap 'rm -rf "${work}"' EXIT

# The SDK headers the two transcriptions draw from. vendor.h defines _u, which
# the register headers expect from the SDK's own platform headers.
{
    echo '#define _u(x) x ## u'
    for header in addressmap resets xosc clocks io_bank0 pads_bank0 uart rvcsr
    do
        printf '#include "hardware/regs/%s.h"\n' "${header}"
    done
    echo '#include "boot/picobin.h"'
} > "${work}/vendor.h"

# boot/picobin.h pulls in the SDK's platform header, which drags in the whole
# of pico_base. Everything it needs from it is already defined above.
mkdir -p "${work}/pico"
: > "${work}/pico/platform.h"

# Every object-like macro the three headers define, minus their include
# guards and the ones Pip composes itself. The trailing space excludes the
# function-like macros, which have no value to compare.
grep -hoE '^#define [A-Z][A-Z0-9_]* ' \
    "${include}/rp2350.h" "${include}/csr.h" "${include}/picobin.h" \
    | cut -d' ' -f2 \
    | grep -vxE 'RP2350_H|CSR_H|PICOBIN_H|PIP_.*' \
    | sort -u > "${work}/names"

: > "${work}/shared"
: > "${work}/local"

while read -r name; do
    if grep -hqE "^#define[[:space:]]+${name}[[:space:]]" \
        "${regs}/hardware/regs/"*.h "${boot}/boot/picobin.h"
    then
        echo "${name}" >> "${work}/shared"
    else
        echo "${name}" >> "${work}/local"
    fi
done < "${work}/names"

# One probe program per side, printing each shared macro's value.
for side in vendor mine; do
    case "${side}" in
        vendor) headers='vendor.h' ;;
        mine)   headers='rp2350.h csr.h picobin.h' ;;
    esac
    {
        # printf is declared rather than included: -I puts the boot layer's
        # own stdio.h, which renames printf, on the <> search path too.
        printf '#include <stdint.h>\nint printf(const char *, ...);\n'
        for header in ${headers}; do
            printf '#include "%s"\n' "${header}"
        done
        echo 'int main(void) {'
        sed 's/.*/  printf("%-46s 0x%08lx\\n", "&", (unsigned long) (&));/' \
            "${work}/shared"
        printf '  return 0;\n}\n'
    } > "${work}/probe_${side}.c"
done

cc -w -I "${work}" -I "${regs}" -I "${boot}" -o "${work}/probe_vendor" \
    "${work}/probe_vendor.c"
cc -w -I "${work}" -I "${include}" -o "${work}/probe_mine" \
    "${work}/probe_mine.c"

"${work}/probe_vendor" > "${work}/out_vendor"
"${work}/probe_mine" > "${work}/out_mine"

if [ -s "${work}/local" ]; then
    printf 'defined locally, not in the pico-sdk:\n'
    sed 's/^/  /' "${work}/local"
fi

if diff -u "${work}/out_vendor" "${work}/out_mine"; then
    printf '%s macros match the pico-sdk\n' "$(wc -l < "${work}/shared")"
else
    printf 'MISMATCH against the pico-sdk\n' >&2
    exit 1
fi
