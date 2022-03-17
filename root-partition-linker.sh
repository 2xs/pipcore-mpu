#!/bin/sh
###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2022)                #
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

link_script='src/arch/dwm1001/link.ld' # default is src/arch/dwm1001/link.ld

usage() {
	printf 'Usage: %s <pip-bin-path> <root-bin-path>\n' "$0"
}

# Test minimum 2 arguments for bin paths
if [ "$#" -lt 2 ]
then
	usage
	exit 1
fi

# Optional: specifiy location of final elf
elf="pip.elf"
if [ ! -z "$3" ]
then
	elf="$3"
fi

cat <<EOF > root_partition.S
.section .multiplexer
.global  __multiplexer

__multiplexer:
	.incbin "$2"
EOF

arm-none-eabi-gcc -o root_partition.o -c root_partition.S
arm-none-eabi-ld -o "$elf" "$1" root_partition.o -L "src/arch/nrf52-common" -T "$link_script"
rm -f root_partition.S root_partition.o
printf 'Created elf file: %s\n' "$elf"
printf 'For debuging:\n'
printf 'arm-none-eabi-objdump -x pip.elf | grep smultiplexer\n'
printf 'add-symbol-file ../pip-mpu-benchmark/gen_benchmarks/aha-mont64/aha-mont64.elf 0xccc0\n'
printf '\nWARNING: using %s\n' "$link_script"
exit 0