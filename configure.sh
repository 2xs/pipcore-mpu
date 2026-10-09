#!/bin/sh
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

set -e

# Minimum required version of the commands
as_minimum_version=
cc_minimum_version=
ld_minimum_version=
rocq_minimum_version=

# Regular expressions used to extract version number
cc_regex=
as_regex=
ld_regex=
rocq_regex=

# Global variables
cc=
as=
ld=
objcopy=
rocq=
dx=
pdflatex=
gdb=
doxygen=
make=
no_command_check=
architecture=
quiet=
debugging_mode='none'
boot_sequence='default'

# Print the script usage
usage() {
    printf "\
Usage: %s <MANDATORY ARGUMENTS> [OPTIONAL ARGUMENTS]

  This configuration script aims to check the availability and the version of
  the commands required by the project.

  The default behavior of the script is to look for the commands needed for the
  architecture, specified by the \"--architecture\" argument, in the \$PATH
  variable and check their version numbers. If a command could not be found or
  if the version number is not the expected one, the script fails by returning a
  non-zero error code. The user can then specify a path to the command
  explicitly using the optional arguments or disable the default behavior by
  passing the \"--no-command-check\" argument.

  MANDATORY ARGUMENTS:

    --architecture=<x>        The target architecture name:
                                  - \"dwm1001\"
                                  - \"rp2350\"
    --fae-directory=<x>       The FAE format include directory filepath such as
                              ../fae_format/src/include for example.

  OPTIONAL ARGUMENTS:

    --help                    Show this message and exit

    --no-command-check        Disable command check

    --quiet                   Turn off the script's error output

    --debugging-mode=<x>      The debugging mode to use for the target
                              architecture. This parameter can have three
                              values: \"none\", \"semihosting\" or \"uart\". If
                              it is omitted, the default value is \"none\". Be
                              careful, not all architectures support all
                              debugging modes. The \"rp2350\" accepts only
                              \"none\" and \"uart\": semihosting is
                              unimplemented for this target.

    --boot-sequence=<x>       The boot sequence to use for the target
                              architecture. This parameter can have two values:
                              \"default\" or \"test\". If omitted, the default
                              value is \"default\". The \"default\" value uses
                              the normal boot sequence. The value \"test\" uses
                              the boot sequence performing unit tests.

    --c-compiler=<x>          Explicitly use a path to a C compiler rather than
                              trying to find it in the \$PATH variable.

    --assembler=<x>           Explicitly use a path to an assembler rather than
                              trying to find it in the \$PATH variable.

    --linker=<x>              Explicitly use a path to a linker rather than
                              trying to find it in the \$PATH variable.

    --objcopy=<x>             Explicitly use a path to objcopy rather than
                              trying to find it in the \$PATH variable.

    --rocq=<x>                Explicitly use a path to the Rocq Prover rather
                              than trying to find it in the \$PATH variable.

    --dx=<x>                  Set the directory in which dx C printer is
                              installed (see variable \$CPRINTERDIR in dx
                              configuration). If you installed dx with opam, it
                              should be \"$(opam var dx:lib)\".
                              If not set, digger will be used.

    --doxygen=<x>             Explicitly use a path to Doxygen rather than
                              trying to find it in the \$PATH variable.

    --gdb=<x>                 Explicitly use a path to GDB rather than trying to
                              find it in the \$PATH variable.

    --make=<x>                Explicitly use a path to Make rather than trying
                              to find it in the \$PATH variable.

    --pdflatex=<x>            Explicitly use a path to pdflatex rather than
                              trying to find it in the \$PATH variable.
" \
"$0"
}

# Generate toolchains with validated commands
generate_toolchains() {
cat <<EOF > toolchain.mk
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

# Tool to convert Rocq code into C code
DIGGER_DIR   = tools/digger
DIGGER     := \$(DIGGER_DIR)/digger

DXDIR := $dx

# Rocq Prover
ROCQ := $rocq

# GNU C Compiler
CC := $cc

# GNU Assembler (invoked through GCC)
AS := $as

# GNU Linker
LD := $ld

# GNU Objcopy
BI := $objcopy

# GNU Debugger
GDB := $gdb

# Prefix of the binutils, for the components that invoke them
# directly rather than through GCC (see src/partition_crt0)
TOOL_PREFIX := $tool_prefix

################# Compilation options #################

TARGET    = $target

# FAE format related options
FAE_DIRECTORY                = $fae_directory
FAE_INCLUDE_DIRECTORY        = $fae_include_directory
FAE_INCLUDE_DIRECTORY_CFLAGS = $fae_include_directory_cflags

# Arch related options
ARCH_CFLAGS   = $arch_cflags
ARCH_LDFLAGS  = $arch_ldflags
ARCH_ASFLAGS  = $arch_asflags

# Arch related options for the root partition's crt0, which is a
# separate binary and does not inherit Pip's own definitions
ARCH_CRT0_CFLAGS = $arch_crt0_cflags

# Debug related options
DEBUG_CFLAGS  = -g
DEBUG_CFLAGS += -Og

# Binary related options
ARCH_BIFLAGS  = $arch_biflags
PADDING_VALUE = $padding_value
PADDING_POW2  = $padding_pow2

# If the DEBUG variable is set, the output binary will
# be in debug mode. Otherwise, if the DEBUG variable is
# not set, the output binary will be in released mode.
DEBUG = yes

################## Execution options ##################

GDBARGS =
EOF
}

# Parse provided arguments
parse_arguments() {
	for argument in "$@"
	do
		value=${argument#*=}
		flag=${argument%=*}

		case $flag in
			--help)
				usage && exit 1
				;;
			--architecture)
				architecture=$value
				;;
			--fae-directory)
				fae_directory=${value:+$(realpath "$value")}
				;;
			--no-command-check)
				no_command_check=1
				;;
			--quiet)
				quiet=1
				;;
			--debugging-mode)
				debugging_mode=$value
				;;
			--boot-sequence)
				boot_sequence=$value
				;;
			--c-compiler)
				cc=$value
				;;
			--assembler)
				as=$value
				;;
			--linker)
				ld=$value
				;;
			--objcopy)
				objcopy=$value
				;;
			--rocq)
			  rocq=$value
				;;
			--dx)
				dx=${value:+$(realpath "$value")}
				;;
			--gdb)
				gdb=$value
				;;
			--doxygen)
				doxygen=$value
				;;
			--make)
				make=$value
				;;
			--pdflatex)
				pdflatex=$value
				;;
		esac
	done
}

# Print message to the stderr
# $1 The message to print
print_error() {
	# Shellcheck will whine about interpreting patterns, which is desired here
	# shellcheck disable=SC2059
	# Check if the "--quiet" argument is set
	if [ -z "$quiet" ]
	then
		printf "\\033[91m" >&2
		printf "$@" >&2
		printf "\\033[0m" >&2
	fi
}

# Select this version group
select_group='\([^.]\+\)'
# Ignore this version group
ignore_group='[0-9]\+'

# Select the MAJOR version number
# $1 The version number from which to select
# Return the MAJOR version number
select_version_major() {
	regex='^'"$select_group"'.*$'
	printf '%s\n' "$1" | sed -n -e 's/'"$regex"'/\1/p'
}

# Select the MINOR version number
# $1 The version number from which to select
# Return the MINOR version number
select_version_minor() {
	regex='^'"$ignore_group"'\.'"$select_group"'.*$'
	printf '%s\n' "$1" | sed -n -e 's/'"$regex"'/\1/p'
}

# Select the PATCH version number
# $1 The version number from which to select
# Return the PATCH version number
select_version_patch() {
	regex='^'"$ignore_group"'\.'"$ignore_group"'\.'"$select_group"'.*$'
	printf '%s\n' "$1" | sed -n -e 's/'"$regex"'/\1/p'
}

# Select the BUILD version number
# $1 The version number from which to select
# Return the BUILD version number
select_version_build() {
	regex='^'"$ignore_group"'\.'"$ignore_group"'\.'"$ignore_group"'\.'"$select_group"'.*$'
	printf '%s\n' "$1" | sed -n -e 's/'"$regex"'/\1/p'
}

# Check if the version number is valid
# $1 The version number to check
# Return 0 is the version number is valid, 1 otherwise
is_valid_version_pattern() {
	version_pattern='^[0-9]+(\.[0-9]+(\.[0-9]+(\.[0-9]+)?)?)?$'
	printf '%s\n' "$1" | grep -E -q "$version_pattern" || return 1
}

# Compare two version groups
# $1 The version group to compare with $2
# $2 The version group to compare with $1
# Return:
#    0 if $1 = $2
#    1 if $1 > $2
#    2 if $1 < $2
compare_version_group() {
	# Check if both groups are set
	[ -z "$1" ] && [ -z "$2" ] && return 0
	[ -n "$1" ] && [ -z "$2" ] && return 1
	[ -z "$1" ] && [ -n "$2" ] && return 2
	# Compare both groups
	[ "$1" -gt "$2" ] && return 1
	[ "$1" -lt "$2" ] && return 2
	# Both groups are equals
	return 0
}

# Compare two version numbers in MAJOR.MINOR.PATCH.BUILD format
# $1 The version number to compare with $2
# $2 The version number to compare with $1
# Return:
#    3 if $1 or $2 are invalid
#    0 if $1 = $2
#    1 if $1 > $2
#    2 if $1 < $2
compare_version() {
	# Checks that the version numbers are valid
	is_valid_version_pattern "$1" || return 3
	is_valid_version_pattern "$2" || return 3

	# Check if the two versions are equal
	[ "$1" = "$2" ] && return 0

	# Compare the two major versions
	v1_group=$(select_version_major "$1")
	v2_group=$(select_version_major "$2")
	compare_version_group "$v1_group" "$v2_group" || return "$?"

	# Compare the two minor versions
	v1_group=$(select_version_minor "$1")
	v2_group=$(select_version_minor "$2")
	compare_version_group "$v1_group" "$v2_group" || return "$?"

	# Compare the two patch versions
	v1_group=$(select_version_patch "$1")
	v2_group=$(select_version_patch "$2")
	compare_version_group "$v1_group" "$v2_group" || return "$?"

	# Compare the two build versions
	v1_group=$(select_version_build "$1")
	v2_group=$(select_version_build "$2")
	compare_version_group "$v1_group" "$v2_group" || return "$?"
}

# Validate command path
# $1 Command path or name
# Return 0 if the function succeed, 1 otherwise
validate_command_path() {
	command -v "$1" >/dev/null 2>&1 || return 1
}

# Select the first of the given commands that can be found in $PATH
# $@ Command names to try, in order of preference
# Return the first command found, or the first argument if none was found, so
# that the subsequent validation reports a sensible name
first_available_command() {
	for candidate in "$@"
	do
		if command -v "$candidate" >/dev/null 2>&1
		then
			printf '%s\n' "$candidate"
			return 0
		fi
	done
	printf '%s\n' "$1"
}

# Validate command version
# $1 Command path or name
# $2 Regular expression used to extract version number
# $3 Minimum required version of the command
# Return 0 if the function succeed, 1 otherwise
validate_command_version() {
	version=$(LC_ALL=C "$1" --version | sed -n -e 's/'"$2"'/\1/p')
	compare_version "$version" "$3"
	[ "$?" -le 1 ] || return 1
}

# Validate command path and version
# $1 Command path or name
# $2 Regular expression used to extract version number
# $3 Minimum required version of the command
# Return 0 if the function succeed, 1 otherwise
validate_command_path_version() {
	validate_command_path "$1" || return 1
	validate_command_version "$1" "$2" "$3" || return 1
}

# Validate command path and print error message if an error occured
# $1 Command path or name
# Return 0 if the function succeed, 1 otherwise
validate_command_path_wrapper() {
	# Shellcheck will whine about not being able to expand $PATH, which is fine
	# shellcheck disable=SC2016
	if ! validate_command_path "$1"
	then
		print_error 'The command "%s" could not be found in the environment ' "$1"
		print_error 'variable $PATH.\nYou must provide a path to a valid version '
		print_error 'of the command by passing the corresponding argument or\n'
		print_error 'disable command checking by passing the "--no-command-check" '
		print_error 'argument.\n'
		return 1
	fi
}

# Validate command path, version and print error message if an error occured
# $1 Command path or name
# $2 Regular expression used to extract version number
# $3 Minimum required version of the command
# Return 0 if the function succeed, 1 otherwise
validate_command_path_version_wrapper() {
	# Shellcheck will whine about not being able to expand $PATH, which is fine
	# shellcheck disable=SC2016
	if ! validate_command_path_version "$1" "$2" "$3"
	then
		print_error 'The command "%s" could not be found in the environment ' "$1"
		print_error 'variable $PATH or has a version below %s.\nYou must provide ' "$3"
		print_error 'a path to a valid version of the command by passing the '
		print_error 'corresponding argument or\ndisable command checking by '
		print_error 'passing the "--no-command-check" argument.\n'
		return 1
	fi
}

# Configure the global variables according to the specified architecture
configure_global_variables() {
	case "$architecture" in
		dwm1001)

			### Directory name of the target

			target='dwm1001'

			# The boot sequence performing the unit tests of the
			# dwm1001 only works in semihosting mode

			if  [ "$debugging_mode" != "semihosting" ] && [ "$boot_sequence" = "test" ]
			then
				print_error 'The unit tests of the dwm1001 only works in semihosting mode ...\n'
				return 1
			fi

			### Default names of the commands

			cc=${cc:='arm-none-eabi-gcc'}
			as=${as:='arm-none-eabi-gcc'}
			ld=${ld:='arm-none-eabi-gcc'}
			objcopy=${objcopy:='arm-none-eabi-objcopy'}
			rocq=${rocq:='rocq'}
			pdflatex=${pdflatex:='pdflatex'}
			gdb=${gdb:='gdb-multiarch'}
			doxygen=${doxygen:='doxygen'}
			make=${make:='make'}

			### Prefix of the binutils, for the components that
			### invoke them directly rather than through GCC

			tool_prefix='arm-none-eabi-'

			### Regular expressions used to extract the version
			### number from the "--version" output

			cc_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			as_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			ld_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			rocq_regex='^The Rocq Prover, version \([^ \n]\+\).*$'

			### Minimum versions of the toolchain for the selected
			### architecture

			as_minimum_version='8.3.1'
			cc_minimum_version='8.3.1'
			ld_minimum_version='8.3.1'
			rocq_minimum_version='9.0.0'

			### CFLAGS for the selected architecture

			arch_cflags='-mthumb'
			arch_cflags="$arch_cflags"' -mcpu=cortex-m4'
			arch_cflags="$arch_cflags"' -mfloat-abi=hard'
			arch_cflags="$arch_cflags"' -mfpu=fpv4-sp-d16'
			arch_cflags="$arch_cflags"' -ffreestanding'
			case $debugging_mode in
				semihosting)
					arch_cflags="$arch_cflags"' -DTRACE'
					;;
				uart)
					arch_cflags="$arch_cflags"' -DUART_DEBUG'
					;;
			esac
			case $boot_sequence in
				test)
					arch_cflags="$arch_cflags"' -DUNIT_TESTS'
					;;
			esac
			arch_cflags="$arch_cflags"' -DDUMP'
			arch_cflags="$arch_cflags"' -DNRF52832_XXAA'
			arch_cflags="$arch_cflags"' -U__UINT32_TYPE__ -D__UINT32_TYPE__=unsigned'

			### LDFLAGS for the selected architecture

			arch_ldflags='-nostartfiles'
			arch_ldflags="$arch_ldflags"' -nodefaultlibs'
			arch_ldflags="$arch_ldflags"' -nolibc'
			arch_ldflags="$arch_ldflags"' -nostdlib'
			arch_ldflags="$arch_ldflags"' -lgcc'
			arch_ldflags="$arch_ldflags"' -mthumb'
			arch_ldflags="$arch_ldflags"' -mcpu=cortex-m4'
			arch_ldflags="$arch_ldflags"' -mfloat-abi=hard'
			arch_ldflags="$arch_ldflags"' -mfpu=fpv4-sp-d16'

			### ASFLAGS for the selected architecture

			arch_asflags="$arch_cflags"
			arch_asflags="$arch_asflags"' -c'

			### BIFLAGS for the selected architecture

			arch_biflags='--input-target=elf32-littlearm'
			arch_biflags="$arch_biflags"' --output-target=binary'

			padding_value='0xff'
			padding_pow2='32'

			### CFLAGS for the root partition's crt0. These are the
			### machine flags only: the crt0 is a separate binary and
			### must not inherit Pip's preprocessor definitions.

			arch_crt0_cflags='-mthumb'
			arch_crt0_cflags="$arch_crt0_cflags"' -mcpu=cortex-m4'
			arch_crt0_cflags="$arch_crt0_cflags"' -ffreestanding'

			;;
		rp2350)

			### Directory name of the target

			target='rp2350'

			# Semihosting is unimplemented on this target, so UART is
			# the debug backend for now.

			if [ "$debugging_mode" = 'semihosting' ]
			then
				print_error 'Semihosting is unimplemented on the rp2350, use --debugging-mode=uart ...\n'
				return 1
			fi

			# The boot sequence performing the unit tests of the
			# rp2350 only works in uart mode

			if  [ "$debugging_mode" != "uart" ] && [ "$boot_sequence" = "test" ]
			then
				print_error 'The unit tests of the rp2350 only works in uart mode ...\n'
				return 1
			fi

			### Default names of the commands
			#
			# Several RISC-V bare-metal toolchain spellings are in
			# circulation. Any of them works: -march and -mabi below
			# pin rv32/ilp32 explicitly, so a toolchain defaulting to
			# rv64 still produces the right code.

			riscv_gcc=$(first_available_command 'riscv32-unknown-elf-gcc'\
			                                   'riscv64-unknown-elf-gcc'\
			                                   'riscv-none-elf-gcc'\
			                                   'riscv64-elf-gcc')

			cc=${cc:="$riscv_gcc"}
			as=${as:="$riscv_gcc"}
			ld=${ld:="$riscv_gcc"}
			objcopy=${objcopy:="${riscv_gcc%gcc}objcopy"}
			rocq=${rocq:='rocq'}
			pdflatex=${pdflatex:='pdflatex'}
			gdb=${gdb:=$(first_available_command "${riscv_gcc%gcc}gdb"\
			                                    'gdb-multiarch')}
			doxygen=${doxygen:='doxygen'}
			make=${make:='make'}

			### Prefix of the binutils, for the components that
			### invoke them directly rather than through GCC

			tool_prefix="${riscv_gcc%gcc}"

			### Regular expressions used to extract the version
			### number from the "--version" output

			cc_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			as_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			ld_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			rocq_regex='^The Rocq Prover, version \([^ \n]\+\).*$'

			### Minimum versions of the toolchain for the selected
			### architecture
			#
			# GCC 11.1 is the first release that accepts the Zicsr
			# and Zifencei extensions as explicit -march components.
			# Before that they were implied by "i" and naming them is
			# an error, so the -march string below needs 11.1 or later.

			as_minimum_version='11.1.0'
			cc_minimum_version='11.1.0'
			ld_minimum_version='11.1.0'
			rocq_minimum_version='9.0.0'

			### CFLAGS for the selected architecture
			#
			# Three of these flags are load-bearing and must not be
			# dropped as tidying:
			#
			# -mno-relax: with linker relaxation enabled, GCC reaches
			#   globals through gp (x3). gp is a general-purpose
			#   register that also appears in a partition's saved
			#   context, so every access to a Pip global would depend
			#   on gp holding Pip's value. Disabling relaxation
			#   removes the question entirely. The trap stub also
			#   carries an explicit ".option norelax".
			#
			# no _zcb/_zcmp: Hazard3 implements both, but a Zcmp
			#   cm.push/cm.pop/cm.popret performs several memory
			#   accesses per instruction, which the PMP refill handler
			#   cannot satisfy from a single faulting effective
			#   address. Excluding them keeps every instruction the
			#   handler may meet single-access.
			#
			# -mcmodel=medany: matches the pico-sdk convention, and
			#   accommodates .text in XIP flash with .data in SRAM.

			arch_cflags='-march=rv32imac_zicsr_zifencei'
			arch_cflags="$arch_cflags"' -mabi=ilp32'
			arch_cflags="$arch_cflags"' -mcmodel=medany'
			arch_cflags="$arch_cflags"' -mno-relax'
			arch_cflags="$arch_cflags"' -ffreestanding'
			case $debugging_mode in
				uart)
					arch_cflags="$arch_cflags"' -DUART_DEBUG'
					;;
			esac
			case $boot_sequence in
				test)
					arch_cflags="$arch_cflags"' -DUNIT_TESTS'
					;;
			esac
			arch_cflags="$arch_cflags"' -DDUMP'
			arch_cflags="$arch_cflags"' -DRP2350'
			arch_cflags="$arch_cflags"' -DPICO2'
			# dx emits "unsigned int" for the index type: the
			# generated code does not compile without this.
			arch_cflags="$arch_cflags"' -U__UINT32_TYPE__ -D__UINT32_TYPE__=unsigned'

			### LDFLAGS for the selected architecture

			arch_ldflags='-nostartfiles'
			arch_ldflags="$arch_ldflags"' -nodefaultlibs'
			arch_ldflags="$arch_ldflags"' -nolibc'
			arch_ldflags="$arch_ldflags"' -nostdlib'
			arch_ldflags="$arch_ldflags"' -lgcc'
			arch_ldflags="$arch_ldflags"' -march=rv32imac_zicsr_zifencei'
			arch_ldflags="$arch_ldflags"' -mabi=ilp32'
			arch_ldflags="$arch_ldflags"' -mno-relax'

			### ASFLAGS for the selected architecture

			arch_asflags="$arch_cflags"
			arch_asflags="$arch_asflags"' -c'

			### BIFLAGS for the selected architecture

			arch_biflags='--input-target=elf32-littleriscv'
			arch_biflags="$arch_biflags"' --output-target=binary'

			# Unchanged from the dwm1001: this is the alignment the
			# appended root partition FAE needs, not an Arm constraint.

			padding_value='0xff'
			padding_pow2='32'

			### CFLAGS for the root partition's crt0. These are the
			### machine flags only: the crt0 is a separate binary and
			### must not inherit Pip's preprocessor definitions.

			arch_crt0_cflags='-march=rv32imac_zicsr_zifencei'
			arch_crt0_cflags="$arch_crt0_cflags"' -mabi=ilp32'
			arch_crt0_cflags="$arch_crt0_cflags"' -mcmodel=medany'
			arch_crt0_cflags="$arch_crt0_cflags"' -mno-relax'
			arch_crt0_cflags="$arch_crt0_cflags"' -ffreestanding'

			;;
		*)
			usage && return 1
	esac

	fae_include_directory="$fae_directory"'/src/include'
	fae_include_directory_cflags='-I '$fae_include_directory
	return 0
}

# The main function of the script
main() {
	parse_arguments "$@"

	# Check if the mandatory arguments are set
	if [ -z "$architecture" ]
	then
		usage && return 1
	fi

	if [ -z "$fae_directory" ]
	then
		usage && return 1
	fi

	configure_global_variables

	if [ -z "$no_command_check" ]
	then
		# These commands need to have their paths and version numbers validated
		validate_command_path_version_wrapper "$cc"   "$cc_regex"   "$cc_minimum_version"
		validate_command_path_version_wrapper "$as"   "$as_regex"   "$as_minimum_version"
		validate_command_path_version_wrapper "$ld"   "$ld_regex"   "$ld_minimum_version"
		validate_command_path_version_wrapper "$rocq" "$rocq_regex" "$rocq_minimum_version"

		# These commands need to have only their paths validated
		validate_command_path_wrapper "$objcopy"
		validate_command_path_wrapper "$pdflatex"
		validate_command_path_wrapper "$gdb"
		validate_command_path_wrapper "$doxygen"
		validate_command_path_wrapper "$make"
	fi

	generate_toolchains

	return 0
}

# Script entry point
main "$@"
