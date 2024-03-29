#!/bin/sh
###############################################################################
#  © Université de Lille, The Pip Development Team (2015-2024)                #
#  Copyright (C) 2020-2024 Orange                                             #
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
coqc_minimum_version=

# Regular expressions used to extract version number
cc_regex=
as_regex=
ld_regex=
coqc_regex=

# Global variables
cc=
as=
ld=
objcopy=
coqc=
dx=
coqdep=
coqdoc=
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

  OPTIONAL ARGUMENTS:

    --help                    Show this message and exit

    --no-command-check        Disable command check

    --quiet                   Turn off the script's error output

    --debugging-mode=<x>      The debugging mode to use for the target
                              architecture. This parameter can have three
                              values: \"none\", \"semihosting\" or \"uart\". If
                              it is omitted, the default value is \"none\". Be
                              careful, not all architectures support all
                              debugging modes.

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

    --coq-compiler=<x>        Explicitly use a path to the Coq compiler rather
                              than trying to find it in the \$PATH variable.

    --dx=<x>                  Set the directory in which dx C printer is
                              installed (see variable \$CPRINTERDIR in dx
                              configuration). If you installed dx with opam, it
                              should be \"$(opam var dx:lib)\".
                              If not set, digger will be used.

    --coqdep=<x>              Explicitly use a path to coqdep rather than trying
                              to find it in the \$PATH variable.

    --coqdoc=<x>              Explicitly use a path to coqdoc rather than trying
                              to find it in the \$PATH variable.

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
#  © Université de Lille, The Pip Development Team (2015-2024)                #
#  Copyright (C) 2020-2024 Orange                                             #
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

# Tool to convert Coq code into C code
DIGGER_DIR   = tools/digger
DIGGER     := \$(DIGGER_DIR)/digger

DXDIR := $dx

# Coq Proof Assistant
COQC   := $coqc
COQDEP := $coqdep
COQDOC := $coqdoc

# GNU C Compiler
CC := $cc

# Netwide assembler
AS := $as

# GNU Linker
LD := $ld

# GNU Objcopy
BI := $objcopy

# GNU Debugger
GDB := $gdb

################# Compilation options #################

TARGET    = $target

# Arch related options
ARCH_CFLAGS   = $arch_cflags
ARCH_LDFLAGS  = $arch_ldflags
ARCH_ASFLAGS  = $arch_asflags

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
			--coq-compiler)
				coqc=$value
				;;
			--dx)
				dx=$value
				;;
			--coqdep)
				coqdep=$value
				;;
			--coqdoc)
				coqdoc=$value
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
			coqc=${coqc:='coqc'}
			pdflatex=${pdflatex:='pdflatex'}
			gdb=${gdb:='gdb-multiarch'}
			doxygen=${doxygen:='doxygen'}
			make=${make:='make'}
			coqdep=${coqdep:='coqdep'}
			coqdoc=${coqdoc:='coqdoc'}

			### Regular expressions used to extract the version
			### number from the "--version" output

			cc_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			as_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			ld_regex='^.*gcc ([^)]\+) \([^ \n]\+\).*$'
			coqc_regex='^The Coq Proof Assistant, version \([^ \n]\+\).*$'

			### Minimum versions of the toolchain for the selected
			### architecture

			as_minimum_version='8.3.1'
			cc_minimum_version='8.3.1'
			ld_minimum_version='8.3.1'
			coqc_minimum_version='8.13.1'

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

			return 0
			;;
		*)
			usage && return 1
	esac
}

# The main function of the script
main() {
	parse_arguments "$@"

	# Check if the mandatory arguments are set
	if [ -z "$architecture" ]
	then
		usage && return 1
	fi

	configure_global_variables

	if [ -z "$no_command_check" ]
	then
		# These commands need to have their paths and version numbers validated
		validate_command_path_version_wrapper "$cc" "$cc_regex" "$cc_minimum_version"
		validate_command_path_version_wrapper "$as" "$as_regex" "$as_minimum_version"
		validate_command_path_version_wrapper "$ld" "$ld_regex" "$ld_minimum_version"
		validate_command_path_version_wrapper "$coqc" "$coqc_regex" "$coqc_minimum_version"

		# These commands need to have only their paths validated
		validate_command_path_wrapper "$coqdep"
		validate_command_path_wrapper "$coqdoc"
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
