

# Readme

Pip-MPU is a project implementing the protokernel Pip on ARM Cortex-M devices having a Memory Protection Unit (MPU).



You can find more about the Pip protokernel at its [website](http://pip.univ-lille.fr/).



The source code is covered by CeCILL-A licence.


The Pip Development Team:

* Damien Amara <damien.amara@univ-lille.fr>

* Nicolas Dejon <nicolas.dejon@orange.com>

* Gilles Grimaud <gilles.grimaud@univ-lille.fr>

* Michaël Hauspie <michael.hauspie@univ-lille.fr>

* Samuel Hym <samuel.hym@univ-lille.fr>

* David Nowak <david.nowak@univ-lille.fr>

* Florian Vanhems <florian.vanhems.etu@univ-lille.fr>

Past members of the Pip Development Team:


* Quentin Bergougnoux

* Julien Cartigny

* Étienne Helluy Lafont

* Narjes Jomaa

* Paolo Torrini

* Mahieddine Yaker



## Repository structure



* `_CoqProject` is a mandatory configuration file for Coq.

* `src` contains the source base directory.

* `src/core` contains the services code base.

* `src/extraction` contains the code to extract Coq services.

* `src/interface` contains the interface between Coq and C.

* `src/model` contains the HAL Coq code.

* `src/arch/{architecture}/MAL` contains the HAL C code.

* `src/arch/{architecture}/boot` contains the "cbits", i.e the required C and assembly code required to boot the kernel.

* `tools` contains the digger tool.

* `proof` contains the Coq proof.

* `proof` contains the documentation.


## Dependencies

Pip-MPU is known to build correctly with this toolchain:



* COQ Proof Assistant version 8.13.1

* Doxygen version 1.9.3 and above (for documentation generation)

* GCC version 12.1.0 and above

* GNU Make version 4.3 and above

* haskell-stack version 2.7.5 and above (is a cross-platform program for developing Haskell projects)

* Texlive any version or another latex tools


## Supported boards

Pip-MPU has been ported to:

* DWM1001 (Nordic Semiconductors) - nRF52832 ARM Cortex-M4

## Quick overview

Pip-MPU is specialised in memory isolation.
It is based on a hierarchical TCB (Trusted Computing Base) made of nested partitions.
Pip-MPU builds a partition tree where each children is isolated from each other.

Pip is originally based on the Memory Management Unit (MMU).

Pip-MPU retains Pip's philosophy and methodology adapted for constrained devices with a *Memory Protection Unit* (MPU), sorts of lightweigth MMU without memory virtualisation.

Pip-MPU is thus forked from the Pip original code base but completely revised to fit the MPU-empowered hardware platform.

More details on Pip-MPU can be read at [Pip-MPU internals](PipInternals.md).

Benchmarks are provided in the 'benchmark' branch.

### Pip-MPU services

Pip-MPU provides 15 system calls:

* `createPartition`: creates a child partition

* `deletePartition`: deletes a child partition

* `prepare`: initialises a configuration block

* `collect`: retrieves a configuration block

* `addMemoryBlock`: adds a memory block to a child partition

* `removeMemoryBlock`: removes a memory block from a child partition

* `cutMemoryBlock`: cuts a memory block

* `mergeMemoryBlocks`: merges back a memory block

* `mapMPU`: activates a memory block in the real MPU

* `readMPU`: reads which memory block is activates

* `findBlock`: retrieves the memory block's attributes

* `setVIDT`: sets the VIDT (Virtual Interrupt Descriptor Table) address of the current partition descriptor or of the partition descriptor of one of its children

* `yield`: switches context

* `in`: reads a register

* `out`: writes a register

## Getting started

Install the required packages to compile the documentation (for Ubuntu users):

```console
~$ sudo apt install git make
```

Clone the repository:
```console
# check the repository name is the same as this git repository
~$ git clone https://gitlab.univ-lille.fr/2xs/pip/pipcore-mpu.git
~$ cd pipcore-mpu
```

You can generate the "Getting Started" tutorial by invoking `make gettingstarted`. The full documentation is generated by invoking `make doc`.

## Building options



You can pass several arguments to ```make``` to compile Pip-MPU.



* `all`: Build target

* `proofs`: Proofs target

* `doc` | `doc-c` | `doc-coq` | `gettingstarted`: Documentation targets

* `clean` | `realclean`: Clean targets

## Funding

The pipcore-mpu project is part of the TinyPART project funded by the
MESRI-BMBF German-French cybersecurity program under grant agreements
n°ANR-20-CYAL-0005 and 16KIS1395K.
