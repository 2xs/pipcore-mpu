# Pip Internals

## Pip-MPU overview
Pip-MPU is an OS (Operating System) kernel specialised in memory management and context switching.
It is a partitioning kernel and a security kernel, ensuring memory isolation between partitions.
It is part of the proto-kernel family, *e.g.* leaving file systems, drivers, scheduler, IPC (Inter-Process Communication) or multiplexer out of the minimalist TCB (Trusted Computing Base).
Therefore, Pip-MPU is sole privileged in the system while all the partitions run unprivileged in userland.
The partitions provide the missing features when necessary (for instance scheduling) as well as the applications and their support components.
Pip-MPU is meant to be trustworthy and proofs of its memory isolation is on going work.

In the rest of the document, we speak about Pip-MPU, the Pip variant which memory isolation is based on the MPU (Memory Protection Unit) and targets low-end microcontrollers.
The informed reader already acquainted with the MMU-based memory isolation variant (the first [Pip](https://gitlab.univ-lille.fr/2xs/pip/pipcore/-/tree/main)) release is highly recommended to read the Pip-related parts in this document as no comparison or evolution from the MMU variant is described.
Pip-MPU is intended to be compatible with both ARMv7-M and ARMv8-M architectures.

## Partitioning model

Pip-MPU's memory management is based on a hierarchical partitioning model.
The main principle is that a *partition* (an execution unit) can create one or several sub-partitions, that in turn can create sub-partitions.
This creates a *partition tree* rooted in a special partition called the *root partition*.
The root partition is the only partition existing at system initialisation.
The other partitions are dynamically created during the system's lifetime.

## Partition lineage
We define in this paragraph fundamental relationships within the partition tree, closely resembling a family tree.
The relationship between a partition and a sub-partition is referred as a  **parent-child** relationship.
A **parent partition** may have **descendants** when a **child partition** also have its own children.
For the descendants, this parent partition is considered as an **ancestor**.
The common ancestor to all partitions is the **root partition**.
Partitions stemming from the same parent are **sibling partitions**.

## Features
Pip-MPU exposes system calls that build up the partition tree.

### Memory sharing
A parent partition can create child partitions and share memory with them.
	All the memory attributed to a partition is directly accessible to this partition.
	The parent can only map memory that it owns itself.
	As a result, the whole system memory is divided in two parts: 1) Pip's memory and 2) the rest owned at start by the root partition.
	The root partition can access any partition's memory.
	This is a natural consequence of the hierarchical partitioning model, where the security of any partition is based on its ancestors, by recursion.
	As such, a parent partition has always the ability to tear down a child.

### Access permissions
The parent decides which access permissions is associated to the shared memory.
	Indeed, a partition can restrict the use of the memory to a child partition.
	However, it can never increase the permissions.

### Fine-grained memory unit
The basic memory unit is a memory block, *i.e.* a continuous range of memory addresses.
	The memory block is defined by a start and an end address and its size can vary during the partition's lifetime.
	Indeed, the user can cut memory blocks in smaller pieces, for example to share only a part of a block to a child.

### Flexible usage
Partitions can leverage the previous features to set up their own requirements and fit their usage.
	Examples are inter-partition communication by moving around memory blocks from isolated partitions, ensuring the W^X principle and least privilege in a partition...
	From the start of the system with the launch of the root partition, the partitioning view is completely dynamic and evolves as desired by the user.

## Security properties
Pip's partitioning model ensures 3 security properties:

* **Vertical sharing**: a parent partition can only share memory to a child partition and must own the memory blocks it gives out.
* **Horizontal isolation**: a memory block can only be shared to as single child partition. This property ensures strict memory isolation between child partitions.
* **Kernel Isolation**: Pip's memory, as well as all metadata structures used for describing the partitioning model, should never be accessible to any partitions.
This property protects the kernel itself and ensures no partition can change its configuration by itself by bypassing Pip.

As such, the Pip-MPU API builds up a nested compartmentalisation.
	Pip-MPU ensures these security properties are guaranteed at any time.



## Pip-MPU nomenclature
This paragraph aims at defining some Pip-MPU objects that are used to describe the API.
This is a simplified view hiding the implementation detailed not relevant for the user.

The metadata structures are Pip's configuration information, used to track the partitioning view and to configure the MPU with the correct information.

In Pip, they are of two types :

* **Partition Descriptor**: A partition is identified by a Partition Descriptor, unique in the system for this partition.
			The Partition Descriptor is a metadata structure containing the partition's references.
* **Kernel structure**: The kernel structure is a metadata structure holding the memory blocks and associated RWX access permissions (Read-Write-Execute).
		A kernel structure has a fixed amount of slots (user-defined, by default 8) where to register the memory blocks.
			Hence, a partition can have several kernel structures.
			If one needs more slots to register new memory blocks, it is sufficient to create new kernel structures, up to a user-defined limit.


	Metadata structures are created out of memory blocks.
	They are only special memory blocks containing Pip-MPU information.
	As such, memory blocks that turned into metadata structures are not accessible anymore to the partition, as they became Pip-MPU objects and should be isolated (Kernel Isolation property).

## Pip-MPU services

Pip-MPU provides 13 system calls:

* `createPartition`: creates a child partition

* `deletePartition`: deletes a child partition

* `prepare`: sets up a new kernel structure to the current partition's or a child partition

* `collect`: finds an empty kernel structure in the current partition or in a child partition and removes it

* `addMemoryBlock`: adds a block (shared memory) to a child partition (consumes one slot in the kernel structure)

* `removeMemoryBlock`: removes a block from a child partition (frees one slot in the kernel structure)

* `cutMemoryBlock`: cuts a block in the current partition (consumes one slot in the kernel structure)

* `mergeMemoryBlocks`: merges back previously cut blocks in the current partition (frees one slot in the kernel structure)

* `mapMPU`: selects a block to be enabled in the MPU of the current partition or a child partition

* `readMPU`: reads the block mapped in a MPU entry of the current partition or a child partition

* `findBlock`: finds a block in the current partition or in a child partition

* `setVIDT`: sets the VIDT (Virtual Interrupt Descriptor Table) address of the current partition descriptor or of the partition descriptor of one of its children

* `yield`: switches context

* `in`: writes a register

* `out`: reads a register
## Focus on the MPU management
The MPU (Memory Protection Unit) is a hardware unit present in many ARM Cortex-M processors.
Its role is to restrict memory accesses according to a defined configuration.
	The configuration consists in a set of memory regions called *MPU regions* having various permission rights (read, write, execute) and additional attributes (caching, buffering...).
	From a broad perspective, the MPU is for small embedded systems what the Memory Management Unit (MMU) is for general-purpose systems, since both share the memory protection role in a similar fashion.

A Pip-based system is guarded by the MPU at all time.
	The memory blocks are meant to be configured as an MPU region, with a minimum size of 32 bytes.
	This means an illegal access (to Pip-MPU or a violation of a block's access permissions) ends up in a memory fault.
	The memory fault is caught by the parent partition which can decide what to do with the faulted child.


Furthermore, Pip-MPU introduces a distinction between all memory blocks owned by a partition (the block pool) and the memory blocks that can be accessed (enabled blocks).
	Indeed, a typical MPU consists in 8 protected MPU regions that are too restrictive for the partition management.
	Not all memory blocks can thus be active at the same time.
	Thus, blocks in the block pool are enabled or disabled.
	**Enabled** means they are guarded by the MPU with their RWX permissions set up.
	**Disabled** means they are not accessible at all.
	**Trying to access disabled blocks, even if they are in the block pool, results in a memory fault.**
	By default, exception made for the root partition, no block is active from the block pool and needs to be manually enabled by the developer.
	Though, enabled blocks must not be confused with **accessible** blocks.
	In fact, when a memory block is shared, it is accessible by default, *i.e.* eligible to be enabled, and the developer choose to enable it or not.
	However, if it leaves this shared state condition, *e.g.* by turning into a metadata structure during partition creation, it becomes inaccessible.
	Only accessible blocks can be enabled in the MPU.

## Special consideration to ARMv7-M users
The ARMv8-M architecture introduces slight differences with the MPU of the previous ARMv7-M version.
	Indeed, ARMv7-M requires more configuration constraints.
	Pip-MPU developed mechanisms to deal with these constraints so to share common grounds between the two versions.
	Basically, this results in 2 consequences to the ARMv7-M user:

* Stack size and alignment: the stack must always be aligned to a power of two aligned on a multiple of its size.
							This is a direct constraint carried forward.
* Access to non-aligned memory blocks: Pip-MPU releases the alignment constraint to any other memory blocks.
									However, in the background, Pip-MPU makes partial memory block configuration that matches the alignment constraint.
									Hence, for any legitimate memory access in an enabled memory block, Pip-MPU reloads the MPU to always match the constraints.
									This means that a legitimate access to a non-aligned memory block could be delayed because of the MPU reloading.


