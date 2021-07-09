(*******************************************************************************)
(*  © Université Lille 1, The Pip Development Team (2015-2018)                 *)
(*                                                                             *)
(*  This software is a computer program whose purpose is to run a minimal,     *)
(*  hypervisor relying on proven properties such as memory isolation.          *)
(*                                                                             *)
(*  This software is governed by the CeCILL license under French law and       *)
(*  abiding by the rules of distribution of free software.  You can  use,      *)
(*  modify and/ or redistribute the software under the terms of the CeCILL     *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL          *)
(*  "http://www.cecill.info".                                                  *)
(*                                                                             *)
(*  As a counterpart to the access to the source code and  rights to copy,     *)
(*  modify and redistribute granted by the license, users are provided only    *)
(*  with a limited warranty  and the software's author,  the holder of the     *)
(*  economic rights,  and the successive licensors  have only  limited         *)
(*  liability.                                                                 *)
(*                                                                             *)
(*  In this respect, the user's attention is drawn to the risks associated     *)
(*  with loading,  using,  modifying and/or developing or reproducing the      *)
(*  software by the user in light of its specific status of free software,     *)
(*  that may mean  that it is complicated to manipulate,  and  that  also      *)
(*  therefore means  that it is reserved for developers  and  experienced      *)
(*  professionals having in-depth computer knowledge. Users are therefore      *)
(*  encouraged to load and test the software's suitability as regards their    *)
(*  requirements in conditions enabling the security of their systems and/or   *)
(*  data to be ensured and,  more generally, to use and operate it in the      *)
(*  same conditions as regards security.                                       *)
(*                                                                             *)
(*  The fact that you are presently reading this means that you have had       *)
(*  knowledge of the CeCILL license and that you accept its terms.             *)
(*******************************************************************************)

(** * Summary
    This file contains PIP memory services : [createPartition], [deletePartition],
			[addMemoryBlock], [removeMemoryBlock],
			[cutMemoryBlock], [mergeMemoryBlocks],
      [prepare] and [collect].

    The definitions of recursive functions like [prepare] and
      [collect] match the same form :
      - part 1 : <<functionNameRecAux>> is the recursive funtion
      - part 2 : <<functionNameRec>> fixes the sufficient timeout value for recursion
                 to complete
      - part 3 : <<funtionName>> is the PIP service. It calls <<functionNameRec>>
                with the required parameters *)

Require Import Model.Monad Model.MAL Core.Internal.
Import Bool Arith List List.ListNotations.

Open Scope mpu_state_scope.

(** ** The createPartition PIP MPU service

    The [createPartition] system call creates a new child (sub-partition of the
    current partition), e.g. initializes the block <idBlock> as a PD block and
		sets the current partition as the parent partition.
		Returns true:OK/false:NOK

    <<MPUAddressBlock>>  The block to become the child Partition Descriptor
												(id = MPU address of an existing block)
*)
Definition createPartition (MPUAddressBlock: paddr) : LLI bool :=
    (** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Find the block in the current partition *)
    perform blockInCurrentPartitionAddr := findBlockInMPUWithAddr 	currentPart
																																	MPUAddressBlock in
		(** Check the block exists, accessible and not shared and
				size > minimum MPU region size ELSE NOK*)
		(* TODO check present ?*)
		perform addrIsNull := compareAddrToNull	blockInCurrentPartitionAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		perform addrIsAccessible := readMPUAccessibleFromMPUEntryAddr	blockInCurrentPartitionAddr in
		if negb addrIsAccessible then (* block is inaccessible *) ret false else

		perform blockSize := sizeOfBlock blockInCurrentPartitionAddr in
		perform minBlockSize := getMinBlockSize in
		perform isBlockTooSmall1 := Index.leb blockSize minBlockSize in
		if isBlockTooSmall1 then (* smaller than minimum MPU size *) ret false else

		perform PDStructureTotalLength := getPDStructureTotalLength in
		perform isBlockTooSmall2 := Index.leb blockSize PDStructureTotalLength in
		if isBlockTooSmall2 then (* too small to become a PD *) ret false else

		(* if accessible, then PDflag can't be set, we just need to check PDchild *)
		perform PDChildAddr := readSh1PDChildFromMPUEntryAddr	blockInCurrentPartitionAddr in
		perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
		if negb PDChildAddrIsNull (*shouldn't be null*) then (* shared *) ret false else

		(** Initialize child Partition Descriptor *)

		perform newPDBlockStartAddr := readMPUStartFromMPUEntryAddr blockInCurrentPartitionAddr in
		perform newPDBlockEndAddr := readMPUEndFromMPUEntryAddr blockInCurrentPartitionAddr in
		(** Erase the future Partition Descriptor content*)
		eraseBlock newPDBlockStartAddr newPDBlockEndAddr;;
		(* create PD Table by setting the structure to the default values *)
		initPDTable newPDBlockStartAddr ;;
		(* set current partition as parent in the child *)
		writePDParent newPDBlockStartAddr currentPart ;;

		(** Reflect the child Partition Description creation in the current partition *)

		(** set the block as not available anymore and remove from physical MPU*)
		writeMPUAccessibleFromMPUEntryAddr blockInCurrentPartitionAddr false ;;
		removeBlockFromPhysicalMPU currentPart blockInCurrentPartitionAddr ;;
		(** set the block as a PD block in shadow 1*)
		writeSh1PDFlagFromMPUEntryAddr blockInCurrentPartitionAddr true ;;
		(** set the block as not accessible anymore to the ancestors *)
		perform blockOrigin := readSCOriginFromMPUEntryAddr blockInCurrentPartitionAddr in
		perform blockStart := readMPUStartFromMPUEntryAddr blockInCurrentPartitionAddr in
		perform blockNext := readSCNextFromMPUEntryAddr blockInCurrentPartitionAddr in
		if beqAddr blockOrigin blockStart && beqAddr blockNext nullAddr then
			(* Block hasn't been cut previously, need to be set unaccessible for the ancestors *)
			perform idBlock := readMPUStartFromMPUEntryAddr blockInCurrentPartitionAddr in
			writeAccessibleRec currentPart idBlock false ;;
			ret true
		else (* block has been cut and is already not accessible in the ancestors *)
			ret true.

(* TODO: rename all MPUAdress... 'cause confusing *)
(** ** The cutMemoryBlock PIP MPU service

    The [cutMemoryBlock] system call cuts the memory block <MPUAddressBlockToCut>
		at <cutAddress> which creates a new subbblock at that address.
		The new subblock is placed in the physical MPU region of the current partition
		if the <MPURegionNb> is a valid region number.
		Returns the new created subblock's MPU address:OK/NULL:NOK

    <<MPUAddressBlockToCut>>		the block to cut
												(id = MPU address of an existing block)
		<<cutAddress>>			the address where to cut the <idBlockToCut> block,
												becomes the id of the created block
    <<MPURegionNb>>			the region number of the physical MPU where to place the
												created block
*)
Definition cutMemoryBlock (MPUAddressBlockToCut cutAddr : paddr) (MPURegionNb : index)
																																: LLI paddr :=
    (** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Check that there is a free slot left*)
		perform nbFreeSlots := readPDNbFreeSlots currentPart in
		perform zero := Index.zero in
		perform isFull := Index.leb nbFreeSlots zero in
		if isFull then ret nullAddr else

		(** Find the block to cut in the current partition (with MPU address) *)
    perform blockToCutMPUAddr := findBlockInMPUWithAddr 	currentPart
																													MPUAddressBlockToCut in
		perform addrIsNull := compareAddrToNull	blockToCutMPUAddr in
		if addrIsNull then(** no block found, stop *) ret nullAddr else

		(** Check the block to cut is accessible *)
		perform blockIsAccessible := readMPUAccessibleFromMPUEntryAddr blockToCutMPUAddr in
		if negb blockIsAccessible then (** block is inaccessible *) ret nullAddr else

		(** Check the block is not shared *)
		(* if accessible, then PDflag can't be set, we just need to check PDchild is null*)
		perform PDChildAddr := readSh1PDChildFromMPUEntryAddr	blockToCutMPUAddr in
		perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
		if negb PDChildAddrIsNull (*shouldn't be null*) then (*shared*) ret nullAddr else

		(** Check the cut address lies between the start and the end address *)
		perform blockToCutStartAddr := readMPUStartFromMPUEntryAddr blockToCutMPUAddr in
		perform isCutAddrBelowStart := Paddr.leb cutAddr blockToCutStartAddr in
		if isCutAddrBelowStart then (* cutAddress outside bounds *) ret nullAddr else

		perform blockToCutEndAddr := readMPUEndFromMPUEntryAddr blockToCutMPUAddr in
		perform isCutAddrAboveEnd := Paddr.leb blockToCutEndAddr cutAddr in
		if isCutAddrAboveEnd then (* cutAddress outside bounds *) ret nullAddr else

		(** Check that the block is greater than the minimum MPU region size*)
		perform blockSize := sizeOfBlock blockToCutMPUAddr in
		perform minBlockSize := getMinBlockSize in
		perform isBlockTooSmall := Index.leb blockSize minBlockSize in
		if isBlockTooSmall then (* block is smaller than the minimum  *) ret nullAddr
		else

		(** Parent and ancestors: set the block inaccessible if this is the block's first cut*)
		perform idBlockToCut := readMPUStartFromMPUEntryAddr MPUAddressBlockToCut in
		writeAccessibleToAncestorsIfNotCutRec currentPart
																					idBlockToCut
																					blockToCutMPUAddr
																					false ;;

		(** Current partition: create the new subblock at cutAddr and insert it in
				the kernel structure, keep the original rights *)
		perform blockEndAddr := readMPUEndFromMPUEntryAddr blockToCutMPUAddr in
		perform blockOrigin := readSCOriginFromMPUEntryAddr blockToCutMPUAddr in
		perform blockR := readMPURFromMPUEntryAddr blockToCutMPUAddr in
		perform blockW := readMPUWFromMPUEntryAddr blockToCutMPUAddr in
		perform blockX := readMPUXFromMPUEntryAddr blockToCutMPUAddr in
		perform newSubblockMPUAddr := insertNewEntry 	currentPart
																									cutAddr
																									blockEndAddr
																									blockOrigin
																									blockR blockW blockX
																									in

		(** Modify initial block: the end address becomes (cutAddress - 1)*)
		perform predCutAddr := Paddr.pred cutAddr in
		writeMPUEndFromMPUEntryAddr blockToCutMPUAddr predCutAddr ;;
		(** Reload the MPU region with the update *)
		perform kernelentriesnb := getKernelStructureEntriesNb in
		perform defaultidx := Index.succ kernelentriesnb in
		perform blockMPURegionNb := findBlockIdxInPhysicalMPU 	currentPart
																													blockToCutMPUAddr
																													defaultidx in
		enableBlockInMPU currentPart blockToCutMPUAddr blockMPURegionNb ;;

		(** Register the cut in the Shadow Cut: insert in middle if needed*)
		perform originalNextSubblock := readSCNextFromMPUEntryAddr blockToCutMPUAddr in
		writeSCNextFromMPUEntryAddr newSubblockMPUAddr originalNextSubblock ;;
		writeSCNextFromMPUEntryAddr blockToCutMPUAddr newSubblockMPUAddr ;;

		(** Enable the new subblock in the MPU if region nb is valid *)
		enableBlockInMPU currentPart newSubblockMPUAddr MPURegionNb ;;

		(** RET new subblock's slot address*)
		ret newSubblockMPUAddr.


(** ** The mergeMemoryBlocks PIP MPU service

    The [mergeMemoryBlocks] system call merges <BlockToMerge1> and
		<BlockToMerge2> together.
		The two blocks have been cut before so @BlockToMerge1Start < @BlockToMerge2Start.
		The merged block is placed in the physical MPU region of the current partition
		if the <MPURegionNb> is a valid region number.

		Returns MPUAddressBlockToMerge1:OK/NULL:NOK

    <<MPUAddressBlockToMerge1>>	the block to merge in becomes the start of the merged blocks
																(id = MPU address of an existing block)
		<<MPUAddressBlockToMerge2>>	the block to be merged disappears from the list of blocks
																(id = MPU address of an existing block)
	  <<MPURegionNb>>							the region number of the physical MPU where to
																place the merged block
*)
Definition mergeMemoryBlocks (MPUAddressBlockToMerge1 MPUAddressBlockToMerge2 : paddr)
														(MPURegionNb : index) : 							LLI paddr :=
    (** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(* Find the block1 to merge in the current partition (with MPU address) *)
    perform block1InCurrPartAddr := findBlockInMPUWithAddr 	currentPart
																														MPUAddressBlockToMerge1 in
		perform addrIsNull := compareAddrToNull	block1InCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret nullAddr else

		(* Find the block2 to merge in the current partition (with MPU address) *)
    perform block2InCurrPartAddr := findBlockInMPUWithAddr 	currentPart
																														MPUAddressBlockToMerge2 in
		perform addrIsNull := compareAddrToNull	block2InCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret nullAddr else

		(** Check blocks accessible, not shared, and follow each other**)

		(* Check blocks are accessible *)
		perform isBlock1Accessible := readMPUAccessibleFromMPUEntryAddr block1InCurrPartAddr in
		perform isBlock2Accessible := readMPUAccessibleFromMPUEntryAddr block2InCurrPartAddr in
		if negb (isBlock1Accessible && isBlock2Accessible)
		then (* one/both blocks not accessible, stop *) ret nullAddr
		else

		(* Check blocks are not shared *)
		(* if accessible, then PDflag can't be set, we just need to check PDchild *)
		perform block1PDChildAddr := readSh1PDChildFromMPUEntryAddr	block1InCurrPartAddr in
		perform block1PDChildAddrIsNull := compareAddrToNull block1PDChildAddr in
		perform block2PDChildAddr := readSh1PDChildFromMPUEntryAddr	block2InCurrPartAddr in
		perform block2PDChildAddrIsNull := compareAddrToNull block2PDChildAddr in
		if negb block1PDChildAddrIsNull || negb block2PDChildAddrIsNull
		then (* one/both blocks shared, stop *) ret nullAddr
		else

		(* Check block 2 follows block 1 TODO changed check order with following instruction*)
		perform block1Next := readSCNextFromMPUEntryAddr block1InCurrPartAddr in
		perform isBlock2Next := getBeqAddr block2InCurrPartAddr block1Next in
		if negb isBlock2Next then (* no merge possible, stop*) ret nullAddr else

		(** Merge block 2 in block 1 *)

		(* replace block 1's next subblock with block 2's next subblock *)
		perform block2Next := readSCNextFromMPUEntryAddr block2InCurrPartAddr in
		writeSCNextFromMPUEntryAddr block1InCurrPartAddr block2Next ;;

		(* replace block 1's end address with block 2's end address *)
		perform block2MPUEnd := readMPUEndFromMPUEntryAddr block2InCurrPartAddr in
		writeMPUEndFromMPUEntryAddr block1InCurrPartAddr block2MPUEnd ;;

		(* remove block 2 entry *)
		freeSlot currentPart block2InCurrPartAddr ;;

		(** Parents and ancestors: set the block accessible again if there are no
		subblocks anymore of block 1 *)
		perform idBlockToMerge1 := readMPUStartFromMPUEntryAddr block1InCurrPartAddr in
		writeAccessibleToAncestorsIfNotCutRec currentPart
																					idBlockToMerge1
																					block1InCurrPartAddr
																					true ;;

		(** Remove the blocks to merge from the physical MPU and add the merged one
				instead *)
		removeBlockFromPhysicalMPU currentPart block1InCurrPartAddr ;;
		removeBlockFromPhysicalMPU currentPart block2InCurrPartAddr ;;
		enableBlockInMPU currentPart block1InCurrPartAddr MPURegionNb ;;

		(** RET block1's slot address *)
		ret idBlockToMerge1.

(* TODO: compute idBlock in writeAccessibleToAncestors instead*)
(** ** The prepare PIP MPU service

    The [prepare] system call prepares the partition <idPD> (current partition
		or child) to receive <projectedSlotsNb> of blocks and use the
		<idRequisitionedBlock> as a metadata structure, e.g. this will prepare
		<idRequisitionedBlock> to be a kernel structure added to the kernel structure
		list of the partition <idPD>
        - if enough free slots to receive <projectedSlotsNb> then won't do anything
				- if not enough free slots then prepare the block
        - if <projectedSlotsNb> == -1 then prepare the block whatever the nb of
					free slots
		Returns true:OK/false:NOK

    <<idPD>>													the block to prepare (current partition or a child)
																			(id = start field of an existing block)
		<<projectedSlotsNb>>							the number of requested slots, -1 if forced prepare
		<<MPUAddressRequisitionedBlock>>	the block used as the new kernel structure
*)
Definition prepare (idPD : paddr) (projectedSlotsNb : index)
									(MPUAddressRequisitionedBlock : paddr) : LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks**)

		(* Check idPD is the current partition or one of its child*)
		perform isCurrentPart := getBeqAddr idPD currentPart in
		perform isChildCurrPart := checkChild currentPart idPD in
		if negb isCurrentPart && negb isChildCurrPart
		then (* idPD is not itself or a child partition, stop*) ret false
		else

		(* Check the max number of prepare hasn't been reached yet*)
		perform nbPrepare := readPDNbPrepare idPD in
		perform maxnbprepare := getMaxNbPrepare in
		perform isMaxPrepare := Index.leb maxnbprepare nbPrepare in
		if isMaxPrepare then (* reached max prepare, stop*) ret false else

		(* Check that there is a need for a prepare: nb of free slots not enough
				to hold the projected slots or forced prepare) *)
		perform currentFreeSlotsNb := readPDNbFreeSlots idPD in
		perform isEnoughFreeSlots := Index.leb projectedSlotsNb currentFreeSlotsNb in
		perform zero := Index.zero in
		perform isForcedPrepare := Index.ltb projectedSlotsNb zero in
		if isEnoughFreeSlots && negb isForcedPrepare
		then (* no need for a prepare, stop*) ret false
		else

		(* Check that the nb of projected slots aren't superior to the max entries
				that a prepare can offer (max kernel entries) in case not forced prepare*)
		perform kernelentriesnb := getKernelStructureEntriesNb in
		perform isOutsideBound := Index.ltb kernelentriesnb projectedSlotsNb in
		if negb isForcedPrepare && isOutsideBound
		then (* bad arguments, stop*) ret false
		else

		(** The requisioned block becomes a kernel structure*)

		(* Find the requisitioned block in the current partition (with MPU address) *)
    perform requisitionedBlockInCurrPartAddr := findBlockInMPUWithAddr
																									currentPart
																									MPUAddressRequisitionedBlock in
		perform addrIsNull := compareAddrToNull	requisitionedBlockInCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		(* Check the block is big enough to hold a kernel structure*)
		perform blockSize := sizeOfBlock requisitionedBlockInCurrPartAddr in
		perform kStructureTotalLength := getKernelStructureTotalLength in
		perform isBlockTooSmall := Index.leb blockSize kStructureTotalLength in
		if isBlockTooSmall then (* block is smaller than minimum  *) ret false else

		(* Check block is accessible and present*)
		perform addrIsAccessible := readMPUAccessibleFromMPUEntryAddr
																	requisitionedBlockInCurrPartAddr in
		if negb addrIsAccessible then (* block is inaccessible *) ret false else
		perform addrIsPresent := readMPUPresentFromMPUEntryAddr
																	requisitionedBlockInCurrPartAddr in
		if negb addrIsPresent then (** block is not present *) ret false else

		(* Init kernel structure (erase first) *)
		perform requisitionedBlockStart := readMPUStartFromMPUEntryAddr
																						requisitionedBlockInCurrPartAddr in
		perform requisitionedBlockEnd := readMPUEndFromMPUEntryAddr
																						requisitionedBlockInCurrPartAddr in
		perform isStructureInitialised := initStructure requisitionedBlockStart
																										requisitionedBlockEnd in
		if negb isStructureInitialised then (** error during init *) ret false else

		perform newKStructurePointer := getAddr requisitionedBlockStart in

		(** Set the requisitioned block inaccessible and remove it from the physical MPU*)
		writeMPUAccessibleFromMPUEntryAddr requisitionedBlockInCurrPartAddr false ;;
		removeBlockFromPhysicalMPU currentPart requisitionedBlockInCurrPartAddr ;;
		(** Parent and ancestors: set the block unaccessible if the block is not cut*)
		perform idRequisitionedBlock := readMPUStartFromMPUEntryAddr
																				requisitionedBlockInCurrPartAddr in
		writeAccessibleToAncestorsIfNotCutRec currentPart
																					idRequisitionedBlock
																					requisitionedBlockInCurrPartAddr
																					false ;;

		(** Link the new kernel structure in the targeted PD *)

		(** Insert the requisitioned block in the kernel structure list *)
		perform oldKStructurePointer := readPDStructurePointer idPD in
		writeNextFromKernelStructureStart newKStructurePointer
																			oldKStructurePointer;;
		writePDStructurePointer idPD newKStructurePointer;;

		(** Adjust the free slot pointer to the next free slot*)

		(* set the new free slots at the head of the previous free slots list *)
		perform lastidx := Index.pred kernelentriesnb in
		perform lastMPUEntryAddr := getMPUEntryAddrFromKernelStructureStart
																		newKStructurePointer
																		lastidx in
		perform currFirstFreeSlot := readPDFirstFreeSlotPointer idPD in
		writeMPUEndFromMPUEntryAddr lastMPUEntryAddr currFirstFreeSlot ;;
		(* set the PD's first free slot pointer to the first entry of the new kernel structure*)
		writePDFirstFreeSlotPointer idPD newKStructurePointer ;;
		(* new count = (count + number of new entries)*)
		perform currentNbFreeSlots := readPDNbFreeSlots idPD in
		perform newNbFreeSlots := Index.addIdx currentNbFreeSlots kernelentriesnb in
		writePDNbFreeSlots idPD newNbFreeSlots ;;
		(* new nbprepare = nbprepare + 1*)
		perform currentNbPrepare := readPDNbPrepare idPD in
		perform succCurrentNbPrepare := Index.succ currentNbPrepare in
		writePDNbPrepare idPD succCurrentNbPrepare ;;

		(** Special treatment for a prepare on a child: set the block as shared in
				the parent*)
		if isChildCurrPart
		then (*prepare is done for another partition than itself*)
			writeSh1PDChildFromMPUEntryAddr requisitionedBlockInCurrPartAddr idPD ;;
			ret true
		else
			ret true.

(** ** The addMemoryBlock PIP MPU service

    The [addMemoryBlock] system call adds a block to a child partition.
		The block is still accessible from the current partition (shared memory).

		Returns the shared block's slot address in the child:OK/NULL:NOK

    <<idPDchild>>							the child partition to share with
		<MPUAddressBlockToShare>>	the MPU address where the block <idBlocktoShare> lies
		<<r w e >>								the rights to apply in the child partition
*)
Definition addMemoryBlock (idPDchild MPUAddressBlockToShare: paddr) (r w e : bool)
																																: LLI paddr :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(* Find the block to share in the current partition (with MPU address) *)
    perform blockInCurrPartAddr := findBlockInMPUWithAddr 	currentPart
																													MPUAddressBlockToShare in
		perform addrIsNull := compareAddrToNull	blockInCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret nullAddr else
		perform rcheck := checkRights blockInCurrPartAddr r w e in
    if negb rcheck then (* new rights not OK, stop *) ret nullAddr else

		addMemoryBlockCommon idPDchild blockInCurrPartAddr r w e.

(** ** The removeMemoryBlock PIP MPU service TODO: return address ?

    The [removeMemoryBlock] system call removes a block from a child partition.

    The block could be cut in the child partition but all subblocks still accessible
    This operation succeeds for any shared memory block previously added, but
		fails if the purpose of the block is not shared memory anymore,
		in particular in such cases:
        - The block can't be removed if the child or its descendants used it
					(or part of it) as a kernel structure
        - The block can't be removed if the child's descendants cut the block

		Returns true:OK/false:NOK

    <<idPDchild>>				the child partition to remove from
		<<MPUAddressBlockToRemove>>	the MPU address where the block <idBlockToRemove> lies
*)
Definition removeMemoryBlock (idPDchild MPUAddressBlockToRemove: paddr)
																																	: LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(* Find the block to remove in the current partition (with MPU address) *)
	  perform blockInCurrPartAddr := findBlockInMPUWithAddr 	currentPart
																													MPUAddressBlockToRemove in
		perform addrIsNull := compareAddrToNull	blockInCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		removeMemoryBlockCommon idPDchild blockInCurrPartAddr.

(** ** The deletePartition PIP MPU service

    The [deletePartition] system call deletes the partition <idPDchildToDelete>
		which is a child of the current partition, e.g. prunes the partition tree by
		removing all references of the child and its respective blocks from the
		current partition

		Returns true:OK/false:NOK

    <<MPUAddressPDchildToDelete>>	the child partition to delete
*)
Definition deletePartition (MPUAddressPDchildToDelete: paddr) : LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(* Find the block to delete in the current partition *)
    perform blockToDeleteInCurrPartAddr := findBlockInMPUWithAddr
																							currentPart
																							MPUAddressPDchildToDelete in
		perform addrIsNull := compareAddrToNull	blockToDeleteInCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		(** Checks *)
		(* Check idPDchild is a child of the current partition TODO use checkchild*)
		perform isChild := readSh1PDFlagFromMPUEntryAddr blockToDeleteInCurrPartAddr in
		if negb isChild then (* idPDchild is not a child partition, stop*) ret false else

		(** Reset PD block TODO reset also kernel structures ?*)
		perform blockStartAddr := readMPUStartFromMPUEntryAddr
																	blockToDeleteInCurrPartAddr in
		perform blockEndAddr := readMPUEndFromMPUEntryAddr
																	blockToDeleteInCurrPartAddr in
		eraseBlock blockStartAddr blockEndAddr ;;

		(** Remove all shared blocks references in current partition (except PD child)*)
		perform currKernelStructureStart := readPDStructurePointer currentPart in
		perform idPDchildToDelete := readMPUStartFromMPUEntryAddr MPUAddressPDchildToDelete in
		deleteSharedBlocksRec currentPart currKernelStructureStart idPDchildToDelete ;;

		(** Erase PD child entry: remove sharing and set accessible for current partition *)
		writeMPUAccessibleFromMPUEntryAddr blockToDeleteInCurrPartAddr true ;;
		perform defaultSh1Entry := getDefaultSh1Entry in
		writeSh1EntryFromMPUEntryAddr blockToDeleteInCurrPartAddr defaultSh1Entry ;;
		perform isCut := checkBlockCut blockToDeleteInCurrPartAddr in
		if isCut
		then	(* if the PD child block to remove is cut, remains not accessible in
							parent and ancestors *)
					ret true
		else (* if the PD child block to remove isn't cut, set it accessible to
							parent and ancestors *)
					writeAccessibleRec currentPart idPDchildToDelete true ;;
					ret true.

(** ** The collect PIP MPU service

    The [collect] system call collects an empty structure (if possible) from
		the partition <idPD> (current partition or a child) and returns the retrieved
		block.

		Returns the collected structure block id :OK/NULL:NOK

    <<idPD>>	the current partition or a child
*)
Definition collect (idPD: paddr) : LLI paddr :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks *)

		(* Check idPD is the current partition or one of its child*)
		perform isCurrentPart := getBeqAddr idPD currentPart in
		perform isChildCurrPart := checkChild currentPart idPD in
		if negb isCurrentPart && negb isChildCurrPart
		then (* idPD is not itself or a child partition, stop*) ret nullAddr
		else

		(* Check that if a collect is done on the current partition, there will
				still remain a structure because can't SELF remove the inital structure
				given by the parent *)
		perform nbPrepare := readPDNbPrepare idPD in
		perform zero := MALInternal.Index.zero in
		perform one := Index.succ zero in
		perform onlyInitialStructureLeft := getBeqIdx one nbPrepare in
		if isCurrentPart && onlyInitialStructureLeft then (*stop*) ret nullAddr else

		(** Call recursive function: go through list of structure nodes and collect
				the first encountered free structure *)
		perform currStructureAddr := readPDStructurePointer idPD in
		perform predStructureAddr := getPDStructurePointerAddrFromPD idPD in
																(* location of the pointer, not the content *)
		collectStructureRec currentPart idPD predStructureAddr currStructureAddr.


(** ** The mapMPU PIP MPU service

    The [mapMPU] system call maps the <MPUAddressBlockToEnable> block owned by
		the partition <idPD> (current partition or a child) in the <MPURegionNb> MPU
		region.
		If the block is NULL, then the targeted MPU region is removed from the MPU.
		If the block was already mapped, moves the block to the given MPU region.

		Returns true:OK/false:NOK

    <<idPD>>	the current partition or a child
    <<MPUAddressBlockToEnable>>	the block to map
    <<MPURegionNb>>	the physical MPU region number
*)
Definition mapMPU (idPD: paddr)
									(MPUAddressBlockToEnable : paddr)
									(MPURegionNb : index) : LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks the idPD is current or child partition, block exists, accessible
				and present *)

		(* Check idPD is the current partition or one of its child*)
		perform isCurrentPart := getBeqAddr idPD currentPart in
		perform isChildCurrPart := checkChild currentPart idPD in
		if negb isCurrentPart && negb isChildCurrPart
		then (* idPD is not itself or a child partition, stop*) ret false
		else

		(* Check block to map is NULL, in such case remove the block at given index *)
		perform blockIsNull := compareAddrToNull	MPUAddressBlockToEnable in
		if blockIsNull
		then (** Remove the block from the physical MPU if region nb is valid *)
				enableBlockInMPU idPD nullAddr MPURegionNb
		else (** Replace the block from the physical MPU if region nb is valid *)

			(* Find the block to enable in the given partition (with MPU address) *)
		  perform blockToEnableAddr := findBlockInMPUWithAddr 	idPD MPUAddressBlockToEnable in
			perform addrIsNull := compareAddrToNull	blockToEnableAddr in
			if addrIsNull then(* no block found, stop *) ret false else

			(* Check block is accessible and present*)
			perform addrIsAccessible := readMPUAccessibleFromMPUEntryAddr
																		blockToEnableAddr in
			if negb addrIsAccessible then (* block is not accessible *) ret false else
			perform addrIsPresent := readMPUPresentFromMPUEntryAddr
																		blockToEnableAddr in
			if negb addrIsPresent then (** block is not present *) ret false else

			(** Remove the block from the MPU if it was already mapped *)
			removeBlockFromPhysicalMPUIfAlreadyMapped idPD blockToEnableAddr ;;

			(** Enable block in MPU if region nb is valid *)
			enableBlockInMPU idPD blockToEnableAddr MPURegionNb.


(** ** The readMPU PIP MPU service

    The [readMPU] system call reads the content of the physical MPU owned by
		the partition <idPD> (current partition or a child) at the <MPURegionNb> MPU
		region.

		Returns block's MPU address if exists, NULL or error otherwise

    <<idPD>>	the current partition or a child
    <<MPURegionNb>>	the physical MPU region number
*)
Definition readMPU (idPD: paddr) (MPURegionNb : index) : LLI paddr :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks the idPD is current or child partition *)

		(* Check idPD is the current partition or one of its child*)
		perform isCurrentPart := getBeqAddr idPD currentPart in
		perform isChildCurrPart := checkChild currentPart idPD in
		if negb isCurrentPart && negb isChildCurrPart
		then (* idPD is not itself or a child partition, stop*) ret nullAddr
		else

		(* Check index *)
		perform zero := Index.zero in
		perform isBelowZero := Index.ltb MPURegionNb zero in
		perform maxMPURegions := getMPURegionsNb in
		perform isAboveMPURegionsNb := Index.leb maxMPURegions MPURegionNb in
		if isBelowZero || isAboveMPURegionsNb
		then (* MPURegionNb not valid, stop*) ret nullAddr (* TODO: ret error ?*)
		else
		(* Read physical MPU *)
		readBlockFromPhysicalMPU idPD MPURegionNb.

(** ** The findBlock PIP MPU service

    The [findBlock] system call finds the block of the provided <addrInBlock> by
		searching in the blocks list of the partition <idPD>.

		Returns the block and its attributes if exists, error otherwise

    <<idPD>>	the current partition or a child
    <<addrInBlock>>	the address stemming from the block to find
*)
Definition findBlock (idPD: paddr) (addrInBlock : paddr) : LLI blockOrError :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks the idPD is current or child partition *)

		(* Check idPD is the current partition or one of its child*)
		perform isCurrentPart := getBeqAddr idPD currentPart in
		perform isChildCurrPart := checkChild currentPart idPD in
		if negb isCurrentPart && negb isChildCurrPart
		then (* idPD is not itself or a child partition, stop *) ret error
		else

		(** Find the block *)
    perform blockAddr := findBelongingBlockInMPU idPD addrInBlock in
		perform addrIsNull := compareAddrToNull	blockAddr in
		if addrIsNull then(* no block found, stop *) ret error else
		(* Return the block's attributes *)
		perform blockmpuentry := readMPUEntryFromMPUEntryAddr blockAddr in
		ret (blockAttr blockAddr blockmpuentry).



