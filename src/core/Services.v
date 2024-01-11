(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
(*  Copyright (C) 2020-2024 Orange                                             *)
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

    <<idBlock>>  The block to become the child Partition Descriptor
								(id = local id)
*)
Definition createPartition (idBlock: paddr) : LLI bool :=
    (** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Find the block in the current partition *)
    perform blockInCurrentPartitionAddr := findBlockInKSWithAddr 	currentPart
																																	idBlock in
		(** Check the block exists, accessible, is in RAM, not shared and
				size > minimum MPU region size ELSE NOK*)
		(* no need to check present bit because it should be accessible*)
		perform addrIsNull := compareAddrToNull	blockInCurrentPartitionAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		perform addrIsAccessible := readBlockAccessibleFromBlockEntryAddr	blockInCurrentPartitionAddr in
		if negb addrIsAccessible then (* block is inaccessible *) ret false else

		perform isInRAM := checkBlockInRAM blockInCurrentPartitionAddr in
		if negb isInRAM then (* not a RAM block, stop *) ret false else

		perform blockSize := sizeOfBlock blockInCurrentPartitionAddr in
		perform minBlockSize := getMinBlockSize in
		perform isBlockTooSmall1 := Index.ltb blockSize minBlockSize in
		if isBlockTooSmall1 then (* smaller than minimum MPU size *) ret false else

		perform PDStructureTotalLength := getPDStructureTotalLength in
		perform isBlockTooSmall2 := Index.ltb blockSize PDStructureTotalLength in
		if isBlockTooSmall2 then (* too small to become a PD *) ret false else

		(* if accessible, then PDflag can't be set, we just need to check PDchild *)
		perform PDChildAddr := readSh1PDChildFromBlockEntryAddr	blockInCurrentPartitionAddr in
		perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
		if negb PDChildAddrIsNull (*shouldn't be null*) then (* shared *) ret false else

		(** Initialize child Partition Descriptor *)

		perform newPDBlockStartAddr := readBlockStartFromBlockEntryAddr blockInCurrentPartitionAddr in
		perform newPDBlockEndAddr := readBlockEndFromBlockEntryAddr blockInCurrentPartitionAddr in
		(** Erase the future Partition Descriptor content*)
		eraseBlock newPDBlockStartAddr newPDBlockEndAddr;;
		(* create PD Table by setting the structure to the default values *)
		initPDTable newPDBlockStartAddr ;;
		(* set current partition as parent in the child *)
		writePDParent newPDBlockStartAddr currentPart ;;

		(** Reflect the child Partition Description creation in the current partition *)

		(** set the block as not available anymore and remove from physical MPU*)
		writeBlockAccessibleFromBlockEntryAddr blockInCurrentPartitionAddr false ;;
		removeBlockFromPhysicalMPU currentPart blockInCurrentPartitionAddr ;;
		(** set the block as a PD block in shadow 1*)
		writeSh1PDFlagFromBlockEntryAddr blockInCurrentPartitionAddr true ;;
		(** set the block as not accessible anymore to the ancestors *)
		perform blockOrigin := readSCOriginFromBlockEntryAddr blockInCurrentPartitionAddr in
		perform blockStart := readBlockStartFromBlockEntryAddr blockInCurrentPartitionAddr in
		perform blockNext := readSCNextFromBlockEntryAddr blockInCurrentPartitionAddr in
		if beqAddr blockOrigin blockStart && beqAddr blockNext nullAddr then
			(* Block hasn't been cut previously, need to be set unaccessible for the ancestors *)
			perform idBlock := readBlockStartFromBlockEntryAddr blockInCurrentPartitionAddr in
			writeAccessibleRec currentPart idBlock false ;;
			ret true
		else (* block has been cut and is already not accessible in the ancestors *)
			ret true.

(** ** The cutMemoryBlock PIP MPU service

    The [cutMemoryBlock] system call cuts the memory block <idBlockToCut>
		at <cutAddress> which creates a new subbblock at that address.
		The new subblock is placed in the physical MPU region of the current partition
		if the <MPURegionNb> is a valid region number.
		Returns the new created subblock's id:OK/NULL:NOK

    <<idBlockToCut>>		the block to cut
												(id = local id)
		<<cutAddress>>			the address where to cut the <idBlockToCut> block,
												becomes the id of the created block
    <<MPURegionNb>>			the region number of the physical MPU where to place the
												created subblock
*)
Definition cutMemoryBlock (idBlockToCut cutAddr : paddr) (MPURegionNb : index)
																																: LLI paddr :=
    (** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Check that there is a free slot left*)
		perform nbFreeSlots := readPDNbFreeSlots currentPart in
		perform zero := Index.zero in
		perform isFull := Index.leb nbFreeSlots zero in
		if isFull then ret nullAddr else

		(** Find the block to cut in the current partition (with block entry address) *)
    perform blockToCutEntryAddr := findBlockInKSWithAddr 	currentPart
																													idBlockToCut in
		perform addrIsNull := compareAddrToNull	blockToCutEntryAddr in
		if addrIsNull then(** no block found, stop *) ret nullAddr else

		(** Check the block to cut is accessible *)
		perform blockIsAccessible := readBlockAccessibleFromBlockEntryAddr blockToCutEntryAddr in
		if negb blockIsAccessible then (** block is inaccessible *) ret nullAddr else

		(** Check the block is not shared *)
		(* if accessible, then PDflag can't be set, we just need to check PDchild is null*)
		perform PDChildAddr := readSh1PDChildFromBlockEntryAddr	blockToCutEntryAddr in
		perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
		if negb PDChildAddrIsNull (*shouldn't be null*) then (*shared*) ret nullAddr else

		(** Check the cut address lies between the start and the end address *)
		perform blockToCutStartAddr := readBlockStartFromBlockEntryAddr blockToCutEntryAddr in
		perform isCutAddrBelowStart := Paddr.leb cutAddr blockToCutStartAddr in
		if isCutAddrBelowStart then (* cutAddress outside bounds *) ret nullAddr else

		perform blockToCutEndAddr := readBlockEndFromBlockEntryAddr blockToCutEntryAddr in
		perform isCutAddrAboveEnd := Paddr.leb blockToCutEndAddr cutAddr in
		if isCutAddrAboveEnd then (* cutAddress outside bounds *) ret nullAddr else

		(** Check that the subblocks to be created are greater than the minimum MPU
				region size*)
		perform subblock1Size := Paddr.subPaddr cutAddr blockToCutStartAddr in
		perform subblock2Size := Paddr.subPaddr blockToCutEndAddr cutAddr in
		perform minBlockSize := getMinBlockSize in
		perform isBlock1TooSmall := Index.ltb subblock1Size minBlockSize in
		perform isBlock2TooSmall := Index.ltb subblock2Size minBlockSize in
		if isBlock1TooSmall || isBlock2TooSmall
		then (* subblock would be smaller than the minimum *) ret nullAddr
		else

		(** Check the cut address is valid = 32 bytes aligned *)
		perform isCutAddrValid := check32Aligned cutAddr in
		if negb isCutAddrValid then (* cutAddr not vlid, stop *) ret nullAddr else

		(** Parent and ancestors: set the block inaccessible if this is the block's first cut*)
		writeAccessibleToAncestorsIfNotCutRec currentPart
																					blockToCutEntryAddr
																					false ;;

		(** Current partition: create the new subblock at cutAddr and insert it in
				the kernel structure, keep the original rights *)
		perform blockEndAddr := readBlockEndFromBlockEntryAddr blockToCutEntryAddr in
		perform blockOrigin := readSCOriginFromBlockEntryAddr blockToCutEntryAddr in
		perform blockR := readBlockRFromBlockEntryAddr blockToCutEntryAddr in
		perform blockW := readBlockWFromBlockEntryAddr blockToCutEntryAddr in
		perform blockX := readBlockXFromBlockEntryAddr blockToCutEntryAddr in
		perform idNewSubblock := insertNewEntry currentPart
																						cutAddr
																						blockEndAddr
																						blockOrigin
																						blockR blockW blockX
																						nbFreeSlots
																						in

		(** Modify initial block: the end address becomes (cutAddress - 1)*)
		perform predCutAddr := Paddr.pred cutAddr in
		writeBlockEndFromBlockEntryAddr blockToCutEntryAddr predCutAddr ;;
		(** Reload the MPU region with the update *)
		perform kernelentriesnb := getKernelStructureEntriesNb in
		perform defaultidx := Index.succ kernelentriesnb in
		perform blockMPURegionNb := findBlockIdxInPhysicalMPU 	currentPart
																													blockToCutEntryAddr
																													defaultidx in
		enableBlockInMPU currentPart blockToCutEntryAddr blockMPURegionNb ;;

		(** Register the cut in the Shadow Cut: insert in middle if needed*)
		perform originalNextSubblock := readSCNextFromBlockEntryAddr blockToCutEntryAddr in
		writeSCNextFromBlockEntryAddr idNewSubblock originalNextSubblock ;;
		writeSCNextFromBlockEntryAddr blockToCutEntryAddr idNewSubblock ;;

		(** Enable the new subblock in the MPU if region nb is valid *)
		enableBlockInMPU currentPart idNewSubblock MPURegionNb ;;

		(** RET new subblock's slot address*)
		ret idNewSubblock.


(** ** The mergeMemoryBlocks PIP MPU service

    The [mergeMemoryBlocks] system call merges <BlockToMerge1> and
		<BlockToMerge2> together.
		The two blocks have been cut before so @BlockToMerge1Start < @BlockToMerge2Start.
		The merged block is placed in the physical MPU region of the current partition
		if the <MPURegionNb> is a valid region number.

		Returns idBlockToMerge1:OK/NULL:NOK

    <<idBlockToMerge1>>	the block to merge in becomes the start of the merged blocks
												(id = local id)
		<<idBlockToMerge2>>	the block to be merged disappears from the list of blocks
												(id = local id)
	  <<MPURegionNb>>			the region number of the physical MPU where to place
												the merged block
*)
Definition mergeMemoryBlocks (idBlockToMerge1 idBlockToMerge2 : paddr)
														(MPURegionNb : index) : 							LLI paddr :=
    (** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(* Find the block1 to merge in the current partition (with block entry address) *)
    perform block1InCurrPartAddr := findBlockInKSWithAddr 	currentPart
																													idBlockToMerge1 in
		perform addrIsNull := compareAddrToNull	block1InCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret nullAddr else

		(* Find the block2 to merge in the current partition (with block entry address) *)
    perform block2InCurrPartAddr := findBlockInKSWithAddr 	currentPart
																													idBlockToMerge2 in
		perform addrIsNull := compareAddrToNull	block2InCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret nullAddr else

		(** Check blocks accessible, not shared, and follow each other**)

		(* Check blocks are accessible *)
		perform isBlock1Accessible := readBlockAccessibleFromBlockEntryAddr block1InCurrPartAddr in
		perform isBlock2Accessible := readBlockAccessibleFromBlockEntryAddr block2InCurrPartAddr in
		if negb (isBlock1Accessible && isBlock2Accessible)
		then (* one/both blocks not accessible, stop *) ret nullAddr
		else

		(* Check blocks are not shared *)
		(* if accessible, then PDflag can't be set, we just need to check PDchild *)
		perform block1PDChildAddr := readSh1PDChildFromBlockEntryAddr	block1InCurrPartAddr in
		perform block1PDChildAddrIsNull := compareAddrToNull block1PDChildAddr in
		perform block2GlobalIdPDChild := readSh1PDChildFromBlockEntryAddr	block2InCurrPartAddr in
		perform block2GlobalIdPDChildIsNull := compareAddrToNull block2GlobalIdPDChild in
		if negb block1PDChildAddrIsNull || negb block2GlobalIdPDChildIsNull
		then (* one/both blocks shared, stop *) ret nullAddr
		else

		(* Check block 2 follows block 1 *)
		perform block1Next := readSCNextFromBlockEntryAddr block1InCurrPartAddr in
		perform isBlock2Next := getBeqAddr block2InCurrPartAddr block1Next in
		if negb isBlock2Next then (* no merge possible, stop*) ret nullAddr else

		(** Merge block 2 in block 1 *)

		(* replace block 1's next subblock with block 2's next subblock *)
		perform block2Next := readSCNextFromBlockEntryAddr block2InCurrPartAddr in
		writeSCNextFromBlockEntryAddr block1InCurrPartAddr block2Next ;;

		(* replace block 1's end address with block 2's end address *)
		perform block2End := readBlockEndFromBlockEntryAddr block2InCurrPartAddr in
		writeBlockEndFromBlockEntryAddr block1InCurrPartAddr block2End ;;

		(* remove block 2 entry *)
		freeSlot currentPart block2InCurrPartAddr ;;

		(** Parents and ancestors: set the block accessible again if there are no
		subblocks anymore of block 1 *)
		writeAccessibleToAncestorsIfNotCutRec currentPart
																					block1InCurrPartAddr
																					true ;;

		(** Remove the blocks to merge from the physical MPU and add the merged one
				instead *)
		removeBlockFromPhysicalMPU currentPart block1InCurrPartAddr ;;
		removeBlockFromPhysicalMPU currentPart block2InCurrPartAddr ;;
		enableBlockInMPU currentPart block1InCurrPartAddr MPURegionNb ;;

		(** RET block1's slot address *)
		ret idBlockToMerge1.

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

    <<idPD>>									the block to prepare (current partition or a child,
															resp. id = current partition or local id)
		<<projectedSlotsNb>>			the number of requested slots, -1 if forced prepare
		<<idRequisitionedBlock>>	the block used as the new kernel structure
*)
Definition prepare (idPD : paddr)
									(projectedSlotsNb : index)
									(idRequisitionedBlock : paddr) : LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
		perform currentPart := getCurPartition in

		(** Checks**)

		(* Check idPD is the current partition or one of its child*)
		perform globalIdPD := getGlobalIdPDCurrentOrChild currentPart idPD in
		perform addrIsNull := compareAddrToNull	globalIdPD in
		if addrIsNull
		then (* idPD is neither itself or a child partition, stop*) ret false
		else
		(* Check the max number of prepare hasn't been reached yet*)
		perform nbPrepare := readPDNbPrepare globalIdPD in
		perform maxnbprepare := getMaxNbPrepare in
		perform isMaxPrepare := Index.leb maxnbprepare nbPrepare in
		if isMaxPrepare then (* reached max prepare, stop*) ret false else

		(* Check that there is a need for a prepare: nb of free slots not enough
				to hold the projected slots or forced prepare) *)
		perform currentFreeSlotsNb := readPDNbFreeSlots globalIdPD in
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

		(* Find the requisitioned block in the current partition (with entry address) *)
    perform requisitionedBlockInCurrPartAddr := findBlockInKSWithAddr
																									currentPart
																									idRequisitionedBlock in
		perform addrIsNull := compareAddrToNull	requisitionedBlockInCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		(* Check block is in RAM *)
		perform isInRAM := checkBlockInRAM requisitionedBlockInCurrPartAddr in
		if negb isInRAM then (* not a RAM block, stop *) ret false else

		(* Check the block is big enough to hold a kernel structure*)
		perform blockSize := sizeOfBlock requisitionedBlockInCurrPartAddr in
		perform kStructureTotalLength := getKernelStructureTotalLength in
		perform isBlockTooSmall := Index.ltb blockSize kStructureTotalLength in
		if isBlockTooSmall then (* block is smaller than minimum  *) ret false else

		(* Check block is accessible and present*)
		(* TODO : No need to check if present since it has been found *)
		perform addrIsAccessible := readBlockAccessibleFromBlockEntryAddr
																	requisitionedBlockInCurrPartAddr in
		if negb addrIsAccessible then (* block is inaccessible *) ret false else
		perform addrIsPresent := readBlockPresentFromBlockEntryAddr
																	requisitionedBlockInCurrPartAddr in
		if negb addrIsPresent then (** block is not present *) ret false else

		(** Check the block is not shared *)
		(* if accessible, then PDflag can't be set, we just need to check PDchild is null*)
		perform PDChildAddr := readSh1PDChildFromBlockEntryAddr
															requisitionedBlockInCurrPartAddr in
		perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
		if negb PDChildAddrIsNull (*shouldn't be null*) then (*shared*) ret false else

		(* Init kernel structure (erase first) *)
		perform requisitionedBlockStart := readBlockStartFromBlockEntryAddr
																						requisitionedBlockInCurrPartAddr in
		perform requisitionedBlockEnd := readBlockEndFromBlockEntryAddr
																						requisitionedBlockInCurrPartAddr in
		perform isStructureInitialised := initStructure requisitionedBlockStart
																										requisitionedBlockEnd in
		if negb isStructureInitialised then (** error during init *) ret false else

		perform newKStructurePointer := getAddr requisitionedBlockStart in

		(** Set the requisitioned block inaccessible and remove it from the physical MPU*)
		writeBlockAccessibleFromBlockEntryAddr requisitionedBlockInCurrPartAddr false ;;
		removeBlockFromPhysicalMPU currentPart requisitionedBlockInCurrPartAddr ;;
		(** Parent and ancestors: set the block unaccessible if the block is not cut*)
		writeAccessibleToAncestorsIfNotCutRec currentPart
																					requisitionedBlockInCurrPartAddr
																					false ;;

		(** Link the new kernel structure in the targeted PD *)

		(** Insert the requisitioned block in the kernel structure list *)
		perform oldKStructurePointer := readPDStructurePointer globalIdPD in
		writeNextFromKernelStructureStart newKStructurePointer
																			oldKStructurePointer;;
		writePDStructurePointer globalIdPD newKStructurePointer;;

		(** Adjust the free slot pointer to the next free slot*)

		(* set the new free slots at the head of the previous free slots list *)
		perform lastidx := Index.pred kernelentriesnb in
		perform lastBlockEntryAddr := getBlockEntryAddrFromKernelStructureStart
																		newKStructurePointer
																		lastidx in
		perform currFirstFreeSlot := readPDFirstFreeSlotPointer globalIdPD in
		writeBlockEndFromBlockEntryAddr lastBlockEntryAddr currFirstFreeSlot ;;
		(* set the PD's first free slot pointer to the first entry of the new kernel structure*)
		writePDFirstFreeSlotPointer globalIdPD newKStructurePointer ;;
		(* new count = (count + number of new entries)*)
		perform currentNbFreeSlots := readPDNbFreeSlots globalIdPD in
		perform newNbFreeSlots := Index.addIdx currentNbFreeSlots kernelentriesnb in
		writePDNbFreeSlots globalIdPD newNbFreeSlots ;;
		(* new nbprepare = nbprepare + 1*)
		perform currentNbPrepare := readPDNbPrepare globalIdPD in
		perform succCurrentNbPrepare := Index.succ currentNbPrepare in
		writePDNbPrepare globalIdPD succCurrentNbPrepare ;;

		(** Special treatment for a prepare on a child: set the block as shared in
				the parent*)
		perform isCurrentPart := getBeqAddr globalIdPD currentPart in
		if negb isCurrentPart
		then (*prepare is done for another partition than itself*)
			writeSh1PDChildFromBlockEntryAddr requisitionedBlockInCurrPartAddr globalIdPD ;;
			ret true
		else
			ret true.

(** ** The addMemoryBlock PIP MPU service

    The [addMemoryBlock] system call adds a block to a child partition.
		The block is still accessible from the current partition (shared memory).

		Returns the shared block's id in the child:OK/NULL:NOK

    <<idPDchild>>			the child partition to share with
											(id = local id)
		<idBlockToShare>>	the block entry address where the block <idBlocktoShare> lies
											(id = local id)
		<<r w e >>				the rights to apply in the child partition
*)
Definition addMemoryBlock (idPDchild idBlockToShare: paddr) (r w e : bool)
																																: LLI paddr :=
		(** Get the current partition (Partition Descriptor) *)
		perform currentPart := getCurPartition in

		(* Find the block to share in the current partition (with block entry address) *)
    	perform blockToShareInCurrPartAddr := findBlockInKSWithAddr 	currentPart
																																idBlockToShare in
		perform addrIsNull := compareAddrToNull	blockToShareInCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret nullAddr else

		(* Check rights *)
		perform rcheck := checkRights blockToShareInCurrPartAddr r w e in
    	if negb rcheck then (* new rights not OK, stop *) ret nullAddr else

		(** Checks (blockToShareInCurrPartAddr checked before)*)

		(* Check idPDchild is a child of the current partition*)
		perform isChildCurrPart := checkChildOfCurrPart currentPart idPDchild in
		if negb isChildCurrPart
		then (* idPDchild is not a child partition, stop*) ret nullAddr
		else
		perform globalIdPDChild := readBlockStartFromBlockEntryAddr idPDchild in
		(* Check there are free slots in the the child to add the block to share*)
		perform currentFreeSlotsNb := readPDNbFreeSlots globalIdPDChild in
		perform zero := Index.zero in
		perform isFull := Index.leb currentFreeSlotsNb zero in
		if isFull then (* no free slots left, stop*) ret nullAddr else

		(* Check first free slot in the child is not null *)
		(* Useless check by knowing nbfreeslots > 0
				-> TODO : use NbFreeSlotsISNbFreeSlotsInList consistency property instead *)
		perform firstfreeslotInChild := readPDFirstFreeSlotPointer globalIdPDChild in
		perform slotIsNull := compareAddrToNull	firstfreeslotInChild in
		if slotIsNull	then (* first free slot is null, stop *) ret nullAddr else

		(* Check block is accessible and present*)
		(* TODO : no need to check present since it has been found, so it is present *)
		perform addrIsAccessible := readBlockAccessibleFromBlockEntryAddr
																	blockToShareInCurrPartAddr in
		if negb addrIsAccessible then (* block not accessible *) ret nullAddr else
		perform addrIsPresent := readBlockPresentFromBlockEntryAddr
																	blockToShareInCurrPartAddr in
		if negb addrIsPresent then (** block is not present *) ret nullAddr else

		(** Check the block is not shared *)
		(* if accessible, then PDflag can't be set, we just need to check PDchild is null*)
		perform PDChildAddr := readSh1PDChildFromBlockEntryAddr	blockToShareInCurrPartAddr in
		perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
		if negb PDChildAddrIsNull (*shouldn't be null*) then (*shared*) ret nullAddr else

		(* Check that the block to add is not the block
		 * containing the VIDT of the current partition. *)
		perform vidtBlockGlobalId := readPDVidt globalIdPDChild in
		if (beqAddr vidtBlockGlobalId blockToShareInCurrPartAddr) then ret nullAddr else

		(** Child: set the block to share in the child's first free slot*)
		(* the block start is set as origin in the child*)
		perform blockstart := readBlockStartFromBlockEntryAddr blockToShareInCurrPartAddr in
		perform blockend := readBlockEndFromBlockEntryAddr blockToShareInCurrPartAddr in
		perform blockToShareChildEntryAddr := insertNewEntry 	globalIdPDChild
																													blockstart blockend
																													blockstart
																													r w e
																													currentFreeSlotsNb
																													in

		(** Parent: register the shared block in Sh1*)
		writeSh1PDChildFromBlockEntryAddr blockToShareInCurrPartAddr globalIdPDChild;;
		writeSh1InChildLocationFromBlockEntryAddr blockToShareInCurrPartAddr
																							blockToShareChildEntryAddr;;
		(* RET shared block slot address in child *)
		ret blockToShareChildEntryAddr.

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

		<<idBlockToRemove>>	the block entry address where the block <idBlockToRemove> lies
*)
Definition removeMemoryBlock (idBlockToRemove: paddr) : LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
		perform currentPart := getCurPartition in

		(** Checks *)
		(* Find the block to remove in the current partition (with block entry address) *)
	  perform blockToRemoveInCurrPartAddr := findBlockInKSWithAddr 	currentPart
																																	idBlockToRemove in
		perform addrIsNull := compareAddrToNull	blockToRemoveInCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		(* Check the block is shared with valid addresses (not NULL)*)
		perform idPDchild := readSh1PDChildFromBlockEntryAddr
															blockToRemoveInCurrPartAddr in
		perform pdchildIsNull := compareAddrToNull idPDchild in
		if pdchildIsNull then(* block not shared or PD, stop *) ret false else

		perform blockToRemoveInChildAddr := readSh1InChildLocationFromBlockEntryAddr
																						blockToRemoveInCurrPartAddr in
		perform blockInChildIsNull := compareAddrToNull blockToRemoveInChildAddr in
		if blockInChildIsNull then(* block not shared or PD, stop *) ret false else

		(* Check that the block to remove is not the block
		* containing the VIDT of the current partition. *)
		perform vidtBlockGlobalId := readPDVidt idPDchild in
		if (beqAddr vidtBlockGlobalId blockToRemoveInCurrPartAddr) then ret false else

		(** Child (and grand-children): remove block if possible *)
		perform blockIsRemoved := removeBlockInChildAndDescendants
																		currentPart
																		blockToRemoveInCurrPartAddr
																		idPDchild
																		blockToRemoveInChildAddr in
		if negb blockIsRemoved then (* block not removed, stop*) ret false else

		(** Parent: remove block reference to the child *)
		writeSh1EntryFromBlockEntryAddr blockToRemoveInCurrPartAddr nullAddr false nullAddr ;;
		ret true.

(** ** The deletePartition PIP MPU service

    The [deletePartition] system call deletes the partition <idPDchildToDelete>
		which is a child of the current partition, e.g. prunes the partition tree by
		removing all references of the child and its respective blocks from the
		current partition

		Returns true:OK/false:NOK

    <<idPDchildToDelete>>	the child partition to delete
													(id = local id)
*)
Definition deletePartition (idPDchildToDelete: paddr) : LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
		perform currentPart := getCurPartition in

		(* Find the block to delete in the current partition *)
    perform blockToDeleteInCurrPartAddr := findBlockInKSWithAddr
																							currentPart
																							idPDchildToDelete in
		perform addrIsNull := compareAddrToNull	blockToDeleteInCurrPartAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		(** Checks *)
		(* Check idPDchild is a child of the current partition, no need for checkChildOfCurrPart*)
		perform isChild := readSh1PDFlagFromBlockEntryAddr blockToDeleteInCurrPartAddr in
		if negb isChild then (* idPDchild is not a child partition, stop*) ret false else

		(** Reset PD block TODO reset also kernel structures ?*)
		perform blockStartAddr := readBlockStartFromBlockEntryAddr
																	blockToDeleteInCurrPartAddr in
		perform blockEndAddr := readBlockEndFromBlockEntryAddr
																	blockToDeleteInCurrPartAddr in
		eraseBlock blockStartAddr blockEndAddr ;;

		(** Remove all shared blocks references in current partition (except PD child)*)
		perform currKernelStructureStart := readPDStructurePointer currentPart in
		perform globalIdPDChildToDelete := readBlockStartFromBlockEntryAddr idPDchildToDelete in
		deleteSharedBlocksRec currentPart currKernelStructureStart globalIdPDChildToDelete ;;

		(** Erase PD child entry: remove sharing and set accessible for current partition *)
		writeBlockAccessibleFromBlockEntryAddr blockToDeleteInCurrPartAddr true ;;
		writeSh1EntryFromBlockEntryAddr blockToDeleteInCurrPartAddr nullAddr false nullAddr ;;
		perform isCut := checkBlockCut blockToDeleteInCurrPartAddr in
		if isCut
		then	(* if the PD child block to remove is cut, remains not accessible in
							parent and ancestors *)
					ret true
		else (* if the PD child block to remove isn't cut, set it accessible to
							parent and ancestors *)
					writeAccessibleRec currentPart globalIdPDChildToDelete true ;;
					ret true.

(** ** The collect PIP MPU service

    The [collect] system call collects an empty structure (if possible) from
		the partition <idPD> (current partition or a child) and returns the retrieved
		block.

		Returns the collected structure block id :OK/NULL:NOK

    <<idPD>>	the current partition or a child
							(resp. id = current partition or local id)
*)
Definition collect (idPD: paddr) : LLI paddr :=
		(** Get the current partition (Partition Descriptor) *)
		perform currentPart := getCurPartition in

		(** Checks *)

		(* Check idPD is the current partition or one of its child*)
		perform globalIdPD := getGlobalIdPDCurrentOrChild currentPart idPD in
		perform addrIsNull := compareAddrToNull	globalIdPD in
		if addrIsNull
		then (* idPD is neither itself or a child partition, stop*) ret nullAddr
		else
		(* Check that if a collect is done on the current partition, there will
				still remain a structure because can't SELF remove the inital structure
				given by the parent *)
		perform nbPrepare := readPDNbPrepare globalIdPD in
		perform zero := MALInternal.Index.zero in
		perform one := Index.succ zero in
		perform onlyInitialStructureLeft := getBeqIdx one nbPrepare in
		perform isCurrentPart := getBeqAddr globalIdPD currentPart in
		if isCurrentPart && onlyInitialStructureLeft then (*stop*) ret nullAddr else

		(** Call recursive function: go through list of structure nodes and collect
				the first encountered free structure *)
		perform currStructureAddr := readPDStructurePointer globalIdPD in
		perform predStructureAddr := getPDStructurePointerAddrFromPD globalIdPD in
																(* location of the pointer, not the content *)
		collectStructureRec currentPart globalIdPD predStructureAddr currStructureAddr.


(** ** The mapMPU PIP MPU service

    The [mapMPU] system call maps the <idBlockToEnable> block owned by
		the partition <idPD> (current partition or a child) in the <MPURegionNb> MPU
		region.
		If the block is NULL, then the targeted MPU region is removed from the MPU.
		If the block was already mapped, moves the block to the given MPU region.

		Returns true:OK/false:NOK

    <<idPD>>	the current partition or a child (resp. id = global id or local id)
    <<idBlockToEnable>>	the block to map
    <<MPURegionNb>>	the physical MPU region number
*)
Definition mapMPU 	(idPD: paddr)
									(idBlockToEnable : paddr)
									(MPURegionNb : index) : LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
		perform currentPart := getCurPartition in

		(** Checks the idPD is current or child partition, block exists, accessible
				and present *)

		(* Check idPD is the current partition or one of its child*)
		perform globalIdPD := getGlobalIdPDCurrentOrChild currentPart idPD in
		perform addrIsNull := compareAddrToNull	globalIdPD in
		if addrIsNull
		then (* idPD is neither itself or a child partition, stop*) ret false
		else
		(* Check block to map is NULL, in such case remove the block at given index *)
		perform blockIsNull := compareAddrToNull	idBlockToEnable in
		if blockIsNull
		then (** Remove the block from the physical MPU if region nb is valid *)
				enableBlockInMPU globalIdPD nullAddr MPURegionNb
		else (** Replace the block from the physical MPU if region nb is valid *)

			(* Find the block to enable in the given partition (with block entry address) *)
		  perform blockToEnableAddr := findBlockInKSWithAddr globalIdPD idBlockToEnable in
			perform addrIsNull := compareAddrToNull	blockToEnableAddr in
			if addrIsNull then(* no block found, stop *) ret false else

			(* Check block is accessible and present*)
			perform addrIsAccessible := readBlockAccessibleFromBlockEntryAddr
																		blockToEnableAddr in
			if negb addrIsAccessible then (* block is not accessible *) ret false else
			perform addrIsPresent := readBlockPresentFromBlockEntryAddr
																		blockToEnableAddr in
			if negb addrIsPresent then (** block is not present *) ret false else

			(** Remove the block from the MPU if it was already mapped *)
			removeBlockFromPhysicalMPUIfAlreadyMapped globalIdPD blockToEnableAddr ;;

			(** Enable block in MPU if region nb is valid *)
			enableBlockInMPU globalIdPD blockToEnableAddr MPURegionNb.


(** ** The readMPU PIP MPU service

    The [readMPU] system call reads the content of the physical MPU owned by
		the partition <idPD> (current partition or a child) at the <MPURegionNb> MPU
		region.

		Returns block's id if exists, NULL or error otherwise

    <<idPD>>	the current partition or a child (resp. id = global id or local id)
    <<MPURegionNb>>	the physical MPU region number
*)
Definition readMPU (idPD: paddr) (MPURegionNb : index) : LLI paddr :=
		(** Get the current partition (Partition Descriptor) *)
		perform currentPart := getCurPartition in

		(** Checks the idPD is current or child partition *)

		(* Check idPD is the current partition or one of its child*)
		perform globalIdPD := getGlobalIdPDCurrentOrChild currentPart idPD in
		perform addrIsNull := compareAddrToNull	globalIdPD in
		if addrIsNull
		then (* idPD is neither itself or a child partition, stop*) ret nullAddr
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
		readBlockFromPhysicalMPU globalIdPD MPURegionNb.

(** ** The findBlock PIP MPU service

    The [findBlock] system call finds the block of the provided <addrInBlock> by
		searching in the blocks list of the partition <idPD>.

		Returns the block and its attributes if exists, error otherwise

    <<idPD>>	the current partition or a child (resp. id = global id or local id)
    <<addrInBlock>>	the address stemming from the block to find
	<<blockResult>> the block id were to write the attributes of the found block (if any)

	TODO: distinguish argument errors from block not found
*)
Definition findBlock (idPD: paddr) (addrInBlock : paddr) (blockResult: paddr) : LLI bool :=
		(** Get the current partition (Partition Descriptor) *)
		perform currentPart := getCurPartition in

		(** Checks the idPD is current or child partition *)

		(* Check idPD is the current partition or one of its child*)
		perform globalIdPD := getGlobalIdPDCurrentOrChild currentPart idPD in
		perform addrIsNull := compareAddrToNull	globalIdPD in
		if addrIsNull
		then (* idPD is neither itself or a child partition, stop*) ret false
		else
		(* Check that addrInBlock is present in globalIdPD *)
		perform blockAddr := findBelongingBlock globalIdPD addrInBlock in
		perform addrIsNull := compareAddrToNull	blockAddr in
		if addrIsNull then(* no block found, stop *) ret false else

		(* Check that blockResult is present and available in currentPart *)
		perform blockResultAddr := findBlockInKSWithAddr currentPart blockResult in
		perform addrIsNull := compareAddrToNull	blockResultAddr in
		if addrIsNull then(* no block found, stop *) ret false else
			(* Check block result is accessible *)
			perform addrIsAccessible := readBlockAccessibleFromBlockEntryAddr blockResultAddr in
			if negb addrIsAccessible then (* block is not accessible *) ret false else
			(* Check block result has RW rights *)
			perform r := readBlockRFromBlockEntryAddr blockResultAddr in
			perform w := readBlockWFromBlockEntryAddr blockResultAddr in
			if negb r then (* not readable, stop *) ret false else
			if negb w then (* not writable, stop *) ret false else
			(* Copy block attributes in block result *)
            copyBlock blockResultAddr blockAddr ;;
		ret true.

(**
 * The setVIDT PIP MPU service.
 *
 * The [setVIDT] system call sets the VIDT address in the partition
 * descriptor structure of the current partition or one of its child.
 *
 * It returns true if the VIDT block has been added to the partition
 * descriptor structure, false otherwise.
 *
 * <<pd>>       The ID of the block containing the partition
 *              descriptor structure of the current partition or
 *              one of its childs.
 *
 * <<vidtAddr>> The address of the VIDT or NULL to reset the VIDT
 *              address to NULL in the partition descriptor.
 *)
Definition setVIDT (pd vidtAddr : paddr) : LLI bool :=
  (* Check 1: Partition descriptor is not null *)
  perform curPd := getCurPartition in
  perform globalPd := getGlobalIdPDCurrentOrChild curPd pd in
  perform globalPdNull := compareAddrToNull globalPd in
  if globalPdNull then ret false else

  (* Check 2: VIDT address is null *)
  perform vidtAddrNull := compareAddrToNull vidtAddr in
  if vidtAddrNull
  then
    writePDVidt globalPd nullAddr ;;
    ret true
  else

  (* Check 3: VIDT block ID is not null *)
  perform vidtBlock := findBelongingBlock globalPd vidtAddr in
  perform vidtBlockNull := compareAddrToNull vidtBlock in
  if vidtBlockNull then ret false else

  (* Check 4: VIDT block is present *)
  perform present := readBlockPresentFromBlockEntryAddr vidtBlock in
  if negb present then ret false else

  (* Check 5: VIDT block is accessible *)
  perform accessible := readBlockAccessibleFromBlockEntryAddr vidtBlock in
  if negb accessible then ret false else

  (* Check 6: VIDT block does not overlap *)
  perform vidtSize := getVidtSize in
  perform vidtEndAddr := Paddr.addPaddrIdx vidtAddr vidtSize in
  perform vidtBlockEndAddr := readBlockEndFromBlockEntryAddr vidtBlock in
  perform overlap := Paddr.leb vidtBlockEndAddr vidtEndAddr in
  if overlap then ret false else

  if (beqAddr globalPd curPd)
  then
    (* The current partition is setting its VIDT. *)

    (* Check 8: VIDT block is not shared *)
    perform childPd := readSh1PDChildFromBlockEntryAddr vidtBlock in
    perform childPdNull := compareAddrToNull childPd in
    if negb childPdNull then ret false else

    writePDVidt globalPd vidtAddr ;;
    ret true

  else
    (* The current partition is setting the VIDT of one of its child. *)

    (* Check 9: VIDT block is not shared in a child *)
    perform vidtBlockChild := readSh1InChildLocationFromBlockEntryAddr vidtBlock in
    perform vidtBlockChildNull := compareAddrToNull vidtBlockChild in
    if negb vidtBlockChildNull then ret false else

    writePDVidt globalPd vidtAddr ;;
    ret true.
