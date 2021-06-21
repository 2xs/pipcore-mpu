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
    This file contains some internal functions used by services *)
Require Import Model.Monad Model.ADT Model.MAL.
Require Import Bool Arith List.

Open Scope mpu_state_scope.

(** Fixed fuel/timeout value to prove function termination *)
Definition N := 100.

(** The [getPd] function returns the page directory of a given partition *)
Definition getPd partition :=
  readPDTable partition.

(** The [compareAddrToNull] returns true if the given addr is equal to the fixed
    default addr (null) *)
Definition compareAddrToNull (p : paddr) : LLI bool :=
  perform nullAddr := getNullAddr in
  getBeqAddr nullAddr p.


(** The [findBlockInMPUStructAux] function recursively search by going through
		the current structure list and search for the <id_block_to_find>.
    Stop conditions:
        1: 	reached end of structure (maximum number of iterations)
        2: 	found <id_block_to_find>
        3: 	issue with the block, i.e. block not found, incorrect MPU address or
						block not present
    Recursive calls: until the current's structure last index
		Max recursion depth: number of kernel structure entries

		Returns the block's MPU address or NULL
*)
Fixpoint findBlockInMPUInStructAux (timeout : nat) (currentidx : index)
													(currentkernelstructure idblock: paddr) : LLI paddr :=
	match timeout with
		| 0 => getNullAddr
		| S timeout1 =>
										(** PROCESSING: check if the entry is the searched one *)
										perform entryaddr := getMPUEntryAddrFromKernelStructureStart
																						currentkernelstructure
																						currentidx in
										perform ispresent := readMPUPresentFromMPUEntryAddr entryaddr in
										perform mpustart := readMPUStartFromMPUEntryAddr entryaddr in
										if ispresent && beqAddr mpustart idblock then
											(** STOP CONDITION 2: block found *)
											ret entryaddr
										else
											(** continue search *)
											perform maxentriesnb := getKernelStructureEntriesNb in
											(** Our last index is table size - 1, as we're indexed on zero*)
											perform maxindex := Index.pred maxentriesnb in
											perform islastidx := getBeqIdx currentidx maxindex in
											if (islastidx)
											then
												(** STOP CONDITION 1: reached end of current structure,
																							block not found *)
												ret nullAddr
											else
												(** RECURSIVE call to the next index**)
												perform nextidx := Index.succ currentidx in
												findBlockInMPUInStructAux 	timeout1
																								nextidx
																								currentkernelstructure
																								idblock
	end.

(** The [findBlockInMPUAux] function recursively search by going through
		the structure list and search for the <id_block_to_find>.
    Stop conditions:
        1: 	reached end of structure list (maximum number of iterations)
        2: 	found <id_block_to_find>
        3: 	issue with the block, i.e. block not found, incorrect MPU address or
						block not present
    Recursive calls: until the end of the linked list
		Max recursion depth: length of the linked list + findBlockInMPUInStructAux

		Returns the found block's MPU address or NULL
*)
Fixpoint findBlockInMPUAux (timeout : nat)
													(currentkernelstructure idblock: paddr) : LLI paddr :=
	match timeout with
		| 0 => getNullAddr
		| S timeout1 =>	(** PROCESSING: seach for the block in the current structure *)
										perform zero := Index.zero in
										perform foundblock := findBlockInMPUInStructAux 	N
																																		zero
																																		currentkernelstructure
																																		idblock in
										perform isnull := getBeqAddr foundblock nullAddr in
										if negb isnull
										then
											(** STOP CONDITION 2: block found, stop *)
											ret foundblock
										else
											(** block not found in current structure, continue search *)
											perform nextkernelstructure := readNextFromKernelStructureStart
																												currentkernelstructure in
											perform isnull :=  getBeqAddr nextkernelstructure nullAddr in
											if isnull
											then
												(** STOP CONDITION 1: reached last structure, not found *)
												ret nullAddr
											else
												(** RECURSIVE call on the next structure *)
												findBlockInMPUAux timeout1 nextkernelstructure idblock
	end.



(* TODO: return Some MPUentry or None *)
(** The [findBlockInMPU] function fixes the timeout value of [findBlockInMPUAux] *)
Definition findBlockInMPU (idPD : paddr) (idBlock: paddr) : LLI paddr :=
	perform kernelstructurestart := readPDStructurePointer idPD in
	findBlockInMPUAux N kernelstructurestart idBlock.


(** The [findBlockInMPUWithAddrAux] function recursively search by going through
		the structure list and search for the <id_block_to_find> given the
    <MPU_address_block_to_find> (only look the entries at this address, so faster
		than blind search going through all the entries of a kernel structure)
    Stop conditions:
        1: 	reached end of structure list (maximum number of iterations)
        2: 	found <id_block_to_find>
        3: 	issue with the block, i.e. block not found, incorrect MPU address or
						block not present
    Recursive calls: until the end of the linked list
		Max recursion depth: length of the linked list

		Returns the block's MPU address or NULL
*)
Fixpoint findBlockInMPUWithAddrAux (timeout : nat)
																	(currentkernelstructure : paddr)
																	(blockMPUAddr: paddr) : LLI paddr :=
	match timeout with
		| 0 => getNullAddr
		| S timeout1 => (*Stop conditions 2 and 3: found block OR issue with the entry *)
										perform isMPUAddrAboveStart := Paddr.leb currentkernelstructure blockMPUAddr in
										perform zero := Index.zero in
										perform maxMPUAddrInStructure :=  getSh1EntryAddrFromKernelStructureStart
																													currentkernelstructure
																													zero in
										perform isMPUAddrBelowEnd := Paddr.leb blockMPUAddr maxMPUAddrInStructure in
										if isMPUAddrAboveStart && isMPUAddrBelowEnd
										then (* the provided address lies in this kernel structure*)
												(** Check the MPU entry exists and is present*)
												perform entryExists := checkEntry 	currentkernelstructure
																														blockMPUAddr in
												perform isPresent := readMPUPresentFromMPUEntryAddr blockMPUAddr in
												if entryExists && isPresent
												then (** STOP CONDITION 2: the block has been found and is present (i.e. it's a real block)*)
													ret blockMPUAddr
												else (** STOP CONDITION 3: bad arguments OR block not present *)
													ret nullAddr
										else (** RECURSIVE call: block not found in current structure,
														check next kernel structure*)
											perform nextKernelStructure := readNextFromKernelStructureStart
																											currentkernelstructure in
											perform isnull :=  getBeqAddr nextKernelStructure nullAddr in
											if isnull
											then
												(** STOP CONDITION 1: reached last structure, not found *)
												ret nullAddr
											else findBlockInMPUWithAddrAux timeout1
																										nextKernelStructure
																										blockMPUAddr
	end.


(* TODO: return Some MPUentry or None *)
(** The [findBlockInMPUWithAddr] function fixes the timeout value of
		[findBlockInMPUWithAddrAux] *)
Definition findBlockInMPUWithAddr (idPD blockMPUAddr: paddr) : LLI paddr :=
	(** All checks done before*)
	(** go through the MPU structure finding the block (== start address of MPU entry)*)
	perform kernelstructurestart := readPDStructurePointer idPD in
	findBlockInMPUWithAddrAux N kernelstructurestart blockMPUAddr.

(** The [checkBlockCut] function checks if the block at <mpublockaddr> has been
		cut or if it is a subblock of some other block*)
Definition checkBlockCut (mpublockaddr : paddr) : LLI bool :=
	perform blockOrigin := readSCOriginFromMPUEntryAddr mpublockaddr in
	perform blockStart := readMPUStartFromMPUEntryAddr mpublockaddr in
	perform blockNext := readSCNextFromMPUEntryAddr mpublockaddr in
	if beqAddr blockStart blockOrigin  && beqAddr blockNext nullAddr then
		(* Block hasn't been cut previously and not a subblock *)
		ret false
	else (* Block has been cut previously *) ret true.


(** The [writeAccessibleRecAux] function recursively write the accessible bit of
		value <accessible_bit> to the block identified as <idblock> to all ancestors
		of <pdbasepartition>
    Stop condition: reached root partiton (last ancestor)
    Processing: remove the block at this level of descendants
    Recursive calls: until the last ancestor
		Max recursion depth: number of ancestors
												+ max(findBlockInMPU, removeBlockFromPhysicalMPUIfNotAccessible)

		Returns true:OK/false:NOK*)
Fixpoint writeAccessibleRecAux 	timeout
																(pdbasepartition idblock : paddr)
																(accessiblebit : bool) : LLI bool :=
	match timeout with
		| 0 => ret false (* reached timeout *)
		| S timeout1 => 	if beqAddr pdbasepartition Constants.rootPart then
												(** STOP condition: reached root partition *)
												ret true
											else
												(** PROCESSING: write accessible bit in this ancestor
																				and if inaccessible also remove the
																				block from the real MPU *)
												perform pdparent := readPDParent pdbasepartition in
												perform blockInParentPartitionAddr := findBlockInMPU
																																	pdparent
																																	idblock in
												perform addrIsNull := compareAddrToNull
																									blockInParentPartitionAddr in
												if addrIsNull then ret false (*Shouldn't happen *) else
												writeMPUAccessibleFromMPUEntryAddr
														blockInParentPartitionAddr
														accessiblebit ;;
												removeBlockFromPhysicalMPUIfNotAccessible
																											pdparent
																											blockInParentPartitionAddr
																											accessiblebit ;;

												(** RECURSIVE call: write accessible in the remaining ancestors*)
												writeAccessibleRecAux timeout1 pdparent idblock accessiblebit
	end.


(** The [writeAccessibleRec] function fixes the timeout value of
		[writeAccessibleRecAux] *)
Definition writeAccessibleRec 	(pdbasepartition : paddr)
															(idblock : paddr)
															(accessiblebit : bool) : LLI bool :=
	writeAccessibleRecAux N pdbasepartition idblock accessiblebit.

(** The [writeAccessibleToAncestorsRecIfNotCut] sets the block <idblock>
	 	in all ancestors (including the parent) of <pdbasepartition> to
		accessible or inaccessible depending on the	<accessiblebit>. *)
Definition writeAccessibleToAncestorsIfNotCutRec (pdbasepartition : paddr)
																								(idblock : paddr)
																								(mpublockaddr : paddr)
																								(accessiblebit : bool) : LLI bool :=
		perform blockOrigin := readSCOriginFromMPUEntryAddr mpublockaddr in
		perform blockStart := readMPUStartFromMPUEntryAddr mpublockaddr in
		perform blockNext := readSCNextFromMPUEntryAddr mpublockaddr in
		if beqAddr blockStart blockOrigin  && beqAddr blockNext nullAddr then
			(* Block hasn't been cut previously, adjust accessible bit *)
			perform recWriteEnded := writeAccessibleRec pdbasepartition
																									idblock
																									accessiblebit in
			if negb recWriteEnded then (* timeout reached or error *) ret false else
			ret true
		else ret true.

(** The [insertNewEntry] function inserts the entry (<startaddr>, <endaddr>, true, true)
 	in the partition <pdinsertion> with block origin <origin>.
	Used in cutMemoryBlock and addMemoryBlock.
	The rights have been checked before.

	Returns the inserted entry's MPU address

	<<pdinsertion>> the PD where to insert the new entry
	<<startaddr>>		the new entry's start address
	<<endaddr>>			the new entry's end address
	<<origin>>			the new entry's block origin
	<<r w e >>			the new entry's rights
*)
Definition insertNewEntry 	(pdinsertion startaddr endaddr origin: paddr)
													(r w e : bool) 													: LLI paddr :=
	(** Checks have been done before: PD is correct, slot start and end @ are correct,
			block_origin is correct, there is one or more free slots *)
	perform newEntryMPUAddr := readPDFirstFreeSlotPointer pdinsertion in
	(** Adjust the free slot pointer to the next free slot*)
	perform newFirstFreeSlotAddr := readMPUEndFromMPUEntryAddr newEntryMPUAddr in
	writePDFirstFreeSlotPointer pdinsertion newFirstFreeSlotAddr ;;
	(** Adjust the free slots count to count - 1*)
	perform currentNbFreeSlots := readPDNbFreeSlots pdinsertion in
	perform predCurrentNbFreeSlots := Index.pred currentNbFreeSlots in
	writePDNbFreeSlots pdinsertion predCurrentNbFreeSlots ;;

	(** Insert the new MPU entry in the free slot*)
	writeMPUStartFromMPUEntryAddr newEntryMPUAddr startaddr ;;
	writeMPUEndFromMPUEntryAddr newEntryMPUAddr endaddr ;;
	writeMPUAccessibleFromMPUEntryAddr newEntryMPUAddr true ;;(** TODO accessible by default else no cut no add*)
	writeMPUPresentFromMPUEntryAddr newEntryMPUAddr true ;;(** TODO present by default*)
	writeMPURFromMPUEntryAddr newEntryMPUAddr r ;;
	writeMPUWFromMPUEntryAddr newEntryMPUAddr w ;;
	writeMPUXFromMPUEntryAddr newEntryMPUAddr e ;;
	writeSCOriginFromMPUEntryAddr newEntryMPUAddr origin ;;

	ret newEntryMPUAddr.

(** The [freeSlot] function frees the entry at <entrytofreempuaddr> in the
		partition <pdfree>.
	Used in mergeMemoryBlock and removeMemoryBlock

	Returns the freed slot's MPU address
*)
Definition freeSlot (pdfree entrytofreempuaddr: paddr) : LLI paddr :=
(** Checks have been done before: check idPD comes from Pip,
		check entryToFreeMPUAddress comes from Pip *)
		(* set default values in slot to free *)
		perform defaultMPUEntry := getDefaultMPUEntry in
		writeMPUEntryFromMPUEntryAddr entrytofreempuaddr defaultMPUEntry;;
		perform defaultSh1Entry := getDefaultSh1Entry in
		writeSh1EntryFromMPUEntryAddr entrytofreempuaddr defaultSh1Entry;;
		perform defaultSCEntry := getDefaultSCEntry in
		writeSCEntryFromMPUEntryAddr entrytofreempuaddr defaultSCEntry;;
		(* insert free slot in the free slot list *)
		perform currFirstFreeSlot := readPDFirstFreeSlotPointer pdfree in
		writeMPUEndFromMPUEntryAddr entrytofreempuaddr currFirstFreeSlot ;;
		writePDFirstFreeSlotPointer pdfree entrytofreempuaddr ;;
		(* add 1 to the number of free slots*)
		perform nbfreeslots := readPDNbFreeSlots pdfree in
		perform nbfreeslotssucc := Index.succ nbfreeslots in
		writePDNbFreeSlots pdfree nbfreeslotssucc ;;
		(* return the freed slot's MPU address *)
		ret entrytofreempuaddr.


(** The [checkChild] function checks that <idPDchild> is a child of <idPDparent>
		by looking for the child in the supposed parent's kernel structure.
		Returns true:OK/false:NOK
*)
Definition checkChild (idPDparent idPDchild : paddr) : LLI bool :=
	(* TODO : check idPDparent is valid*)
	perform blockInParentPartAddr := findBlockInMPU idPDparent idPDchild in
	perform addrIsNull := compareAddrToNull	blockInParentPartAddr in
	if addrIsNull then(** child block not found, stop *) ret false else

	perform isChild := readSh1PDFlagFromMPUEntryAddr blockInParentPartAddr in
	if negb isChild then (* idPDchild is not a child partition, stop*) ret false else
	ret true.

(** ** The addMemoryBlockCommon Internal function

    The [addMemoryBlockCommon] system call adds a block to a child partition
		The block is still accessible from the current partition (shared memory)

		Returns the shared block's slot address in the child:OK/NULL:NOK

    <<idPDchild>>						the child partition to share with
		<<blockToShareMPUAddr>>	the block to share MPU address in the parent
		<<r w e >>							the rights to apply in the child partition
*)
Definition addMemoryBlockCommon 	(idPDchild blockToShareMPUAddr: paddr)
																(r w e : bool) : LLI paddr :=
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks (blockToShareMPUAddr checked before)*)

		(* Check idPDchild is a child of the current partition*)
		perform isChildCurrPart := checkChild currentPart idPDchild in
		if negb isChildCurrPart
		then (* idPDchild is not a child partition, stop*) ret nullAddr
		else

		(* Check there are free slots in the the child to add the block to share*)
		perform currentFreeSlotsNb := readPDNbFreeSlots idPDchild in
		perform zero := Index.zero in
		perform isFull := Index.leb currentFreeSlotsNb zero in
		if isFull then (* no free slots left, stop*) ret nullAddr else

		(* Check block is accessible and present*)
		perform addrIsAccessible := readMPUAccessibleFromMPUEntryAddr
																	blockToShareMPUAddr in
		if negb addrIsAccessible then (* block not accessible *) ret nullAddr else
		perform addrIsPresent := readMPUPresentFromMPUEntryAddr
																	blockToShareMPUAddr in
		if negb addrIsPresent then (** block is not present *) ret nullAddr else


		(** Child: set the block to share in the child's first free slot*)
		(* the block start is set as origin in the child*)
		perform blockstart := readMPUStartFromMPUEntryAddr blockToShareMPUAddr in
		perform blockend := readMPUEndFromMPUEntryAddr blockToShareMPUAddr in
		perform blockToShareChildMPUAddr := insertNewEntry 	idPDchild
																												blockstart blockend
																												blockstart
																												r w e
																												in

		(** Parent: register the shared block in Sh1*)
		writeSh1PDChildFromMPUEntryAddr blockToShareMPUAddr idPDchild;;
		writeSh1InChildLocationFromMPUEntryAddr blockToShareMPUAddr
																						blockToShareChildMPUAddr;;
		(* RET shared block slot address in child *)
		ret blockToShareChildMPUAddr.

(** The [removeBlockInDescendantsRecAux] function recursively removes the block
		identified at MPU address <currLevelBlockToRemoveAddr> of the current
		descendant by going through the descendants and remove the block on the way
    Stop condition: reached last descendant (leaf) (maximum number of iterations)
    Processing: remove the block at this level of descendants
    Recursive calls: until the last descendant
		Max recursion depth: number of descendants

		Returns unit*)
Fixpoint removeBlockInDescendantsRecAux (timeout : nat)
																				(currLevelIdPD : paddr)
																				(currLevelBlockToRemoveAddr : paddr)
																																	: LLI bool :=
	match timeout with
		| 0 => ret false (*reached timeout*)
		| S timeout1 => perform isNull := compareAddrToNull currLevelBlockToRemoveAddr in
										if isNull
										then (** STOP condition: reached last descendant (leaf)*)
											ret true
										else
											(* get the descendant's references before block deletion *)
											perform nextdescendant := readSh1PDChildFromMPUEntryAddr
																									currLevelBlockToRemoveAddr in
											perform blockToRemoveInDescendantAddr :=
															readSh1InChildLocationFromMPUEntryAddr
																currLevelBlockToRemoveAddr in
											(** PROCESSING: remove the block for this descendant *)
											freeSlot currLevelIdPD currLevelBlockToRemoveAddr ;;

											(** RECURSIVE call: remove block in the remaining descendants*)
											removeBlockInDescendantsRecAux 	timeout1
																											nextdescendant
																											blockToRemoveInDescendantAddr
	end.

(** The [removeBlockInDescendantsRec] fixes the timeout value of
		[removeBlockInDescendantsRecAux] *)
Definition removeBlockInDescendantsRec 	(currLevelIdPD : paddr)
																				(currLevelBlockToRemoveAddr : paddr)
																																	: LLI bool :=
	removeBlockInDescendantsRecAux N currLevelIdPD currLevelBlockToRemoveAddr.

(** The [checkRemoveSubblocksRecAux] function recursively check by going through
		the subblocks starting from <subblockAddr>
    Check all cuts are not shared and accessible and present
		Stop conditions:
        1: reached last subblock (maximum number of iterations)
        2: the subblock is not accessible, not present or shared
    Recursive calls: until the last subblock
		Max recursion depth: length of the subblocks linked list

		Returns true:OK/false:NOK*)
Fixpoint checkRemoveSubblocksRecAux (timeout : nat) (subblockAddr : paddr): LLI bool :=
	match timeout with
		| 0 => ret false (*reached timeout*)
		| S timeout1 => perform isNull := compareAddrToNull subblockAddr in
										if isNull
										then (** STOP condition 1: reached last subblock*) ret true
										else
												(** PROCESSING: checks *)
												perform isAccessible := readMPUAccessibleFromMPUEntryAddr
																										subblockAddr in
												perform isPresent := readMPUPresentFromMPUEntryAddr
																										subblockAddr in
												(* if accessible, then PDflag can't be set, we just need to check PDchild *)
												perform PDChildAddr := readSh1PDChildFromMPUEntryAddr	subblockAddr in
												perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
												if negb (isAccessible && isPresent && PDChildAddrIsNull)
												then (** STOP condition 2: the subblock is not accessible,
															not present or is shared *) ret false
												else (** RECURSIVE call: check the next subblock*)
														perform nextsubblock := readSCNextFromMPUEntryAddr
																												subblockAddr in
														checkRemoveSubblocksRecAux timeout1 nextsubblock
	end.

(** The [checkRemoveSubblocksRec] fixes the timeout value of
		[checkRemoveSubblocksRecAux] *)
Definition checkRemoveSubblocksRec (subblockAddr : paddr): LLI bool :=
	checkRemoveSubblocksRecAux N subblockAddr.

(** The [removeSubblocksRecAux] function recursively removes all subblocks
		by going through the subblocks and free them
    Stop condition: reached last subblock (maximum number of iterations)
    Processing: free the subblock's slot
    Recursive calls: until last subblock
		ax recursion depth: lenth of the subblocks linked list

		Returns true:OK/false:NOK*)
Fixpoint removeSubblocksRecAux (timeout : nat) (idPDchild subblockAddr : paddr)
																																	: LLI bool :=
	match timeout with
		| 0 => ret false (*reached timeout*)
		| S timeout1 => perform isNull := compareAddrToNull subblockAddr in
										if isNull
										then (** STOP condition: reached last subblock*) ret true
										else
												(** PROCESSING: free the subblock *)
												perform nextsubblock := readSCNextFromMPUEntryAddr
																										subblockAddr in
												freeSlot idPDchild subblockAddr ;;
												(** RECURSIVE call: check the next subblock*)
												removeSubblocksRecAux timeout1 idPDchild nextsubblock
	end.

(** The [removeSubblocksRec] fixes the timeout value of
		[removeSubblocksRecAux] *)
Definition removeSubblocksRec (idPDchild subblockAddr : paddr): LLI bool :=
	removeSubblocksRecAux N idPDchild subblockAddr.

(** The [removeBlockInChildAndDescendants] function removes the block <idBlockToRemove>
		from the child and potential descendants.
		There are two treatments depending if the block to remove is cut or not:
			- not cut: remove the block in the child and all descendants if it is
								accessible (e.g. not used as kernel structure in the child or
								in the descedants nor cut in the descendants)
			- cut: remove the block only if all subblocks are accessible, present and
						not shared

		Returns true:OK/false:NOK

    <<currentPart>>					the current/parent partition
		<<idPDchild>>						the child partition to remove from
		<<idBlockToRemove>>			the block to remove
		<<blockToRemoveInCurrPartAddr>>	the block to remove MPU address in the parent
*)
Definition removeBlockInChildAndDescendants (currentPart
																						idPDchild
																						idBlockToRemove
																						blockToRemoveInCurrPartAddr : paddr)
																																	: LLI bool :=
		perform blockToRemoveInChildAddr := readSh1InChildLocationFromMPUEntryAddr
																						blockToRemoveInCurrPartAddr in
		perform isBlockCut := checkBlockCut blockToRemoveInChildAddr in
		if negb isBlockCut
		then (** Case 1: block not cut in the child partition -> remove the
							block in the child and all grand-children *)

				(* 	check block is accessible *)
				perform addrIsAccessible := readMPUAccessibleFromMPUEntryAddr
																			blockToRemoveInChildAddr in
				if negb addrIsAccessible
				then
						(* block is inaccessible, it is used as kernel structure or cut in
						grand-children, stop *)
						ret false
				else
						(* block is accessible and only used as shared memory in grand-children*)

						(** Remove shared block from child and all grand-children *)
						perform recRemoveInDescendantsEnded := removeBlockInDescendantsRec
																											idPDchild
																											blockToRemoveInChildAddr in
						if negb recRemoveInDescendantsEnded then (* timeout reached *) ret false else
						ret true

		else (** Case 2: block cut in the child partition -> remove all
							subblocks in the child*)

				(* Check all subblocks are not shared, accessible, and present *)
				perform isRemovePossible := checkRemoveSubblocksRec
																				blockToRemoveInChildAddr in
				if negb isRemovePossible then (* remove impossible, stop *) ret false else

				(** Remove all subblocks  from the child*)
				perform recRemoveSubblocksEnded := removeSubblocksRec
																											idPDchild
																											blockToRemoveInChildAddr in
				if negb recRemoveSubblocksEnded then (* timeout reached *) ret false else

				(** Set back the block as accessible in the ancestors because it was cut *)
				writeMPUAccessibleFromMPUEntryAddr blockToRemoveInCurrPartAddr true ;;
				perform recWriteEnded := writeAccessibleRec currentPart
																										idBlockToRemove
																										true in
				if negb recWriteEnded then (* timeout reached or error *) ret false else
				ret true.

(** ** The removeMemoryBlockCommon Internal function

    The [removeMemoryBlockCommon] system call removes a block from a child partition
		The block could be cut in the child partition but all subblocks still accessible
    This operation succeeds for any shared memory block previously added, but
		fails if the purpose of the block is not shared memory anymore,
		in particular in such cases:
        - The block can't be removed if the child or its descendants used it
				(or part of it) as a kernel structure
        - The block can't be removed if the child's descendants cut the block

		Returns true:OK/false:NOK

    <<idPDchild>>						the child partition to remove from
		<<blockToRemoveMPUAddr>>	the block to remove MPU address in the parent
*)
Definition removeMemoryBlockCommon (	idPDchild
																		blockToRemoveInCurrPartAddr: paddr) : LLI bool :=

		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks (blockToRemoveMPUAddr checked before from idBlockToRemove)*)

		(* Check the provided idPDchild corresponds to the child to whom the block
				has been previously given (if given)*)
		perform pdchildblock := readSh1PDChildFromMPUEntryAddr
																blockToRemoveInCurrPartAddr in
		perform hasChildBlock := getBeqAddr idPDchild pdchildblock in
		if negb hasChildBlock then (* no correspondance, stop *) ret false else

		(** Child (and grand-children): remove block if possible *)
		perform idBlockToRemove := readMPUStartFromMPUEntryAddr blockToRemoveInCurrPartAddr in
		perform blockIsRemoved := removeBlockInChildAndDescendants
																		currentPart
																		idPDchild
																		idBlockToRemove
																		blockToRemoveInCurrPartAddr in
		if negb blockIsRemoved then (* block not removed, stop*) ret false else

		(** Parent: remove block reference to the child *)
		perform defaultSh1Entry := getDefaultSh1Entry in
		writeSh1EntryFromMPUEntryAddr blockToRemoveInCurrPartAddr defaultSh1Entry ;;
		ret true.


(** The [sizeOfBlock] function computes the size of block referenced in an MPU entry
	Returns the difference between the block's end and start addresses
*)
Definition sizeOfBlock (mpuentryaddr : paddr) : LLI index :=
	perform startAddr := readMPUStartFromMPUEntryAddr mpuentryaddr in
	perform endAddr := readMPUEndFromMPUEntryAddr mpuentryaddr in
	Paddr.subPaddr endAddr startAddr.

(** The [initPDTable] function initializes the PD table pointed by <pdtableaddr>
		with the default PD table
	Returns unit
*)
Definition initPDTable (pdtablepaddr : paddr) : LLI unit :=
	perform emptytable := getEmptyPDTable in
	writePDTable pdtablepaddr emptytable.

(** The [initMPUEntryRec] function recursively initializes all MPU entries from
		<indexCurr> to 0 of kernel structure located at <kernelStructureStartAddr>
		by constructing a linked list of all entries representing the free slots.
		The indexes are 0-indexed.
	Max recursion depth: number of kernel structure entries

	Returns true:OK/false:NOK
*)
Fixpoint initMPUEntryRecAux 	(timeout : nat)
															(kernelStructureStartAddr : paddr)
															(indexCurr : index): LLI bool :=
	match timeout with
	| 0 => 	ret false (* timeout reached *)
	| S timeout1 =>
									(** PROCESSING: set default values in current entry *)
									perform idxsucc := Index.succ indexCurr in
									(* current entry points to the next via the endAddr field*)
									perform nextEntryPointer := getMPUEntryAddrFromKernelStructureStart
																								kernelStructureStartAddr
																								idxsucc in
									perform mpuEntry := buildMPUEntry
																				nullAddr
																				nextEntryPointer
																				false
																				false in
									perform currEntryPointer := getMPUEntryAddrFromKernelStructureStart
																								kernelStructureStartAddr
																								indexCurr in
									writeMPUEntryWithIndexFromMPUEntryAddr
											currEntryPointer
											indexCurr
											mpuEntry;;

									perform zero := Index.zero in
									if beqIdx indexCurr zero
									then (** STOP condition: parsed all entries *)
										ret true
									else
										(** RECURSIVE call: write default values in precedent index *)
										perform idxpred := Index.pred indexCurr in
										initMPUEntryRecAux timeout1 kernelStructureStartAddr idxpred
	end.

(** The [initMPUStructure] function initializes the MPU part of the kernel
		structure located at <kernelStructureStartAddr>. It creates the linked list
		of the free slots. The MPU indexes are 0-indexed. The last index is special,
		it should point to NULL.
	Returns true:OK/false:NOK
*)
Definition initMPUStructure (kernelStructureStartAddr : paddr) : LLI bool :=
	perform entriesnb := getKernelStructureEntriesNb in
	perform lastindex := Index.pred entriesnb in (* 0-indexed*)
	(** Initialize the MPU entries until the penultimate entry, the last entry is
			is not identical*)
	perform secondlastindex := Index.pred lastindex in
	perform initEnded := initMPUEntryRecAux N
																					kernelStructureStartAddr
																					secondlastindex in
	if negb initEnded then (* timeout reached *) ret false else
	(** Last entry has no following entry: make it point to NULL*)
	perform lastMPUEntry := buildMPUEntry nullAddr
																				nullAddr
																				false
																				false in
	perform lastEntryPointer := getMPUEntryAddrFromKernelStructureStart
									 								kernelStructureStartAddr
																	lastindex in
	writeMPUEntryWithIndexFromMPUEntryAddr 	lastEntryPointer
																					lastindex
																					lastMPUEntry;;
	ret true.


(** The [initSh1EntryRec] function recursively initializes all Sh1 entries from
		<indexCurr> to 0 of kernel structure located at <kernelStructureStartAddr>
		wit the default Sh1 entry value.
		The indexes are 0-indexed.
	Max recursion depth: number of kernel structure entries

	Returns true:OK/false:NOK
*)
Fixpoint initSh1EntryRecAux 	(timeout : nat) (kernelStructureStartAddr : paddr)
													(indexCurr : index) : LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 => (** PROCESSING: set default values in current entry *)
										perform defaultSh1Entry := getDefaultSh1Entry in
										perform currEntryPointer := getMPUEntryAddrFromKernelStructureStart
																									kernelStructureStartAddr
																									indexCurr in
										writeSh1EntryFromMPUEntryAddr currEntryPointer
																									defaultSh1Entry;;
										perform zero := Index.zero in
										if beqIdx indexCurr zero
										then (** STOP condition: parsed all entries *)
											ret true
										else
											(** RECURSIVE call: write default values in precedent index *)
											perform idxpred := Index.pred indexCurr in
											initSh1EntryRecAux timeout1 kernelStructureStartAddr idxpred
	end.

(** The [initSh1Structure] function initializes the Sh1 part of the kernel
		structure located at <kernelStructureStartAddr>. The indexes are
		0-indexed.
	Returns true:OK/false:NOK
*)
Definition initSh1Structure (kernelStructureStartAddr : paddr) : LLI bool :=
	perform entriesnb := getKernelStructureEntriesNb in
	perform lastindex := Index.pred entriesnb in (* 0-indexed*)
	perform initEnded := initSh1EntryRecAux N kernelStructureStartAddr lastindex in
	if negb initEnded then (* timeout reached *) ret false else
	ret true.


(** The [initSCEntryRec] function recursively initializes all SC entries from
		<indexCurr> to 0 of kernel structure located at <kernelStructureStartAddr>
		wit the default SC entry value.
		The indexes are 0-indexed.
	Max recursion depth: number of kernel structure entries

	Returns true:OK/false:NOK
*)
Fixpoint initSCEntryRecAux 	(timeout : nat) (kernelStructureStartAddr : paddr)
													(indexCurr : index) : LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 => (** PROCESSING: set default values in current entry *)
										perform defaultSCEntry := getDefaultSCEntry in
										perform currEntryPointer := getMPUEntryAddrFromKernelStructureStart
																									kernelStructureStartAddr
																									indexCurr in
										writeSCEntryFromMPUEntryAddr 	currEntryPointer
																									defaultSCEntry;;
										perform zero := Index.zero in
										if beqIdx indexCurr zero
										then (** STOP condition: parsed all entries *)
											ret true
										else
											(** RECURSIVE call: write default values in precedent index *)
											perform idxpred := Index.pred indexCurr in
											initSCEntryRecAux timeout1 kernelStructureStartAddr idxpred
	end.

(** The [initSCStructure] function initializes the SC part of the kernel
		structure located at <kernelStructureStartAddr>. The indexes are
		0-indexed.
	Returns true:OK/false:NOK
*)
Definition initSCStructure (kernelStructureStartAddr : paddr) : LLI bool :=
	perform entriesnb := getKernelStructureEntriesNb in
	perform lastindex := Index.pred entriesnb in (* 0-indexed*)
	perform initEnded := initSCEntryRecAux N kernelStructureStartAddr lastindex in
	if negb initEnded then (* timeout reached *) ret false else
	ret true.

(** The [initSh1Structure] function initializes the Sh1 part of the kernel
		structure located at <kernelStructureStartAddr>. The indexes are
		0-indexed.
	Returns true:OK/false:NOK
*)
Definition initStructure (kernelStructureStartAddr kernelStructureEndAddr: paddr)
																																	: LLI bool :=
	perform isBlockErased := 	eraseBlock 	kernelStructureStartAddr
																				kernelStructureEndAddr in
	if negb isBlockErased then (** error in block erasure *) ret false else
	initMPUStructure kernelStructureStartAddr ;;
	initSh1Structure kernelStructureStartAddr ;;
	initSCStructure kernelStructureStartAddr ;;
	writeNextFromKernelStructureStart kernelStructureStartAddr nullAddr ;;
	ret true.

(** The [deleteSharedBlocksInStructRecAux] function recursively removes all blocks
		belonging to the child <idPDchildToDelete> in the <currentPart> by going
		through all entries of the structure <kernelStructureStartAddr> from the
		last entry
		Stop condition: reached first entry of the structure (maximum number of iterations)
		Processing: remove all blocks shared with the child to delete in the current
								structure
    Recursive calls: until the first entry
		Max recursion depth: number of kernel structure entries + writeAccessibleRec

		Returns true:OK/false:NOK*)
Fixpoint deleteSharedBlocksInStructRecAux 	(timeout : nat)
																						(currentPart : paddr)
																						(kernelStructureStartAddr : paddr)
																						(idPDchildToDelete : paddr)
																						(currIndex : index): LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 =>
										(** PROCESSING: remove all blocks shared with the child to
																		delete in the current structure *)
										perform currMPUEntryAddr :=	getMPUEntryAddrFromKernelStructureStart
																											kernelStructureStartAddr
																											currIndex in
										perform blockID := readMPUStartFromMPUEntryAddr
																					currMPUEntryAddr in
										perform currPDChild := readSh1PDChildFromMPUEntryAddr
																							currMPUEntryAddr in
										if beqAddr currPDChild idPDchildToDelete
										then (* the slot corresponds to memory shared or prepared
													with the child to destruct, remove sharing *)
														(* Set block accessible in current partition *)
														writeMPUAccessibleFromMPUEntryAddr 	currMPUEntryAddr
																																true ;;
														perform defaultSh1Entry := getDefaultSh1Entry in
														writeSh1EntryFromMPUEntryAddr currMPUEntryAddr
																													defaultSh1Entry ;;
													(* 	whatever the accessibility of the block that could
															not be accessible because of the child's operations,
															set the block accessible again*)
													perform isCut := checkBlockCut currMPUEntryAddr in
													if negb isCut
													then (* if the block isn't cut in the current
																partition, set as accessible in the ancestors *)
																writeAccessibleRec currentPart blockID true ;;

																perform zero := Index.zero in
																if beqIdx currIndex zero
																then
																	(** STOP condition: parsed all entries of the 
																											current structure *)
																	ret true
																else
																	(** RECURSIVE call: delete block of next entry *)
																	perform idxpred := Index.pred currIndex in
																	deleteSharedBlocksInStructRecAux 	timeout1
																																		currentPart
																																		kernelStructureStartAddr
																																		idPDchildToDelete
																																		idxpred
													else	(* the block is cut, don't set it back as
																		accessible in ancestors, continue *)
																perform zero := Index.zero in
																if beqIdx currIndex zero
																then
																	(** STOP condition: parsed all entries of the 
																											current structure *)
																	ret true
																else
																	(** RECURSIVE call: delete block of next entry *)
																	perform idxpred := Index.pred currIndex in
																	deleteSharedBlocksInStructRecAux 	timeout1
																																		currentPart
																																		kernelStructureStartAddr
																																		idPDchildToDelete
																																		idxpred
										else
													(* current block entry is not shared, check next entry *)
													perform zero := Index.zero in
													if beqIdx currIndex zero
													then
														(** STOP condition: parsed all entries *)
														ret true
													else
														(** RECURSIVE call: delete block of next entry *)
														perform idxpred := Index.pred currIndex in
														deleteSharedBlocksInStructRecAux 	timeout1
																															currentPart
																															kernelStructureStartAddr
																															idPDchildToDelete
																															idxpred
	end.

(** The [deleteSharedBlocksRecAux] function recursively removes all blocks
		belonging to the child <idPDchildToDelete> in the <currentPart> by going
		through the structure list
		Stop condition: reached end of structure list (maximum number of iterations)
		Processing: remove all blocks shared with the child to delete in the current
								structure
    Recursive calls: until the end of the linked list
		Max recursion depth: length of the linked list + deleteSharedBlocksInStructRecAux

		Returns true:OK/false:NOK*)
Fixpoint deleteSharedBlocksRecAux 	(timeout : nat)
																		(currentPart : paddr)
																		(currKernelStructureStartAddr : paddr)
																		(idPDchildToDelete : paddr) : LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 =>
										if beqAddr currKernelStructureStartAddr nullAddr
										then
											(** STOP condition: reached end of structure list *)
											ret true
										else
											(** PROCESSING: remove all blocks shared with the child to
																			delete in the current structure *)
											perform entriesnb := getKernelStructureEntriesNb in
											perform lastindex := Index.pred entriesnb in (* 0-indexed*)
											deleteSharedBlocksInStructRecAux 	N
																												currentPart
																												currKernelStructureStartAddr
																												idPDchildToDelete
																												lastindex;;
											(** RECURSIVE call: remove shared blocks in the next structure *)
											perform nextStructureAddr := readNextFromKernelStructureStart
																											currKernelStructureStartAddr in
											deleteSharedBlocksRecAux timeout1
																							currentPart
																							nextStructureAddr
																							idPDchildToDelete
	end.

(** The [deleteSharedBlocksRec] function fixes the timeout value of
		[deleteSharedBlocksRecAux] *)
Definition deleteSharedBlocksRec (currentPart : paddr)
																(kernelStructureStartAddr : paddr)
																(idPDchildToDelete : paddr) : LLI bool :=
	deleteSharedBlocksRecAux N currentPart kernelStructureStartAddr idPDchildToDelete.


(** The [removeStructure] function pulls the structure to be collected out of
		the list of structures.
		Returns unit

    <<idPD>>									the PD where the collect is done
		<<predStructureAddr>>			the structure before the stucture to be collected
		<<collectStructureAddr>>	the structure to be collected

 *)
Definition removeStructure (idPD predStructureAddr collectStructureAddr : paddr)
																																: LLI unit :=
	(* remove the structure to collect from the kernel structure linked list *)
	perform nextStructureAddr := readNextFromKernelStructureStart collectStructureAddr in
	perform firstStructure := readPDStructurePointer idPD in
	perform isFirstStructure := getBeqAddr collectStructureAddr firstStructure in
	if isFirstStructure
	then (* Special case: structure to remove is the first structure -> adjust pointers *)
				(* 	set the PD's structure pointer to the next structure (which could
						be NULL if it was the last TODO compressed statements*)
				writePDStructurePointer idPD nextStructureAddr ;;
				ret tt
	else (* the structure to remove is somewhere in the middle of the list of
					structures, link previous structure to next structure *)
				writeNextFromKernelStructureStart predStructureAddr nextStructureAddr ;;
				ret tt.

(** The [checkStructureEmptyRecAux] function recursively checks the current
		structure is empty from last entry until first entry.

		Stop conditions:
				1: found a used entry
				2: all entries of the structure are empty (maximum number of iterations)
		Processing: check the current entry
    Recursive calls: until all entries are cheked
		Max recursion depth: number of kernel structure entries

		Returns true:structure empty/false:structure not empty

		<<currIndex>>				the current checked index
    <<structureAddr>>		the structure to check
*)
Fixpoint checkStructureEmptyRecAux 	(timeout : nat)
																		(structureAddr :paddr)
																		(currIndex : index): LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 =>	(** PROCESSING: check the current entry *)
										perform currMPUEntryAddr :=	getMPUEntryAddrFromKernelStructureStart
																										structureAddr
																										currIndex in
										perform isPresent := readMPUPresentFromMPUEntryAddr
																						currMPUEntryAddr in
										if isPresent
										then
												(** STOP condition 1: found a used entry *)
												ret false
										else
											perform zero := Index.zero in
											if beqIdx currIndex zero
											then
													(** STOP condition 2: all entries parsed, structure is
															empty *)
													ret true
											else
													(** RECURSIVE call: check previous entry *)
													perform idxpred := Index.pred currIndex in
													checkStructureEmptyRecAux timeout1
																										structureAddr
																										idxpred
	end.

(** The [collectFreeSlotsRecAux] function recursively removes all free slots
		belonging to the empty structure that is collected by going through the free
		slots list.

		Stop condition: reached end of free slots list (maximum number of iterations)
		Processing: remove slots to collect from free slots list
    Recursive calls: until the end of the list
		Max recursion depth: length of the free slots linked list

		Returns unit

		<<currFreeSlotAddr>>				the recursive checked free slot
    <<predFreeSlotAddr>>				pointer to the previous free slot
		<<idPD>>										the PD from where to collect
		<<structureCollectAddr>>		the structure to collect
*)
Fixpoint collectFreeSlotsRecAux (timeout : nat)
																(predFreeSlotAddr currFreeSlotAddr : paddr)
																(idPD : paddr)
																(structureCollectAddr : paddr) : LLI unit :=

match timeout with
		| 0 => 	ret tt (* timeout reached *)
		| S timeout1 =>

										if beqAddr currFreeSlotAddr nullAddr
										then
											(** STOP condition: reached end of free slots list *)
											ret tt
										else
											(** PROCESSING: remove slots to collect from free slots list*)

											(* compute the current slot's kernel structure *)
											perform MPUEntryIndex := readMPUIndexFromMPUEntryAddr
																										currFreeSlotAddr in
											perform slotKStructureStart := getKernelStructureStartAddr
																												currFreeSlotAddr
																												MPUEntryIndex in

											(* get next free slot from MPU end field *)
											perform nextFreeSlotAddr := readMPUEndFromMPUEntryAddr
																											currFreeSlotAddr in
											if beqAddr slotKStructureStart structureCollectAddr
											then
												(* the slot is located in the structure to collect *)
												perform firstFreeSlotAddr := readPDFirstFreeSlotPointer idPD in
												if beqAddr currFreeSlotAddr firstFreeSlotAddr
												then
													(* Special case if slot to remove is the first free
														slot: the next free slot becomes the first free slot
														of the free slots list *)
													writePDFirstFreeSlotPointer idPD nextFreeSlotAddr ;;
													(** RECURSIVE call: continue collect with rest of list *)
													collectFreeSlotsRecAux 	timeout1
																									currFreeSlotAddr
																									nextFreeSlotAddr
																									idPD
																									structureCollectAddr
												else
													(* remove current slot from free slot list: chain
														previous to next free slot *)
														writeMPUEndFromMPUEntryAddr predFreeSlotAddr
																												nextFreeSlotAddr ;;
														(** RECURSIVE call: continue collect with rest of list *)
														collectFreeSlotsRecAux 	timeout1
																										currFreeSlotAddr
																										nextFreeSlotAddr
																										idPD
																										structureCollectAddr
										else
											(* the slot is not located in the structure to collect *)
											(** RECURSIVE call: continue collect with rest of list *)
											collectFreeSlotsRecAux 	timeout1
																							currFreeSlotAddr
																							nextFreeSlotAddr
																							idPD
																							structureCollectAddr
end.

(** The [collectStructureRecAux] function recursively search for a structure
		to collect by going through the structure list and do the collect if found

		Stop conditions:
				1: reached end of structure list (maximum number of iterations) OR
        2: found a free structure
		Processing: collect the structure
    Recursive calls: until the last structure and if the current structure is
        - not empty
        - empty but has not been prepared by the current partition
					(e.g. the child tries to collect/steal a structure from its
					parent's set of blocks
		Max recursion depth: length of the kernel structure linked list +
													max(checkStructureEmptyRecAux, collectFreeSlotsRecAux)

		Returns the collected structure's block id:OK/NULL:NOK

		<<currStructureAddr>>				the current checked structure
		<<predStructureAddr>>				pointer to the previous structure
    <<currentPart>>							the current partition
		<<idPD>>										the PD where to collect
*)
Fixpoint collectStructureRecAux (timeout : nat)
																(currentPart : paddr)
																(idPD :paddr)
																(predStructureAddr currStructureAddr :paddr)
																																	: LLI paddr :=
match timeout with
		| 0 => 	ret nullAddr (* timeout reached *)
		| S timeout1 =>
										if beqAddr currStructureAddr nullAddr
										then
											(** STOP condition 1: reached end of structure list *)
											ret nullAddr
										else
											(* Check if structure is empty *)
											perform entriesnb := getKernelStructureEntriesNb in
											perform lastindex := Index.pred entriesnb in (* 0-indexed*)
											perform isEmpty := checkStructureEmptyRecAux
																						N
																						currStructureAddr
																						lastindex in
											if negb isEmpty
											then
												(* not empty, can't collect *)
												(** RECURSIVE call: check next structure TODO changed order*)
												perform nextStructureAddr := readNextFromKernelStructureStart
																											currStructureAddr in
												collectStructureRecAux 	timeout1
																								currentPart
																								idPD
																								currStructureAddr
																								nextStructureAddr
											else
												(* structure empty, MAY be collected, check first *)
											(** Checks *)
											(* Check structure is a block in current partition,
													otherwise means the current partition wants to collect
													a node given by its parent and this can't be collected
													so pass to next node*)
											(* Find the block in the current partition *)
											perform blockToCollectMPUAddr := findBlockInMPU
																													currentPart
																													currStructureAddr in
											perform addrIsNull := compareAddrToNull	blockToCollectMPUAddr in
											if addrIsNull
											then(* can't remove a block prepared by parent, can't collect *)
												(** RECURSIVE call: check next structure *)
												perform nextStructureAddr := readNextFromKernelStructureStart
																											currStructureAddr in
												collectStructureRecAux 	timeout1
																								currentPart
																								idPD
																								currStructureAddr
																								nextStructureAddr
											else
												(** PROCESSING: collect structure *)
												(* remove all slots to collect from list of free slots*)
												perform firstFreeSlotAddr := readPDFirstFreeSlotPointer idPD in
												collectFreeSlotsRecAux 	N
																								nullAddr
																								firstFreeSlotAddr
																								idPD
																								currStructureAddr ;;
												(* Pull out the structure from the list of structures *)
												removeStructure idPD predStructureAddr currStructureAddr ;;

												(* Change PD structure accordingly *)
												perform nbPrepare := readPDNbPrepare idPD in
												perform predNbPrepare := Index.pred nbPrepare in
												writePDNbPrepare idPD predNbPrepare ;;
												perform nbFreeSlots := readPDNbFreeSlots idPD in
												perform entriesnb := getKernelStructureEntriesNb in
												perform subNbFreeSlots := Index.subIdx nbFreeSlots entriesnb in
												writePDNbFreeSlots idPD subNbFreeSlots ;;

												(* Set block accessible where it is (current or child) *)
												writeMPUAccessibleFromMPUEntryAddr 	blockToCollectMPUAddr
																														true ;;
												(* Set block accessible in parent and ancestors if not cut *)
												writeAccessibleToAncestorsIfNotCutRec idPD
																															currStructureAddr
																															blockToCollectMPUAddr
																															true ;;
												(* Erase sh1 reference *)
												perform defaultSh1Entry := getDefaultSh1Entry in
												writeSh1EntryFromMPUEntryAddr blockToCollectMPUAddr
																											defaultSh1Entry ;;

											(** STOP condition 2: found a structure to collect *)
											ret currStructureAddr
	end.

(** The [collectStructureRec] function fixes the timeout value of
		[collectStructureRecAux] *)
Definition collectStructureRec (currentPart
															idPD
															predStructureAddr currStructureAddr :paddr)
																																	: LLI paddr :=
	collectStructureRecAux N currentPart idPD predStructureAddr currStructureAddr.

(** The [enableBlockInMPU] function enables the block <mpuentryaddr> in the physical
		MPU of the partition <idPD> at the given region number <MPURegionNb>.
		The block is not enabled if the <MPURegionNb> is not valid.

		Returns True if the given <MPURegionNb> is valid for the physical MPU/False

		<<idPD>>								the partition where to reconfigure the physical MPU
    <<blockmpuentryaddr>>		the new block to enable
    <<MPURegionNb>>					the physical MPU region to replace
*)
Definition enableBlockInMPU 	(idPD : paddr)
														(blockmpuentryaddr : paddr)
														(MPURegionNb : index)
 																																: LLI bool :=
	perform zero := Index.zero in
	perform isBelowZero := Index.ltb MPURegionNb zero in
	perform maxMPURegions := getMPURegionsNb in
	perform isAboveMPURegionsNb := Index.leb maxMPURegions MPURegionNb in
	if isBelowZero || isAboveMPURegionsNb
	then (* MPURegionNb not valid, don't enable it*)
			ret false
	else
			(* Enables the block in the physical MPU *)
			replaceBlockInPhysicalMPU idPD blockmpuentryaddr MPURegionNb ;;
			ret true.

