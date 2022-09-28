(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2022)                *)
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

(** The [compareAddrToNull] returns true if the given addr is equal to the fixed
    default addr (null) *)
Definition compareAddrToNull (p : paddr) : LLI bool :=
  perform nullAddr := getNullAddr in
  getBeqAddr nullAddr p.

(** The [findBlockComp] function decides if the given block <entryaddr> matches
		the given <referenceaddr> according to the selected comparator <option>.

		Returns if the block suits the address according to the comparator
*)
Definition findBlockComp 	(entryaddr : paddr)
												(referenceaddr : paddr)
												(comparator : index)
																																	: LLI bool :=
	perform blockstart := readBlockStartFromBlockEntryAddr entryaddr in
	perform zero := Index.zero in
	if beqIdx comparator zero
	then (* Comparator 0: block's start addr == referenceaddr *)
		if beqAddr blockstart referenceaddr
		then (* block found *) ret true
		else (* block not found *) ret false
	else (* Comparator 2: block's start addr < referenceaddr < block's end addr *)
		perform blockend := readBlockEndFromBlockEntryAddr entryaddr in
		perform aboveStart := Paddr.leb blockstart referenceaddr in
		perform belowEnd := Paddr.leb referenceaddr blockend in
		if aboveStart && belowEnd
		then (* block found *) ret true
		else (* block not found *)ret false.

(** The [findBlockInKSInStructAux] function recursively searches by going through
		the current structure list and search for the <id_block_to_find>.
    Stop conditions:
        1: 	reached end of structure (maximum number of iterations)
        2: 	found <id_block_to_find>
        3: 	issue with the block, i.e. block not found, incorrect entry address or
						block not present
    Recursive calls: until the current's structure last index
		Max recursion depth: number of kernel structure entries

		Returns the block's entry address or NULL
*)
Fixpoint findBlockInKSInStructAux (timeout : nat) (currentidx : index)
													(currentkernelstructure referenceaddr : paddr)
													(compoption : index) : LLI paddr :=
	match timeout with
		| 0 => getNullAddr
		| S timeout1 =>
										(** PROCESSING: check if the entry is the searched one *)
										perform entryaddr := getBlockEntryAddrFromKernelStructureStart
																						currentkernelstructure
																						currentidx in
										perform ispresent := readBlockPresentFromBlockEntryAddr entryaddr in
										perform matchcomp := findBlockComp entryaddr
																											referenceaddr
																											compoption in
										if ispresent &&  matchcomp then
											(** STOP CONDITION 2: block found *)
											ret entryaddr
										else
											(** continue search *)
											perform maxentriesnb := getKernelStructureEntriesNb in
											perform nextidx := Index.succ currentidx in
											(** Indexed on zero, so <*)
											perform isnotlastidx := Index.ltb nextidx maxentriesnb in
											if (isnotlastidx)
											then
												(** RECURSIVE call to the next index**)
												findBlockInKSInStructAux timeout1
																								nextidx
																								currentkernelstructure
																								referenceaddr
																								compoption
											else
												(** STOP CONDITION 1: reached end of current structure,
																							block not found *)
												ret nullAddr

	end.

(** The [findBlockInKSAux] function recursively search by going through
		the structure list and search for the <id_block_to_find>.
    Stop conditions:
        1: 	reached end of structure list (maximum number of iterations)
        2: 	found <id_block_to_find>
        3: 	issue with the block, i.e. block not found, incorrect block address or
						block not present
    Recursive calls: until the end of the linked list
		Max recursion depth: length of the linked list + findBlockInKSInStructAux

		Returns the found block's entry address or NULL
*)
Fixpoint findBlockInKSAux (timeout : nat)
													(currentkernelstructure idblock: paddr)
													(compoption : index)									: LLI paddr :=
	match timeout with
		| 0 => getNullAddr
		| S timeout1 =>	(** PROCESSING: seach for the block in the current structure *)
										perform zero := Index.zero in
										perform foundblock := findBlockInKSInStructAux 	N
																																		zero
																																		currentkernelstructure
																																		idblock
																																		compoption in
										perform foundblockisnull := compareAddrToNull foundblock in
										if negb foundblockisnull
										then
											(** STOP CONDITION 2: block found, stop *)
											ret foundblock
										else
											(** block not found in current structure, continue search *)
											perform nextkernelstructure := readNextFromKernelStructureStart
																												currentkernelstructure in
											perform nextKSisnull :=  compareAddrToNull nextkernelstructure in
											if nextKSisnull
											then
												(** STOP CONDITION 1: reached last structure, not found *)
												ret nullAddr
											else
												(** RECURSIVE call on the next structure *)
												findBlockInKSAux timeout1 nextkernelstructure idblock compoption
	end.



(* TODO: return Some blockentry or None *)
(** The [findBlockInKS] function fixes the timeout value of [findBlockInKSAux]
		and lauches the block seach for the address being the start address.
		Same function as in findBelongingBlock but with a different comparator. *)
Definition findBlockInKS (idPD : paddr) (idBlock: paddr) : LLI paddr :=
	perform zero := Index.zero in (* Comparator 1 *)
	perform kernelstructurestart := readPDStructurePointer idPD in
	findBlockInKSAux N kernelstructurestart idBlock zero.

(* TODO: return Some blockentry or None *)
(** The [findBelongingBlock] function fixes the timeout value of [findBlockInKSAux]
		and lauches the search for a block encapsulating the address.
		Same function as in findBlockInKS but with a different comparator. *)
Definition findBelongingBlock (idPD : paddr) (referenceaddr: paddr) : LLI paddr :=
	perform zero := Index.zero in
	perform one := Index.succ zero in (* Comparator 2 *)
	perform kernelstructurestart := readPDStructurePointer idPD in
	findBlockInKSAux N kernelstructurestart referenceaddr one.


(** The [findBlockInKSWithAddrAux] function recursively search by going through
		the structure list and search for the <id_block_to_find> given the
    <blockEntryAddr> (only look the entries at this address, so faster
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
Fixpoint findBlockInKSWithAddrAux 	(timeout : nat)
																	(currentkernelstructure : paddr)
																	(blockEntryAddr: paddr) : LLI paddr :=
	match timeout with
		| 0 => getNullAddr
		| S timeout1 => (*Stop conditions 2 and 3: found block OR issue with the entry *)
										perform isEntryAddrAboveStart := Paddr.leb 	currentkernelstructure
																																blockEntryAddr in
										perform zero := Index.zero in
										perform maxEntryAddrInStructure :=  getSh1EntryAddrFromKernelStructureStart
																													currentkernelstructure
																													zero in
										perform isEntryAddrBelowEnd := Paddr.leb blockEntryAddr maxEntryAddrInStructure in
										if isEntryAddrAboveStart && isEntryAddrBelowEnd
										then (* the provided address lies in this kernel structure*)
												(** Check the block entry exists and is present*)
												perform entryExists := checkEntry 	currentkernelstructure
																														blockEntryAddr in
												if (negb entryExists)
												then (** STOP CONDITION 3: bad arguments *)
													ret nullAddr
												else (* entry addr is valid *)
													perform isPresent := readBlockPresentFromBlockEntryAddr blockEntryAddr in
													if isPresent
													then (** STOP CONDITION 2: the block has been found and is present (i.e. it's a real block)*)
														ret blockEntryAddr
													else (** STOP CONDITION 3: block not present *)
														ret nullAddr
										else (** RECURSIVE call: block not found in current structure,
														check next kernel structure*)
											perform nextKernelStructure := readNextFromKernelStructureStart
																											currentkernelstructure in
											perform isnull :=  compareAddrToNull nextKernelStructure in
											if isnull
											then
												(** STOP CONDITION 1: reached last structure, not found *)
												ret nullAddr
											else findBlockInKSWithAddrAux timeout1
																										nextKernelStructure
																										blockEntryAddr
	end.


(* TODO: return Some blockentry or None *)
(** The [findBlockInKSWithAddr] function fixes the timeout value of
		[findBlockInKSWithAddrAux] *)
Definition findBlockInKSWithAddr (idPD blockEntryAddr: paddr) : LLI paddr :=
	(** All checks done before*)
	(** go through the Blocks structure finding the block (== start address of block entry)*)
	perform kernelstructurestart := readPDStructurePointer idPD in
	findBlockInKSWithAddrAux N kernelstructurestart blockEntryAddr.

(** The [checkBlockCut] function checks if the block at <blockentryaddr> has been
		cut or if it is a subblock of some other block*)
Definition checkBlockCut (blockentryaddr : paddr) : LLI bool :=
	perform blockOrigin := readSCOriginFromBlockEntryAddr blockentryaddr in
	perform blockStart := readBlockStartFromBlockEntryAddr blockentryaddr in
	perform blockNext := readSCNextFromBlockEntryAddr blockentryaddr in
	if beqAddr blockStart blockOrigin  && beqAddr blockNext nullAddr then
		(* Block hasn't been cut previously and not a subblock *)
		ret false
	else (* Block has been cut previously *) ret true.


(** The [writeAccessibleRecAux] function recursively writes the accessible bit of
		value <accessible_bit> to the block identified as <idblock> to all ancestors
		of <pdbasepartition>
    Stop condition: reached root partiton (last ancestor)
    Processing: remove the block at this level of descendants
    Recursive calls: until the last ancestor
		Max recursion depth: number of ancestors
												+ max(findBlockInKS, removeBlockFromPhysicalMPUIfNotAccessible)

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
												perform blockInParentPartitionAddr := findBlockInKS
																																	pdparent
																																	idblock in
												perform addrIsNull := compareAddrToNull
																									blockInParentPartitionAddr in
												if addrIsNull then ret false (*Shouldn't happen *) else
												writeBlockAccessibleFromBlockEntryAddr
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
																								(blockentryaddr : paddr)
																								(accessiblebit : bool) : LLI bool :=
		perform blockOrigin := readSCOriginFromBlockEntryAddr blockentryaddr in
		perform blockStart := readBlockStartFromBlockEntryAddr blockentryaddr in
		perform blockNext := readSCNextFromBlockEntryAddr blockentryaddr in
		perform globalIdBlock := readBlockStartFromBlockEntryAddr
																				blockentryaddr in
		if beqAddr blockStart blockOrigin  && beqAddr blockNext nullAddr then
			(* Block hasn't been cut previously, adjust accessible bit *)
			perform recWriteEnded := writeAccessibleRec pdbasepartition
																									globalIdBlock
																									accessiblebit in
			if negb recWriteEnded then (* timeout reached or error *) ret false else
			ret true
		else ret true.

(** The [insertNewEntry] function inserts the entry (<startaddr>, <endaddr>, true, true)
 	in the partition <pdinsertion> with block origin <origin>.
	Used in cutMemoryBlock and addMemoryBlock.
	The rights have been checked before.

	Returns the inserted entry's address

	<<pdinsertion>> 		the PD where to insert the new entry
	<<startaddr>>				the new entry's start address
	<<endaddr>>					the new entry's end address
	<<origin>>					the new entry's block origin
	<<r w e >>					the new entry's rights
	<<currnbfreeslots>> the current number of free slots
*)
Definition insertNewEntry 	(pdinsertion startaddr endaddr origin: paddr)
													(r w e : bool) (currnbfreeslots : index): LLI paddr :=
	(** Checks have been done before: PD is correct, slot start and end @ are correct,
			block_origin is correct, there is one or more free slots *)
	perform newBlockEntryAddr := readPDFirstFreeSlotPointer pdinsertion in
	(** Adjust the free slot pointer to the next free slot*)
	perform newFirstFreeSlotAddr := readBlockEndFromBlockEntryAddr newBlockEntryAddr in
	(** Adjust the free slots count to count - 1*)
	perform predCurrentNbFreeSlots := Index.pred currnbfreeslots in

	writePDFirstFreeSlotPointer pdinsertion newFirstFreeSlotAddr ;;
	writePDNbFreeSlots pdinsertion predCurrentNbFreeSlots ;;

	(** Insert the new block entry in the free slot*)
	writeBlockStartFromBlockEntryAddr newBlockEntryAddr startaddr ;;
	writeBlockEndFromBlockEntryAddr newBlockEntryAddr endaddr ;;
	writeBlockAccessibleFromBlockEntryAddr newBlockEntryAddr true ;;
	writeBlockPresentFromBlockEntryAddr newBlockEntryAddr true ;;
	writeBlockRFromBlockEntryAddr newBlockEntryAddr r ;;
	writeBlockWFromBlockEntryAddr newBlockEntryAddr w ;;
	writeBlockXFromBlockEntryAddr newBlockEntryAddr e ;;
	writeSCOriginFromBlockEntryAddr newBlockEntryAddr origin ;;

	ret newBlockEntryAddr.

(** The [freeSlot] function frees the entry at <entrytofreeaddr> in the
		partition <pdfree>.
	Used in mergeMemoryBlock and removeMemoryBlock

	Returns the freed slot's address
*)
Definition freeSlot (pdfree entrytofreeaddr: paddr) : LLI paddr :=
(** Checks have been done before: check idPD comes from Pip,
		check entrytofreeaddress comes from Pip *)
		(* Remove block from physical MPU if it is there *)
		removeBlockFromPhysicalMPU 	pdfree entrytofreeaddr ;;
		(* set default values in slot to free *)
		perform defaultBlockEntry := getDefaultBlockEntry in
		writeBlockEntryFromBlockEntryAddr entrytofreeaddr defaultBlockEntry;;
		writeSh1EntryFromBlockEntryAddr entrytofreeaddr nullAddr false nullAddr;;
		perform defaultSCEntry := getDefaultSCEntry in
		writeSCEntryFromBlockEntryAddr entrytofreeaddr defaultSCEntry;;
		(* insert free slot in the free slot list *)
		perform currFirstFreeSlot := readPDFirstFreeSlotPointer pdfree in
		writeBlockEndFromBlockEntryAddr entrytofreeaddr currFirstFreeSlot ;;
		writePDFirstFreeSlotPointer pdfree entrytofreeaddr ;;
		(* add 1 to the number of free slots*)
		perform nbfreeslots := readPDNbFreeSlots pdfree in
		perform nbfreeslotssucc := Index.succ nbfreeslots in
		writePDNbFreeSlots pdfree nbfreeslotssucc ;;
		(* return the freed slot's address *)
		ret entrytofreeaddr.


(** The [checkChildOfCurrPart] function checks that <idPDchild> is a child of
		the current	partition by looking for the child in the current partition's
		kernel structure.
		Returns true:OK/false:NOK
*)
Definition checkChildOfCurrPart (currentPartition idPDchild : paddr) : LLI bool :=
	perform blockInParentPartAddr := findBlockInKSWithAddr currentPartition idPDchild in
	perform addrIsNull := compareAddrToNull	blockInParentPartAddr in
	if addrIsNull then(** child block not found, stop *) ret false else

	perform isChild := readSh1PDFlagFromBlockEntryAddr blockInParentPartAddr in
	if negb isChild then (* idPDchild is not a child partition, stop*) ret false else
	ret true.

(** The [removeBlockInDescendantsRecAux] function recursively removes the block
		identified at block entry address <currLevelBlockToRemoveAddr> of the current
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
											perform nextdescendant := readSh1PDChildFromBlockEntryAddr
																									currLevelBlockToRemoveAddr in
											perform blockToRemoveInDescendantAddr :=
															readSh1InChildLocationFromBlockEntryAddr
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
		| S timeout1 => (** PROCESSING: checks (subblockAddr is valid, checked before *)
										perform isAccessible := readBlockAccessibleFromBlockEntryAddr
																								subblockAddr in
										perform isPresent := readBlockPresentFromBlockEntryAddr
																								subblockAddr in
										(* if accessible, then PDflag can't be set, we just need to check PDchild *)
										perform PDChildAddr := readSh1PDChildFromBlockEntryAddr	subblockAddr in
										perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
										if negb (isAccessible && isPresent && PDChildAddrIsNull)
										then (** STOP condition 2: the subblock is not accessible,
													not present or is shared *) ret false
										else
												perform nextsubblock := readSCNextFromBlockEntryAddr
																										subblockAddr in
												perform isnull := compareAddrToNull nextsubblock in
												if isnull
												then (** STOP condition 1: reached last subblock*)
														ret true
												else (** RECURSIVE call: check the next subblock*)
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
												perform nextsubblock := readSCNextFromBlockEntryAddr
																										subblockAddr in
												freeSlot idPDchild subblockAddr ;;
												(** RECURSIVE call: check the next subblock*)
												removeSubblocksRecAux timeout1 idPDchild nextsubblock
	end.

(** The [removeSubblocksRec] fixes the timeout value of
		[removeSubblocksRecAux] *)
Definition removeSubblocksRec (idPDchild subblockAddr : paddr): LLI bool :=
	removeSubblocksRecAux N idPDchild subblockAddr.

(** The [removeBlockInChildAndDescendants] function removes the block
		<blockToRemoveInCurrPartAddr> from the child and potential descendants.
		There are two treatments depending if the block to remove is cut or not:
			- not cut: remove the block in the child and all descendants if it is
								accessible (e.g. not used as kernel structure in the child or
								in the descedants nor cut in the descendants)
			- cut: remove the block only if all subblocks are accessible, present and
						not shared

		Returns true:OK/false:NOK

    <<currentPart>>					the current/parent partition
		<<blockToRemoveInCurrPartAddr>>	the block to remove id in the parent
*)
Definition removeBlockInChildAndDescendants (currentPart
																						blockToRemoveInCurrPartAddr
																						idPDchild
																						blockToRemoveInChildAddr : paddr)
																																	: LLI bool :=
		(** Checks done before, blockToRemoveInCurrPartAddr and blockToRemoveInChildAddr
				are valid block entries *)
		perform globalIdBlockToRemove := readBlockStartFromBlockEntryAddr
																				blockToRemoveInCurrPartAddr in
		perform isBlockCut := checkBlockCut blockToRemoveInChildAddr in
		if negb isBlockCut
		then (** Case 1: block not cut in the child partition -> remove the
							block in the child and all grand-children *)

				(* 	check block is accessible *)
				perform addrIsAccessible := readBlockAccessibleFromBlockEntryAddr
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
				writeBlockAccessibleFromBlockEntryAddr blockToRemoveInCurrPartAddr true ;;
				perform recWriteEnded := writeAccessibleRec currentPart
																										globalIdBlockToRemove
																										true in
				if negb recWriteEnded then (* timeout reached or error *) ret false else
				ret true.


(** The [sizeOfBlock] function computes the size of block referenced in a block entry
	Returns the difference between the block's end and start addresses
*)
Definition sizeOfBlock (blockentryaddr : paddr) : LLI index :=
	perform startAddr := readBlockStartFromBlockEntryAddr blockentryaddr in
	perform endAddr := readBlockEndFromBlockEntryAddr blockentryaddr in
	perform size := Paddr.subPaddr endAddr startAddr in
	(* last address must be counted *)
	Index.succ size.

(** The [initBlockEntryRec] function recursively initializes all block entries from
		<indexCurr> to 0 of kernel structure located at <kernelStructureStartAddr>
		by constructing a linked list of all entries representing the free slots.
		The indexes are 0-indexed.
	Max recursion depth: number of kernel structure entries

	Returns true:OK/false:NOK
*)
Fixpoint initBlockEntryRecAux 	(timeout : nat)
															(kernelStructureStartAddr : paddr)
															(indexCurr : index): LLI bool :=
	match timeout with
	| 0 => 	ret false (* timeout reached *)
	| S timeout1 =>
									(** PROCESSING: set default values in current entry *)
									perform idxsucc := Index.succ indexCurr in
									(* current entry points to the next via the endAddr field*)
									perform nextEntryPointer := getBlockEntryAddrFromKernelStructureStart
																								kernelStructureStartAddr
																								idxsucc in
									perform blockEntry := buildBlockEntry
																				nullAddr
																				nextEntryPointer
																				false
																				false in
									perform currEntryPointer := getBlockEntryAddrFromKernelStructureStart
																								kernelStructureStartAddr
																								indexCurr in
									writeBlockEntryWithIndexFromBlockEntryAddr
											currEntryPointer
											indexCurr
											blockEntry;;

									perform zero := Index.zero in
									if beqIdx indexCurr zero
									then (** STOP condition: parsed all entries *)
										ret true
									else
										(** RECURSIVE call: write default values in precedent index *)
										perform idxpred := Index.pred indexCurr in
										initBlockEntryRecAux timeout1 kernelStructureStartAddr idxpred
	end.

(** The [initBlocksStructure] function initializes the blocks part of the kernel
		structure located at <kernelStructureStartAddr>. It creates the linked list
		of the free slots. The block indexes are 0-indexed. The last index is special,
		it should point to NULL.
	Returns true:OK/false:NOK
*)
Definition initBlocksStructure (kernelStructureStartAddr : paddr) : LLI bool :=
	perform entriesnb := getKernelStructureEntriesNb in
	perform lastindex := Index.pred entriesnb in (* 0-indexed*)
	(** Initialize the block entries until the penultimate entry, the last entry is
			is not identical*)
	perform secondlastindex := Index.pred lastindex in
	perform initEnded := initBlockEntryRecAux N
																					kernelStructureStartAddr
																					secondlastindex in
	if negb initEnded then (* timeout reached *) ret false else
	(** Last entry has no following entry: make it point to NULL*)
	perform lastBlockEntry := buildBlockEntry nullAddr
																				nullAddr
																				false
																				false in
	perform lastEntryPointer := getBlockEntryAddrFromKernelStructureStart
									 								kernelStructureStartAddr
																	lastindex in
	writeBlockEntryWithIndexFromBlockEntryAddr 	lastEntryPointer
																					lastindex
																					lastBlockEntry;;
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
										perform currEntryPointer := getBlockEntryAddrFromKernelStructureStart
																									kernelStructureStartAddr
																									indexCurr in
										writeSh1EntryFromBlockEntryAddr currEntryPointer nullAddr false nullAddr;;
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
										perform currEntryPointer := getBlockEntryAddrFromKernelStructureStart
																									kernelStructureStartAddr
																									indexCurr in
										writeSCEntryFromBlockEntryAddr 	currEntryPointer
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
	initBlocksStructure kernelStructureStartAddr ;;
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
										perform currBlockEntryAddr :=	getBlockEntryAddrFromKernelStructureStart
																											kernelStructureStartAddr
																											currIndex in
										perform blockID := readBlockStartFromBlockEntryAddr
																					currBlockEntryAddr in
										perform currPDChild := readSh1PDChildFromBlockEntryAddr
																							currBlockEntryAddr in
										if beqAddr currPDChild idPDchildToDelete
										then (* the slot corresponds to memory shared or prepared
													with the child to destruct, remove sharing *)
														(* Set block accessible in current partition *)
														writeBlockAccessibleFromBlockEntryAddr 	currBlockEntryAddr
																																true ;;
														writeSh1EntryFromBlockEntryAddr currBlockEntryAddr nullAddr false nullAddr ;;
													(* 	whatever the accessibility of the block that could
															not be accessible because of the child's operations,
															set the block accessible again*)
													perform isCut := checkBlockCut currBlockEntryAddr in
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
										perform currBlockEntryAddr :=	getBlockEntryAddrFromKernelStructureStart
																										structureAddr
																										currIndex in
										perform isPresent := readBlockPresentFromBlockEntryAddr
																						currBlockEntryAddr in
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
											perform blockEntryIndex := readBlockIndexFromBlockEntryAddr
																										currFreeSlotAddr in
											perform slotKStructureStart := getKernelStructureStartAddr
																												currFreeSlotAddr
																												blockEntryIndex in

											(* get next free slot from Block's end field *)
											perform nextFreeSlotAddr := readBlockEndFromBlockEntryAddr
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
														writeBlockEndFromBlockEntryAddr predFreeSlotAddr
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
												(** RECURSIVE call: check next structure *)
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
											perform blockToCollectAddr := findBlockInKS
																													currentPart
																													currStructureAddr in
											perform addrIsNull := compareAddrToNull	blockToCollectAddr in
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
												writeBlockAccessibleFromBlockEntryAddr 	blockToCollectAddr
																														true ;;
												(* Set block accessible in parent and ancestors if not cut *)
												writeAccessibleToAncestorsIfNotCutRec idPD
																															blockToCollectAddr
																															true ;;
												(* Erase sh1 reference *)
												writeSh1EntryFromBlockEntryAddr blockToCollectAddr nullAddr false nullAddr ;;

											(** STOP condition 2: found a structure to collect *)
											ret blockToCollectAddr
	end.

(** The [collectStructureRec] function fixes the timeout value of
		[collectStructureRecAux] *)
Definition collectStructureRec (currentPart
															idPD
															predStructureAddr currStructureAddr :paddr)
																																	: LLI paddr :=
	collectStructureRecAux N currentPart idPD predStructureAddr currStructureAddr.

(** The [enableBlockInMPU] function enables the block <blockentryaddr> in the physical
		MPU of the partition <idPD> at the given region number <MPURegionNb>.
		The block is not enabled if the <MPURegionNb> is not valid.

		Returns True if the given <MPURegionNb> is valid for the physical MPU/False

		<<idPD>>								the partition where to reconfigure the physical MPU
    <<blockentryaddr>>		the new block to enable
    <<MPURegionNb>>					the physical MPU region to replace
*)
Definition enableBlockInMPU 	(idPD : paddr)
														(blockentryaddr : paddr)
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
			replaceBlockInPhysicalMPU idPD blockentryaddr MPURegionNb ;;
			ret true.

(** The [removeBlockFromPhysicalMPUIfAlreadyMapped] function removes the block
		<blockentryaddr> from the physical MPU of the partition <idPD> if the block
		is already mapped in the MPU.

		Returns unit

		<<idPD>>								the partition where to look for the physical MPU
    <<blockentryaddr>>		the block to find
*)
Definition removeBlockFromPhysicalMPUIfAlreadyMapped (idPD : paddr)
																										(blockentryaddr : paddr)
																										: LLI unit :=

	perform kernelentriesnb := getKernelStructureEntriesNb in
	perform defaultidx := Index.succ kernelentriesnb in
	perform oldMPURegionNb := findBlockIdxInPhysicalMPU 	idPD
																											blockentryaddr
																											defaultidx in
	if beqIdx oldMPURegionNb defaultidx
	then (* block was already mapped, remove it*)
		enableBlockInMPU idPD nullAddr oldMPURegionNb ;;
		ret tt
	else ret tt.

(** The [getGlobalIdPDCurrentOrChild] function returns the <idPDToCheck>'s global id.

		Returns the global id of <idPDToCheck> if current partition or a child/NULL

		<<currentPartition>>	the current partition's PD
    <<idPDToCheck>>				the block to check
*)
Definition getGlobalIdPDCurrentOrChild (currentPartition idPDToCheck : paddr)
																																: LLI paddr :=

		perform isCurrentPart := getBeqAddr idPDToCheck currentPartition in
		if isCurrentPart
		then (* idPDToCheck is the current partition *) ret currentPartition
		else
		perform isChildCurrPart := checkChildOfCurrPart currentPartition idPDToCheck in
		if isChildCurrPart
		then (* idPDToCheck is a child *)
			perform idPDChild := readBlockStartFromBlockEntryAddr idPDToCheck in
			ret idPDChild
		else (* idPDToCheck is neither itself or a child partition *) ret nullAddr.

(** The [compatibleRight] function checks that the <newright> is compatible with
		the <originalright> (less or equal than original)*)
Definition compatibleRight (originalright newright : bool) : LLI bool :=
	if newright
	then	ret (eqb originalright newright) else	ret true.

(** The [checkRights] function checks that the rights <r, w, x> are compatible
		with Pip's access control policy for unprivileged accesses given a base block.

		Policy:
			- always readable (only enabled regions are present in the kernel structure)
			- can't give more rights than the original block

		Returns OK/NOK

		<<originalblockentryaddr>>  the original block to copy from
		<<r>> 											the read right
		<<w>> 											the write right
		<<x>> 											the exec right
*)
Definition checkRights (originalblockentryaddr : paddr) (r w x : bool) : LLI bool :=
	(* read has to be true *)
	if negb r then ret false else
	(* check the rights are not increased *)
	perform xoriginal := readBlockXFromBlockEntryAddr originalblockentryaddr in
	perform woriginal := readBlockWFromBlockEntryAddr originalblockentryaddr in

	perform isCompatibleWithX := compatibleRight xoriginal x in
	perform isCompatibleWithW := compatibleRight woriginal w in
	if negb (isCompatibleWithX && isCompatibleWithW)
	then (** incompatible rights *) ret false else
	ret true.

