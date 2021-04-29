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

(*
    def __find_block_in_MPU_rec(self, next_kernel_structure, id_block_to_find):
        """Recursive search by going through the structure list and search for the <id_block_to_find>
        Stop conditions:
            1: reached end of structure list (maximum number of iterations)
            2: found <id_block_to_find>
        Recursive calls: until the end of the list
        """
        # Stop condition 1: reached end of structure list
        if next_kernel_structure == 0:  # TODO: NULL
            # end of structure list, stop
            return -1

        # Stop condition 2: found block
        for i in range(self.constants.kernel_structure_entries_nb):
            entry_i_address = i*self.constants.MPU_entry_length + next_kernel_structure
            if self.helpers.get_MPU_present_from_MPU_entry_address(entry_i_address) == 0:
                # empty slot, don't consider the value
                continue
            entry_i_start = self.helpers.get_MPU_start_from_MPU_entry_address(entry_i_address)
            if entry_i_start == id_block_to_find:
                # the block has been found
                block_in_MPU = entry_i_address
                return block_in_MPU

        # RECURSIVE call: check next kernel structure
        next_kernel_structure = self.helpers.get_kernel_structure_next_from_kernel_structure_start(next_kernel_structure)
        return self.__find_block_in_MPU_rec(next_kernel_structure, id_block_to_find)

    def __find_block_in_MPU(self, PD_to_find_in, id_block_to_find):
        """Go through the kernel structure linked list searching in the MPU structure for the <id_block_to_find>
        :return: block address / NOK (-1)"""
        # Check that PD is OK done before

        # go through the MPU structure finding the block (== start address of MPU entry)
        next_kernel_structure = self.helpers.get_PD_pointer_to_MPU_linked_list(PD_to_find_in)
        return self.__find_block_in_MPU_rec(next_kernel_structure, id_block_to_find)
*)


Fixpoint findBlockInMPUAux (timeout : nat) (currentidx : index)
													(currentkernelstructure idblock: paddr) : LLI paddr :=
	match timeout with
		| 0 => getNullAddr
		| S timeout1 =>
										perform maxentriesnb := getKernelStructureEntriesNb in (** Our last index is table size - 1, as we're indexed on zero*)
										perform maxindex := Index.pred maxentriesnb in
										perform islastidx := getBeqIdx currentidx maxindex in
										if (islastidx)
										then
											perform nextkernelstructure := readNextFromKernelStructureStart currentkernelstructure in
											perform nullAddr :=  getNullAddr in
											perform isnull :=  getBeqAddr nextkernelstructure nullAddr in
											if isnull
											then getNullAddr
											else
												(** Recursive call on the next table, start at index 0 *)
												perform zero := Index.zero in
												findBlockInMPUAux timeout1 zero nextkernelstructure idblock
									else
											perform entryaddr := getMPUEntryAddrFromKernelStructureStart currentkernelstructure currentidx in
											perform ispresent := readMPUPresentFromMPUEntryAddr entryaddr in
											perform mpustart := readMPUStartFromMPUEntryAddr entryaddr in
											if ispresent && beqAddr mpustart idblock then
												(* block found*)
												ret entryaddr
											else
												(** Recursive call to the next index**)
												perform nextidx := Index.succ currentidx in
												findBlockInMPUAux timeout1 nextidx currentkernelstructure idblock
	end.



(* TODO: return Some MPUentry or None *)
(** The [findBlockInMPU] function fixes the timeout value of [findBlockInMPUAux] *)
Definition findBlockInMPU (idPD : paddr) (idBlock: paddr) : LLI paddr :=
	perform kernelstructurestart := readPDStructurePointer idPD in
	perform zero := Index.zero in
	findBlockInMPUAux N zero kernelstructurestart idBlock.

(*
def __find_block_in_MPU_with_address_rec(self, next_kernel_structure, id_block_to_find, MPU_address_block_to_find):
    """Recursive search by going through the structure list and search for the <id_block_to_find> given the
    <MPU_address_block_to_find> (only look the entries at this address, so faster than blind search going through
    all the entries of a kernel structure)
    Stop conditions:
        1: reached end of structure list (maximum number of iterations)
        2: found <id_block_to_find>
        3: issue with the block, i.e. block not found, incorrect MPU address or block not present
    Recursive calls: until the end of the list
    """
    # Stop condition 1: reached end of structure list
    if next_kernel_structure == 0:  # TODO: NULL
        # end of structure list, stop
        return -1

    # Stop conditions 2 and 3: found block OR issue with the entry
    if next_kernel_structure <= MPU_address_block_to_find < (next_kernel_structure + self.constants.indexSh1):
        # the provided address lies in this kernel structure
        index = self.helpers.get_MPU_index(MPU_address_block_to_find)
        if 0 <= index < self.constants.kernel_structure_entries_nb:
            if self.helpers.get_MPU_start_from_MPU_entry_address(MPU_address_block_to_find) == id_block_to_find\
                    and self.helpers.get_MPU_present_from_MPU_entry_address(MPU_address_block_to_find) != 0:
                    # the block has been found and is present (i.e. it's a real block)
                    block_in_MPU = MPU_address_block_to_find
                    return block_in_MPU
        # Stop condition 3: issue with the entry (i.e. block not found OR incorrect MPU address OR block not present)
        return -1

    # RECURSIVE call: block not found in current structure, check next kernel structure
    next_kernel_structure = self.helpers.get_kernel_structure_next_from_kernel_structure_start(next_kernel_structure)
    return self.__find_block_in_MPU_with_address_rec(next_kernel_structure,
                                                     id_block_to_find,
                                                     MPU_address_block_to_find)
*)
(** The [findBlockInMPUWithAddrAux] function recursively search by going through
		the structure list and search for the <id_block_to_find> given the
    <MPU_address_block_to_find> (only look the entries at this address, so faster
		than blind search going through all the entries of a kernel structure)
    Stop conditions:
        1: 	reached end of structure list (maximum number of iterations)
        2: 	found <id_block_to_find>
        3: 	issue with the block, i.e. block not found, incorrect MPU address or
						block not present
    Recursive calls: until the end of the linked list *)
Fixpoint findBlockInMPUWithAddrAux (timeout : nat)
																	(currentkernelstructure idblock : paddr)
																	(blockMPUAddr: paddr) : LLI paddr :=
	match timeout with
		| 0 => getNullAddr (*Stop condition 1: reached end of structure list*)
		| S timeout1 => (*Stop conditions 2 and 3: found block OR issue with the entry *)
										perform isMPUAddrAboveStart := Paddr.leb currentkernelstructure blockMPUAddr in
										perform maxMPUAddrInStructure :=  Paddr.addPaddrIdx
																													currentkernelstructure
																													Constants.sh1offset in
										perform isMPUAddrBelowEnd := Paddr.leb maxMPUAddrInStructure blockMPUAddr in
										if isMPUAddrAboveStart && isMPUAddrBelowEnd
										then (* the provided address lies in this kernel structure*)
											(** Check 0 <= index < max entries nb*)
											perform index := readMPUIndexFromMPUEntryAddr blockMPUAddr in

											perform maxEntriesNb := getKernelStructureEntriesNb in
											perform zero := Index.zero in
											perform lastindex := Index.pred maxEntriesNb in
											perform isAbove0 := Index.leb zero index in
											perform isLessMaxEntriesNb := Index.leb index maxEntriesNb in
											if isAbove0 && isLessMaxEntriesNb
											then (* 0 <= index <= lastidx is valid*)
												(** Check the MPU entry matches the submitted idblock
														and is present*)
												perform entryBlockStart := readMPUStartFromMPUEntryAddr blockMPUAddr in
												perform isEntryValid := getBeqAddr entryBlockStart idblock in
												perform isPresent := readMPUPresentFromMPUEntryAddr blockMPUAddr in
												if isEntryValid && isPresent
												then (* Stop condition 2: the block has been found and is present (i.e. it's a real block)*)
													ret blockMPUAddr
												else (*Stop condition 3a: bad arguments OR block not present *)
													ret nullAddr
											else (*Stop condition 3b: block not found at the correct MPU location *)
														ret nullAddr
										else (* RECURSIVE call: block not found in current structure,
														check next kernel structure*)
											perform nextKernelStructure := readNextFromKernelStructureStart
																											currentkernelstructure in
											findBlockInMPUWithAddrAux timeout1 nextKernelStructure
																												idblock
																												blockMPUAddr
	end.

(*
def __find_block_in_MPU_with_address(self, PD_to_find_in, id_block_to_find, MPU_address_block_to_find):
    """Go through the kernel structure linked list searching in the MPU structure for the <id_block_to_find>
    located at <MPU_address_block_to_find>
    :return block address / NOK (-1)"""
    # all checks done before
    # go through the MPU structure finding the block (== start address of MPU entry)
    next_kernel_structure = self.helpers.get_PD_pointer_to_MPU_linked_list(PD_to_find_in)
    return self.__find_block_in_MPU_with_address_rec(next_kernel_structure,
                                                     id_block_to_find,
                                                     MPU_address_block_to_find)
*)
(* TODO: return Some MPUentry or None *)
(** The [findBlockInMPUWithAddr] function fixes the timeout value of
		[findBlockInMPUWithAddrAux] *)
Definition findBlockInMPUWithAddr (idPD idBlock blockMPUAddr: paddr) : LLI paddr :=
	(** All checks done before*)
	(** go through the MPU structure finding the block (== start address of MPU entry)*)
	perform kernelstructurestart := readPDStructurePointer idPD in
	findBlockInMPUWithAddrAux N kernelstructurestart idBlock blockMPUAddr.

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

(*
    def __write_accessible_to_ancestors_rec(self, PD_base_partition, id_base_block, accessible_bit):
        """Write the accessible bit of value <accessible_bit> to the block identified as
            <id_base_block> to all ancestors of <PD_base_partition>"""
        if PD_base_partition == self.root_partition:
            # root partition, no ancestor, stop
            return 1
        else:
            # get parent partition
            PD_parent_partition = self.helpers.get_PD_parent(PD_base_partition)
            # find block in MPU structure
            block_in_parent_MPU_address = self.__find_block_in_MPU(PD_parent_partition, id_base_block)
            if block_in_parent_MPU_address == -1:
                # block not found, shouldn't happen TODO: write accessible could fail
                return 0

            self.helpers.set_MPU_accessible_from_MPU_entry_address(block_in_parent_MPU_address, accessible_bit)

            # recursive call until we reached the root partition
            return self.__write_accessible_to_ancestors_rec(PD_parent_partition, id_base_block, accessible_bit)
*)

(** The [writeAccessibleRecAux] function recursively write the accessible bit of
		value <accessible_bit> to the block identified as <idblock> to all ancestors
		of <pdbasepartition>
    Stop condition: reached root partiton (last ancestor)
    Processing: remove the block at this level of descendants
    Recursive calls: until the last ancestor

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

(*     def __insert_new_entry(self, PD_insertion, entry_to_insert, block_origin):
        """Insert the entry <entry_to_insert> in the partition <PD_insertion> with block origin <block_origin>
        Used in cutMemoryBlock and addMemoryBlock"""
        # insérerEntrée(idPDinsertion, entrée à insérer, origine bloc) : insère l’entrée au 1er emplacement libre dans la MPU de idPDinsertion et précise l’origine du bloc, retourne l’emplacement MPU où l’entrée a été insérée (O(1))
        # Checks have been done before: PD is correct, MPU_entry is correct, block_origin is correct, there is one or
        # more free slots

        # entrée MPU libre <- idPDinsertion[pointeur libre] (récupérer la 1ère entrée libre)
        new_entry_address = self.helpers.get_PD_first_free_slot_address(PD_insertion)

        # // Ajuster le pointeur libre
        # Adjust the free slot pointer and count
        # Ecrire idPDinsertion[pointeur libre]->end à idPDinsertion[pointeur libre] (changer le pointeur libre vers la prochaine entrée MPU libre)
        new_first_free_slot_address = self.helpers.get_MPU_end_from_MPU_entry_address(new_entry_address)
        self.helpers.set_PD_first_free_slot_address(PD_insertion, new_first_free_slot_address)

        # Ecrire (idPDinsertion[compteur]–1) à idPDinsertion[compteur] (enlever 1 au compteur d’entrées libres)
        self.helpers.set_PD_nb_free_slots(PD_insertion, self.helpers.get_PD_nb_free_slots(PD_insertion) - 1)

        # // Insérer l’entrée au 1er emplacement libre
        # Ecrire (entrée à insérer) à @(entrée MPU libre) (insérer l’entrée à l’emplacement libre)
        self.helpers.write_MPU_entry(new_entry_address, entry_to_insert[1], entry_to_insert[2], entry_to_insert[3], entry_to_insert[4])

        # Ecrire (origine bloc) à SC[entrée MPU libre]->origin (indiquer que le bloc est l’origine des coupes futures, soit le start du bloc qui a été donné)
        self.helpers.set_SC_origin_from_MPU_entry_address(new_entry_address, block_origin)

        # RET @(entrée MPU libre)
        return new_entry_address
*)
(** The [insertNewEntry] function inserts the entry (<startaddr>, <endaddr>, true, true)
 	in the partition <pdinsertion> with block origin <origin>.
	Used in cutMemoryBlock and addMemoryBlock
	Returns the inserted entry's MPU address
	 *)
Definition insertNewEntry (pdinsertion startaddr endaddr origin: paddr) : LLI paddr :=
(** Checks have been done before: PD is correct, MPU_entry is correct, block_origin is correct, there is one or more free slots *)
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
	(* TODO : set the block's RWX rights here ?*)
	writeSCOriginFromMPUEntryAddr newEntryMPUAddr origin ;;

	ret newEntryMPUAddr.


(*
    def __free_slot(self, idPD, entryToFreeMPUAddress):
        """Free the slot by setting to default"""
        # Checks have been done before: check idPD comes from Pip, check entryToFreeMPUAddress comes from Pip

        # Ecrire default à (entrée MPU à libérer) (écraser l’entrée MPU -> le bloc n’existe plus)
        self.helpers.set_MPU_entry_from_MPU_entry_address(entryToFreeMPUAddress, 0, 0, 0, 0)
        # Ecrire default à Sh1[entrée MPU à libérer] (écraser l’entrée Sh1 associée à l’entrée MPU à libérer -> bloc enlevé de la descendance)
        self.helpers.set_Sh1_entry_from_MPU_entry_address(entryToFreeMPUAddress, 0, 0, 0)
        # Ecrire default à SC[entrée MPU à libérer] (écraser l’entrée SC associée à l’entrée MPU à libérer)
        self.helpers.set_SC_entry_from_MPU_entry_address(entryToFreeMPUAddress, 0, 0)
        # // Insérer l’emplacement dans la liste des emplacements libres
        # Ecrire idPDlibération[pointeur libre] à (entrée MPU à libérer)->end (insérer l’entrée dans la chaîne des emplacements libres)
        current_first_free_slot_address = self.helpers.get_PD_first_free_slot_address(idPD)
        self.helpers.set_MPU_end_from_MPU_entry_address(entryToFreeMPUAddress, current_first_free_slot_address)
        # Ecrire (entrée MPU à libérer) à idPDlibération[pointeur libre] (le pointeur libre devient l’emplacement libéré)
        self.helpers.set_PD_first_free_slot_address(idPD, entryToFreeMPUAddress)
        # Ecrire (idPDlibération[compteur]+1) à idPDlibération[compteur] (+1 au compteur des emplacements libres)
        self.helpers.set_PD_nb_free_slots(idPD, self.helpers.get_PD_nb_free_slots(idPD) + 1)
        # RET @entrée MPU à libérer
        return entryToFreeMPUAddress
*)
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


(*    def __checkChild(self, idPDparent, idPDchild):
        """
        Checks that <idPDchild> is a child of <idPD> by going through the kernel structure of the parent looking for
        the child
        :param idPDparent: the parent partition
        :param idPDchild: the supposed child partition of <idPDparent>
        :return: OK (1) /NOK (0)
        """
        block_in_parent_partition_address = self.__find_block_in_MPU(idPDparent, idPDchild)
        if block_in_parent_partition_address == -1:
            # no block found, stop
            return 0  # TODO: return NULL

        if self.helpers.get_Sh1_PDflag_from_MPU_entry_address(block_in_parent_partition_address) != True:
            # idPDchild is not a child partition, stop
            return 0  # TODO: return NULL

        return 1*)


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

		Returns the child's MPU entry address used to store the shared block:OK/NULL:NOK

    <<idPDchild>>				the child partition to share with
		<<blockToShareMPUAddr>>	the block to share MPU address in the parent
*)
Definition addMemoryBlockCommon (idPDchild blockToShareMPUAddr: paddr) : LLI paddr :=
(*
def __add_memory_block(self, idPDchild, block_to_share_in_current_partition_address):
    """
    Adds a block to a child partition
    The block is still accessible from the current partition (shared memory)
    :param idPDchild: the child partition to share with
    :param block_to_share_in_current_partition_address: the block to share MPU address
    :return:the child's MPU entry address where the block has been added
    """
    # check of block_to_share_in_current_partition_address done in previous internal function
*)
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks (blockToShareMPUAddr checked before)*)
(*
    # Check idPDchild is a child of the current partition
    if self.__checkChild(self.current_partition, idPDchild) == 0:
        # idPD is not a child partition, stop
        return 0  # TODO: return NULL
*)
		(* Check idPDchild is a child of the current partition*)
		perform isChildCurrPart := checkChild currentPart idPDchild in
		if negb isChildCurrPart
		then (* idPDchild is not a child partition, stop*) ret nullAddr
		else

(*
    # Vérifier idPDenfant[compteur libre] > 0 SINON RET NULL
    # Check there are free slots in the the child to add the block to share
    if self.helpers.get_PD_nb_free_slots(idPDchild) <= 0:
        # no free slots left, stop
        return 0  # TODO: return NULL
*)
		(* Check there are free slots in the the child to add the block to share*)
		perform currentFreeSlotsNb := readPDNbFreeSlots idPDchild in
		perform zero := Index.zero in
		perform isFull := Index.leb currentFreeSlotsNb zero in
		if isFull then (* no free slots left, stop*) ret nullAddr
		else

(*
    block_to_share_entry = self.helpers.get_MPU_entry(block_to_share_in_current_partition_address)

    # Check block is accessible and present
    if block_to_share_entry[3] is False or block_to_share_entry[4] is False:
        # block not accessible or present, stop
        return 0  # TODO: return NULL
*)
		(* Check block is accessible and present*)
		perform addrIsAccessible := readMPUAccessibleFromMPUEntryAddr
																	blockToShareMPUAddr in
		if negb addrIsAccessible then (* block is inaccessible *) ret nullAddr else
		perform addrIsPresent := readMPUPresentFromMPUEntryAddr
																	blockToShareMPUAddr in
		if negb addrIsPresent then (** block is not present *) ret nullAddr else

(*
    # // Enfant : Placer le bloc du parent dans le 1er emplacement libre de l’enfant
    # entrée MPU enfant <- insérerEntrée(idPDenfant, entrée MPU courant, entrée MPU courant->start)
    # add the block to the child partition with itself as origin in the child
    block_shared_child_MPU_address = self.__insert_new_entry(
        idPDchild,
        block_to_share_entry,
        block_to_share_entry[1]  # origin
    )
*)
		(** Child: set the block to share in the child's first free slot*)
		(* the block start is set as origin in the child*)
		perform blockstart := readMPUStartFromMPUEntryAddr blockToShareMPUAddr in
		perform blockend := readMPUEndFromMPUEntryAddr blockToShareMPUAddr in
		perform blockToShareChildMPUAddr := insertNewEntry 	idPDchild
																												blockstart blockend
																												blockstart in


(*
    # // Parent : Partage du bloc avec son enfant
    # Ecrire idPDenfant à Sh1courant[entrée MPU courant ] (indiquer le partage du blocADonner dans le Shadow 1 de la partition courante)
    self.helpers.set_Sh1_PDchild_from_MPU_entry_address(block_to_share_in_current_partition_address, idPDchild)
    # Ecrire (entrée MPU enfant) à Sh1courant[entrée MPU courant]->inChildLocation (faire pointer inChildLocation à l’endroit où est stocké le bloc partagé dans la MPU enfant)
    self.helpers.set_Sh1_inChildLocation_from_MPU_entry_address(block_to_share_in_current_partition_address, block_shared_child_MPU_address)
*)
		(** Parent: register the shared block in Sh1*)
		writeSh1PDChildFromMPUEntryAddr blockToShareMPUAddr idPDchild;;
		writeSh1InChildLocationFromMPUEntryAddr blockToShareMPUAddr
																						blockToShareChildMPUAddr;;
(*
    # RET @entrée MPU enfant
    return block_shared_child_MPU_address*)
		ret blockToShareChildMPUAddr.

(*
def __remove_block_in_descendants_rec(self, current_idPDchild, current_block_to_remove_child_MPU_address):
    """
    Recursive deletion by going through the descendants and remove the block on the way
    Stop condition: reached last descendant (leaf) (maximum number of iterations)
    Processing: remove the block at this level of descendants
    Recursive calls: until the last descendant
    """
    # Remove the block in all grand-children (block not cut in any grand-children and accessible)
    # Stop condition: reached last descendant (leaf)
    if current_block_to_remove_child_MPU_address == 0:
        return

    # PROCESSING: remove the block at this level of descendants
    # // Libérer l’entrée dans l’enfant courant
    # Get descendant before block deletion
    # PDenfantNext<-Sh1enfant[MPUenfant]->PDchild (récupérer le prochain petit-enfant)
    next_idPDchild = self.helpers.get_Sh1_PDchild_from_MPU_entry_address(
        current_block_to_remove_child_MPU_address)
    # MPUenfantNext<-Sh1enfant[MPUenfant]->inChildLocation (récupérer l’emplacement du bloc partagé dans la MPU du petit-enfant)
    next_block_to_remove_child_MPU_address = self.helpers.get_Sh1_inChildLocation_from_MPU_entry_address(
        current_block_to_remove_child_MPU_address)
    # libérerEmplacement(PDenfant, MPUenfant)
    self.__free_slot(current_idPDchild, current_block_to_remove_child_MPU_address)

    # RECURSIVE call: remove block in the remaining descendants
    return self.__remove_block_in_descendants_rec(next_idPDchild, next_block_to_remove_child_MPU_address)*)

(** The [removeBlockInDescendantsRecAux] function recursively removes the block
		identified at MPU address <currLevelBlockToRemoveAddr> of the current
		descendant by going through the descendants and remove the block on the way
    Stop condition: reached last descendant (leaf) (maximum number of iterations)
    Processing: remove the block at this level of descendants
    Recursive calls: until the last descendant

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

(*
def __remove_check_subblocks_rec(self, subblock):
    """
    Recursive check by going through the subblocks starting from <subblock>
    Check all cuts are not shared and accessible and present
    Stop conditions:
        1: reached last subblock (maximum number of iterations)
        2: the block is not accessible, not present or shared
    Recursive calls: until the last subblock
    """
    # Stop condition 1: reached last subblock
    if subblock == 0:
        return 1  # TODO: return NULL

    # Stop condition 2: the block is not accessible, not present or shared
    if (
            self.helpers.get_MPU_accessible_from_MPU_entry_address(subblock) is True and
            self.helpers.get_MPU_present_from_MPU_entry_address(subblock) is True and
            self.helpers.get_Sh1_PDflag_from_MPU_entry_address(subblock) is False and
            self.helpers.get_Sh1_PDchild_from_MPU_entry_address(subblock) == 0
    ) is False:
        # block is not accessible or not present, or shared, stop
        return 0  # TODO: return NULL

    # RECURSIVE call: check next subblock
    return self.__remove_check_subblocks_rec(self.helpers.get_SC_next_from_MPU_entry_address(subblock))*)

(** The [checkRemoveSubblocksRecAux] function recursively check by going through
		the subblocks starting from <subblockAddr>
    Check all cuts are not shared and accessible and present
		Stop conditions:
        1: reached last subblock (maximum number of iterations)
        2: the subblock is not accessible, not present or shared
    Recursive calls: until the last subblock

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

(*
  def __remove_subblocks_rec(self, subblock, idPDchild):
      """
      Recursive removal by going through the subblocks and free them
      Stop condition: reached last subblock (maximum number of iterations)
      Processing: free the subblock's slot
      Recursive calls: until last subblock
      """
      # Stop condition 1: reached last subblock
      if subblock == 0:
          return  # TODO: return NULL

      # PROCESSING: free the subblock's slot
      # // Libère l’entrée dans l’enfant : insère le sous-bloc à retirer comme 1er emplacement libre puis passe au prochain sous-bloc
      # (sous-bloc next) <- SCenfant[sous-bloc]->suivant (récupèrer le sous-bloc suivant à traiter)
      next_subblock = self.helpers.get_SC_next_from_MPU_entry_address(subblock)
      # libérerEmplacement(PDenfant, sous-bloc)
      self.__free_slot(idPDchild, subblock)

      # RECURSIVE call: remove next subblock
      return self.__remove_subblocks_rec(next_subblock, idPDchild)
*)
(** The [removeSubblocksRecAux] function recursively removes all subblocks
		by going through the subblocks and free them
    Stop condition: reached last subblock (maximum number of iterations)
    Processing: free the subblock's slot
    Recursive calls: until last subblock

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
		if isBlockCut
		then (** Case 1: the block is not cut in the child partition -> remove the
							block in the child and all grand-children *)
(*
        # block not cut

        # SI MPUcourant[entrée MPU courant]->accessible == FALSE ALORS (bloc coupé dans les petits-enfants ou réquisitionné pour structure noyau) RET FALSE
        # Check if block inaccessible because of grand-children partitions (used for prepare or create, or cut
        # in grand-children)
        if self.helpers.get_MPU_accessible_from_MPU_entry_address(block_to_remove_in_current_partition_address) is False:
            # block inaccessible, stop
            return 0  # TODO: return NULL
*)
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
(*
        # // Le bloc n’est pas coupé dans les petits-enfants : Enlever le bloc partagé dans tous les petits-enfants
        # Tant que MPUenfant != NULL (parcourir l’enfant et tous les petits-enfants ayant le bloc partagé) (O(q))
        # Remove the block in all grand-children (block not cut in any grand-children and accessible)
        self.__remove_block_in_descendants_rec(idPDchild, block_to_remove_child_MPU_address)*)
				(** Remove block from child and all grand-children *)
				perform recRemoveInDescendantsEnded := removeBlockInDescendantsRec
																									idPDchild
																									blockToRemoveInChildAddr in
				if negb recRemoveInDescendantsEnded then (* timeout reached *) ret false else
				ret true
(*
    # SINON (l’enfant a coupé le bloc donc on récupère les sous-blocs sauf s’ils sont partagés et dans ce cas on avorte l’opération)
    else:
*)
		else (** Case 2: the block has been cut in the child partition -> remove all
							subblocks in the child*)
(*        # block cut

        # Vérifier que tous les sous-blocs sont non partagés et accessibles SINON RET false (O(1) si bloc non coupé -> O(s))
        # Check all cuts are not shared and accessible and present
        # first subblock is always the start of the cut linked list since it stems from the initial added block
        if self.__remove_check_subblocks_rec(block_to_remove_child_MPU_address) == 0:
            # if block is not accessible or not present, or if it is shared, stop
            return 0  # TODO: return NULL*)
				(* Check all subblocks are not shared, accessible, and present *)
				perform isRemovePossible := checkRemoveSubblocksRec
																				blockToRemoveInChildAddr in
				if negb isRemovePossible then (* remove impossible, stop *) ret false else
(*
        # Tant que sous-bloc != NULL : (O(s))
        # Remove all subblocks from the child
        self.__remove_subblocks_rec(block_to_remove_child_MPU_address, idPDchild)*)
				(** Remove all subblocks *)
				perform recRemoveSubblocksEnded := removeSubblocksRec
																											idPDchild
																											blockToRemoveInChildAddr in
				if negb recRemoveSubblocksEnded then (* timeout reached *) ret false else
(*
        # Ecrire TRUE à MPUcourant[entrée MPU courant].accessible (si le bloc a été coupé alors il faut rendre le bloc accessible de nouveau à la partition courante et aux ancêtres)
        self.helpers.set_MPU_accessible_from_MPU_entry_address(block_to_remove_in_current_partition_address, True)*)
				(** Qet back the block as accessible in the ancestors because it was cut *)
				writeMPUAccessibleFromMPUEntryAddr blockToRemoveInCurrPartAddr true ;;
(*
        # Ecrire TRUE à MPU[ancêtres].accessible (O(p) parait acceptable pour un remove avec un bloc coupé, sinon besoin de stocker l’adresse du bloc dans les ancêtres)
        self.__write_accessible_to_ancestors_rec(self.current_partition,
                                                 self.helpers.get_MPU_start_from_MPU_entry_address(
                                                 block_to_remove_in_current_partition_address
                                             ), True)*)
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
																		idBlockToRemove
																		blockToRemoveInCurrPartAddr: paddr) : LLI bool :=
(*
    def __remove_memory_block(self, idPDchild, block_to_remove_in_current_partition_address):
        """
        Removes a block from a child partition
        The block could be cut in the child partition but all subblocks still accessible
        This operation succeeds for any shared memory block previously added, but fails if the purpose of the block is
        not shared memory anymore, in particular in such cases:
            - The block can't be removed if the child or its descendants used it (or part of it) as a kernel structure
            - The block can't be removed if the child's descendants cut the block
        :param idPDchild: the child partition to remove from
        :param block_to_remove_in_current_partition_address: the block to remove MPU address
        :return: OK(1)/NOK(0)
        """
*)
		(** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

		(** Checks (blockToRemoveMPUAddr checked before from idBlockToRemove )*)
(*
    # check of block_to_remove_in_current_partition_address done in previous internal function

    # // Enfant : Retirer le bloc du parent
    # Check the provided idPDchild corresponds to the child to whom the block has been given (if given)
    if self.helpers.get_Sh1_PDchild_from_MPU_entry_address(block_to_remove_in_current_partition_address) != idPDchild:
        # no correspondance, stop
        return 0  # TODO: return NULL*)
		(* check the provided idPDchild corresponds to the child to whom the block
				has been previously given (if given)*)
		perform pdchildblock := readSh1PDChildFromMPUEntryAddr
																blockToRemoveInCurrPartAddr in
		perform hasChildBlock := getBeqAddr idPDchild pdchildblock in
		if negb hasChildBlock then (* no correspondance, stop *) ret false else

(*
    # // Enfant : Libérer l’entrée en récupérant tous les sous-blocs coupés éventuels (O(1) -> O(q) || O(s||p))
    # entrée MPU enfant <- Sh1courant[entrée MPU courant]->inChildLocation (récupérer l’emplacement du bloc dans la MPU de enfant)
    block_to_remove_child_MPU_address = self.helpers.get_Sh1_inChildLocation_from_MPU_entry_address(
        block_to_remove_in_current_partition_address)
    # Si SCenfant[entrée MPU enfant]->origin == MPUenfant[entrée MPU enfant]->start ET SCenfant[entrée MPU enfant]->next == NULL ALORS (l’enfant n’a pas coupé le bloc donc on récupère le bloc dans l’enfant et tous les petits-enfants)
    # Check if the block is cut in the child partition
    if (self.helpers.get_SC_origin_from_MPU_entry_address(block_to_remove_child_MPU_address) ==
        self.helpers.get_MPU_start_from_MPU_entry_address(block_to_remove_in_current_partition_address)) \
            and self.helpers.get_SC_next_from_MPU_entry_address(block_to_remove_child_MPU_address) == 0:
*)
		(** Child (and grand-children): remove block *)
		perform blockIsRemoved := removeBlockInChildAndDescendants
																		currentPart
																		idPDchild
																		idBlockToRemove
																		blockToRemoveInCurrPartAddr in
		if negb blockIsRemoved then (* block not removed, stop*) ret false else
(*
    # // Parent : rétablir l’entrée dans la partition courante
    # Ecrire default dans Sh1courant[entrée MPU courant]
    self.helpers.set_Sh1_entry_from_MPU_entry_address(block_to_remove_in_current_partition_address, 0, 0, 0)*)
		(** Parent: remove block reference to the child *)
		perform defaultSh1Entry := getDefaultSh1Entry in
		writeSh1EntryFromMPUEntryAddr blockToRemoveInCurrPartAddr defaultSh1Entry ;;
(*
    # RET OK
    return 1*)
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


(** The [eraseBlockAux] function recursively zeroes all addresses until it reaches
		the <startAddr>
		Stop condition: reached base address
    Processing: zeroes the current address
    Recursive calls: until base address
*)
(*Fixpoint eraseBlockAux 	(timeout : nat) (startAddr currentAddr : paddr): LLI unit :=
	match timeout with
		| 0 => ret tt (*Stop condition 1: reached end of structure list*)
		| S timeout1 =>	eraseAddr currentAddr ;; (*erase the current address*)
										if beqAddr currentAddr startAddr then
											(*Reached start address, no more addresses to erase*)
											ret tt
										else
											(*Continue to erase lower addresses*)
											perform predAddr := Paddr.pred currentAddr in
											eraseBlockAux timeout1 startAddr predAddr
end.*)

(** The [eraseBlock] function fixes the timeout value of [eraseBlockAux] *)
(*Definition eraseBlock (startAddr endAddr : paddr) : LLI unit :=
	eraseBlockAux N startAddr endAddr.*)

(*
    def init_MPU(self, kernel_structure_start, index_start, index_end):
        """
        Initializes all entries of the MPU between <index_start> and <index_end>
        The free slots list starts with the entry <index_start>, points to the next entry until reaching <index_end>
        :param kernel_structure_address: kernel structure frame's start address
        :param index_start: entry used as the free slots list's head
        :param index_end: entry used as the free slots list's queue
        :return: void
        """
        # middle entries are pointing their previous and following entries
        for n in range(index_start, index_end - 1):
            address = kernel_structure_start + n * self.constants.MPU_entry_length
            start = 0
            end = kernel_structure_start + (n + 1) * self.constants.MPU_entry_length
            self.helpers.write_MPU_entry_with_index(address, n, start, end, False, False)
        # last entry has no following entry
        self.helpers.write_MPU_entry_with_index(
            (index_end - 1) * self.constants.MPU_entry_length + kernel_structure_start,
            index_end - 1,
            0,
            0,
            False,
            False
        )
*)
(** The [initMPUEntryRec] function recursively initializes all MPU entries from
		<indexCurr> to 0 of kernel structure located at <kernelStructureStartAddr>
		by constructing a linked list of all entries representing the free slots.
		The indexes are 0-indexed.
	Returns true:OK/false:NOK
*)
Fixpoint initMPUEntryRecAux 	(timeout : nat)
															(kernelStructureStartAddr : paddr)
															(indexCurr : index): LLI bool :=
	match timeout with
	| 0 => 	ret false (* timeout reached *)
	| S timeout1 => 	(** PROCESSING: set default values in current entry *)
										perform zero := Index.zero in
										if beqIdx indexCurr zero
										then
											(** STOP condition: parsed all entries *)
											perform secondEntryPointer := Paddr.addPaddrIdx
																											kernelStructureStartAddr
																											Constants.MPUEntryLength in
											perform mpuEntry := buildMPUEntry
																						nullAddr
																						secondEntryPointer
																						false
																						false in
											writeMPUEntryWithIndexFromMPUEntryAddr
													kernelStructureStartAddr
													zero
													mpuEntry;;
											ret true
										else
											perform idxsucc := Index.succ indexCurr in
											(* current entry points to the next via the endAddr field*)
											perform nextEntryOffset := Index.mulIdx
																									idxsucc
																									Constants.MPUEntryLength in
											(*perform nextEntryPointer := Paddr.addPaddr
																										kernelStructureStartAddr
																										nextEntryOffset in*)
											perform nextEntryPointer := Paddr.addPaddrIdx
																										kernelStructureStartAddr
																										nextEntryOffset in
											perform mpuEntry := buildMPUEntry
																						nullAddr
																						nextEntryPointer
																						false
																						false in
											perform currEntryOffset := Index.mulIdx
																									indexCurr
																									Constants.MPUEntryLength in
											perform currEntryPointer := Paddr.addPaddrIdx
																										kernelStructureStartAddr
																										currEntryOffset in
											writeMPUEntryWithIndexFromMPUEntryAddr
													currEntryPointer
													indexCurr
													mpuEntry;;
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
	perform lastEntryOffset := Index.mulIdx lastindex Constants.MPUEntryLength in
	perform lastEntryPointer := Paddr.addPaddrIdx 	kernelStructureStartAddr
																									lastEntryOffset in
	writeMPUEntryWithIndexFromMPUEntryAddr 	lastEntryPointer
																					lastindex
																					lastMPUEntry;;
	ret true.

(*
def init_Sh1(self, kernel_structure_start, index_start, index_end):
      """
      Initializes all entries of the Sh1 between <index_start> and <index_end> (excluded) to default -> 0 | 0 | 0
      :param kernel_structure_address: kernel structure frame's start address
      :param index_start: start entry
      :param index_end: end entry
      :return: void
      """
      for i in range(index_start, index_end):
          self.helpers.set_Sh1_entry_from_MPU_entry_address(kernel_structure_start
                                                            + i * self.constants.MPU_entry_length,
                                                            0, 0, 0)*)

(** The [initSh1EntryRec] function recursively initializes all Sh1 entries from
		<indexCurr> to 0 of kernel structure located at <kernelStructureStartAddr>
		wit the default Sh1 entry value.
		The indexes are 0-indexed.
	Returns true:OK/false:NOK
*)
Fixpoint initSh1EntryRecAux 	(timeout : nat) (kernelStructureStartAddr : paddr)
													(indexCurr : index) : LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 => (** PROCESSING: set default values in current entry *)
										perform zero := Index.zero in
										if beqIdx indexCurr zero
										then
											(** STOP condition: parsed all entries *)
											perform defaultSh1Entry := getDefaultSh1Entry in
											writeSh1EntryFromMPUEntryAddr kernelStructureStartAddr
																										defaultSh1Entry;;
											ret true
										else
											perform defaultSh1Entry := getDefaultSh1Entry in
											perform currEntryOffset := Index.mulIdx
																									indexCurr
																									Constants.MPUEntryLength in
											perform currEntryPointer := Paddr.addPaddrIdx
																										kernelStructureStartAddr
																										currEntryOffset in
											writeSh1EntryFromMPUEntryAddr currEntryPointer
																										defaultSh1Entry;;
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
(*
  def init_SC(self, kernel_structure_start, index_start, index_end):
      """
      Initializes all entries of the SC between <index_start> and <index_end> (excluded) to default -> 0 | 0
      :param kernel_structure_address: kernel structure frame's start address
      :param index_start: start entry
      :param index_end: end entry
      :return: void
      """
      for i in range(index_start, index_end):
          self.helpers.set_SC_entry_from_MPU_entry_address(kernel_structure_start
                                                           + i * self.constants.MPU_entry_length,
                                                           0, 0)
*)

(** The [initSCEntryRec] function recursively initializes all SC entries from
		<indexCurr> to 0 of kernel structure located at <kernelStructureStartAddr>
		wit the default SC entry value.
		The indexes are 0-indexed.
	Returns true:OK/false:NOK
*)
Fixpoint initSCEntryRecAux 	(timeout : nat) (kernelStructureStartAddr : paddr)
													(indexCurr : index) : LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 => (** PROCESSING: set default values in current entry *)
										perform zero := Index.zero in
										if beqIdx indexCurr zero
										then
											(** STOP condition: parsed all entries *)
											perform defaultSCEntry := getDefaultSCEntry in
											writeSCEntryFromMPUEntryAddr 	kernelStructureStartAddr
																										defaultSCEntry;;
											ret true
										else
											perform defaultSCEntry := getDefaultSCEntry in
											perform currEntryOffset := Index.mulIdx
																									indexCurr
																									Constants.MPUEntryLength in
											perform currEntryPointer := Paddr.addPaddrIdx
																										kernelStructureStartAddr
																										currEntryOffset in
											writeSCEntryFromMPUEntryAddr 	currEntryPointer
																										defaultSCEntry;;
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
(*
def __delete_shared_blocks_rec(self, current_MPU_kernel_structure, idPDchildToDelete):
    """Recursive deletion by going through the structure list and remove all blocks belonging to the child that is
    deleted
    Stop condition: reached end of structure list (maximum number of iterations)
    Processing: remove all blocks shared with the child to delete in the current structure
    Recursive calls: until the end of the structure
    """
    # Stop condition: reached end of structure list
    if current_MPU_kernel_structure == 0:  # TODO NULL
        return

    # PROCESSING: remove all blocks shared with the child to delete in the current structure
    for i in range(self.constants.kernel_structure_entries_nb):
        # SI ptSh1courant[indexCourant]->PDChild == PDenfantASupprimer ALORS (le bloc à l’index courant appartient à la partition enfant à supprimer)
        current_MPU_entry_address = current_MPU_kernel_structure + i*self.constants.MPU_entry_length
        block_id = self.helpers.get_MPU_start_from_MPU_entry_address(current_MPU_entry_address)
        if self.helpers.get_Sh1_PDchild_from_MPU_entry_address(current_MPU_entry_address) == idPDchildToDelete:
            # the slot corresponds to memory shared or prepared  with the child to destruct, remove sharing
            # Ecrire TRUE à MPU[ancêtres].accessible (O(m*p) car recherche dans p ancêtres, sinon besoin de stocker l’adresse du bloc dans l’ancêtre direct pour O(p))
            if self.helpers.get_SC_next_from_MPU_entry_address(current_MPU_entry_address) == 0 \
                    and self.helpers.get_SC_origin_from_MPU_entry_address(current_MPU_entry_address) \
                    == block_id:
                # if the block isn't cut in the current partition, set as accessible in the ancestors
                self.__write_accessible_to_ancestors_rec(self.current_partition, block_id, True)
            # Ecrire TRUE à MPUcourant[indexCourant].accessible (si le bloc a été coupé alors il faut rendre le bloc accessible de nouveau à la partition courante et aux ancêtres)
            self.helpers.set_MPU_accessible_from_MPU_entry_address(current_MPU_entry_address, True)
            # Ecrire default à ptSh1courant[indexCourant] (Mettre à default Sh1)
            self.helpers.set_Sh1_entry_from_MPU_entry_address(current_MPU_entry_address, 0, 0, 0)
    # RECURSIVE call to next structure
    # ptMPUcourant <- ptMPUcourant[indexCourant] (passer au nœud MPU suivant)
    current_MPU_kernel_structure = self.helpers.get_kernel_structure_next_from_kernel_structure_start(current_MPU_kernel_structure)
    return self.__delete_shared_blocks_rec(current_MPU_kernel_structure, idPDchildToDelete)
*)
(** The [deleteSharedBlocksInStructRecAux] function recursively removes all blocks
		belonging to the child <idPDchildToDelete> in the <currentPart> by going
		through all entries of the structure <kernelStructureStartAddr> from the
		last entry
		Stop condition: reached first entry of the structure (maximum number of iterations)
		Processing: remove all blocks shared with the child to delete in the current
								structure
    Recursive calls: until the first entry

		Returns true:OK/false:NOK*)
Fixpoint deleteSharedBlocksInStructRecAux 	(timeout : nat)
																						(currentPart : paddr)
																						(kernelStructureStartAddr : paddr)
																						(idPDchildToDelete : paddr)
																						(currIndex : index): LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 =>
										perform zero := Index.zero in
										if beqIdx currIndex zero
										then
											(** STOP condition: parsed all entries *)
											ret true
										else
											(** PROCESSING: remove all blocks shared with the child to
																			delete in the current structure *)
											perform offset := Index.mulIdx currIndex Constants.MPUEntryLength in
											perform currMPUEntryAddr :=	Paddr.addPaddrIdx
																												kernelStructureStartAddr
																												offset in
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
														if isCut
														then (* if the block isn't cut in the current
																	partition, set as accessible in the ancestors *)
																	writeAccessibleRec currentPart blockID true ;;
																	(** RECURSIVE call: delete block of next entry
																											if needed *)
																	perform idxpred := Index.pred currIndex in
																	deleteSharedBlocksInStructRecAux 	timeout1
																																		currentPart
																																		kernelStructureStartAddr
																																		idPDchildToDelete
																																		idxpred
														else
																	(** RECURSIVE call: delete block of next entry
																											if needed *)
																	perform idxpred := Index.pred currIndex in
																	deleteSharedBlocksInStructRecAux 	timeout1
																																		currentPart
																																		kernelStructureStartAddr
																																		idPDchildToDelete
																																		idxpred
										else
													(** RECURSIVE call: delete block of next entry if needed *)
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

		Returns true:OK/false:NOK*)
Fixpoint deleteSharedBlocksRecAux 	(timeout : nat)
																		(currentPart : paddr)
																		(currKernelStructureStartAddr : paddr)
																		(idPDchildToDelete : paddr) : LLI bool :=
	match timeout with
		| 0 => 	ret false (* timeout reached *)
		| S timeout1 =>
										if beqAddr idPDchildToDelete nullAddr
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
											(** RECURSIVE call: write default values in precedent index *)
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


(** The [collectStructure] function pulls the structure to be collected out of
		the list of structures.
		Returns unit

    <<idPD>>									the PD where the collect is done
		<<predStructureAddr>>			the structure before the stucture to be collected
		<<collectStructureAddr>>	the structure to be collected

 *)
Definition collectStructure (idPD predStructureAddr collectStructureAddr : paddr)
																																: LLI unit :=
(*
  # // sortir le nœud vide collecté de la liste des structures
  # all collected slots removed from free slot list
  # Ecrire ptNoeudCourant->next à ptMPUsuivantPrécédent (relier le bloc MPU précédent au bloc MPU suivant de celui qu’on enlève)
  next_structure_address = self.helpers.get_kernel_structure_next_from_kernel_structure_start(
      current_structure_address)
	if current_structure_address == self.helpers.get_PD_pointer_to_MPU_linked_list(idPD):*)
	perform nextStructureAddr := readNextFromKernelStructureStart collectStructureAddr in
	perform firstStructure := readPDStructurePointer idPD in
	perform isFirstStructure := getBeqAddr collectStructureAddr firstStructure in
	if isFirstStructure
	then (* Special case: structure to remove is the first structure -> adjust pointers *)
(*
        # Special case: structure to remove is the first structure -> adjust pointers
        if next_structure_address == 0:
            # no more structures in list
            self.helpers.set_PD_pointer_to_MPU_linked_list(previous_structure_address,
                                                           next_structure_address)
        else:
            # still structures in list, set correct pointers to PD's Sh1 and PD's SC
            self.helpers.set_PD_pointer_to_MPU_linked_list(previous_structure_address,
                                                           next_structure_address)*)
				(* 	set the PD's structure pointer to the next structure (which could
						be NULL if it was the last TODO compressed statements*)
				writePDStructurePointer idPD nextStructureAddr ;;
				ret tt
(*
    else:
        # structure to remove is in the chained list of structures -> link previous to next structure
        self.helpers.set_kernel_structure_next_from_kernel_structure_start(previous_structure_address,
                                                                                   next_structure_address)*)
	else (* the structure to remove is somewhere in the middle of the list of
					structures, link previous structure to next structure *)
				writeNextFromKernelStructureStart predStructureAddr nextStructureAddr ;;
				ret tt.

(*
    # Stop condition 2: found a free structure to collect
    # toCollect <- True
    collect = True
    # Pour indexCourant de 0 à MaxEntrées : (Parcourir les entrées du nœud : on vérifie qu’aucune entrée n’est présente dans le noeud)
    for current_index in range(self.constants.kernel_structure_entries_nb):
       # SI MPUcourant[indexCourant]->present == 1 ALORS (une entrée est présente, le nœud n’est pas collectable, on peut passer au noeud suivant) || start = NULL pour enlever dépendance à present
        if self.helpers.get_MPU_present_from_MPU_entry_address(
                current_structure_address + current_index*self.constants.MPU_entry_length):
            # toCollect <- False ;
            collect = False
            # break
            break*)

(** The [checkStructureEmptyRecAux] function recursively checks the current
		structure is empty from last entry until first entry.

		Stop conditions:
				1: found a used entry
				2: all entries of the structure are empty (maximum number of iterations)
		Processing: check the current entry
    Recursive calls: until all entries are cheked

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
										perform offset := Index.mulIdx currIndex
																									Constants.MPUEntryLength in
										perform currMPUEntryAddr :=	Paddr.addPaddrIdx 	structureAddr
																																		offset in
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

		Returns unit

		<<currFreeSlotAddr>>				the recursive checked free slot
    <<predFreeSlotAddr>>				pointer to the previous free slot
		<<idPD>>										the PD from where to collect
		<<structureCollectAddr>>		the structure to collect
*)
Fixpoint collectFreeSlotsRecAux (timeout : nat)
																(predFreeSlotAddr currFreeSlotAddr : paddr)
																(idPD :paddr)
																(structureCollectAddr : paddr) : LLI unit :=
(*
  def __collect_free_slots_rec(self, previous_free_slot_address, current_free_slot_address, idPD, current_structure_address):
      """Recursive removal by going through the free slots list and remove the free slots belonging to the empty
      structure that is collected
      Stop condition: reached end of free slots list (maximum number of iterations)
      Recursive calls: until the end of the list
      """*)

match timeout with
		| 0 => 	ret tt (* timeout reached *)
		| S timeout1 =>

										if beqAddr currFreeSlotAddr nullAddr
										then
											(** STOP condition: reached end of free slots list *)
(*
      # Stop condition: reached end of free slots list
      if current_free_slot_address == 0:
          return*)
											ret tt
										else
											(** PROCESSING: remove slots to collect from free slots list*)
(*
      # RECURSIVE call to next free slot inspection (slot to be removed if belongs to the empty structure collected)
      # compute the current slot's kernel structure
      slot_structure = current_free_slot_address \
                       - self.helpers.get_MPU_index(current_free_slot_address) * self.constants.MPU_entry_length*)
											(* compute the current slot's kernel structure *)
											perform MPUEntryIndex := readMPUIndexFromMPUEntryAddr
																										currFreeSlotAddr in
											perform slotKStructureStart := getKernelStructureStartAddr
																												currFreeSlotAddr
																												MPUEntryIndex in
(*
      # get next free slot
      next_free_slot_address = self.helpers.get_MPU_end_from_MPU_entry_address(current_free_slot_address)*)
											(* get next free slot from MPU end field *)
											perform nextFreeSlotAddr := readMPUEndFromMPUEntryAddr
																											currFreeSlotAddr in
(*
      # SI slotLibreCourant appartient à ptMPUCourant (le slot est dans la page à collecter, on l’enlève)
      if (slot_structure == current_structure_address):
          # slot must be collected*)
											if beqAddr slotKStructureStart structureCollectAddr
											then
												(* the slot is located in the structure to collect *)
(*
          # SI slotLibreCourant == PDcourant[pointeur emplacement libre] ALORS (l’emplacement à libérer est le 1er emplacement libre)
          if current_free_slot_address == self.helpers.get_PD_first_free_slot_address(idPD):
              # // Ajuster pointeur libre
              # Special case if slot to remove is the first free slot
              # Ecrire slotLibreCourant->end à idPD[pointeur libre] (décaler le 1er emplacement libre au prochain)
              self.helpers.set_PD_first_free_slot_address(idPD, next_free_slot_address)*)

												perform firstFreeSlotAddr := readPDFirstFreeSlotPointer idPD in
												if beqAddr currFreeSlotAddr firstFreeSlotAddr
												then
													(* Special case if slot to remove is the first free
														slot: the next free slot becomes the first free slot
														of the free slots list *)
													writePDFirstFreeSlotPointer idPD nextFreeSlotAddr ;;
													(** RECURSIVE call: continue collect with rest of list *)
													collectFreeSlotsRecAux 	timeout1
																									idPD
																									currFreeSlotAddr
																									nextFreeSlotAddr
																									structureCollectAddr
(*
          # SINON
          else:
              # // Supprimer le bloc libre de la chaîne libre : relier le bloc libre précédent au bloc libre suivant
              # remove current slot from free slot list: chain previous to next free slot
              # Ecrire slotLibreCourant ->end à slotLibrePrécédent->end (end contient l’emplacement libre suivant qu’on décale)
              self.helpers.set_MPU_end_from_MPU_entry_address(previous_free_slot_address, next_free_slot_address)*)
												else
													(* remove current slot from free slot list: chain
														previous to next free slot *)
														writeMPUEndFromMPUEntryAddr predFreeSlotAddr
																												nextFreeSlotAddr ;;
														(** RECURSIVE call: continue collect with rest of list *)
														collectFreeSlotsRecAux 	timeout1
																										idPD
																										currFreeSlotAddr
																										nextFreeSlotAddr
																										structureCollectAddr
(*
      # SINON slotLibrePrécédent <- slotLibreCourant (slot courant reste dans la liste des emplacements libres, traité donc devient précédent)
      else:
          # slot is not collected, adjust previous pointer
          previous_free_slot_address = current_free_slot_address
      # slotLibreCourant <- slotLibreCourant ->end
      current_free_slot_address = next_free_slot_address
      return self.__collect_free_slots_rec(previous_free_slot_address,
                                           current_free_slot_address,
                                           idPD,
                                           current_structure_address)*)
										else
											(* the slot is not located in the structure to collect *)
											(** RECURSIVE call: continue collect with rest of list *)
											collectFreeSlotsRecAux 	timeout1
																							idPD
																							currFreeSlotAddr
																							nextFreeSlotAddr
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
(*
def __collect_structure_rec(self, idPD, previous_structure_address, current_structure_address):
    """Recursive collect by going through the structure list
    Stop conditions:
        1: reached end of structure list (maximum number of iterations) OR
        2: found a free structure
    Recursive calls:
        - the structure is not empty
        - the structure is empty but has not been prepared by the current partition (e.g. the child tries to collect/
            steal a structure from its parent's set of blocks
    """*)
match timeout with
		| 0 => 	ret nullAddr (* timeout reached *)
		| S timeout1 =>
										if beqAddr currStructureAddr nullAddr
										then
											(** STOP condition 1: reached end of structure list *)
											(*# Stop condition 1: reached end of structure list
													if current_structure_address == 0:  # TODO: if NULL
															# RET NULL
															return 0  # TODO: return NULL*)
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
(*
    # RECURSIVE call to next structure inspection (structure not empty or can't be collected)
    # SINON ptMPUsuivantPrécédent <- ptMPUcourant ; ptNoeudCourant <- ptNoeudCourant->next (passer au nœud MPU suivant)
    previous_structure_address = current_structure_address
    current_structure_address = self.helpers.get_kernel_structure_next_from_kernel_structure_start(
        current_structure_address)
    return self.__collect_structure_rec(idPD, previous_structure_address, current_structure_address)
*)
												perform nextStructureAddr := readNextFromKernelStructureStart
																											currStructureAddr in
												collectStructureRecAux 	timeout1
																								currentPart
																								idPD
																								currStructureAddr
																								nextStructureAddr
											else
												(* structure empty, MAY be collected, check first *)
(*
    # SI toCollect ==  True ALORS (on a atteint la fin du nœud courant, tous les emplacements de la page sont libres, on collecte la page courante)
    if collect is True:
        # collect structure

        # check structure is a block in current partition
        # otherwise means the current partition wants to collect a node given by its parent and this can't be
        # collected so pass to next node
        # noeudASupprimer <- ChercherBlocDansMPU(idPD, ptMPUcourant) (O(m) acceptable car collect, PDcourant peut être soit l’enfant lui-même soit le parent)
        structure_to_collect_MPU_address = self.__find_block_in_MPU(self.current_partition, current_structure_address)
        if structure_to_collect_MPU_address != -1:
            # structure to collect comes from previous prepare of current partition, ok to collect
*)
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
(*
            # find inner slots to remove from list of free slots
            #slotLibreCourant <- PDcourant[pointeur emplacement libre] (on démarre du 1er emplacement libre, forcément non NULL car on peut retirer une page)
            current_free_slot_address = self.helpers.get_PD_first_free_slot_address(idPD)
            # slotLibrePrécédent <- NULL (pointeur vers le slot précédent qu’on va devoir relier au suivant si besoin d’enlever le slot courant)
            previous_free_slot_address = 0
            # Tant que slotLibrecourant != NULL : (Parcourir la liste des emplacements libres et libérer les slots dans la page à collecter)
            self.__collect_free_slots_rec(previous_free_slot_address, current_free_slot_address, idPD, current_structure_address)*)
												(* remove all slots to collect from list of free slots*)
												perform firstFreeSlotAddr := readPDFirstFreeSlotPointer idPD in
												collectFreeSlotsRecAux 	N
																								nullAddr
																								firstFreeSlotAddr
																								idPD
																								currStructureAddr ;;
												(* Pull out the structure from the list of structures
														TODO created specific function*)
												collectStructure idPD predStructureAddr currStructureAddr ;;
(*
						# Change PD structure accordingly
            # Ecrire (idPD[nbPrepare]-1) à idPD[nbPrepare] (-1 à nbPrepare)
            self.helpers.set_PD_nb_prepare(idPD, self.helpers.get_PD_nb_prepare(idPD) - 1)
            # Ecrire (idPD[compteur]-MaxEntrees) à idPD[compteur] (enlever #MaxEntrees emplacements libres)
            self.helpers.set_PD_nb_free_slots(idPD,
                                              self.helpers.get_PD_nb_free_slots(idPD)
                                              - self.constants.kernel_structure_entries_nb)
*)
											(* Change PD structure accordingly *)
											perform nbPrepare := readPDNbPrepare idPD in
											perform predNbPrepare := Index.pred nbPrepare in
											writePDNbPrepare idPD predNbPrepare ;;
											perform nbFreeSlots := readPDNbFreeSlots idPD in
											perform entriesnb := getKernelStructureEntriesNb in
											perform subNbFreeSlots := Index.subIdx nbFreeSlots entriesnb in
											writePDNbFreeSlots idPD subNbFreeSlots ;;
(*
            # // remettre accessible le bloc où il est (parent ou enfant même traitement)
            # Ecrire TRUE à @noeudASupprimer->accessible
            self.helpers.set_MPU_accessible_from_MPU_entry_address(structure_to_collect_MPU_address, True)*)
											(* Set block accessible where it is (current or child) *)
											writeMPUAccessibleFromMPUEntryAddr 	blockToCollectMPUAddr
																													true ;;
(*
            # //Si bloc pas coupé alors remettre accessible au parent et aux ancêtres (bloc coupé ->reste inaccessible aux ancêtres)
            # SI SC[noeudASupprimer]->suivant == NULL ET SC[noeudASupprimer]->origin == noeudASupprimer ALORS (bloc pas coupé)
            if (self.helpers.get_SC_next_from_MPU_entry_address(structure_to_collect_MPU_address) == 0 and
                    self.helpers.get_SC_origin_from_MPU_entry_address(structure_to_collect_MPU_address)
                    == self.helpers.get_MPU_start_from_MPU_entry_address(structure_to_collect_MPU_address)):
                # block used to prepare is not cut ->set accesible in ancestors
                # Ecrire TRUE dans MPU[ancêtres]->accessible (O(m*p) car recherche dans p ancêtres, sinon besoin de stocker l’adresse du bloc dans l’ancêtre direct pour O(p))
                self.__write_accessible_to_ancestors_rec(idPD, current_structure_address, True)*)
											(* Set block accessible in parent and ancestors if not cut *)
											writeAccessibleToAncestorsIfNotCutRec idPD
																														currStructureAddr
																														blockToCollectMPUAddr
																														true ;;
(*
            # Ecrire default à Sh1[noeudASupprimer] (écraser l’entrée Sh1 dans le cas où ce serait un collect sur un enfant)
            self.helpers.set_Sh1_entry_from_MPU_entry_address(structure_to_collect_MPU_address, 0, 0, 0)*)
											perform defaultSh1Entry := getDefaultSh1Entry in
											writeSh1EntryFromMPUEntryAddr blockToCollectMPUAddr
																										defaultSh1Entry ;;

(*            # RET ptMPUCourant
            return current_structure_address*)
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

