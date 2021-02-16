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
    This file contains PIP memory services : [createPartition],
      [deletePartition], [addVAddr], [removeVAddr], [countToMap],
      [prepare] and [collect].

    The definitions of recursive functions like [countToMap], [prepare] and
      [collect] match the same form :
      - part 1 : <<functionNameRec>> is the recursive funtion
      - part 2 : <<functionNameAux>> fixes the sufficient timeout value for recursion
                 to complete
      - part 3 : <<funtionName>> is the PIP service. It calls <<functionNameAux>>
                with the required parameters *)

Require Import Model.Hardware Model.ADT Model.Lib Model.MAL Bool Core.Internal Arith  List.
Import List.ListNotations.

Export Internal.Helpers.
Set Printing Implicit.
Set Typeclasses Debug Verbosity 5.
Open Scope mpu_state_scope.
Print Visibility.

(** ** The createPartition PIP MPU service

    The [createPartition] system call creates a new child (sub-partition of the
    current partition), e.g. initializes the block <idBlock> as a PD block and 
		sets the current partition as the parent partition.
		Returns true:OK/false:NOK

    <<idBlock>>       	The block to become the child Partition Descriptor 
												(id = start field of an existing block)
*)
Definition createPartition (idBlock: paddr) : LLI bool :=
    (** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in

(*	# entrée MPU <- ChercherBlocDansMPU(idPartitionCourante, idBloc)
    block_in_current_partition_address = self.__find_block_in_MPU(self.current_partition, idBlock)
    *)
		(** Find the block in the current partition *)
    perform blockInCurrentPartitionAddr := findBlockInMPU currentPart idBlock in
		
		(** Check the block exists and not shared and size > minimum MPU region size ELSE NOK*)
(*
    if block_in_current_partition_address == -1:
        # no block found, stop
        return 0*)
		perform addrIsNull := compareAddrToNull	blockInCurrentPartitionAddr in
		if addrIsNull then(** no block found, stop *) ret false else
		(*block_MPU_entry = self.helpers.get_MPU_entry(block_in_current_partition_address) *)
		perform blockMPUentry := readMPUEntry blockInCurrentPartitionAddr in
(*
    if not block_MPU_entry[3]:
        # block is inaccessible
        return 0
		*)
		perform addrIsAccessible := readMPUAccessibleFromMPUEntryAddr	blockInCurrentPartitionAddr in
		if negb addrIsAccessible then (** block is inaccessible *) ret false else
(*
    if (block_MPU_entry[2] - block_MPU_entry[1]) < self.constants.MPU_region_min_size:
        # block is smaller than the MPU region constraint
        return 0 
*)
		perform blockSize := sizeOfBlock blockMPUentry.(mpublock) in
		perform minBlockSize := getMinBlockSize in
		perform isBlockTooSmall := Paddr.leb blockSize minBlockSize in
		if isBlockTooSmall then (** block is smaller than the minimum  *) ret false 
		else

(*
    if self.helpers.get_Sh1_PDchild_from_MPU_entry_address(block_in_current_partition_address) != 0:
        # block is already shared with a child partition
        return 0  # TODO: return NULL*)
		(* if accessible, then PDflag can't be set, we just need to check PDchild *)
		perform PDChildAddr := readPDChildFromMPUEntry	blockInCurrentPartitionAddr in
		perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
		if negb PDChildAddrIsNull (*shouldn't be null*) then ret false else

(*

    # // Initialiser bloc PD enfant
    # blocPD <- RécupérerBloc(entrée MPU)
    new_PD_block = self.helpers.get_MPU_start_from_MPU_entry_address(block_in_current_partition_address)*)
		perform newPDBlock := readMPUBlockFromMPUEntryAddr blockInCurrentPartitionAddr in

(*
    # Mettre à 0 le blocPD entier (ou jusqu’à index pointeur libre-> cas où le bloc est très grand)
    for i in range(self.helpers.get_MPU_start_from_MPU_entry_address(block_in_current_partition_address),
                   self.helpers.get_MPU_end_from_MPU_entry_address(block_in_current_partition_address)):
        self.memory.write_bit(i, 0)*)
		(** Erase the future Partition Descriptor content*)
		eraseBlock newPDBlock ;;

(*
    # Ecrire NULL à blocPD[index MPU]
    self.helpers.set_PD_pointer_to_MPU_linked_list(new_PD_block, 0)*)
		(* create PD Table by setting the structure to the default values *)
		initPDTable newPDBlock.(startAddr) ;;
		perform nullAddr := getNullAddr in
		writePDStructurePointer newPDBlock.(startAddr) nullAddr ;; 

(*
    # Ecrire 0 à blocPD[compteur libre]
    self.helpers.set_PD_nb_free_slots(new_PD_block, 0)*)
		writePDNbFreeSlots newPDBlock.(startAddr) 0 ;;
(*
    # Ecrire NULL à blocPD[pointeur libre]
    self.helpers.set_PD_first_free_slot_address(new_PD_block, 0)*)
		writePDFirstFreeSlotAddr newPDBlock.(startAddr) nullAddr ;;

(*
    # Ecrire 0 à blocPD[compteur nbPrepare]
    self.helpers.set_PD_nb_prepare(new_PD_block, 0)*)
		writePDNbPrepare newPDBlock.(startAddr) 0 ;;
(*
    # //Lier PD enfant à la partition courante
    # Ecrire PDcourant à blocPD[parent]
    self.helpers.set_PD_parent(new_PD_block, self.current_partition)*)
		writePDParent newPDBlock.(startAddr) currentPart ;;

(*
    # Ecrire FALSE dans MPUcourant[entrée MPU]->Accessible (bloc inaccessible pour la partition courante)
    self.helpers.set_MPU_accessible_from_MPU_entry_address(block_in_current_partition_address, False)*)
		(** Reflect the child Partition Description creation in the current partition *)
		(** set the block as not available anymore*)
		writeMPUAccessibleFromMPUEntryAddr blockInCurrentPartitionAddr false ;;
(*
    # Ecrire TRUE dans Shadow1courant[entrée MPU]->PDflag (bloc marqué comme PD dans la partition courante)
    self.helpers.set_Sh1_PDflag_from_MPU_entry_address(block_in_current_partition_address, True)*)
		(** set the block as a PD block in shadow 1*)
		writeSh1PDFlagFromMPUEntryAddr blockInCurrentPartitionAddr true ;;
(*
    # Si SCcourant[entrée MPU]->origine == (entrée MPU)->start || SC[courant[entrée MPU]->suivant == NULL alors (si le bloc n’a pas été coupé auparavant, il faut le rendre inaccessible aux ancêtres)
    if (self.helpers.get_SC_origin_from_MPU_entry_address(block_in_current_partition_address)
            == self.helpers.get_MPU_start_from_MPU_entry_address(block_in_current_partition_address))\
            and (self.helpers.get_SC_next_from_MPU_entry_address(block_in_current_partition_address) == 0):
        # Ecrire FALSE dans (ancêtres).Accessible (O(p) parait acceptable pour un createPartition, sinon besoin de stocker l’adresse du bloc dans les ancêtres)
        self.__write_accessible_to_ancestors_rec(self.current_partition, idBlock, False)*)
		(** set the block as not accessible anymore to the ancestors *)
		perform blockOrigin := readSCOriginFromMPUEntryAddr blockInCurrentPartitionAddr in
		perform blockStart := readMPUStartFromMPUEntryAddr blockInCurrentPartitionAddr in
		perform blockNext := readSCNextFromMPUEntryAddr blockInCurrentPartitionAddr in
		if beqAddr blockOrigin blockStart && beqAddr blockNext nullAddr then
			(* Block hasn't been cut previously, need to be set unaccessible for the ancestors *)
			writeAccessibleRecAux currentPart idBlock false ;;
			ret true 
		else
(*
    #
    # RET OK
    return 1*)
		ret true.
Check createPartition.
Print createPartition.

(** ** The cutMemoryBlock PIP MPU service

    The [cutMemoryBlock] system call cuts the memory block <idBlockToCut> 
		at <cutAddress> which creates a new subbblock at that address.
		Returns the new created subblock's MPU address:OK/NULL:NOK

    <<idBlockToCut>>		the block to cut
												(id = start field of an existing block)
		<<cutAddress>>			the address where to cut the <idBlockToCut> block, 
												becomes the id of the created block
*)
Definition cutMemoryBlock (idBlockToCut cutAddr : paddr) : LLI paddr :=
(*    def cutMemoryBlock(self, idBlockToCut, cutAddress):
    """Cuts the memory block <idBlockToCut> and creates a new block at <cutAddress>
    :param idBlockToCut: the block to cut
    :param cutAddress: the address where to cut the <idBlockToCut> block, becomes the id of the created block
    :return: address of the created block's MPU location:OK/0:NOK
    """*)
    (** Get the current partition (Partition Descriptor) *)
    perform currentPart := getCurPartition in
(*
    # check that there is a free slot left
    if self.helpers.get_PD_nb_free_slots(self.current_partition) <= 0:
        # no free slot, stop
        return 0  # TODO: return NULL*)
		(** Check that there is a free slot left*)
		perform nbFreeSlots := readPDNbFreeSlots currentPart in
		if leb nbFreeSlots 0 then ret nullAddr else
(*
    # find the block in the current partition's MPU structure
    block_to_cut_MPU_address= self.__find_block_in_MPU(self.current_partition, idBlockToCut)
    if block_to_cut_MPU_address == -1:
        # no block found, stop
        return 0 # TODO: return NULL*)
		(** Find the block in the current partition *)
    perform blockToCutMPUAddr := findBlockInMPU currentPart idBlockToCut in
		perform addrIsNull := compareAddrToNull	blockToCutMPUAddr in
		if addrIsNull then(** no block found, stop *) ret nullAddr else

(*
    block_to_cut_MPU_entry = self.helpers.get_MPU_entry(block_to_cut_MPU_address)
    block_to_cut_Sh1_entry = self.helpers.get_Sh1_entry_from_MPU_entry_address(block_to_cut_MPU_address)
    # check that the block is accessible + not shared
    if block_to_cut_MPU_entry[3] == False \
        or block_to_cut_Sh1_entry[0] != 0 \
        or block_to_cut_Sh1_entry[1] == True:
        # root is always 0 so an entry 0 in shared is default
        return 0 # TODO: return NULL*)
		(** Check the block to cut is accessible *)
		perform blockIsAccessible := readMPUAccessibleFromMPUEntryAddr blockToCutMPUAddr in
		if negb blockIsAccessible then (** block is inaccessible *) ret nullAddr else

		(** Check the block is not shared TODO: changed condition *)
		(* if accessible, then PDflag can't be set, we just need to check PDchild is null*)
		perform PDChildAddr := readPDChildFromMPUEntry	blockToCutMPUAddr in
		perform PDChildAddrIsNull := compareAddrToNull PDChildAddr in
		if negb PDChildAddrIsNull (*shouldn't be null*) then ret nullAddr else

(*
    # Check that the cut address lies between the start and the end address
    if cutAddress < block_to_cut_MPU_entry[1] or cutAddress > block_to_cut_MPU_entry[2]:
        # cutAddress outside bounds
        return 0  # TODO: return NULL*)
		(** Check the cut address lies between the start and the end address *)
		perform blockToCutStartAddr := readMPUStartFromMPUEntryAddr blockToCutMPUAddr in
		perform isCutAddrBelowStart := Paddr.leb cutAddr blockToCutStartAddr in
		if isCutAddrBelowStart then (**cutAddress outside bounds*) ret nullAddr else

		perform blockToCutEndAddr := readMPUEndFromMPUEntryAddr blockToCutMPUAddr in
		perform isCutAddrAboveEnd := Paddr.leb blockToCutEndAddr cutAddr in
		if isCutAddrAboveEnd then (**cutAddress outside bounds*) ret nullAddr else
(*
    # check that the new subblockS is at least 32 bytes (don't care if power of 2 because could be intermdiary)*)
		(** Check that the block is greater than the minimum MPU region size*)
		perform blockMPUentry := readMPUEntry blockToCutMPUAddr in
		perform blockSize := sizeOfBlock blockMPUentry.(mpublock) in
		perform minBlockSize := getMinBlockSize in
		perform isBlockTooSmall := Paddr.leb blockSize minBlockSize in
		if isBlockTooSmall then (** block is smaller than the minimum  *) ret nullAddr 
		else
(*
    # // Parent et ancêtres : si on coupe le bloc pour la 1ère fois, on rend ce bloc inaccessible aux ancêtres
    # Ecrire FALSE à MPU[ancêtres].accessible (O(p) car recherche dans p ancêtres, sinon besoin de stocker l’adresse du bloc dans l’ancêtre direct pour O(p))
    block_origin = self.helpers.get_SC_origin_from_MPU_entry_address(block_to_cut_MPU_address)
    if (self.helpers.get_SC_next_from_MPU_entry_address(block_to_cut_MPU_address) == 0) and \
            (block_origin == idBlockToCut):
        self.__write_accessible_to_ancestors_rec(self.current_partition, block_to_cut_MPU_entry[1], False)*)
		(** Parents and ancestors: set the block unaccessible if this is the block's first cut*)
		perform blockOrigin := readSCOriginFromMPUEntryAddr blockToCutMPUAddr in
		perform blockNext := readSCNextFromMPUEntryAddr blockToCutMPUAddr in
		writeAccessibleToAncestorsIfNoCut currentPart idBlockToCut blockToCutMPUAddr
																			blockOrigin blockNext false ;;
(*
    # // Enfant : on créé un sous-bloc dérivé du bloc initial
    # adresse MPU insertion <- insérerEntrée(idPDcourant, entrée à insérer, SC[entrée MPU courant]->origin) (insérer le nouveau bloc créé avec la même origine que le bloc initial)
    new_entry = block_to_cut_MPU_entry
    # the new entry has the same characteristics as the initial block except the start address becomes cutAddress
    new_entry[1] = cutAddress  # index 1 is start address
    new_entry_MPU_address = self.__insert_new_entry(
        self.current_partition,
        new_entry,
        block_origin
    )*)
		(** Child: create the new subblock at cutAddr and insert it in the kernel structure*)
		perform blockEndAddr := readMPUEndFromMPUEntryAddr blockToCutMPUAddr in
		perform newSubblockMPUAddr := insertNewEntry currentPart cutAddr blockEndAddr blockOrigin in

(*
    # // Modifier le bloc initial
    # modify initial block: the end address becomes (cutAddress - 1)
    self.helpers.set_MPU_end_from_MPU_entry_address(block_to_cut_MPU_address, cutAddress - 1)*)
		(** Modify initial block: the end address becomes (cutAddress - 1)*)
		writeMPUEndFromMPUEntryAddr blockToCutMPUAddr (pred cutAddr) ;;

(*
    #  // Indiquer coupe dans Shadow Cut : bloc pourrait déjà être coupé auquel cas on doit l’insérer correctement dans la liste chaînée SC
    # sous-bloc suivant <- SC[entrée MPU courant]->suivant (récupérer le pointeur vers le sous-bloc suivant, NULL si 1ère coupe ou fin de liste)
    next_subblock = self.helpers.get_SC_next_from_MPU_entry_address(block_to_cut_MPU_address)
		# Ecrire (sous-bloc suivant) à SC[adresse MPU insertion]->suivant (faire pointer le nouveau sous-bloc vers le sous-bloc suivant, NULL si 1ère coupe)
    self.helpers.set_SC_next_from_MPU_entry_address(new_entry_MPU_address, next_subblock)
		# Ecrire (adresse MPU insertion) à SC[entrée MPU courant]->suivant (faire pointer le bloc coupé vers le nouveau sous-bloc créé)
    self.helpers.set_SC_next_from_MPU_entry_address(block_to_cut_MPU_address, new_entry_MPU_address)

*)
		(** Register the cut in the Shadow Cut: insert in middle if needed*)
		perform originalNextSubblock := readSCNextFromMPUEntryAddr blockToCutMPUAddr in
		writeSCNextFromMPUEntryAddr newSubblockMPUAddr originalNextSubblock ;;
		writeSCNextFromMPUEntryAddr blockToCutMPUAddr newSubblockMPUAddr ;;
(*
    #  RET @coupe
    return new_entry_MPU_address*)
		ret newSubblockMPUAddr.

Print cutMemoryBlock.
