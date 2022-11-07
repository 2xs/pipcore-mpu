(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2022)                *)
(*  Copyright (C) 2020-2022 Orange                                             *)
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
    This file contains required functions to define properties about a given state *)
Require Import Model.ADT Model.Monad Model.Lib Model.MAL.

Require Import ProofIrrelevance Coq.Program.Equality Arith List Lia Bool.
Import List.ListNotations.

Module Index.
Definition geb (a b : index) : bool := b <=? a.
Definition leb (a b : index) : bool := a <=? b.
Definition ltb (a b : index) : bool := a <? b.
Definition gtb (a b : index) : bool := b <? a.
Definition eqb (a b : index) : bool := a =? b.
Definition succ (n : index): option index:=
let isucc := n + 1 in
match le_dec isucc maxIdx with
| left x =>
    Some {| i := isucc; Hi := MALInternal.Index.succ_obligation_1 n x |}
| right _ => None
end.

Program Definition pred (n : index) : option index :=
if gt_dec n 0 then
let ipred := n-1 in
Some (Build_index ipred _ )
else  None.
Next Obligation.
destruct n.
simpl.
lia.
Qed.

End Index.

(* DUP *)
Module Paddr.
Definition geb (a b : paddr) : bool := b <=? a.
Definition leb (a b : paddr) : bool := a <=? b.
Definition ltb (a b : paddr) : bool := a <? b.
Definition gtb (a b : paddr) : bool := b <? a.
Definition eqb (a b : paddr) : bool := a =? b.
(*Definition succ (n : index): option index:=
let isucc := n + 1 in
match lt_dec isucc tableSize with
| left x =>
    Some {| i := isucc; Hi := MALInternal.Index.succ_obligation_1 n x |}
| right _ => None
end.*)

Program Definition pred (n : paddr) : option paddr :=
if gt_dec n 0 then
let pred := n-1 in
Some (Build_paddr pred _ )
else  None.
Next Obligation.
destruct n.
simpl.
lia.
Qed.

Program Definition subPaddr (a b : paddr)  : option index :=
let res := a-b in
if (le_dec res maxIdx) then
Some (Build_index res _ )
else  None.

Program Definition subPaddrIdx (n : paddr) (m : index)  : option paddr :=
let res := n-m in
if (le_dec res maxAddr )
then
Some (Build_paddr res _ )
else  None.

Program Definition addPaddrIdx (n : paddr) (m : index)  : option paddr :=
let res := n+m in
if (le_dec res maxAddr )
then
Some (Build_paddr res _ )
else  None.

End Paddr.

Definition is32Aligned (a : paddr) : bool := a/32=?0.

Definition entryExists (blockentryaddr : paddr) memory : bool :=
let entry :=  lookup blockentryaddr memory beqAddr  in
  match entry with
  | Some (BE a) => true
  | _ => false
 end.

Definition blockInRAM (blockentryaddr : paddr) s : bool :=
match lookup blockentryaddr s.(memory) beqAddr with
| Some (BE a) => ((RAMStartAddr <=? a.(blockrange).(startAddr)) &&
											(a.(blockrange).(endAddr) <=?	RAMEndAddr))
| _ => false
end.

Definition isBlockInRAM (blockentryaddr : paddr) (isInRAM : bool) s : Prop :=
match lookup blockentryaddr s.(memory) beqAddr with
| Some (BE a) => isInRAM = ((RAMStartAddr <=? a.(blockrange).(startAddr)) &&
											(a.(blockrange).(endAddr) <=?	RAMEndAddr))
| _ => False
end.

Definition monadToValue {A : Type} (p : LLI A) s : option A :=
match p s with
	| val (n,s') => Some n
	| undef _ _ => None
	end.

(** The [getCurPartition] function returns the current partition descriptor of a given state *)
(*Definition getCurPartition s : paddr :=
currentPartition s. *)

(** The [readPhysical] function returns the physical page stored into a given 
    page at a given position in physical memory. The table should contain only Physical pages 
    (The type [PP] is already defined into [Model.ADT]) *)
Definition readPDTable (paddr : paddr) memory: option PDTable :=
let entry :=  lookup paddr memory beqAddr  in 
  match entry with
  | Some (PDT a) => Some a
  | _ => None
 end.



(**  The [getPd] function returns the physical page of the page directory of
     a given partition  *)
Definition getPd (pa : paddr) s : option PDTable :=
monadToValue(MAL.readPDTable pa) s.


(** The [readPresent] function returns the flag value stored into a given table
    at a given position in memory. The table should contain only Physical entries
    (The type [PE] is already defined in [Model.ADT]) *)
Definition getBlockIndex  (paddr : paddr) s : option index:=
monadToValue(readBlockIndexFromBlockEntryAddr paddr) s.

Definition getSh1EntryAddr (paddr : paddr) s : option ADT.paddr:=
monadToValue(getSh1EntryAddrFromBlockEntryAddr paddr) s.



Inductive optionPaddr : Type:=
|SomePaddr : paddr -> optionPaddr
|NonePaddr : optionPaddr
.


(** The [checkChild] function returns true if the given physical address corresponds
    to a child of the given partition
    *)
(*Definition checkChild (partition : paddr) (s : state) (paddr : paddr) : bool :=
	match (readSh1PDFlagFromBlockEntryAddr paddr) s with
	| val _ => true
	| undef _ _ => false
	end.*)


(*Definition checkChild (partition : paddr) (s : state) (sh1entryaddr : paddr) : bool :=
(*if nullAddr =? sh1entryaddr then false
else 	*) match lookup sh1entryaddr s.(memory) beqAddr  with
				| Some (SHE sh1entry) => sh1entry.(PDflag)
				|	_ => false
				end.*)
(*	else 	match lookup paddr s.(memory) beqAddr  with
				| Some (BE entry) => match lookup entry.(blockrange).(startAddr) s.(memory) beqAddr with
															| Some (SHE sh1entry) => sh1entry.(PDflag)
															| _ => false
															end
				|	_ => false
				end.*)
	(*match monadToValue (readSh1PDFlagFromBlockEntryAddr paddr) s with
	| Some true => true
	| Some false => false
	| None => false
	end.
*)

Definition checkChild (blockentryaddr : paddr) (s : state) (sh1entryaddr : paddr) : bool :=
match lookup blockentryaddr s.(memory) beqAddr  with
				| Some (BE entry) => match lookup sh1entryaddr s.(memory) beqAddr  with
														| Some (SHE sh1entry) => sh1entry.(PDflag)
														|	_ => false
														end

				|	_ => false
				end.

(** The [getPdsVAddr] function returns the list of virtual addresses used as
    partition descriptor into a given partition *)
Definition getPDsPAddr (partition : paddr) (paList : list paddr) s :=
filter (checkChild partition s) paList.

(** The [filterOption] function removes the option type from the list and filters
		out all	unreachable paddr.
		As we use the MAL functions, these paddr aren't accessible by Pip anyways in
		its operations.
TODO check explanation*)
Fixpoint filterOption (l : list optionPaddr) :=
match l with
| [] => []
| SomePaddr a :: l1 => a :: filterOption l1
| _ :: l1 => filterOption l1
end.

(*
(** The [getMappedPagesAux] function removes option type from mapped pages list *)
Definition getMappedPagesAux (pd :page)  (vaList : list vaddr) s : list page  :=
filterOption (getMappedPagesOption pd vaList s).*)

(** The [getAccessibleMappedPagesAux] function removes option type from
    accessible mapped pages list *)
(*Definition getAccessibleMappedPagesAux (pd :page)  (vaList : list vaddr) s : list page :=
filterOption (getAccessibleMappedPagesOption pd vaList s).*)

(** The [getTablePages] function returns the list of physical pages stored into
    a given configuration table from a given index *)
Fixpoint getConfigBlocksAux (count : nat) (currKernelStructure : paddr) (s : state) : list optionPaddr :=
match count with
| O => []
| S n => match currKernelStructure with
				| Build_paddr 0 _ => []
				|	_ => 	let nextkernelstructure := monadToValue(readNextFromKernelStructureStart
																									currKernelStructure) s in
								match nextkernelstructure with
								| Some p => [SomePaddr currKernelStructure] ++ (getConfigBlocksAux n p s)
								| None => [NonePaddr]
								end
				end
end.

(*
Definition getAccessibleMappedPagesAux (pd :page)  (vaList : list vaddr) s : list page :=
filterOption (getAccessibleMappedPagesOption pd vaList s).*)

(** The [getConfigPagesAux] function returns all configuration pages of a
    given partition *)
Definition getConfigBlocks (partition : paddr) (s : state) : list paddr :=
	(*let entry := lookup partition s.(memory) beqAddr in
	match entry with
	| Some (PDT a) => *)let firstKernelStructure := monadToValue(
																										readPDStructurePointer partition) s in
										match firstKernelStructure with
										| Some p =>	[partition] ++ filterOption (getConfigBlocksAux maxNbPrepare p s)
										| None => []
										end
	(*| _ => []
	end*).

(*Definition getConfigBlocks (partition : paddr) (s : state) : list paddr :=
partition :: (getConfigBlocks partition s).*)


Fixpoint getOriginalBlocksInKSInStructNoDupAux (currIdx : nat) (currKernelStructure: paddr) s : list optionPaddr :=
match currIdx with
| 0 => []
|	S n => 	match monadToValue(getBlockEntryAddrFromKernelStructureStart
																						currKernelStructure
																						(CIndex currIdx)) s with
					| Some entryaddr =>	match monadToValue(readBlockPresentFromBlockEntryAddr entryaddr) s with
															| Some isPresent =>	if isPresent
																								then (* just keep one original block, taking the last elment in the subblock chain*)
																										match monadToValue(readSCNextFromBlockEntryAddr entryaddr) s with
																										| Some nextSubblock =>	if beqAddr nextSubblock nullAddr
																																						then (* retrieve the original block's start address *)
																																									match monadToValue(readBlockStartFromBlockEntryAddr entryaddr) s with
																																									| Some startAddr =>  [SomePaddr startAddr] ++ (getOriginalBlocksInKSInStructNoDupAux n currKernelStructure s)
																																									| _ => (* not existing or undef *) [NonePaddr]
																																									end
																																						else (getOriginalBlocksInKSInStructNoDupAux n currKernelStructure s)
																											| _ => (* not existing or undef *) [NonePaddr]
																												end
																											else (getOriginalBlocksInKSInStructNoDupAux n currKernelStructure s)
															| _ => (* not existing or undef *) [NonePaddr]
															end
					| _ => (* not existing or undef *) [NonePaddr]
					end
end.


Fixpoint getOriginalBlocksInKSAux (count : nat) (currKernelStructure: paddr) s : list optionPaddr :=
match count with
| O => []
| S n => (* Recursion on each KS *)
					match currKernelStructure with
					| Build_paddr 0 _ => []
					|	_ => 	let blocks := (getOriginalBlocksInKSInStructNoDupAux 	kernelStructureEntriesNb
																															currKernelStructure) s in
									match monadToValue(readNextFromKernelStructureStart
																										currKernelStructure) s with
									| Some nextkernelstructure  => (getOriginalBlocksInKSAux n nextkernelstructure s) ++ blocks
									| _ => (* not existing or undef *) [NonePaddr]
									end
					end
end.


(** The [getMappedPages] function Returns all present pages of a given partition *)
Definition getOriginalBlocks (partition : paddr) (s : state) : list paddr :=
	let entry :=  lookup partition s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => filterOption (getOriginalBlocksInKSAux maxNbPrepare partition s)
  | _ => []
  end.


(** The [getMappedPages] function Returns all present pages of a given partition that are not config blocks*)
Definition getMappedBlocks (partition : paddr) (s : state) : list paddr :=
	let entry :=  lookup partition s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => (*(* substract the KS blocks from all original blocks:
										the new list only has blocks that are present and cut or shared
										but not Ks structures *)
										let presentblocks := getPresentBlocks partition s in
										let configblocks := getConfigBlocks partition s in
										filter (fun p => existsb (beqAddr p) (presentblocks)) configblocks*)
										(* get all original blocks, the rest are subblocks*)
										getOriginalBlocks partition s
  | _ => []
  end.


(*
Fixpoint getAccessibleMappedBlocksInKSInStructAux (currIdx : nat) (currKernelStructure: paddr) s : list optionPaddr :=
match currIdx with
| 0 => match monadToValue(getBlockEntryAddrFromKernelStructureStart
																						currKernelStructure
																						(CIndex currIdx)) s with
			| Some entryaddr => [SomePaddr entryaddr]
			| _ => (* not existing or undef *) [NonePaddr]
			end
|	S n =>  match monadToValue(getBlockEntryAddrFromKernelStructureStart
																						currKernelStructure
																						(CIndex currIdx)) s with
					| Some entryaddr => [SomePaddr entryaddr] ++ getAccessibleBlocksInKSInStructAux n currKernelStructure s

	match monadToValue(readBlockAccessibleFromBlockEntryAddr entryaddr) s with
															| Some isAccessible => if isAccessible
																									then
																									else getAccessibleBlocksInKSInStructAux n currKernelStructure s
															| _ => (* not existing or undef *) [NonePaddr]
															end
					| _ => (* not existing or undef *) [NonePaddr]
					end
end.


Fixpoint getAccessibleMappedBlocksInKSAux (count : nat) (currKernelStructure: paddr) s : list optionPaddr :=
match count with
| O => []
| S n => match currKernelStructure with
					| Build_paddr 0 _ => []
					|	_ => let blocks := (getAccessibleBlocksInKSInStructAux 	kernelStructureEntriesNb
																																		currKernelStructure) s in
								match monadToValue(readNextFromKernelStructureStart
																									currKernelStructure) s with
								| Some nextkernelstructure => (getAccessibleBlocksInKSAux n nextkernelstructure s) ++ blocks
								| _ => (* not existing or undef *) [NonePaddr]
								end
				end
end.*)

Fixpoint filterAccessible (l : list paddr) (s : state) :=
match l with
| [] => []
| entryaddr :: l1 => match monadToValue(readBlockAccessibleFromBlockEntryAddr entryaddr) s with
										| Some isAccessible => 	if isAccessible
																						then entryaddr :: filterAccessible l1 s
																						else filterAccessible l1 s
										| _ => (* not existing or undef *) filterAccessible l1 s
										end
end.


(** The [getAccessibleMappedPages] function Returns all present and
    accessible pages of a given partition *)
Definition getAccessibleMappedBlocks (partition : paddr) s : list paddr :=
	let entry :=  lookup partition s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => filterAccessible (getMappedBlocks partition s) s
  | _ => []
  end.

Fixpoint getPresentBlocksInKSInStructAux (currIdx : nat) (currKernelStructure: paddr) s : list optionPaddr :=
match currIdx with
| 0 => match monadToValue(getBlockEntryAddrFromKernelStructureStart
																						currKernelStructure
																						(CIndex currIdx)) s with
			| Some entryaddr => [SomePaddr entryaddr]
			| _ => (* not existing or undef *) [NonePaddr]
			end
|	S n => 	match monadToValue(getBlockEntryAddrFromKernelStructureStart
																						currKernelStructure
																						(CIndex currIdx)) s with
					| Some entryaddr =>	match monadToValue(readBlockPresentFromBlockEntryAddr entryaddr) s with
															| Some isPresent =>	if isPresent
																									then [SomePaddr entryaddr] ++ (getPresentBlocksInKSInStructAux n currKernelStructure s)
																									else (getPresentBlocksInKSInStructAux n currKernelStructure s)
															| _ => (* not existing or undef *) [NonePaddr]
															end
					| _ => (* not existing or undef *) [NonePaddr]
					end
end.



Fixpoint getPresentBlocksInKSAux (count : nat) (currKernelStructure: paddr) s : list optionPaddr :=
match count with
| O => []
| S n =>
					match currKernelStructure with
					| Build_paddr 0 _ => []
					|	_ => 	let blocks := (getPresentBlocksInKSInStructAux 	kernelStructureEntriesNb
																																	currKernelStructure) s in
									match monadToValue(readNextFromKernelStructureStart
																										currKernelStructure) s with
									| Some nextkernelstructure => blocks ++
																								(getPresentBlocksInKSAux n nextkernelstructure s)
									| _ => (* not existing or undef *) [NonePaddr]
									end
					end
end.




(** The [getMappedBlocksAux] function removes option type from mapped blocks list *)
(*Definition getMappedBlocksAux (pd :page)  (vaList : list vaddr) s : list paddr  :=
filterOption (getMappedBlocksOption pd vaList s).*)

(** The [getMappedPages] function Returns all present pages of a given partition *)
Definition getPresentBlocks (partition : paddr) (s : state) : list paddr :=
	let entry :=  lookup partition s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => filterOption (getPresentBlocksInKSAux maxNbPrepare partition s)
  | _ => []
  end.


(** The [getAccessibleMappedPages] function Returns all present and
>>>>>>> Stashed changes
    accessible pages of a given partition *)
Definition getAccessibleBlocks (partition : paddr) s : list paddr :=
	let entry :=  lookup partition s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => filterAccessible (getPresentBlocks partition s) s
  | _ => []
  end.

(** The [getUsedPages] function Returns all used pages (present and config pages)
    of a given partition including the partition descriptor itself *)
Definition getUsedBlocks (partition: paddr) s : list paddr :=
  getConfigBlocks partition s ++ getMappedBlocks partition s.


(** The [getChildren] function Returns all children of a given partition *)
Definition getChildren (partition : paddr) s :=
	let entry :=  lookup partition s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => getPDsPAddr partition (getPresentBlocks partition s) s
	|_ => []
end.

(*
(** The [getPartitionsAux] function returns all pages marked as descriptor partition *)
Fixpoint getPartitionAux (partitionRoot : page) (s : state) bound {struct bound} : list page :=
  match bound with
    | O => []
    | S bound1 => partitionRoot :: flat_map (fun p => getPartitionAux p s bound1)
                                    (getChildren partitionRoot s )
  end.

(** The [getPartitions] function fixes the sufficient timeout value to retrieve all partitions *)
Definition getPartitions (root : page) s : list page  :=
(getPartitionAux root s (nbPage+1)).

*)

(** The [getPartitionsAux] function returns all pages marked as descriptor partition *)
Fixpoint getPartitionAux (partitionRoot : paddr) (s : state) bound {struct bound} : list paddr :=
  match bound with
    | O => []
    | S bound1 => partitionRoot :: flat_map (fun p => getPartitionAux p s bound1)
                                    (getChildren partitionRoot s )
  end.

(** The [getPartitions] function fixes the sufficient timeout value to retrieve all partitions *)
Definition getPartitions (root : paddr) s : list paddr  :=
(getPartitionAux root s (maxAddr+1)).


(** Propositions *)
(** The [isPE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isBE paddr s: Prop :=
match lookup paddr s.(memory) beqAddr with
             |Some (BE _) => True
             |_ => False
end.

(*DUP*)
(** The [isSHE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isSHE paddr s: Prop :=
match lookup paddr s.(memory) beqAddr with
             |Some (SHE _) => True
             |_ => False
end.

(*DUP*)
(** The [isSCE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isSCE paddr s: Prop :=
match lookup paddr s.(memory) beqAddr with
             |Some (SCE _) => True
             |_ => False
end.

(*DUP*)
(** The [isSHE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isPDT paddr s: Prop :=
match lookup paddr s.(memory) beqAddr with
             |Some (PDT _) => True
             |_ => False
end.

(*DUP*)
(** The [isSHE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isPADDR paddr s: Prop :=
match lookup paddr s.(memory) beqAddr with
             |Some (PADDR _) => True
             |_ => False
end.

(*DUP*)
(** The [isSHE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
(* isKS is not distinguishable by the match but onmly constructed after some specific instructions
		like readNextFromKernelStructureStart *)
Definition isKS paddr s: Prop :=
match lookup paddr s.(memory) beqAddr with
             |Some (BE _) => True
             |_ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryRFlag entryaddr flag s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (BE entry) => flag =  entry.(read)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryWFlag entryaddr flag s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (BE entry) => flag =  entry.(write)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryXFlag entryaddr flag s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (BE entry) => flag =  entry.(exec)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryStartAddr entryaddr start s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (BE entry) => start =  entry.(blockrange).(startAddr)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryEndAddr entryaddr endaddr s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (BE entry) => endaddr =  entry.(blockrange).(endAddr)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryBlockIndex (*paddr*) blockentryaddr index s:=
match lookup blockentryaddr s.(memory) beqAddr with
| Some (BE entry) => index =  entry.(blockindex) /\ (index < kernelStructureEntriesNb)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition entryBE entryaddr be s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (BE entry) => be = entry
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition pdentryFirstFreeSlot entryaddr firstfreeslotaddr s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (PDT entry) => firstfreeslotaddr =  entry.(firstfreeslot)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition pdentryNbFreeSlots entryaddr nbFreeSlots s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (PDT entry) => nbFreeSlots =  entry.(nbfreeslots)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition pdentryNbPrepare entryaddr nbPrepare s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (PDT entry) => nbPrepare =  entry.(nbprepare)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition pdentryStructurePointer entryaddr structurepointer s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (PDT entry) => structurepointer =  entry.(structure) (*/\ isBE structurepointer s*)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition pdentryMPU entryaddr mpu s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (PDT entry) => mpu =  entry.(MPU)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition pdentryMPUblock entryaddr index mpublock s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (PDT entry) => mpublock =  readElementAt index entry.(MPU) nullAddr
| _ => False
end.



(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition entryPDT entryaddr pd s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (BE entry) => match lookup entry.(blockrange).(startAddr) s.(memory) beqAddr with
										| Some (PDT pdentry) => pd =  entry.(blockrange).(startAddr)
										| _ => False
										end
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition scentryOrigin scentryaddr scorigin s:=
match lookup scentryaddr s.(memory) beqAddr with
| Some (SCE entry) => scorigin =  entry.(origin)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition scentryNext scentryaddr scnext s:=
match lookup scentryaddr s.(memory) beqAddr with
| Some (SCE entry) => scnext =  entry.(next)
| _ => False
end.



(*let sh1entryaddr := monadToValue(getSh1EntryAddrFromBlockEntryAddr paddr) in
match sh1entryaddr s with
| Some p => match lookup p s.(memory) beqAddr with
| Some (SHE entry) => flag =  entry.(PDflag)
| _ => False
end
| None => False
end.*)

(*
=======
end.
>>>>>>> Stashed changes

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryXFlag entryaddr flag s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (BE entry) => flag =  entry.(exec)
| _ => False
<<<<<<< Updated upstream
end. *)


(* DUP *)
(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryAFlag paddr flag s:=
match lookup paddr s.(memory) beqAddr with
| Some (BE entry) => flag =  entry.(accessible)
| _ => False
end.

(* DUP *)
(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition bentryPFlag paddr flag s:=
match lookup paddr s.(memory) beqAddr with
| Some (BE entry) => flag =  entry.(present)
| _ => False
end.

(* DUP *)
(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition sh1entryAddr paddr sh1entryaddr s:=
match lookup paddr s.(memory) beqAddr with
| Some (BE entry) => sh1entryaddr =  CPaddr (paddr + sh1offset)
| _ => False
end.

(** The [entryPDFlag]  proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the pd flag stored into
    this entry is equal to a given flag [flag] *)
Definition sh1entryPDflag (*paddr*) sh1entryaddr flag s:=
match lookup sh1entryaddr s.(memory) beqAddr with
| Some (SHE entry) => flag =  entry.(PDflag)
| _ => False
end.

(** The [entryPDFlag]  proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the pd flag stored into
    this entry is equal to a given flag [flag] *)
Definition sh1entryPDchild (*paddr*) sh1entryaddr pdchild s:=
match lookup sh1entryaddr s.(memory) beqAddr with
| Some (SHE entry) => pdchild =  entry.(PDchild)
| _ => False
end.


(** The [entryPDFlag]  proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the pd flag stored into
    this entry is equal to a given flag [flag] *)
Definition sh1entryInChildLocation (*paddr*) sh1entryaddr inchildlocation s:=
match lookup sh1entryaddr s.(memory) beqAddr with
| Some (SHE entry) => inchildlocation =  entry.(inChildLocation)
											/\ (inchildlocation <> nullAddr -> isBE inchildlocation s)
| _ => False
end.


(* DUP *)
(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition scentryAddr paddr scentryaddr s:=
match lookup paddr s.(memory) beqAddr with
| Some (BE entry) => scentryaddr =  CPaddr (paddr + scoffset)
| _ => False
end.

(* DUP *)
(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition nextKSAddr paddr nextKSaddr s:=
match lookup paddr s.(memory) beqAddr with
| Some (PADDR entry) => nextKSaddr =  entry
| _ => False
end.

(** The [getPDFlag] checks if the given virtual address corresponds to a partition
    descriptor **)
Definition getPDFlag pa s :=
match monadToValue( readSh1PDFlagFromBlockEntryAddr pa ) s with
       | Some true => true
       | Some false => false
       | None => false
end.

(** The [getPDFlag] checks if the given virtual address corresponds to a partition
    descriptor **)
Definition getNullAddr s :=
lookup nullAddr (memory s) beqAddr.

Ltac symmetrynot :=
match goal with
| [ |- ?x <> ?y ] => unfold not ; let Hk := fresh in intro Hk ; symmetry in Hk ;contradict Hk
end.

Definition issubblock (subblock block : paddr) (s : state) : bool :=
	match monadToValue (readBlockEntryFromBlockEntryAddr block) s with
	| Some b => match monadToValue (readBlockEntryFromBlockEntryAddr subblock) s with
							| Some sb =>
													match monadToValue(MALInternal.Paddr.leb b.(blockrange).(startAddr) sb.(blockrange).(startAddr)) s, monadToValue(MALInternal.Paddr.leb sb.(blockrange).(endAddr) b.(blockrange).(endAddr)) s with
													| Some above, Some below => if (above && below)
																										then (* sb is a subblock of b *) true
																										else false
													| _, _ => false
													end
							| None => false
							end
	| None => false
	end.

Definition checkissubblock (subblock block : paddr) (s : state) : Prop :=
	match monadToValue (readBlockEntryFromBlockEntryAddr block) s with
	| Some b => match monadToValue (readBlockEntryFromBlockEntryAddr subblock) s with
							| Some sb =>
													match monadToValue(MALInternal.Paddr.leb b.(blockrange).(startAddr) sb.(blockrange).(startAddr)) s, monadToValue(MALInternal.Paddr.leb sb.(blockrange).(endAddr) b.(blockrange).(endAddr)) s with
													| Some above, Some below => if (above && below)
																										then (* sb is a subblock of b *) True
																										else False
													| _, _ => False
													end
							| None => True
							end
	| None => True
	end.


