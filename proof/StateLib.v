(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2023)                *)
(*  Copyright (C) 2020-2023 Orange                                             *)
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
Definition leb (a b : index) : bool := a <=? b.
Definition ltb (a b : index) : bool := a <? b.
Definition eqb (a b : index) : bool := a =? b.
Program Definition succ (n : index): option index:=
if lt_dec n maxIdx then
let isucc := n + 1 in
Some (Build_index isucc _ )
else None.
Next Obligation.
destruct n.
simpl in *.
lia.
Qed.

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
Definition leb (a b : paddr) : bool := a <=? b.
Definition ltb (a b : paddr) : bool := a <? b.
Definition eqb (a b : paddr) : bool := a =? b.

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

Inductive optionPaddr : Type:= 
|SomePaddr : paddr -> optionPaddr
|NonePaddr : optionPaddr
.

Fixpoint getAllPaddrBlockAux (pos offset count: nat) : list paddr :=
  match count with
    | 0        => []
    | S count1 => match le_dec (pos+offset) maxAddr with
                   | left pf => Build_paddr (pos+offset) pf :: getAllPaddrBlockAux (S pos) offset count1
                   | _       => []
                 end
  end.

(** The [getAllIndicesAux] function returns the list of all indices  *)
Definition getAllPaddrBlock (startaddr endaddr : paddr) : list paddr :=
getAllPaddrBlockAux 0 startaddr (endaddr-startaddr).

Fixpoint getAllPaddrAux (blocklist : list paddr) (s : state) :=
match blocklist with
| [] => []
| block::list1 => match lookup block (memory s) beqAddr with
									| Some (BE bentry) => getAllPaddrBlock bentry.(blockrange).(startAddr)
																													bentry.(blockrange).(endAddr) ++
																				getAllPaddrAux list1 s
									| _ => getAllPaddrAux list1 s
									end
end.

Definition checkChild (blockentryaddr : paddr) (s : state) (sh1entryaddr : paddr) : bool :=
match lookup blockentryaddr s.(memory) beqAddr  with
| Some (BE entry) => match lookup sh1entryaddr s.(memory) beqAddr  with
										| Some (SHE sh1entry) => sh1entry.(PDflag)
										|	_ => false
										end
|	_ => false
end.

Definition childFilter (s : state) (blockentryaddr : paddr) : bool :=
match lookup blockentryaddr s.(memory) beqAddr  with
| Some (BE entry) => let sh1entryaddr := Paddr.addPaddrIdx blockentryaddr sh1offset in
											match sh1entryaddr with
											| Some p =>	match lookup p s.(memory) beqAddr  with
																	| Some (SHE sh1entry) => sh1entry.(PDflag)
																	|	_ => false
																	end
											|	_ => (* NOK *) false
											end
|	_ => false
end.

Definition getPDsPaddr (paList : list paddr) s :=
map (fun bentryaddr => match lookup bentryaddr (memory s) beqAddr with
												| Some (BE bentry) => bentry.(blockrange).(startAddr)
												| _ => nullAddr
											end
		) paList.

(** The [getPdsVAddr] function returns the list of virtual addresses used as
    partition descriptor into a given partition *)
Definition getPDs (paList : list paddr) s :=
getPDsPaddr (filter (childFilter s) paList) s.


(** The [filterOption] function removes the option type from the list and filters
		out all	unreachable paddr.
		As we use the MAL functions, these paddr aren't accessible by Pip anyways in
		its operations.
TODO check explanation*)
Fixpoint filterOptionPaddr (l : list optionPaddr) := 
match l with 
| [] => []
| SomePaddr a :: l1 => a :: filterOptionPaddr l1
| _ :: l1 => filterOptionPaddr l1
end.

Fixpoint getConfigBlocksAux (bound : nat) (currKernelStructure: paddr) s (maxStructNbleft : index) : list optionPaddr :=
match bound with
|	0 => (* NOK *) [NonePaddr]
| S bound1 => (* Recursion on each KS *)
							if Index.ltb maxStructNbleft zero (*<? -> == OK*)
							then (* NOK, unreachable, should have stopped at NULL if end of list *)
									[NonePaddr]
							else
									match lookup currKernelStructure (memory s) beqAddr with
									| Some (BE kernelstructure) =>
												let nextkernelstructureoffset := Paddr.addPaddrIdx currKernelStructure nextoffset in
												match nextkernelstructureoffset with
												| Some p =>
														match lookup p s.(memory) beqAddr with
														| Some (PADDR addr) => 	match Index.pred maxStructNbleft with
													          								|Some p => [SomePaddr currKernelStructure]++(getConfigBlocksAux bound1 addr s p)
																										|None => [NonePaddr]
																										end

														|	_ => (* NOK *) [NonePaddr]
														end
												|	_ => (* NOK *) [NonePaddr]
												end
									| Some (PADDR null) => if beqAddr null nullAddr
																					then (* OK, end of list *)
																								[]
																					else [NonePaddr]
									|	_ => (* Wrong entry type, trying to access unexpected entry *)
													[NonePaddr]
									end
end.

Definition getConfigBlocks (partition : paddr) (s : state) : list paddr :=
match lookup partition s.(memory) beqAddr with
| Some (PDT pdentry) => (filterOptionPaddr (getConfigBlocksAux (maxIdx+1) pdentry.(structure) s (CIndex maxNbPrepare)))
| _ => []
end.


Fixpoint getAllPaddrConfigAux (kslist : list paddr) (s : state) :=
match kslist with
| [] => []
| ks::list1 => match lookup ks (memory s) beqAddr with
									| Some (BE bentry) => getAllPaddrBlockAux 0
																														ks
																														(ks + Constants.kernelStructureTotalLength) ++
																				getAllPaddrConfigAux list1 s
									| _ => getAllPaddrConfigAux list1 s
									end
end.

Fixpoint getAllPaddrPDTAux (pdtlist : list paddr) (s : state) :=
match pdtlist with
| [] => []
| pd::list1 => match lookup pd (memory s) beqAddr with
									| Some (PDT bentry) => getAllPaddrBlockAux 0
																														pd
																														(pd + Constants.PDStructureTotalLength) ++
																					getAllPaddrPDTAux list1 s
									| _ => getAllPaddrPDTAux list1 s
									end
end.

Definition getConfigPaddr (partition : paddr) (s : state) : list paddr :=
let ksList := getConfigBlocks partition s in
getAllPaddrPDTAux [partition] s ++ getAllPaddrConfigAux ksList s.

Fixpoint getKSEntriesInStructAux (bound : nat) (currKernelStructure: paddr) (s : state) (iterleft : index) : list optionPaddr :=
match bound with
|	0 => (* NOK *) [NonePaddr]
| S bound1 => (* Recursion on each KS entry *)
					if Index.ltb iterleft zero (*<? -> == OK*)
						then (* NOK, unreachable, should have stopped at NULL if end of list *)
									[NonePaddr]
						else
							let blockentryaddr := Paddr.addPaddrIdx currKernelStructure iterleft in
							match blockentryaddr with
							| Some addr =>
								match lookup addr s.(memory) beqAddr with
								| Some (BE entry) =>	if beqIdx iterleft zero
																			then [SomePaddr addr]
																			else
																				match Index.pred iterleft with
												                |Some p =>  SomePaddr addr :: getKSEntriesInStructAux bound1 currKernelStructure s p
												                |None => [NonePaddr]
																				end
								|_ => (* Wrong entry type, trying to access unexpected entry *)
											[NonePaddr]
		         		end
							|_ => (* Wrong entry type, trying to access unexpected entry *)
											[NonePaddr]
			       	end
end.

Fixpoint getKSEntriesAux (bound : nat) (currKernelStructure: paddr) s : list optionPaddr :=
match bound with
|	0 => (* NOK *) [NonePaddr]
| S bound1 => (* Recursion on each KS *)
				let blocks := (getKSEntriesInStructAux	(maxIdx+1)	currKernelStructure
																s  (CIndex (kernelStructureEntriesNb-1))) in
				let nextkernelstructureoffset := Paddr.addPaddrIdx currKernelStructure nextoffset in
				match nextkernelstructureoffset with
				| Some p =>
						match lookup p s.(memory) beqAddr with
						| Some (PADDR addr) => 	match lookup addr (memory s) beqAddr with
												| Some (BE nextkernelstructure) => blocks ++ (getKSEntriesAux bound1 addr s)
												| Some (PADDR null) => if beqAddr addr nullAddr
																		then (* OK, end of list *) blocks
																		else (* NOK *) [NonePaddr]
												|	_ => (* Wrong entry type, trying to access unexpected entry *)
														[NonePaddr]
												end
						|	_ => (* NOK *) [NonePaddr]
						end
				|	_ => (* NOK *) [NonePaddr]
				end
end.

Definition getKSEntries (partition: paddr) s :=
  match lookup partition s.(memory) beqAddr with
  | Some (PDT pdentry) => (* get all entries from all kernel structures for this pd *)
													(* filtering the list enables to reuse the same list somewhere else *)
							if beqAddr pdentry.(structure) nullAddr
							then []
							else (getKSEntriesAux maxNbPrepare pdentry.(structure) s)
  | _ => []
  end.

(* only the BE interests us, the other types that modify the state do not change the list *)
Fixpoint filterPresent (l : list paddr) (s : state):= 
match l with 
| [] => []
| blockaddr :: l1 => match lookup blockaddr (memory s) beqAddr with
											| Some (BE blockentry) => if blockentry.(present)
																								then blockaddr :: filterPresent l1 s
																								else filterPresent l1 s
											| _ => filterPresent l1 s
											end
end.

Definition getMappedBlocks (partition : paddr) (s : state) : list paddr :=
(* get all entries from all kernel structures for this pd *)
(* filtering the list in the last step enables to reuse the same list somewhere else *)
filterPresent (filterOptionPaddr (getKSEntries partition s)) s.

(** The [getMappedPages] function Returns all present pages of a given partition *)
Definition getMappedPaddr (partition : paddr) s : list paddr :=
let blockList := getMappedBlocks partition s in
getAllPaddrAux blockList s.

Fixpoint filterAccessible (l : list paddr) (s : state):= 
match l with 
| [] => []
| blockaddr :: l1 => match lookup blockaddr (memory s) beqAddr with
											| Some (BE blockentry) => if blockentry.(accessible)
																								then blockaddr :: filterAccessible l1 s
																								else filterAccessible l1 s
											| _ => filterAccessible l1 s
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

(** The [getMappedPages] function Returns all present pages of a given partition *)
Definition getAccessibleMappedPaddr (partition : paddr) s : list paddr :=
let blockList := getAccessibleMappedBlocks partition s in
getAllPaddrAux blockList s.

(** The [getMappedPages] function Returns all present pages of a given partition *)
Definition getUsedPaddr (partition : paddr) s : list paddr :=
let ksList := getConfigPaddr partition s in
let mappedblockList := getMappedPaddr partition s in
ksList ++ mappedblockList.

(** The [getChildren] function Returns all children of a given partition *)
Definition getChildren (partition : paddr) s :=
	let entry :=  lookup partition s.(memory) beqAddr in
  match entry with
  | Some (PDT a) => getPDs (getMappedBlocks partition s) s
	|_ => []
end.

(** The [geTrdShadows] returns physical pages used to keep informations about
    configuration pages
*)
Definition getFreeSlotsListAux bound FuncAux (blockentryaddr : paddr) s (nbfreeslotsleft : index) : list optionPaddr:=
match bound with
|0 => (* NOK *) [NonePaddr]
|S bound1 => if Index.ltb nbfreeslotsleft zero (*<? -> == OK*)
						then (* NOK, unreachable, should have stopped at NULL if end of list *)[NonePaddr]
						else
							match lookup blockentryaddr s.(memory) beqAddr with
							| Some (BE entry) =>	match Index.pred nbfreeslotsleft with
								                    |Some p =>  SomePaddr blockentryaddr :: FuncAux bound1 entry.(blockrange).(endAddr) s p
								                    |None => [NonePaddr]
								                    end
							| Some (PADDR entry) => if beqAddr blockentryaddr nullAddr
																			then (* OK, end of list *) []
																			else (* NOK, only acceptable PADDR is NULL *) [NonePaddr]
		          |_ => (* Wrong entry type, trying to access unexpected entry *) [NonePaddr]
		         end
end.

Fixpoint getFreeSlotsListRec (bound : nat) (blockentryaddr : paddr) s (nbfreeslotsleft : index) {struct bound} := getFreeSlotsListAux bound getFreeSlotsListRec blockentryaddr s nbfreeslotsleft.

Definition getFreeSlotsList (partition : paddr) s :=
  match lookup partition s.(memory) beqAddr with
  | Some (PDT pdentry) => if beqAddr pdentry.(firstfreeslot) nullAddr
													then []
													else getFreeSlotsListRec (maxIdx+1) pdentry.(firstfreeslot) s pdentry.(nbfreeslots)
																(* as nbfreeslots is of type index, it must be < maxIdx, so case 0 never reached*)
	|_ => []
end.

Fixpoint wellFormedFreeSlotsList (l : list optionPaddr) :=
match l with
| [] => True
| SomePaddr entryaddr :: l1 => wellFormedFreeSlotsList l1
| _ => (* undef because of recursion *) False
end.

Lemma FreeSlotsListRec_unroll :
forall blockentryaddr s bound nbfreeslotsleft, getFreeSlotsListRec bound blockentryaddr s nbfreeslotsleft = getFreeSlotsListAux bound getFreeSlotsListRec blockentryaddr s nbfreeslotsleft.
destruct bound; simpl;reflexivity.
Qed.

Fixpoint getPartitionsAux (bound : nat)  (partitionRoot : paddr) (s : state) {struct bound} :=
match bound with
|	0 => (* end of fuel *) []
| S bound1 =>  [partitionRoot] ++ flat_map (fun p => getPartitionsAux bound1 p s) 
																										(getChildren partitionRoot s )
end.

(** The [getPartitions] function fixes the sufficient timeout value to retrieve all partitions *)
Definition getPartitions (root : paddr) (s : state) : list paddr  :=
getPartitionsAux (maxAddr+2) root s.

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
             |Some (BE bentry) => bentry.(blockindex) = zero
             |_ => False
end.

(*DUP*)
(** The [isSHE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isFreeSlot paddr s: Prop :=
match lookup paddr s.(memory) beqAddr with 
|Some (BE entry) => match lookup (CPaddr (paddr + sh1offset)) s.(memory) beqAddr with
									 	|Some (SHE sh1entry) =>
												match lookup (CPaddr (paddr + scoffset)) s.(memory) beqAddr with 
												|Some (SCE scentry) => entry.(blockrange).(startAddr) = nullAddr /\
																							entry.(read) = false /\
																							entry.(write) = false /\
																							entry.(exec) = false /\
																							entry.(present) = false /\
																							entry.(accessible) = false /\
																							(* no cycles for same slot by general consistency property on chained free slots*)
																							sh1entry.(PDchild) = nullAddr /\ sh1entry.(PDflag) = false /\ sh1entry.(inChildLocation) = nullAddr /\
																							scentry.(origin) = nullAddr /\ scentry.(next) = nullAddr
									 			|_ => False
												end
										|_ => False
										end
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
| Some (BE entry) => index =  entry.(blockindex)
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
Definition pdentryVidt entryaddr vidtblock s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (PDT entry) => vidtblock = entry.(vidtAddr)
| _ => False
end.

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into
    this entry is equal to a given flag [flag] *)
Definition pdentryParent entryaddr parent s:=
match lookup entryaddr s.(memory) beqAddr with
| Some (PDT entry) => parent =  entry.(ADT.parent)
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
| Some (BE entry) => nextKSaddr =  CPaddr (paddr + nextoffset)
| _ => False
end.

Definition nextKSentry nextKSaddr nextKS s:=
match lookup nextKSaddr s.(memory) beqAddr with
| Some (PADDR entry) => nextKS =  entry
| _ => False
end.

Definition getNullAddr s :=
lookup nullAddr (memory s) beqAddr.

Ltac symmetrynot :=
match goal with
| [ |- ?x <> ?y ] => unfold not ; let Hk := fresh in intro Hk ; symmetry in Hk ;contradict Hk
end.