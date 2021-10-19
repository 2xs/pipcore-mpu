(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2021)                *)
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
(*Definition succ (n : index): option index:=
let isucc := n + 1 in
match lt_dec isucc tableSize with
| left x =>
    Some {| i := isucc; Hi := MALInternal.Index.succ_obligation_1 n x |}
| right _ => None
end.*)

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
if (lt_dec res maxIdx) then
Some (Build_index res _ )
else  None.

Program Definition subPaddrIdx (n : paddr) (m : index)  : option paddr := 
let res := n-m in
if (lt_dec res maxAddr )
then
Some (Build_paddr res _ )
else  None.

Program Definition addPaddrIdx (n : paddr) (m : index)  : option paddr := 
let res := n+m in
if (lt_dec res maxAddr )
then
Some (Build_paddr res _ )
else  None.

End Paddr.

Definition is32Aligned (a : paddr) : bool := a/32=?0.

Definition monadToValue {A : Type} (p : LLI A) s : option A :=
match p s with
	| val (n,s') => Some n
	| undef _ _ => None
	end.

(*Module Page. 
Definition eqb (p1 : page)  (p2 : page) : bool := (p1 =? p2).
End Page.*)

(*Module Level. 
Definition gtb (a b : level) : bool := b <? a .
Definition eqb (a b : level) : bool:= a =? b.
Program Definition pred (n : level) : option level := 
if gt_dec n 0 then
let ipred := n-1 in 
Some (Build_level ipred _ )
else  None.
Next Obligation.
destruct n.
simpl.
lia.
Qed.
End Level. 

Module VAddr.
Definition eqbList(vaddr1 : vaddr) (vaddr2 : vaddr) : bool :=
 beqVAddr vaddr1 vaddr2.
End VAddr.*)

(** The [getCurPartition] function returns the current partition descriptor of a given state *)
(*Definition getCurPartition s : paddr :=
currentPartition s. *)

(** The [getMaxIndex] function returns the last position into a page table *) 
(*Definition getMaxIndex : option index:=
match gt_dec tableSize 0 with
| left x =>
    Some
      {|
      i := tableSize - 1;
      Hi := MAL.getMaxIndex_obligation_1 x |}
| right _ => None 
end. 

(** The [readPhysical] function returns the physical page stored into a given 
    page at a given position in physical memory. The table should contain only Physical pages 
    (The type [PP] is already defined into [Model.ADT]) *)
Definition readPhysical (paddr : page) (idx : index) memory: option page :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PP a) => Some a
  | _ => None
 end.*)
(** The [readPhysical] function returns the physical page stored into a given 
    page at a given position in physical memory. The table should contain only Physical pages 
    (The type [PP] is already defined into [Model.ADT]) *)
Definition readPDTable (paddr : paddr) memory: option PDTable :=
let entry :=  lookup paddr memory beqAddr  in 
  match entry with
  | Some (PDT a) => Some a
  | _ => None
 end.


(*
(**  The [getPd] function returns the physical page of the page directory of
     a given partition  *)
Definition getPd partition memory: option page:= 
match Index.succ PDidx with 
|None => None
|Some idx => readPhysical partition idx memory
end. *)

(**  The [getPd] function returns the physical page of the page directory of
     a given partition  *)
Definition getPd (pa : paddr) s : option PDTable :=
monadToValue(MAL.readPDTable pa) s.

(*
(**  The [getFstShadow] returns the physical page of the first shadow page of
     a given partition  *)
Definition getFstShadow partition memory: option page:= 
match Index.succ sh1idx with 
|None => None
|Some idx => readPhysical partition idx memory
end. 

(**  The [getSndShadow] returns the physical page of the second shadow page  of
     a given partition *)
Definition getSndShadow partition memory: option page:= 
match Index.succ sh2idx with 
|None => None
|Some idx => readPhysical partition idx memory
end. 

(**  The [getConfigTablesLinkedList] returns the physical address of the indirection tables
 reverse translation of a given partition  *)
Definition getConfigTablesLinkedList partition memory: option page:= 
match Index.succ sh3idx with 
|None => None
|Some idx => readPhysical partition idx memory
end. 

(** The [readPDflag] function returns the flag value stored into a given table 
    at a given position in memory. The table should contain only virtual entries 
    (The type [VE] is already defined in [Model.ADT])  *)
Definition readPDflag  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (VE a) => Some a.(pd)
  | Some _ => None
  | None => None
 end.

(** The [getNbLevel] function returns the number of translation levels of the MMU *) 
Definition getNbLevel : option level:=
match gt_dec nbLevel 0 with
| left x =>
    Some {| l := nbLevel - 1; Hl := MAL.getNbLevel_obligation_1 x |}
| right _ => None
end.

(** The [readPresent] function returns the flag value stored into a given table 
    at a given position in memory. The table should contain only Physical entries 
    (The type [PE] is already defined in [Model.ADT]) *)
Definition readPresent  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PE a) => Some a.(present)
  | Some _ => None
  | None => None
 end. *)
(** The [readPresent] function returns the flag value stored into a given table 
    at a given position in memory. The table should contain only Physical entries 
    (The type [PE] is already defined in [Model.ADT]) *)
Definition getBlockIndex  (paddr : paddr) s : option index:=
monadToValue(readBlockIndexFromBlockEntryAddr paddr) s.

Definition getSh1EntryAddr (paddr : paddr) s : option ADT.paddr:=
monadToValue(getSh1EntryAddrFromBlockEntryAddr paddr) s.



(*
(** The [readAccessible] function returns the flag value stored into a given table 
    at a given position in memory. The table should contain only Physical entries 
    (The type [PE] is already defined in [Model.ADT]) *)
Definition readAccessible  (paddr : page) (idx : index) memory : option bool:=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PE a) => Some a.(user)
  | Some _ => None
  | None => None
 end. 

Definition getIndexOfAddr (va : vaddr) (l : level) : index:=
nth ((length va) - (l + 2))  va defaultIndex .

(** The [checkVAddrsEqualityWOOffset] function compares two given virtual addresses 
    without taking into account the last index *)
Fixpoint checkVAddrsEqualityWOOffset (timeout : nat) (va1 va2 : vaddr) (l : level) := 
match timeout with 
|0 => true
|S timeout1 =>  
let idx1 := getIndexOfAddr va1 l in
 let idx2 := getIndexOfAddr va2 l in
if Level.eqb l fstLevel 
then
      (idx1 =? idx2) 
    else 
      match Level.pred l with 
      | Some levelpred =>  if idx1 =? idx2 
                              then checkVAddrsEqualityWOOffset timeout1 va1 va2 levelpred
                              else false
      | _ => true
      end
end. 

(** The [readPhyEntry] function returns the physical page stored into a given table 
    at a given position in memory. The table should contain only Physical entries 
    (The type [PE] is already defined in [Model.ADT]) *)
Definition readPhyEntry(paddr : page) (idx : index) memory: option page :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (PE a) => Some a.(pa)
  | Some _ => None
  | None => None
 end. 

(** The [readIndex] function returns the index stored into a given table 
    at a given position in memory. The table should contain only indices 
    (The type [I] is already defined in [Model.ADT]) *)
Definition readIndex  (paddr : page) (idx : index) memory : option index :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (I indexValue) => Some indexValue
  | Some _ => None
  | None => None
 end. 
 
 (** The [readVirtual] function returns the virtual address strored into a given table 
    at a given position in memory. The table should contain a virtual address at this position 
    (The type [VA] is already defined in [Model.ADT]) *)
Definition readVirtual (paddr : page) (idx : index) memory : option vaddr :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (VA addr) => Some addr
  | Some _ => None
  | None => None
 end. *)
 (** The [readVirtual] function returns the virtual address strored into a given table 
    at a given position in memory. The table should contain a virtual address at this position 
    (The type [VA] is already defined in [Model.ADT]) *)
(*Definition readPDTable (paddr : paddr) memory : option paddr :=
perform s := get in
(let entry := lookup paddr0 memory beqAddr in
 match entry with
 | Some (PDT a) => ret a
 | None => undefined 4 -> on perd les codes d'erreur
 | _ => undefined 5
 end)


let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (VA addr) => Some addr
  | Some _ => None
  | None => None
 end. *)

(*

(** The [readVirEntry] function returns the virtual address strored into a given table 
    at a given position in memory. The table should contain a VEntry at this position 
    (The type [VEntry] is already defined in [Model.ADT]) *)
Definition readVirEntry (paddr : page) (idx : index) memory : option vaddr :=
let entry :=  lookup paddr idx memory beqPage beqIndex  in 
  match entry with
  | Some (VE addr) => Some (va addr)
  | Some _ => None
  | None => None
 end. 
 
(** The [getDefaultPage] function returns the value of the default page *)
Definition getDefaultPage := defaultPage.

(** The [getIndirection] function returns the configuration table entry that corresponds 
    to the given level and virtual address *)
Fixpoint  getIndirection (pd : page) (va : vaddr) (currentlevel : level) (stop : nat) s :=
match stop with 
|0 => Some pd 
|S stop1 => 
if (Level.eqb currentlevel fstLevel)  
then Some pd 
  else  
    let idx :=  getIndexOfAddr va currentlevel in 
       match readPhyEntry pd idx s.(memory) with 
       | Some addr =>  if  defaultPage =? addr 
                          then Some defaultPage 
                          else 
                            match Level.pred currentlevel with
                            |Some p =>  getIndirection addr va p stop1 s
                            |None => None
                            end
      |None => None
    end
   end. 

Inductive optionPage : Type:= 
|SomePage : page -> optionPage
|SomeDefault :  optionPage
|NonePage : optionPage
.*)
Inductive optionPaddr : Type:= 
|SomePaddr : paddr -> optionPaddr
|NonePaddr : optionPaddr
.

(*

(** The [getMappedPage] function returns the physical page stored into a leaf node, 
   which corresponds to a given virtual address, if the present flag is equal to true **)
Definition getMappedPage pd s va: optionPage  :=
match getNbLevel  with 
 |None => NonePage
 |Some level => let idxVA := getIndexOfAddr va fstLevel  in 
               match getIndirection pd va level (nbLevel - 1) s with 
                | Some tbl =>  if defaultPage =? tbl
                                   then NonePage 
                                   else match (readPresent tbl idxVA s.(memory)) with 
                                         | Some false => SomeDefault
                                         |Some true => match readPhyEntry tbl idxVA s.(memory)  with 
                                                       | Some a => SomePage a
                                                       | _ => NonePage
                                                       end
                                         |_ => NonePage
                                         end
                | _ => NonePage
               end
end.*)
(** The [getMappedPage] function returns the physical page stored into a leaf node, 
   which corresponds to a given virtual address, if the present flag is equal to true **)
Definition getMappedBlock pa s: option BlockEntry :=
match monadToValue(readBlockPresentFromBlockEntryAddr pa ) s with 
| Some false => None
|	Some true => monadToValue(readBlockEntryFromBlockEntryAddr pa) s
| _ => None
end.

(*

(** The [getVirtualAddressSh2] function returns the virtual address stored into the 
    second shadow structure which corresponds to a given virtual address **)
Definition getVirtualAddressSh2 sh2 s va: option vaddr :=
match getNbLevel  with 
 |None => None
 |Some level => let idxVA := getIndexOfAddr va fstLevel  in 
               match getIndirection sh2 va level (nbLevel - 1) s with 
                | Some tbl =>  if defaultPage =? tbl
                                   then None 
                                   else readVirtual tbl idxVA s.(memory) 
                | _ => None
               end
end.

(** The [getVirtualAddressSh2] function returns the virtual address stored into the 
    parent **)
Definition getVAInParent partition s va: option vaddr :=
match getSndShadow partition (memory s) with 
|Some sh2 => match getVirtualAddressSh2 sh2 s va with 
             | Some vainparent =>  if (VAddr.eqbList defaultVAddr vainparent) 
                                     then None 
                                     else Some vainparent
             | _ => None
             end
| _ => None
end. 

(** The [getVirtualAddressSh1] function returns the virtual address stored into the first
   shadow structure which corresponds to a given virtual address **)
Definition getVirtualAddressSh1 sh1 s va: option vaddr :=
match getNbLevel  with 
 |None => None
 |Some level => let idxVA := getIndexOfAddr va fstLevel  in 
               match getIndirection sh1 va level (nbLevel - 1) s with 
                | Some tbl =>  if defaultPage =? tbl
                                   then None 
                                   else readVirEntry tbl idxVA s.(memory) 
                | _ => None
               end
end.

(** The [getAccessibleMappedPage] function returns the physical page stored into a leaf node, 
   which corresponds to a given virtual address, if the present and user flags are equal to true **)
Definition getAccessibleMappedPage pd s va: optionPage :=
match getNbLevel  with 
 |None => NonePage
 |Some level =>let idxVA := getIndexOfAddr va fstLevel  in 
               match getIndirection pd va level (nbLevel - 1) s with 
                | Some tbl => if defaultPage =? tbl
                                   then NonePage 
                                   else  match (readPresent tbl idxVA s.(memory)),
                                                   (readAccessible tbl idxVA s.(memory)) with 
                                           |Some true, Some true => match readPhyEntry tbl idxVA s.(memory)  with 
                                                       | Some a => SomePage a
                                                       | _ => NonePage
                                                       end
                                           | _, _ =>  NonePage 
                                          end
                | _ => NonePage
               end
end.

(** The [geTrdShadows] returns physical pages used to keep informations about 
    configuration pages 
*)
Fixpoint getLLPages (sh3 : page) s bound :=
match bound with 
|0 => []
|S bound1 => match getMaxIndex with 
            |None => []
            |Some maxindex =>  match readPhysical sh3 maxindex s.(memory) with 
                                |None => [sh3]
                                |Some addr => if addr =? defaultPage then [sh3] else sh3 :: getLLPages addr s bound1
                               end
           end
end.
*)
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




(*
(** The [getTablePages] function returns the list of physical pages stored into 
    a given configuration table from a given index *)
Fixpoint getTablePages (table : page ) (idx : nat) s : list page := 
match idx with 
| 0 => []
|S idx1 => match  lookup table (CIndex idx1) s.(memory) beqPage beqIndex  with 
              | Some (PE entry) => if (pa entry =? defaultPage ) then getTablePages table idx1 s
                                      else getTablePages table idx1 s ++ [pa entry] 
              | _ => getTablePages table idx1 s
            end
end.

Fixpoint getIndirectionsAux (pa : page) (s : state) level {struct level} : list page :=
  match level with
    | O => []
    | S level1 => pa :: flat_map (fun p => getIndirectionsAux p s level1) 
                                    (getTablePages pa tableSize s)
  end.

(** The [getIndirectionsAux] function returns the list of physical pages 
    used into a configuration tables tree *)
Definition getIndirections pd s : list page :=
  getIndirectionsAux pd s nbLevel.

Fixpoint getAllIndicesAux (pos count: nat) : list index :=
  match count with
    | 0        => []
    | S count1 => match lt_dec pos tableSize with
                   | left pf => Build_index pos pf :: getAllIndicesAux (S pos) count1
                   | _       => []
                 end
  end.

(** The [getAllIndicesAux] function returns the list of all indices  *)
Definition getAllIndices := getAllIndicesAux 0 tableSize.

Fixpoint getAllVAddrAux (levels: nat) : list (list index) :=
  match levels with
    | 0         => [[]]
    | S levels1 => let alls := getAllVAddrAux levels1 in
                  flat_map (fun (idx : index) => map (cons idx) alls) getAllIndices
  end.

(** The [getAllVAddr] function returns the list of all virtual addresses *)
Definition getAllVAddr :=map CVaddr (getAllVAddrAux (S nbLevel)).

Definition checkOffset0 (va : vaddr) :bool :=
if ( nth nbLevel va  defaultIndex  =? CIndex 0 ) then true else false .

Definition getAllVAddrWithOffset0 :=filter checkOffset0 getAllVAddr.
*)

(*Fixpoint getAllPAddrAux (count: nat) (currKernelStructure: paddr) : list (list paddr) :=
	match count with
	| 0 => []
	| S count1 => 
  match levels with
    | 0         => [[]]
    | S levels1 => let alls := getAllVAddrAux levels1 in
                  flat_map (fun (idx : index) => map (cons idx) alls) getAllIndices
  end.*)


(** The [getPdsVAddr] function returns the list of virtual addresses used as 
    partition descriptor into a given partition *)
Definition getPDsPAddr (partition : paddr) (paList : list paddr) s :=
filter (checkChild partition s) paList.

(** The [getMappedPagesOption] function Return all physical pages marked as 
    present into a partition *)
(*Definition getMappedPagesOption (pd : page) (vaList : list vaddr) s : list optionPage :=
map (getMappedPage pd s) vaList.

(** The [getAccessibleMappedPagesOption] function Return all physical pages 
    marked as present and accessible into a partition *)
Definition getAccessibleMappedPagesOption (pd : page) (vaList : list vaddr) s : list optionPage :=
map (getAccessibleMappedPage pd s) vaList.

(** The [filterOption] function Remove option type from list *)
Fixpoint filterOption (l : list (optionPage)) := 
match l with 
| [] => []
| SomePage a :: l1 => a:: filterOption l1
| _ :: l1 => filterOption l1
end.
*)

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
(** The [getMappedPages] function Returns all present pages of a given partition *)
Definition getMappedBlocks (partition : paddr) s : list paddr :=
  match getPd partition s.(memory) with
    |None => []
    |Some pd => let vaList := getAllVAddrWithOffset0 in getMappedPagesAux pd vaList s
  end.*)
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

(*
Lemma  eqPageDec : forall n m : page, {n = m} + {n <> m}.
Proof.
intros.
destruct n. destruct m.
assert ({p = p0} + {p <> p0}).
apply eq_nat_dec.
destruct H.
left.
subst.
assert(Hp = Hp0) by apply proof_irrelevance.
subst.
trivial.
right.
unfold not in *.
intros. apply n.
clear n.
inversion H. trivial.
Qed.
*)
(*
(** The [getChildren] function Returns all children of a given partition *)
Definition getChildren (partition : page) s := 
let vaList := getAllVAddrWithOffset0 in 
match getNbLevel, getPd partition s.(memory) with 
|Some l1,Some pd => getMappedPagesAux pd (getPdsVAddr partition l1 vaList s) s
|_, _ => []
end.

*)

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


(*
(** The [getParent] function returns the parent partition descriptor of a given partition *)
Definition getParent partition memory :=
match Index.succ PPRidx with 
| Some idx =>  readPhysical partition idx memory
| _ => None 
end.

(** The [getAncestorsAux] function returns the ancestors list of a given partition *)
Fixpoint getAncestorsAux (partition : page) memory depth : list page := 
match depth with 
|0 => [] 
| S depth1 => match getParent partition memory with 
               | Some parent => parent :: getAncestorsAux parent memory depth1
               | _ => []
              end
end.

(** The [getAncestors] function fixes the sufficient timeout value to retrieve all ancestors *)
Definition getAncestors (partition : page) s := 
getAncestorsAux partition s.(memory) (nbPage+1). 

(** Propositions *)
*)
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
Definition pdentryPDStructurePointer entryaddr structurepointer s:= 
match lookup entryaddr s.(memory) beqAddr with 
| Some (PDT entry) => structurepointer =  entry.(structure) /\ isBE structurepointer s
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

(*
(** The [isPE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isPE table idx s: Prop := 
match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (PE _) => True
             |_ => False
end. 

(** The [isVE] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [VE] *)
Definition isVE table idx s: Prop := 
 match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (VE _) => True
             |_ => False
end.

(** The [isVA] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [VA] *)
Definition isVA table idx s: Prop := 
 match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (VA _) => True
             |_ => False
end.

(** The [isPP] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] *)
Definition isPP table idx s: Prop := 
 match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (PP _) => True
             |_ => False
end.

(** The [isPP'] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PP] and physical page stored into this entry 
    is equal to a given physical page [pg]*)
Definition isPP' table idx pg s: Prop := 
 match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (PP p) => p = pg
             |_ => False
end.


(** The [nextEntryIsPP] proposition reutrns True if the entry at position [idx+1]
    into the given physical page [table] is type of [PP] and physical page stored into 
    this entry is equal to a given physical page [pg] *)
Definition nextEntryIsPP table idxroot tableroot s : Prop:= 
match Index.succ idxroot with 
| Some idxsucc => match lookup table idxsucc (memory s) beqPage beqIndex with 
                  | Some (PP table) => tableroot = table
                  |_ => False 
                  end
| _ => False 
end.

(** The [entryPresentFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [PP] and the present flag stored into 
    this entry is equal to a given flag [flag] *)
Definition entryPresentFlag table idx flag s:= 
match lookup table idx s.(memory) beqPage beqIndex with 
| Some (PE entry) => flag =  entry.(present)
| _ => False
end. 

(** The [entryPDFlag]  proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the pd flag stored into 
    this entry is equal to a given flag [flag] *)
Definition entryPDFlag table idx flag s:= 
match lookup table idx s.(memory) beqPage beqIndex with 
| Some (VE entry) => flag =  entry.(pd)
| _ => False
end. *)

Definition bentryBlockIndex (*paddr*) blockentryaddr index s:= 
match lookup blockentryaddr s.(memory) beqAddr with 
| Some (BE entry) => index =  entry.(blockindex) /\ (index < kernelStructureEntriesNb)
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

(** The [entryUserFlag] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the user flag stored into 
    this entry is equal to a given flag [flag] *)
Definition entryUserFlag table idx flag s:= 
match lookup table idx s.(memory) beqPage beqIndex with 
| Some (PE entry) => flag =  entry.(user)
| _ => False
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


(*
(** The [VEDerivation] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the given boolean value 
    [res] specifies if the virtual address stored into  
    this entry is equal or not to the default virtual address *)
Definition VEDerivation table idx (res : bool) s:= 
match lookup table idx s.(memory) beqPage beqIndex with 
| Some (VE entry) => ~ (beqVAddr entry.(va) defaultVAddr) = res
| _ => False
end. 

(** The [isEntryVA] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VE] and the virtual address
    stored into this entry is equal to a given virtual address [v1] *)
Definition isEntryVA table idx v1 s:=
 match lookup table idx (memory s) beqPage beqIndex with 
 | Some (VE entry)  => entry.(va) = v1
 | _ => False
 end.

(** The [isVA'] proposition reutrns True if the entry at position [idx]
    into the given physical page [table] is type of [VA] and the virtual address
    stored into this entry is equal to a given virtual address [v1] *)
Definition isVA' table idx v1 s:=
 match lookup table idx (memory s) beqPage beqIndex with 
 | Some (VA entry)  => entry = v1
 | _ => False
 end.

(** The [isVAUser] specifies the value of v1 *)
Definition isVAUser table idx v1 s:=
 match lookup table idx (memory s) beqPage beqIndex with 
 | Some (VA entry)  => entry = v1
 | _ => defaultVAddr = v1
 end.

(** The [isEntryPage] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [PE] and physical page stored into this entry 
    is equal to a given physical page [page1]*)
Definition isEntryPage table idx page1 s:=
 match lookup table idx (memory s) beqPage beqIndex with 
 | Some (PE entry)  => entry.(pa) = page1
 | _ => False
 end.

(** The [isIndexValue] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [I] and the index stored into this memory location 
    is equal to a given index value [vindex]*)
Definition isIndexValue table idx vindex s:=
 match lookup table idx (memory s) beqPage beqIndex with 
 | Some (I value)  =>  value = vindex
 | _ => False
 end.
 
(** The [isI] proposition reutrns True if the entry at position [idx]
    into the given page [table] is type of [I] *)
Definition isI table idx s: Prop := 
match lookup table idx s.(memory) beqPage beqIndex with 
             |Some (I _) => True
             |_ => False
end. 



(** The [getTableAddrRoot'] proposition returns True if the given physical page [table]
is a configuration table into different structures (pd, shadow1 or shadow2). This table should be associated to the 
given virtual address [va]  *)
Definition getTableAddrRoot' (table : page) (idxroot : index) 
(currentPart : page) (va : vaddr) (s : state) : Prop :=
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx) /\
(forall tableroot : page,
 nextEntryIsPP currentPart idxroot tableroot s ->
 exists nbL : level,
   Some nbL = getNbLevel /\
   (exists stop : nat, stop > 0 /\ stop <= nbL /\ getIndirection tableroot va nbL stop s = Some table)).

(** The [getTableAddrRoot] proposition returns True if the given physical page [table]
is the last page table into a structure (pd, shadow1 or shadow2) that corresponds to a given virtual address [va] *)
Definition getTableAddrRoot table idxroot currentPart va s : Prop :=
(idxroot = PDidx \/ idxroot = sh1idx \/ idxroot = sh2idx)/\
   forall (tableroot : page), nextEntryIsPP  currentPart idxroot tableroot s ->  
   exists nbL, Some nbL = getNbLevel  /\ exists (stop :nat) , stop = nbL+1  /\ 
    getIndirection tableroot va nbL stop s = Some table . 

(** The [getAllPages] returns the list of all physical pages *)
Definition getAllPages: list page:= 
map CPage (seq 0 nbPage ).

(** The [getPDFlag] checks if the given virtual address corresponds to a partition
    descriptor **)
Definition getPDFlag sh1 va s :=
let idxVA := getIndexOfAddr va fstLevel in
match getNbLevel with
|Some nbL =>  match getIndirection sh1 va nbL (nbLevel - 1) s with
  | Some tbl =>
      if tbl =? defaultPage
      then false
      else
       match readPDflag tbl idxVA (memory s) with
       | Some true => true
       | Some false => false
       | None => false
       end
  | None => false
  end
| None => false
end.*)

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

(*

(** The [isAccessibleMappedPageInParent] function returns true if the given physical
    page is accessible in the parent of the given partition **)
Definition isAccessibleMappedPageInParent partition va accessiblePage s  :=
match getSndShadow partition (memory s) with 
| Some sh2 => 
  match  getVirtualAddressSh2 sh2 s va  with 
   | Some vaInParent => 
     match getParent partition (memory s) with 
      | Some parent => 
        match getPd parent (memory s) with 
         | Some pdParent => 
           match getAccessibleMappedPage pdParent s vaInParent with 
            | SomePage sameAccessiblePage => accessiblePage =? sameAccessiblePage
            | _ => false
           end
         | None => false
        end
    | None => false
           end
| None => false
           end
| None => false
end.

(** The [isPartitionFalse] returns true if the partition descriptor flag of a given
     entry is equal to false or there is no data stored into this entry **)  
Definition isPartitionFalse ptPDChildSh1 idxPDChild s :=
readPDflag ptPDChildSh1 idxPDChild (memory s) = Some false \/
readPDflag ptPDChildSh1 idxPDChild (memory s) = None.

(** The [isAncestor] funtion returns true if the given partitions are equal 
    or the descParent partition is an ancestor of currentPart **)
Definition isAncestor  currentPart descParent s :=
( currentPart = descParent \/ In descParent (getAncestors currentPart s)).

Definition isWellFormedFstShadow nbL table  s:= 
(nbL <> fstLevel /\ 
(forall idx, readPhyEntry table  idx s.(memory) = Some defaultPage /\ 
readPresent table idx (memory s) = Some false )) \/ 
(nbL = fstLevel /\ 
( forall idx : index, 
(readVirEntry table idx (memory s) = Some defaultVAddr) /\ 
readPDflag table idx (memory s) = Some false) ).

Definition isWellFormedSndShadow nbL table  s:= 
(nbL <> fstLevel /\ (
forall idx, readPhyEntry table  idx s.(memory) = Some defaultPage /\ 
readPresent table idx (memory s) = Some false )) \/ 
(nbL = fstLevel /\ ( forall idx : index, 
(readVirtual table idx (memory s) = Some defaultVAddr) ) ).

(** The [isDerived] funtion returns true if a physical page is derived 
    into the given partition , this physical page is associated to the given 
    virtual address [va] **)
Definition isDerived partition va  s  :=
match getFstShadow partition (memory s) with 
| Some sh1 => 
  match  getVirtualAddressSh1 sh1 s va  with 
   | Some va0 => beqVAddr defaultVAddr va0 = false
   | _ => False
  end
| None => False
end.

Lemma  pageDec :
forall x y : page, {x = y} + {x <> y}.
Proof.
intros.
destruct x; destruct y.
assert({p = p0} + {p <> p0}).
apply Nat.eq_dec.
destruct H.
left.
subst.
f_equal.
apply proof_irrelevance.
right.
contradict n.
inversion n.
subst;trivial.
Qed.

Fixpoint closestAncestorAux part1 part2 s bound : option page :=
match bound  with
| 0 => None
| S bound1 => match getParent part1 (memory s) with
              | Some parent => match in_dec pageDec part2 
                                    (getPartitionAux parent s (nbPage+1)) with 
                               | left _  => Some parent
                               | _ =>  closestAncestorAux parent part2 s bound1
                               end 
              | None =>  Some multiplexer 
              end 
end.

Definition closestAncestor part1 part2 s := 
closestAncestorAux part1 part2 s (nbPage+1).
*)

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

