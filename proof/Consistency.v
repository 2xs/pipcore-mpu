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
    This file contains the formalization of the consistency properties :
for each one we summarize the description of its definition *)
Require Import Model.ADT Model.Monad Model.MAL Model.Lib Lib (*Isolation*)
StateLib.
Require Import List Coq.Logic.ProofIrrelevance.
Import List.ListNotations.

Definition wellFormedFstShadowIfBlockEntry s :=
forall pa,
isBE pa s ->
isSHE (CPaddr (pa + sh1offset)) s.

Definition wellFormedShadowCutIfBlockEntry s :=
forall pa,
isBE pa s ->
exists scentryaddr : paddr, isSCE scentryaddr s
/\ scentryaddr = CPaddr (pa + scoffset).

Definition wellFormedBlock s :=
forall block startaddr endaddr,
bentryPFlag block true s ->
bentryStartAddr block startaddr s ->
bentryEndAddr block endaddr s ->
(* startaddr inferior to endaddr + size of block greater than minimum MPU size *)
(startaddr < endaddr) /\ (Constants.minBlockSize < (endaddr - startaddr)).

Definition PDTIfPDFlag s :=
forall idPDchild sh1entryaddr,
true = StateLib.checkChild idPDchild s sh1entryaddr /\
sh1entryAddr idPDchild sh1entryaddr s ->
bentryAFlag idPDchild false s /\
bentryPFlag idPDchild true s /\
exists startaddr, bentryStartAddr idPDchild startaddr s /\
 entryPDT idPDchild startaddr s.

Definition AccessibleNoPDFlag s :=
forall block sh1entryaddr,
isBE block s ->
sh1entryAddr block sh1entryaddr s ->
bentryAFlag block true s ->
sh1entryPDflag sh1entryaddr false s.

Definition nullAddrExists s :=
isPADDR nullAddr s.

(* TODO : to remove -> consequence of freeSlotsListIsFreeSlot and FreeSlotIsBE
	-> but convenient for now so keep it *)
Definition FirstFreeSlotPointerIsBEAndFreeSlot s :=
forall pdentryaddr pdentry,
lookup pdentryaddr (memory s) beqAddr = Some (PDT pdentry) ->
pdentry.(firstfreeslot) <> nullAddr ->
isBE pdentry.(firstfreeslot) s /\
isFreeSlot pdentry.(firstfreeslot) s.

(* TODO : when removing the unecessary check in addMemoryBlock if this holds *)
Definition NbFreeSlotsISNbFreeSlotsInList s :=
forall pd nbfreeslots,
isPDT pd s ->
pdentryNbFreeSlots pd nbfreeslots s ->
exists optionfreeslotslist, optionfreeslotslist = getFreeSlotsList pd s /\
wellFormedFreeSlotsList optionfreeslotslist <> False /\ (* to get rid of false induction bound constraints *)
nbfreeslots.(i) (* nat *) = length (*(filterOption*) (optionfreeslotslist).

Definition DisjointFreeSlotsLists s :=
forall pd1 pd2,
isPDT pd1 s ->
isPDT pd2 s ->
pd1 <> pd2 ->
exists optionfreeslotslist1 optionfreeslotslist2,
optionfreeslotslist1 = getFreeSlotsList pd1 s /\
wellFormedFreeSlotsList optionfreeslotslist1 <> False /\ (* to get rid of false induction bound constraints *)
optionfreeslotslist2 = getFreeSlotsList pd2 s /\
wellFormedFreeSlotsList optionfreeslotslist2 <> False /\ (* to get rid of false induction bound constraints *)
disjoint (filterOptionPaddr (optionfreeslotslist1))(filterOptionPaddr (optionfreeslotslist2)).


Definition NoDupInFreeSlotsList s :=
forall pd pdentry,
lookup pd (memory s) beqAddr = Some (PDT pdentry) ->
exists optionfreeslotslist, optionfreeslotslist = getFreeSlotsList pd s /\
wellFormedFreeSlotsList optionfreeslotslist <> False /\ (* to get rid of false induction bound constraints *)
NoDup (filterOptionPaddr (optionfreeslotslist)).

(* TODO : state the blockindexes list constraints *)
Definition StructurePointerIsKS s :=
forall entryaddr entry,
lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
isKS entry.(structure) s.

Definition NextKSOffsetIsPADDR s :=
forall addr nextksaddr : paddr,
isKS addr s ->
nextKSAddr addr nextksaddr s ->
isPADDR nextksaddr s.

Definition NextKSIsKS s :=
forall addr nextKSaddr nextKS : paddr,
isKS addr s ->
nextKSAddr addr nextKSaddr s ->
nextKSentry nextKSaddr nextKS s ->
nextKS <> nullAddr ->
isKS nextKS s.

Definition multiplexerIsPDT s :=
isPDT multiplexer s.

Definition currentPartitionInPartitionsList s :=
In (currentPartition s) (getPartitions multiplexer s).
(*forall pdaddr,
currentPartition s = pdaddr ->
isPDT pdaddr s.*)

Definition BlocksRangeFromKernelStartIsBE s :=
forall kernelentryaddr : paddr, forall blockidx : index,
isKS kernelentryaddr s ->
blockidx < kernelStructureEntriesNb ->
isBE (CPaddr (kernelentryaddr + blockidx)) s.

Definition KernelStructureStartFromBlockEntryAddrIsKS s :=
forall (blockentryaddr : paddr) (blockidx : index),
isBE blockentryaddr s ->
bentryBlockIndex blockentryaddr blockidx s ->
isKS (CPaddr (blockentryaddr - blockidx)) s.

(* To remove if unnecessary *)
(*Definition PDchildIsPDT s :=
forall sh1entryaddr sh1entry,
lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) ->
sh1entry.(PDchild) <> nullAddr ->
isPDT sh1entry.(PDchild) s.*)

Definition sh1InChildLocationIsBE s :=
forall sh1entryaddr sh1entry,
lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) ->
sh1entry.(inChildLocation) <> nullAddr ->
isBE sh1entry.(inChildLocation) s.

Definition freeSlotsListIsFreeSlot s :=
forall pd freeslotaddr optionfreeslotslist freeslotslist,
isPDT pd s ->
optionfreeslotslist = getFreeSlotsList pd s /\
wellFormedFreeSlotsList optionfreeslotslist <> False -> (* to get rid of false induction bound constraints *)
freeslotslist = filterOptionPaddr(optionfreeslotslist) /\
In freeslotaddr freeslotslist ->
freeslotaddr <> nullAddr ->
isFreeSlot freeslotaddr s.

Definition inclFreeSlotsBlockEntries s :=
forall pd,
isPDT pd s ->
incl (getFreeSlotsList pd s) (getKSEntries pd s).


Definition DisjointKSEntries s :=
forall pd1 pd2,
isPDT pd1 s ->
isPDT pd2 s ->
pd1 <> pd2 ->
exists optionentrieslist1 optionentrieslist2,
optionentrieslist1 = getKSEntries pd1 s /\
(*wellFormedFreeSlotsList optionfreeslotslist1 <> False /\ (* to get rid of false induction bound constraints *)
*) optionentrieslist2 = getKSEntries pd2 s /\
(*wellFormedFreeSlotsList optionfreeslotslist2 <> False /\ (* to get rid of false induction bound constraints *)
*) disjoint (filterOptionPaddr (optionentrieslist1))(filterOptionPaddr (optionentrieslist2)).

(* Prove DisjointKSEntries -> DisjointFreeSlotsList because of inclusion *)

(** ** The [isChild] specifies that a given partition should be a child of the
        physical page stored as parent into the associated partition descriptor
    (11) **)
Definition isChild  s :=
forall partition parent : paddr,
In partition (getPartitions multiplexer s) ->
pdentryParent partition parent s ->
In partition (getChildren parent s).


(** ** The [isParent] specifies that if we take any child into the children list of any
partition into the partition list so this partition should be the parent of this child
 (..) **)
Definition isParent  s :=
forall partition parent : paddr,
In parent (getPartitions multiplexer s) ->
In partition (getChildren parent s) ->
pdentryParent partition parent s.

(* TODO: remove, consequence of noDupKSEntriesList*)
Definition noDupMappedBlocksList s :=
forall (partition : paddr),
isPDT partition s ->
NoDup (getMappedBlocks partition s).

Definition noDupKSEntriesList s :=
forall (partition : paddr),
isPDT partition s ->
NoDup (filterOptionPaddr (getKSEntries partition s)).

(* TODO: remove, consequence of noDupKSEntriesList*)
Definition noDupUsedPaddrList s :=
forall (partition : paddr),
isPDT partition s ->
NoDup (getUsedPaddr partition s).

Definition noDupPartitionTree s :=
NoDup (getPartitions multiplexer s) .

Definition sharedBlockPointsToChild s :=
forall parent child addr parentblock sh1entryaddr,
In parent (getPartitions multiplexer s) ->
In child (getChildren parent s) ->
In addr (getUsedPaddr child s) ->
In addr (getAllPaddrAux [parentblock] s) ->
In parentblock (getMappedBlocks parent s) ->
sh1entryAddr parentblock sh1entryaddr s ->
(sh1entryPDchild (CPaddr (parentblock + sh1offset)) child s \/
sh1entryPDflag (CPaddr (parentblock + sh1offset)) true s).

Definition accessibleChildPaddrIsAccessibleIntoParent s :=
 forall parent child addr,
In parent (getPartitions multiplexer s) ->
In child (getChildren parent s) ->
In addr (getAccessibleMappedPaddr child s) ->
In addr (getAccessibleMappedPaddr parent s).

(** ** First batch of consistency properties *)
Definition consistency1 s :=
nullAddrExists s /\
wellFormedFstShadowIfBlockEntry s /\
PDTIfPDFlag s /\
AccessibleNoPDFlag s /\
FirstFreeSlotPointerIsBEAndFreeSlot s /\
multiplexerIsPDT s /\
currentPartitionInPartitionsList s /\
wellFormedShadowCutIfBlockEntry s /\
BlocksRangeFromKernelStartIsBE s /\
KernelStructureStartFromBlockEntryAddrIsKS s /\
sh1InChildLocationIsBE s /\
StructurePointerIsKS s /\
NextKSIsKS s /\
NextKSOffsetIsPADDR s /\
NoDupInFreeSlotsList s /\
freeSlotsListIsFreeSlot s /\
DisjointFreeSlotsLists s /\
inclFreeSlotsBlockEntries s /\
DisjointKSEntries s /\
noDupPartitionTree s /\
isParent s /\
isChild s /\
noDupKSEntriesList s /\
noDupMappedBlocksList s /\
wellFormedBlock s.

(** ** Second batch of consistency properties *)
Definition consistency2 s :=
noDupUsedPaddrList s /\
accessibleChildPaddrIsAccessibleIntoParent s /\
sharedBlockPointsToChild s.

(** ** Conjunction of all consistency properties *)
Definition consistency s :=
consistency1 s /\ consistency2 s.
