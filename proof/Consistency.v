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

Definition PDTIfPDFlag s :=
(*forall idPDchild sh1entryaddr,
true = StateLib.checkChild idPDchild s sh1entryaddr ->
(exists entry, lookup idPDchild s.(memory) beqAddr = Some (BE entry)
/\ entryPDT idPDchild entry.(blockrange).(startAddr) s).*)
forall idPDchild sh1entryaddr,
true = StateLib.checkChild idPDchild s sh1entryaddr /\
sh1entryAddr idPDchild sh1entryaddr s ->
bentryAFlag idPDchild false s /\
bentryPFlag idPDchild true s /\
exists startaddr, bentryStartAddr idPDchild startaddr s /\
 entryPDT idPDchild startaddr s.

Definition nullAddrExists s :=
(*forall n,
getNullAddr s = Some n.*)
isPADDR nullAddr s.

(* TODO : to remove -> consequence of freeSlotsListIsFreeSlot and FreeSlotIsBE
	-> but convenient for know so keep it *)
Definition FirstFreeSlotPointerIsBEAndFreeSlot s :=
forall pdentryaddr pdentry,
lookup pdentryaddr (memory s) beqAddr = Some (PDT pdentry) ->
pdentry.(firstfreeslot) <> nullAddr ->
isBE pdentry.(firstfreeslot) s /\
(*exists slotentry, lookup entry.(firstfreeslot) s.(memory) beqAddr = Some (BE slotentry) /\*)
isFreeSlot pdentry.(firstfreeslot) s.

(*Definition FirstFreeSlotPointerNotNullEq s :=
(*forall pdinsertion currnbfreeslots,
pdentryNbFreeSlots pdinsertion currnbfreeslots s /\ currnbfreeslots > 0 <->
exists freeslotpointer, pdentryFirstFreeSlot pdinsertion freeslotpointer s /\
freeslotpointer <> nullAddr.*)
forall pdinsertion currnbfreeslots,
pdentryNbFreeSlots pdinsertion currnbfreeslots s /\ currnbfreeslots > 0 ->
exists freeslotpointer, pdentryFirstFreeSlot pdinsertion freeslotpointer s /\
isBE freeslotpointer s.*)

(*forall pdinsertion freeslotpointer currnbfreeslots,
(pdentryFirstFreeSlot pdinsertion freeslotpointer s ->
freeslotpointer <> nullAddr) <->
( exists optionfreeslotslist1,
optionfreeslotslist1 = getFreeSlotsList pdinsertion s /\
wellFormedFreeSlotsList optionfreeslotslist1 s <> False ->
currnbfreeslots = CIndex (length (filterOption (optionfreeslotslist1)))) ->
pdentryNbFreeSlots pdinsertion currnbfreeslots s
-> currnbfreeslots > 0.*)

(*Definition FirstFreeSlotPointerNull s :=
forall pdinsertion freeslotpointer nbFreeSlots,
pdentryFirstFreeSlot pdinsertion freeslotpointer s ->
pdentryNbFreeSlots pdinsertion nbFreeSlots s ->
freeslotpointer = nullAddr ->
nbFreeSlots = zero.*)

(* TODO *)
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
disjoint (filterOption (optionfreeslotslist1))(filterOption (optionfreeslotslist2)).


Definition NoDupInFreeSlotsList s :=
forall pd pdentry,
lookup pd (memory s) beqAddr = Some (PDT pdentry) ->
exists optionfreeslotslist, optionfreeslotslist = getFreeSlotsList pd s /\
wellFormedFreeSlotsList optionfreeslotslist <> False /\ (* to get rid of false induction bound constraints *)
NoDup (filterOption (optionfreeslotslist)).

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

Definition CurrentPartIsPDT s :=
forall pdaddr,
currentPartition s = pdaddr ->
isPDT pdaddr s.

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
freeslotslist = filterOption(optionfreeslotslist) /\
In freeslotaddr freeslotslist ->
freeslotaddr <> nullAddr ->
isFreeSlot freeslotaddr s.

(** ** Conjunction of all consistency properties *)
Definition consistency s :=
wellFormedFstShadowIfBlockEntry s /\
PDTIfPDFlag s /\
nullAddrExists s /\
FirstFreeSlotPointerIsBEAndFreeSlot s /\
CurrentPartIsPDT s /\
wellFormedShadowCutIfBlockEntry s /\
BlocksRangeFromKernelStartIsBE s /\
KernelStructureStartFromBlockEntryAddrIsKS s /\
sh1InChildLocationIsBE s /\
StructurePointerIsKS s /\
NextKSIsKS s /\
NextKSOffsetIsPADDR s /\
NoDupInFreeSlotsList s /\
freeSlotsListIsFreeSlot s /\
DisjointFreeSlotsLists s.
