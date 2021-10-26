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
Require Import  Omega List Coq.Logic.ProofIrrelevance.
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
forall idPDchild sh1entryaddr,
true = StateLib.checkChild idPDchild s sh1entryaddr ->
(exists entry, lookup idPDchild s.(memory) beqAddr = Some (BE entry)
/\ entryPDT idPDchild entry.(blockrange).(startAddr) s).

(* TODO : check if needed *)
Definition nullAddrExists s :=
(*forall n,
getNullAddr s = Some n.*)
isPADDR nullAddr s.

Definition FirstFreeSlotPointerIsBE s :=
forall entryaddr entry,
lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
exists slotentry, lookup entry.(firstfreeslot) s.(memory) beqAddr = Some (BE slotentry).

Definition StructurePointerIsBE s :=
forall entryaddr entry,
lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
isBE entry.(structure) s.

Definition StructurePointerIsKS s :=
forall entryaddr entry,
lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
isKS entry.(structure) s.


Definition NextKSOffsetIsPADDR s :=
forall addr nextksaddr : paddr,
isKS addr s ->
nextksaddr = CPaddr (addr + nextoffset) /\
isPADDR nextksaddr s.

Definition NextKSIsKS s :=
forall addr nextksaddr nextKS : paddr,
isKS addr s ->
nextksaddr = CPaddr (addr + nextoffset) /\
nextKSAddr nextksaddr nextKS s ->
nextKS <> nullAddr ->
isKS nextKS s.

Definition KSIsBE s :=
forall addr : paddr,
isKS addr s ->
isBE addr s.


Definition CurrentPartIsPDT s :=
forall pdaddr,
currentPartition s = pdaddr ->
isPDT pdaddr s.

Definition KernelStartIsBE s :=
forall blockentryaddr,
exists blockentry : BlockEntry,
lookup blockentryaddr (memory s) beqAddr = Some (BE blockentry) ->
exists kernelstartaddr : paddr,
StateLib.Paddr.subPaddrIdx blockentryaddr blockentry.(blockindex) = Some kernelstartaddr
/\ isBE kernelstartaddr s.

(* TODO : check if needed *)
(*Definition BlockEntryAddrInBlocksRangeIsBE s :=
forall blockentryaddr : paddr, forall blockidx : index, forall entry : BlockEntry,
lookup blockentryaddr (memory s) beqAddr = Some (BE entry) ->
blockidx < kernelStructureEntriesNb ->
isBE (CPaddr (blockentryaddr + blockidx)) s.*)

Definition KernelStructureStartFromBlockEntryAddrIsBE s :=
forall blockentryaddr : paddr, forall entry : BlockEntry,
lookup blockentryaddr (memory s) beqAddr = Some (BE entry) ->
isBE (CPaddr (blockentryaddr - entry.(blockindex))) s.

Definition PDchildIsBE s :=
forall sh1entryaddr sh1entry,
lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) ->
sh1entry.(PDchild) <> nullAddr ->
isBE sh1entry.(PDchild) s.

Definition sh1InChildLocationIsBE s :=
forall sh1entryaddr sh1entry,
lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) ->
sh1entry.(inChildLocation) <> nullAddr ->
isBE sh1entry.(inChildLocation) s.



(** ** Conjunction of all consistency properties *)
Definition consistency s := 
wellFormedFstShadowIfBlockEntry s /\
PDTIfPDFlag s /\
nullAddrExists s /\
FirstFreeSlotPointerIsBE s /\
CurrentPartIsPDT s /\
KernelStartIsBE s /\
wellFormedShadowCutIfBlockEntry s /\
(*BlockEntryAddrInBlocksRangeIsBE s /\*)
KernelStructureStartFromBlockEntryAddrIsBE s /\
PDchildIsBE s /\
sh1InChildLocationIsBE s /\
StructurePointerIsBE s /\
StructurePointerIsKS s /\
NextKSIsKS s /\
NextKSOffsetIsPADDR s /\
KSIsBE s.
