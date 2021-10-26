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

(**  * Summary 
    In this file we formalize and prove all invariants of the MAL and MALInternal functions *)
Require Import Model.ADT (*Pip.Model.Hardware Pip.Model.IAL*) Model.Monad Model.Lib
               Model.MAL.
Require Import Core.Internal Core.Services.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec EqNat List Bool.

Module WP := WeakestPreconditions.


(* COPY *)
Lemma getCurPartition P :
{{fun s => P s /\ consistency s }} MAL.getCurPartition 
{{fun (pd : paddr) (s : state) => P s /\ consistency s  /\ isPDT pd s /\ pd = currentPartition s }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.getCurPartition .
cbn. intros . intuition.
unfold consistency in *.
unfold CurrentPartIsPDT in *.
intuition. 
Qed.

Module Index. 
(*Lemma eqb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.eqb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.eqb index1 index2}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Index.eqb .
intros. simpl. split;trivial.
Qed.

Lemma gtb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.gtb index1 index2
{{ fun b s => P s /\ b = StateLib.Index.gtb index1 index2 }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Index.gtb .
intros. simpl. split;trivial.
Qed.

Lemma ltb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.ltb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.ltb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.ltb.
intros. simpl. split;trivial.
Qed.*)
(* COPY*)
Lemma ltb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.ltb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.ltb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.ltb.
intros. simpl. split;trivial.
Qed.

(*
Lemma leb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.leb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.leb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.leb.
intros. simpl. split;trivial.
Qed.*)

(*COPY *)
Lemma leb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.leb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.leb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.leb.
intros. simpl. split;trivial.
Qed.

(*
Lemma geb index1 index2 (P : state -> Prop):
{{ fun s : state => P  s }} MALInternal.Index.geb index1 index2 
{{ fun b s => P s /\ b = StateLib.Index.geb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.geb.
intros. simpl. split;trivial.
Qed.

Lemma zero P :
{{fun s => P s }} MALInternal.Index.zero 
{{fun (idx0 : index) (s : state) => P s  /\ idx0 = CIndex 0 }}.
Proof.
unfold MALInternal.Index.zero.
eapply WP.weaken.
eapply WP.ret .
intros. simpl.
intuition.
unfold CIndex.
case_eq (lt_dec 0 tableSize).
intros. f_equal. apply proof_irrelevance.
intuition. assert (tableSize > tableSizeLowerBound). apply tableSizeBigEnough.
unfold  tableSizeLowerBound in * . contradict H1. lia.
Qed.
*)

(* partial DUP *)
Lemma zero P :
{{fun s => P s }} MALInternal.Index.zero 
{{fun (idx0 : index) (s : state) => P s  /\ idx0 = CIndex 0 }}.
Proof.
unfold MALInternal.Index.zero.
eapply WP.weaken.
eapply WP.ret .
intros. simpl.
intuition.
Qed.

(*

Lemma succ (idx : index ) P :
{{fun s => P s  /\ idx < tableSize - 1}} MALInternal.Index.succ idx 
{{fun (idxsuc : index) (s : state) => P s  /\ StateLib.Index.succ idx = Some idxsuc }}.
Proof.
eapply WP.weaken. 
eapply  WeakestPreconditions.Index.succ.
cbn.
intros.
split.  
intuition.
intros.
split. intuition.
unfold StateLib.Index.succ.
subst.
destruct (lt_dec (idx + 1) tableSize). assert (l=l0).
apply proof_irrelevance.
subst. reflexivity.
intuition. 
Qed.
*)

Lemma pred (idx : index ) P :
{{fun s => P s  /\ idx > 0}} MALInternal.Index.pred idx 
{{fun (idxpred : index) (s : state) => P s  /\ StateLib.Index.pred idx = Some idxpred }}.
Proof.
eapply WP.weaken. 
eapply  WeakestPreconditions.Index.pred.
cbn.
intros.
split.  
intuition.
intros.
split. intuition.
unfold StateLib.Index.pred.
subst.
destruct (gt_dec idx 0).
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition. 
Qed.
End Index.

Module Paddr.
(* DUP *)
Lemma leb addr1 addr2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Paddr.leb addr1 addr2
{{ fun b s => P s /\ b = StateLib.Paddr.leb addr1 addr2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Paddr.leb.
intros. simpl. split;trivial.
Qed.

(* DUP *)
(*Lemma subPaddr addr1 addr2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Paddr.subPaddr addr1 addr2
{{ fun b s => P s /\ b = StateLib.Paddr.subPaddr addr1 addr2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Paddr.subPaddr.
intros. simpl. split;trivial.
Qed.*)

(* DUP de pred *)
Lemma subPaddr  (addr1 addr2 : paddr ) P :
{{fun s => P s  /\ addr1 >= 0 /\ addr2 >= 0 /\ addr1 - addr2 < maxIdx}}
MALInternal.Paddr.subPaddr addr1 addr2
{{fun (idxsub : index) (s : state) => P s  /\ StateLib.Paddr.subPaddr addr1 addr2 = Some idxsub }}.
Proof.
eapply WP.weaken. 
eapply  WeakestPreconditions.Paddr.subPaddr.
cbn.
intros.
split.  
intuition.
intros.
split. intuition.
unfold StateLib.Paddr.subPaddr.
subst.
destruct (lt_dec (addr1 - addr2) maxIdx).
split. intuition. intuition. 
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition. 
Qed.

(* DUP*)
Lemma subPaddrIdx  (addr : paddr) (idx: index) (P: state -> Prop) :
{{ fun s : state => P s /\ addr >= 0 /\ idx >= 0 /\ addr - idx < maxAddr (*/\ forall Hp : n - m < maxAddr,  
                   P {| p := n -m; Hp := Hp |} s*) }}
MALInternal.Paddr.subPaddrIdx addr idx
{{fun (paddrsub : paddr) (s : state) => P s  (*/\ StateLib.Paddr.subPaddrIdx addr idx = Some paddrsub *)
/\ CPaddr (addr - idx) = paddrsub}}.
Proof.
(*eapply WP.weaken. 
eapply  WeakestPreconditions.Paddr.subPaddrIdx.
cbn.
intros.
split.  
intuition.
intros.
split. intuition.
intros. split. apply H.
unfold StateLib.Paddr.subPaddrIdx.
destruct (lt_dec (addr - idx) maxAddr). intuition.
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition.*)
eapply WP.weaken. 
eapply  WeakestPreconditions.Paddr.subPaddrIdx.
cbn.
intros.
split.  
intuition.
intros.
split. intuition.
intros. split. apply H.
unfold CPaddr.
destruct (lt_dec (addr - idx) maxAddr). intuition.
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition.
Qed.

(* DUP *)
Lemma pred (addr : paddr ) P :
{{fun s => P s  /\ addr > 0}} MALInternal.Paddr.pred addr 
{{fun (addrpred : paddr) (s : state) => P s  /\ StateLib.Paddr.pred addr = Some addrpred }}.
Proof.
eapply WP.weaken. 
eapply WeakestPreconditions.Paddr.pred.
cbn.
intros.
split.  
intuition.
intros.
split. intuition.
unfold StateLib.Paddr.pred.
subst.
destruct (gt_dec addr 0).
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition. 
Qed.

End Paddr.

Lemma check32Aligned (addr : paddr ) P :
{{fun s => P s  /\ addr >= 0}} MAL.check32Aligned addr 
{{fun (is32aligned : bool) (s : state) => P s  /\ is32aligned = StateLib.is32Aligned addr }}.
Proof.
eapply WP.weaken. 
eapply  WeakestPreconditions.check32Aligned.
cbn.
intros.
split.  
intuition.
intros. reflexivity.
Qed.
(*

Module Level.
Lemma gtb level1 level2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Level.gtb level1 level2 
{{ fun b s => P s /\ b = StateLib.Level.gtb level1 level2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Level.gtb.
intros. simpl. split;trivial.
Qed.

Lemma pred (level1 : level ) P :
{{fun s => P s  /\ level1 > 0 }} MALInternal.Level.pred level1
{{fun (levelpred : level) (s : state) => P s  /\ StateLib.Level.pred level1 = Some levelpred }}.
Proof.
eapply WP.weaken. 
eapply WeakestPreconditions.Level.pred . cbn.
intros.
split.  
intuition.
intros.
split. intuition.
unfold StateLib.Level.pred.
unfold runvalue. subst. 
destruct (gt_dec level1 0).
intros. assert (Hl =  StateLib.Level.pred_obligation_1 level1 g ).
apply proof_irrelevance.
subst. reflexivity.
intuition. 
Qed.

Lemma eqb level1 level2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Level.eqb level1 level2 
{{ fun b s => P s /\  b = StateLib.Level.eqb level1 level2 }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Level.eqb .
intros; simpl; split;trivial.
Qed.
End Level.

Module Page. 
Lemma eqb page1 page2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Page.eqb page1 page2 
{{ fun b s => P s /\ b = StateLib.Page.eqb page1 page2}}.
Proof.
eapply WP.weaken.
eapply WP.Page.eqb .
intros. simpl. split;trivial.
Qed.
End Page.

Module VAddr. 
Lemma eqbList vaddr1 vaddr2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.VAddr.eqbList vaddr1 vaddr2 
{{ fun b s => P s /\ b = StateLib.VAddr.eqbList vaddr1 vaddr2}}.
Proof.
eapply WP.weaken.
eapply WP.VAddr.eqbList .
intros. simpl. split;trivial.
Qed.
End VAddr.

Lemma ret (A : Type) (a : A)  P :
{{fun s => P s }} Hardware.ret a
{{fun (v : A) (s : state) => P s  /\ v = a }}.
Proof.
eapply WP.weaken. 
eapply WP.ret . cbn.
intros. 
auto.
Qed.

Lemma getMaxIndex P : 
{{ fun s => P s }} MAL.getMaxIndex 
{{ fun idx s => P s /\ idx = CIndex (tableSize -1) }}.
Proof.
unfold MAL.getMaxIndex.
case_eq (gt_dec tableSize 0);
intros.
eapply WP.weaken.
eapply WP.ret . intros.
simpl. split. assumption.
unfold CIndex.
case_eq ( lt_dec (tableSize - 1) tableSize ).
intros.     
f_equal. apply proof_irrelevance.
intuition.
assert (tableSize > tableSizeLowerBound).
apply tableSizeBigEnough.
unfold  tableSizeLowerBound in * .
contradict H0. lia.
Qed.



Lemma readPhyEntry (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s /\  isPE table idx s}} MAL.readPhyEntry table idx 
{{fun (page1 : page) (s : state) => P s /\ isEntryPage table idx page1 s}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.readPhyEntry .
simpl. intros.
destruct H as (H & Hpage).
unfold isPE, isEntryPage in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
Qed.

Lemma readIndex (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s /\  isI table idx s}} MAL.readIndex table idx 
{{fun (ivalue : index) (s : state) => P s /\ isIndexValue table idx ivalue s}}.
Proof.
eapply WP.weaken.
eapply WP.readIndex .
simpl. intros.
destruct H as (H & Hpage).
unfold isI, isIndexValue in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
Qed.


Lemma getDefaultPage P : 
{{fun s => P s}} MALInternal.getDefaultPage 
{{fun nullp s => P s /\ nullp = defaultPage}}.
Proof.
unfold MALInternal.getDefaultPage.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.  

Lemma getDefaultVAddr P : 
{{fun s => P s}} MALInternal.getDefaultVAddr 
{{fun nullv s => P s /\ nullv = defaultVAddr }}.
Proof.
unfold MALInternal.getDefaultVAddr.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.
*)

(* DUP of getDefaultVaddr *)
Lemma getMinBlockSize P : 
{{fun s => P s}} MALInternal.getMinBlockSize
{{fun minsize s => P s /\ minsize = Constants.minBlockSize }}.
Proof.
unfold MALInternal.getMinBlockSize.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.

(* DUP *)
Lemma removeDupIdentity  (l :  list (paddr * value)) : 
forall addr1 addr2 , addr1 <> addr2  -> 
lookup addr1 (removeDup addr2 l  beqAddr) beqAddr = 
lookup addr1 l beqAddr.
Proof.
intros.
induction l.
simpl. trivial.
simpl.
destruct a.
destruct p.
+ case_eq (beqAddr {| p := p; Hp := Hp |} addr2).
  - intros. cbn in *.
    case_eq (PeanoNat.Nat.eqb p addr1).
    * intros.
      apply beq_nat_true in H0.
      apply beq_nat_true in H1.
			rewrite H1 in H0.
			apply beqAddrFalse in H.
			unfold beqAddr in H.
			apply beq_nat_false in H.
			congruence.

		* intros. assumption.
	- intros. simpl. 
		case_eq (beqAddr {| p := p; Hp := Hp |} addr1).
		intros. trivial.
		intros. assumption.
Qed.

Lemma removeDupDupIdentity  (l :  list (paddr * value)) : 
forall addr1 addr2 , addr1 <> addr2  -> 
lookup addr1
  (removeDup addr2 (removeDup addr2 l beqAddr) beqAddr)
	beqAddr
= lookup addr1 (removeDup addr2 l beqAddr) beqAddr.
Proof.
intros.
induction l.
simpl. trivial.
simpl.
destruct a.
destruct p.
+ case_eq (beqAddr {| p := p; Hp := Hp |} addr2).
  - intros. cbn in *. rewrite removeDupIdentity. reflexivity.
		assumption.
	- intros. simpl.
		rewrite H0. simpl. 
		case_eq (beqAddr {| p := p; Hp := Hp |} addr1).
		intros. trivial.
		intros. assumption.
Qed.

(* DUP *)
Lemma isPDTLookupEq (pd : paddr) s : 
isPDT pd s -> exists entry : PDTable,
  lookup pd (memory s) beqAddr = Some (PDT entry).
Proof.
intros.  
unfold isPDT in H.
destruct (lookup pd (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

(* DUP *)
Lemma isBELookupEq (blockentryaddr : paddr) s : 
isBE blockentryaddr s -> exists entry : BlockEntry,
  lookup blockentryaddr (memory s) beqAddr = Some (BE entry).
Proof.
intros.  
unfold isBE in H.
destruct (lookup blockentryaddr (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

(* DUP *)
Lemma isSHELookupEq (sh1entryaddr : paddr) s : 
isSHE sh1entryaddr s -> exists entry : Sh1Entry,
  lookup sh1entryaddr (memory s) beqAddr = Some (SHE entry).
Proof.
intros.  
unfold isSHE in H.
destruct (lookup sh1entryaddr (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

(* DUP *)
Lemma isSCELookupEq (scentryaddr : paddr) s : 
isSCE scentryaddr s -> exists entry : SCEntry,
  lookup scentryaddr (memory s) beqAddr = Some (SCE entry).
Proof.
intros.
unfold isSCE in H.
destruct (lookup scentryaddr (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

(* DUP *)
Lemma isKSLookupEq (addr : paddr) s : 
isKS addr s -> exists entry : BlockEntry,
  lookup addr (memory s) beqAddr = Some (BE entry).
Proof.
intros.  
unfold isKS in H.
destruct (lookup addr (memory s) beqAddr); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
Qed.

(* DUP*)
Lemma lookupBEntryAccessibleFlag entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
bentryAFlag entryaddr (accessible entry) s. 
Proof.
intros.
unfold bentryAFlag.
rewrite H;trivial.
Qed.

(* DUP*)
Lemma lookupBEntryPresentFlag entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
bentryPFlag entryaddr (present entry) s. 
Proof.
intros.
unfold bentryPFlag.
rewrite H;trivial.
Qed.

(* DUP*)
Lemma lookupBEntryReadFlag entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
bentryRFlag entryaddr (read entry) s. 
Proof.
intros.
unfold bentryRFlag.
rewrite H;trivial.
Qed.

(* DUP*)
Lemma lookupBEntryWriteFlag entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
bentryWFlag entryaddr (write entry) s. 
Proof.
intros.
unfold bentryWFlag.
rewrite H;trivial.
Qed.

(* DUP *)
Lemma lookupBEntryExecFlag entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
bentryXFlag entryaddr (exec entry) s. 
Proof.
intros.
unfold bentryXFlag.
rewrite H;trivial.
Qed.

Lemma lookupBEntryBlockIndex entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
bentryBlockIndex entryaddr (blockindex entry) s. 
Proof.
intros.
unfold bentryBlockIndex.
rewrite H;trivial.
split. reflexivity.
destruct entry.
trivial.
Qed.

(*DUP*)
Lemma lookupBEntryStartAddr entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
bentryStartAddr entryaddr (startAddr (blockrange entry)) s. 
Proof.
intros.
unfold bentryStartAddr.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupBEntryEndAddr entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
bentryEndAddr entryaddr (endAddr (blockrange entry)) s. 
Proof.
intros.
unfold bentryEndAddr.
rewrite H;trivial.
Qed.

(* DUP *)
Lemma lookupSh1EntryPDflag paddr s : 
forall entry , lookup paddr (memory s) beqAddr = Some (SHE entry) -> 
sh1entryPDflag paddr (PDflag entry) s. 
Proof.
intros.
unfold sh1entryPDflag.
rewrite H;trivial.
Qed.

Lemma lookupSh1EntryPDchild paddr s : 
forall entry , lookup paddr (memory s) beqAddr = Some (SHE entry) -> 
sh1entryPDchild paddr (PDchild entry) s. 
Proof.
intros.
unfold sh1entryPDchild.
rewrite H;trivial.
Qed.

Lemma lookupSh1EntryInChildLocation paddr s : 
forall entry , lookup paddr (memory s) beqAddr = Some (SHE entry) -> 
consistency s ->
sh1entryInChildLocation paddr (inChildLocation entry) s. 
Proof.
intros.
unfold sh1entryInChildLocation.
rewrite H;trivial.
intuition.
unfold consistency in *. unfold sh1InChildLocationIsBE in *. intuition.
specialize (H10 paddr entry H H1). trivial.
Qed.

Lemma lookupSCEntryOrigin paddr s : 
forall entry , lookup paddr (memory s) beqAddr = Some (SCE entry) -> 
scentryOrigin paddr (origin entry) s. 
Proof.
intros.
unfold scentryOrigin.
rewrite H;trivial.
Qed.

Lemma lookupSCEntryNext paddr s : 
forall entry , lookup paddr (memory s) beqAddr = Some (SCE entry) -> 
scentryNext paddr (next entry) s. 
Proof.
intros.
unfold scentryNext.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupPDEntryFirstFreeSlot entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) -> 
pdentryFirstFreeSlot entryaddr (firstfreeslot entry) s.
Proof.
intros.
unfold pdentryFirstFreeSlot.
rewrite H;trivial.
Qed.


(*DUP*)
Lemma lookupPDEntryNbFreeSlots entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) -> 
pdentryNbFreeSlots entryaddr (nbfreeslots entry) s.
Proof.
intros.
unfold pdentryNbFreeSlots.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupPDEntryStructurePointer entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
(*consistency s ->*)
pdentryStructurePointer entryaddr (structure entry) s.
Proof.
intros.
unfold pdentryStructurePointer.
rewrite H;trivial.
(*intuition.
unfold consistency in *. unfold StructurePointerIsBE in *. intuition.
specialize (H11 entryaddr entry H). trivial.*)
Qed.

(*DUP*)
Lemma lookupPDEntryMPU entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
pdentryMPU entryaddr (MPU entry) s.
Proof.
intros.
unfold pdentryMPU.
rewrite H;trivial.
Qed.

(* DUP*)
Lemma lookupSh1EntryAddr entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
sh1entryAddr entryaddr (CPaddr (entryaddr + sh1offset)) s.
Proof.
intros.
unfold sh1entryAddr.
rewrite H;trivial.
Qed.


(* DUP*)
Lemma lookupSCEntryAddr entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (BE entry) -> 
scentryAddr entryaddr (CPaddr (entryaddr + scoffset)) s.
Proof.
intros.
unfold scentryAddr.
rewrite H;trivial.
Qed.

(*DUP*)
Lemma lookupPDStructurePointer entryaddr s : 
forall entry , lookup entryaddr (memory s) beqAddr = Some (PDT entry) ->
(*consistency s ->*)
pdentryPDStructurePointer entryaddr (structure entry) s.
Proof.
intros.
unfold pdentryPDStructurePointer.
rewrite H;trivial.
(*intuition.
unfold consistency in *. unfold StructurePointerIsBE in *. intuition.
specialize (H11 entryaddr entry H). trivial.*)
Qed.


(* DUP *)
Lemma readBlockStartFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockStartFromBlockEntryAddr paddr
{{ fun (start : ADT.paddr) (s : state) => P s /\ bentryStartAddr paddr start s }}.
Proof.
eapply WP.weaken. 
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryStartAddr;trivial.
Qed.

(*
(* DUP *)
Lemma readBlockStartFromBlockEntryAddrUndecided (addr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ exists entry : value, lookup addr s.(memory) beqAddr = Some entry }} MAL.readBlockStartFromBlockEntryAddr addr
{{ fun (start : paddr) (s : state) => P s /\ entryStartAddr addr start s }}.
Proof.
eapply WP.weaken.
<<<<<<< Updated upstream
unfold MAL.readBlockStartFromBlockEntryAddr.
eapply bind.
- intros. destruct (lookup addr (memory a) beqAddr) eqn:Hlookup.
	destruct v eqn:Hv.
	eapply weaken. apply ret.
	intros. simpl. split. exact H.
	apply lookupEntryStartAddr. simpl in *. intuition. assumption. unfold entryStartAddr.
	destruct (lookup addr (memory s) beqAddr).
	destruct v0.


Qed.*)

Lemma readBlockEndFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockEndFromBlockEntryAddr paddr
{{ fun (endaddr : ADT.paddr) (s : state) => P s /\ bentryEndAddr paddr endaddr s }}.
Proof.
eapply WP.weaken. 
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryEndAddr;trivial.
Qed.


(* DUP *)
Lemma readBlockAccessibleFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockAccessibleFromBlockEntryAddr paddr
{{ fun (isA : bool) (s : state) => P s /\ bentryAFlag paddr isA s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryAccessibleFlag;trivial.
Qed.

Lemma readBlockPresentFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockPresentFromBlockEntryAddr paddr
{{ fun (isP : bool) (s : state) => P s /\ bentryPFlag paddr isP s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryPresentFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockRFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockRFromBlockEntryAddr paddr
{{ fun (isR : bool) (s : state) => P s /\ bentryRFlag paddr isR s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryReadFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockWFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockWFromBlockEntryAddr paddr
{{ fun (isW : bool) (s : state) => P s /\ bentryWFlag paddr isW s }}.
Proof.
eapply WP.weaken. 
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryWriteFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockXFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockXFromBlockEntryAddr paddr
{{ fun (isX : bool) (s : state) => P s /\ bentryXFlag paddr isX s }}.
Proof.
eapply WP.weaken. 
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryExecFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockIndexFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockIndexFromBlockEntryAddr paddr
{{ fun (idx : index) (s : state) => P s /\ isBE paddr s /\ bentryBlockIndex paddr idx s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
unfold isBE. rewrite Hentry ; trivial.
apply lookupBEntryBlockIndex;trivial.
Qed.

(* DUP *)
Lemma readPDFirstFreeSlotPointer (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isPDT paddr s  }} MAL.readPDFirstFreeSlotPointer paddr
{{ fun (firstfreeslotaddr : ADT.paddr) (s : state) => P s /\ pdentryFirstFreeSlot paddr firstfreeslotaddr s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupPDEntryFirstFreeSlot;trivial.
Qed.

(* DUP *)
Lemma readPDNbFreeSlots (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isPDT paddr s  }} MAL.readPDNbFreeSlots paddr
{{ fun (nbfreeslots : index) (s : state) => P s /\ pdentryNbFreeSlots paddr nbfreeslots s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupPDEntryNbFreeSlots;trivial.
Qed.

(* DUP *)
Lemma readPDStructurePointer (pdpaddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isPDT pdpaddr s  }} MAL.readPDStructurePointer pdpaddr
{{ fun (structurepointer : paddr) (s : state) => P s /\ pdentryPDStructurePointer pdpaddr structurepointer s }}.
Proof.
eapply WP.weaken. 
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. intuition.
apply lookupPDStructurePointer;trivial.
Qed.


(* Partial DUP *)
Lemma compareAddrToNull (pa : paddr) (P : state -> Prop): 
{{fun s => P s }} compareAddrToNull pa 
{{fun (isnull : bool) (s : state) => P s /\ 
                                       (beqAddr nullAddr pa) = isnull }}. 
Proof.
unfold compareAddrToNull.
eapply WP.bindRev.
+ unfold MALInternal.getNullAddr.
  eapply WP.weaken.  
  eapply WP.ret . intros.
  instantiate (1:= fun nullPa s => P s /\ beqAddr nullAddr nullPa = true ).
  simpl.
  intuition.
  unfold beqAddr.
  destruct nullAddr.
  simpl.
  clear Hp.
  induction p. simpl. trivial.
  simpl.
	apply IHp. 
+ intro nullPa. simpl.
  unfold MALInternal.getBeqAddr.
  eapply WP.weaken. eapply WP.ret . intros. 
  simpl. intuition.
  unfold beqAddr in *.
	destruct nullAddr, pa.
  simpl in *.
	case_eq p. intros. induction p0. subst. simpl. destruct H1.
	Search PeanoNat.Nat.eqb.
	apply PeanoNat.Nat.eqb_sym.
	
	subst. apply PeanoNat.Nat.eqb_eq in H1.
rewrite -> H1. trivial.
intros. apply PeanoNat.Nat.eqb_eq in H1. rewrite <- H1. rewrite ->H. trivial. 
Qed.

Lemma getBeqAddr (p1 : paddr)  (p2 : paddr) (P : state -> Prop): 
{{fun s => P s }} getBeqAddr p1 p2
{{fun (isequal : bool) (s : state) => P s /\ 
                                       (beqAddr p1 p2) = isequal }}.
Proof.
	unfold MALInternal.getBeqAddr.
  eapply WP.weaken. eapply WP.ret . intros. 
  simpl. intuition.
Qed.

(*

(* DUP *)
Lemma readPDStructurePointer (pdpaddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isPDT pdpaddr s  }} MAL.readPDStructurePointer pdpaddr
{{ fun (structurepointer : paddr) (s : state) => P s /\ pdentryStructurePointer pdpaddr structurepointer s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. intuition.
apply lookupPDEntryStructurePointer;trivial.
Qed.

(* DUP *)
Lemma readPDMPU (pdtablepaddr: paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isPDT pdtablepaddr s  }} MAL.readPDMPU pdtablepaddr
{{ fun (realMPUentries : list paddr) (s : state) => P s /\ pdentryMPU pdtablepaddr realMPUentries s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupPDEntryMPU;trivial.
Qed.

(*
(* DUP *)
Lemma readBlockAccessibleFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockAccessibleFromBlockEntryAddr paddr
{{ fun (isA : bool) (s : state) => P s /\ bentryAFlag paddr isA s }}.
Proof.
eapply WP.weaken. 
apply WP.readBlockAccessibleFromBlockEntryAddr.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryAccessibleFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockPresentFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockPresentFromBlockEntryAddr paddr
{{ fun (isP : bool) (s : state) => P s /\ bentryPFlag paddr isP s }}.
Proof.
eapply WP.weaken. 
apply WP.readBlockPresentFromBlockEntryAddr.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryPresentFlag;trivial.
Qed.


(* DUP *)
Lemma readBlockRFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockRFromBlockEntryAddr paddr
{{ fun (isR : bool) (s : state) => P s /\ bentryRFlag paddr isR s }}.
>>>>>>> Stashed changes
Proof.
eapply WP.weaken. 
apply WP.readBlockRFromBlockEntryAddr.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryReadFlag;trivial.
Qed.


(* DUP *)
Lemma readBlockWFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockWFromBlockEntryAddr paddr
{{ fun (isW : bool) (s : state) => P s /\ bentryWFlag paddr isW s }}.
Proof.
eapply WP.weaken. 
apply WP.readBlockWFromBlockEntryAddr.
simpl.
intros.
<<<<<<< Updated upstream
unfold entryPresentFlag, isPE in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict H.
destruct v; try now contradict H.
eexists;repeat split;trivial.
=======
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryWriteFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockXFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockXFromBlockEntryAddr paddr
{{ fun (isX : bool) (s : state) => P s /\ bentryXFlag paddr isX s }}.
Proof.
eapply WP.weaken. 
apply WP.readBlockXFromBlockEntryAddr.
simpl.
intros.
<<<<<<< Updated upstream
unfold entryPresentFlag, isPE in *. 
destruct (lookup table idx (memory s) beqPage beqIndex)
as [v |]; [ destruct v as [ p |v|p|v|i]; [trivial | now contradict H | 
now contradict H| now contradict H| now contradict H ] | now contradict H ].
>>>>>>> Stashed changes
Qed.

Lemma getPd (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In PR (getPartitions multiplexer s) }} 
                      Internal.getPd PR 
{{fun (pd : page) (s : state) => P s /\ nextEntryIsPP PR PDidx pd s 
                                             }}.
Proof.
unfold Internal.getPd.
eapply WP.bindRev.
(** getPDidx **)
apply getPDidx.
intro idxPD. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
destruct H as ((Hp & Hdescr & Hcurpart ) & Hidx). 
subst.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
generalize (Hdescr PR Hcurpart); clear Hdescr; intros Hdescr.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx 
\/ PDidx = sh3idx \/ PDidx = PPRidx \/ PDidx = PRidx ) as Htmp by auto.
generalize (Hdescr PDidx Htmp); clear Hdescr; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hcons & Hcur ) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in Hcons.
unfold currentPartitionInPartitionsList in *.
generalize (Hcons PR Hcur); clear Hcons; intros Hcons.

generalize (Hcons  PDidx); clear Hcons; intro Hpdtmp.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/ PDidx = sh3idx  \/ PDidx = PPRidx \/ PDidx = PRidx ) 
as Hpd by auto.
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup PR idxsucc (memory s) beqPage beqIndex); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma readPhysical (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s /\ isPP table idx s}} MAL.readPhysical table idx 
{{fun (page1 : page) (s : state) => P s /\ isPP' table idx page1 s}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (H & Hpage).
unfold isPP', isPP in *.
<<<<<<< Updated upstream
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
=======
destruct (lookup table idx (memory s) beqPage beqIndex)
       as [v |];  [ destruct v as [ p |v|p|v|i] ; [ now contradict Hpage | now contradict Hpage | 
       eexists; repeat split;trivial| now contradict Hpage| now contradict Hpage ] | now contradict Hpage].
=======
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupBEntryExecFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockIndexFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockIndexFromBlockEntryAddr paddr
{{ fun (idx : index) (s : state) => P s /\ isBE paddr s /\ bentryBlockIndex paddr idx s }}.
Proof.
eapply WP.weaken. 
apply WP.readBlockIndexFromBlockEntryAddr.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
unfold isBE. rewrite Hentry ; trivial.
apply lookupBEntryBlockIndex;trivial.
>>>>>>> Stashed changes
>>>>>>> Stashed changes
Qed.

(* DUP *)
Lemma readPDFirstFreeSlotPointer (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isPDT paddr s  }} MAL.readPDFirstFreeSlotPointer paddr
{{ fun (firstfreeslotaddr : ADT.paddr) (s : state) => P s /\ pdentryFirstFreeSlot paddr firstfreeslotaddr s }}.
Proof.
<<<<<<< Updated upstream
eapply WP.weaken.
eapply WeakestPreconditions.readVirtual .
simpl. intros.
destruct H as (H & Hpage).
unfold isVA, isVA' in *.
destruct (lookup table idx (memory s) beqPage beqIndex); try now contradict Hpage.
destruct v; try now contradict Hpage.
eexists;repeat split;trivial.
Qed.

Lemma readVirtualUser (table : page) (idx : index) (P : state -> Prop):
{{fun s => P s}} MAL.readVirtualUser table idx 
{{fun (va : vaddr) (s : state) => P s /\ isVAUser table idx va s}}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.readVirtualUser .
simpl. intros.
unfold isVAUser.
destruct (lookup table idx (memory s) beqPage beqIndex);
[destruct v|]; split;trivial.
Qed.

Lemma getSndShadow (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ In PR (getPartitions multiplexer s) }} Internal.getSndShadow PR 
{{fun (sh2 : page) (s : state) => P s /\ nextEntryIsPP PR sh2idx sh2 s }}.
Proof.
unfold Internal.getSndShadow.
eapply WP.bindRev.
(** getSh2idx **)
apply getSh2idx.
intro idxSh2. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
subst.
intuition. subst.
unfold partitionDescriptorEntry in *.
generalize (H0 PR H3); clear H0; intros H0.
assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/ sh2idx = sh3idx 
\/  sh2idx  = PPRidx \/  sh2idx  = PRidx ) as Htmp by auto.
generalize (H0 sh2idx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as ( ((HP & Hcons & Hcur ) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in Hcons.
generalize (Hcons PR Hcur ); clear Hcons; intros Hcons.
generalize (Hcons  sh2idx); clear Hcons; intro Hpdtmp.
assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/ sh2idx = sh3idx \/  sh2idx  = PPRidx
 \/  sh2idx  = PRidx)  
as Hpd by auto.
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
unfold nextEntryIsPP in Hpp.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup PR idxsucc (memory s) beqPage beqIndex); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma getFstShadow (PR : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ currentPartitionInPartitionsList s /\  PR = currentPartition s}} Internal.getFstShadow PR 
{{fun (sh1 : page) (s : state) => P s /\ nextEntryIsPP PR sh1idx sh1 s }}.
Proof.
unfold Internal.getFstShadow.
eapply WP.bindRev.
(** getPDidx **)
apply getSh1idx.
intro idxSh1. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
subst.
intuition. subst.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
generalize (H0 (currentPartition s) H2); clear H0; intros H0.
assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/ sh1idx = sh3idx 
\/  sh1idx  = PPRidx \/  sh1idx  = PRidx ) as Htmp by auto.
generalize (H0 sh1idx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hcons & Hcur & Hpr) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in Hcons.
unfold currentPartitionInPartitionsList in *.
generalize (Hcons (currentPartition s) Hcur ); clear Hcons; intros Hcons.
generalize (Hcons  sh1idx); clear Hcons; intro Hpdtmp.
assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/ sh1idx = sh3idx
 \/  sh1idx  = PPRidx \/  sh1idx  = PRidx)  
as Hpd by auto.
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup (currentPartition s) idxsucc (memory s) beqPage beqIndex); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.

Lemma getFstShadow1 (partition : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ 
In partition (getPartitions multiplexer s)  }} 
Internal.getFstShadow partition
{{fun (sh1 : page) (s : state) => P s /\ nextEntryIsPP partition sh1idx sh1 s }}.
Proof.
unfold Internal.getFstShadow.
eapply WP.bindRev.
(** getPDidx **)
apply getSh1idx.
intro idxSh1. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
subst.
intuition. subst.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
generalize (H0 partition H3); clear H0; intros H0.
assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/ sh1idx = sh3idx 
\/  sh1idx  = PPRidx \/  sh1idx  = PRidx ) as Htmp by auto.
generalize (H0 sh1idx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hpde & Hpr) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in *.
apply Hpde with partition sh1idx in Hpr.
destruct Hpr as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
split.
unfold nextEntryIsPP in Hpp.
destruct (StateLib.Index.succ sh1idx);inversion Hidxsucc;subst. 
destruct (lookup partition idxsucc (memory s) beqPage beqIndex);
try now contradict Hpp.
destruct v ; try now contradict Hpp.
destruct page1;destruct p;simpl in *. 
do 2 f_equal.
inversion Hpp.
subst. 
f_equal.
apply proof_irrelevance.
split;trivial.
right;left;trivial.
Qed.

Lemma getConfigTablesLinkedList  (partition : page) (P : state -> Prop) :
{{fun s => P s  /\ partitionDescriptorEntry s /\ 
In partition (getPartitions multiplexer s)  }} 
Internal.getConfigTablesLinkedList  partition
{{fun (LL : page) (s : state) => P s /\ nextEntryIsPP partition sh3idx LL s }}.
Proof.
unfold Internal.getConfigTablesLinkedList .
eapply WP.bindRev.
(** getPDidx **)
apply getSh3idx.
intro idxSh3. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
subst.
intuition. subst.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
generalize (H0 partition H3); clear H0; intros H0.
assert (sh3idx = PDidx \/ sh3idx = sh1idx \/ sh3idx = sh2idx \/ sh3idx = sh3idx 
\/  sh3idx  = PPRidx \/  sh3idx  = PRidx ) as Htmp by auto.
generalize (H0 sh3idx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hpde & Hpr) &Hidx) & Hidxsucc).
subst.
unfold partitionDescriptorEntry in *.
apply Hpde with partition sh3idx in Hpr.
destruct Hpr as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
split.
unfold nextEntryIsPP in Hpp.
destruct (StateLib.Index.succ sh3idx);inversion Hidxsucc;subst. 
destruct (lookup partition idxsucc (memory s) beqPage beqIndex);
try now contradict Hpp.
destruct v ; try now contradict Hpp.
destruct page1;destruct p;simpl in *. 
do 2 f_equal.
inversion Hpp.
subst. 
f_equal.
apply proof_irrelevance.
split;trivial.
do 3 right;left;trivial.
Qed.


Lemma checkKernelMap  (va: vaddr) (P : state -> Prop): 
{{fun s => P s }} checkKernelMap va 
{{fun isk s => P s /\ (Nat.eqb Kidx (nth (length va - (nbLevel - 1 + 2)) va defaultIndex) ) = isk}}.
Proof.
unfold checkKernelMap.
eapply WP.bindRev.
eapply getKidx.
simpl.
intros kidx.
eapply WP.bindRev.
eapply WP.weaken.
eapply getNbLevel.
simpl. intros.
pattern s in H.
eapply H.
intro l.
eapply WP.bindRev.
eapply WP.weaken.
eapply getIndexOfAddr.
intros. simpl.
pattern s in H.
eapply H.
intros idx.
simpl.
eapply WP.weaken.
eapply WP.ret .
simpl.
intros.
unfold StateLib.getIndexOfAddr in *.
intuition.
rewrite <- H1.
unfold StateLib.getNbLevel in H2.
case_eq (gt_dec nbLevel 0);
intros; rewrite H in H2.
inversion H2.
destruct l.
simpl in *. subst.  reflexivity.
assert(0 < nbLevel) by apply nbLevelNotZero.
now contradict H4.  
Qed. 

Lemma checkVAddrsEqualityWOOffset (va1 va2 : vaddr) (level1 : level) (P : state -> Prop) : 
{{fun s => P s }} Internal.checkVAddrsEqualityWOOffset va1 va2 level1 
{{fun res s => P s /\ res = checkVAddrsEqualityWOOffset nbLevel va1 va2 level1 }}.
Proof.
unfold Internal.checkVAddrsEqualityWOOffset.
revert va1 va2 level1 P.
induction nbLevel;intros.
+ simpl. eapply WP.weaken.
  eapply WP.ret . intros. simpl.  split;trivial.
+ simpl.
(** getIndexOfAddr **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply getIndexOfAddr.
  simpl.
  intros.
  eassumption.
  intros idx1.
(** getIndexOfAddr **)
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply getIndexOfAddr.
  simpl.
  intros.
  pattern s in H. 
  eassumption.
  intros idx2.
(** MALInternal.Level.eqb **)
  eapply WP.bindRev. 
  eapply WP.weaken.
  eapply Level.eqb.
  simpl. intros.
  pattern s in H.
  eassumption.
(** test *)
  intros a; simpl.
  case_eq a;intros.
  - eapply WP.strengthen.
    eapply WP.weaken. 
    eapply Index.eqb.
    simpl; intros.
    pattern s in H0.
    eassumption. simpl.
    split; intuition.
    rewrite <- H3, H4.
    subst.     
    unfold StateLib.Index.eqb.
    trivial.
  - (** MALInternal.Level.pred **) 
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply Level.pred.
    intros; simpl.
    split. 
    pattern s in H0.
    eassumption.
    destruct H0.
    symmetry in H1.
    apply levelEqBEqNatFalse0  in H1. assumption.
    intros levelpred.
(** MALInternal.Index.eqb **)
    eapply WP.bindRev.
    eapply WP.weaken.
    eapply Index.eqb.
    intros; simpl.
    pattern s in H0.
    eapply H0. 
    simpl in *.
    intros. 
    case_eq a0; intros.
    eapply WP.strengthen.
    generalize (IHn va1 va2 levelpred (fun s : state => ((((P s /\ StateLib.getIndexOfAddr va1 level1 = idx1) /\ 
    StateLib.getIndexOfAddr va2 level1 = idx2) /\
     false = StateLib.Level.eqb level1 fstLevel) /\ StateLib.Level.pred level1 = Some levelpred) /\ 
   true = StateLib.Index.eqb idx1 idx2 ) ); clear IHn; intros IHn.
    eapply IHn.
    simpl.
    intros; intuition. subst.
    rewrite <- H6.
    rewrite H5.
    unfold StateLib.Index.eqb in H4.   
    rewrite <- H4. trivial.
    eapply WP.weaken.
    eapply WP.ret .
    simpl.
    intros.
    intuition.
    rewrite <- H5.
    rewrite H4. 
    unfold StateLib.Index.eqb in H3.
    subst.
    rewrite <- H3; trivial.
Qed.

Lemma readPDflag (table : page) (idx : index) (P : state -> Prop) : 
{{ fun s => P s /\ isVE table idx s }} MAL.readPDflag table idx 
{{ fun (ispd : bool) (s : state) => P s /\  entryPDFlag table idx ispd s }}.
=======
eapply WP.weaken. 
apply WP.readPDFirstFreeSlotPointer.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupPDEntryFirstFreeSlot;trivial.
Qed.

(* DUP *)
Lemma readPDNbFreeSlots (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isPDT paddr s  }} MAL.readPDNbFreeSlots paddr
{{ fun (nbfreeslots : index) (s : state) => P s /\ pdentryNbFreeSlots paddr nbfreeslots s }}.
Proof.
eapply WP.weaken. 
apply WP.readPDNbFreeSlots.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry). 
exists entry. repeat split;trivial.
apply lookupPDEntryNbFreeSlots;trivial.
Qed.

(* DUP *)
Lemma readPDStructurePointer (pdpaddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isPDT pdpaddr s  }} MAL.readPDStructurePointer pdpaddr
{{ fun (structurepointer : paddr) (s : state) => P s /\ pdentryPDStructurePointer pdpaddr structurepointer s }}.
>>>>>>> Stashed changes
Proof.
eapply WP.weaken. 
apply WP.readPDStructurePointer.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. intuition.
apply lookupPDStructurePointer;trivial.
Qed.*)

<<<<<<< Updated upstream
Lemma getParent (PR : page) (P : state -> Prop) :
{{fun s => P s /\ consistency s /\ In PR (getPartitions multiplexer s) }} Internal.getParent PR 
{{fun (parent : page) (s : state) => P s /\ nextEntryIsPP PR PPRidx parent s }}.
Proof.
unfold Internal.getParent.
eapply WP.bindRev.
(** getPDidx **)
apply getPPRidx.
intro idxppr. 
simpl. 
(** MALInternal.Index.succ **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Index.succ.
intros. simpl.
split.
pattern s in H. 
eapply H.
destruct H as ((H1 & H2 & H3) & H4). 
subst.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
unfold currentPartitionInPartitionsList in *.
destruct H2. 
generalize (H PR H3); clear H0; intros H0.
assert (PPRidx = PDidx \/ PPRidx= sh1idx \/ PPRidx = sh2idx 
\/ PPRidx = sh3idx \/ PPRidx = PPRidx \/ PPRidx = PRidx) as Htmp.
right. right. right. right. left. auto.
generalize (H0 PPRidx Htmp); clear H0; intros H0.
destruct H0; trivial.
(** readPhysical **)
intro idxsucc. simpl.
eapply WP.weaken.
eapply WeakestPreconditions.readPhysical .
simpl. intros.
destruct H as (((HP & Hcons  & Hpr) &Hidx) & Hidxsucc).
subst.
unfold consistency in *.
unfold partitionDescriptorEntry in Hcons.
unfold currentPartitionInPartitionsList in *.
destruct Hcons as (Hcons & _).

generalize (Hcons PR Hpr ); clear Hcons; intros Hcons.
generalize (Hcons  PPRidx); clear Hcons; intro Hpdtmp.
assert (PPRidx = PDidx \/ PPRidx= sh1idx \/ PPRidx = sh2idx \/ 
PPRidx = sh3idx \/ PPRidx = PPRidx \/ PPRidx = PRidx) as Hpd. 
right. right. right. right. left. auto. 
apply Hpdtmp in Hpd.
clear Hpdtmp. 
unfold partitionDescriptorEntry in Hpd.
destruct Hpd as (_ & Hva & Hpage).
destruct Hpage as (page1 & Hpp & Hnotnul).
subst. exists page1.
repeat split; try assumption.
unfold nextEntryIsPP in Hpp; rewrite Hidxsucc in Hpp.
destruct (lookup PR idxsucc (memory s) beqPage beqIndex); try now contradict Hpp.
destruct v; try now contradict Hpp.
rewrite Hpp; trivial.
Qed.
*)
Lemma compatibleRight (originalright newright : bool) (P : state -> Prop) : 
{{fun s => P s}} Internal.compatibleRight originalright newright {{fun iscompatible s => P s}}.
Proof.
unfold Internal.compatibleRight.
case_eq newright.
	- intros.
		eapply WP.weaken.
		eapply WP.ret.
		intros.
 simpl; trivial.
	- intros.
		eapply WP.weaken.
		eapply WP.ret.
		intros.  simpl; trivial.
Qed.

Lemma getSh1EntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (blockidx : index) (P : state -> Prop) : 
{{ fun s => P s /\ wellFormedFstShadowIfBlockEntry s 
								(*/\ BlockEntryAddrInBlocksRangeIsBE s*)
								/\ isBE kernelStartAddr s
								/\ blockidx < kernelStructureEntriesNb}}
MAL.getSh1EntryAddrFromKernelStructureStart kernelStartAddr blockidx
{{ fun (SHEAddr : ADT.paddr) (s : state) => P s /\ SHEAddr = CPaddr (kernelStartAddr + sh1offset + blockidx)
																								(*/\ SHEntryAddr (CPaddr (kernelStartAddr + blockidx)) SHEAddr s*) }}.
Proof.
	(*unfold MAL.getSh1EntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	unfold wellFormedFstShadowIfBlockEntry in H.
	destruct H. destruct H0.
	specialize (H0 (CPaddr (kernelStartAddr + blockidx))).

	destruct H1. unfold BlockEntryAddrInBlocksRangeIsBE in H1.
	specialize (H1 kernelStartAddr blockidx). destruct H2.
	intuition.*)

unfold MAL.getSh1EntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	unfold wellFormedFstShadowIfBlockEntry in H.
	destruct H. destruct H0.
	specialize (H0 (CPaddr (kernelStartAddr + blockidx))).
	destruct H1. reflexivity. 
Qed.


Lemma getSCEntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (blockidx : index) (P : state -> Prop) : 
{{fun s => 
					P s /\ wellFormedShadowCutIfBlockEntry s 
					/\ exists entry, lookup kernelStartAddr s.(memory) beqAddr = Some (BE entry)
							 }}
MAL.getSCEntryAddrFromKernelStructureStart kernelStartAddr blockidx
{{ fun scentryaddr s => P s /\ scentryaddr = CPaddr (kernelStartAddr + scoffset + blockidx)
															(* SCEntryAddr (CPaddr (kernelStartAddr + blockidx)) scentryaddr s*) 
}}.
Proof.
unfold MAL.getSCEntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	unfold wellFormedShadowCutIfBlockEntry in H.
	destruct H. destruct H0.
	specialize (H0 (CPaddr (kernelStartAddr + blockidx))).
	destruct H1. reflexivity.
Qed.

Lemma getKernelStructureStartAddr  (blockentryaddr : paddr) (blockidx : index)  (P : state -> Prop) : 
{{fun s => (*wellFormedFstShadowIfBlockEntry s /\*)
					(*/\ P blockentryaddr s /\ *)
					P s /\ 	KernelStructureStartFromBlockEntryAddrIsBE s /\
									blockidx < maxIdx /\ blockentryaddr < maxAddr /\
								exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)
								/\ bentryBlockIndex blockentryaddr blockidx s
}}

MAL.getKernelStructureStartAddr blockentryaddr blockidx
{{ fun KSstart s => P s
									/\ exists entry, lookup KSstart s.(memory) beqAddr = Some (BE entry)
									/\ KSstart = CPaddr (blockentryaddr - blockidx) (* need for getSCEntryAddrFromblockentryAddr *)
 (*fun (sh1entryaddr : paddr) (s : state) =>
exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) /\ 
Q sh1entryaddr s*)}}.
Proof.
unfold MAL.getKernelStructureStartAddr.
(*eapply bind. intro kernelStartAddr. apply ret.
eapply weaken.
apply Paddr.subPaddrIdx. intros. simpl in *. split. destruct H. apply H.

intuition. unfold StateLib.Paddr.subPaddrIdx in H1.*)

eapply bindRev.
eapply weaken.
apply Paddr.subPaddrIdx. intros. simpl. split. apply H.
intuition.
(*unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
	destruct H2. specialize (H blockentryaddr x).
	destruct H1. specialize (H H1). unfold entryBlockIndex in H2.
	rewrite H1 in H2. destruct H2.
	subst.
	apply isBELookupEq in H. destruct H.
	intuition.*)



intro kernelStartAddr. simpl. eapply weaken. apply ret.
intros. simpl. split. apply H.
intuition. unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
	destruct H5. destruct H4. specialize(H0 blockentryaddr x H4).
	
	unfold bentryBlockIndex in H5.
	rewrite H4 in H5.
	destruct H5.
	apply isBELookupEq in H0.
	destruct H0.
replace kernelStartAddr with (CPaddr (blockentryaddr - blockidx)).
	exists x0.
	split. rewrite H5. apply H0. reflexivity.
Qed.


Lemma getSh1EntryAddrFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop) : 
{{fun s => Q s /\ wellFormedFstShadowIfBlockEntry s /\
					(*/\ P blockentryaddr s /\ *)
					  KernelStructureStartFromBlockEntryAddrIsBE s
							/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.getSh1EntryAddrFromBlockEntryAddr blockentryaddr
{{ fun sh1entryaddr s => Q s /\ exists sh1entry : Sh1Entry,
lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry) 
/\ sh1entryAddr blockentryaddr sh1entryaddr s
 (*fun (sh1entryaddr : paddr) (s : state) =>
exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) /\ 
Q sh1entryaddr s*)}}.
Proof.
unfold MAL.getSh1EntryAddrFromBlockEntryAddr.
eapply bindRev.
- eapply weaken. apply readBlockIndexFromBlockEntryAddr.
	intros. simpl. split. apply H.
	unfold isBE. destruct (lookup blockentryaddr (memory s) beqAddr).
	destruct v eqn:V; trivial ; destruct H ; destruct H0 ; destruct H1 ; destruct H2 ; congruence.
	destruct H. destruct H0. destruct H1. destruct H2. congruence.
- intro BlockEntryIndex.
	eapply bindRev. eapply weaken.
	apply getKernelStructureStartAddr.
	intros. simpl. split. exact H.
	intuition.
	destruct BlockEntryIndex. simpl. trivial.
	destruct blockentryaddr. simpl. trivial.
	destruct H5. exists x. split. apply H4.
	assumption.
	intro kernelStartAddr.
	intros.
	eapply bindRev.
{ 
	eapply weaken. apply getSh1EntryAddrFromKernelStructureStart.
	intros. simpl. split. exact H. split. apply H.
	intros. split. unfold isBE.
	intuition. destruct H1. destruct H1. rewrite H1. trivial.
	intuition. unfold bentryBlockIndex in *. destruct H6. rewrite H5 in H4.
	intuition.
}
(* Preuve : kernelStartAddr + blockindex est BE, donc +sh1offset est SHE
	blockentryindex < kernelstructurenb dans entryBlockIndex*)
	intro SHEAddr. eapply weaken. apply ret.
	intros. simpl. split. apply H.
	intuition.
	unfold wellFormedFstShadowIfBlockEntry in *.
	specialize (H3 blockentryaddr H0).
	unfold isSHE in *.
	destruct H2.
	destruct H2.
	rewrite H6 in H1.
	assert (CPaddr (CPaddr (blockentryaddr - BlockEntryIndex) + sh1offset + BlockEntryIndex)
					= CPaddr (blockentryaddr + sh1offset)).
	{ admit. }
	rewrite H8 in H1.
	rewrite <- H1 in H3.
	destruct (lookup SHEAddr (memory s) beqAddr). destruct v.
	exfalso ; congruence.
	exists s0. split. reflexivity. unfold sh1entryAddr. destruct H7. rewrite H7; trivial. 
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
Admitted.

(* DUP *)
Lemma getNextAddrFromKernelStructureStart  (kernelStartAddr : paddr) (P : state -> Prop) : 
{{fun s => P s (*/\ wellFormedNextKSAddrIfKernelStructureStart s *)
					/\ exists entry, lookup kernelStartAddr s.(memory) beqAddr = Some (BE entry)}}
MAL.getNextAddrFromKernelStructureStart kernelStartAddr
{{ fun nextaddr s => P s /\ nextaddr = CPaddr (kernelStartAddr + nextoffset) (*/\ exists entry, lookup nextaddr s.(memory) beqAddr = Some (PADDR entry)
/\ nextKSAddr nextksaddr nextksaddr s
/\ nextksaddr = CPaddr (kernelStartAddr + nextoffset)*)}}.
Proof.
unfold MAL.getNextAddrFromKernelStructureStart.
eapply weaken. apply ret.
intros. simpl. intuition. 
Qed.

Lemma readSh1PDChildFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)  (*/\ 
             exists sh1entry, P sh1entry.(PDflag) s *)}}
MAL.readSh1PDChildFromBlockEntryAddr blockentryaddr
{{fun pdchild s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryPDchild sh1entryaddr pdchild s}}.
Proof.
unfold MAL.readSh1PDChildFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+	intro sh1entryaddr. simpl.
	eapply bind.
	intros. apply ret.
	eapply weaken. apply getSh1RecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	apply lookupSh1EntryPDchild. apply H0.
Qed.

(* DUP *)
Lemma readSh1PDFlagFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSh1PDFlagFromBlockEntryAddr blockentryaddr
{{fun pdflag s => Q s
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryPDflag sh1entryaddr pdflag s}}.
Proof.
unfold MAL.readSh1PDFlagFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+	intro sh1entryaddr. simpl.
	eapply bind.
	intros. apply ret.
	eapply weaken. apply getSh1RecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	apply lookupSh1EntryPDflag. apply H0.
Qed.

(* DUP with deeper changes because of lookupSh1EntryInChildLocation *)
Lemma readSh1InChildLocationFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSh1InChildLocationFromBlockEntryAddr blockentryaddr
{{fun inchildlocation s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryInChildLocation sh1entryaddr inchildlocation s}}.
Proof.
unfold readSh1InChildLocationFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. unfold consistency in H. intuition.
+	intro sh1entryaddr. simpl.
	eapply bind.
	intros. apply ret.
	eapply weaken. apply getSh1RecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	apply lookupSh1EntryInChildLocation. apply H0. intuition.
Qed.


Lemma getSCEntryAddrFromBlockEntryAddr  (blockentryaddr : paddr) (P : state -> Prop) : 
{{fun s => (*wellFormedFstShadowIfBlockEntry s /\*)
					(*/\ P blockentryaddr s /\ *)
					P s /\ wellFormedShadowCutIfBlockEntry s /\ KernelStructureStartFromBlockEntryAddrIsBE s
					/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)
							 }}
MAL.getSCEntryAddrFromBlockEntryAddr blockentryaddr
{{ fun scentryaddr s => P s /\ exists entry, lookup scentryaddr s.(memory) beqAddr = Some (SCE entry)
																/\ scentryAddr blockentryaddr scentryaddr s 
(*/\ exists scentry : SCEntry,
lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry) *)
 (*fun (sh1entryaddr : paddr) (s : state) =>
exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) /\ 
Q sh1entryaddr s*)}}.
Proof.
unfold MAL.getSCEntryAddrFromBlockEntryAddr.
eapply bindRev.
{ eapply weaken.
- apply readBlockIndexFromBlockEntryAddr.
- intros. cbn. split. exact H. (* NOTE : Important to propagate the whole property *)
unfold isBE. destruct H. destruct H0. destruct H1. destruct H2. rewrite H2. trivial.
}
intro BlockEntryIndex.
eapply bindRev.
{ eapply weaken.
- apply getKernelStructureStartAddr.
- intros. cbn. split. exact H. intuition.
	destruct BlockEntryIndex. simpl. trivial.
	destruct blockentryaddr. simpl. trivial. (* already done in sh1entry*)
	apply isBELookupEq in H0.
	destruct H0. exists x. intuition.
}
intro kernelStartAddr. simpl.
eapply bindRev.
{
	eapply weaken.  apply getSCEntryAddrFromKernelStructureStart.
	intros. simpl. split. apply H. intuition.
	intuition. destruct H1. exists x. apply H1.
}

	intro SCEAddr.
	eapply weaken. apply ret.
	intros. simpl.
	split. apply H.
	intuition.
	rewrite H1. destruct H2. destruct H2.
	unfold scentryAddr.
	destruct H7.
	rewrite H7.
	rewrite H6.
	unfold wellFormedShadowCutIfBlockEntry in *.
	specialize (H3 blockentryaddr H0).
	destruct H3. destruct H3.
	apply isSCELookupEq in H3.
	destruct H3. exists x2.
	assert (CPaddr (CPaddr (blockentryaddr - BlockEntryIndex) + scoffset + BlockEntryIndex)
					= CPaddr (blockentryaddr + scoffset)).
	{ admit. }
	split. subst.
	rewrite H9. assumption.
	assumption.
	
Admitted.

(* DUP *)
Lemma readSCOriginFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSCOriginFromBlockEntryAddr blockentryaddr
{{fun origin s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists scentry : SCEntry, exists scentryaddr : paddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry)
										/\ scentryOrigin scentryaddr origin s}}.
Proof.
unfold MAL.readSCOriginFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+	intro scentryaddr. simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply getSCRecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists scentryaddr. split. apply H0.
	apply lookupSCEntryOrigin. apply H0.
Qed.

(* DUP with changes in scentryNext + lookupSCEntryNext + changes of function names*)
Lemma readSCNextFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSCNextFromBlockEntryAddr blockentryaddr
{{fun next s => Q s 
										/\ exists scentry : SCEntry, exists scentryaddr : paddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry)
										/\ scentryNext scentryaddr next s}}.
Proof.
unfold MAL.readSCNextFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+	intro scentryaddr. simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply getSCRecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists scentryaddr. split. apply H0.
	apply lookupSCEntryNext. apply H0.
Qed.

Lemma readNextFromKernelStructureStart (structurepaddr : paddr) (P : state -> Prop)  : 
{{fun s  =>  P s /\ NextKSOffsetIsPADDR s /\
						isKS structurepaddr s
             }}
MAL.readNextFromKernelStructureStart structurepaddr
{{fun nextkernelstructure s => P s 
																/\ exists offset, (offset = CPaddr (structurepaddr + nextoffset)
																/\ nextKSAddr offset nextkernelstructure s)}}.
Proof.
unfold MAL.readNextFromKernelStructureStart.
eapply WP.bindRev.
+   eapply WP.weaken. apply getNextAddrFromKernelStructureStart.
	intros. simpl. split. apply H. intuition. apply isKSLookupEq in H2.
	assumption.
+ intro nextaddr.
	simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply WP.readNextFromKernelStructureStart2.
	intros. simpl. intuition. subst.
	 unfold NextKSOffsetIsPADDR in H0.
	specialize (H0 structurepaddr (CPaddr (structurepaddr + nextoffset)) H3).
	intuition. unfold isPADDR in H2.
	destruct (lookup (CPaddr (structurepaddr + nextoffset)) (memory s) beqAddr) eqn:Hlookup ; intuition.
	destruct v eqn:Hv ; intuition.
	exists p. intuition. subst. 
	eexists. intuition. unfold nextKSAddr. rewrite Hlookup ; trivial.
Qed.

(*
(* Partial DUP *)
Lemma compareAddrToNull (pa : paddr) (P : state -> Prop): 
{{fun s => P s }} compareAddrToNull pa 
{{fun (isnull : bool) (s : state) => P s /\ 
                                       (beqAddr nullAddr pa) = isnull }}. 
Proof.
unfold compareAddrToNull.
eapply WP.bindRev.
+ unfold MALInternal.getNullAddr.
  eapply WP.weaken.  
  eapply WP.ret . intros.
  instantiate (1:= fun nullPa s => P s /\ beqAddr nullAddr nullPa = true ).
  simpl.
  intuition.
  unfold beqAddr.
  destruct nullAddr.
  simpl.
  clear Hp.
  induction p. simpl. trivial.
  simpl.
	apply IHp. 
+ intro nullPa. simpl.
  unfold MALInternal.getBeqAddr.
  eapply WP.weaken. eapply WP.ret . intros. 
  simpl. intuition.
  unfold beqAddr in *.
	destruct nullAddr, pa.
  simpl in *.
	case_eq p. intros. induction p0. subst. simpl. destruct H1.
	Search PeanoNat.Nat.eqb.
	apply PeanoNat.Nat.eqb_sym.
	
	subst. apply PeanoNat.Nat.eqb_eq in H1.
rewrite -> H1. trivial.
intros. apply PeanoNat.Nat.eqb_eq in H1. rewrite <- H1. rewrite ->H. trivial. 
Qed.


Lemma getBeqAddr (p1 : paddr)  (p2 : paddr) (P : state -> Prop): 
{{fun s => P s }} getBeqAddr p1 p2
{{fun (isequal : bool) (s : state) => P s /\ 
                                       (beqAddr p1 p2) = isequal }}.
Proof.
	unfold MALInternal.getBeqAddr.
  eapply WP.weaken. eapply WP.ret . intros. 
  simpl. intuition.
Qed.

Lemma compatibleRight (originalright newright : bool) (P : state -> Prop) : 
{{fun s => P s}} Internal.compatibleRight originalright newright {{fun iscompatible s => P s}}.
Proof.
unfold Internal.compatibleRight.
case_eq newright.
	- intros.
		eapply WP.weaken.
		eapply WP.ret.
		intros.
 simpl; trivial.
	- intros.
		eapply WP.weaken.
		eapply WP.ret.
		intros.  simpl; trivial.
Qed.*)

Lemma checkRights p r w e P : 
{{ fun s => P s /\ exists entry, lookup p s.(memory) beqAddr = Some (BE entry)}}
Internal.checkRights  p r w e
{{ fun rights s => P s /\ exists entry, lookup p s.(memory) beqAddr = Some (BE entry)  }}.
Proof. 
unfold checkRights.
case_eq r.
2: {intros. simpl.
	eapply WP.weaken.
eapply WP.ret.
simpl; trivial. (* intuition.*)
}
 intros. simpl.
	eapply WP.bindRev.
{
	eapply WP.weaken.
	eapply readBlockXFromBlockEntryAddr.
	intuition. apply H1. 
	
unfold isBE.
	destruct H2. destruct (lookup p (memory s) beqAddr). destruct v.
	trivial. repeat congruence. congruence. congruence. congruence. congruence.
}
	intro xoriginal.
 	eapply WP.bindRev.
{
		eapply WP.weaken.
	eapply readBlockWFromBlockEntryAddr.
	intuition. apply H1.

	unfold bentryXFlag in H2. 
	
unfold isBE;
destruct (lookup p (memory s) beqAddr). destruct v.
destruct xoriginal.  destruct exec. try repeat trivial. repeat trivial. trivial. trivial. trivial.
trivial. trivial. trivial.
}
	intro woriginal.
 	eapply WP.bindRev.
{ case_eq e.
	intros.
	intros;	apply compatibleRight.
	intros; apply compatibleRight.
}
	intro isCompatibleWithX.
 	eapply WP.bindRev.
{ case_eq w.
	intros;	apply compatibleRight.
	intros; apply compatibleRight.
}
	intro isCompatibleWithW.
	simpl in *.
	destruct (isCompatibleWithX && isCompatibleWithW).
- (* Dup *)
	simpl.
	eapply WP.weaken.
	eapply WP.ret.
	intuition.
	unfold bentryWFlag in H2.
	destruct (lookup p (memory s) beqAddr) eqn:lookup.
	destruct v eqn:V.
	exists b. reflexivity. intuition. intuition. intuition. intuition. intuition.
- simpl.
	eapply WP.weaken.
	eapply WP.ret.
	intuition.
	unfold bentryWFlag in H2.
	destruct (lookup p (memory s) beqAddr) eqn:lookup.
	destruct v eqn:V.
	exists b. reflexivity. intuition. intuition. intuition. intuition. intuition.
Qed.




(*
<<<<<<< Updated upstream
=======
>>>>>>> Stashed changes
>>>>>>> Stashed changes
Lemma checkRights r w e P : 
{{ fun s => P s }} checkRights r w e {{ fun rights s => P s  }}.
Proof. 
unfold checkRights.
case_eq (r && w && e );
intros;
eapply WP.weaken. 
eapply WP.ret.
simpl; trivial.
intros; simpl.
eapply WP.ret.
simpl; trivial.
Qed.
<<<<<<< Updated upstream
=======
<<<<<<< Updated upstream


=======
>>>>>>> Stashed changes
Lemma checkIndexPropertyLTB (userIndex : userValue) (P : state -> Prop) :
{{ fun s => P s }} IAL.checkIndexPropertyLTB userIndex {{ fun b s => (P s /\ (Nat.ltb userIndex tableSize) = b)}}.
Proof.
eapply WP.weaken.
apply WP.checkIndexPropertyLTB.
simpl.
intros. split;trivial.
Qed.
*)


(*Lemma getSh1EntryAddrFromBlockEntryAddr  (paddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s  }} MAL.getSh1EntryAddrFromBlockEntryAddr paddr
{{ fun (sh1entryaddr : ADT.paddr) (s : state) => P s }}.*)
(*Proof.
eapply WP.weaken. 
Admitted.*)



(*Lemma readSh1PDFlagFromBlockEntryAddr  (blockentryaddr : paddr) (P : bool -> state -> Prop) : 
{{fun s  =>  exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) (* /\ 
             exists sh1entry, P sh1entry.(PDflag) s*) }}
MAL.readSh1PDFlagFromBlockEntryAddr blockentryaddr {{fun isPD s => P isPD s}}.
Proof.
unfold MAL.readSh1PDFlagFromBlockEntryAddr.
eapply bindRev.
- eapply weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. destruct H as [HBE]. exists HBE. apply H. (*destruct H as [Hlookup].*) (*split.*)
	(*+ admit. (*apply (P blockentryaddr s).
	*)
	+ now exists HBE.*)
- intro Sh1EAddr. eapply bindRev. apply get. intro s. simpl.
	destruct (lookup Sh1EAddr (memory s) beqAddr) eqn:lookup.
	destruct v eqn:V.
	eapply undefined.
	destruct PDflag eqn:flag.
	eapply weaken. apply ret. (*why False ?*) intros. exfalso ; apply H.
	eapply weaken. apply ret. intros. exfalso ; apply H.
	apply undefined. apply undefined. apply undefined. apply undefined.
Qed.*)
(*
Lemma readSh1PDFlagFromBlockEntryAddr (paddr sh1entryaddr : paddr) (P : state -> Prop) : 
{{ fun s => P s /\ isBE paddr s (*/\ isSHE sh1entryaddr s*) (*/\ wellFormedFstShadowIfBlockEntry s*) }} MAL.readSh1PDFlagFromBlockEntryAddr paddr
{{ fun (ispd : bool) (s : state) => P s /\  entryPDFlag sh1entryaddr ispd s}}.
Proof.

eapply WP.weaken.
apply WP.readSh1PDFlagFromBlockEntryAddr.
simpl.
intros.
destruct H as (H & HBE).
apply isBELookupEq in HBE.
destruct HBE.
exists x. repeat split;trivial.
(*apply isSHELookupEq in HSHE.
destruct HSHE.
exists x0. split. apply H.
unfold entryPDFlag.
rewrite H1; trivial.*)
Qed.*)

(*
Lemma getKernelStructureStartAddr  (blockentryaddr : paddr) (blockidx : index)  (P : state -> Prop) : 
{{fun s => (*wellFormedFstShadowIfBlockEntry s /\*)
					(*/\ P blockentryaddr s /\ *)
					P s /\ 	KernelStructureStartFromBlockEntryAddrIsBE s /\
									blockidx < maxIdx /\ blockentryaddr < maxAddr /\
								exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)
								/\ bentryBlockIndex blockentryaddr blockidx s
}}

MAL.getKernelStructureStartAddr blockentryaddr blockidx
{{ fun KSstart s => P s
									/\ exists entry, lookup KSstart s.(memory) beqAddr = Some (BE entry)
									/\ KSstart = CPaddr (blockentryaddr - blockidx) (* need for getSCEntryAddrFromblockentryAddr *)
 (*fun (sh1entryaddr : paddr) (s : state) =>
exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) /\ 
Q sh1entryaddr s*)}}.
Proof.
unfold MAL.getKernelStructureStartAddr.
(*eapply bind. intro kernelStartAddr. apply ret.
eapply weaken.
apply Paddr.subPaddrIdx. intros. simpl in *. split. destruct H. apply H.

intuition. unfold StateLib.Paddr.subPaddrIdx in H1.*)

eapply bindRev.
eapply weaken.
apply Paddr.subPaddrIdx. intros. simpl. split. apply H.
intuition.
(*unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
	destruct H2. specialize (H blockentryaddr x).
	destruct H1. specialize (H H1). unfold entryBlockIndex in H2.
	rewrite H1 in H2. destruct H2.
	subst.
	apply isBELookupEq in H. destruct H.
	intuition.*)



intro kernelStartAddr. simpl. eapply weaken. apply ret.
intros. simpl. split. apply H.
intuition. unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
	destruct H5. destruct H4. specialize(H0 blockentryaddr x H4).
	
	unfold bentryBlockIndex in H5.
	rewrite H4 in H5.
	destruct H5.
	apply isBELookupEq in H0.
	destruct H0.
replace kernelStartAddr with (CPaddr (blockentryaddr - blockidx)).
	exists x0.
	split. rewrite H5. apply H0. reflexivity.
Qed.*)


(*Lemma CPaddr_add :
forall a : paddr, forall b c : index, CPaddr (CPaddr (a + c) + b) = CPaddr (a + b + c).
Proof.
	intros.
	assert(forall x : paddr, CPaddr (x) = x).
	{ intros. unfold CPaddr. destruct (lt_dec x maxAddr). cbn.

Qed.*)

(*
Lemma getSh1EntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (blockidx : index) (P : state -> Prop) : 
{{ fun s => P s /\ wellFormedFstShadowIfBlockEntry s 
								(*/\ BlockEntryAddrInBlocksRangeIsBE s*)
								/\ isBE kernelStartAddr s
								/\ blockidx < kernelStructureEntriesNb}}
MAL.getSh1EntryAddrFromKernelStructureStart kernelStartAddr blockidx
{{ fun (SHEAddr : ADT.paddr) (s : state) => P s /\ SHEAddr = CPaddr (kernelStartAddr + sh1offset + blockidx)
																								(*/\ SHEntryAddr (CPaddr (kernelStartAddr + blockidx)) SHEAddr s*) }}.
Proof.
	(*unfold MAL.getSh1EntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	unfold wellFormedFstShadowIfBlockEntry in H.
	destruct H. destruct H0.
	specialize (H0 (CPaddr (kernelStartAddr + blockidx))).

	destruct H1. unfold BlockEntryAddrInBlocksRangeIsBE in H1.
	specialize (H1 kernelStartAddr blockidx). destruct H2.
	intuition.*)

unfold MAL.getSh1EntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	unfold wellFormedFstShadowIfBlockEntry in H.
	destruct H. destruct H0.
	specialize (H0 (CPaddr (kernelStartAddr + blockidx))).
	destruct H1. reflexivity. 
Qed.

(*
	unfold SHEntryAddr.
	unfold isBE in H1.
	apply isBELookupEq in H1.
	destruct H1.
	rewrite H0.
	destruct (CPaddr (kernelStartAddr + sh1offset + blockidx)). 
	destruct (CPaddr (CPaddr (kernelStartAddr + blockidx) + sh1offset)).
	simpl. cbn.
simpl.


	apply H2 in H1.
	destruct H2.
	specialize (H1 H2 H3).
	unfold isBE in H0.
	destruct H1.
unfold SHEntryAddr.
	unfold isBE in H1.
	apply isBELookupEq in H1.
	destruct H1.
	rewrite H1 in H0. destruct H0 ; trivial.
	rewrite H1.
	destruct H0.
	Search (_=_).
	assert (forall a : paddr, forall b c : index, CPaddr (CPaddr (a + c) + b) = CPaddr (a + b + c)).
{
	intros. 
}
	rewrite <- H5. reflexivity.
Qed.


rewrite <- H4.
	unfold SHEntryAddr.
	destruct H0. rewrite H1.

destruct (lookup (CPaddr (kernelStartAddr + blockidx)) (memory s) beqAddr ).
	destruct v. simpl in *.
	destruct H0 ; trivial.
	unfold Paddr.addPaddrIdx in H1. 
	destruct H0. rewrite H1.

	destruct kernelStartAddr.
	destruct sh1offset.
	destruct blockidx.
	simpl.
	simpl.
	reflexivity.
 unfold isBE in H2.
	
 destruct H0.
	rewrite H1 in H0. destruct H0 ; trivial.
	unfold SCEntryAddr.
	rewrite H1. reflexivity.
Qed.*)


Lemma getSCEntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (blockidx : index) (P : state -> Prop) : 
{{fun s => 
					P s /\ wellFormedShadowCutIfBlockEntry s 
					/\ exists entry, lookup kernelStartAddr s.(memory) beqAddr = Some (BE entry)
							 }}
MAL.getSCEntryAddrFromKernelStructureStart kernelStartAddr blockidx
{{ fun scentryaddr s => P s /\ scentryaddr = CPaddr (kernelStartAddr + scoffset + blockidx)
															(* SCEntryAddr (CPaddr (kernelStartAddr + blockidx)) scentryaddr s*) 
}}.
Proof.
unfold MAL.getSCEntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	unfold wellFormedShadowCutIfBlockEntry in H.
	destruct H. destruct H0.
	specialize (H0 (CPaddr (kernelStartAddr + blockidx))).
	destruct H1. reflexivity.
Qed.

Lemma getSh1EntryAddrFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop) : 
{{fun s => Q s /\ wellFormedFstShadowIfBlockEntry s /\
					(*/\ P blockentryaddr s /\ *)
					  KernelStructureStartFromBlockEntryAddrIsBE s
							/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.getSh1EntryAddrFromBlockEntryAddr blockentryaddr
{{ fun sh1entryaddr s => Q s /\ exists sh1entry : Sh1Entry,
lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry) 
/\ sh1entryAddr blockentryaddr sh1entryaddr s
 (*fun (sh1entryaddr : paddr) (s : state) =>
exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) /\ 
Q sh1entryaddr s*)}}.
Proof.
unfold MAL.getSh1EntryAddrFromBlockEntryAddr.
eapply bindRev.
- eapply weaken. apply readBlockIndexFromBlockEntryAddr.
	intros. simpl. split. apply H.
	unfold isBE. destruct (lookup blockentryaddr (memory s) beqAddr).
	destruct v eqn:V; trivial ; destruct H ; destruct H0 ; destruct H1 ; destruct H2 ; congruence.
	destruct H. destruct H0. destruct H1. destruct H2. congruence.
- intro BlockEntryIndex.
	eapply bindRev. eapply weaken.
	apply getKernelStructureStartAddr.
	intros. simpl. split. exact H.
	intuition.
	destruct BlockEntryIndex. simpl. trivial.
	destruct blockentryaddr. simpl. trivial.
	destruct H5. exists x. split. apply H4.
	assumption.
	intro kernelStartAddr.
	intros.
	eapply bindRev.
{ 
	eapply weaken. apply getSh1EntryAddrFromKernelStructureStart.
	intros. simpl. split. exact H. split. apply H.
	intros. split. unfold isBE.
	intuition. destruct H1. destruct H1. rewrite H1. trivial.
	intuition. unfold bentryBlockIndex in *. destruct H6. rewrite H5 in H4.
	intuition.
}
(* Preuve : kernelStartAddr + blockindex est BE, donc +sh1offset est SHE
	blockentryindex < kernelstructurenb dans entryBlockIndex*)
	intro SHEAddr. eapply weaken. apply ret.
	intros. simpl. split. apply H.
	intuition.
	unfold wellFormedFstShadowIfBlockEntry in *.
	specialize (H3 blockentryaddr H0).
	unfold isSHE in *.
	destruct H2.
	destruct H2.
	rewrite H6 in H1.
	assert (CPaddr (CPaddr (blockentryaddr - BlockEntryIndex) + sh1offset + BlockEntryIndex)
					= CPaddr (blockentryaddr + sh1offset)).
	{ admit. }
	rewrite H8 in H1.
	rewrite <- H1 in H3.
	destruct (lookup SHEAddr (memory s) beqAddr). destruct v.
	exfalso ; congruence.
	exists s0. split. reflexivity. unfold sh1entryAddr. destruct H7. rewrite H7; trivial. 
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
Admitted.

(* DUP *)
Lemma getNextAddrFromKernelStructureStart  (kernelStartAddr : paddr) (P : state -> Prop) : 
{{fun s => P s (*/\ wellFormedNextKSAddrIfKernelStructureStart s *)
					/\ exists entry, lookup kernelStartAddr s.(memory) beqAddr = Some (BE entry)}}
MAL.getNextAddrFromKernelStructureStart kernelStartAddr
{{ fun nextaddr s => P s /\ nextaddr = CPaddr (kernelStartAddr + nextoffset) (*/\ exists entry, lookup nextaddr s.(memory) beqAddr = Some (PADDR entry)
/\ nextKSAddr nextksaddr nextksaddr s
/\ nextksaddr = CPaddr (kernelStartAddr + nextoffset)*)}}.
Proof.
unfold MAL.getNextAddrFromKernelStructureStart.
eapply weaken. apply ret.
intros. simpl. intuition. 
Qed.*)

(*Lemma getSh1EntryAddrFromBlockEntryAddr  (blockentryaddr : paddr) (Q : paddr -> state -> Prop) : 
{{fun s => (*wellFormedFstShadowIfBlockEntry s*)
					(*/\ P blockentryaddr s /\ *)
					exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.getSh1EntryAddrFromBlockEntryAddr blockentryaddr
{{fun (sh1entryaddr : paddr) (s : state) =>
(*exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) /\ *)
Q sh1entryaddr s}}.
Proof.
eapply weaken.
unfold MAL.getSh1EntryAddrFromBlockEntryAddr.
eapply bindRev.
- apply readBlockIndexFromBlockEntryAddr.
- intro BlockEntryIndex.
	eapply bindRev.
	apply getKernelStructureStartAddr.
	intro kernelStartAddr.
	eapply bindRev.
	eapply weaken.
	apply getSh1EntryAddrFromKernelStructureStart.
	intros. simpl. destruct H. destruct H0. exists x. apply H0.
	intro SHEAddr.
	apply ret.
- intros. simpl. destruct H as (C0 & (Hentry &Hprop)). (*destruct H.*) exists Hentry. split. 
	apply Hprop.
	pose (Htrue := P blockentryaddr s). apply Htrue. Hprop.
Qed.*)


(*
>>>>>>> Stashed changes
Lemma readSh1PDChildFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)  (*/\ 
             exists sh1entry, P sh1entry.(PDflag) s *)}}
MAL.readSh1PDChildFromBlockEntryAddr blockentryaddr
{{fun pdchild s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryPDchild sh1entryaddr pdchild s}}.
Proof.
unfold MAL.readSh1PDChildFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+
	intro sh1entryaddr. simpl. eapply bind.
	intros. apply ret.


	eapply weaken. apply readSh1PDChildFromBlockEntryAddr2.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	apply lookupSh1EntryPDchild. apply H0.
Qed.
<<<<<<< Updated upstream


=======
*)

(*
>>>>>>> Stashed changes
(* DUP *)
Lemma readSh1PDFlagFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)  (*/\ 
             exists sh1entry, P sh1entry.(PDflag) s *)}}
MAL.readSh1PDFlagFromBlockEntryAddr blockentryaddr
{{fun pdflag s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryPDflag sh1entryaddr pdflag s}}.
Proof.
unfold MAL.readSh1PDFlagFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+
	intro sh1entryaddr. simpl. eapply bind.
	intros. apply ret.


	eapply weaken. apply readSh1PDFlagFromBlockEntryAddr2.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	apply lookupSh1EntryPDflag. apply H0.
Qed.

(* DUP with deeper changes because of lookupSh1EntryInChildLocation *)
Lemma readSh1InChildLocationFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSh1InChildLocationFromBlockEntryAddr blockentryaddr
{{fun inchildlocation s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryInChildLocation sh1entryaddr inchildlocation s}}.
Proof.
unfold MAL.readSh1InChildLocationFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. unfold consistency in H. intuition.
+
	intro sh1entryaddr. simpl. eapply bind.
	intros. apply ret.


	eapply weaken. apply readSh1InChildLocationFromBlockEntryAddr2.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	apply lookupSh1EntryInChildLocation. apply H0. intuition.
Qed.
*)

(*
Lemma getSCEntryAddrFromBlockEntryAddr  (blockentryaddr : paddr) (P : state -> Prop) : 
{{fun s => (*wellFormedFstShadowIfBlockEntry s /\*)
					(*/\ P blockentryaddr s /\ *)
					P s /\ wellFormedShadowCutIfBlockEntry s /\ KernelStructureStartFromBlockEntryAddrIsBE s
					/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)
							 }}
MAL.getSCEntryAddrFromBlockEntryAddr blockentryaddr
{{ fun scentryaddr s => P s /\ exists entry, lookup scentryaddr s.(memory) beqAddr = Some (SCE entry)
																/\ scentryAddr blockentryaddr scentryaddr s 
(*/\ exists scentry : SCEntry,
lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry) *)
 (*fun (sh1entryaddr : paddr) (s : state) =>
exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry) /\ 
Q sh1entryaddr s*)}}.
Proof.
unfold MAL.getSCEntryAddrFromBlockEntryAddr.
eapply bindRev.
{ eapply weaken.
- apply readBlockIndexFromBlockEntryAddr.
- intros. cbn. split. exact H. (* NOTE : Important to propagate the whole property *)
unfold isBE. destruct H. destruct H0. destruct H1. destruct H2. rewrite H2. trivial.
}
intro BlockEntryIndex.
eapply bindRev.
{ eapply weaken.
- apply getKernelStructureStartAddr.
- intros. cbn. split. exact H. intuition.
	destruct BlockEntryIndex. simpl. trivial.
	destruct blockentryaddr. simpl. trivial. (* already done in sh1entry*)
	apply isBELookupEq in H0.
	destruct H0. exists x. intuition.
}
intro kernelStartAddr. simpl.
eapply bindRev.
{
	eapply weaken.  apply getSCEntryAddrFromKernelStructureStart.
	intros. simpl. split. apply H. intuition.
	intuition. destruct H1. exists x. apply H1.
}



(*
assert(
{{fun s => (*wellFormedFstShadowIfBlockEntry s /\*)
					(*/\ P blockentryaddr s /\ *)
					P s /\ wellFormedShadowCutIfBlockEntry s 
					/\ exists entry, lookup kernelStartAddr s.(memory) beqAddr = Some (BE entry)
							 }}
MAL.getSCEntryAddrFromKernelStructureStart kernelStartAddr
{{ fun scentryaddr s => P s /\ SCEntryAddr kernelStartAddr scentryaddr s }}).
{	
	unfold MAL.getSCEntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	unfold wellFormedShadowCutIfBlockEntry in H.
	destruct H. destruct H0.
	specialize (H0 kernelStartAddr).
	unfold isBE in H0. destruct H1.
	rewrite H1 in H0. destruct H0 ; trivial.
	unfold SCEntryAddr.
	rewrite H1. reflexivity.
 }

eapply weaken. apply H.

	intros. simpl. split.  apply H0. split. apply H0.
	destruct H0. destruct H1. exists x. exact H1.
}*)
	intro SCEAddr.
	eapply weaken. apply ret.
	intros. simpl.
	split. apply H.
	intuition.
	rewrite H1. destruct H2. destruct H2.
	unfold scentryAddr.
	destruct H7.
	rewrite H7.
	rewrite H6.
	unfold wellFormedShadowCutIfBlockEntry in *.
	specialize (H3 blockentryaddr H0).
	destruct H3. destruct H3.
	apply isSCELookupEq in H3.
	destruct H3. exists x2.
	assert (CPaddr (CPaddr (blockentryaddr - BlockEntryIndex) + scoffset + BlockEntryIndex)
					= CPaddr (blockentryaddr + scoffset)).
	{ admit. }
	split. subst.
	rewrite H9. assumption.
	assumption.
	
Admitted.*)
	
(*
	unfold MAL.getSCEntryAddrFromKernelStructureStart.
		apply ret.
intros. simpl.
	intuition.
	destruct H. apply H. destruct H. destruct H. destruct H2.
	unfold wellFormedShadowCutIfBlockEntry in *.
	specialize (H2 kernelStartAddr).
	unfold isBE in H2.
	destruct H1.
	rewrite H1 in H2.
	destruct H2 ; trivial.
	destruct H2. rewrite <- H5.
	apply isSCELookupEq in H2. assumption.

(*
	eapply bindRev.
{ eapply weaken.
	unfold MAL.getSCEntryAddrFromKernelStructureStart.
		apply ret.
	intros. simpl.
	intuition.
	destruct H3. destruct H2.
	unfold wellFormedShadowCutIfBlockEntry in *.
	specialize (H3 kernelStartAddr).
	unfold isBE in H3.
	destruct H1.
	rewrite H1 in H3.
	destruct H3 ; trivial.
	destruct H3. rewrite <- H5. exact H3.
}
intro SCEAddr.
	eapply weaken. apply ret.
	intros. simpl. split. exact (P s). unfold isSCE in *.



apply getSCEntryAddrFromKernelStructureStart.
	intros. cbn. destruct H. destruct H0. exists x.
 	split. assumption.

		unfold wellFormedShadowCutIfBlockEntry in *.
		specialize H with (entry := x).
specialize H with (pa := kernelStartAddr).
	
	destruct H as ((Hprop&HSCE) & Hidx) eqn:HFull.


	
	destruct HSCE as (be&(HBE&HSCE'')).
	unfold wellFormedShadowCutIfBlockEntry in HSCE''.
	specialize (HSCE'' kernelStartAddr).
	unfold isBE in H3.
	rewrite H0 in H3. destruct H3. trivial.
	destruct H3. rewrite <- H5.
	pose (Hprop := H0 /\ H2 /\ H1 /\ H4 /\ H3 /\ H5).

exact H3.
}
	intro SCEAddr.
	eapply weaken. apply ret.
	intros. simpl. split. exact P. unfold isSCE in *.



eapply bind. intro BlockEntryIndex.
eapply bind. intro kernelStartAddr.
eapply bind. intro SCEAddr.
apply ret.
eapply weaken.
apply WP.getSCEntryAddrFromKernelStructureStart.
intros. cbn. exact H.
eapply weaken. 
 apply WP.getKernelStructureStartAddr.

2 : { intros. exact H. }


eapply getKernelStructureStartAddr.

eapply bindRev.
- eapply weaken. apply readBlockIndexFromBlockEntryAddr.
	intros. simpl. destruct H. destruct H0. exists x. split. apply H0.
	apply H.
	unfold isBE. destruct (lookup blockentryaddr (memory s) beqAddr).
	destruct v eqn:V; trivial; destruct H ; destruct H0 ;destruct H1 ; congruence.
	destruct H. destruct H0. destruct H1. congruence.
- intro BlockEntryIndex.
	eapply bindRev.
	apply getKernelStructureStartAddr.
	intro kernelStartAddr.
	eapply bind.
	intros. apply ret.
	eapply weaken.
	unfold MAL.getSh1EntryAddrFromKernelStructureStart.
	apply ret.
	intros. simpl.
	split. apply H.
	intuition.
	unfold wellFormedFstShadowIfBlockEntry in H0.
	unfold isBE in H0.
	unfold isSHE in H0.
	destruct H1.
	pose proof (H0 kernelStartAddr). destruct (lookup kernelStartAddr (memory s) beqAddr) eqn:Hlookup in H3.
	destruct v eqn:Hv in H3. simpl in H3. destruct H3. trivial.
	destruct H3. destruct (lookup x0 (memory s) beqAddr) eqn:Hlookup' in H3.
	destruct v0 eqn:Hv' in H3.
	exfalso ; congruence.
	exists s0. rewrite <- H5. rewrite -> Hlookup'. rewrite -> Hv'. reflexivity.
	repeat exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.
	exfalso ; congruence.*)
Qed.*)


(*Lemma writeSCOriginFromBlockEntryAddr  (entryaddr : paddr) (neworigin : ADT.paddr)  (P : state -> Prop) :
{{fun s => P s /\ exists entry : BlockEntry,
  lookup entryaddr (memory s) beqAddr = Some (BE entry) /\
  wellFormedShadowCutIfBlockEntry s}}
writeSCOriginFromBlockEntryAddr entryaddr neworigin  {{fun _ s => P s}}.
Proof.

unfold writeSCOriginFromBlockEntryAddr.
eapply bindRev.
{ eapply weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. split. exact H.
	destruct H. destruct H0. exists x. apply H0.
}
	intro SCEAddr.
{
	eapply weaken. apply WP.writeSCOriginFromBlockEntryAddr2. apply SCEAddr.
	intros. simpl. destruct H. destruct H0. exists x.

	apply H3.
	assumption.
eapply H2. 
	specialize (H2 x SCEAddr).
destruct H2.
	destruct H2. destruct H2. apply H3.
	specialize (H2 SCEAddr). intuition.
}*)

(*
Lemma readSCOriginFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSCOriginFromBlockEntryAddr blockentryaddr
{{fun origin s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists scentry : SCEntry, exists scentryaddr : paddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry)
										/\ scentryOrigin scentryaddr origin s}}.
Proof.
unfold MAL.readSCOriginFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+
	intro scentryaddr. simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply readSCOriginFromBlockEntryAddr2.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists scentryaddr. split. apply H0.
	apply lookupSCEntryOrigin. apply H0.
Qed.
*)

Lemma writeSCOriginFromBlockEntryAddr  (entryaddr : paddr) (neworigin : ADT.paddr)  (P : unit -> state -> Prop) :
{{fun  s => (*exists blockentry , lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\*)
						isBE entryaddr s 
						/\ wellFormedShadowCutIfBlockEntry s
						/\ KernelStructureStartFromBlockEntryAddrIsBE s
						(*exists entry , exists scentryaddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE entry) /\ *)
/\ exists entry , lookup (CPaddr (entryaddr + scoffset)) s.(memory) beqAddr = Some (SCE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add (CPaddr (entryaddr + scoffset))
              (SCE {| origin := neworigin ; next := entry.(next) |})
              (memory s) beqAddr |} }}
writeSCOriginFromBlockEntryAddr entryaddr neworigin  {{P}}.
Proof.
unfold MAL.writeSCOriginFromBlockEntryAddr.
eapply bindRev.
{ eapply weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
 apply isBELookupEq in H0 ;trivial.
}
	intro SCEAddr.
{ cbn. eapply weaken. eapply WP.writeSCOriginFromBlockEntryAddr2.
	cbn.
	intros. simpl. destruct H.
	intuition.
	unfold scentryAddr in H0.
	apply isBELookupEq in H1. destruct H1.
	rewrite H1 in H0.
	destruct H0. destruct H0.
	subst.
	assumption.
}
Qed.


(* DUP with changes in scentryNext + lookupSCEntryNext + changes of function names*)
(*Lemma readSCNextFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSCNextFromBlockEntryAddr blockentryaddr
{{fun next s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists scentry : SCEntry, exists scentryaddr : paddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry)
										/\ scentryNext scentryaddr next s}}.
Proof.
unfold MAL.readSCNextFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+
	intro scentryaddr. simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply readSCNextFromBlockEntryAddr2.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists scentryaddr. split. apply H0.
	apply lookupSCEntryNext. apply H0.
Qed.*)


Lemma writeSh1PDChildFromBlockEntryAddr (blockentryaddr pdchild : paddr)  (P : unit -> state -> Prop) :
{{fun  s => (*exists blockentry , lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\*)
						 exists entry , lookup (CPaddr (blockentryaddr + sh1offset)) s.(memory) beqAddr = Some (SHE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add (CPaddr (blockentryaddr + sh1offset))
              (SHE {|	PDchild := pdchild;
											PDflag := entry.(PDflag);
											inChildLocation := entry.(inChildLocation) |})
              (memory s) beqAddr |} 
/\ isBE blockentryaddr s 
						/\ wellFormedFstShadowIfBlockEntry s
						/\ KernelStructureStartFromBlockEntryAddrIsBE s
						(*exists entry , exists scentryaddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE entry) /\ *)
 }}
MAL.writeSh1PDChildFromBlockEntryAddr blockentryaddr pdchild  {{P}}.
Proof.
eapply bindRev.
{ eapply weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. destruct H. intuition.
 apply isBELookupEq in H1 ;trivial.
}
	intro Sh1EAddr.
{ cbn. eapply weaken. eapply WP.writeSh1PDChildFromBlockEntryAddr2.	cbn.
	intros. simpl. destruct H. destruct H.
	intuition.
	unfold sh1entryAddr in *.
	apply isBELookupEq in H2. destruct H2.
	rewrite H2 in H0.
	destruct H0. destruct H0.
	subst. exists x. split.
	assumption. assumption.
}
Qed.


(*
Lemma readSh1PDFlagFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop) : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)  (*/\ 
             exists sh1entry, P sh1entry.(PDflag) s *)}}
MAL.readSh1PDFlagFromBlockEntryAddr blockentryaddr
{{fun isPD s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ entryPDFlag sh1entryaddr isPD s}}.
Proof.
unfold MAL.readSh1PDFlagFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros.  intuition. unfold consistency in H. apply H. apply H0.
+
	intro sh1entryaddr. simpl. eapply bind.
	intros. apply ret.


	eapply weaken. apply readSh1PDFlagFromBlockEntryAddr2.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	apply lookupEntryPDFlag. apply H0.
Qed.*)

(* DUP*)
Lemma writeSh1InChildLocationFromBlockEntryAddr (blockentryaddr newinchildlocation : paddr)  (P : unit -> state -> Prop) :
{{fun  s => (*exists blockentry , lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\*)
						 exists entry , lookup (CPaddr (blockentryaddr + sh1offset)) s.(memory) beqAddr = Some (SHE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add (CPaddr (blockentryaddr + sh1offset))
              (SHE {|	PDchild := entry.(PDchild);
											PDflag := entry.(PDflag);
											inChildLocation := newinchildlocation |})
              (memory s) beqAddr |} 
/\ isBE blockentryaddr s 
						/\ wellFormedFstShadowIfBlockEntry s
						/\ KernelStructureStartFromBlockEntryAddrIsBE s
						(*exists entry , exists scentryaddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE entry) /\ *)
 }}
MAL.writeSh1InChildLocationFromBlockEntryAddr blockentryaddr newinchildlocation  {{P}}.
Proof.
eapply bindRev.
{ eapply weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. destruct H. intuition.
 apply isBELookupEq in H1 ;trivial.
}
	intro Sh1EAddr.
{ cbn. eapply weaken. eapply WP.writeSh1InChildLocationFromBlockEntryAddr2.	cbn.
	intros. simpl. destruct H. destruct H.
	intuition.
	unfold sh1entryAddr in *.
	apply isBELookupEq in H2. destruct H2.
	rewrite H2 in H0.
	destruct H0. destruct H0.
	subst. exists x. split.
	assumption. assumption.
}
Qed.


(*
Lemma readSCOriginFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSCOriginFromBlockEntryAddr blockentryaddr
{{fun origin s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists scentry : SCEntry, exists scentryaddr : paddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry)
										/\ scentryOrigin scentryaddr origin s}}.
Proof.
unfold MAL.readSCOriginFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+
	intro scentryaddr. simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply readSCOriginFromBlockEntryAddr2.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists scentryaddr. split. apply H0.
	apply lookupSCEntryOrigin. apply H0.
Qed.*)

(*
Lemma writeSCOriginFromBlockEntryAddr  (entryaddr : paddr) (neworigin : ADT.paddr)  (P : unit -> state -> Prop) :
{{fun  s => (*exists blockentry , lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\*)
						isBE entryaddr s 
						/\ wellFormedShadowCutIfBlockEntry s
						/\ KernelStructureStartFromBlockEntryAddrIsBE s
						(*exists entry , exists scentryaddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE entry) /\ *)
/\ exists entry , lookup (CPaddr (entryaddr + scoffset)) s.(memory) beqAddr = Some (SCE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add (CPaddr (entryaddr + scoffset))
              (SCE {| origin := neworigin ; next := entry.(next) |})
              (memory s) beqAddr |} }}
writeSCOriginFromBlockEntryAddr entryaddr neworigin  {{P}}.
Proof.
unfold MAL.writeSCOriginFromBlockEntryAddr.
eapply bindRev.
{ eapply weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
 apply isBELookupEq in H0 ;trivial.
}
	intro SCEAddr.
{ cbn. eapply weaken. eapply WP.writeSCOriginFromBlockEntryAddr2.
	cbn.
	intros. simpl. destruct H.
	intuition.
	unfold scentryAddr in H0.
	apply isBELookupEq in H1. destruct H1.
	rewrite H1 in H0.
	destruct H0. destruct H0.
	subst.
	assumption.
}
Qed.*)

(*
(* DUP with changes in scentryNext + lookupSCEntryNext + changes of function names*)
Lemma readSCNextFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  : 
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSCNextFromBlockEntryAddr blockentryaddr
{{fun next s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists scentry : SCEntry, exists scentryaddr : paddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry)
										/\ scentryNext scentryaddr next s}}.
Proof.
unfold MAL.readSCNextFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. intuition.
+
	intro scentryaddr. simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply readSCNextFromBlockEntryAddr2.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists scentryaddr. split. apply H0.
	apply lookupSCEntryNext. apply H0.
Qed.*)

(*
>>>>>>> Stashed changes
Lemma readNextFromKernelStructureStart (structurepaddr : paddr) (P : state -> Prop)  : 
{{fun s  =>  P s (*/\ consistency s /\*) /\ NextKSOffsetIsPADDR s /\
						isKS structurepaddr s
						(*isPADDR (CPaddr (structurepaddr + nextoffset)) s*)
             }}
MAL.readNextFromKernelStructureStart structurepaddr
{{fun nextkernelstructure s => P s 
																/\ exists offset, (offset = CPaddr (structurepaddr + nextoffset)
																/\ nextKSAddr offset nextkernelstructure s)
 (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										(*/\ nextKSAddr nextaddr nextkernelstructure s*)}}.
Proof.
unfold MAL.readNextFromKernelStructureStart.
eapply WP.bindRev.
+   eapply WP.weaken. apply getNextAddrFromKernelStructureStart.
	intros. simpl. split. apply H. intuition. apply isKSLookupEq in H2.
	assumption.
+ intro nextaddr. (*
	eapply bindRev.
	{ eapply weaken. apply readNextFromKernelStructureStart2.
		intros. simpl.*)
simpl. eapply bind.
	intros. apply ret.


	eapply weaken. apply readNextFromKernelStructureStart2.
	intros. simpl. intuition. subst.
	 unfold NextKSOffsetIsPADDR in H0.
	specialize (H0 structurepaddr (CPaddr (structurepaddr + nextoffset)) H3).
	intuition. unfold isPADDR in H2.

	destruct (lookup (CPaddr (structurepaddr + nextoffset)) (memory s) beqAddr) eqn:Hlookup ; intuition.
	destruct v eqn:Hv ; intuition.
	exists p. intuition. subst. 
	eexists. intuition. unfold nextKSAddr. rewrite Hlookup ; trivial.
<<<<<<< Updated upstream
Qed.
=======
Qed.*)

Lemma checkEntry  (kernelstructurestart blockentryaddr : paddr) (P :  state -> Prop) :
{{fun s => P s

(*/\ exists bentry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE bentry)*) }}
MAL.checkEntry kernelstructurestart blockentryaddr
{{fun isValidentry s => P s /\ (isValidentry = true -> isBE blockentryaddr s)}}.
Proof.
eapply weaken. apply WeakestPreconditions.checkEntry.
intros.  simpl. intuition.
unfold entryExists in *. unfold isBE.
destruct (lookup blockentryaddr (memory s) beqAddr) eqn:Hlookup.
destruct v eqn:Hv ; trivial ; intuition. intuition.
Qed.
