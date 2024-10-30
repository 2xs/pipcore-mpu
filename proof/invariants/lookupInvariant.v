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

Require Import Model.ADT Model.Monad Model.MAL Model.Lib.
Require Import Proof.Consistency Proof.StateLib.
Require Import InternalLemmas.
Require Import List Coq.Logic.ProofIrrelevance Lia Classical_Prop Compare_dec EqNat Arith
  FunctionalExtensionality.

Lemma getFreeSlotsListRecEqLookup n freeslotaddr nbfreeslotsleft s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getFreeSlotsListRec n freeslotaddr s nbfreeslotsleft
= getFreeSlotsListRec n freeslotaddr s0 nbfreeslotsleft.
Proof.
intro HlookupEq. revert freeslotaddr nbfreeslotsleft. induction n; intros.
- rewrite FreeSlotsListRec_unroll. rewrite FreeSlotsListRec_unroll. simpl. reflexivity.
- rewrite FreeSlotsListRec_unroll. rewrite FreeSlotsListRec_unroll. simpl. rewrite HlookupEq.
  destruct (lookup freeslotaddr (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
  destruct (Index.pred nbfreeslotsleft); try(reflexivity). f_equal. apply IHn.
Qed.

Lemma getFreeSlotsListEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getFreeSlotsList partition s = getFreeSlotsList partition s0.
Proof.
intro HlookupEq. unfold getFreeSlotsList. rewrite HlookupEq.
destruct (lookup partition (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
destruct (beqAddr (firstfreeslot p) nullAddr); try(reflexivity).
apply getFreeSlotsListRecEqLookup. assumption.
Qed.

Lemma getKSEntriesInStructAuxEqLookup n kernel iterleft s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getKSEntriesInStructAux n kernel s iterleft = getKSEntriesInStructAux n kernel s0 iterleft.
Proof.
intro HlookupEq. revert kernel iterleft. induction n; intros; simpl; try(reflexivity).
destruct (Paddr.addPaddrIdx kernel iterleft); try(reflexivity). rewrite HlookupEq.
destruct (lookup p (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
destruct (indexEq iterleft zero); try(reflexivity). destruct (Index.pred iterleft); try(reflexivity).
f_equal. apply IHn.
Qed.

Lemma getKSEntriesAuxEqLookup n partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getKSEntriesAux n partition s = getKSEntriesAux n partition s0.
Proof.
intro HlookupEq. revert partition. induction n; intro; simpl; try(reflexivity).
destruct (Paddr.addPaddrIdx partition nextoffset); try(reflexivity). rewrite HlookupEq.
destruct (lookup p (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity). rewrite HlookupEq.
destruct (lookup p0 (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
- f_equal; try(apply IHn). apply getKSEntriesInStructAuxEqLookup. assumption.
- destruct (beqAddr p0 nullAddr); try(reflexivity). apply getKSEntriesInStructAuxEqLookup. assumption.
Qed.

Lemma getKSEntriesEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getKSEntries partition s = getKSEntries partition s0.
Proof.
intro HlookupEq. unfold getKSEntries. rewrite HlookupEq.
destruct (lookup partition (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
destruct (beqAddr (structure p) nullAddr); try(reflexivity). apply getKSEntriesAuxEqLookup. assumption.
Qed.

Lemma getMappedBlocksEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getMappedBlocks partition s = getMappedBlocks partition s0.
Proof.
intro HlookupEq. unfold getMappedBlocks. rewrite getKSEntriesEqLookup with partition s s0; try(assumption).
induction (filterOptionPaddr (getKSEntries partition s0)); simpl; try(reflexivity). rewrite HlookupEq.
destruct (lookup a (memory s0) beqAddr); try(assumption). destruct v; try(assumption).
destruct (present b); try(assumption). f_equal. assumption.
Qed.

Lemma childFilterEqLookup s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> childFilter s = childFilter s0.
Proof.
intro HlookupEq. unfold childFilter. apply functional_extensionality. intro x. rewrite HlookupEq.
destruct (lookup x (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
destruct (Paddr.addPaddrIdx x sh1offset); try(reflexivity). rewrite HlookupEq.
destruct (lookup p (memory s0) beqAddr); try(reflexivity).
Qed.

Lemma getChildrenEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getChildren partition s = getChildren partition s0.
Proof.
intro HlookupEq. unfold getChildren. rewrite HlookupEq.
destruct (lookup partition (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
rewrite getMappedBlocksEqLookup with partition s s0; try(assumption). unfold getPDs.
rewrite childFilterEqLookup with s s0; try(assumption).
induction (getMappedBlocks partition s0); simpl; try(reflexivity).
destruct (childFilter s0 a); try(assumption). simpl. rewrite HlookupEq.
destruct (lookup a (memory s0) beqAddr); try(f_equal; try(reflexivity); assumption).
Qed.

Lemma getPartitionsAuxEqLookup n partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getPartitionsAux n partition s = getPartitionsAux n partition s0.
Proof.
intro HlookupEq. revert partition. induction n; intro; simpl; try(reflexivity). f_equal.
rewrite getChildrenEqLookup with partition s s0; try(assumption).
induction (getChildren partition s0); simpl; try(reflexivity). rewrite IHl. f_equal. apply IHn.
Qed.

Lemma getPartitionsEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getPartitions partition s = getPartitions partition s0.
Proof.
intro HlookupEq. unfold getPartitions. apply getPartitionsAuxEqLookup. assumption.
Qed.

Lemma getAllPaddrPDTAuxEqLookup l s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getAllPaddrPDTAux l s = getAllPaddrPDTAux l s0.
Proof.
intro HlookupEq. induction l; simpl; try(reflexivity). rewrite HlookupEq.
destruct (lookup a (memory s0) beqAddr); try(assumption). destruct v; try(assumption). f_equal. assumption.
Qed.

Lemma getAllPaddrConfigAuxEqLookup l s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getAllPaddrConfigAux l s = getAllPaddrConfigAux l s0.
Proof.
intro HlookupEq. induction l; simpl; try(reflexivity). rewrite HlookupEq.
destruct (lookup a (memory s0) beqAddr); try(assumption). destruct v; try(assumption). f_equal. assumption.
Qed.

Lemma getConfigBlocksAuxEqLookup n kernel nbleft s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getConfigBlocksAux n kernel s nbleft = getConfigBlocksAux n kernel s0 nbleft.
Proof.
intro HlookupEq. revert kernel nbleft. induction n; intros; simpl; try(reflexivity). rewrite HlookupEq.
destruct (lookup kernel (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
destruct (Paddr.addPaddrIdx kernel nextoffset); try(reflexivity). rewrite HlookupEq.
destruct (lookup p (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
destruct (Index.pred nbleft); try(reflexivity). f_equal. apply IHn.
Qed.

Lemma getConfigBlocksEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getConfigBlocks partition s = getConfigBlocks partition s0.
Proof.
intro HlookupEq. unfold getConfigBlocks. rewrite HlookupEq.
destruct (lookup partition (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
rewrite getConfigBlocksAuxEqLookup with (maxIdx + 1) (structure p) (CIndex maxNbPrepare) s s0;
    try(assumption). reflexivity.
Qed.

Lemma getConfigPaddrEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getConfigPaddr partition s = getConfigPaddr partition s0.
Proof.
intro HlookupEq. unfold getConfigPaddr.
rewrite getAllPaddrPDTAuxEqLookup with (partition :: nil) s s0; try(assumption). f_equal.
rewrite getConfigBlocksEqLookup with partition s s0; try(assumption).
apply getAllPaddrConfigAuxEqLookup. assumption.
Qed.

Lemma getAllPaddrAuxEqLookup l s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getAllPaddrAux l s = getAllPaddrAux l s0.
Proof.
intro HlookupEq. induction l; simpl; try(reflexivity). rewrite HlookupEq.
destruct (lookup a (memory s0) beqAddr); try(assumption). destruct v; try(assumption). f_equal. assumption.
Qed.

Lemma getMappedPaddrEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getMappedPaddr partition s = getMappedPaddr partition s0.
Proof.
intro HlookupEq. unfold getMappedPaddr.
rewrite getMappedBlocksEqLookup with partition s s0; try(assumption).
apply getAllPaddrAuxEqLookup. assumption.
Qed.

Lemma getUsedPaddrEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getUsedPaddr partition s = getUsedPaddr partition s0.
Proof.
intro HlookupEq. unfold getUsedPaddr.
rewrite getMappedPaddrEqLookup with partition s s0; try(assumption). f_equal.
apply getConfigPaddrEqLookup. assumption.
Qed.

Lemma getAccessibleMappedBlocksEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0.
Proof.
intro HlookupEq. unfold getAccessibleMappedBlocks. rewrite HlookupEq.
destruct (lookup partition (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
rewrite getMappedBlocksEqLookup with partition s s0; try(assumption).
induction (getMappedBlocks partition s0); simpl; try(reflexivity). rewrite HlookupEq.
destruct (lookup a (memory s0) beqAddr); try(assumption). destruct v; try(assumption).
destruct (accessible b); try(assumption). f_equal. assumption.
Qed.

Lemma getAccessibleMappedPaddrEqLookup partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0.
Proof.
intro HlookupEq. unfold getAccessibleMappedPaddr.
rewrite getAccessibleMappedBlocksEqLookup with partition s s0; try(assumption).
rewrite getAllPaddrAuxEqLookup with (getAccessibleMappedBlocks partition s0) s s0; try(assumption).
reflexivity.
Qed.

Lemma isListOfKernelsAuxEqLookup kernList kern s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isListOfKernelsAux kernList kern s = isListOfKernelsAux kernList kern s0.
Proof.
intro HlookupEq. revert kern. induction kernList; intro; simpl; try(reflexivity). f_equal. f_equal.
apply HlookupEq. f_equal. f_equal. apply IHkernList.
Qed.

Lemma isListOfKernelsEqLookup kernList partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isListOfKernels kernList partition s = isListOfKernels kernList partition s0.
Proof.
intro HlookupEq. unfold isListOfKernels. destruct kernList; try(reflexivity). rewrite HlookupEq.
rewrite isListOfKernelsAuxEqLookup with kernList p s s0; try(assumption). reflexivity.
Qed.

Lemma isParentsListEqLookup parentsList partition s s0:
(forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isParentsList s parentsList partition = isParentsList s0 parentsList partition.
Proof.
intro HlookupEq. revert partition. induction parentsList; intro; simpl; try(reflexivity). rewrite HlookupEq.
destruct (lookup a (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity). rewrite HlookupEq.
f_equal. f_equal. apply IHparentsList.
Qed.
