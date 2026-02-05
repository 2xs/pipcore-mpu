(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
(*  Copyright (C) 2020-2024 Orange                                             *)
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
    This file contains several internal lemmas to help prove DeletePartition *)
From Stdlib Require Import List Lia EqNat Arith Classical_Prop FunctionalExtensionality.
Import Compare_dec.
Require Import Model.ADT Model.Monad Model.MAL Model.Lib Core.Internal.

Require Import StateLib DependentTypeLemmas InternalLemmas InternalLemmas2.
Require Import Proof.Isolation Proof.Consistency.

Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.Program.Equality.

Module DTL := DependentTypeLemmas.

Import List.ListNotations.

Lemma getKSEntriesInStructAuxEqRemoveAddr n block s0 s idx removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> getKSEntriesInStructAux n block s idx = getKSEntriesInStructAux n block s0 idx.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert block idx. induction n; intros block idx; simpl; trivial.
destruct (Paddr.addPaddrIdx block idx); trivial.
destruct (beqAddr p removedAddr) eqn:HbeqPRemoved.
- rewrite <-DTL.beqAddrTrue in HbeqPRemoved. subst p. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  destruct (lookup p (memory s0) beqAddr); trivial. destruct v; trivial. destruct (indexEq idx zero); trivial.
  destruct (Index.pred idx); trivial. rewrite IHn. reflexivity.
Qed.

Lemma getKSEntriesAuxEqRemoveAddr n block s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> getKSEntriesAux n block s = getKSEntriesAux n block s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert block. induction n; intro block; simpl; trivial.
destruct (Paddr.addPaddrIdx block nextoffset) eqn:Hadd; trivial.
destruct (beqAddr p removedAddr) eqn:HbeqPRemoved.
- rewrite <-DTL.beqAddrTrue in HbeqPRemoved. subst p. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
  destruct (lookup p (memory s0) beqAddr); trivial. destruct v; trivial.
  destruct (beqAddr p0 removedAddr) eqn:HbeqP0Removed.
  + rewrite <-DTL.beqAddrTrue in HbeqP0Removed. subst p0. rewrite HlookupRemoved. unfold isPDT in *.
    destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  + rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. rewrite IHn.
    assert(HstrAuxEq: getKSEntriesInStructAux (maxIdx + 1) block s (CIndex 7)
      = getKSEntriesInStructAux (maxIdx + 1) block s0 (CIndex 7)).
    { revert HremovedIsPDT. apply getKSEntriesInStructAuxEqRemoveAddr; trivial. }
    rewrite HstrAuxEq. reflexivity.
Qed.

Lemma getKSEntriesEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> getKSEntries part s = getKSEntries part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold getKSEntries. rewrite HlookupsEq; trivial.
destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull; trivial. revert HremovedIsPDT.
apply getKSEntriesAuxEqRemoveAddr; assumption.
Qed.

Lemma getMappedBlocksEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> getMappedBlocks part s = getMappedBlocks part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold getMappedBlocks.
assert(HkernsEq: getKSEntries part s = getKSEntries part s0).
{ revert HbeqPartRemoved. apply getKSEntriesEqRemoveAddr; assumption. }
rewrite HkernsEq. induction (filterOptionPaddr (getKSEntries part s0)); trivial. simpl. rewrite IHl.
destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
- rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getChildrenImplRemoveAddr part partBase s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> In part (getChildren partBase s)
-> In part (getChildren partBase s0).
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HpartIsChild. unfold getChildren in *.
assert(partBase <> removedAddr).
{
  intro. subst partBase. rewrite HlookupRemoved in *. simpl in *. congruence.
}
rewrite HlookupsEq in HpartIsChild; trivial.
destruct (lookup partBase (memory s0) beqAddr); try(simpl in *; congruence).
destruct v; try(simpl in *; congruence).
assert(HgetMappedEq: getMappedBlocks partBase s = getMappedBlocks partBase s0).
{ apply getMappedBlocksEqRemoveAddr with removedAddr; assumption. }
rewrite HgetMappedEq in *. clear HgetMappedEq.
induction (getMappedBlocks partBase s0); simpl in *; try(congruence). unfold getPDs in *. simpl in *.
assert(HchildFEq: childFilter s a = childFilter s0 a).
{
  unfold childFilter. destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
  - rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved. unfold isPDT in *.
    destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  - rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
    destruct (lookup a (memory s0) beqAddr); trivial. destruct v; trivial.
    destruct (Paddr.addPaddrIdx a sh1offset); trivial. destruct (beqAddr p0 removedAddr) eqn:HbeqP0Removed.
    + rewrite <-DTL.beqAddrTrue in HbeqP0Removed. subst p0. rewrite HlookupRemoved. unfold isPDT in *.
      destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). trivial.
    + rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
}
rewrite HchildFEq in *. destruct (childFilter s0 a); try(apply IHl; assumption). simpl in *.
destruct HpartIsChild as [Hfirst | HpartIsChild]; try(right; apply IHl; assumption). left.
destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
- rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved in *. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq in Hfirst; trivial.
Qed.

Lemma getPartitionsImplRemoveAddrAux n part partBase s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> In part (getPartitionsAux n partBase s)
-> In part (getPartitionsAux n partBase s0).
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert part partBase.
induction n; simpl; intros part partBase HpartIsPart; try(congruence).
destruct HpartIsPart as [HpartsEq | HpartIsPart]; auto. right.
assert(HgetChildrenImpl: forall partB, In partB (getChildren partBase s) -> In partB (getChildren partBase s0)).
{ intro partB. apply getChildrenImplRemoveAddr with removedAddr; assumption. }
induction (getChildren partBase s); simpl in *; try(exfalso; congruence).
assert(HgetChildrenImplRec: forall partB : paddr, In partB l -> In partB (getChildren partBase s0)).
{ intros. apply HgetChildrenImpl; auto. }
apply in_app_or in HpartIsPart. destruct HpartIsPart as [HpartInA | HpartIsPart]; try(apply IHl; assumption).
clear IHl. clear HgetChildrenImplRec. assert(HpropsOr: a = a \/ In a l) by auto.
specialize(HgetChildrenImpl a HpropsOr). clear HpropsOr. apply IHn in HpartInA. clear IHn.
induction (getChildren partBase s0); simpl in *; try(congruence).
destruct HgetChildrenImpl as [Heq | HgetChildrenImpl].
- subst a0. apply in_or_app. auto.
- apply in_or_app. right. apply IHl0; assumption.
Qed.

Lemma getPartitionsImplRemoveAddr part partBase s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> In part (getPartitions partBase s)
-> In part (getPartitions partBase s0).
Proof.
unfold getPartitions. apply getPartitionsImplRemoveAddrAux.
Qed.

Lemma getChildrenEqRemoveAddr partBase s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> partBase <> removedAddr
-> getChildren partBase s = getChildren partBase s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqBaseRemoved. unfold getChildren.
rewrite HlookupsEq; trivial.
destruct (lookup partBase (memory s0) beqAddr); trivial. destruct v; trivial.
assert(HgetMappedEq: getMappedBlocks partBase s = getMappedBlocks partBase s0).
{ apply getMappedBlocksEqRemoveAddr with removedAddr; assumption. }
rewrite HgetMappedEq. clear HgetMappedEq.
induction (getMappedBlocks partBase s0); simpl; trivial. unfold getPDs in *. simpl.
assert(HchildFEq: childFilter s a = childFilter s0 a).
{
  unfold childFilter. destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
  - rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved. unfold isPDT in *.
    destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  - rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
    destruct (lookup a (memory s0) beqAddr); trivial. destruct v; trivial.
    destruct (Paddr.addPaddrIdx a sh1offset); trivial. destruct (beqAddr p0 removedAddr) eqn:HbeqP0Removed.
    + rewrite <-DTL.beqAddrTrue in HbeqP0Removed. subst p0. rewrite HlookupRemoved. unfold isPDT in *.
      destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). trivial.
    + rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
}
rewrite HchildFEq. destruct (childFilter s0 a); try(apply IHl). simpl. rewrite IHl. f_equal.
destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
- rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getPartitionsAuxImplRemoveAddrRev n part partBase s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> In part (getPartitionsAux n partBase s0)
-> In part (getPartitionsAux n partBase s) \/ In part (getPartitionsAux n removedAddr s0).
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert part partBase.
induction n; intros part partBase HpartIn; simpl in HpartIn; try(exfalso; congruence). rewrite <-Nat.add_1_r at 2.
simpl. destruct HpartIn as [HpartsEq | HpartIn]; auto.
destruct (beqAddr partBase removedAddr) eqn:HbeqBaseRemoved.
- rewrite <-DTL.beqAddrTrue in HbeqBaseRemoved. subst partBase. right. rewrite Nat.add_1_r. simpl. auto.
- rewrite <-beqAddrFalse in *.
  assert(HgetChildrenEq: getChildren partBase s = getChildren partBase s0).
  { apply getChildrenEqRemoveAddr with removedAddr; assumption. }
  rewrite HgetChildrenEq. clear HgetChildrenEq.
  induction (getChildren partBase s0); simpl in *; try(exfalso; congruence). apply in_app_or in HpartIn.
  destruct HpartIn as [HpartInA | HpartIn].
  + apply IHn in HpartInA. destruct HpartInA as [HpartInA | HpartInRemoved].
    * left. right. apply in_or_app. auto.
    * right. apply getPartitionsAuxSbound; assumption.
  + apply IHl in HpartIn. destruct HpartIn as [HpartIn | HpartInRemoved]; auto. left. destruct HpartIn; auto.
    right. apply in_or_app. auto.
Qed.

Lemma getPartitionsImplRemoveAddrRev part partBase s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> In part (getPartitions partBase s0)
-> In part (getPartitions partBase s) \/ In part (getPartitions removedAddr s0).
Proof.
unfold getPartitions. apply getPartitionsAuxImplRemoveAddrRev.
Qed.

Lemma getAccessibleMappedBlocksEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold getAccessibleMappedBlocks.
assert(HgetMappedEq: getMappedBlocks part s = getMappedBlocks part s0).
{ revert HbeqPartRemoved. apply getMappedBlocksEqRemoveAddr; assumption. }
rewrite HgetMappedEq. rewrite HlookupsEq; trivial.
destruct (lookup part (memory s0) beqAddr); trivial. destruct v; trivial. clear HgetMappedEq.
induction (getMappedBlocks part s0); trivial. simpl. rewrite IHl.
destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
- rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getMappedPaddrEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> getMappedPaddr part s = getMappedPaddr part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold getMappedPaddr.
assert(HgetMappedEq: getMappedBlocks part s = getMappedBlocks part s0).
{ revert HbeqPartRemoved. apply getMappedBlocksEqRemoveAddr; assumption. }
rewrite HgetMappedEq. clear HgetMappedEq. induction (getMappedBlocks part s0); trivial. simpl. rewrite IHl.
destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
- rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getAccessibleMappedPaddrEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold getAccessibleMappedPaddr.
assert(HgetAccMappedEq: getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s0).
{ revert HbeqPartRemoved. apply getAccessibleMappedBlocksEqRemoveAddr; assumption. }
rewrite HgetAccMappedEq. clear HgetAccMappedEq.
induction (getAccessibleMappedBlocks part s0); trivial. simpl. rewrite IHl.
destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
- rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getConfigBlocksAuxEqRemoveAddr n block nbleft s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> getConfigBlocksAux n block s nbleft = getConfigBlocksAux n block s0 nbleft.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert block nbleft.
induction n; simpl; intros block nbleft; trivial.
destruct (beqAddr block removedAddr) eqn:HbeqBlockRemoved.
- rewrite <-DTL.beqAddrTrue in HbeqBlockRemoved. subst block. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. destruct (lookup block (memory s0) beqAddr); trivial.
  destruct v; trivial. destruct (Paddr.addPaddrIdx block nextoffset); trivial.
  destruct (beqAddr p removedAddr) eqn:HbeqPRemoved.
  + rewrite <-DTL.beqAddrTrue in HbeqPRemoved. subst p. rewrite HlookupRemoved. unfold isPDT in *.
    destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  + rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. destruct (lookup p (memory s0) beqAddr); trivial.
    destruct v; trivial. destruct (Index.pred nbleft); trivial. rewrite IHn. reflexivity.
Qed.

Lemma getConfigBlocksEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> getConfigBlocks part s = getConfigBlocks part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold getConfigBlocks.
rewrite HlookupsEq; trivial. destruct (lookup part (memory s0) beqAddr); trivial. destruct v; trivial.
f_equal. apply getConfigBlocksAuxEqRemoveAddr with removedAddr; trivial.
Qed.

Lemma getConfigPaddrEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> getConfigPaddr part s = getConfigPaddr part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold getConfigPaddr.
rewrite getConfigBlocksEqRemoveAddr with (s0:=s0) (removedAddr:=removedAddr); trivial. simpl.
rewrite HlookupsEq; trivial. f_equal. induction (getConfigBlocks part s0); trivial. simpl getAllPaddrConfigAux.
rewrite IHl. destruct (beqAddr a removedAddr) eqn:HbeqARemoved.
- rewrite <-DTL.beqAddrTrue in HbeqARemoved. subst a. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getFreeSlotsListRecEqRemoveAddr n block s0 s nbfree removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> getFreeSlotsListRec n block s nbfree = getFreeSlotsListRec n block s0 nbfree.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert block nbfree.
induction n; simpl; intros block nbfree; trivial.
destruct (beqAddr block removedAddr) eqn:HbeqBlockRemoved.
- rewrite <-DTL.beqAddrTrue in HbeqBlockRemoved. subst block. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. destruct (lookup block (memory s0) beqAddr); trivial.
  destruct v; trivial. destruct (Index.pred nbfree); trivial. rewrite IHn. reflexivity.
Qed.

Lemma getFreeSlotsListEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> getFreeSlotsList part s = getFreeSlotsList part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold getFreeSlotsList.
rewrite HlookupsEq; trivial. destruct (lookup part (memory s0) beqAddr); trivial.
destruct v; trivial. rewrite getFreeSlotsListRecEqRemoveAddr with (s0:=s0) (removedAddr:=removedAddr); trivial.
Qed.

Lemma noDupGetPartitionsEqRemoveAddr part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> NoDup (getPartitions part s0)
-> NoDup (getPartitions part s).
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert part. unfold getPartitions. generalize (maxAddr + 2).
intro n. induction n; simpl; intros part HnoDup; trivial. apply NoDup_cons_iff in HnoDup. apply NoDup_cons_iff.
destruct (beqAddr part removedAddr) eqn:HbeqPartRem.
{
  rewrite <-DTL.beqAddrTrue in HbeqPartRem. subst part. unfold getChildren. rewrite HlookupRemoved. simpl.
  split; auto. apply NoDup_nil.
}
rewrite <-beqAddrFalse in *. rewrite getChildrenEqRemoveAddr with (s0:=s0) (removedAddr:=removedAddr); trivial.
destruct HnoDup as (HpartNotIn & HnoDup). induction (getChildren part s0); simpl in *.
- split; auto.
- apply Lib.in_app_or_neg in HpartNotIn. destruct HpartNotIn as (HpartNotInA & HpartNotIn).
  apply Lib.NoDupSplitInclIff in HnoDup. destruct HnoDup as ((HnoDupA & HnoDup) & Hdisjoint).
  specialize(IHl HpartNotIn HnoDup). destruct IHl as (HpartNotIns & HnoDups). split.
  + apply Lib.in_or_app_neg. split; trivial. contradict HpartNotInA.
    apply getPartitionsImplRemoveAddrAux with s removedAddr; trivial.
  + apply Lib.NoDupSplitInclIff. split; try(split); trivial.
    * apply IHn; assumption.
    * intros addr HaddrInA.
      apply getPartitionsImplRemoveAddrAux with (s0:=s0) (removedAddr:=removedAddr) in HaddrInA; trivial.
      specialize(Hdisjoint addr HaddrInA). clear HnoDup. clear HpartNotIn. clear HpartNotIns. clear HnoDups.
      contradict Hdisjoint. induction l; simpl in *; try(congruence). apply in_app_or in Hdisjoint. apply in_or_app.
      destruct Hdisjoint as [HaddrNotInA | Hdisjoint]; try(right; apply IHl; assumption). left.
      apply getPartitionsImplRemoveAddrAux with s removedAddr; trivial.
Qed.

Lemma getPartitionsAuxExcludesRemovedAddr n m part basePart s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> In part (getPartitionsAux m removedAddr s0)
-> part <> removedAddr
-> NoDup (getPartitionsAux (n+m) basePart s0)
-> In removedAddr (getPartitionsAux n basePart s0)
-> ~In part (getPartitionsAux n basePart s).
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HpartInRemoved HbeqPartRemoved. revert basePart.
induction n; simpl; intros basePart HnoDup HremovedIn; try(exfalso; congruence).
apply NoDup_cons_iff in HnoDup. destruct HnoDup as (HbaseNotIn & HnoDup).
destruct (beqAddr basePart removedAddr) eqn:HbeqBaseRemoved.
- rewrite <-DTL.beqAddrTrue in HbeqBaseRemoved. subst basePart. unfold getChildren. rewrite HlookupRemoved. simpl.
  apply and_not_or. auto.
- rewrite <-beqAddrFalse in *. destruct HremovedIn as [Hcontra | HremovedIn]; try(exfalso; congruence).
  apply and_not_or. rewrite getChildrenEqRemoveAddr with (s0:=s0) (removedAddr:=removedAddr); trivial.
  assert(basePart <> part).
  {
    intro. subst part. clear HnoDup. contradict HbaseNotIn.
    induction (getChildren basePart s0); simpl in *; try(congruence). apply in_app_or in HremovedIn.
    apply in_or_app. destruct HremovedIn as [HremovedInA | HremovedIn].
    - left. apply getPartitionsAuxExtWithMidpoint with removedAddr; trivial.
    - right. apply IHl; trivial.
  }
  split; trivial. induction (getChildren basePart s0); simpl in *; try(exfalso; congruence).
  apply in_app_or in HremovedIn. apply Lib.NoDupSplitInclIff in HnoDup.
  destruct HnoDup as ((HnoDupA & HnoDup) & Hdisjoint). apply Lib.in_app_or_neg in HbaseNotIn.
  destruct HbaseNotIn as (HbaseNotInA & HbaseNotIn). apply Lib.in_or_app_neg.
  destruct HremovedIn as [HremovedInA | HremovedIn].
  + specialize(IHn a HnoDupA HremovedInA). split; trivial.
    assert(HpartInExt: In part (getPartitionsAux (n + m) a s0)).
    { apply getPartitionsAuxExtWithMidpoint with removedAddr; trivial. }
    specialize(Hdisjoint part HpartInExt). clear HnoDup. clear HbaseNotIn. clear IHl. contradict Hdisjoint.
    induction l; simpl in *; try(congruence). apply in_app_or in Hdisjoint. apply in_or_app.
    destruct Hdisjoint as [HpartInA0 | HpartIn].
    * left. apply getPartitionsImplRemoveAddrAux with (s0:=s0) (removedAddr:=removedAddr) in HpartInA0; trivial.
      apply getPartitionsAuxExt; trivial.
    * right. apply IHl; trivial.
  + split; try(apply IHl; trivial).
    assert(HpartInL: In part (flat_map (fun p : paddr => getPartitionsAux (n + m) p s0) l)).
    {
      clear HnoDup. clear HbaseNotIn. clear Hdisjoint. clear IHl. induction l; simpl in *; try(congruence).
      apply in_or_app. apply in_app_or in HremovedIn.
      destruct HremovedIn as [HremovedInA0 | HremovedIn]; try(right; apply IHl; assumption). left.
      apply getPartitionsAuxExtWithMidpoint with removedAddr; trivial.
    }
    apply Lib.disjointPermut in Hdisjoint. specialize(Hdisjoint part HpartInL). contradict Hdisjoint.
    apply getPartitionsImplRemoveAddrAux with (s0:=s0) (removedAddr:=removedAddr) in Hdisjoint; trivial.
    apply getPartitionsAuxExt; trivial.
Qed.

Lemma getPartitionsExcludesRemovedAddr part basePart s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> In part (getPartitions removedAddr s0)
-> part <> removedAddr
-> NoDup (getPartitions basePart s0)
-> In removedAddr (getPartitions basePart s0)
-> ~In part (getPartitions basePart s).
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HpartInRemoved HbeqPartRemoved HnoDup HremovedIn.
unfold getPartitions in *. apply getPartitionsAuxExcludesRemovedAddr with (maxAddr+2) s0 removedAddr; trivial.
rewrite getPartitionsEndAny with (n:=maxAddr+2); trivial; try(lia). apply lengthNoDupPartitions in HnoDup. lia.
Qed.

Lemma isListOfKernelsAuxEqRemovedAddr kernList kernel s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> isListOfKernelsAux kernList kernel s0
-> isListOfKernelsAux kernList kernel s.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert kernel.
induction kernList; simpl; intros kernel HkernList; trivial.
destruct HkernList as (HlookupNext & HlebNextMax & HbeqANull & HkernList). apply IHkernList in HkernList.
split; auto. rewrite HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
rewrite HlookupNext in *. congruence.
Qed.

Lemma isListOfKernelsEqRemovedAddr kernList part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> part <> removedAddr
-> isListOfKernels kernList part s0
-> isListOfKernels kernList part s.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT HbeqPartRemoved. unfold isListOfKernels. destruct kernList; trivial.
intro HkernList. destruct HkernList as [pdentry (HlookupPart & HbeqStructNull & HeqStruct & HkernList)].
exists pdentry. rewrite HlookupsEq; trivial. split; try(split; try(split)); trivial. revert HremovedIsPDT HkernList.
apply isListOfKernelsAuxEqRemovedAddr; assumption.
Qed.

Lemma isListOfKernelsAuxEqRemovedAddrRev kernList kernel s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> isListOfKernelsAux kernList kernel s
-> isListOfKernelsAux kernList kernel s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert kernel.
induction kernList; simpl; intros kernel HkernList; trivial.
destruct HkernList as (HlookupNext & HlebNextMax & HbeqANull & HkernList). apply IHkernList in HkernList.
split; auto. rewrite HlookupsEq in HlookupNext; trivial. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
rewrite HlookupNext in *. congruence.
Qed.

Lemma isListOfKernelsEqRemovedAddrRev kernList part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> isListOfKernels kernList part s
-> isListOfKernels kernList part s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. unfold isListOfKernels. destruct kernList; trivial.
intro HkernList. destruct HkernList as [pdentry (HlookupPart & HbeqStructNull & HeqStruct & HkernList)].
assert(part <> removedAddr).
{ intro. subst part. exfalso; congruence. }
exists pdentry. rewrite <-HlookupsEq; trivial. split; try(split; try(split)); trivial. revert HremovedIsPDT HkernList.
apply isListOfKernelsAuxEqRemovedAddrRev; assumption.
Qed.

Lemma isParentsListImplRemovedAddrRev parentsList part s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> isParentsList s parentsList part
-> isParentsList s0 parentsList part.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert part.
induction parentsList; simpl; intros part HparentsList; trivial. assert(a <> removedAddr).
{ intro. subst a. rewrite HlookupRemoved in *. congruence. }
rewrite HlookupsEq in HparentsList; trivial. destruct (lookup a (memory s0) beqAddr); try(congruence).
destruct v; try(congruence).
destruct HparentsList as (HbeqPartRoot & [pdentry (HlookupPart & Hparent)] & HparentsList).
specialize(IHparentsList a HparentsList). split; try(split); trivial. exists pdentry. assert(part <> removedAddr).
{ intro. subst part. congruence. }
rewrite HlookupsEq in HlookupPart; auto.
Qed.

Lemma completeListOfKernelsAuxEqRemovedAddr n kernel s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> completeListOfKernelsAux n kernel s = completeListOfKernelsAux n kernel s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. revert kernel. induction n; simpl; intro; trivial.
destruct (beqAddr (CPaddr (kernel + nextoffset)) removedAddr) eqn:HbeqNextRemoved.
- rewrite <-DTL.beqAddrTrue in HbeqNextRemoved. rewrite HbeqNextRemoved. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  reflexivity.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial. rewrite IHn.
  reflexivity.
Qed.

Lemma completeListOfKernelsEqRemovedAddr kernel s0 s removedAddr:
(forall addr, addr <> removedAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> lookup removedAddr (memory s) beqAddr = None
-> isPDT removedAddr s0
-> completeListOfKernels kernel s = completeListOfKernels kernel s0.
Proof.
intros HlookupsEq HlookupRemoved HremovedIsPDT. unfold completeListOfKernels.
rewrite completeListOfKernelsAuxEqRemovedAddr with (s0:=s0) (removedAddr:=removedAddr); trivial.
destruct (beqAddr kernel removedAddr) eqn:HbeqKernRemoved.
- rewrite <-DTL.beqAddrTrue in HbeqKernRemoved. subst kernel. rewrite HlookupRemoved. unfold isPDT in *.
  destruct (lookup removedAddr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  reflexivity.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.
