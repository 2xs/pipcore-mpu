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

Require Import Model.ADT Model.Lib Model.MAL.
Require Import Core.Services.

Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib (*Proof.InternalLemmas Proof.InternalLemmas2*) Proof.DependentTypeLemmas.

Require Import Invariants (*GetTableAddr UpdateShadow2Structure UpdateShadow1Structure
               PropagatedProperties MapMMUPage*) findBlockInKSWithAddr.

Require Import Bool List EqNat.

Require Import Model.Monad.

Module WP := WeakestPreconditions.

(** * Summary
    This file contains the invariant of [addVaddr].
    We prove that this PIP service preserves the isolation property *)

Lemma removeMemoryBlock (idBlockToRemove: paddr) :
{{fun s => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
removeMemoryBlock idBlockToRemove
{{fun _ s  => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold removeMemoryBlock.
(** getCurPartition **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getCurPartition.
cbn.
intros.
intuition.
pose proof (HP := conj H0 (conj H H1)).
exact HP.
intro currentPart.
eapply WP.bindRev.
{ (** findBlockInKSWithAddr **)
	eapply weaken. apply findBlockInKSWithAddr.findBlockInKSWithAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockToShareInCurrPartAddr.
eapply WP.bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H.
}
intro addrIsNull.
case_eq addrIsNull.
{ (* case_eq addrIsNull = true *)
	intros. eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
(* case_eq addrIsNull = false *)
intros.
eapply bindRev.
{ (** MAL.readSh1PDChildFromBlockEntryAddr *)
	eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
	intros. simpl. split. apply H0.
	intuition.
	- (* blockToShareInCurrPartAddr is NOT NULL, prove inconsistency *)
		rewrite <- beqAddrFalse in H2. congruence.
	- destruct H7. exists x. intuition.
}
intro idPDchild.
eapply WP.bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H0.
}
intro pdchildIsNull.
case_eq pdchildIsNull.
{ (* case_eq pdchildIsNull = true *)
	intros. eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
(* case_eq pdchildIsNull = false *)
intros.
eapply bindRev.
{ (** MAL.readSh1InChildLocationFromBlockEntryAddr *)
	eapply weaken. apply readSh1InChildLocationFromBlockEntryAddr.
	intros. simpl. split. apply H1.
	intuition.
	- (* blockToShareInCurrPartAddr is NOT NULL, prove inconsistency *)
		subst. rewrite <- beqAddrFalse in H5. congruence.
	- destruct H10. exists x. intuition.
}
intro blockToRemoveInChildAddr.
eapply WP.bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H1.
}
intro blockInChildIsNull.
case_eq blockInChildIsNull.
{ (* case_eq idPDchildIsNull = true *)
	intros. eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}
(* case_eq blockInChildIsNull = false *)
intros.
eapply bindRev.
{	(* Internal.removeBlockInChildAndDescendants *)
