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
               PropagatedProperties MapMMUPage*) findBlockInKSWithAddr removeBlockInChildAndDescendants.

From Stdlib Require Import Bool List EqNat.

Require Import Model.Monad.

Module WP := WeakestPreconditions.

(** * Summary
    This file contains the invariant of [removeMemoryBlock].
    We prove that this PIP service preserves the isolation property *)

Lemma removeMemoryBlock (idBlockToRemove: paddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
removeMemoryBlock idBlockToRemove
{{fun _ s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold removeMemoryBlock.
eapply bindRev.
{ (** getCurPartition **)
  eapply weaken. eapply getCurPartition. intros s Hprops. simpl. apply Hprops.
}
intro currentPart. eapply bindRev.
{ (** findBlockInKSWithAddr **)
  eapply weaken. apply findBlockInKSWithAddr.
  intros s Hprops. simpl. split. apply Hprops. split. intuition.
  destruct Hprops as (Hprops & Hcurr). rewrite Hcurr.
  apply IL.partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
}
intro blockToRemoveInCurrPartAddr. eapply bindRev.
{ (** compareAddrToNull **)
  eapply weaken. apply compareAddrToNull.
  intros s Hprops. simpl. apply Hprops.
}
intro addrIsNull. destruct addrIsNull.
{ (* case_eq addrIsNull = true *)
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
(* case_eq addrIsNull = false *)
eapply bindRev.
{ (** MAL.readSh1PDChildFromBlockEntryAddr *)
  eapply weaken. apply readSh1PDChildFromBlockEntryAddr. intros s Hprops. simpl. rewrite <-beqAddrFalse in Hprops.
  destruct Hprops as ((((HPI & HKDI & HVS & Hconsist) & Hcurr) & _ & HpropsOr) & HbeqNullBlock).
  destruct HpropsOr as [Hcontra | [bentry (HlookupBlock & HblockEq & HPflag & HblockMapped)]];
    try(exfalso; congruence). rewrite beqAddrFalse in HbeqNullBlock.
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ consistency s /\ currentPart = currentPartition s /\ blockToRemoveInCurrPartAddr = idBlockToRemove
    /\ bentryPFlag blockToRemoveInCurrPartAddr true s
    /\ In blockToRemoveInCurrPartAddr (getMappedBlocks currentPart s)
    /\ beqAddr nullAddr blockToRemoveInCurrPartAddr = false). split. intuition.
  unfold consistency in *; unfold consistency1 in *. split. intuition. split.
  intuition. split. intuition. split. intuition. exists bentry. assumption.
}
intro idPDchild. eapply bindRev.
{ (** compareAddrToNull **)
  eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
}
intro pdchildIsNull. destruct pdchildIsNull.
{ (* case_eq pdchildIsNull = true *)
  eapply weaken. eapply WP.ret. simpl. intros s Hprops. intuition.
}
(* case_eq pdchildIsNull = false *)
eapply bindRev.
{ (** MAL.readSh1InChildLocationFromBlockEntryAddr *)
  eapply weaken. apply readSh1InChildLocationFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as ((Hprops & Hsh1) & HbeqNullChild).
  destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchild & Hsh1)]].
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ consistency s /\ currentPart = currentPartition s /\ blockToRemoveInCurrPartAddr = idBlockToRemove
    /\ bentryPFlag blockToRemoveInCurrPartAddr true s
    /\ In blockToRemoveInCurrPartAddr (getMappedBlocks currentPart s)
    /\ beqAddr nullAddr blockToRemoveInCurrPartAddr = false
    /\ beqAddr nullAddr idPDchild = false
    /\ (exists sh1entryaddr, sh1entryPDchild sh1entryaddr idPDchild s
          /\ sh1entryAddr blockToRemoveInCurrPartAddr sh1entryaddr s)).
  intuition. 2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
  - exists sh1entryaddr. intuition.
  - unfold bentryPFlag in *.
    destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists b. reflexivity.
}
intro blockToRemoveInChildAddr. eapply bindRev.
{ (** compareAddrToNull **)
  eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
}
intro blockInChildIsNull. destruct blockInChildIsNull.
{ (* case_eq idPDchildIsNull = true *)
  eapply weaken. apply WP.ret. simpl. intros s Hprops. intuition.
}
(* case_eq blockInChildIsNull = false *)
eapply bindRev.
{ (** MAL.readPDVidt **)
  eapply weaken. apply readPDVidt. intros s Hprops. simpl. split. apply Hprops. intuition.
  unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
  destruct (lookup currentPart (memory s) beqAddr); try(simpl in *; congruence).
  destruct v; try(simpl in *; congruence). trivial.
}
intro vidtBlockGlobalId. destruct (beqAddr vidtBlockGlobalId blockToRemoveInCurrPartAddr) eqn:HbeqVidtBlockTR.
{ (* case vidtBlockGlobalId = blockToRemoveInCurrPartAddr *)
  eapply weaken. apply WP.ret. intros s Hprops. intuition.
}
(* case vidtBlockGlobalId <> blockToRemoveInCurrPartAddr *)
eapply bindRev.
{	(* Internal.removeBlockInChildAndDescendants *)
  eapply weaken. apply removeBlockInChildAndDescendants. intros s Hprops. simpl.
  destruct Hprops as ((((HPI & HKDi & HVS & Hconsist & Hcurr & HBTREq & HPflagBTR & HBTRMapped & HbeqNullBTR &
    HbeqNullChild & [sh1entryaddrBis (HPDchild & Hsh1Bis)]) & [sh1entry [sh1entryaddr (HlookupSh1 & Hsh1 & Hloc)]]) &
    HbeqNullBTRChild) & _). assert(isBE blockToRemoveInCurrPartAddr s).
  {
    unfold isBE. unfold bentryPFlag in *.
    destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(isBE blockToRemoveInChildAddr s).
  {
    unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). destruct Hloc as (_ & Hres). rewrite <-beqAddrFalse in *.
    apply not_eq_sym in HbeqNullBTRChild. apply Hres; assumption.
  }
  assert(In currentPart (getPartitions multiplexer s)).
  {
    subst currentPart. unfold consistency in *; unfold consistency1 in *; intuition.
  }
  intuition. exists sh1entryaddr. unfold sh1entryAddr in *.
  destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). subst sh1entryaddr. subst sh1entryaddrBis. auto.
}
intro blockIsRemoved. destruct (negb blockIsRemoved) eqn:HnRemoved.
- eapply weaken. apply WP.ret. intuition.
- eapply weaken. apply WP.ret. intuition.
Qed.
