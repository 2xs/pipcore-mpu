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
    This file contains the invariant of [findBlock].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
  Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas Proof.InternalLemmas2.
Require Import Invariants getGlobalIdPDCurrentOrChild findBlockInKSWithAddr freeSlot.
Require Import writeAccessibleToAncestorsIfNotCutRec removeBlockFromPhysicalMPUIfAlreadyMapped.
From Stdlib Require Import Compare_dec Bool Lia List Logic.ProofIrrelevance.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Import ListNotations.

Module WP := WeakestPreconditions.

Lemma mergeMemoryBlocks (idBlockToMerge1 idBlockToMerge2 : paddr) (MPURegionNb : index) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.mergeMemoryBlocks idBlockToMerge1 idBlockToMerge2 MPURegionNb
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold Services.mergeMemoryBlocks. eapply bindRev.
{ (** getCurPartition **)
  eapply weaken. apply getCurPartition.
  intros s Hprops. simpl. apply Hprops.
}
intro currentPart. eapply bindRev.
{ (** Internal.findBlockInKSWithAddr *)
  eapply weaken. apply findBlockInKSWithAddr.
  intros s Hprops. simpl. split. apply Hprops. intuition. subst currentPart. unfold consistency in *.
  unfold consistency1 in *. apply partitionsArePDT; intuition.
}
intro block1InCurrPartAddr. eapply bindRev.
{ (** compareAddrToNull **)
  eapply weaken. apply Invariants.compareAddrToNull.
  intros s Hprops. simpl. apply Hprops.
}
intro addrIsNull. case_eq addrIsNull.
{ (* case_eq addrIsNull = true *)
  intros. eapply weaken. apply WP.ret.
  simpl. intros. intuition.
}
(* case_eq addrIsNull = false *)
intros HaddrIsNull. eapply bindRev.
{ (** Internal.findBlockInKSWithAddr *)
  eapply weaken. apply findBlockInKSWithAddr.
  intros s Hprops. simpl.
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
    /\ currentPart = currentPartition s
    /\ (exists bentry,
         lookup block1InCurrPartAddr (memory s) beqAddr = Some (BE bentry)
         /\ block1InCurrPartAddr = idBlockToMerge1
         /\ bentryPFlag block1InCurrPartAddr true s
         /\ In block1InCurrPartAddr (getMappedBlocks currentPart s))). rewrite <-beqAddrFalse in *.
  destruct Hprops as ((Hprops & _ & HpropsOr) & HbeqNullBlock).
  destruct HpropsOr as [Hcontra | Hblock]; try(exfalso; congruence). intuition. subst currentPart.
  unfold consistency in *. unfold consistency1 in *. apply partitionsArePDT; intuition.
}
intro block2InCurrPartAddr. eapply bindRev.
{ (** compareAddrToNull **)
  eapply weaken. apply Invariants.compareAddrToNull.
  intros s Hprops. simpl. apply Hprops.
}
intro addrIsNull0. case_eq addrIsNull0.
{ (* case_eq addrIsNull0 = true *)
  intros. eapply weaken. apply WP.ret.
  simpl. intros. intuition.
}
(* case_eq addrIsNull0 = false *)
intros HaddrIsNull2. eapply bindRev.
{ (** MAL.readBlockAccessibleFromBlockEntryAddr *)
  eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
  intros s Hprops. destruct Hprops as (((HPI & HKDI & HVS & Hconsist & Hcurr & Hblock) & _ & HpropsOr) &
    HbeqNullBlock2).
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
    /\ currentPart = currentPartition s
    /\ (exists bentry1,
         lookup block1InCurrPartAddr (memory s) beqAddr = Some (BE bentry1)
         /\ block1InCurrPartAddr = idBlockToMerge1
         /\ bentryPFlag block1InCurrPartAddr true s
         /\ In block1InCurrPartAddr (getMappedBlocks currentPart s))
    /\ (exists bentry2,
         lookup block2InCurrPartAddr (memory s) beqAddr = Some (BE bentry2)
         /\ block2InCurrPartAddr = idBlockToMerge2
         /\ bentryPFlag block2InCurrPartAddr true s
         /\ In block2InCurrPartAddr (getMappedBlocks currentPart s))). rewrite <-beqAddrFalse in *.
  destruct HpropsOr as [Hcontra | Hblock2]; try(exfalso; congruence). intuition.
  destruct Hblock as [bentry1 (HlookupBlock1 & _)]. unfold isBE. rewrite HlookupBlock1. trivial.
}
intro isBlock1Accessible. eapply bindRev.
{ (** MAL.readBlockAccessibleFromBlockEntryAddr *)
  eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
  intros s Hprops. simpl. split. apply Hprops. destruct Hprops as ((_ & _ & _ & _ & _ & _ & Hblock) & _).
  unfold bentryAFlag in *. unfold isBE. destruct Hblock as [bentry2 (HlookupBlock2 & _)]. rewrite HlookupBlock2.
  trivial.
}
intro isBlock2Accessible. case_eq (negb (isBlock1Accessible && isBlock2Accessible)).
{ (* case_eq (negb (isBlock1Accessible && isBlock2Accessible)) = true *)
  intros. eapply weaken. apply WP.ret.
  simpl. intros. intuition.
}
(* case_eq (negb (isBlock1Accessible && isBlock2Accessible)) = false *)
intros HblocksAcc. apply negb_false_iff in HblocksAcc. apply andb_prop in HblocksAcc.
destruct HblocksAcc as (Hacc1 & Hacc2). subst isBlock1Accessible. subst isBlock2Accessible. eapply bindRev.
{ (** MAL.readSh1PDChildFromBlockEntryAddr *)
  eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
  intros s Hprops. simpl. split. apply Hprops. unfold consistency in *. unfold consistency1 in *. intuition.
  unfold bentryAFlag in *. destruct (lookup block1InCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. reflexivity.
}
intro block1PDChildAddr. eapply bindRev.
{ (** compareAddrToNull **)
  eapply weaken. apply Invariants.compareAddrToNull.
  intros s Hprops. simpl. apply Hprops.
}
intro block1PDChildAddrIsNull. eapply bindRev.
{ (** MAL.readSh1PDChildFromBlockEntryAddr *)
  eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
  intros s Hprops. simpl. split. apply Hprops. unfold consistency in *. unfold consistency1 in *. intuition.
  unfold bentryAFlag in *. destruct (lookup block2InCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. reflexivity.
}
intro block2GlobalIdPDChild. eapply bindRev.
{ (** compareAddrToNull **)
  eapply weaken. apply Invariants.compareAddrToNull.
  intros s Hprops. simpl. apply Hprops.
}
intro block2GlobalIdPDChildIsNull. case_eq ((negb block1PDChildAddrIsNull || negb block2GlobalIdPDChildIsNull)).
{ (* case_eq ((negb block1PDChildAddrIsNull || negb block2GlobalIdPDChildIsNull)) = true *)
  intros. eapply weaken. apply WP.ret.
  simpl. intros. intuition.
}
(* case_eq ((negb block1PDChildAddrIsNull || negb block2GlobalIdPDChildIsNull)) = false *)
intros HpdsNull. apply orb_false_iff in HpdsNull. destruct HpdsNull as (Hpd1Null & Hpd2Null).
apply negb_false_iff in Hpd1Null,Hpd2Null. subst block1PDChildAddrIsNull. subst block2GlobalIdPDChildIsNull.
eapply bindRev.
{ (** MAL.readSCNextFromBlockEntryAddr **)
  eapply weaken. apply readSCNextFromBlockEntryAddr.
  intros s Hprops. simpl. split. apply Hprops. unfold consistency in *. unfold consistency1 in *. intuition.
  unfold bentryAFlag in *.
  destruct (lookup block1InCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. reflexivity.
}
intro block1Next. eapply bindRev.
{ (** getBeqAddr **)
  eapply weaken. apply Invariants.getBeqAddr.
  intros s Hprops. simpl. apply Hprops.
}
intro isBlock2Next. case_eq (negb isBlock2Next).
{ (* case_eq (negb isBlock2Next) = true *)
  intros. eapply weaken. apply WP.ret.
  simpl. intros s Hprops. intuition.
}
(* case_eq (negb isBlock2Next = false *)
intros Hnext2. apply negb_false_iff in Hnext2. subst isBlock2Next. eapply bindRev.
{ (** MAL.readSCNextFromBlockEntryAddr **)
  eapply weaken. apply readSCNextFromBlockEntryAddr.
  intros s Hprops. simpl. split. apply Hprops. unfold consistency in *. unfold consistency1 in *.
  intuition. unfold bentryAFlag in *.
  destruct (lookup block2InCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. reflexivity.
}
intro block2Next. eapply bindRev.
{ (** MAL.writeSCNextFromBlockEntryAddr **)
  eapply weaken. apply writeSCNextFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as ((((((((((HPI & HKDI & HVS & Hconsist & Hcurr & Hblock1 & Hblock2) & HAflag1) & HAflag2) &
    Hchild1) & Hchild1IsNull) & Hchild2) & Hchild2IsNull) & Hnext1) & Hblock2IsNext1) & Hnext2).
  destruct Hblock1 as [bentry1 (HlookupBlock1 & Hblock1 & HPflag1 & Hblock1Mapped)].
  destruct Hblock2 as [bentry2 (HlookupBlock2 & Hblock2 & HPflag2 & Hblock2Mapped)]. rewrite <-DTL.beqAddrTrue in *.
  subst block1PDChildAddr. subst block1Next. destruct Hchild1 as [_ [sh1entryaddr1 (_ & HPDchild1 & Hsh11)]].
  destruct Hchild2 as [_ [sh1entryaddr2 (_ & HPDchild2 & Hsh12)]]. unfold consistency in *. unfold consistency1 in *.
  split. intuition. split. intuition. split. intuition. split. intuition. exists bentry1. exists (blockindex bentry1).
  assert(Hsce1: exists scentry1, lookup (CPaddr (block1InCurrPartAddr+scoffset)) (memory s) beqAddr
    = Some (SCE scentry1)).
  {
    unfold scentryNext in *.
    destruct (lookup (CPaddr (block1InCurrPartAddr+scoffset)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists s0. reflexivity.
  }
  destruct Hsce1 as [scentry1 HlookupSCE1]. exists scentry1. split; trivial. split; trivial. split; trivial.
  set(newS := {|
                currentPartition := currentPartition s;
                memory :=
                  add (CPaddr (block1InCurrPartAddr + scoffset))
                    (SCE {| origin := origin scentry1; next := block2Next |}) (memory s) beqAddr
              |}).
  assert(HcurrEq: currentPartition newS = currentPartition s) by reflexivity.
  assert(Hsce1IsSCE: isSCE (CPaddr (block1InCurrPartAddr+scoffset)) s)
    by (unfold isSCE; rewrite HlookupSCE1; trivial).
  assert(HgetPartsEq: getPartitions multiplexer newS = getPartitions multiplexer s).
  { apply getPartitionsEqSCE; intuition. }
  assert(HgetKSEq: forall partition pdentry,
    lookup partition (memory s) beqAddr = Some (PDT pdentry)
    -> getKSEntries partition newS = getKSEntries partition s).
  { intros partition pdentry HlookupPart. apply getKSEntriesEqSCE with pdentry; intuition. }
  assert(HgetMappedBEq: forall partition, isPDT partition s
    -> getMappedBlocks partition newS = getMappedBlocks partition s).
  { intros partition HpartIsPDT. apply getMappedBlocksEqSCE; intuition. }
  assert(HgetMappedPEq: forall partition, isPDT partition s
    -> getMappedPaddr partition newS = getMappedPaddr partition s).
  { intros partition HpartIsPDT. apply getMappedPaddrEqSCE; intuition. }
  assert(HgetAccMappedBEq: forall partition, isPDT partition s
    -> getAccessibleMappedBlocks partition newS = getAccessibleMappedBlocks partition s).
  { intros partition HpartIsPDT. apply getAccessibleMappedBlocksEqSCE; intuition. }
  assert(HgetAccMappedPEq: forall partition, isPDT partition s
    -> getAccessibleMappedPaddr partition newS = getAccessibleMappedPaddr partition s).
  { intros partition HpartIsPDT. apply getAccessibleMappedPaddrEqSCE; intuition. }
  assert(HgetConfigBEq: forall partition pdentry,
    lookup partition (memory s) beqAddr = Some (PDT pdentry)
    -> getConfigBlocks partition newS = getConfigBlocks partition s).
  { intros partition pdentry HlookupPart. apply getConfigBlocksEqSCE with pdentry; intuition. }
  assert(HgetConfigPEq: forall partition, isPDT partition s
    -> getConfigPaddr partition newS = getConfigPaddr partition s).
  { intros partition HpartIsPDT. apply getConfigPaddrEqSCE; intuition. }
  assert(HgetFreePEq: forall partition, getFreeSlotsList partition newS = getFreeSlotsList partition s).
  {
    intro partition. unfold getFreeSlotsList. simpl.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) partition) eqn:HbeqScePart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqScePart. rewrite HbeqScePart in *. rewrite HlookupSCE1 in *. reflexivity.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
    destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial. apply getFreeSlotsListRecEqSCE.
    2,3: unfold isBE; unfold isPADDR; rewrite HlookupSCE1; intuition. rewrite <-beqAddrFalse in *. intro Hcontra.
    assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
    specialize(HfirstIsBE partition p HlookupPart HbeqFirstNull). destruct HfirstIsBE as (HfirstIsBE & _).
    rewrite Hcontra in *. unfold isBE in *. rewrite HlookupSCE1 in *. congruence.
  }
  assert(HgetChildrenEq: forall partition, isPDT partition s
    -> getChildren partition newS = getChildren partition s).
  { intros partition HpartIsPDT. apply getChildrenEqSCE; intuition. }
  assert(HisListOfKernEq: forall kernList partition, isListOfKernels kernList partition newS
    -> isListOfKernels kernList partition s).
  { intros kernList partition. apply isListOfKernelsEqSCE. }
  assert(HisParentsListEq: forall parentsList pdparent, isPDT pdparent s
    -> isParentsList newS parentsList pdparent
    -> isParentsList s parentsList pdparent).
  {
    intros parentsList pdparent HparentIsPart. apply isParentsListEqSCERev with scentry1; trivial.
    - apply isPDTLookupEq in HparentIsPart. assumption.
    - intuition.
  }
  assert(consistency1 newS).
  {
    assert(nullAddrExists newS).
    { (* BEGIN nullAddrExists newS *)
      assert(Hcons0: nullAddrExists s) by intuition. unfold nullAddrExists in *. unfold isPADDR in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) nullAddr) eqn:HbeqSceNull.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceNull. rewrite HbeqSceNull in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END nullAddrExists *)
    }

    assert(wellFormedFstShadowIfBlockEntry newS).
    { (* BEGIN wellFormedFstShadowIfBlockEntry newS *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s) by intuition. intros block HblockIsBE. unfold isBE in *.
      simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block HblockIsBE). unfold isSHE in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (CPaddr (block + sh1offset))) eqn:HbeqSceSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(PDTIfPDFlag newS).
    { (* BEGIN PDTIfPDFlag newS *)
      assert(Hcons0: PDTIfPDFlag s) by intuition. intros idPDchild sh1entryaddr HcheckChild.
      assert(HlookupBlockEq: lookup idPDchild (memory newS) beqAddr = lookup idPDchild (memory s) beqAddr).
      {
        destruct HcheckChild as (_ & Hsh1). unfold sh1entryAddr in *. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) idPDchild) eqn:HbeqSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      assert(HcheckChilds: true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s).
      {
        destruct HcheckChild as (HcheckChild & Hsh1). unfold checkChild in *. unfold sh1entryAddr in *.
        rewrite HlookupBlockEq in *. split; trivial. destruct (lookup idPDchild (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). simpl in HcheckChild.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSceSh1;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds). unfold bentryAFlag. unfold bentryStartAddr.
      unfold bentryPFlag. unfold entryPDT in *. rewrite HlookupBlockEq.
      destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
      exists startaddr. split; trivial. destruct (lookup idPDchild (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (startAddr (blockrange b))) eqn:HbeqSceStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceStart. rewrite HbeqSceStart in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag newS).
    { (* BEGIN AccessibleNoPDFlag newS *)
      assert(Hcons0: AccessibleNoPDFlag s) by intuition. intros block sh1entryaddr HblockIsBE Hsh1 HAflag.
      assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        unfold sh1entryAddr in *. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold isBE in *. unfold sh1entryAddr in *. unfold bentryAFlag in *. rewrite HlookupBlockEq in *.
      specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAflag). unfold sh1entryPDflag in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) sh1entryaddr) eqn:HbeqSceSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot newS).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot newS *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
      intros partition pdentry HlookupPart HbeqFirstNull. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart HbeqFirstNull). destruct Hcons0 as (_ & Hcons0). unfold isBE.
      unfold isFreeSlot in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (firstfreeslot pdentry)) eqn:HbeqSceFirst.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceFirst. rewrite HbeqSceFirst in *. rewrite HlookupSCE1 in *. exfalso.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (firstfreeslot pdentry) (memory s) beqAddr) eqn:HlookupFirst; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split; trivial.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (firstfreeslot pdentry+sh1offset)))
        eqn:HbeqSceFirstSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceFirstSh1. rewrite HbeqSceFirstSh1 in *. rewrite HlookupSCE1 in *. exfalso.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (firstfreeslot pdentry+scoffset)))
        eqn:HbeqSceFirstSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceFirstSce. exfalso. unfold CPaddr in HbeqSceFirstSce.
        unfold CPaddr in HlookupSCE1. assert(Hnull: isPADDR nullAddr s) by intuition. unfold isPADDR in *.
        destruct (le_dec (block1InCurrPartAddr + scoffset) maxAddr).
        - destruct (le_dec (firstfreeslot pdentry + scoffset) maxAddr).
          + injection HbeqSceFirstSce as HbeqSceFirstSce. apply PeanoNat.Nat.add_cancel_r in HbeqSceFirstSce.
            apply paddrEqNatEqEquiv in HbeqSceFirstSce. rewrite HbeqSceFirstSce in *. unfold bentryPFlag in *.
            rewrite HlookupFirst in *.
            destruct (lookup (CPaddr (firstfreeslot pdentry + scoffset)) (memory s) beqAddr); try(congruence).
            destruct v; try(congruence). destruct Hcons0 as (_ & _ & _ & _ & Hcontra & _). congruence.
          + assert(HnullEq: {| p:=0; Hp := ADT.CPaddr_obligation_2 (firstfreeslot pdentry+scoffset) n |} = nullAddr).
            { cbn. f_equal. apply proof_irrelevance. }
            rewrite HbeqSceFirstSce in *. rewrite HnullEq in *. rewrite HlookupSCE1 in *. congruence.
        - assert(HnullEq: {| p:=0; Hp := ADT.CPaddr_obligation_2 (block1InCurrPartAddr+scoffset) n |} = nullAddr).
          { cbn. f_equal. apply proof_irrelevance. }
          rewrite HnullEq in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT newS).
    { (* BEGIN multiplexerIsPDT newS *)
      assert(Hcons0: multiplexerIsPDT s) by intuition. unfold multiplexerIsPDT in *. unfold isPDT in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) multiplexer) eqn:HbeqSceMult.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceMult. rewrite HbeqSceMult in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END multiplexerIsPDT *)
    }

    assert(currentPartitionInPartitionsList newS).
    { (* BEGIN currentPartitionInPartitionsList newS *)
      assert(Hcons0: currentPartitionInPartitionsList s) by intuition. unfold currentPartitionInPartitionsList.
      rewrite HcurrEq. rewrite HgetPartsEq. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry newS).
    { (* BEGIN wellFormedShadowCutIfBlockEntry newS *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s) by intuition. intros block HblockIsBE. unfold isBE in *.
      simpl in HblockIsBE. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block) eqn:HbeqSceBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 block HblockIsBE).
      destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr. split; trivial. unfold isSCE. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE newS).
    { (* BEGIN BlocksRangeFromKernelStartIsBE newS *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s) by intuition. intros kernel idx HkernIsKS HltIdxKernEntries.
      unfold isKS in *. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (CPaddr (kernel + idx))) eqn:HbeqSceIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceIdx. rewrite HbeqSceIdx in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS newS).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS newS *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s) by intuition. intros block idx HblockIsBE Hidx.
      assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        unfold isBE in *. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold isBE in *. unfold bentryBlockIndex in *. rewrite HlookupBlockEq in *.
      specialize(Hcons0 block idx HblockIsBE Hidx). unfold isKS in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (CPaddr (block - idx))) eqn:HbeqSceKern.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceKern. rewrite HbeqSceKern in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(sh1InChildLocationIsBE newS).
    { (* BEGIN sh1InChildLocationIsBE newS *)
      assert(Hcons0: sh1InChildLocationIsBE s) by intuition. intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull.
      simpl in HlookupSh1. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) sh1entryaddr) eqn:HbeqSceSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). unfold isBE in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (inChildLocation sh1entry)) eqn:HbeqSceLoc.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceLoc. rewrite HbeqSceLoc in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END sh1InChildLocationIsBE *)
    }

    assert(StructurePointerIsKS newS).
    { (* BEGIN StructurePointerIsKS newS *)
      assert(Hcons0: StructurePointerIsKS s) by intuition. intros partition pdentry HlookupPart HbeqStructNull.
      simpl in HlookupPart.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart HbeqStructNull). unfold isKS in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (structure pdentry)) eqn:HbeqSceStruct.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceStruct. rewrite HbeqSceStruct in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END StructurePointerIsKS *)
    }

    assert(NextKSIsKS newS).
    { (* BEGIN NextKSIsKS newS *)
      assert(Hcons0: NextKSIsKS s) by intuition.
      intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull. unfold nextKSAddr in *.
      unfold isKS in HkernIsKS. unfold nextKSentry in *. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) nextKSaddr) eqn:HbeqSceNextAd;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull). unfold isKS in *.
      simpl. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) nextKS) eqn:HbeqSceNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceNext. rewrite HbeqSceNext in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR newS).
    { (* BEGIN NextKSOffsetIsPADDR newS *)
      assert(Hcons0: NextKSOffsetIsPADDR s) by intuition. intros kernel nextKSaddr HkernIsKS HnextAddr.
      unfold isKS in *. unfold nextKSAddr in *. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel nextKSaddr HkernIsKS HnextAddr). destruct Hcons0 as (HnextIsPADDR & HnextNotNull).
      split; trivial. unfold isPADDR in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) nextKSaddr) eqn:HbeqSceNextA.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceNextA. rewrite HbeqSceNextA in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(NoDupInFreeSlotsList newS).
    { (* BEGIN NoDupInFreeSlotsList newS *)
      assert(Hcons0: NoDupInFreeSlotsList s) by intuition. intros partition pdentry HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart).
      destruct Hcons0 as [optFreeList (Hlist & HwellFormedList & HnoDupList)]. exists optFreeList.
      rewrite HgetFreePEq. auto.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot newS).
    { (* BEGIN freeSlotsListIsFreeSlot newS *)
      assert(Hcons0: freeSlotsListIsFreeSlot s) by intuition.
      intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
      rewrite HgetFreePEq in HwellFormed. unfold isPDT in *. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList
        HbeqAddrNull). unfold isFreeSlot in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) addr) eqn:HbeqSceAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite HlookupSCE1 in *. exfalso.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup addr (memory s) beqAddr) eqn:HlookupAddr; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (addr+sh1offset))) eqn:HbeqSceAddrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceAddrSh1. rewrite HbeqSceAddrSh1 in *. rewrite HlookupSCE1 in *. exfalso.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (addr + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (addr+scoffset))) eqn:HbeqSceAddrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceAddrSce. exfalso. unfold CPaddr in HbeqSceAddrSce.
        unfold CPaddr in HlookupSCE1. assert(Hnull: isPADDR nullAddr s) by intuition. unfold isPADDR in *.
        destruct (le_dec (block1InCurrPartAddr + scoffset) maxAddr).
        - destruct (le_dec (addr + scoffset) maxAddr).
          + injection HbeqSceAddrSce as HbeqSceAddrSce. apply PeanoNat.Nat.add_cancel_r in HbeqSceAddrSce.
            apply paddrEqNatEqEquiv in HbeqSceAddrSce. rewrite HbeqSceAddrSce in *. unfold bentryPFlag in *.
            rewrite HlookupAddr in *.
            destruct (lookup (CPaddr (addr + scoffset)) (memory s) beqAddr); try(congruence).
            destruct v; try(congruence). destruct Hcons0 as (_ & _ & _ & _ & Hcontra & _). congruence.
          + assert(HnullEq: {| p:=0; Hp := ADT.CPaddr_obligation_2 (addr+scoffset) n |} = nullAddr).
            { cbn. f_equal. apply proof_irrelevance. }
            rewrite HbeqSceAddrSce in *. rewrite HnullEq in *. rewrite HlookupSCE1 in *. congruence.
        - assert(HnullEq: {| p:=0; Hp := ADT.CPaddr_obligation_2 (block1InCurrPartAddr+scoffset) n |} = nullAddr).
          { cbn. f_equal. apply proof_irrelevance. }
          rewrite HnullEq in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(DisjointFreeSlotsLists newS).
    { (* BEGIN DisjointFreeSlotsLists newS *)
      assert(Hcons0: DisjointFreeSlotsLists s) by intuition. intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
      rewrite HgetFreePEq. rewrite HgetFreePEq. unfold isPDT in *. simpl in Hpart1IsPDT. simpl in Hpart2IsPDT.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) part1) eqn:HbeqScePart1; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) part2) eqn:HbeqScePart2; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). assumption.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries newS).
    { (* BEGIN inclFreeSlotsBlockEntries newS *)
      assert(Hcons0: inclFreeSlotsBlockEntries s) by intuition. intros partition HpartIsPDT.
      rewrite HgetFreePEq. unfold isPDT in *. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition HpartIsPDT). apply isPDTLookupEq in HpartIsPDT.
      destruct HpartIsPDT as [pdentry HlookupPart]. rewrite HgetKSEq with partition pdentry; trivial.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries newS).
    { (* BEGIN DisjointKSEntries newS *)
      assert(Hcons0: DisjointKSEntries s) by intuition. intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
      unfold isPDT in *. simpl in Hpart1IsPDT. simpl in Hpart2IsPDT.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) part1) eqn:HbeqScePart1; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) part2) eqn:HbeqScePart2; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). apply isPDTLookupEq in Hpart1IsPDT.
      apply isPDTLookupEq in Hpart2IsPDT. destruct Hpart1IsPDT as [pdentry1 HlookupPart1].
      destruct Hpart2IsPDT as [pdentry2 HlookupPart2]. rewrite HgetKSEq with part1 pdentry1; trivial.
      rewrite HgetKSEq with part2 pdentry2; trivial.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree newS).
    { (* BEGIN noDupPartitionTree newS *)
      assert(Hcons0: noDupPartitionTree s) by intuition. unfold noDupPartitionTree. rewrite HgetPartsEq. assumption.
      (* END noDupPartitionTree *)
    }

    assert(isParent newS).
    { (* BEGIN isParent newS *)
      assert(Hcons0: isParent s) by intuition. intros partition pdparent HparentIsPart HpartIsChild.
      rewrite HgetPartsEq in *. rewrite HgetChildrenEq in HpartIsChild; try(apply partitionsArePDT; intuition).
      specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) partition) eqn:HbeqScePart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqScePart. rewrite HbeqScePart in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END isParent *)
    }

    assert(isChild newS).
    { (* BEGIN isChild newS *)
      assert(Hcons0: isChild s) by intuition. intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot.
      rewrite HgetPartsEq in *. unfold pdentryParent in *. simpl in HparentIsParent.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
      rewrite HgetChildrenEq; trivial. unfold getChildren in Hcons0. unfold isPDT.
      destruct (lookup pdparent (memory s) beqAddr); try(simpl in Hcons0; congruence).
      destruct v; try(simpl in Hcons0; congruence). trivial.
      (* END isChild *)
    }

    assert(noDupKSEntriesList newS).
    { (* BEGIN noDupKSEntriesList newS *)
      assert(Hcons0: noDupKSEntriesList s) by intuition. intros partition HpartIsPDT.
      unfold isPDT in *. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition HpartIsPDT). apply isPDTLookupEq in HpartIsPDT.
      destruct HpartIsPDT as [pdentry HlookupPart]. rewrite HgetKSEq with partition pdentry; trivial.
      (* END noDupKSEntriesList *)
    }

    assert(noDupMappedBlocksList newS).
    { (* BEGIN noDupMappedBlocksList newS *)
      assert(Hcons0: noDupMappedBlocksList s) by intuition. intros partition HpartIsPDT.
      unfold isPDT in *. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition HpartIsPDT). rewrite HgetMappedBEq; trivial.
      (* END noDupMappedBlocksList *)
    }

    assert(wellFormedBlock newS).
    { (* BEGIN wellFormedBlock newS *)
      assert(Hcons0: wellFormedBlock s) by intuition. intros block startaddr endaddr HPflag HstartBlock HendBlock.
      assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        unfold bentryPFlag in *. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockEq in *.
      specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
      (* END wellFormedBlock *)
    }

    assert(parentOfPartitionIsPartition newS).
    { (* BEGIN parentOfPartitionIsPartition newS *)
      assert(Hcons0: parentOfPartitionIsPartition s) by intuition. intros partition pdentry HlookupPart.
      simpl in HlookupPart.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart). destruct Hcons0 as (HparentIsPart & Hrest).
      rewrite HgetPartsEq. split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial. exists parentEntry.
      simpl. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (parent pdentry)) eqn:HbeqSceParent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceParent. rewrite HbeqSceParent in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END parentOfPartitionIsPartition *)
    }

    assert(NbFreeSlotsISNbFreeSlotsInList newS).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList newS *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s) by intuition.
      intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. unfold pdentryNbFreeSlots in *. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree). rewrite HgetFreePEq. assumption.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(maxNbPrepareIsMaxNbKernels newS).
    { (* BEGIN maxNbPrepareIsMaxNbKernels newS *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s) by intuition. intros partition kernList HlistOfKerns.
      apply HisListOfKernEq in HlistOfKerns. specialize(Hcons0 partition kernList HlistOfKerns). assumption.
      (* END maxNbPrepareIsMaxNbKernels *)
    }

    assert(blockInChildHasAtLeastEquivalentBlockInParent newS).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent newS *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s) by intuition.
      intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild
        HendChild HPflagChild. rewrite HgetPartsEq in *.
      rewrite HgetChildrenEq in HchildIsChild; try(apply partitionsArePDT; intuition).
      rewrite HgetMappedBEq in HblockMappedChild; try(apply childrenArePDT with pdparent; intuition).
      unfold bentryStartAddr in HstartChild. unfold bentryEndAddr in HendChild. unfold bentryPFlag in HPflagChild.
      simpl in *. destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBloc;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        HstartChild HendChild HPflagChild).
      destruct Hcons0 as [blockParent [startParent [endParent (HblockPMapped & HstartParent & HendParent & Hbound)]]].
      exists blockParent. exists startParent. exists endParent.
      rewrite HgetMappedBEq; try(apply partitionsArePDT; intuition). split; trivial. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSceBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceBlockP. rewrite HbeqSceBlockP in *. rewrite HlookupSCE1 in *. exfalso.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. auto.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(partitionTreeIsTree newS).
    { (* BEGIN partitionTreeIsTree newS *)
      assert(Hcons0: partitionTreeIsTree s) by intuition.
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
      rewrite HgetPartsEq in *. unfold pdentryParent in *. simpl in HparentIsParent.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) child) eqn:HbeqSceChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 child pdparent). apply Hcons0; trivial. apply HisParentsListEq; trivial.
      assert(Hparent: parentOfPartitionIsPartition s) by intuition.
      destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). subst pdparent. specialize(Hparent child p HlookupChild).
      destruct Hparent as (HparentIsPart & _). specialize(HparentIsPart HbeqChildRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & _). unfold isPDT. rewrite HlookupParent. trivial.
      (* END partitionTreeIsTree *)
    }

    assert(kernelEntriesAreValid newS).
    { (* BEGIN kernelEntriesAreValid newS *)
      assert(Hcons0: kernelEntriesAreValid s) by intuition. intros kernel idx HkernIsKS Hidx.
      unfold isKS in *. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel idx HkernIsKS Hidx). unfold isBE in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (CPaddr (kernel + idx))) eqn:HbeqSceIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceIdx. rewrite HbeqSceIdx in *. rewrite HlookupSCE1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END kernelEntriesAreValid *)
    }

    assert(nextKernelIsValid newS).
    { (* BEGIN nextKernelIsValid newS *)
      assert(Hcons0: nextKernelIsValid s) by intuition. intros kernel HkernIsKS. unfold isKS in *. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel HkernIsKS). destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]).
      split; trivial. exists nextAddr. split.
      - intro Hp. specialize(HlookupNext Hp). simpl.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) {| p := kernel + nextoffset; Hp := Hp |})
          eqn:HbeqSceNext.
        { rewrite <-DTL.beqAddrTrue in HbeqSceNext. rewrite HbeqSceNext in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - destruct Hnext as [HnextIsKS | HnextIsNull]; try(right; assumption). left. simpl. unfold isKS in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) nextAddr) eqn:HbeqSceNext.
        { rewrite <-DTL.beqAddrTrue in HbeqSceNext. rewrite HbeqSceNext in *. rewrite HlookupSCE1 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns newS).
    { (* BEGIN noDupListOfKerns newS *)
      assert(Hcons0: noDupListOfKerns s) by intuition. intros partition kernList HlistOfKerns.
      apply HisListOfKernEq in HlistOfKerns. specialize(Hcons0 partition kernList HlistOfKerns). assumption.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax newS).
    { (* BEGIN MPUsizeIsBelowMax newS *)
      assert(Hcons0: MPUsizeIsBelowMax s) by intuition. intros partition MPUlist HMPU. unfold pdentryMPU in *.
      simpl in HMPU.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition MPUlist HMPU). assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart newS).
    { (* BEGIN originIsParentBlocksStart newS *)
      assert(Hcons0: originIsParentBlocksStart s) by intuition.
      intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEq in *. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(Horigins0: scentryOrigin scentryaddr scorigin s).
      {
        unfold scentryOrigin in *. simpl in Horigin.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces.
        - rewrite <-DTL.beqAddrTrue in HbeqSces. rewrite HbeqSces in *. rewrite HlookupSCE1. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBlock & _)]. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetMappedBEq in HblockMapped; try(unfold isPDT; rewrite HlookupPart; trivial).
      specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
        Horigins0). destruct Hcons0 as (HblockP & HstartIsOrigin). split.
      - intro HbeqPartRoot. specialize(HblockP HbeqPartRoot).
        destruct HblockP as [blockParent (HblockPMapped & HstartP & Hincl)]. exists blockParent.
        assert(HlookupBlockPEq: lookup blockParent (memory newS) beqAddr = lookup blockParent (memory s) beqAddr).
        {
          apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (HlookupBlockP & _)]. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) blockParent) eqn:HbeqSceBlockP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSceBlockP. subst blockParent. rewrite HlookupSCE1 in *. exfalso.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        unfold bentryStartAddr. unfold getAllPaddrAux. rewrite HlookupBlockPEq. rewrite HlookupBlockEq. split; auto.
        rewrite HgetMappedBEq; trivial. assert(Hparent: parentOfPartitionIsPartition s) by intuition.
        specialize(Hparent partition pdentry HlookupPart). destruct Hparent as (HparentIsPart & _).
        specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & _).
        unfold isPDT. rewrite HlookupParent. trivial.
      - intros startaddr Hstart. unfold bentryStartAddr in *. rewrite HlookupBlockEq in Hstart.
        specialize(HstartIsOrigin startaddr Hstart). assumption.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut newS).
    { (* BEGIN nextImpliesBlockWasCut newS *)
      assert(Hcons0: nextImpliesBlockWasCut s) by intuition.
      intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock Hsce
        HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEq in *. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
      {
        apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBlock & _)]. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetMappedBEq in HblockMapped; try(unfold isPDT; rewrite HlookupPart; trivial).
      unfold bentryEndAddr in *. rewrite HlookupBlockEq in *. unfold scentryNext in *. simpl in Hnext.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces.
      - rewrite <-DTL.beqAddrTrue in HbeqSces. rewrite HbeqSces in *. simpl in Hnext. subst scnext. subst scentryaddr.
        unfold CPaddr in HbeqSces. unfold isSCE in Hsce1IsSCE. unfold CPaddr in Hsce1IsSCE.
        assert(Hnull: isPADDR nullAddr s) by intuition. unfold isPADDR in *.
        destruct (le_dec (block + scoffset) maxAddr).
        + destruct (le_dec (block1InCurrPartAddr + scoffset) maxAddr).
          * injection HbeqSces as HbeqSces. apply PeanoNat.Nat.add_cancel_r in HbeqSces.
            apply paddrEqNatEqEquiv in HbeqSces. subst block.
            assert(HsceTriv: CPaddr (block1InCurrPartAddr+scoffset) = CPaddr (block1InCurrPartAddr+scoffset))
              by trivial.
            assert(HbeqSceNull: block2InCurrPartAddr <> nullAddr).
            {
              intro Hcontra. rewrite Hcontra in *. assert(isPADDR nullAddr s) by intuition. unfold isPADDR in *.
              rewrite HlookupBlock2 in *. congruence.
            }
            specialize(Hcons0 partition pdentry block1InCurrPartAddr (CPaddr (block1InCurrPartAddr+scoffset))
              block2InCurrPartAddr endaddr HpartIsPart HlookupPart HblockMapped HendBlock HsceTriv
              HbeqSceNull Hnext1 HbeqPartRoot).
            assert(HnextSide: blockAndNextAreSideBySide s) by (unfold consistency2 in *; intuition).
            specialize(HnextSide partition block1InCurrPartAddr (CPaddr (block1InCurrPartAddr+scoffset))
              block2InCurrPartAddr endaddr HpartIsPart HblockMapped HendBlock HsceTriv HbeqSceNull Hnext1).
            destruct Hcons0 as [blockParent [endParent (HblockPMapped & HendP & HltEnds & HleftIncl)]].
            exists blockParent. exists endParent.
            assert(isPDT (parent pdentry) s).
            {
              assert(HparentOfPart: parentOfPartitionIsPartition s) by intuition.
              specialize(HparentOfPart partition pdentry HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
              specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & _).
              unfold isPDT. rewrite HlookupParent. trivial.
            }
            rewrite HgetMappedBEq; trivial. split; trivial. unfold getAllPaddrAux. rewrite HlookupBlockEq.
            unfold bentryEndAddr in *. simpl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSceBlockP.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSceBlockP. subst blockParent. rewrite HlookupSCE1 in *.
              exfalso; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          * assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block1InCurrPartAddr+scoffset) n |} = nullAddr).
            { cbn. f_equal. apply proof_irrelevance. }
            rewrite <-HbeqSces in *. rewrite HnullEq in *. exfalso.
            destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
        + assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block+scoffset) n |} = nullAddr).
          { cbn. f_equal. apply proof_irrelevance. }
          rewrite HnullEq in *. exfalso. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
          destruct v; congruence.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
          HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
        destruct Hcons0 as [blockParent [endParent (HblockPMapped & HendP & HltEnds & Hincl)]]. exists blockParent.
        unfold bentryEndAddr in *.
        assert(HlookupBlockPEq: lookup blockParent (memory newS) beqAddr = lookup blockParent (memory s) beqAddr).
        {
          simpl. destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) blockParent) eqn:HbeqSceBlock.
          {
            exfalso. rewrite <-DTL.beqAddrTrue in HbeqSceBlock. subst blockParent. rewrite HlookupSCE1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        exists endParent. unfold getAllPaddrAux. rewrite HlookupBlockEq. rewrite HlookupBlockPEq. split; auto.
        rewrite HgetMappedBEq; trivial. unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
        destruct (lookup (parent pdentry) (memory s) beqAddr); try(exfalso; simpl in HblockPMapped; congruence).
        destruct v; try(exfalso; simpl in HblockPMapped; congruence). trivial.
      (* END nextImpliesBlockWasCut *)
    }

    assert(blocksAddressesTypes newS).
    { (* BEGIN blocksAddressesTypes newS *)
      assert(Hcons0: blocksAddressesTypes s) by intuition.
      intros block startaddr endaddr HstartBlock HendBlock HPflag HPDchildBlock. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. unfold bentryPFlag in *. simpl in HstartBlock. simpl in HendBlock. simpl in HPflag.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      unfold sh1entryPDchild in *. simpl in HPDchildBlock.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (block + sh1offset))) eqn:HbeqSceSh1;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr endaddr HstartBlock HendBlock HPflag HPDchildBlock).
      destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hnone]].
      - left. split.
        + unfold isKS in *. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) startaddr) eqn:HbeqSceStart.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSceStart. rewrite HbeqSceStart in *. rewrite HlookupSCE1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
          destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
          * left. unfold isBE in *. simpl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) addr) eqn:HbeqSceAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite HlookupSCE1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. left. unfold isSHE in *. simpl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) addr) eqn:HbeqSceAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite HlookupSCE1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. left. unfold isSCE in *. simpl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) addr) eqn:HbeqSceAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite HlookupSCE1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. right. left. unfold isPADDR in *. simpl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) addr) eqn:HbeqSceAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite HlookupSCE1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. right. right. simpl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) addr) eqn:HbeqSceAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite HlookupSCE1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. left. split.
        + unfold isPDT in *. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) startaddr) eqn:HbeqSceStart.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSceStart. rewrite HbeqSceStart in *. rewrite HlookupSCE1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) addr) eqn:HbeqSceAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite HlookupSCE1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. right. intros addr HaddrInRange. specialize(Hnone addr HaddrInRange). simpl.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) addr) eqn:HbeqSceAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite HlookupSCE1 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END blocksAddressesTypes *)
    }

    assert(notPDTIfNotPDflag newS).
    { (* BEGIN notPDTIfNotPDflag newS *)
      assert(Hcons0: notPDTIfNotPDflag s) by intuition.
      intros block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild. unfold bentryStartAddr in *.
      unfold sh1entryAddr in *. unfold bentryPFlag in *. simpl in HstartBlock. simpl in Hsh1. simpl in HPflag.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      unfold sh1entryPDchild in *. unfold sh1entryPDflag in *. simpl in HPDchild. simpl in HPDflag.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSceSh1;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild). unfold isPDT in *.
      simpl. contradict Hcons0. destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) startaddr)
        eqn:HbeqSceStart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END notPDTIfNotPDflag *)
    }

    assert(nextKernAddrIsInSameBlock newS).
    { (* BEGIN nextKernAddrIsInSameBlock newS *)
      assert(Hcons0: nextKernAddrIsInSameBlock s) by intuition.
      intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HnextInRange HkernIsKS.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      unfold sh1entryPDchild in *. simpl in HnextInRange.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (block + sh1offset))) eqn:HbeqSceSh1;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      unfold isKS in *. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HnextInRange HkernIsKS).
      assumption.
      (* END nextKernAddrIsInSameBlock *)
    }

    assert(blockBelongsToAPart newS).
    { (* BEGIN blockBelongsToAPart newS *)
      assert(Hcons0: blockBelongsToAPart s) by intuition. intros block HPflagBlock. unfold bentryPFlag in *.
      simpl in *. rewrite HgetPartsEq.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block HPflagBlock). destruct Hcons0 as [partition (HpartIsPart & HblockMapped)].
      exists partition. split; trivial. rewrite HgetMappedBEq; trivial.
      apply partitionsArePDT; trivial; intuition.
      (* END blockBelongsToAPart *)
    }

    assert(PDflagMeansNoChild newS).
    { (* BEGIN PDflagMeansNoChild newS *)
      assert(Hcons0: PDflagMeansNoChild s) by intuition. intros block HblockIsBE HPDflagBlock. unfold isBE in *.
      simpl in HblockIsBE. unfold sh1entryPDflag in *. unfold sh1entryPDchild.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (CPaddr (block + sh1offset))) eqn:HbeqSceSh1;
        try(congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block HblockIsBE HPDflagBlock). assumption.
      (* END PDflagMeansNoChild *)
    }

    assert(nbPrepareIsNbKern newS).
    { (* BEGIN nbPrepareIsNbKern newS *)
      assert(Hcons0: nbPrepareIsNbKern s) by intuition. intros partition pdentry HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart). unfold newS. rewrite completeListOfKernelsEqSCE; trivial.
     (* END nbPrepareIsNbKern *)
    }

    assert(pdchildIsPDT newS).
    { (* BEGIN pdchildIsPDT newS *)
      assert(Hcons0: pdchildIsPDT s) by intuition.
      intros part block sh1entryaddr idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
      rewrite HgetPartsEq in *. assert(isPDT part s).
      { apply partitionsArePDT; trivial; intuition. }
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryAddr in *. unfold sh1entryPDchild in *.
      simpl in *. destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSceSh1;
        try(exfalso; congruence). destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull).
      rewrite HgetChildrenEq; assumption.
      (* END pdchildIsPDT *)
    }

    assert(childBlockNullIfChildNull newS).
    { (* BEGIN childBlockNullIfChildNull newS *)
      assert(Hcons0: childBlockNullIfChildNull s) by intuition.
      intros part block sh1entryaddr HpartBisIsPart HblockMapped Hsh1 HPDchild. rewrite HgetPartsEq in *.
      unfold sh1entryInChildLocation. assert(isPDT part s).
      { apply partitionsArePDT; trivial; intuition. }
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryAddr in *. unfold sh1entryPDchild in *.
      simpl in *. destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSceSh1;
        try(exfalso; congruence). destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr HpartBisIsPart HblockMapped Hsh1 HPDchild).
      unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). destruct Hcons0. split; trivial. intro. exfalso; congruence.
      (* END pdchildIsPDT *)
    }

    assert(accessibleBlocksArePresent newS).
    { (* BEGIN accessibleBlocksArePresent newS *)
      assert(Hcons0: accessibleBlocksArePresent s) by intuition. intros block HAflag. unfold bentryAFlag in *.
      unfold bentryPFlag. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block) eqn:HbeqSh1Block; try(congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      apply Hcons0; assumption.
      (* END childLocHasSameStart *)
    }

    unfold consistency1. intuition.
  }

  assert(noDupMappedPaddrList newS).
  { (* BEGIN noDupMappedPaddrList newS *)
    assert(Hcons0: noDupMappedPaddrList s) by (unfold consistency2 in *; intuition).
    intros partition HpartIsPDT. unfold isPDT in *. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition HpartIsPDT). rewrite HgetMappedPEq; trivial.
    (* END noDupMappedPaddrList *)
  }

  assert(accessibleParentPaddrIsAccessibleIntoChild newS).
  { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild newS *)
    assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s) by (unfold consistency2 in *; intuition).
    intros pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
    rewrite HgetPartsEq in *. assert(isPDT pdparent s) by (apply partitionsArePDT; intuition).
    rewrite HgetChildrenEq in *; trivial. assert(isPDT child s) by (apply childrenArePDT with pdparent; intuition).
    rewrite HgetAccMappedPEq in *; trivial. rewrite HgetMappedPEq in *; trivial.
    specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild).
    trivial.
    (* END accessibleParentPaddrIsAccessibleIntoChild *)
  }

  assert(sharedBlockPointsToChild newS).
  { (* BEGIN sharedBlockPointsToChild newS *)
    assert(Hcons0: sharedBlockPointsToChild s) by (unfold consistency2 in *; intuition).
    intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParent HblockParentMapped Hsh1.
    rewrite HgetPartsEq in *. assert(isPDT pdparent s) by (apply partitionsArePDT; intuition).
    rewrite HgetChildrenEq in *; trivial. assert(isPDT child s) by (apply childrenArePDT with pdparent; intuition).
    rewrite HgetMappedBEq in *; trivial. unfold getUsedPaddr in *. rewrite HgetMappedPEq in *; trivial.
    rewrite HgetConfigPEq in *; trivial. unfold sh1entryAddr in *. simpl in Hsh1.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) blockParent) eqn:HbeqSceBlock;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(HaddrInBlockParents: In addr (getAllPaddrAux [blockParent] s)).
    {
      simpl in *. rewrite beqAddrFalse in HbeqSceBlock. rewrite HbeqSceBlock in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParents HblockParentMapped Hsh1). unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
    simpl.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (blockParent+sh1offset))) eqn:HbeqSceSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. rewrite HlookupSCE1 in *. assumption.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END sharedBlockPointsToChild *)
  }

  (*Note that blockAndNextAreSideBySide is false at this point*)

  (*False too*)
  (*assert(adressesRangePreservedIfOriginAndNextOk newS).
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk newS *)
    assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s) by (unfold consistency2 in *; intuition).
    intros partition pdentry block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE HstartBlock
      HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. simpl in *. rewrite HgetPartsEq in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(HpartIsPDT: isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial). unfold isBE in HblockIsBE.
    unfold bentryStartAddr in HstartBlock. unfold bentryEndAddr in HendBlock. unfold bentryPFlag in HPflag.
    simpl in *. destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(HparentOfPart: parentOfPartitionIsPartition s) by intuition.
    specialize(HparentOfPart partition pdentry HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
    specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & _).
    assert(HparentIsPDT: isPDT (parent pdentry) s) by (unfold isPDT; rewrite HlookupParent; trivial).
    rewrite HgetMappedBEq in *; trivial. unfold scentryNext in *. unfold scentryOrigin in *.
    simpl in *. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces.
    - rewrite <-DTL.beqAddrTrue in HbeqSces. rewrite HbeqSces in *. simpl in *. subst scentryaddr.
      assert(block1InCurrPartAddr = block).
      {
        apply CPaddrAddEq with (cst := scoffset); trivial. assert(Hblock1IsBE: isBE block1InCurrPartAddr s).
        { unfold isBE. rewrite HlookupBlock1. trivial. }
        assert(Hsce1IsSCEBis: wellFormedShadowCutIfBlockEntry s) by intuition.
        specialize(Hsce1IsSCEBis block1InCurrPartAddr Hblock1IsBE).
        destruct Hsce1IsSCEBis as [scentryaddr (Hsce1IsSCEBis & Hsce)]. subst scentryaddr. intro Hcontra.
        assert(isPADDR nullAddr s) by intuition. unfold isPADDR in *. rewrite Hcontra in *. unfold isSCE in *.
        destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      subst block. assert(HoriginParent: originIsParentBlocksStart s) by intuition.
      assert(HsceTriv: CPaddr (block1InCurrPartAddr+scoffset) = CPaddr (block1InCurrPartAddr+scoffset)) by trivial.
      assert(HoriginBis: scentryOrigin (CPaddr (block1InCurrPartAddr + scoffset)) startBlock s).
      { unfold scentryOrigin. rewrite HlookupSCE1. assumption. }
      specialize(HoriginParent partition pdentry block1InCurrPartAddr (CPaddr (block1InCurrPartAddr + scoffset))
        startBlock HpartIsPart HlookupPart HblockMapped HsceTriv HoriginBis).
      destruct HoriginParent as (HoriginParent & _). specialize(HoriginParent HbeqPartRoot).
      destruct HoriginParent as [blockParent (HblockParentMapped & HstartParent & Hblock1Incl)]. exists blockParent.
      split; trivial. unfold isBE. unfold bentryStartAddr in *. unfold bentryEndAddr. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSceBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceBlockP. subst blockParent. rewrite HlookupSCE1 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split.
      + destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
      + split; trivial. assert(HnextSide: blockAndNextAreSideBySide s) by (unfold consistency2 in *; intuition).
        assert(HbeqNext1Null: block2InCurrPartAddr <> nullAddr).
        {
          assert(isPADDR nullAddr s) by intuition. unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *.
          rewrite HlookupBlock2 in *. congruence.
        }
        specialize(HnextSide partition block1InCurrPartAddr (CPaddr (block1InCurrPartAddr + scoffset))
          block2InCurrPartAddr endBlock HpartIsPart HblockMapped HendBlock HsceTriv HbeqNext1Null Hnext1).
        assert(HnextCut: nextImpliesBlockWasCut s) by intuition.
        specialize(HnextCut partition pdentry block1InCurrPartAddr (CPaddr (block1InCurrPartAddr + scoffset))
          block2InCurrPartAddr endBlock HpartIsPart HlookupPart HblockMapped HendBlock HsceTriv HbeqNext1Null Hnext1
          HbeqPartRoot).
        destruct HnextCut as [blockParentBis [endParentBis (HblockPBisMapped & HendParentBis & HltEnds &
          Hblock1InclBis)]]. assert(blockParentBis = blockParent).
        {
          destruct (beqAddr blockParentBis blockParent) eqn:HbeqParents; try(rewrite DTL.beqAddrTrue; assumption).
          exfalso. rewrite <-beqAddrFalse in *. assert(HwellFormed: wellFormedBlock s) by intuition.
          specialize(HwellFormed block1InCurrPartAddr startBlock endBlock HPflag1 HstartBlock HendBlock).
          destruct HwellFormed as (HwellFormed & _).
          assert(In startBlock (getAllPaddrAux [block1InCurrPartAddr] s)).
          {
            simpl. destruct (lookup block1InCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartBlock. rewrite <-HendBlock. rewrite app_nil_r.
            apply getAllPaddrBlockIncl; lia.
          }
          assert(HstartInPPBis: In startBlock (getAllPaddrAux [blockParentBis] s)).
          { apply Hblock1InclBis. assumption. }
          assert(HnoDupMappedP: noDupMappedPaddrList s) by (unfold consistency2 in *; intuition).
          pose proof (DisjointPaddrInPart (parent pdentry) blockParentBis blockParent startBlock s HnoDupMappedP
            HparentIsPDT HblockPBisMapped HblockParentMapped HbeqParents HstartInPPBis) as Hcontra.
          contradict Hcontra. apply Hblock1Incl. assumption.
        }
        subst blockParentBis.
        assert(HparentsEnd: parentBlocksBoundsIfNoNext s) by (unfold consistency2 in *; intuition).
        specialize(HparentsEnd partition pdentry block2GlobalIdPDChild (CPaddr (block2InCurrPartAddr + scoffset))
          endBlock ).
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE
        HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot).
      destruct Hcons0 as [blockParent (HblockPMapped & HblockPIsBE & HstartP & HendP)]. exists blockParent.
      split; trivial. unfold isBE in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSceBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceBlockP. subst blockParent. rewrite HlookupSCE1 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }*)

  assert(childsBlocksPropsInParent newS).
  { (* BEGIN childsBlocksPropsInParent newS *)
    assert(Hcons0: childsBlocksPropsInParent s) by (unfold consistency2 in *; intuition).
    intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
      HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
      HPflagParent HlebStart HgebEnd. rewrite HgetPartsEq in *.
    assert(isPDT pdparent s) by (apply partitionsArePDT; intuition). rewrite HgetChildrenEq in *; trivial.
    assert(isPDT child s) by (apply childrenArePDT with pdparent; intuition). rewrite HgetMappedBEq in *; trivial.
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
    assert(HlookupBlockPEq: lookup blockParent (memory newS) beqAddr = lookup blockParent (memory s) beqAddr).
    {
      simpl. simpl in HPflagParent. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent)
        eqn:HbeqSceBlockP; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    rewrite HlookupBlockPEq in *. simpl in HstartChild. simpl in HendChild. simpl in HPflagChild.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockChild) eqn:HbeqSceBlockC;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
      HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
      HPflagParent HlebStart HgebEnd).
    destruct Hcons0 as (HcheckCh & HchildNotNull & HchildLocNotNull & HAflag). unfold checkChild in *.
    unfold bentryAFlag in *. rewrite HlookupBlockPEq.
    assert(HlookupSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory newS) beqAddr
      = lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr).
    {
      assert(Hres: wellFormedFstShadowIfBlockEntry s) by intuition.
      assert(HblockPIsBE: isBE blockParent s).
      {
        unfold isBE. destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; try(congruence).
        trivial.
      }
      specialize(Hres blockParent HblockPIsBE). unfold isSHE in *. unfold isSCE in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (blockParent+sh1offset))) eqn:HbeqSceSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. exfalso.
        destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    unfold sh1entryPDchild. unfold sh1entryInChildLocation in *. rewrite HlookupSh1Eq. split; trivial.
    split; trivial. split; trivial. intros blockIDInChild HchildLoc. apply HchildLocNotNull.
    destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr); try(congruence).
    destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial. intro HlocNotNull.
    specialize(HlocIsBE HlocNotNull). unfold isBE in *. simpl in HlocIsBE.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockIDInChild) eqn:HbeqSceLoc;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END childsBlocksPropsInParent *)
  }

  assert(noChildImpliesAddressesNotShared newS).
  { (* BEGIN noChildImpliesAddressesNotShared newS *)
    assert(Hcons0: noChildImpliesAddressesNotShared s) by (unfold consistency2 in *; intuition).
    intros partition pdentry block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild child addr
      HchildIsChild HaddrInBlock. simpl in HlookupPart. rewrite HgetPartsEq in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial).
    rewrite HgetChildrenEq in *; trivial. assert(isPDT child s) by (apply childrenArePDT with partition; intuition).
    rewrite HgetMappedBEq in *; trivial. rewrite HgetMappedPEq; trivial. unfold sh1entryPDchild in *.
    simpl in HPDchild. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) sh1entryaddr) eqn:HbeqSceSh1;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentry block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild).
    apply Hcons0; trivial. simpl in *. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block)
      eqn:HbeqSceBlock; try(exfalso; simpl in *; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END noChildImpliesAddressesNotShared *)
  }

  assert(kernelsAreNotAccessible newS).
  { (* BEGIN kernelsAreNotAccessible newS *)
    assert(Hcons0: kernelsAreNotAccessible s) by (unfold consistency2 in *; intuition).
    intros block startaddr Hstart HPflag HstartIsKS. unfold bentryStartAddr in *. unfold bentryPFlag in *.
    unfold bentryAFlag. unfold isKS in *. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block) eqn:HbeqSceBlock; try(congruence).
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) startaddr) eqn:HbeqSceStart;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 block startaddr Hstart HPflag HstartIsKS). assumption.
    (* END kernelsAreNotAccessible *)
  }

  assert(childLocMappedInChild newS).
  { (* BEGIN childLocMappedInChild newS *)
    assert(Hcons0: childLocMappedInChild s) by (unfold consistency2 in *; intuition).
    intros part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1 HPDchild Hloc
      HbeqIdChildNull Hstart HstartNotKS.
    rewrite HgetPartsEq in *. assert(isPDT part s).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryAddr in *. unfold sh1entryInChildLocationWeak in *.
    unfold sh1entryPDchild in *. unfold bentryStartAddr in Hstart. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSceSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (*assert(Hlocs: sh1entryInChildLocation sh1entryaddr blockChild s).
    {
      unfold sh1entryInChildLocation. destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). destruct Hloc as (Hloc & HlocIsBE). split; trivial. unfold isBE in *. simpl in *.
      intro HbeqLocNull. specialize(HlocIsBE HbeqLocNull).
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) blockChild) eqn:HbeqSceBC; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }*)
    assert(HstartNotKSs: ~isKS startaddr s).
    {
      contradict HstartNotKS. unfold isKS in *. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) startaddr) eqn:HbeqSceStart.
      { rewrite <-DTL.beqAddrTrue in HbeqSceStart. subst startaddr. rewrite HlookupSCE1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1 HPDchild
      Hloc HbeqIdChildNull Hstart HstartNotKSs). destruct Hcons0 as (HbeqBCNull & HBCMapped & HstartChild).
    split; trivial. assert(isPDT idchild s).
    {
      unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
      destruct (lookup idchild (memory s) beqAddr); try(simpl in *; congruence).
      destruct v; try(simpl in *; congruence). trivial.
    }
    rewrite HgetMappedBEq; trivial. split; trivial. unfold bentryStartAddr in *. simpl.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) blockChild) eqn:HbeqSceBC.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceBC. subst blockChild. rewrite HlookupSCE1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END childLocMappedInChild *)
  }

  assert(childLocHasSameStart newS).
  { (* BEGIN childLocHasSameStart newS *)
    assert(Hcons0: childLocHasSameStart s) by (unfold consistency2 in *; intuition).
    intros part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1 HPDchild Hloc
      HbeqIdChildNull HbeqBCNull startaddr Hstart.
    rewrite HgetPartsEq in *. assert(isPDT part s).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryAddr in *. unfold sh1entryInChildLocationWeak in *.
    unfold sh1entryPDchild in *. unfold bentryStartAddr in Hstart. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSceSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1 HPDchild
      Hloc HbeqIdChildNull HbeqBCNull startaddr Hstart). unfold bentryStartAddr in *. simpl.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) blockChild) eqn:HbeqSceBC.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceBC. subst blockChild. rewrite HlookupSCE1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END childLocHasSameStart *)
  }

  assert(verticalSharing newS).
  { (* BEGIN verticalSharing newS *)
    intros pdparent child HparentIsPart HchildIsChild. rewrite HgetPartsEq in *.
    assert(isPDT pdparent s) by (apply partitionsArePDT; intuition). rewrite HgetChildrenEq in *; trivial.
    rewrite HgetMappedPEq; trivial. unfold getUsedPaddr.
    assert(isPDT child s) by (apply childrenArePDT with pdparent; intuition). rewrite HgetMappedPEq; trivial.
    rewrite HgetConfigPEq; trivial. specialize(HVS pdparent child HparentIsPart HchildIsChild). apply HVS.
    (* END verticalSharing *)
  }

  assert(partitionsIsolation newS).
  { (* BEGIN partitionsIsolation newS *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren. rewrite HgetPartsEq in *.
    assert(isPDT pdparent s) by (apply partitionsArePDT; intuition). rewrite HgetChildrenEq in *; trivial.
    unfold getUsedPaddr. assert(isPDT child1 s) by (apply childrenArePDT with pdparent; intuition).
    assert(isPDT child2 s) by (apply childrenArePDT with pdparent; intuition). rewrite HgetMappedPEq; trivial.
    rewrite HgetMappedPEq; trivial. rewrite HgetConfigPEq; trivial. rewrite HgetConfigPEq; trivial.
    specialize(HPI pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren). assumption.
    (* END partitionsIsolation *)
  }

  assert(kernelDataIsolation newS).
  { (* BEGIN kernelDataIsolation newS *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart. rewrite HgetPartsEq in *.
    assert(isPDT part1 s) by (apply partitionsArePDT; intuition). rewrite HgetAccMappedPEq; trivial.
    assert(isPDT part2 s) by (apply partitionsArePDT; intuition). rewrite HgetConfigPEq; trivial.
    specialize(HKDI part1 part2 Hpart1IsPart Hpart2IsPart). assumption.
    (* END kernelDataIsolation *)
  }

  instantiate(1 := fun _ s =>
    exists s0 scentry1 sh1entryaddr1 sh1entryaddr2,
      s = {|
            currentPartition := currentPartition s0;
            memory :=
              add (CPaddr (block1InCurrPartAddr + scoffset))
                (SCE {| origin := origin scentry1; next := block2Next |}) (memory s0) beqAddr
          |}
      /\ block1InCurrPartAddr = idBlockToMerge1
      /\ block2InCurrPartAddr = idBlockToMerge2
      /\ consistency1 s
      /\ noDupMappedPaddrList s
      /\ accessibleParentPaddrIsAccessibleIntoChild s
      /\ sharedBlockPointsToChild s
      /\ childsBlocksPropsInParent s
      /\ noChildImpliesAddressesNotShared s
      /\ kernelsAreNotAccessible s
      /\ childLocMappedInChild s
      /\ childLocHasSameStart s
      /\ verticalSharing s
      /\ partitionsIsolation s
      /\ kernelDataIsolation s
      /\ currentPart = currentPartition s
      /\ sh1entryAddr block1InCurrPartAddr sh1entryaddr1 s
      /\ sh1entryAddr block2InCurrPartAddr sh1entryaddr2 s
      /\ sh1entryPDchild sh1entryaddr2 nullAddr s
      /\ bentryAFlag block1InCurrPartAddr true s
      /\ bentryAFlag block2InCurrPartAddr true s
      /\ bentryPFlag block2InCurrPartAddr true s
      /\ bentryPFlag block1InCurrPartAddr true s
      /\ sh1entryPDchild sh1entryaddr1 nullAddr s
      /\ In block2InCurrPartAddr (getMappedBlocks currentPart s)
      /\ In block1InCurrPartAddr (getMappedBlocks currentPart s)
      /\ consistency s0
      /\ verticalSharing s0
      /\ partitionsIsolation s0
      /\ kernelDataIsolation s0
      /\ currentPartition s = currentPartition s0
      /\ getPartitions multiplexer s = getPartitions multiplexer s0
      /\ (forall partition, isPDT partition s0 -> getChildren partition s = getChildren partition s0)
      /\ (forall partition, isPDT partition s0 -> getMappedBlocks partition s = getMappedBlocks partition s0)
      /\ lookup (CPaddr (block1InCurrPartAddr + scoffset)) (memory s0) beqAddr = Some (SCE scentry1)
      /\ sh1entryAddr block1InCurrPartAddr sh1entryaddr1 s0
      /\ sh1entryAddr block2InCurrPartAddr sh1entryaddr2 s0
      /\ sh1entryPDchild sh1entryaddr2 block2GlobalIdPDChild s0
      /\ bentryAFlag block1InCurrPartAddr true s0
      /\ bentryAFlag block2InCurrPartAddr true s0
      /\ bentryPFlag block2InCurrPartAddr true s0
      /\ bentryPFlag block1InCurrPartAddr true s0
      /\ sh1entryPDchild sh1entryaddr1 nullAddr s0
      /\ In block2InCurrPartAddr (getMappedBlocks currentPart s0)
      /\ In block1InCurrPartAddr (getMappedBlocks currentPart s0)
      /\ scentryNext (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr s0
      /\ scentryNext (CPaddr (block2InCurrPartAddr + scoffset)) block2Next s0
    ).
    exists s. exists scentry1. exists sh1entryaddr1. exists sh1entryaddr2. unfold bentryAFlag. unfold bentryPFlag.
    unfold sh1entryPDchild in *. unfold sh1entryAddr in *. simpl. subst block2GlobalIdPDChild.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block1InCurrPartAddr) eqn:HbeqSceBlock1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceBlock1. rewrite HbeqSceBlock1 in *. rewrite HlookupSCE1 in *.
      exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock2.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceBlock2. rewrite HbeqSceBlock2 in *. rewrite HlookupSCE1 in *.
      exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) sh1entryaddr2) eqn:HbeqSceSh12.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceSh12. rewrite HbeqSceSh12 in *. rewrite HlookupSCE1 in *.
      exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) sh1entryaddr1) eqn:HbeqSceSh11.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceSh11. rewrite HbeqSceSh11 in *. rewrite HlookupSCE1 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    assert(isPDT currentPart s).
    {
      unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
      destruct (lookup currentPart (memory s) beqAddr); try(simpl in *; congruence).
      destruct v; try(simpl in *; congruence). trivial.
    }
    rewrite HgetMappedBEq; trivial. unfold consistency; intuition. unfold consistency1; intuition.
}
intro. eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr **)
  eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. simpl.
  split. apply Hprops.
  destruct Hprops as [s0 [scentry1 [sh1entryaddr1 [sh1entryadd2 (Hs & Hblock1Eq & Hblock2Eq & Hconsist1s &
    HnoDupMapped & Haccess & Hshared & HchildBlockProp & HnoChild & HkernNotAcc & HlocProps & HsameStart & HVS & HPI &
    HKDI & Hcurr & Hsh11 & Hsh12 & HPDchild2 & HAflag1 & HAflag2 & HPflag2 & HPflag1 & HPDchild1 & Hblock2Mapped &
    Hblock1Mapped & Hconsists0 & HVSs0 & HPIs0 & HKDIs0 & HcurrEqs0 & HgetPartsEqs0 & HgetChildrenEqs0 &
    HgetMappedBEqs0 & HlookupSce1 & Hsh11s0 & Hsh12s0 & HPDchild2s0 & HAflag1s0 & HAflag2s0 & HPflag2s0 & HPflag1s0 &
    HPDchild1s0 & Hblock2Mappeds0 & Hblock1Mappeds0 & Hsce1s0 & Hsce2s0)]]]]. unfold isBE. unfold sh1entryAddr in *.
  destruct (lookup block2InCurrPartAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
}
intro block2End. eapply bindRev.
{ (** MAL.writeBlockEndFromBlockEntryAddr **)
  eapply weaken. apply writeBlockEndFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as ([s0 [scentry1 [sh1entryaddr1 [sh1entryaddr2 (Hs & Hblock1Eq & Hblock2Eq & Hconsist1s &
    HnoDupMapped & Haccess & Hshared & HchildBlockProp & HnoChild & HkernNotAcc & HlocProps & HsameStart & HVS &
    HPI & HKDI & Hcurr
    & Hsh11 & Hsh12 & HPDchild2 & HAflag1 & HAflag2 & HPflag2 & HPflag1 & HPDchild1 & Hblock2Mapped & Hblock1Mapped &
    Hconsists0 & HVSs0 & HPIs0 & HKDIs0 & HcurrEqs0 & HgetPartsEqs0 & HgetChildrenEqs0 & HgetMappedBEqs0 &
    HlookupSce1s0 & Hsh11s0 & Hsh12s0 & HPDchild2s0 & HAflag1s0 & HAflag2s0 & HPflag2s0 & HPflag1s0 & HPDchild1s0 &
    Hblock2Mappeds0 & Hblock1Mappeds0 & Hsce1s0 & Hsce2s0)]]]] & HendBlock2).
  assert(HlookupBlock1: exists bentry1, lookup block1InCurrPartAddr (memory s) beqAddr = Some (BE bentry1)).
  {
    unfold sh1entryAddr in *. destruct (lookup block1InCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists b. reflexivity.
  }
  destruct HlookupBlock1 as [bentry1 HlookupBlock1]. exists bentry1. split; trivial.
  assert(HnewB: exists l l0, CBlockEntry (read bentry1) (write bentry1) (exec bentry1) (present bentry1)
                      (accessible bentry1) (blockindex bentry1)
                      (CBlock (startAddr (blockrange bentry1)) block2End)
            = {|
                read := read bentry1;
                write := write bentry1;
                exec := exec bentry1;
                present := present bentry1;
                accessible := accessible bentry1;
                blockindex := blockindex bentry1;
                blockrange := {|
                                startAddr := startAddr (blockrange bentry1);
                                endAddr := block2End;
                                Hsize := ADT.CBlock_obligation_1 (startAddr (blockrange bentry1)) block2End l0
                              |};
                Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry1) l
              |}).
  {
    unfold CBlockEntry. pose proof (Hidx bentry1).
    destruct (lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia). exists l. unfold CBlock.
    assert(block2End <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
    destruct (le_dec (block2End - startAddr (blockrange bentry1)) maxIdx); try(lia). exists l0. reflexivity.
  }

  instantiate(1 := fun _ s =>
    exists s1 s0 scentry1 sh1entryaddr1 sh1entryaddr2 bentry1 pdentryCurr,
      s = {|
            currentPartition := currentPartition s1;
            memory :=
              add block1InCurrPartAddr
                (BE
                   (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) (present bentry1)
                      (accessible bentry1) (blockindex bentry1)
                      (CBlock (startAddr (blockrange bentry1)) block2End)))
                (memory s1) beqAddr
          |}
      /\ (exists l l0, CBlockEntry (read bentry1) (write bentry1) (exec bentry1) (present bentry1)
                      (accessible bentry1) (blockindex bentry1)
                      (CBlock (startAddr (blockrange bentry1)) block2End)
            = {|
                read := read bentry1;
                write := write bentry1;
                exec := exec bentry1;
                present := present bentry1;
                accessible := accessible bentry1;
                blockindex := blockindex bentry1;
                blockrange := {|
                                startAddr := startAddr (blockrange bentry1);
                                endAddr := block2End;
                                Hsize := ADT.CBlock_obligation_1 (startAddr (blockrange bentry1)) block2End l0
                              |};
                Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry1) l
              |})
      /\ s1 = {|
                currentPartition := currentPartition s0;
                memory :=
                  add (CPaddr (block1InCurrPartAddr + scoffset))
                    (SCE {| origin := origin scentry1; next := block2Next |}) (memory s0) beqAddr
              |}
      /\ block1InCurrPartAddr = idBlockToMerge1
      /\ block2InCurrPartAddr = idBlockToMerge2
      /\ endAddr (blockrange bentry1) < block2End
      /\ Constants.minBlockSize <= block2End - endAddr (blockrange bentry1)
      /\ block1InCurrPartAddr <> block2InCurrPartAddr
      /\ currentPartition s = currentPartition s1
      /\ getPartitions multiplexer s = getPartitions multiplexer s1
      /\ (forall partition, isPDT partition s1 -> getChildren partition s = getChildren partition s1)
      /\ (forall partition, getMappedBlocks partition s = getMappedBlocks partition s1)
      /\ lookup currentPart (memory s1) beqAddr = Some (PDT pdentryCurr)
      /\ lookup block1InCurrPartAddr (memory s1) beqAddr = Some (BE bentry1)
      /\ consistency1 s
      /\ consistency1 s1
      /\ noDupMappedPaddrList s1
      /\ accessibleParentPaddrIsAccessibleIntoChild s1
      /\ sharedBlockPointsToChild s1
      /\ childsBlocksPropsInParent s1
      /\ noChildImpliesAddressesNotShared s1
      /\ kernelsAreNotAccessible s1
      /\ childLocMappedInChild s1
      /\ childLocHasSameStart s1
      /\ verticalSharing s1
      /\ partitionsIsolation s1
      /\ kernelDataIsolation s1
      /\ currentPart = currentPartition s1
      /\ sh1entryAddr block1InCurrPartAddr sh1entryaddr1 s1
      /\ sh1entryAddr block2InCurrPartAddr sh1entryaddr2 s1
      /\ sh1entryPDchild sh1entryaddr2 nullAddr s1
      /\ bentryAFlag block1InCurrPartAddr true s1
      /\ bentryAFlag block2InCurrPartAddr true s1
      /\ bentryPFlag block2InCurrPartAddr true s1
      /\ bentryPFlag block1InCurrPartAddr true s1
      /\ bentryStartAddr block2InCurrPartAddr (endAddr (blockrange bentry1)) s1
      /\ sh1entryPDchild sh1entryaddr1 nullAddr s1
      /\ In block2InCurrPartAddr (getMappedBlocks currentPart s1)
      /\ In block1InCurrPartAddr (getMappedBlocks currentPart s1)
      /\ consistency s0
      /\ verticalSharing s0
      /\ partitionsIsolation s0
      /\ kernelDataIsolation s0
      /\ currentPartition s1 = currentPartition s0
      /\ getPartitions multiplexer s1 = getPartitions multiplexer s0
      /\ (forall partition, isPDT partition s0 -> getChildren partition s1 = getChildren partition s0)
      /\ (forall partition, isPDT partition s0 -> getMappedBlocks partition s1 = getMappedBlocks partition s0)
      /\ lookup (CPaddr (block1InCurrPartAddr + scoffset)) (memory s0) beqAddr = Some (SCE scentry1)
      /\ sh1entryAddr block1InCurrPartAddr sh1entryaddr1 s0
      /\ sh1entryAddr block2InCurrPartAddr sh1entryaddr2 s0
      /\ sh1entryPDchild sh1entryaddr2 block2GlobalIdPDChild s0
      /\ bentryAFlag block1InCurrPartAddr true s0
      /\ bentryAFlag block2InCurrPartAddr true s0
      /\ bentryPFlag block2InCurrPartAddr true s0
      /\ bentryPFlag block1InCurrPartAddr true s0
      /\ sh1entryPDchild sh1entryaddr1 nullAddr s0
      /\ In block2InCurrPartAddr (getMappedBlocks currentPart s0)
      /\ In block1InCurrPartAddr (getMappedBlocks currentPart s0)
      /\ scentryNext (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr s0
      /\ scentryNext (CPaddr (block2InCurrPartAddr + scoffset)) block2Next s0
      /\ bentryStartAddr block2InCurrPartAddr (endAddr (blockrange bentry1)) s0
      /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentryCurr)
      /\ bentryEndAddr block2InCurrPartAddr block2End s0
      /\ (currentPart <> constantRootPartM
          -> exists parentBlock12 startP endP, In parentBlock12 (getMappedBlocks (parent pdentryCurr) s0)
                /\ bentryStartAddr parentBlock12 startP s0
                /\ bentryEndAddr parentBlock12 endP s0
                /\ startP <= startAddr (blockrange bentry1)
                /\ endP >= block2End)
    ).
  set(newS := {|
                currentPartition := currentPartition s;
                memory :=
                  add block1InCurrPartAddr
                    (BE
                        (CBlockEntry (read bentry1) (write bentry1) (exec bentry1)
                          (present bentry1) (accessible bentry1) (blockindex bentry1)
                          (CBlock (startAddr (blockrange bentry1)) block2End)))
                    (memory s) beqAddr
              |}).
  assert(HcurrEq: currentPartition newS = currentPartition s) by reflexivity.
  assert(HgetPartsEq: getPartitions multiplexer newS = getPartitions multiplexer s).
  {
    apply getPartitionsEqBEPDflagFalse with bentry1 sh1entryaddr1; trivial.
    - unfold consistency1 in *; intuition.
    - unfold consistency1 in *; intuition.
    - assert(HaccessPD: AccessibleNoPDFlag s) by (unfold consistency1 in *; intuition).
      assert(Hblock1BE: isBE block1InCurrPartAddr s) by (unfold isBE; rewrite HlookupBlock1; trivial).
      specialize(HaccessPD block1InCurrPartAddr sh1entryaddr1 Hblock1BE Hsh11 HAflag1). assumption.
  }
  destruct HnewB as [l [l0 HnewB]].
  assert(HgetChildrenEq: forall partition, isPDT partition s
    -> getChildren partition newS = getChildren partition s).
  {
    intros partition HpartIsPDT. apply getChildrenEqBENoStartNoPresentChange with bentry1; try(rewrite HnewB); auto.
  }
  assert(HgetMappedBEq: forall partition, getMappedBlocks partition newS = getMappedBlocks partition s).
  {
    intro partition. apply getMappedBlocksEqBENoChange with bentry1; try(rewrite HnewB); auto.
  }
  assert(HendBlock1: bentryEndAddr block1InCurrPartAddr (endAddr (blockrange bentry1)) s).
  { unfold bentryEndAddr. rewrite HlookupBlock1. reflexivity. }
  assert(HlookupBlock1s0: lookup block1InCurrPartAddr (memory s0) beqAddr = Some (BE bentry1)).
  {
    rewrite Hs in HlookupBlock1. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block1InCurrPartAddr) eqn:HbeqSceBlock;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HendBlock1s0: bentryEndAddr block1InCurrPartAddr (endAddr (blockrange bentry1)) s0).
  { unfold bentryEndAddr. rewrite HlookupBlock1s0. reflexivity. }
  assert(HwellFormed2: wellFormedBlock s) by (unfold consistency1 in *; intuition).
  assert(HnextSide: blockAndNextAreSideBySide s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
  assert(HcurrIsParts0: In currentPart (getPartitions multiplexer s0)).
  { subst currentPart. rewrite HcurrEqs0. unfold consistency in *; unfold consistency1 in *; intuition. }
  assert(HlookupCurrs0: exists pdentry, lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)).
  {
    apply isPDTLookupEq. apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
  }
  destruct HlookupCurrs0 as [pdentryCurr HlookupCurrs0].
  assert(HlookupCurr: lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)).
  {
    rewrite Hs. simpl. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) currentPart) eqn:HbeqSceCurr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceCurr. rewrite HbeqSceCurr in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HsceTriv: CPaddr (block1InCurrPartAddr+scoffset) = CPaddr (block1InCurrPartAddr+scoffset)) by reflexivity.
  assert(HbeqBlock2Null: block2InCurrPartAddr <> nullAddr).
  {
    intro Hcontra. assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    rewrite Hcontra in *. unfold isPADDR in *. unfold bentryPFlag in *.
    destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  specialize(HnextSide currentPart block1InCurrPartAddr (CPaddr (block1InCurrPartAddr + scoffset))
    block2InCurrPartAddr (endAddr (blockrange bentry1)) HcurrIsParts0 Hblock1Mappeds0 HendBlock1s0 HsceTriv
    HbeqBlock2Null Hsce1s0). destruct HnextSide as (HnextSide & _).
  assert(HlookupSce1: lookup (CPaddr (block1InCurrPartAddr + scoffset)) (memory s) beqAddr
    = Some (SCE {| origin := origin scentry1; next := block2Next |})).
  { rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity. }
  assert(HstartBlock2: bentryStartAddr block2InCurrPartAddr (endAddr (blockrange bentry1)) s).
  {
    unfold bentryStartAddr in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock2.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceBlock2. rewrite HbeqSceBlock2 in *. rewrite HlookupSce1s0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(HwellFormed2 block2InCurrPartAddr (endAddr (blockrange bentry1)) block2End HPflag2 HstartBlock2
    HendBlock2). destruct HwellFormed2 as (HltStartEnd2 & Hsubstr2).
  assert(HendBlock2s0: bentryEndAddr block2InCurrPartAddr block2End s0).
  {
    unfold bentryEndAddr in *. rewrite Hs in HendBlock2. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock2;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HstartBlock1s0: bentryStartAddr block1InCurrPartAddr (startAddr (blockrange bentry1)) s0).
  { unfold bentryStartAddr. rewrite HlookupBlock1s0. trivial. }
  assert(HparentOfPart: parentOfPartitionIsPartition s0)
    by (unfold consistency in *; unfold consistency1 in *; intuition).
  specialize(HparentOfPart currentPart pdentryCurr HlookupCurrs0).
  destruct HparentOfPart as (HparentIsPartCurr & _ & HbeqParentCurr).
  assert(HparentBlock: currentPart <> constantRootPartM
    -> exists parentBlock12 startP endP, In parentBlock12 (getMappedBlocks (parent pdentryCurr) s0)
          /\ bentryStartAddr parentBlock12 startP s0
          /\ bentryEndAddr parentBlock12 endP s0
          /\ startP <= startAddr (blockrange bentry1)
          /\ endP >= block2End).
  {
    intro HbeqCurrRoot.
    assert(HblockCut: nextImpliesBlockWasCut s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HblockCut currentPart pdentryCurr block1InCurrPartAddr (CPaddr (block1InCurrPartAddr + scoffset))
      block2InCurrPartAddr (endAddr (blockrange bentry1)) HcurrIsParts0 HlookupCurrs0 Hblock1Mappeds0 HendBlock1s0
      HsceTriv HbeqBlock2Null Hsce1s0 HbeqCurrRoot).
    destruct HblockCut as [blockParent [endParent (HblockPMapped & HendP & HltEnds & Hincl)]]. exists blockParent.
    assert(HlookupBlockP: exists bentryP, lookup blockParent (memory s0) beqAddr = Some (BE bentryP)
      /\ bentryStartAddr blockParent (startAddr (blockrange bentryP)) s0).
    {
      unfold bentryEndAddr in *. unfold bentryStartAddr.
      destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists b. auto.
    }
    destruct HlookupBlockP as [bentryP (HlookupBlockP & HstartBlockP)]. exists (startAddr (blockrange bentryP)).
    exists endParent. split; trivial. split; trivial. split; trivial.
    assert(HstartInBlock: In (startAddr (blockrange bentry1)) (getAllPaddrAux [block1InCurrPartAddr] s0)).
    {
      simpl. rewrite HlookupBlock1s0. rewrite app_nil_r.
      assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
        HPflag1s0 HstartBlock1s0 HendBlock1s0). destruct Hwell as (Hwell & _).
      apply getAllPaddrBlockIncl; lia.
    }
    specialize(Hincl (startAddr (blockrange bentry1)) HstartInBlock). simpl in Hincl. rewrite HlookupBlockP in *.
    rewrite app_nil_r in *. apply getAllPaddrBlockInclRev in Hincl. destruct Hincl. split; trivial.
    assert(HblockEquiv2: blockInChildHasAtLeastEquivalentBlockInParent s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HparentIsPartCurr HbeqCurrRoot).
    destruct HparentIsPartCurr as ([parentEntry HlookupParent] & HparentIsPart).
    assert(HcurrIsChild: In currentPart (getChildren (parent pdentryCurr) s0)).
    {
      assert(Hres: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      specialize(Hres currentPart (parent pdentryCurr) HcurrIsParts0). apply Hres; trivial. unfold pdentryParent.
      rewrite HlookupCurrs0. reflexivity.
    }
    specialize(HblockEquiv2 (parent pdentryCurr) currentPart block2InCurrPartAddr (endAddr (blockrange bentry1))
      block2End HparentIsPart HcurrIsChild Hblock2Mappeds0 HnextSide HendBlock2s0 HPflag2s0).
    destruct HblockEquiv2 as [blockPBis [startPBis [endPBis (HblockPBisMapped & HstartBlockPBis & HendBlockPBis &
      HlebStarts & HgebEnds)]]].
    assert(HPflagP: bentryPFlag blockParent true s0).
    {
      apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentryPBis (HlookupBlockPBis & Hres)].
      unfold bentryPFlag. rewrite HlookupBlockPBis. auto.
    }
    assert(HbeqBlockParents: blockParent = blockPBis).
    {
      destruct (beqAddr blockParent blockPBis) eqn:HbeqBlockParents; try(rewrite DTL.beqAddrTrue; assumption).
      rewrite <-beqAddrFalse in *. exfalso.
      assert(HendInBlockP: In (endAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s0)).
      {
        assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(Hwell1: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(Hwell blockParent (startAddr (blockrange bentryP)) endParent HPflagP HstartBlockP HendP).
        specialize(Hwell1 block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
          HPflag1s0 HstartBlock1s0 HendBlock1s0). destruct Hwell as (Hwell & _). destruct Hwell1 as (Hwell1 & _).
        simpl. unfold bentryEndAddr in *. rewrite HlookupBlockP in *.
        rewrite app_nil_r. rewrite <-HendP. apply getAllPaddrBlockIncl; lia.
      }
      assert(HnoDupMappeds0: noDupMappedPaddrList s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      assert(HparentIsPDT: isPDT (parent pdentryCurr) s0) by (unfold isPDT; rewrite HlookupParent; trivial).
      pose proof (DisjointPaddrInPart (parent pdentryCurr) blockParent blockPBis(endAddr (blockrange bentry1)) s0
        HnoDupMappeds0 HparentIsPDT HblockPMapped HblockPBisMapped HbeqBlockParents HendInBlockP) as Hcontra.
      contradict Hcontra. simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      destruct (lookup blockPBis (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite app_nil_r. subst startPBis. subst endPBis.
      apply getAllPaddrBlockIncl; lia.
    }
    subst blockPBis. unfold bentryEndAddr in *. rewrite HlookupBlockP in *. rewrite <-HendP in *. subst endPBis. lia.
  }
  assert(HstartBlock1s: bentryStartAddr block1InCurrPartAddr (startAddr (blockrange bentry1)) s).
  {
    unfold bentryStartAddr in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block1InCurrPartAddr) eqn:HbeqSceBlock1.
    { rewrite <-DTL.beqAddrTrue in HbeqSceBlock1. rewrite HbeqSceBlock1 in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HbeqBlocks12: block1InCurrPartAddr <> block2InCurrPartAddr).
  {
    assert(HwellFormed1: wellFormedBlock s) by (unfold consistency1 in *; intuition).
    specialize(HwellFormed1 block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
      HPflag1 HstartBlock1s HendBlock1). destruct HwellFormed1 as (HwellFormed1 & _). unfold bentryStartAddr in *.
    intro Hcontra. rewrite Hcontra in *. rewrite HlookupBlock1 in *. rewrite HstartBlock2 in *. lia.
  }
  simpl. exists s. exists s0. exists scentry1. exists sh1entryaddr1. exists sh1entryaddr2. exists bentry1.
  exists pdentryCurr. intuition.
  exists l. exists l0. assumption.
  unfold consistency1. split.

  { (* BEGIN nullAddrExists newS *)
    assert(Hcons0: nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in *.
    unfold isPADDR in *. simpl. destruct (beqAddr block1InCurrPartAddr nullAddr) eqn:HbeqBlock1Null.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlock1Null. rewrite HbeqBlock1Null in *. rewrite HlookupBlock1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END nullAddrExists *)
  }

  split.
  { (* BEGIN wellFormedFstShadowIfBlockEntry newS *)
    assert(Hcons0: wellFormedFstShadowIfBlockEntry s) by (unfold consistency1 in *; intuition).
    intros block HblockIsBE. assert(HblockIsBEs: isBE block s).
    {
      unfold isBE in *. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 block HblockIsBEs). unfold isSHE in *. simpl.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite HbeqBlockSh1 in *. rewrite HlookupBlock1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END wellFormedFstShadowIfBlockEntry *)
  }

  split.
  { (* BEGIN PDTIfPDFlag newS *)
    assert(Hcons0: PDTIfPDFlag s) by (unfold consistency1 in *; intuition). intros idPDchild sh1entryaddr HcheckChild.
    unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr. unfold checkChild in *. unfold sh1entryAddr in *.
    simpl in *. destruct HcheckChild as (HcheckChild & Hsh1).
    destruct (beqAddr block1InCurrPartAddr idPDchild) eqn:HbeqBlocks.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst idPDchild. exfalso.
      assert(HaccessPD: AccessibleNoPDFlag s) by (unfold consistency1 in *; intuition).
      assert(Hblock1BE: isBE block1InCurrPartAddr s) by (unfold isBE; rewrite HlookupBlock1; trivial).
      specialize(HaccessPD block1InCurrPartAddr sh1entryaddr1 Hblock1BE Hsh11 HAflag1).
      destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(congruence). subst sh1entryaddr.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite HlookupBlock1 in *. subst sh1entryaddr1. unfold sh1entryPDflag in *.
      destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(HcheckChilds: true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s).
    {
      unfold checkChild. unfold sh1entryAddr.
      destruct (lookup idPDchild (memory s) beqAddr); try(exfalso; congruence). split; trivial.
      destruct v; try(exfalso; congruence).
      destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds).
    destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HPDT)]). split; trivial. split; trivial.
    exists startaddr. split; trivial. unfold entryPDT in *. simpl. rewrite beqAddrFalse in *. rewrite HbeqBlocks.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    destruct (lookup idPDchild (memory s) beqAddr); try(congruence). destruct v; try(congruence).
    destruct (beqAddr block1InCurrPartAddr (startAddr (blockrange b))) eqn:HbeqBlockStart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite HbeqBlockStart in *. rewrite HlookupBlock1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END PDTIfPDFlag *)
  }

  split.
  { (* BEGIN AccessibleNoPDFlag newS *)
    assert(Hcons0: AccessibleNoPDFlag s) by (unfold consistency1 in *; intuition).
    intros block sh1entryaddr HblockIsBE Hsh1 HAflag.
    assert(Hblocks: isBE block s /\ sh1entryAddr block sh1entryaddr s /\ bentryAFlag block true s).
    {
      unfold isBE in *. unfold sh1entryAddr in *. unfold bentryAFlag in *. simpl in *.
      destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in *. simpl in *. rewrite HlookupBlock1.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct Hblocks as (HblockIsBEs & Hsh1s & HAflags).
    specialize(Hcons0 block sh1entryaddr HblockIsBEs Hsh1s HAflags). unfold sh1entryPDflag in *. simpl.
    destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite HbeqBlockSh1 in *. rewrite HlookupBlock1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END AccessibleNoPDFlag *)
  }

  split.
  { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot newS *)
    assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
    intros partition pdentry HlookupPart HbeqFirstNull. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentry HlookupPart HbeqFirstNull). destruct Hcons0 as (HBE & HfirstFree).
    unfold isBE in *. unfold isFreeSlot in *. simpl.
    destruct (beqAddr block1InCurrPartAddr (firstfreeslot pdentry)) eqn:HbeqBlockFirst.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockFirst. rewrite HbeqBlockFirst in *. rewrite HlookupBlock1 in *.
      split; trivial.
      destruct (beqAddr (firstfreeslot pdentry) (CPaddr (firstfreeslot pdentry + sh1offset))) eqn:HbeqFirstFSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqFirstFSh1. rewrite <-HbeqFirstFSh1 in *. rewrite HlookupBlock1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HnewB. simpl.
      destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr (firstfreeslot pdentry) (CPaddr (firstfreeslot pdentry + scoffset))) eqn:HbeqFirstFSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqFirstFSce. rewrite <-HbeqFirstFSce in *. rewrite HlookupBlock1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (firstfreeslot pdentry) (memory s) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split; trivial.
      destruct (beqAddr block1InCurrPartAddr (CPaddr (firstfreeslot pdentry + sh1offset))) eqn:HbeqFirstFSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqFirstFSh1. rewrite <-HbeqFirstFSh1 in *. rewrite HlookupBlock1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr block1InCurrPartAddr (CPaddr (firstfreeslot pdentry + scoffset))) eqn:HbeqFirstFSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqFirstFSce. rewrite <-HbeqFirstFSce in *. rewrite HlookupBlock1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
  }

  split.
  { (* BEGIN multiplexerIsPDT newS *)
    assert(Hcons0: multiplexerIsPDT s) by (unfold consistency1 in *; intuition). unfold multiplexerIsPDT in *.
    unfold isPDT in *. simpl. destruct (beqAddr block1InCurrPartAddr multiplexer) eqn:HbeqBlockMult.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockMult. rewrite <-HbeqBlockMult in *. rewrite HlookupBlock1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END multiplexerIsPDT *)
  }

  split.
  { (* BEGIN currentPartitionInPartitionsList newS *)
    assert(Hcons0: currentPartitionInPartitionsList s) by (unfold consistency1 in *; intuition).
    unfold currentPartitionInPartitionsList in *. rewrite HcurrEq. rewrite HgetPartsEq. assumption.
    (* END currentPartitionInPartitionsList *)
  }

  split.
  { (* BEGIN wellFormedShadowCutIfBlockEntry newS *)
    assert(Hcons0: wellFormedShadowCutIfBlockEntry s) by (unfold consistency1 in *; intuition).
    intros block HblockIsBE. assert(HblockIsBEs: isBE block s).
    {
      unfold isBE in *. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 block HblockIsBEs). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr.
    split; trivial. unfold isSCE in *. simpl. destruct (beqAddr block1InCurrPartAddr scentryaddr) eqn:HbeqBlockSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *. rewrite HlookupBlock1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END wellFormedShadowCutIfBlockEntry *)
  }

  split.
  { (* BEGIN BlocksRangeFromKernelStartIsBE newS *)
    assert(Hcons0: BlocksRangeFromKernelStartIsBE s) by (unfold consistency1 in *; intuition).
    intros kernel idx HkernIsKS HltIdxKernEntries. assert(HkernIsKSs: isKS kernel s).
    {
      unfold isKS in *. simpl in *. destruct (beqAddr block1InCurrPartAddr kernel) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1. rewrite HnewB in *.
        simpl in *. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 kernel idx HkernIsKSs HltIdxKernEntries). unfold isBE in *. simpl.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (kernel + idx))) eqn:HbeqBlockIdx; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END BlocksRangeFromKernelStartIsBE *)
  }

  split.
  { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS newS *)
    assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s) by (unfold consistency1 in *; intuition).
    intros block idx HblockIsBE Hidx. assert(Hblocks: isBE block s /\ bentryBlockIndex block idx s).
    {
      unfold isBE in *. unfold bentryBlockIndex in *. simpl in *.
      destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in *. simpl in *. rewrite HlookupBlock1.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct Hblocks as (HblockIsBEs & Hidxs). specialize(Hcons0 block idx HblockIsBEs Hidxs). unfold isKS in *.
    simpl. destruct (beqAddr block1InCurrPartAddr (CPaddr (block - idx))) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1 in *. rewrite HnewB.
      auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END KernelStructureStartFromBlockEntryAddrIsKS *)
  }

  split.
  { (* BEGIN sh1InChildLocationIsBE newS *)
    assert(Hcons0: sh1InChildLocationIsBE s) by (unfold consistency1 in *; intuition).
    intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull. unfold isBE. simpl in *.
    destruct (beqAddr block1InCurrPartAddr (inChildLocation sh1entry)) eqn:HbeqBlocks; trivial.
    destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). assumption.
    (* END sh1InChildLocationIsBE *)
  }

  split.
  { (* BEGIN StructurePointerIsKS newS *)
    assert(Hcons0: StructurePointerIsKS s) by (unfold consistency1 in *; intuition).
    intros partition pdentry HlookupPart HbeqStructNull. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentry HlookupPart HbeqStructNull). unfold isKS in *. simpl.
    destruct (beqAddr block1InCurrPartAddr (structure pdentry)) eqn:HbeqBlockStruct.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockStruct. rewrite HbeqBlockStruct in *. rewrite HlookupBlock1 in *.
      rewrite HnewB. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END StructurePointerIsKS *)
  }

  split.
  { (* BEGIN NextKSIsKS newS *)
    assert(Hcons0: NextKSIsKS s) by (unfold consistency1 in *; intuition).
    intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull.
    assert(Hkern: isKS kernel s /\ nextKSAddr kernel nextKSaddr s).
    {
      unfold isKS in *. unfold nextKSAddr in *. simpl in *.
      destruct (beqAddr block1InCurrPartAddr kernel) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1. rewrite HnewB in *.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct Hkern as (HkernIsKSs & HnextAddrs). unfold nextKSentry in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr nextKSaddr) eqn:HbeqBlockNext; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKSs HnextAddrs HnextKSAddr HbeqNextNull). unfold isKS in *.
    simpl. destruct (beqAddr block1InCurrPartAddr nextKS) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1 in *. rewrite HnewB.
      auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END NextKSIsKS *)
  }

  split.
  { (* BEGIN NextKSOffsetIsPADDR newS *)
    assert(Hcons0: NextKSOffsetIsPADDR s) by (unfold consistency1 in *; intuition).
    intros kernel nextKSaddr HkernIsKS HnextAddr.
    assert(Hkern: isKS kernel s /\ nextKSAddr kernel nextKSaddr s).
    {
      unfold isKS in *. unfold nextKSAddr in *. simpl in *.
      destruct (beqAddr block1InCurrPartAddr kernel) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1. rewrite HnewB in *.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct Hkern as (HkernIsKSs & HnextAddrs). specialize(Hcons0 kernel nextKSaddr HkernIsKSs HnextAddrs).
    destruct Hcons0 as (HnextIsPADDR & HbeqNextNull). split; trivial. unfold isPADDR in *. simpl.
    destruct (beqAddr block1InCurrPartAddr nextKSaddr) eqn:HbeqBlockNext.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite HbeqBlockNext in *. rewrite HlookupBlock1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END NextKSOffsetIsPADDR *)
  }

  assert(HgetFreeEq: forall partition, isPDT partition s
    -> getFreeSlotsList partition newS = getFreeSlotsList partition s).
  {
    intros partition HpartIsPDT. assert(HnoDupFree: NoDupInFreeSlotsList s) by (unfold consistency1 in *; intuition).
    assert(Hfree: freeSlotsListIsFreeSlot s) by (unfold consistency1 in *; intuition).
    specialize(Hfree partition block1InCurrPartAddr (getFreeSlotsList partition s)
      (filterOptionPaddr (getFreeSlotsList partition s)) HpartIsPDT).
    unfold isPDT in *. destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). specialize(HnoDupFree partition p HlookupPart).
    destruct HnoDupFree as [optFreeList (Hlist & HwellFormedList & HnoDupList)]. subst optFreeList.
    assert(Hwell: getFreeSlotsList partition s = getFreeSlotsList partition s
      /\ wellFormedFreeSlotsList (getFreeSlotsList partition s) <> False) by auto.
    specialize(Hfree Hwell). unfold getFreeSlotsList in *. simpl.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *. rewrite HlookupBlock1 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite HlookupPart in *. destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
    rewrite <-beqAddrFalse in *.
    assert(HfirstProps: FirstFreeSlotPointerIsBEAndFreeSlot s) by (unfold consistency1 in *; intuition).
    specialize(HfirstProps partition p HlookupPart HbeqFirstNull).
    destruct HfirstProps as (HfirstIsBE & HfirstIsFree). apply getFreeSlotsListRecEqBE; trivial.
    - intro Hcontra. rewrite Hcontra in *. unfold isFreeSlot in *. unfold bentryPFlag in *.
      rewrite HlookupBlock1 in *.
      destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (lookup (CPaddr (block1InCurrPartAddr + scoffset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HfirstIsFree as (_ & _ & _ & _ & Hpres & _). congruence.
    - unfold isBE. rewrite HlookupBlock1. trivial.
    - intro Hcontra. assert(HblockIsFree: isFreeSlot block1InCurrPartAddr s).
      {
        apply Hfree; auto. intro HbeqBlockNull. assert(isPADDR nullAddr s) by (unfold consistency1 in *; intuition).
        unfold isPADDR in *. rewrite HbeqBlockNull in *. rewrite HlookupBlock1 in *. congruence.
      }
      unfold isFreeSlot in *. unfold bentryPFlag in *. rewrite HlookupBlock1 in *.
      destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (lookup (CPaddr (block1InCurrPartAddr + scoffset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HblockIsFree as (_ & _ & _ & _ & Hpres & _). congruence.
  }

  split.
  { (* BEGIN NoDupInFreeSlotsList newS *)
    assert(Hcons0: NoDupInFreeSlotsList s) by (unfold consistency1 in *; intuition).
    intros partition pdentry HlookupPart. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentry HlookupPart).
    destruct Hcons0 as [optFreeList (Hlist & HwellFormedList & HnoDupList)]. exists optFreeList. split; auto.
    subst optFreeList. apply eq_sym. apply HgetFreeEq. unfold isPDT. rewrite HlookupPart. trivial.
    (* END NoDupInFreeSlotsList *)
  }

  split.
  { (* BEGIN freeSlotsListIsFreeSlot newS *)
    assert(Hcons0: freeSlotsListIsFreeSlot s) by (unfold consistency1 in *; intuition).
    intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
    unfold isPDT in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite HgetFreeEq in HwellFormed; trivial.
    specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList
      HbeqAddrNull). unfold isFreeSlot in *. simpl.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (addr + sh1offset))) eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite HbeqBlockSh1 in *. rewrite HlookupBlock1 in *.
      exfalso. destruct (lookup addr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    destruct (beqAddr block1InCurrPartAddr (CPaddr (addr + scoffset))) eqn:HbeqBlockSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *. rewrite HlookupBlock1 in *.
      exfalso. destruct (lookup addr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (lookup (CPaddr (addr + sh1offset)) (memory s) beqAddr); try(congruence). destruct v; try(congruence).
    }
    destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlockAddr.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlock1 in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (block1InCurrPartAddr + scoffset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). rewrite HnewB. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END freeSlotsListIsFreeSlot *)
  }

  split.
  { (* BEGIN DisjointFreeSlotsLists newS *)
    assert(Hcons0: DisjointFreeSlotsLists s) by (unfold consistency1 in *; intuition).
    intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr part1) eqn:HbeqBlockPart1; try(exfalso; congruence).
    destruct (beqAddr block1InCurrPartAddr part2) eqn:HbeqBlockPart2; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). rewrite HgetFreeEq; trivial.
    rewrite HgetFreeEq; trivial.
    (* END DisjointFreeSlotsLists *)
  }

  assert(HgetKSEq: forall partition, getKSEntries partition newS = getKSEntries partition s).
  {
    intro partition. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock1. trivial.
  }

  split.
  { (* BEGIN inclFreeSlotsBlockEntries newS *)
    assert(Hcons0: inclFreeSlotsBlockEntries s) by (unfold consistency1 in *; intuition).
    intros partition HpartIsPDT. unfold isPDT in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite HgetFreeEq; trivial. specialize(Hcons0 partition HpartIsPDT). rewrite HgetKSEq. assumption.
    (* END inclFreeSlotsBlockEntries *)
  }

  split.
  { (* BEGIN DisjointKSEntries newS *)
    assert(Hcons0: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
    intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr part1) eqn:HbeqBlockPart1; try(exfalso; congruence).
    destruct (beqAddr block1InCurrPartAddr part2) eqn:HbeqBlockPart2; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). rewrite HgetKSEq. rewrite HgetKSEq. assumption.
    (* END DisjointKSEntries *)
  }

  split.
  { (* BEGIN noDupPartitionTree newS *)
    assert(Hcons0: noDupPartitionTree s) by (unfold consistency1 in *; intuition). unfold noDupPartitionTree.
    rewrite HgetPartsEq. assumption.
    (* END noDupPartitionTree *)
  }

  split.
  { (* BEGIN isParent newS *)
    assert(Hcons0: isParent s) by (unfold consistency1 in *; intuition).
    intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEq in *.
    assert(HparentIsPDT: isPDT pdparent s) by (apply partitionsArePDT; unfold consistency1 in *; intuition).
    rewrite HgetChildrenEq in *; trivial. specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild).
    assert(HpartIsPDT: isPDT partition s)
      by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition). unfold isPDT in *.
    unfold pdentryParent. simpl. destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst partition. rewrite HlookupBlock1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END isParent *)
  }

  split.
  { (* BEGIN isChild newS *)
    assert(Hcons0: isChild s) by (unfold consistency1 in *; intuition).
    intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEq in *.
    unfold pdentryParent in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
    rewrite HgetChildrenEq; trivial.
    assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). specialize(HparentOfPart partition p HlookupPart).
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqPartRoot). subst pdparent.
    destruct HparentIsPart as ([parentEntry HlookupParent] & _). unfold isPDT. rewrite HlookupParent. trivial.
    (* END isChild *)
  }

  split.
  { (* BEGIN noDupKSEntriesList newS *)
    assert(Hcons0: noDupKSEntriesList s) by (unfold consistency1 in *; intuition).
    intros partition HpartIsPDT. unfold isPDT in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HgetKSEq.
    specialize(Hcons0 partition HpartIsPDT). assumption.
    (* END noDupKSEntriesList *)
  }

  split.
  { (* BEGIN noDupMappedBlocksList newS *)
    assert(Hcons0: noDupMappedBlocksList s) by (unfold consistency1 in *; intuition).
    intros partition HpartIsPDT. unfold isPDT in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition HpartIsPDT). rewrite HgetMappedBEq. assumption.
    (* END noDupMappedBlocksList *)
  }

  split.
  { (* BEGIN wellFormedBlock newS *)
    assert(Hcons0: wellFormedBlock s) by (unfold consistency1 in *; intuition).
    intros block startaddr endaddr HPflag HstartBlock HendBlock. unfold bentryPFlag in *. unfold bentryStartAddr in *.
    unfold bentryEndAddr in *. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
    - rewrite HnewB in *. simpl in *. subst endaddr.
      assert(HstartBlock1: bentryStartAddr block1InCurrPartAddr startaddr s).
      { unfold bentryStartAddr. rewrite HlookupBlock1. assumption. }
      specialize(Hcons0 block1InCurrPartAddr startaddr (endAddr (blockrange bentry1)) HPflag1 HstartBlock1
        HendBlock1). split; lia.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
    (* END wellFormedBlock *)
  }

  split.
  { (* BEGIN parentOfPartitionIsPartition newS *)
    assert(Hcons0: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    intros partition pdentry HlookupPart. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentry HlookupPart). destruct Hcons0 as (HparentOfPart & Hparent). split; trivial.
    intro HbeqPartRoot. specialize(HparentOfPart HbeqPartRoot). rewrite HgetPartsEq.
    destruct HparentOfPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial. exists parentEntry.
    destruct (beqAddr block1InCurrPartAddr (parent pdentry)) eqn:HbeqBlockParent.
    { rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *. exfalso; congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END parentOfPartitionIsPartition *)
  }

  split.
  { (* BEGIN NbFreeSlotsISNbFreeSlotsInList newS *)
    assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s) by (unfold consistency1 in *; intuition).
    intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. unfold pdentryNbFreeSlots in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree). rewrite HgetFreeEq; trivial.
    (* END NbFreeSlotsISNbFreeSlotsInList *)
  }

  assert(HkernListEq: forall kernList partition, isListOfKernels kernList partition newS
    -> isListOfKernels kernList partition s).
  { intros kernList partition. apply isListOfKernelsEqBE. }

  split.
  { (* BEGIN maxNbPrepareIsMaxNbKernels newS *)
    assert(Hcons0: maxNbPrepareIsMaxNbKernels s) by (unfold consistency1 in *; intuition).
    intros partition kernList HlistOfKerns. apply HkernListEq in HlistOfKerns.
    specialize(Hcons0 partition kernList HlistOfKerns). assumption.
    (* END maxNbPrepareIsMaxNbKernels *)
  }

  split.
  { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent newS *)
    assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s) by (unfold consistency1 in *; intuition).
    intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild
      HendChild HPflagChild. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *.
    assert(HparentIsPDT: isPDT pdparent s) by (apply partitionsArePDT; unfold consistency1 in *; intuition).
    rewrite HgetChildrenEq in *; trivial. unfold bentryStartAddr in HstartChild. unfold bentryPFlag in HPflagChild.
    unfold bentryEndAddr in HendChild. simpl in *.
    destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in *. simpl in *. subst endChild.
      subst startChild. assert(HeqParts: child = currentPart).
      {
        destruct (beqAddr child currentPart) eqn:HbeqChildCurr; try(apply DTL.beqAddrTrue; assumption). exfalso.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition). rewrite <-beqAddrFalse in *.
        assert(HchildIsPDT: isPDT child s)
          by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
        assert(HcurrIsPDT: isPDT currentPart s)
          by (apply partitionsArePDT; try(rewrite HgetPartsEqs0); unfold consistency1 in *; intuition).
        specialize(Hdisjoint child currentPart HchildIsPDT HcurrIsPDT HbeqChildCurr).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMappedChild.
        apply InFilterPresentInList in Hblock1Mapped. specialize(Hdisjoint block1InCurrPartAddr HblockMappedChild).
        congruence.
      }
      subst child. assert(Hchild: isParent s) by (unfold consistency1 in *; intuition).
      specialize(Hchild currentPart pdparent HparentIsPart HchildIsChild). unfold pdentryParent in *.
      rewrite HlookupCurr in *. subst pdparent. assert(HbeqCurrRoot: currentPart <> constantRootPartM).
      {
        intro Hcontra. assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
        specialize(HparentOfPart currentPart pdentryCurr HlookupCurr). unfold isPDT in *.
        destruct HparentOfPart as (_ & HparentIsRoot & _). specialize(HparentIsRoot Hcontra).
        assert(isPADDR nullAddr s) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
        rewrite HparentIsRoot in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
        destruct v; congruence.
      }
      specialize(HparentBlock HbeqCurrRoot). destruct HparentBlock as [parentBlock12 [startP [endP (HblockPMapped &
        HstartP & HendP & HlebStart & HgebEnd)]]]. exists parentBlock12. exists startP. exists endP.
      assert(isPDT (parent pdentryCurr) s0).
      {
        rewrite HgetPartsEqs0 in *.
        apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
      }
      rewrite HgetMappedBEqs0; trivial. split; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
      destruct (beqAddr block1InCurrPartAddr parentBlock12) eqn:HbeqBlock1Parent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlock1Parent. rewrite HbeqBlock1Parent in *. unfold getMappedBlocks in *.
        exfalso. apply InFilterPresentInList in Hblock1Mappeds0. apply InFilterPresentInList in HblockPMapped.
        unfold isPDT in *.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HcurrIsPDT: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
        rewrite Hs in HparentIsPDT. simpl in HparentIsPDT.
        destruct (beqAddr (CPaddr (parentBlock12 + scoffset)) (parent pdentryCurr)) eqn:HbeqSceParent;
          try(congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hdisjoint (parent pdentryCurr) currentPart HparentIsPDT HcurrIsPDT HbeqParentCurr).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        specialize(Hdisjoint parentBlock12 HblockPMapped). congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSceBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceBlockP. rewrite HbeqSceBlockP in *. rewrite HlookupSce1s0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        HstartChild HendChild HPflagChild).
      destruct Hcons0 as [blockParent [startParent [endParent (HblockPMapped & HstartP & HendP & Hstarts & Hends)]]].
      exists blockParent. exists startParent. unfold bentryStartAddr in *. unfold bentryEndAddr. simpl.
      destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlocks1P.
      + rewrite <-DTL.beqAddrTrue in HbeqBlocks1P. subst blockParent. unfold bentryEndAddr in *.
        rewrite HlookupBlock1 in *. exists block2End. rewrite HnewB. simpl. subst endParent.
        assert(block2End >= endChild) by lia. auto.
      + exists endParent. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
    (* END blockInChildHasAtLeastEquivalentBlockInParent *)
  }

  assert(HparentListEq: forall parentsList part,
    (exists pdentry, lookup part (memory s) beqAddr = Some (PDT pdentry))
    -> isParentsList newS parentsList part
    -> isParentsList s parentsList part).
  {
    intros parentsList part HpartIsPDT. apply isParentsListEqBERev with bentry1; auto.
    unfold consistency1 in *; intuition.
  }

  split.
  { (* BEGIN partitionTreeIsTree newS *)
    assert(Hcons0: partitionTreeIsTree s) by (unfold consistency1 in *; intuition).
    intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
    rewrite HgetPartsEq in *. unfold pdentryParent in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr child) eqn:HbeqBlockChild; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent). apply Hcons0.
    revert HparentsList. apply HparentListEq.
    assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild).
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqChildRoot). subst pdparent.
    destruct HparentIsPart. assumption.
    (* END partitionTreeIsTree *)
  }

  split.
  { (* BEGIN kernelEntriesAreValid newS *)
    assert(Hcons0: kernelEntriesAreValid s) by (unfold consistency1 in *; intuition).
    intros kernel idx HkernIsKS Hidx. assert(HkernIsKSs: isKS kernel s).
    {
      unfold isKS in *. simpl in *.
      destruct (beqAddr block1InCurrPartAddr kernel) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1. rewrite HnewB in *.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    specialize(Hcons0 kernel idx HkernIsKSs Hidx). unfold isBE. simpl.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (kernel + idx))) eqn:HbeqBlockIdx; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END kernelEntriesAreValid *)
  }

  split.
  { (* BEGIN nextKernelIsValid newS *)
    assert(Hcons0: nextKernelIsValid s) by (unfold consistency1 in *; intuition). intros kernel HkernIsKS.
    assert(HkernIsKSs: isKS kernel s).
    {
      unfold isKS in *. simpl in *.
      destruct (beqAddr block1InCurrPartAddr kernel) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlock1. rewrite HnewB in *.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    specialize(Hcons0 kernel HkernIsKSs). destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]).
    split; trivial. exists nextAddr. split.
    - intro Hp. specialize(HlookupNext Hp). simpl.
      destruct (beqAddr block1InCurrPartAddr {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqBlockNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite <-HbeqBlockNext in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - destruct Hnext as [HnextIsKS | HnextIsNull]; try(right; assumption). left. unfold isKS in *. simpl.
      destruct (beqAddr block1InCurrPartAddr nextAddr) eqn:HbeqBlockNext.
      + rewrite <-DTL.beqAddrTrue in HbeqBlockNext. subst nextAddr. rewrite HlookupBlock1 in *. rewrite HnewB. auto.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END nextKernelIsValid *)
  }

  split.
  { (* BEGIN noDupListOfKerns newS *)
    assert(Hcons0: noDupListOfKerns s) by (unfold consistency1 in *; intuition).
    intros partition kernList HlistOfKerns.
    apply HkernListEq in HlistOfKerns. specialize(Hcons0 partition kernList HlistOfKerns). assumption.
    (* END noDupListOfKerns *)
  }

  split.
  { (* BEGIN MPUsizeIsBelowMax newS *)
    assert(Hcons0: MPUsizeIsBelowMax s) by (unfold consistency1 in *; intuition). intros partition MPUlist HMPU.
    unfold pdentryMPU in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition MPUlist HMPU). assumption.
    (* END MPUsizeIsBelowMax *)
  }

  split.
  { (* BEGIN originIsParentBlocksStart newS *)
    assert(Hcons0: originIsParentBlocksStart s) by (unfold consistency1 in *; intuition).
    intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
    rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. unfold scentryOrigin in *. simpl in Horigin.
    destruct (beqAddr block1InCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
    simpl in HlookupPart.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin).
    destruct Hcons0 as (HoriginIsStartParent & HlebOriginStart). split.
    - intro HbeqPartRoot. specialize(HoriginIsStartParent HbeqPartRoot).
      destruct HoriginIsStartParent as [blockParent (HblockPMapped & HstartP & Hincl)]. exists blockParent.
      split; trivial.
      unfold bentryStartAddr in *. simpl in *. destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlockP.
      + rewrite <-DTL.beqAddrTrue in HbeqBlockP. subst blockParent. rewrite HnewB. simpl. rewrite HlookupBlock1 in *.
        destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. exfalso. unfold getMappedBlocks in *.
          apply InFilterPresentInList in HblockMapped. apply InFilterPresentInList in HblockPMapped.
          unfold isPDT in *. assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
          assert(HpartIsPDT: isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial).
          assert(HparentIsPDT: isPDT (parent pdentry) s).
          {
            unfold isPDT. unfold getKSEntries in *.
            destruct (lookup (parent pdentry) (memory s) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
          specialize(HparentOfPart partition pdentry HlookupPart). destruct HparentOfPart as (_ & _ & HbeqParentPart).
          specialize(Hdisjoint (parent pdentry) partition HparentIsPDT HpartIsPDT HbeqParentPart).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint block1InCurrPartAddr HblockPMapped). congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial.
        intros addr HaddrInBlock. specialize(Hincl addr HaddrInBlock). rewrite app_nil_r in *.
        apply getAllPaddrBlockInclRev in Hincl. destruct Hincl as (HlebStartAddr & HltAddrEnd & _).
        apply getAllPaddrBlockIncl; lia.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial.
        intros addr HaddrInBlock. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
        * rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in HaddrInBlock. simpl in *.
          rewrite app_nil_r in *. assert(partition = currentPart).
          {
            destruct (beqAddr partition currentPart) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
            rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMapped.
            apply InFilterPresentInList in Hblock1Mapped.
            assert(HcurrIsPDT: isPDT currentPart s) by (unfold isPDT; rewrite HlookupCurr; trivial).
            assert(HpartIsPDT: isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial).
            assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
            specialize(Hdisjoint partition currentPart HpartIsPDT HcurrIsPDT HbeqParts).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint block1InCurrPartAddr HblockMapped). congruence.
          }
          subst partition. rewrite HlookupCurr in HlookupPart. injection HlookupPart as HpdentriesEq. subst pdentry.
          specialize(HparentBlock HbeqPartRoot). destruct HparentBlock as [parentBlock12 [startP [endP
            (HblockPMappeds0 & HstartPBis & HendP & HlebStarts & HgebEnds)]]].
          assert(Hwell: wellFormedBlock s) by (unfold consistency1 in *; intuition).
          assert(HstartBlock1: bentryStartAddr block1InCurrPartAddr (startAddr (blockrange bentry1)) s).
          {
            unfold bentryStartAddr. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block1InCurrPartAddr) eqn:HbeqSceBlock.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSceBlock. rewrite HbeqSceBlock in *. exfalso; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
            HPflag1 HstartBlock1 HendBlock1). destruct Hwell as (HwellBlock1 & _).
          assert(HstartInParent: In (startAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s0)).
          {
            assert(HstartInParent: In (startAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s)).
            { apply Hincl. rewrite HlookupBlock1. rewrite app_nil_r. apply getAllPaddrBlockIncl; lia. }
            simpl in *. rewrite Hs in HstartInParent. simpl in *.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSceBlockP;
              try(simpl in *; exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          assert(HstartInParentBis: In (startAddr (blockrange bentry1)) (getAllPaddrAux [parentBlock12] s0)).
          {
            unfold bentryEndAddr in *. simpl.
            assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HPflagP: bentryPFlag parentBlock12 true s0).
            {
              unfold bentryPFlag. apply mappedBlockIsBE in HblockPMappeds0.
              destruct HblockPMappeds0 as [bentry (Hlookup & Hpres)]. rewrite Hlookup. auto.
            }
            specialize(Hwell parentBlock12 startP endP HPflagP HstartPBis HendP). destruct Hwell as (Hwell & _).
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). subst startP. subst endP. rewrite app_nil_r.
            apply getAllPaddrBlockIncl; lia.
          }
          assert(blockParent = parentBlock12).
          {
            destruct (beqAddr blockParent parentBlock12) eqn:HbeqParent; try(rewrite DTL.beqAddrTrue; assumption).
            exfalso.
            assert(HnoDupPaddr: noDupMappedPaddrList s0) by (unfold consistency in *; unfold consistency2 in *;
              intuition).
            rewrite <-beqAddrFalse in *. specialize(HparentIsPartCurr HbeqPartRoot).
            destruct HparentIsPartCurr as (HlookupParent & _). assert(HparentIsPDT: isPDT (parent pdentryCurr) s0).
            { destruct HlookupParent as [parentEntry Hlookup]. unfold isPDT. rewrite Hlookup. trivial. }
            rewrite HgetMappedBEqs0 in HblockPMapped; trivial.
            pose proof (DisjointPaddrInPart (parent pdentryCurr) blockParent parentBlock12
              (startAddr (blockrange bentry1)) s0 HnoDupPaddr HparentIsPDT HblockPMapped HblockPMappeds0 HbeqParent
              HstartInParent) as Hres. congruence.
          }
          subst blockParent. unfold bentryEndAddr in *. rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSceBlockP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSceBlockP. rewrite HbeqSceBlockP in *. rewrite HlookupSce1s0 in *. simpl.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). subst startP. subst endP. apply getAllPaddrBlockInclRev in HaddrInBlock.
          rewrite app_nil_r. destruct HaddrInBlock as (HlebStartAddr & HltAddrEnd & _).
          apply getAllPaddrBlockIncl; lia.
        * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hincl addr HaddrInBlock). assumption.
    - intros startaddr Hstart. assert(Hstarts: bentryStartAddr block startaddr s).
      {
        unfold bentryStartAddr in *. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
        + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlock1. rewrite HnewB in *. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      apply HlebOriginStart; assumption.
    (* END originIsParentBlocksStart *)
  }

  split.
  { (* BEGIN nextImpliesBlockWasCut newS *)
    assert(Hcons0: nextImpliesBlockWasCut s) by (unfold consistency1 in *; intuition).
    intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock Hsce
      HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. simpl in HlookupPart.
    destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    unfold scentryNext in *.
    simpl in Hnext. destruct (beqAddr block1InCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    unfold bentryEndAddr in *. simpl in HendBlock. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in *. simpl in HendBlock. subst endaddr.
      assert(partition = currentPart).
      {
        destruct (beqAddr partition currentPart) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
        rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMapped.
        apply InFilterPresentInList in Hblock1Mapped.
        assert(HcurrIsPDT: isPDT currentPart s) by (unfold isPDT; rewrite HlookupCurr; trivial).
        assert(HpartIsPDT: isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial).
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
        specialize(Hdisjoint partition currentPart HpartIsPDT HcurrIsPDT HbeqParts).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        specialize(Hdisjoint block1InCurrPartAddr HblockMapped). congruence.
      }
      subst partition. rewrite HlookupCurr in HlookupPart. injection HlookupPart as HpdentriesEq. subst pdentry.
      subst scentryaddr. rewrite HlookupSce1 in *. simpl in Hnext. subst scnext.
      assert(HsceTriv2: CPaddr (block2InCurrPartAddr + scoffset) = CPaddr (block2InCurrPartAddr + scoffset))
        by reflexivity.
      assert(Hsce2s: scentryNext (CPaddr (block2InCurrPartAddr + scoffset)) block2Next s).
      {
        unfold scentryNext. rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (CPaddr (block2InCurrPartAddr + scoffset)))
          eqn:HbeqSces.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSces. exfalso.
          assert(HbeqSce1Null: CPaddr (block1InCurrPartAddr + scoffset) <> nullAddr).
          {
            intro Hcontra. rewrite Hcontra in *. assert(isPADDR nullAddr s) by (unfold consistency1 in *; intuition).
            unfold isPADDR in *. rewrite HlookupSce1 in *. congruence.
          }
          apply CPaddrAddEq in HbeqSces; trivial. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 currentPart pdentryCurr block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + scoffset))
        block2Next block2End HpartIsPart HlookupCurr Hblock2Mapped HendBlock2 HsceTriv2 HbeqNextNull Hsce2s
        HbeqPartRoot).
      specialize(HparentBlock HbeqPartRoot). destruct HparentBlock as [parentBlock12 [startP [endP (HblockPMapped &
        HstartP & HendP & HlebStarts & HgebEnds)]]].
      destruct Hcons0 as [blockParent [endParent (HblockPBisMapped & HendPBis & HltEnds & Hincl)]].
      assert(Hwell: wellFormedBlock s) by (unfold consistency1 in *; intuition).
      specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)) HPflag1
        HstartBlock1s HendBlock1). destruct Hwell as (HwellBlock1 & _).
      assert(HendInParent: In (endAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s0)).
      {
        assert(HendInParent: In (endAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s)).
        {
          apply Hincl. simpl. unfold bentryStartAddr in *.
          destruct (lookup block2InCurrPartAddr (memory s) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HendBlock2. rewrite <-HstartBlock2.
          apply getAllPaddrBlockIncl; lia.
        }
        simpl in *. rewrite Hs in HendInParent. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSceBlockP;
          try(simpl in *; exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HendInParentBis: In (endAddr (blockrange bentry1)) (getAllPaddrAux [parentBlock12] s0)).
      {
        unfold bentryStartAddr in *. simpl.
        assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HPflagP: bentryPFlag parentBlock12 true s0).
        {
          unfold bentryPFlag. apply mappedBlockIsBE in HblockPMapped.
          destruct HblockPMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup. auto.
        }
        specialize(Hwell parentBlock12 startP endP HPflagP HstartP HendP). destruct Hwell as (Hwell & _).
        destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence). subst startP. subst endP. rewrite app_nil_r.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(blockParent = parentBlock12).
      {
        destruct (beqAddr blockParent parentBlock12) eqn:HbeqParent; try(rewrite DTL.beqAddrTrue; assumption).
        exfalso. assert(HnoDupPaddr: noDupMappedPaddrList s0)
          by (unfold consistency in *; unfold consistency2 in *; intuition).
        rewrite <-beqAddrFalse in *. specialize(HparentIsPartCurr HbeqPartRoot).
        destruct HparentIsPartCurr as (HlookupParent & _). assert(HparentIsPDT: isPDT (parent pdentryCurr) s0).
        { destruct HlookupParent as [parentEntry Hlookup]. unfold isPDT. rewrite Hlookup. trivial. }
        rewrite HgetMappedBEqs0 in HblockPBisMapped; trivial.
        pose proof (DisjointPaddrInPart (parent pdentryCurr) blockParent parentBlock12 (endAddr (blockrange bentry1))
          s0 HnoDupPaddr HparentIsPDT HblockPBisMapped HblockPMapped HbeqParent HendInParent) as Hres. congruence.
      }
      subst blockParent. exists parentBlock12. exists endParent. split; trivial. simpl. rewrite beqAddrTrue.
      rewrite HnewB. destruct (beqAddr block1InCurrPartAddr parentBlock12) eqn:HbeqBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockP. subst parentBlock12. specialize(HparentIsPartCurr HbeqPartRoot).
        destruct HparentIsPartCurr as ([parentEntry HlookupBlockP] & _). exfalso. unfold getMappedBlocks in *.
        apply InFilterPresentInList in Hblock1Mapped. assert(HparentIsPDT: isPDT (parent pdentryCurr) s).
        {
          unfold isPDT. rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (parent pdentryCurr)) eqn:HbeqSceParent.
          { rewrite <-DTL.beqAddrTrue in HbeqSceParent. rewrite HbeqSceParent in *. exfalso; congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite HlookupBlockP; trivial.
        }
        assert(HcurrIsPDT: isPDT currentPart s) by (unfold isPDT; rewrite HlookupCurr; trivial).
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
        specialize(Hdisjoint (parent pdentryCurr) currentPart HparentIsPDT HcurrIsPDT HbeqParentCurr).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        apply InFilterPresentInList in HblockPBisMapped. specialize(Hdisjoint block1InCurrPartAddr HblockPBisMapped).
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. simpl. split; trivial.
      assert(endP = endParent).
      {
        unfold bentryEndAddr in *. rewrite Hs in HendPBis. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) parentBlock12) eqn:HbeqSceBlockP;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        destruct (lookup parentBlock12 (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst endParent. assumption.
      }
      subst endP. split; trivial. intros addr HaddrInNewBlock. rewrite app_nil_r in HaddrInNewBlock. rewrite Hs.
      unfold bentryEndAddr in *. unfold bentryStartAddr in *. rewrite Hs in HendPBis. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSceBlockP;
        try(simpl; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
      rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendP. apply getAllPaddrBlockInclRev in HaddrInNewBlock.
      destruct HaddrInNewBlock as (HlebStartAddr & HltAddrEnd & _). apply getAllPaddrBlockIncl; lia.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
        HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockPMapped & HendP & HltEnds & Hincl)]]. exists blockParent.
      simpl. rewrite beqAddrFalse in HbeqBlocks. rewrite HbeqBlocks.
      destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlockP.
      + rewrite <-DTL.beqAddrTrue in HbeqBlockP. subst blockParent. rewrite HnewB. simpl. exists block2End.
        split; trivial. split; trivial. unfold bentryEndAddr in *. rewrite HlookupBlock1 in *. subst endParent.
        split; try(lia). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        intros addr HaddrInBlock. specialize(Hincl addr HaddrInBlock). simpl in *. rewrite HlookupBlock1 in *.
        rewrite app_nil_r in *. apply getAllPaddrBlockInclRev in Hincl.
        destruct Hincl as (HlebStartAddr & HltAddrEnd & _). apply getAllPaddrBlockIncl; lia.
      + exists endParent. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        split; trivial. split; trivial. split; trivial. intros addr HaddrInBlock.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. apply Hincl; assumption.
    (* END nextImpliesBlockWasCut *)
  }

  assert(~isKS (startAddr (blockrange bentry1)) s).
  {
    intro Hcontra. specialize(HkernNotAcc block1InCurrPartAddr (startAddr (blockrange bentry1)) HstartBlock1s HPflag1
      Hcontra).
    unfold bentryAFlag in *. rewrite HlookupBlock1 in *. congruence.
  }

  assert(~isPDT (startAddr (blockrange bentry1)) s).
  {
    assert(HaccessNoPD: AccessibleNoPDFlag s) by (unfold consistency1 in *; intuition).
    assert(Hblock1IsBE: isBE block1InCurrPartAddr s) by (unfold isBE; rewrite HlookupBlock1; trivial).
    specialize(HaccessNoPD block1InCurrPartAddr sh1entryaddr1 Hblock1IsBE Hsh11 HAflag1).
    assert(Hres: notPDTIfNotPDflag s) by (unfold consistency1 in *; intuition).
    specialize(Hres block1InCurrPartAddr (startAddr (blockrange bentry1)) sh1entryaddr1). apply Hres; assumption.
  }

  assert(~isKS (endAddr (blockrange bentry1)) s).
  {
    intro Hcontra. specialize(HkernNotAcc block2InCurrPartAddr (endAddr (blockrange bentry1)) HstartBlock2 HPflag2
      Hcontra). unfold bentryAFlag in *. destruct (lookup block2InCurrPartAddr (memory s) beqAddr); try(congruence).
    destruct v; congruence.
  }

  assert(~isPDT (endAddr (blockrange bentry1)) s).
  {
    assert(HaccessNoPD: AccessibleNoPDFlag s) by (unfold consistency1 in *; intuition).
    assert(Hblock2IsBE: isBE block2InCurrPartAddr s).
    {
      unfold bentryPFlag in *. unfold isBE.
      destruct (lookup block2InCurrPartAddr (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
    }
    specialize(HaccessNoPD block2InCurrPartAddr sh1entryaddr2 Hblock2IsBE Hsh12 HAflag2).
    assert(Hres: notPDTIfNotPDflag s) by (unfold consistency1 in *; intuition).
    specialize(Hres block2InCurrPartAddr (endAddr (blockrange bentry1)) sh1entryaddr2). apply Hres; assumption.
  }

  split.
  { (* BEGIN blocksAddressesTypes newS *)
    assert(Hcons0: blocksAddressesTypes s) by (unfold consistency1 in *; intuition).
    intros block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock. unfold sh1entryPDchild in *.
    simpl in HPDchildBlock. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in HstartBlock.
    simpl in HendBlock. simpl in HPflagBlock. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in *. simpl in HstartBlock.
      simpl in HendBlock. simpl in HPflagBlock.
      specialize(Hcons0 block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
        HstartBlock1s HendBlock1 HPflag1 HPDchildBlock).
      destruct Hcons0 as [(HKS & _) | [(HPDT & _) | Hnone1]]; try(exfalso; congruence). unfold sh1entryAddr in *.
      assert(sh1entryaddr2 = CPaddr (block2InCurrPartAddr+sh1offset)).
      {
        destruct (lookup block2InCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). assumption.
      }
      subst sh1entryaddr2. assert(Hcons0: blocksAddressesTypes s) by (unfold consistency1 in *; intuition).
      specialize(Hcons0 block2InCurrPartAddr (endAddr (blockrange bentry1)) block2End HstartBlock2 HendBlock2 HPflag2
        HPDchild2). subst startaddr. subst endaddr. right. right.
      destruct Hcons0 as [(HKS & _) | [(HPDT & _) | Hnone2]]; try(exfalso; congruence). intros addr HaddrInNewBlock.
      assert(HpropsOr: In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)))
        \/ In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)).
      {
        apply getAllPaddrBlockInclRev in HaddrInNewBlock.
        destruct HaddrInNewBlock as (HlebStartAddr & HltAddrEnd & _).
        destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
        - apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. left. apply getAllPaddrBlockIncl; lia.
        - apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. right. apply getAllPaddrBlockIncl; lia.
      }
      destruct HpropsOr as [HaddrInBlock1 | HaddrInBlock2].
      + specialize(Hnone1 addr HaddrInBlock1). simpl. destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlock1Addr. subst addr. exfalso; congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      + specialize(Hnone2 addr HaddrInBlock2). simpl. destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlock1Addr. subst addr. exfalso; congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock).
      destruct Hcons0 as [(HKS & Hnone) | [(HPDT & Hnone) | Hnone]].
      + left. split.
        * unfold isKS in *. simpl. destruct (beqAddr block1InCurrPartAddr startaddr) eqn:HbeqBlock1Start.
          --- rewrite <-DTL.beqAddrTrue in HbeqBlock1Start. subst startaddr. rewrite HlookupBlock1 in *.
              rewrite HnewB. auto.
          --- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        * intros addr HaddrInRange. specialize(Hnone addr HaddrInRange).
          destruct Hnone as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
          --- left. unfold isBE in *. simpl. destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr; trivial.
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          --- right. left. unfold isSHE in *. simpl. destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr.
              { rewrite <-DTL.beqAddrTrue in HbeqBlock1Addr. subst addr. rewrite HlookupBlock1 in *. congruence. }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          --- right. right. left. unfold isSCE in *. simpl.
              destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr.
              { rewrite <-DTL.beqAddrTrue in HbeqBlock1Addr. subst addr. rewrite HlookupBlock1 in *. congruence. }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          --- right. right. right. left. unfold isPADDR in *. simpl.
              destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr.
              { rewrite <-DTL.beqAddrTrue in HbeqBlock1Addr. subst addr. rewrite HlookupBlock1 in *. congruence. }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          --- right. right. right. right. simpl. destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr.
              { rewrite <-DTL.beqAddrTrue in HbeqBlock1Addr. subst addr. rewrite HlookupBlock1 in *. congruence. }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      + right. left. split.
        * unfold isPDT in *. simpl. destruct (beqAddr block1InCurrPartAddr startaddr) eqn:HbeqBlock1Start.
          { rewrite <-DTL.beqAddrTrue in HbeqBlock1Start. subst startaddr. rewrite HlookupBlock1 in *. congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        * intros addr HaddrInRange. specialize(Hnone addr HaddrInRange). simpl.
          destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr.
          { rewrite <-DTL.beqAddrTrue in HbeqBlock1Addr. subst addr. rewrite HlookupBlock1 in *. congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      + right. right. intros addr HaddrInRange. specialize(Hnone addr HaddrInRange). simpl.
        destruct (beqAddr block1InCurrPartAddr addr) eqn:HbeqBlock1Addr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlock1Addr. subst addr. rewrite HlookupBlock1 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END blocksAddressesTypes *)
  }

  split.
  { (* BEGIN notPDTIfNotPDflag newS *)
    assert(Hcons0: notPDTIfNotPDflag s) by (unfold consistency1 in *; intuition).
    intros block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild. unfold sh1entryPDflag in *.
    unfold sh1entryPDchild in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(Hblock: bentryStartAddr block startaddr s /\ sh1entryAddr block sh1entryaddr s
      /\ bentryPFlag block true s).
    {
      unfold bentryStartAddr in *. unfold sh1entryAddr in *. unfold bentryPFlag in *. simpl in *.
      destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlock1. rewrite HnewB in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct Hblock as (HstartBlocks & Hsh1s & HPflags).
    specialize(Hcons0 block startaddr sh1entryaddr HstartBlocks Hsh1s HPflags HPDflag HPDchild). unfold isPDT in *.
    simpl. contradict Hcons0.
    destruct (beqAddr block1InCurrPartAddr startaddr) eqn:HbeqBlockStart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END notPDTIfNotPDflag *)
  }

  split.
  { (* BEGIN nextKernAddrIsInSameBlock newS *)
    assert(Hcons0: nextKernAddrIsInSameBlock s) by (unfold consistency1 in *; intuition).
    intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HnextInRange HkernIsKS.
    unfold sh1entryPDchild in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(HkernIsKSs: isKS kernel s).
    {
      unfold isKS in *. simpl in *. destruct (beqAddr block1InCurrPartAddr kernel) eqn:HbeqBlockKern.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlock1. rewrite HnewB in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in *. simpl in *. subst endaddr.
      subst startaddr. intro HnextInNewBlock.
      assert(HpropsOr:
        In (CPaddr (kernel + nextoffset)) (getAllPaddrBlock (startAddr (blockrange bentry1))
          (endAddr (blockrange bentry1)))
        \/ In (CPaddr (kernel + nextoffset)) (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)).
      {
        apply getAllPaddrBlockInclRev in HnextInNewBlock.
        destruct HnextInNewBlock as (HlebStartNext & HltNextEnd & _).
        destruct (Nat.ltb (CPaddr (kernel + nextoffset)) (endAddr (blockrange bentry1))) eqn:HltNextEnd1.
        - apply PeanoNat.Nat.ltb_lt in HltNextEnd1. left. apply getAllPaddrBlockIncl; lia.
        - apply PeanoNat.Nat.ltb_ge in HltNextEnd1. right. apply getAllPaddrBlockIncl; lia.
      }
      exfalso. destruct HpropsOr as [HaddrInBlock1 | HaddrInBlock2].
      - specialize(Hcons0 block1InCurrPartAddr kernel (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
          HstartBlock1s HendBlock1 HPflag1 HnextInRange HkernIsKSs HaddrInBlock1). subst kernel. congruence.
      - assert(sh1entryaddr2 = CPaddr (block2InCurrPartAddr+sh1offset)).
        {
          unfold sh1entryAddr in *.
          destruct (lookup block2InCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). assumption.
        }
        subst sh1entryaddr2. specialize(Hcons0 block2InCurrPartAddr kernel (endAddr (blockrange bentry1)) block2End
          HstartBlock2 HendBlock2 HPflag2 HPDchild2 HkernIsKSs HaddrInBlock2). subst kernel. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HnextInRange HkernIsKSs).
    assumption.
    (* END nextKernAddrIsInSameBlock *)
  }

  split.
  { (* BEGIN blockBelongsToAPart newS *)
    assert(Hcons0: blockBelongsToAPart s) by (unfold consistency1 in *; intuition). intros block HPflagBlock.
    assert(HPflagBlocks: bentryPFlag block true s).
    {
      unfold bentryPFlag in *. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlock1. rewrite HnewB in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 block HPflagBlocks). rewrite HgetPartsEq. destruct Hcons0 as [part Hcons0]. exists part.
    rewrite HgetMappedBEq. assumption.
    (* END blockBelongsToAPart *)
  }

  split.
  { (* BEGIN PDflagMeansNoChild newS *)
    assert(Hcons0: PDflagMeansNoChild s) by (unfold consistency1 in *; intuition).
    intros block HblockIsBE HPDflagBlock. assert(HblockIsBEs: isBE block s).
    {
      unfold isBE in *. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlock1. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    unfold sh1entryPDflag in *. unfold sh1entryPDchild. simpl in *.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1; try(congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 block HblockIsBEs HPDflagBlock). assumption.
    (* END PDflagMeansNoChild *)
  }

  split.
  { (* BEGIN nbPrepareIsNbKern newS *)
    assert(Hcons0: nbPrepareIsNbKern s) by (unfold consistency1 in *; intuition).
    intros partition pdentry HlookupPart.
    simpl in *. destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentry HlookupPart). unfold newS.
    rewrite completeListOfKernelsEqBE with (bentry := bentry1); trivial. rewrite HnewB. auto.
   (* END nbPrepareIsNbKern *)
  }

  split.
  { (* BEGIN pdchildIsPDT newS *)
    assert(Hcons0: pdchildIsPDT s) by (unfold consistency1 in *; intuition).
    intros part block sh1entryaddr idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
    rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. assert(isPDT part s).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    assert(Hsh1s: sh1entryAddr block sh1entryaddr s).
    {
      unfold sh1entryAddr in *. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlock1. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    unfold sh1entryPDchild in *. simpl in *.
    destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 part block sh1entryaddr idchild HpartBisIsPart HblockMapped Hsh1s HPDchild HbeqIdChildNull).
    rewrite HgetChildrenEq in *; assumption.
    (* END pdchildIsPDT *)
  }

  split.
  { (* BEGIN childBlockNullIfChildNull newS *)
    assert(Hcons0: childBlockNullIfChildNull s) by (unfold consistency1 in *; intuition).
    intros part block sh1entryaddr HpartBisIsPart HblockMapped Hsh1 HPDchild.
    rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. assert(isPDT part s).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    assert(Hsh1s: sh1entryAddr block sh1entryaddr s).
    {
      unfold sh1entryAddr in *. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlock1. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    unfold sh1entryPDchild in *. unfold sh1entryInChildLocation. simpl in *.
    destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 part block sh1entryaddr HpartBisIsPart HblockMapped Hsh1s HPDchild).
    unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence).
    destruct v; try(congruence). destruct Hcons0. split; trivial. intro. exfalso; congruence.
    (* END pdchildIsPDT *)
  }

  (* BEGIN accessibleBlocksArePresent newS *)
  assert(Hcons0: accessibleBlocksArePresent s) by (unfold consistency1 in *; intuition).
  intros block HAflag. unfold bentryAFlag in *. unfold bentryPFlag in *. simpl in *.
  destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
  - rewrite HnewB. rewrite HlookupBlock1 in *. auto.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    apply Hcons0; assumption.
  (* END childLocHasSameStart *)
}
intro. eapply bindRev.
{ (** Internal.freeSlot **)
  eapply weaken. apply freeSlot. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s1 [s0 [scentry1 [sh1entryaddr1 [sh1entryaddr2 [bentry1 [pdentryCurr (Hs & HnewB & Hs1 &
    Hblock1 & Hblock2 & HltEnds & HlebMinSize2 & HbeqBlocks & HcurrEqss1 & HgetPartsEq & HgetChildrenEqss1 &
    HgetMappedBEqss1 & HlookupCurrs1 & HlookupBlock1s1 & Hconsists & Hconsists1 & HnoDups1 & Haccesss1 & Hshareds1 &
    HchildBlockProps & HnoChilds1 & HkernNotAccs1 & HlocPropss1 & HsameStarts1 & HVSs1 & HPIs1 & HKDIs1 & Hcurrs1
    & Hsh11s1 & Hsh12s1
    & HPDchild2s1 & HAflag1s1 & HAflag2s1 & HPflag1s1 & HPflag2s1 & Hstart2s1 & HPDchild1s1 & Hblock2Mappes1 &
    Hblock1Mappeds1 & Hprops)]]]]]]]. unfold isPDT. unfold isBE. unfold bentryPFlag. rewrite HgetMappedBEqss1.
  rewrite Hs. simpl. destruct (beqAddr block1InCurrPartAddr currentPart) eqn:HbeqBlock1Curr.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlock1Curr. rewrite HbeqBlock1Curr in *. unfold sh1entryAddr in *.
    rewrite HlookupCurrs1 in *. exfalso; congruence.
  }
  rewrite beqAddrFalse in *. rewrite HbeqBlocks. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite <-Hs. rewrite HlookupCurrs1.
  assert(Hblock2IsBEs1: isBE block2InCurrPartAddr s1).
  {
    unfold isBE. unfold sh1entryAddr in *.
    destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
    trivial.
  }
  intuition.
  - unfold cons1Free. unfold consistency1 in *. intuition.
  - assert(HaccNoPDs1: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
    specialize(HaccNoPDs1 block2InCurrPartAddr sh1entryaddr2 Hblock2IsBEs1 Hsh12s1 HAflag2s1).
    unfold sh1entryAddr in *. destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst sh1entryaddr2. unfold sh1entryPDflag in *. rewrite Hs. simpl.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqBlock1Sh12.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlock1Sh12. rewrite <-HbeqBlock1Sh12 in *.
      destruct (lookup block1InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
intro. eapply bindRev.
{ (** Internal.writeAccessibleToAncestorsIfNotCutRec **)
  eapply weaken. apply writeAccessibleToAncestorsIfNotCutRecNoBounds. intros s Hprops. simpl.
  destruct Hprops as [s2 [s3 [s4 [s5 [s6 [s7 [s8 [pdentry [pdentry1 [pdentry2 [pdentry3 [realMPU [emptyBentry
    [freeBentry [currFirstFreeSlot [blockToFreeIdx (Hs & Hs8 & Hs7 & Hs6 & Hs5 & Hs4 & Hs3 & Hcons1s & Hstructs8 &
    Hstructs7 & HlookupCurrs7 & HlookupBlock2s6
    & HfirstFrees6 & Hbindex2s3 & HlookupCurrs2 & Hblock2IsBEs2 & HMPUs2 & Hconsists2 & HgetPartsEqss2 &
    HgetChildrenEqss2 & HgetMappedBNotCurrEqss2 & HgetMappedBCurrEqss2 & HnewB2 & Hpdentry1 & Hpdentry2 & Hpdentry3 &
    HlebNbFreeMax & HnewB3 & [s1 [s0 [scentry1 [sh1entryaddr1 [sh1entryaddr2 [bentry1 [pdentryCurr (Hs2 & HnewB & Hs1
    & Hblock1 & Hblock2 & HltEnds & HlebMinSize2 & HbeqBlocks12 & HcurrEqs2s1 & HgetPartsEqs2s1 & HgetChildrenEqs2s1 &
    HgetMappedBEqs2s1 & HlookupCurrs1 & HlookupBlock1s1 & _ & Hconsists1 & HnoDupMappedPs1 & Haccesss1 & Hshareds1 &
    HchildBlockPropss1 & HnoChilds1 & HkernNotAccs1 & HlocPropss1 & HsameStarts1 & HVSs1 & HPIs1 & HKDIs1 & Hcurr &
    Hsh11s1 & Hsh12s1 & HPDchild2s1 & HAflag1s1 & HAflag2s1 & HPflag2s1 & HPflag1s1 & Hstart2s1 & HPDchild1s1 &
    Hblock2Mappeds1 & Hblock1Mappeds1 & Hconsists0 & HVSs0 & HPIs0 & HKDIs0 & HcurrEqs1s0 & HgetPartsEqs1s0 &
    HgetChildrenEqs1s0 & HgetMappedBEqs1s0 & HlookupSce1s0 & Hsh11s0 & Hsh12s0 & HPDchild2s0 & HAflag1s0 & HAflag2s0 &
    HPflag2s0 & HPflag1s0 & HPDchild1s0 & Hblock2Mappeds0 & Hblock1Mappeds0 & Hnext1s0 & Hnext2s0 & Hstart2s0 &
    HlookupCurrs0 & Hend2s0 & HparentCurr)]]]]]]] & HgetPartsEqs3s2 & HPDTIfPDFlags3 & HmultIsPDTs3 & HgetMappedBEqss4
    & HgetKSEqss2 & HparentsListEqs2s)]]]]]]]]]]]]]]]].
  assert(HcurrIsPDTs1: isPDT currentPart s1) by (unfold isPDT; rewrite HlookupCurrs1; trivial).
  assert(HcurrIsPDTs2: isPDT currentPart s2) by (unfold isPDT; rewrite HlookupCurrs2; trivial).
  assert(HlookupCurrs4: lookup currentPart (memory s4) beqAddr = Some (PDT pdentry1)).
  {
    rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr currentPart) eqn:HbeqBlock2Curr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlock2Curr. rewrite HbeqBlock2Curr in *. unfold isBE in *.
      rewrite HlookupCurrs2 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    rewrite beqAddrTrue. reflexivity.
  }
  assert(HgetKSEntriesEqs3s2: forall part, getKSEntries part s3 = getKSEntries part s2).
  {
    intro part. rewrite Hs3. apply getKSEntriesEqPDT with pdentry; trivial.
    - unfold cons1Free in *. intuition.
    - rewrite Hpdentry1. reflexivity.
  }
  assert(HlookupCurrs8: lookup currentPart (memory s8) beqAddr = Some (PDT pdentry2)).
  {
    rewrite Hs8. simpl. rewrite beqAddrTrue. reflexivity.
  }
  assert(HlookupCurrs6: lookup currentPart (memory s6) beqAddr = Some (PDT pdentry1)).
  {
    rewrite Hs7 in HlookupCurrs7. simpl in *.
    destruct (beqAddr block2InCurrPartAddr currentPart) eqn:HbeqBlock2Curr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HlookupBlock2s5: lookup block2InCurrPartAddr (memory s5) beqAddr = Some (BE emptyBentry)).
  {
    rewrite Hs6 in HlookupBlock2s6. simpl in *.
    destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HgetMappedPEqss4: forall part, isPDT part s -> getMappedPaddr part s = getMappedPaddr part s4).
  {
    destruct HnewB2 as [l0 [l1 HnewB2]]. destruct HnewB3 as [l2 [l3 HnewB3]].
    intros part HpartIsPDTs. assert(Heqs8: getMappedPaddr part s = getMappedPaddr part s8).
    {
      rewrite Hs. apply getMappedPaddrEqPDT with pdentry2; trivial. rewrite Hpdentry3. reflexivity.
    }
    assert(Heqs7: getMappedPaddr part s = getMappedPaddr part s7).
    {
      rewrite Heqs8. rewrite Hs8. apply getMappedPaddrEqPDT with pdentry1; trivial. rewrite Hpdentry2. reflexivity.
    }
    assert(HpartIsPDTs6: isPDT part s6).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDTs. rewrite Hs8 in HpartIsPDTs. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs6. trivial.
      - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HpartIsPDTs. simpl in *.
        destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs5: isPDT part s5).
    {
      unfold isPDT in *. rewrite Hs6 in HpartIsPDTs6. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) part) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(Heqs6: getMappedPaddr part s = getMappedPaddr part s6).
    {
      rewrite Heqs7. rewrite Hs7. apply getMappedPaddrEqBEPresentFalseNoChange with emptyBentry; trivial.
      - rewrite HnewB3. reflexivity.
      - rewrite HnewB2. reflexivity.
    }
    assert(Heqs5: getMappedPaddr part s = getMappedPaddr part s5).
    {
      rewrite Heqs6. rewrite Hs6. apply getMappedPaddrEqSCE; trivial.
      assert(Hwell: wellFormedShadowCutIfBlockEntry s2) by (unfold cons1Free in *; intuition).
      specialize(Hwell block2InCurrPartAddr Hblock2IsBEs2). destruct Hwell as [sce (HsceIsSCE & Hsce)]. subst sce.
      assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s2) by (unfold cons1Free in *; intuition).
      specialize(Hsh1IsSHE block2InCurrPartAddr Hblock2IsBEs2). unfold isSCE in *. rewrite Hs5. simpl.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) (CPaddr (block2InCurrPartAddr + scoffset)))
        eqn:HbeqSh1Sce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. unfold isSHE in *.
        destruct (lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s2) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      destruct (beqAddr block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqBlockSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *. unfold isBE in *.
        destruct (lookup block2InCurrPartAddr (memory s2) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr currentPart (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite <-HbeqCurrSce in *. rewrite HlookupCurrs2 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs4: isPDT part s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDTs. rewrite Hs8 in HpartIsPDTs. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs4. trivial.
      - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HpartIsPDTs. simpl in *.
        destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in HpartIsPDTs. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) part) eqn:HbeqSce2Part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs5 in HpartIsPDTs. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) part) eqn:HbeqSh12Part;
          try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    rewrite Heqs5. rewrite Hs5. apply getMappedPaddrEqSHE; trivial.
    assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s2) by (unfold cons1Free in *; intuition).
    specialize(Hsh1IsSHE block2InCurrPartAddr Hblock2IsBEs2). unfold isSHE in *. rewrite Hs4. simpl.
    destruct (beqAddr block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. unfold isBE in *.
      destruct (lookup block2InCurrPartAddr (memory s2) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr currentPart (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqCurrSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite <-HbeqCurrSh1 in *. rewrite HlookupCurrs2 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HgetMappedPNotCurrEqss1: forall part, isPDT part s -> currentPart <> part
    -> getMappedPaddr part s = getMappedPaddr part s1).
  {
    intros part HpartIsPDTs HbeqCurrPart. assert(Heqs3s2: getMappedPaddr part s3 = getMappedPaddr part s2).
    {
      rewrite Hs3. apply getMappedPaddrEqPDT with pdentry; trivial.
      - rewrite Hpdentry1. reflexivity.
      - unfold cons1Free in *. intuition.
    }
    rewrite HgetMappedPEqss4; trivial. assert(HpartIsPDTs4: isPDT part s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDTs. rewrite Hs8 in HpartIsPDTs. simpl in *.
      rewrite beqAddrFalse in *. rewrite HbeqCurrPart in *. rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HpartIsPDTs. simpl in *.
      destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HpartIsPDTs. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) part) eqn:HbeqSce2Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HpartIsPDTs. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) part) eqn:HbeqSh12Part;
        try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs2: isPDT part s2).
    {
      unfold isPDT in *. rewrite Hs4 in HpartIsPDTs4. simpl in *.
      destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HpartIsPDTs4. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrPart in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs1: isPDT part s1).
    {
      unfold isPDT in *. rewrite Hs2 in HpartIsPDTs2. simpl in *.
      destruct (beqAddr block1InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(Heqs3: getMappedPaddr part s3 = getMappedPaddr part s1).
    {
      rewrite Heqs3s2. rewrite Hs2. apply getMappedPaddrEqBENotInPart.
      + unfold isBE. unfold sh1entryAddr in *.
        destruct (lookup block1InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
        trivial.
      + unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock1Mappeds1.
        assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
        specialize(Hdisjoint currentPart part HcurrIsPDTs1 HpartIsPDTs1 HbeqCurrPart).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        apply Hdisjoint; assumption.
    }
    rewrite <-Heqs3. rewrite Hs4. apply getMappedPaddrEqBENotInPart.
    + unfold isBE. unfold bentryBlockIndex in *.
      destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; try(congruence).
      trivial.
    + rewrite <-HgetMappedBEqs2s1 in Hblock2Mappeds1. unfold getMappedBlocks in *.
      apply InFilterPresentInList in Hblock2Mappeds1.
      assert(Hdisjoint: DisjointKSEntries s2) by (unfold cons1Free in *; intuition).
      specialize(Hdisjoint currentPart part HcurrIsPDTs2 HpartIsPDTs2 HbeqCurrPart).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      rewrite HgetKSEntriesEqs3s2. apply Hdisjoint; assumption.
  }
  assert(HcurrIsPDTs: isPDT currentPart s).
  { unfold isPDT. rewrite Hs. simpl. rewrite beqAddrTrue. trivial. }
  assert(HlookupBlock1s2: lookup block1InCurrPartAddr (memory s2) beqAddr
    = Some(BE (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) (present bentry1) (accessible bentry1)
           (blockindex bentry1) (CBlock (startAddr (blockrange bentry1)) block2End)))).
  { rewrite Hs2. simpl. rewrite beqAddrTrue. reflexivity. }
  assert(HlookupBlock1s0: lookup block1InCurrPartAddr (memory s0) beqAddr = Some (BE bentry1)).
  {
    rewrite Hs1 in HlookupBlock1s1. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block1InCurrPartAddr) eqn:HbeqSceBlock1;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HlookupBlock1Eqss2: lookup block1InCurrPartAddr (memory s) beqAddr
    = lookup block1InCurrPartAddr (memory s2) beqAddr).
  {
    rewrite Hs. rewrite Hs8. simpl. destruct (beqAddr currentPart block1InCurrPartAddr) eqn:HbeqCurrBlock1.
    { rewrite <-DTL.beqAddrTrue in HbeqCurrBlock1. rewrite HbeqCurrBlock1 in *. exfalso; congruence. }
    rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
    rewrite beqAddrSym in HbeqBlocks12. rewrite HbeqBlocks12. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
    destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block1InCurrPartAddr) eqn:HbeqSceBlock1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceBlock1. rewrite HbeqSceBlock1 in *. unfold scentryNext in *.
      rewrite HlookupBlock1s0 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
    destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) block1InCurrPartAddr) eqn:HbeqSh1Block1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Block1. unfold sh1entryAddr in *. exfalso.
      destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      subst sh1entryaddr2. rewrite HbeqSh1Block1 in *. unfold sh1entryPDchild in *. rewrite HlookupBlock1s1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlocks12. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqCurrBlock1. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(Hstart1s1: bentryStartAddr block1InCurrPartAddr (startAddr (blockrange bentry1)) s1).
  { unfold bentryStartAddr. rewrite HlookupBlock1s1. reflexivity. }
  assert(Hend1s1: bentryEndAddr block1InCurrPartAddr (endAddr (blockrange bentry1)) s1).
  { unfold bentryEndAddr. rewrite HlookupBlock1s1. reflexivity. }
  assert(HgetMappedPCurrEqss1: forall addr,
    (In addr (getMappedPaddr currentPart s) <-> In addr (getMappedPaddr currentPart s1))).
  {
    destruct HnewB as [l0 [l1 HnewB]]. destruct HnewB2 as [l2 [l3 HnewB2]]. destruct HnewB3 as [l4 [l5 HnewB3]].
    intro addr. unfold getMappedPaddr. split.
    - intro HaddrMappeds. assert(HgetMappedBEqss2: forall block,
        In block (getMappedBlocks currentPart s) -> In block (getMappedBlocks currentPart s2)).
      {
        intro block. specialize(HgetMappedBCurrEqss2 block). destruct HgetMappedBCurrEqss2 as (_ & Hres & _). trivial.
      }
      assert(HmappedIsPres: forall block, In block (getMappedBlocks currentPart s) -> bentryPFlag block true s).
      {
        intros block HblockMapped. apply mappedBlockIsBE in HblockMapped. unfold bentryPFlag.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup. auto.
      }
      clear HgetMappedBCurrEqss2. induction (getMappedBlocks currentPart s); simpl in *; try(exfalso; congruence).
      assert(HgetMappedBEqss2Rec: forall block, In block l -> In block (getMappedBlocks currentPart s2)).
      { intros block HblockMapped. apply HgetMappedBEqss2; auto. }
      assert(HmappedIsPresRec: forall block, In block l -> bentryPFlag block true s).
      { intros block HblockMapped. apply HmappedIsPres; auto. }
      destruct (lookup a2 (memory s) beqAddr) eqn:HlookupA; try(apply IHl; assumption).
      destruct v; try(apply IHl; assumption). apply in_app_or in HaddrMappeds.
      destruct HaddrMappeds as [HaddrInBlock | HaddrMappedsRec]; try(apply IHl; assumption).
      assert(Ha2: a2 = a2 \/ In a2 l) by (left; reflexivity). specialize(HgetMappedBEqss2 a2 Ha2).
      specialize(HmappedIsPres a2 Ha2). unfold bentryPFlag in *. rewrite HlookupA in *.
      rewrite HgetMappedBEqs2s1 in *. rewrite Hs in HlookupA. rewrite Hs8 in HlookupA. simpl in *.
      destruct (beqAddr currentPart a2) eqn:HbeqCurrA; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HlookupA. simpl in *.
      destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A.
      {
        injection HlookupA as HbentriesEq. subst b. rewrite HnewB3 in HmappedIsPres. simpl in *.
        rewrite HnewB2 in HmappedIsPres. simpl in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HlookupA. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) a2) eqn:HbeqSceA; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HlookupA. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) a2) eqn:HbeqSh1A; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HlookupA. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2A in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HlookupA. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrA in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupA. simpl in *. destruct (beqAddr block1InCurrPartAddr a2) eqn:HbeqBlock1A.
      + injection HlookupA as HbentriesEq. rewrite HnewB in HbentriesEq. subst b. simpl in *.
        assert(HpropsOr: In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)))
          \/ In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)).
        {
          apply getAllPaddrBlockInclRev in HaddrInBlock. destruct HaddrInBlock as (HlebStart1Addr & HltAddrEnd2 & _).
          destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
          - apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. left. apply getAllPaddrBlockIncl; lia.
          - apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. right. apply getAllPaddrBlockIncl; lia.
        }
        destruct HpropsOr as [HaddrInBlock1 | HaddrInBlock2].
        * apply blockIsMappedAddrInPaddrList with block1InCurrPartAddr; trivial. simpl. rewrite HlookupBlock1s1.
          rewrite app_nil_r. assumption.
        * apply blockIsMappedAddrInPaddrList with block2InCurrPartAddr; trivial. simpl. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite Hs1. rewrite Hs1 in Hstart2s1. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock2;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. subst block2End. rewrite Hstart2s1 in *. assumption.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        apply blockIsMappedAddrInPaddrList with a2; trivial. simpl. rewrite HlookupA. rewrite app_nil_r. assumption.
    - intro HaddrMappeds1. rewrite <-HgetMappedBEqs2s1 in HaddrMappeds1.
      assert(HgetMappedBEqss2: forall block, In block (getMappedBlocks currentPart s2) ->
        block2InCurrPartAddr = block \/ In block (getMappedBlocks currentPart s)).
      { intro block. specialize(HgetMappedBCurrEqss2 block). apply HgetMappedBCurrEqss2. }
      assert(In block1InCurrPartAddr (getMappedBlocks currentPart s)).
      {
        specialize(HgetMappedBCurrEqss2 block1InCurrPartAddr). destruct HgetMappedBCurrEqss2 as (Hres & _).
        rewrite HgetMappedBEqs2s1 in Hres. specialize(Hres Hblock1Mappeds1).
        destruct Hres as [Hcontra | Hres]; try(exfalso; congruence). assumption.
      }
      clear HgetMappedBCurrEqss2. induction (getMappedBlocks currentPart s2); simpl in *; try(exfalso; congruence).
      assert(forall block, In block l -> block2InCurrPartAddr = block \/ In block (getMappedBlocks currentPart s)).
      { intros block HblockMapped. apply HgetMappedBEqss2; auto. }
      destruct (lookup a2 (memory s1) beqAddr) eqn:HlookupA; try(apply IHl; assumption).
      destruct v; try(apply IHl; assumption). apply in_app_or in HaddrMappeds1.
      destruct HaddrMappeds1 as [HaddrInBlock | HaddrMappeds1Rec]; try(apply IHl; assumption).
      assert(Ha2: a2 = a2 \/ In a2 l) by (left; reflexivity). specialize(HgetMappedBEqss2 a2 Ha2).
      destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A.
      + rewrite <-DTL.beqAddrTrue in HbeqBlock2A. subst a2. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        rewrite HlookupA in *. rewrite Hs1 in HlookupA. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock2;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HlookupA in *. rewrite <-Hend2s0 in *.
        rewrite <-Hstart2s1 in *. apply blockIsMappedAddrInPaddrList with block1InCurrPartAddr; trivial. simpl.
        rewrite HlookupBlock1Eqss2. rewrite HlookupBlock1s2. rewrite HnewB. simpl. rewrite app_nil_r.
        apply getAllPaddrBlockInclRev in HaddrInBlock. destruct HaddrInBlock as (HlebEnd1Addr & HltAddrEnd2 & _).
        assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
        specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
          HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
        apply getAllPaddrBlockIncl; lia.
      + rewrite <-beqAddrFalse in *.
        destruct HgetMappedBEqss2 as [Hcontra | HgetMappedBEqss2Rec]; try(exfalso; congruence).
        apply blockIsMappedAddrInPaddrList with a2; trivial. simpl. rewrite Hs. rewrite Hs8. simpl.
        destruct (beqAddr currentPart a2) eqn:HbeqCurrA.
        { rewrite <-DTL.beqAddrTrue in HbeqCurrA. subst a2. simpl. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqBlock2A. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) a2) eqn:HbeqSceA.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceA. subst a2. rewrite Hs1 in HlookupA. simpl in *. exfalso.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset))
           (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqSces; try(congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          unfold scentryNext in *. rewrite HlookupA in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        simpl. destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) a2) eqn:HbeqSh1A.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1A. subst a2. unfold sh1entryAddr in *. exfalso.
          destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
          subst sh1entryaddr2. unfold sh1entryPDchild in *. rewrite HlookupA in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4.
        simpl. rewrite beqAddrFalse in *. rewrite HbeqBlock2A. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqCurrA. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        destruct (beqAddr block1InCurrPartAddr a2) eqn:HbeqBlock1A.
        * rewrite HnewB. simpl. rewrite <-DTL.beqAddrTrue in HbeqBlock1A. subst a2. rewrite HlookupBlock1s1 in *.
          injection HlookupA as HbentriesEq. subst b. rewrite app_nil_r.
          apply getAllPaddrBlockInclRev in HaddrInBlock. destruct HaddrInBlock as (HlebEnd1Addr & HltAddrEnd1 & _).
          apply getAllPaddrBlockIncl; lia.
        * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite HlookupA. rewrite app_nil_r. assumption.
  }
  assert(HlookupSce2Eqs5s2: lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s5) beqAddr
    = lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s2) beqAddr).
  {
    unfold scentryNext in *. rewrite Hs5. simpl.
    destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) (CPaddr (block2InCurrPartAddr+scoffset)))
      eqn:HbeqSh12Sce2.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh12Sce2. unfold sh1entryAddr in *. exfalso.
      destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      subst sh1entryaddr2. unfold sh1entryPDchild in *. rewrite HbeqSh12Sce2 in *.
      destruct (lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqBlock2Sce2.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlock2Sce2. rewrite <-HbeqBlock2Sce2 in *. exfalso.
      unfold sh1entryAddr in *. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr currentPart (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqCurrSce2.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrSce2. rewrite HbeqCurrSce2 in *. rewrite HlookupCurrs0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupSce2Eqs5s1: lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s5) beqAddr
    = lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s1) beqAddr).
  {
    rewrite HlookupSce2Eqs5s2. unfold scentryNext in *. rewrite Hs2. simpl.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqBlock1Sce2.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlock1Sce2. rewrite <-HbeqBlock1Sce2 in *. rewrite HlookupBlock1s0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupSce2Eqs5s0: lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s5) beqAddr
    = lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s0) beqAddr).
  {
    rewrite HlookupSce2Eqs5s1. unfold scentryNext in *. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (block2InCurrPartAddr+scoffset))) eqn:HbeqSces.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSces. apply CPaddrAddEq in HbeqSces. exfalso; congruence. intro Hcontra.
      assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold isPADDR in *. rewrite Hcontra in *. rewrite HlookupSce1s0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupSh12Eqs4s3: lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s4) beqAddr
    = lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s3) beqAddr).
  {
    unfold sh1entryAddr in *. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *. rewrite Hs4. simpl.
    destruct (beqAddr block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqBlock2Sh12.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlock2Sh12. rewrite <-HbeqBlock2Sh12 in *. exfalso.
      destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupSh12Eqs4s2: lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s4) beqAddr
    = lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s2) beqAddr).
  {
    unfold sh1entryAddr in *. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *.
    rewrite HlookupSh12Eqs4s3. rewrite Hs3. simpl.
    destruct (beqAddr currentPart (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqCurrSh12.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrSh12. rewrite <-HbeqCurrSh12 in *. rewrite HlookupCurrs0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupSh12Eqs4s1: lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s4) beqAddr
    = lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s1) beqAddr).
  {
    rewrite HlookupSh12Eqs4s2.
    unfold sh1entryAddr in *. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *. rewrite Hs2. simpl.
    destruct (beqAddr block1InCurrPartAddr (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqBlock1Sh12.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlock1Sh12. rewrite <-HbeqBlock1Sh12 in *. rewrite HlookupBlock1s0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupCurrs3: lookup currentPart (memory s3) beqAddr = Some (PDT pdentry1)).
  { rewrite Hs3. simpl. rewrite beqAddrTrue. reflexivity. }
  assert(HgetConfigPEq: forall part, isPDT part s -> getConfigPaddr part s = getConfigPaddr part s1).
  {
    intros part HpartIsPDT. assert(HpartIsPDTs8: isPDT part s8).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. rewrite HlookupCurrs8. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(Heqss8: getConfigPaddr part s = getConfigPaddr part s8).
    {
      rewrite Hs. apply getConfigPaddrEqPDT with pdentry2; trivial. rewrite Hpdentry3. reflexivity.
    }
    assert(HpartIsPDTs7: isPDT part s7).
    {
      unfold isPDT in *. rewrite Hs8 in HpartIsPDTs8. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. rewrite HlookupCurrs7. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(Heqss7: getConfigPaddr part s = getConfigPaddr part s7).
    {
      rewrite Heqss8. rewrite Hs8. apply getConfigPaddrEqPDT with pdentry1; trivial. rewrite Hpdentry2. reflexivity.
    }
    unfold isPDT in HpartIsPDTs7. rewrite Hs7 in HpartIsPDTs7. simpl in *.
    destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2Part; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(Heqss6: getConfigPaddr part s = getConfigPaddr part s6).
    {
      rewrite Heqss7. rewrite Hs7. apply getConfigPaddrEqBE; trivial. unfold isBE. rewrite HlookupBlock2s6. trivial.
    }
    rewrite Hs6 in HpartIsPDTs7. simpl in *.
    destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) part) eqn:HbeqScePart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(Heqss5: getConfigPaddr part s = getConfigPaddr part s5).
    {
      rewrite Heqss6. rewrite Hs6. apply getConfigPaddrEqSCE; trivial. unfold scentryNext in *. unfold isSCE.
      rewrite HlookupSce2Eqs5s0.
      destruct (lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
    }
    rewrite Hs5 in HpartIsPDTs7. simpl in *.
    destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) part) eqn:HbeqSh1Part; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(Heqss4: getConfigPaddr part s = getConfigPaddr part s4).
    {
      rewrite Heqss5. rewrite Hs5. apply getConfigPaddrEqSHE; trivial. unfold sh1entryAddr in *. unfold isSHE.
      destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). subst sh1entryaddr2. rewrite HlookupSh12Eqs4s1.
      unfold sh1entryPDchild in *.
      destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
    }
    rewrite Hs4 in HpartIsPDTs7. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Part in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(Heqss3: getConfigPaddr part s = getConfigPaddr part s3).
    {
      rewrite Heqss4. rewrite Hs4. apply getConfigPaddrEqBE; trivial. unfold bentryBlockIndex in *. unfold isBE.
      destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
    }
    assert(HpartIsPDTs2: isPDT part s2).
    {
      unfold isPDT. rewrite Hs3 in HpartIsPDTs7. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. rewrite HlookupCurrs2. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(Heqss2: getConfigPaddr part s = getConfigPaddr part s2).
    {
      rewrite Heqss3. rewrite Hs3. apply getConfigPaddrEqPDT with pdentry; trivial. rewrite Hpdentry1. reflexivity.
    }
    unfold isPDT in *. rewrite Hs2 in HpartIsPDTs2. simpl in *.
    destruct (beqAddr block1InCurrPartAddr part) eqn:HbeqBlock1Part; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Heqss2. rewrite Hs2. apply getConfigPaddrEqBE; trivial. unfold isBE. rewrite HlookupBlock1s1. trivial.
  }
  assert(HgetAccMappedPEqss4: forall part, isPDT part s
    -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s4).
  {
    destruct HnewB2 as [l0 [l1 HnewB2]]. destruct HnewB3 as [l2 [l3 HnewB3]].
    intros part HpartIsPDTs. assert(Heqs8: getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s8).
    {
      rewrite Hs. apply getAccessibleMappedPaddrEqPDT with pdentry2; trivial. rewrite Hpdentry3. reflexivity.
    }
    assert(Heqs7: getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s7).
    {
      rewrite Heqs8. rewrite Hs8. apply getAccessibleMappedPaddrEqPDT with pdentry1; trivial. rewrite Hpdentry2.
      reflexivity.
    }
    assert(HpartIsPDTs6: isPDT part s6).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDTs. rewrite Hs8 in HpartIsPDTs. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs6. trivial.
      - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HpartIsPDTs. simpl in *.
        destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs5: isPDT part s5).
    {
      unfold isPDT in *. rewrite Hs6 in HpartIsPDTs6. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) part) eqn:HbeqScePart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(Heqs6: getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s6).
    {
      rewrite Heqs7. rewrite Hs7.
      apply getAccessibleMappedPaddrEqBEPresentFalseNoChangeLight with emptyBentry; trivial.
      - rewrite HnewB3; try(reflexivity).
      - rewrite HnewB3. simpl. rewrite HnewB2. reflexivity.
    }
    assert(Heqs5: getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s5).
    {
      rewrite Heqs6. rewrite Hs6. apply getAccessibleMappedPaddrEqSCE; trivial.
      assert(Hwell: wellFormedShadowCutIfBlockEntry s2) by (unfold cons1Free in *; intuition).
      specialize(Hwell block2InCurrPartAddr Hblock2IsBEs2). destruct Hwell as [sce (HsceIsSCE & Hsce)]. subst sce.
      assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s2) by (unfold cons1Free in *; intuition).
      specialize(Hsh1IsSHE block2InCurrPartAddr Hblock2IsBEs2). unfold isSCE in *. rewrite Hs5. simpl.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) (CPaddr (block2InCurrPartAddr + scoffset)))
        eqn:HbeqSh1Sce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. unfold isSHE in *.
        destruct (lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s2) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      destruct (beqAddr block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqBlockSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *. unfold isBE in *.
        destruct (lookup block2InCurrPartAddr (memory s2) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr currentPart (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite <-HbeqCurrSce in *. rewrite HlookupCurrs2 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs4: isPDT part s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDTs. rewrite Hs8 in HpartIsPDTs. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs4. trivial.
      - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HpartIsPDTs. simpl in *.
        destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in HpartIsPDTs. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) part) eqn:HbeqSce2Part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs5 in HpartIsPDTs. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) part) eqn:HbeqSh12Part;
          try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    rewrite Heqs5. rewrite Hs5. apply getAccessibleMappedPaddrEqSHE; trivial.
    assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s2) by (unfold cons1Free in *; intuition).
    specialize(Hsh1IsSHE block2InCurrPartAddr Hblock2IsBEs2). unfold isSHE in *. rewrite Hs4. simpl.
    destruct (beqAddr block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. unfold isBE in *.
      destruct (lookup block2InCurrPartAddr (memory s2) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr currentPart (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqCurrSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite <-HbeqCurrSh1 in *. rewrite HlookupCurrs2 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HgetAccMappedPNotCurrEqss1: forall part, isPDT part s -> currentPart <> part
    -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s1).
  {
    intros part HpartIsPDTs HbeqCurrPart.
    assert(Heqs3s2: getAccessibleMappedPaddr part s3 = getAccessibleMappedPaddr part s2).
    {
      rewrite Hs3. apply getAccessibleMappedPaddrEqPDT with pdentry; trivial.
      - rewrite Hpdentry1. reflexivity.
      - unfold cons1Free in *. intuition.
    }
    rewrite HgetAccMappedPEqss4; trivial. assert(HpartIsPDTs4: isPDT part s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDTs. rewrite Hs8 in HpartIsPDTs. simpl in *.
      rewrite beqAddrFalse in *. rewrite HbeqCurrPart in *. rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HpartIsPDTs. simpl in *.
      destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HpartIsPDTs. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) part) eqn:HbeqSce2Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HpartIsPDTs. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) part) eqn:HbeqSh12Part;
        try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs3: isPDT part s3).
    {
      unfold isPDT in *. rewrite Hs4 in HpartIsPDTs4. simpl in *.
      destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs2: isPDT part s2).
    {
      unfold isPDT in *. rewrite Hs3 in HpartIsPDTs3. simpl in *. rewrite beqAddrFalse in *.
      rewrite HbeqCurrPart in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HpartIsPDTs1: isPDT part s1).
    {
      unfold isPDT in *. rewrite Hs2 in HpartIsPDTs2. simpl in *.
      destruct (beqAddr block1InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(Heqs3: getAccessibleMappedPaddr part s3 = getAccessibleMappedPaddr part s1).
    {
      rewrite Heqs3s2. rewrite Hs2. apply getAccessibleMappedPaddrEqBENotInPart; trivial.
      + unfold isBE. unfold sh1entryAddr in *.
        destruct (lookup block1InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
        trivial.
      + unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock1Mappeds1.
        assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
        specialize(Hdisjoint currentPart part HcurrIsPDTs1 HpartIsPDTs1 HbeqCurrPart).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        apply Hdisjoint; assumption.
    }
    rewrite <-Heqs3. rewrite Hs4. apply getAccessibleMappedPaddrEqBENotInPart; trivial.
    + unfold isBE. unfold bentryBlockIndex in *.
      destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; try(congruence).
      trivial.
    + rewrite <-HgetMappedBEqs2s1 in Hblock2Mappeds1. unfold getMappedBlocks in *.
      apply InFilterPresentInList in Hblock2Mappeds1.
      assert(Hdisjoint: DisjointKSEntries s2) by (unfold cons1Free in *; intuition).
      specialize(Hdisjoint currentPart part HcurrIsPDTs2 HpartIsPDTs2 HbeqCurrPart).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      rewrite HgetKSEntriesEqs3s2. apply Hdisjoint; assumption.
  }
  assert(HgetAccessMappedEqs2s1: forall part, getAccessibleMappedBlocks part s2 = getAccessibleMappedBlocks part s1).
  {
    destruct HnewB as [l0 [l1 HnewB]].
    intro part. rewrite Hs2. apply getAccessibleMappedBlocksEqBEAccessiblePresentNoChange with bentry1; trivial.
    1,2: rewrite HnewB; reflexivity.
  }
  assert(HAflag1s: bentryAFlag block1InCurrPartAddr true s).
  {
    destruct HnewB as [l0 [l1 HnewB]]. unfold bentryAFlag in *. rewrite HlookupBlock1Eqss2. rewrite HlookupBlock1s2.
    rewrite HnewB. simpl. rewrite HlookupBlock1s1 in *. assumption.
  }
  assert(HgetAccMappedPCurrEqss1: forall addr,
    In addr (getAccessibleMappedPaddr currentPart s) <-> In addr (getAccessibleMappedPaddr currentPart s1)).
  {
    destruct HnewB as [l0 [l1 HnewB]]. destruct HnewB2 as [l2 [l3 HnewB2]]. destruct HnewB3 as [l4 [l5 HnewB3]].
    intro addr. unfold getAccessibleMappedPaddr. split.
    - intro HaddrMappeds. assert(HgetMappedBEqss2: forall block,
        In block (getAccessibleMappedBlocks currentPart s) -> In block (getAccessibleMappedBlocks currentPart s2)).
      {
        intros block HblockAcc. assert(HblockMapped: In block (getMappedBlocks currentPart s)).
        {
          unfold getAccessibleMappedBlocks in *.
          destruct (lookup currentPart (memory s) beqAddr); try(simpl in *; exfalso; congruence).
          destruct v; try(simpl in *; exfalso; congruence). apply InFilterAccessibleInList with s; assumption.
        }
        specialize(HgetMappedBCurrEqss2 block). destruct HgetMappedBCurrEqss2 as (_ & Hres & _).
        specialize(Hres HblockMapped). apply accessibleBlockIsAccessibleMapped; trivial.
        apply accessibleMappedBlockIsAccessible in HblockAcc. unfold bentryAFlag in *. rewrite Hs in HblockAcc.
        rewrite Hs8 in HblockAcc. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HblockAcc. simpl in *.
        destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        { rewrite HnewB3 in HblockAcc. simpl in *. rewrite HnewB2 in HblockAcc. simpl in *. exfalso; congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in HblockAcc. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs5 in HblockAcc. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs4 in HblockAcc. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Block in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs3 in HblockAcc. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HmappedIsPres: forall block, In block (getAccessibleMappedBlocks currentPart s)
        -> bentryAFlag block true s).
      { intros block. apply accessibleMappedBlockIsAccessible. }
      induction (getAccessibleMappedBlocks currentPart s); simpl in *; try(exfalso; congruence).
      assert(HgetMappedBEqss2Rec: forall block, In block l -> In block (getAccessibleMappedBlocks currentPart s2)).
      { intros block HblockMapped. apply HgetMappedBEqss2; auto. }
      assert(HmappedIsPresRec: forall block, In block l -> bentryAFlag block true s).
      { intros block HblockMapped. apply HmappedIsPres; auto. }
      destruct (lookup a2 (memory s) beqAddr) eqn:HlookupA; try(apply IHl; assumption).
      destruct v; try(apply IHl; assumption). apply in_app_or in HaddrMappeds.
      destruct HaddrMappeds as [HaddrInBlock | HaddrMappedsRec]; try(apply IHl; assumption).
      assert(Ha2: a2 = a2 \/ In a2 l) by (left; reflexivity). specialize(HgetMappedBEqss2 a2 Ha2).
      specialize(HmappedIsPres a2 Ha2). unfold bentryAFlag in *. rewrite HlookupA in *.
      rewrite HgetMappedBEqs2s1 in *. rewrite Hs in HlookupA. rewrite Hs8 in HlookupA. simpl in *.
      destruct (beqAddr currentPart a2) eqn:HbeqCurrA; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HlookupA. simpl in *.
      destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A.
      {
        injection HlookupA as HbentriesEq. subst b. rewrite HnewB3 in HmappedIsPres. simpl in *.
        rewrite HnewB2 in HmappedIsPres. simpl in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HlookupA. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) a2) eqn:HbeqSceA; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HlookupA. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) a2) eqn:HbeqSh1A; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HlookupA. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2A in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HlookupA. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrA in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupA. simpl in *. destruct (beqAddr block1InCurrPartAddr a2) eqn:HbeqBlock1A.
      + injection HlookupA as HbentriesEq. rewrite HnewB in HbentriesEq. subst b. simpl in *.
        assert(HpropsOr: In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)))
          \/ In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)).
        {
          apply getAllPaddrBlockInclRev in HaddrInBlock. destruct HaddrInBlock as (HlebStart1Addr & HltAddrEnd2 & _).
          destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
          - apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. left. apply getAllPaddrBlockIncl; lia.
          - apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. right. apply getAllPaddrBlockIncl; lia.
        }
        destruct HpropsOr as [HaddrInBlock1 | HaddrInBlock2].
        * apply blockIsMappedAddrInPaddrList with block1InCurrPartAddr.
          --- apply accessibleBlockIsAccessibleMapped; trivial.
          --- simpl. rewrite HlookupBlock1s1. rewrite app_nil_r. assumption.
        * apply blockIsMappedAddrInPaddrList with block2InCurrPartAddr.
          --- apply accessibleBlockIsAccessibleMapped; trivial.
          --- simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs1. rewrite Hs1 in Hstart2s1.
              simpl in *.
              destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock2;
                try(exfalso; congruence). rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r. subst block2End. rewrite Hstart2s1 in *.
              assumption.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        apply blockIsMappedAddrInPaddrList with a2.
        * rewrite <-HgetAccessMappedEqs2s1. assumption.
        * simpl. rewrite HlookupA. rewrite app_nil_r. assumption.
    - intro HaddrMappeds1. rewrite <-HgetAccessMappedEqs2s1 in HaddrMappeds1.
      assert(HgetMappedBEqss2: forall block, In block (getAccessibleMappedBlocks currentPart s2) ->
        block2InCurrPartAddr = block \/ In block (getAccessibleMappedBlocks currentPart s)).
      {
        intros block HblockAcc. assert(HblockMapped: In block (getMappedBlocks currentPart s2)).
        {
          unfold getAccessibleMappedBlocks in *.
          destruct (lookup currentPart (memory s2) beqAddr); try(simpl in *; exfalso; congruence).
          destruct v; try(simpl in *; exfalso; congruence). apply InFilterAccessibleInList with s2; assumption.
        }
        specialize(HgetMappedBCurrEqss2 block). destruct HgetMappedBCurrEqss2 as (Hres & _).
        specialize(Hres HblockMapped). destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        + rewrite <-DTL.beqAddrTrue in HbeqBlock2Block. left. assumption.
        + rewrite <-beqAddrFalse in *. destruct Hres as [HblocksEq | Hres]; try(exfalso; congruence). right.
          apply accessibleBlockIsAccessibleMapped; trivial.
          apply accessibleMappedBlockIsAccessible in HblockAcc. unfold bentryAFlag in *. rewrite Hs. rewrite Hs8.
          simpl. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrBlock. subst block. rewrite HlookupCurrs2 in *. congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqBlock2Block. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block) eqn:HbeqSceBlock.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSceBlock. rewrite HbeqSceBlock in *. unfold scentryNext in *. exfalso.
            rewrite <-HlookupSce2Eqs5s0 in *. rewrite HlookupSce2Eqs5s2 in *.
            destruct (lookup block (memory s2) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSh1Block. unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2. unfold sh1entryPDchild in *. rewrite HbeqSh1Block in *.
            rewrite <-HlookupSh12Eqs4s2 in HblockAcc. rewrite HlookupSh12Eqs4s1 in HblockAcc.
            destruct (lookup block (memory s1) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Block. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrBlock. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      assert(In block1InCurrPartAddr (getAccessibleMappedBlocks currentPart s)).
      {
        specialize(HgetMappedBCurrEqss2 block1InCurrPartAddr). destruct HgetMappedBCurrEqss2 as (Hres & _).
        rewrite HgetMappedBEqs2s1 in Hres. specialize(Hres Hblock1Mappeds1).
        destruct Hres as [Hcontra | Hres]; try(exfalso; congruence). apply accessibleBlockIsAccessibleMapped; trivial.
      }
      induction (getAccessibleMappedBlocks currentPart s2); simpl in *; try(exfalso; congruence).
      assert(forall block, In block l ->
        block2InCurrPartAddr = block \/ In block (getAccessibleMappedBlocks currentPart s)).
      { intros block HblockMapped. apply HgetMappedBEqss2; auto. }
      destruct (lookup a2 (memory s1) beqAddr) eqn:HlookupA; try(apply IHl; assumption).
      destruct v; try(apply IHl; assumption). apply in_app_or in HaddrMappeds1.
      destruct HaddrMappeds1 as [HaddrInBlock | HaddrMappeds1Rec]; try(apply IHl; assumption).
      assert(Ha2: a2 = a2 \/ In a2 l) by (left; reflexivity). specialize(HgetMappedBEqss2 a2 Ha2).
      destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A.
      + rewrite <-DTL.beqAddrTrue in HbeqBlock2A. subst a2. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        rewrite HlookupA in *. rewrite Hs1 in HlookupA. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock2;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HlookupA in *. rewrite <-Hend2s0 in *.
        rewrite <-Hstart2s1 in *. apply blockIsMappedAddrInPaddrList with block1InCurrPartAddr; trivial. simpl.
        rewrite HlookupBlock1Eqss2. rewrite HlookupBlock1s2. rewrite HnewB. simpl. rewrite app_nil_r.
        apply getAllPaddrBlockInclRev in HaddrInBlock. destruct HaddrInBlock as (HlebEnd1Addr & HltAddrEnd2 & _).
        assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
        specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
          HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
        apply getAllPaddrBlockIncl; lia.
      + rewrite <-beqAddrFalse in *.
        destruct HgetMappedBEqss2 as [Hcontra | HgetMappedBEqss2Rec]; try(exfalso; congruence).
        apply blockIsMappedAddrInPaddrList with a2; trivial. simpl. rewrite Hs. rewrite Hs8. simpl.
        destruct (beqAddr currentPart a2) eqn:HbeqCurrA.
        { rewrite <-DTL.beqAddrTrue in HbeqCurrA. subst a2. simpl. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqBlock2A. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) a2) eqn:HbeqSceA.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceA. subst a2. rewrite Hs1 in HlookupA. simpl in *. exfalso.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset))
           (CPaddr (block2InCurrPartAddr + scoffset))) eqn:HbeqSces; try(congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          unfold scentryNext in *. rewrite HlookupA in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        simpl. destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) a2) eqn:HbeqSh1A.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1A. subst a2. unfold sh1entryAddr in *. exfalso.
          destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
          subst sh1entryaddr2. unfold sh1entryPDchild in *. rewrite HlookupA in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4.
        simpl. rewrite beqAddrFalse in *. rewrite HbeqBlock2A. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqCurrA. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        destruct (beqAddr block1InCurrPartAddr a2) eqn:HbeqBlock1A.
        * rewrite HnewB. simpl. rewrite <-DTL.beqAddrTrue in HbeqBlock1A. subst a2. rewrite HlookupBlock1s1 in *.
          injection HlookupA as HbentriesEq. subst b. rewrite app_nil_r.
          apply getAllPaddrBlockInclRev in HaddrInBlock. destruct HaddrInBlock as (HlebEnd1Addr & HltAddrEnd1 & _).
          apply getAllPaddrBlockIncl; lia.
        * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite HlookupA. rewrite app_nil_r. assumption.
  }

  assert(partitionsIsolation s).
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
    assert(isPDT child1 s) by (apply childrenArePDT with pdparent; unfold cons1Free in *; intuition).
    assert(isPDT child2 s) by (apply childrenArePDT with pdparent; unfold cons1Free in *; intuition).
    rewrite HgetPartsEqss2 in *. assert(isPDT pdparent s3).
    { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
    rewrite HgetChildrenEqss2 in *; trivial. rewrite HgetPartsEqs2s1 in *. assert(isPDT pdparent s1).
    { apply partitionsArePDT; unfold consistency1 in *; intuition. }
    rewrite HgetChildrenEqs2s1 in *; trivial.
    specialize(HPIs1 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
    unfold getUsedPaddr in *. rewrite HgetConfigPEq; trivial. rewrite HgetConfigPEq; trivial. intros addr HaddrUsed1.
    assert(HaddrUsed1s1: In addr (getConfigPaddr child1 s1 ++ getMappedPaddr child1 s1)).
    {
      destruct (beqAddr currentPart child1) eqn:HbeqCurrChild1.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrChild1. subst child1. apply in_or_app. apply in_app_or in HaddrUsed1.
        destruct HaddrUsed1 as [HaddrConfig | HaddrMappeds]; try(left; assumption). right.
        apply HgetMappedPCurrEqss1; assumption.
      - rewrite <-beqAddrFalse in *. rewrite HgetMappedPNotCurrEqss1 in HaddrUsed1; assumption.
    }
    specialize(HPIs1 addr HaddrUsed1s1). contradict HPIs1. destruct (beqAddr currentPart child2) eqn:HbeqCurrChild2.
    - rewrite <-DTL.beqAddrTrue in HbeqCurrChild2. subst child2. apply in_or_app. apply in_app_or in HPIs1.
      destruct HPIs1 as [HaddrConfig | HaddrMappeds]; try(left; assumption). right.
      apply HgetMappedPCurrEqss1; assumption.
    - rewrite <-beqAddrFalse in *. rewrite HgetMappedPNotCurrEqss1 in HPIs1; assumption.
    (* END partitionsIsolation *)
  }

  assert(kernelDataIsolation s).
  { (* BEGIN kernelDataIsolation s *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart. assert(isPDT part2 s).
    { apply partitionsArePDT; unfold cons1Free in *; intuition. }
    assert(isPDT part1 s).
    { apply partitionsArePDT; unfold cons1Free in *; intuition. }
    rewrite HgetPartsEqss2 in *. rewrite HgetPartsEqs2s1 in *.
    specialize(HKDIs1 part1 part2 Hpart1IsPart Hpart2IsPart). rewrite HgetConfigPEq; trivial.
    intros addr HaddrAccMapped. apply HKDIs1. destruct (beqAddr currentPart part1) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part1. apply HgetAccMappedPCurrEqss1; assumption.
    - rewrite <-beqAddrFalse in *. rewrite <-HgetAccMappedPNotCurrEqss1; trivial.
    (* END kernelDataIsolation *)
  }

  assert(verticalSharing s).
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild. assert(isPDT pdparent s).
    { apply partitionsArePDT; unfold cons1Free in *; intuition. }
    assert(isPDT child s).
    { apply childrenArePDT with pdparent; unfold cons1Free in *; intuition. }
    rewrite HgetPartsEqss2 in *. assert(isPDT pdparent s3).
    { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; intuition. }
    rewrite HgetPartsEqs2s1 in *. assert(isPDT pdparent s1).
    { apply partitionsArePDT; unfold consistency1 in *; intuition. }
    rewrite HgetChildrenEqss2 in *; trivial. rewrite HgetChildrenEqs2s1 in *; trivial.
    specialize(HVSs1 pdparent child HparentIsPart HchildIsChild). unfold getUsedPaddr. intros addr HaddrUsed.
    rewrite HgetConfigPEq in *; trivial. assert(HaddrUseds1: In addr (getUsedPaddr child s1)).
    {
      unfold getUsedPaddr. apply in_or_app. apply in_app_or in HaddrUsed.
      destruct HaddrUsed as [HaddrInConfig | HaddrMapped]; try(left; assumption). right.
      destruct (beqAddr currentPart child) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst child. apply HgetMappedPCurrEqss1. assumption.
      - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedPNotCurrEqss1; assumption.
    }
    specialize(HVSs1 addr HaddrUseds1). destruct (beqAddr currentPart pdparent) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. apply HgetMappedPCurrEqss1. assumption.
    - rewrite <-beqAddrFalse in *. rewrite HgetMappedPNotCurrEqss1; assumption.
    (* END verticalSharing *)
  }

  assert(HgetKSEqs2s1: forall part, getKSEntries part s2 = getKSEntries part s1).
  {
    intro part. rewrite Hs2. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock1s1. trivial.
  }
  assert(HlookupBlock2Eqss7: lookup block2InCurrPartAddr (memory s) beqAddr
    = lookup block2InCurrPartAddr (memory s7) beqAddr).
  {
    rewrite Hs. rewrite Hs8. simpl. destruct (beqAddr currentPart block2InCurrPartAddr) eqn:HbeqCurrBlock2.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBlock2. rewrite HbeqCurrBlock2 in *. exfalso; congruence.
    }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupBlock2Eqs1s0: lookup block2InCurrPartAddr (memory s1) beqAddr
    = lookup block2InCurrPartAddr (memory s0) beqAddr).
  {
    unfold bentryPFlag in *. rewrite Hs1. rewrite Hs1 in HPflag2s1. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2InCurrPartAddr) eqn:HbeqSceBlock2;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupBlock1Eqs3s1: lookup block2InCurrPartAddr (memory s3) beqAddr
    = lookup block2InCurrPartAddr (memory s1) beqAddr).
  {
    unfold bentryBlockIndex in *. rewrite Hs3. rewrite Hs3 in Hbindex2s3. simpl in *.
    destruct (beqAddr currentPart block2InCurrPartAddr) eqn:HbeqCurrBlock2; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlocks12. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(Hblock2IsBEs1: isBE block2InCurrPartAddr s1).
  {
    unfold isBE. unfold bentryPFlag in *. destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqs4s3: getPartitions multiplexer s4 = getPartitions multiplexer s3).
  {
    rewrite Hs4. unfold bentryBlockIndex in *.
    destruct (lookup block2InCurrPartAddr (memory s3) beqAddr) eqn:Hlookup2; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    apply getPartitionsEqBEPDflagFalse with b sh1entryaddr2; trivial.
    - unfold sh1entryAddr in *. rewrite <-HlookupBlock1Eqs3s1 in *. rewrite Hlookup2. assumption.
    - assert(HnoPDs1: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
      specialize(HnoPDs1 block2InCurrPartAddr sh1entryaddr2 Hblock2IsBEs1 Hsh12s1 HAflag2s1).
      unfold sh1entryPDflag in *. unfold sh1entryAddr in *. rewrite <-HlookupBlock1Eqs3s1 in *. subst sh1entryaddr2.
      rewrite <-HlookupSh12Eqs4s3. rewrite HlookupSh12Eqs4s1. assumption.
  }
  assert(HpdentriesEq: pdentryCurr = pdentry).
  {
    rewrite Hs2 in HlookupCurrs2. simpl in *.
    destruct (beqAddr block1InCurrPartAddr currentPart) eqn:HbeqBlock1Curr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite HlookupCurrs1 in HlookupCurrs2. injection HlookupCurrs2. trivial.
  }
  subst pdentryCurr.
  assert(HlookupSh12Eqs1s0: lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s1) beqAddr
    = lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s0) beqAddr).
  {
    unfold sh1entryAddr in *. unfold sh1entryPDchild in *.
    destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst sh1entryaddr2. rewrite Hs1. rewrite Hs1 in HPDchild2s1. simpl in *.
    destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (CPaddr (block2InCurrPartAddr + sh1offset)))
      eqn:HbeqSce2Sh12; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(Hblock1HasNoChilds0: forall child addr, In child (getChildren currentPart s0)
    -> In addr (getAllPaddrAux [block1InCurrPartAddr] s0)
    -> ~ In addr (getMappedPaddr child s0)).
  {
    unfold sh1entryAddr in *. rewrite HlookupBlock1s0 in *. rewrite Hs1 in Hcurr. simpl in *.
    assert(HcurrIsParts0: In (currentPartition s0) (getPartitions multiplexer s0)).
    { unfold consistency in *; unfold consistency1 in *; intuition. }
    unfold currentPartitionInPartitionsList in *. rewrite <-Hcurr in *.
    assert(HnoChilds0: noChildImpliesAddressesNotShared s0).
    { unfold consistency in *; unfold consistency2 in *; intuition. }
    specialize(HnoChilds0 currentPart pdentry block1InCurrPartAddr sh1entryaddr1 HcurrIsParts0 HlookupCurrs0
      Hblock1Mappeds0 Hsh11s0 HPDchild1s0). assumption.
  }
  assert(HPDchild2s0Bis: sh1entryPDchild sh1entryaddr2 nullAddr s0).
  {
    unfold sh1entryAddr in *.
    destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *.
    rewrite HlookupSh12Eqs1s0 in *. assumption.
  }
  assert(Hblock2HasNoChilds0: forall child addr, In child (getChildren currentPart s0)
    -> In addr (getAllPaddrAux [block2InCurrPartAddr] s0)
    -> ~ In addr (getMappedPaddr child s0)).
  {
    unfold sh1entryAddr in *.
    destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite Hs1 in Hcurr. simpl in *.
    assert(HcurrIsParts0: In (currentPartition s0) (getPartitions multiplexer s0)).
    { unfold consistency in *; unfold consistency1 in *; intuition. }
    unfold currentPartitionInPartitionsList in *. rewrite <-Hcurr in *.
    assert(HnoChilds0: noChildImpliesAddressesNotShared s0).
    { unfold consistency in *; unfold consistency2 in *; intuition. }
    specialize(HnoChilds0 currentPart pdentry block2InCurrPartAddr sh1entryaddr2 HcurrIsParts0 HlookupCurrs0
      Hblock2Mappeds0 Hsh12s0 HPDchild2s0Bis). assumption.
  }
  assert(HgetMappedPEqs1s0: forall part, isPDT part s0 -> getMappedPaddr part s1 = getMappedPaddr part s0).
  {
    intros part HpartIsPDT. rewrite Hs1. apply getMappedPaddrEqSCE; trivial. unfold isSCE. rewrite HlookupSce1s0.
    trivial.
  }

  assert(consistency2 s).
  {
    destruct HnewB as [l0 [l1 HnewB]]. destruct HnewB2 as [l2 [l3 HnewB2]]. destruct HnewB3 as [l4 [l5 HnewB3]].
    assert(noDupMappedPaddrList s).
    { (* BEGIN noDupMappedPaddrList s *)
      intros part HpartIsPDT. assert(HpartIsPDTs4: isPDT part s4).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs8 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs4. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HpartIsPDT. simpl in *.
          destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs6 in HpartIsPDT. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) part) eqn:HbeqSce2Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs5 in HpartIsPDT. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) part) eqn:HbeqSh12Part;
            try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HpartIsPDTs1: isPDT part s1).
      {
        unfold isPDT in *. rewrite Hs4 in HpartIsPDTs4. simpl in *.
        destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock2Part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs3 in HpartIsPDTs4. simpl in *. destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HpartIsPDTs4. simpl in *.
          destruct (beqAddr block1InCurrPartAddr part) eqn:HbeqBlock1Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(HnoDupMappedPs1 part HpartIsPDTs1). destruct (beqAddr currentPart part) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part.
        assert(HmappedIsPres: forall block, In block (getMappedBlocks currentPart s) -> bentryPFlag block true s).
        {
          intros block HblockMapped. apply mappedBlockIsBE in HblockMapped. unfold bentryPFlag.
          destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup. auto.
        }
        unfold getMappedBlocks in HmappedIsPres. unfold getMappedPaddr.
        unfold getMappedPaddr in HnoDupMappedPs1. unfold getMappedBlocks in HnoDupMappedPs1. unfold getMappedBlocks.
        rewrite HgetKSEqss2 in *; trivial. rewrite HgetKSEqs2s1 in *. unfold getMappedBlocks in Hblock2Mappeds1.
        assert(HnoDupKSs1: noDupKSEntriesList s1) by (unfold consistency1 in *; intuition).
        specialize(HnoDupKSs1 currentPart HpartIsPDTs1). unfold getMappedBlocks in Hblock1Mappeds1.
        induction (filterOptionPaddr (getKSEntries currentPart s1)); simpl in *; try(apply NoDup_nil).
        apply NoDup_cons_iff in HnoDupKSs1. destruct HnoDupKSs1 as (Ha2NotInL & HnoDupKSs1).
        assert(HmappedIsPresRec: forall block, In block (filterPresent l s) -> bentryPFlag block true s).
        {
          intros block HblockMapped. apply HmappedIsPres.
          destruct (lookup a2 (memory s) beqAddr); trivial. destruct v; trivial. destruct (present b); trivial. simpl.
          right. assumption.
        }
        assert(HnoDupMappedPs1Rec: NoDup (getAllPaddrAux (filterPresent l s1) s1)).
        {
          destruct (lookup a2 (memory s1) beqAddr) eqn:HlookupA; trivial. destruct v; trivial.
          destruct (present b); trivial. simpl in *. rewrite HlookupA in *.
          apply Lib.NoDupSplitInclIff in HnoDupMappedPs1. apply HnoDupMappedPs1.
        }
        assert(HpropsOrBlock2: a2 = block2InCurrPartAddr \/ In block2InCurrPartAddr (filterPresent l s1)).
        {
          destruct (lookup a2 (memory s1) beqAddr); try(right; assumption). destruct v; try(right; assumption).
          destruct (present b); try(right; assumption). simpl in *. assumption.
        }
        assert(HpropsOrBlock1: a2 = block1InCurrPartAddr \/ In block1InCurrPartAddr (filterPresent l s1)).
        {
          destruct (lookup a2 (memory s1) beqAddr); try(right; assumption). destruct v; try(right; assumption).
          destruct (present b); try(right; assumption). simpl in *. assumption.
        }
        clear Hblock2Mappeds1. clear Hblock1Mappeds1.
        assert(HfilterEqss4: filterPresent l s = filterPresent l s4).
        {
          assert(Heqs8: filterPresent l s = filterPresent l s8).
          { rewrite Hs. apply filterPresentEqPDT. unfold isPDT. rewrite HlookupCurrs8. trivial. }
          assert(Heqs7: filterPresent l s = filterPresent l s7).
          { rewrite Heqs8. rewrite Hs8. apply filterPresentEqPDT. unfold isPDT. rewrite HlookupCurrs7. trivial. }
          assert(Heqs6: filterPresent l s = filterPresent l s6).
          {
            rewrite Heqs7. rewrite Hs7. apply filterPresentEqBENoChange with emptyBentry; trivial. rewrite HnewB3.
            reflexivity.
          }
          assert(Heqs5: filterPresent l s = filterPresent l s5).
          {
            rewrite Heqs6. rewrite Hs6. apply filterPresentEqSCE. unfold isSCE. rewrite HlookupSce2Eqs5s0.
            unfold scentryNext in *.
            destruct (lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). trivial.
          }
          rewrite Heqs5. rewrite Hs5. apply filterPresentEqSHE. unfold isSHE. rewrite HlookupSh12Eqs4s1.
          unfold sh1entryAddr in *.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *.
          destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s1) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
        }
        rewrite HfilterEqss4 in *. assert(HallPaddrEqss4: getAllPaddrAux (filterPresent l s4) s
          = getAllPaddrAux (filterPresent l s4) s2).
        {
          assert(Heqs8: getAllPaddrAux (filterPresent l s4) s = getAllPaddrAux (filterPresent l s4) s8).
          { rewrite Hs. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupCurrs8. trivial. }
          assert(Heqs7: getAllPaddrAux (filterPresent l s4) s = getAllPaddrAux (filterPresent l s4) s7).
          { rewrite Heqs8. rewrite Hs8. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupCurrs7. trivial. }
          assert(~ In block2InCurrPartAddr (filterPresent l s4)).
          {
            intro Hcontra. apply HmappedIsPresRec in Hcontra. unfold bentryPFlag in *.
            rewrite HlookupBlock2Eqss7 in *. rewrite Hs7 in Hcontra. simpl in *. rewrite beqAddrTrue in *.
            rewrite HnewB3 in Hcontra. simpl in *. rewrite HnewB2 in Hcontra. simpl in *. congruence.
          }
          assert(Heqs6: getAllPaddrAux (filterPresent l s4) s = getAllPaddrAux (filterPresent l s4) s6).
          { rewrite Heqs7. rewrite Hs7. apply getAllPaddrAuxEqBENoInList; assumption. }
          assert(Heqs5: getAllPaddrAux (filterPresent l s4) s = getAllPaddrAux (filterPresent l s4) s5).
          {
            rewrite Heqs6. rewrite Hs6. apply getAllPaddrAuxEqSCE. unfold isSCE. rewrite HlookupSce2Eqs5s0.
            unfold scentryNext in *.
            destruct (lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). trivial.
          }
          assert(Heqs4: getAllPaddrAux (filterPresent l s4) s = getAllPaddrAux (filterPresent l s4) s4).
          {
            rewrite Heqs5. rewrite Hs5. apply getAllPaddrAuxEqSHE. unfold isSHE. rewrite HlookupSh12Eqs4s1.
            unfold sh1entryAddr in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s1) beqAddr); try(congruence).
            destruct v; try(congruence). trivial.
          }
          assert(Heqs3: getAllPaddrAux (filterPresent l s4) s = getAllPaddrAux (filterPresent l s4) s3).
          { rewrite Heqs4. rewrite Hs4. apply getAllPaddrAuxEqBENoInList; rewrite <-Hs4; trivial. }
          rewrite Heqs3. rewrite Hs3. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupCurrs2. trivial.
        }
        rewrite HallPaddrEqss4 in *.
        destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A.
        + rewrite <-DTL.beqAddrTrue in HbeqBlock2A. subst a2. rewrite HlookupBlock2Eqss7 in *. rewrite Hs7. simpl.
          rewrite beqAddrTrue. rewrite HnewB3. simpl. rewrite HnewB2. simpl. rewrite HallPaddrEqss4.
          rewrite Hs7 in HmappedIsPres. simpl in *. rewrite beqAddrTrue in *. rewrite HnewB3 in HmappedIsPres.
          simpl in *. rewrite HnewB2 in HmappedIsPres. simpl in *. clear HpropsOrBlock1.
          unfold bentryStartAddr in *. rewrite HlookupBlock2Eqs1s0 in *. unfold bentryEndAddr in *.
          unfold bentryPFlag in *.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlock2s0; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-HPflag2s0 in *. simpl in *.
          rewrite HlookupBlock2Eqs1s0 in *. apply Lib.NoDupSplitInclIff in HnoDupMappedPs1.
          destruct HnoDupMappedPs1 as (_ & HdisjointRangeL).
          clear HfilterEqss4. clear HpropsOrBlock2. clear HmappedIsPres. clear HmappedIsPresRec. clear HallPaddrEqss4.
          clear IHl. rewrite <-Hend2s0 in *. rewrite <-Hstart2s1 in *.
          induction l; simpl in *; try(apply NoDup_nil). rewrite Hs4. simpl. rewrite <-Hs4.
          apply Classical_Prop.not_or_and in Ha2NotInL. destruct Ha2NotInL as (HbeqBlock2A & Hblock2NotInL).
          apply not_eq_sym in HbeqBlock2A. rewrite beqAddrFalse in *. rewrite HbeqBlock2A.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          destruct (beqAddr currentPart a2) eqn:HbeqCurrA.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrA. subst a2. rewrite HlookupCurrs1 in *. apply IHl; trivial.
            apply NoDup_cons_iff in HnoDupKSs1. destruct HnoDupKSs1 as (_ & Hrec). assumption.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite <-Hs2. destruct (beqAddr block1InCurrPartAddr a2) eqn:HbeqBlock1A.
          * rewrite <-DTL.beqAddrTrue in HbeqBlock1A. subst a2. rewrite HnewB. simpl. rewrite HlookupBlock1s1 in *.
            rewrite <-HPflag1s1 in *. simpl in *. rewrite HlookupBlock1s1 in *. rewrite Hs2. simpl.
            rewrite beqAddrTrue. rewrite <-Hs2. rewrite HnewB. simpl. apply Lib.NoDupSplitInclIff.
            apply Lib.NoDupSplitInclIff in HnoDupMappedPs1Rec. apply NoDup_cons_iff in HnoDupKSs1.
            destruct HnoDupMappedPs1Rec as ((_ & HnoDupFiltL) & HdisjointRangeBisL).
            destruct HnoDupKSs1 as (Hblock1NotInL & HnoDupKSs1Rec).
            assert(NoDup (getAllPaddrAux (filterPresent l s4) s2)).
            {
              apply IHl; trivial. intros addr HaddrNotInRange. specialize(HdisjointRangeL addr HaddrNotInRange).
              apply Lib.in_app_or_neg in HdisjointRangeL. apply HdisjointRangeL.
            }
            split; try(split); trivial. apply NoDupPaddrBlock. clear IHl. intros addr HaddrInRange.
            apply getAllPaddrBlockInclRev in HaddrInRange. destruct HaddrInRange as (HlebStartAddr & HltAddrEnd).
            assert(HpropsOrAddr: In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)
              \/ In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)))).
            {
              destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
              - apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. right. apply getAllPaddrBlockIncl; lia.
              - apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. left. apply getAllPaddrBlockIncl; lia.
            }
            assert(HaddrNotInFiltLs1: ~ In addr (getAllPaddrAux (filterPresent l s1) s1)).
            {
              destruct HpropsOrAddr as [HaddrInBlock2 | HaddrInBlock1].
              - specialize(HdisjointRangeL addr HaddrInBlock2). apply Lib.in_app_or_neg in HdisjointRangeL.
                apply HdisjointRangeL.
              - apply HdisjointRangeBisL; assumption.
            }
            assert(HfiltEqs4s1: filterPresent l s4 = filterPresent l s1).
            {
              assert(Heqs3: filterPresent l s4 = filterPresent l s3).
              { rewrite Hs4. apply filterPresentEqBENotInListNoChange; assumption. }
              assert(Heqs2: filterPresent l s4 = filterPresent l s2).
              { rewrite Heqs3. rewrite Hs3. apply filterPresentEqPDT. unfold isPDT. rewrite HlookupCurrs2. trivial. }
              rewrite Heqs2. rewrite Hs2. apply filterPresentEqBENoChange with bentry1; trivial. rewrite HnewB.
              auto.
            }
            rewrite HfiltEqs4s1.
            assert(HallPaddrEq: getAllPaddrAux (filterPresent l s1) s2 = getAllPaddrAux (filterPresent l s1) s1).
            {
              rewrite Hs2. apply getAllPaddrAuxEqBENoInList. apply NotInListNotInFilterPresent; assumption.
            }
            rewrite HallPaddrEq. assumption.
          * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. simpl in *.
            apply NoDup_cons_iff in HnoDupKSs1. destruct HnoDupKSs1 as (Ha2NotInL & HnoDupKSs1Rec).
            destruct (lookup a2 (memory s1) beqAddr) eqn:HlookupA; try(apply IHl; assumption).
            destruct v; try(apply IHl; assumption). destruct (present b0); try(apply IHl; assumption). simpl.
            rewrite Hs2. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock1A. rewrite <-Hs2.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite HlookupA in *. apply Lib.NoDupSplitInclIff. apply Lib.NoDupSplitInclIff in HnoDupMappedPs1Rec.
            destruct HnoDupMappedPs1Rec as ((HnoDupRange & HnoDupFiltL) & HdisjointRangeBisL).
            assert(HnoDupFiltLs2: NoDup (getAllPaddrAux (filterPresent l s4) s2)).
            {
              apply IHl; trivial. intros addr HaddrInRange. specialize(HdisjointRangeL addr HaddrInRange).
              contradict HdisjointRangeL. apply in_or_app. auto.
            }
            split; try(split); trivial. intros addr HaddrInRange. specialize(HdisjointRangeBisL addr HaddrInRange).
            assert(HfiltEqs4s1: filterPresent l s4 = filterPresent l s1).
            {
              assert(Heqs3: filterPresent l s4 = filterPresent l s3).
              { rewrite Hs4. apply filterPresentEqBENotInListNoChange; assumption. }
              assert(Heqs2: filterPresent l s4 = filterPresent l s2).
              { rewrite Heqs3. rewrite Hs3. apply filterPresentEqPDT. unfold isPDT. rewrite HlookupCurrs2. trivial. }
              rewrite Heqs2. rewrite Hs2. apply filterPresentEqBENoChange with bentry1; trivial. rewrite HnewB.
              reflexivity.
            }
            rewrite HfiltEqs4s1. clear HfiltEqs4s1. clear HnoDupKSs1Rec. clear Ha2NotInL. clear Hblock2NotInL.
            assert(HaddrNotInBlock2: ~In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)).
            {
              intro Hcontra. specialize(HdisjointRangeL addr Hcontra). apply HdisjointRangeL. apply in_or_app. auto.
            }
            clear IHl. clear HdisjointRangeL. clear HnoDupFiltLs2. clear HnoDupFiltL.
            induction (filterPresent l s1); simpl in *; try(intro Hcontra; assumption). rewrite Hs2. simpl.
            rewrite <-Hs2. destruct (beqAddr block1InCurrPartAddr a3) eqn:HbeqBlock1A3.
            --- rewrite <-DTL.beqAddrTrue in HbeqBlock1A3. subst a3. rewrite HnewB. simpl.
                rewrite HlookupBlock1s1 in *. apply Lib.in_or_app_neg. apply Lib.in_app_or_neg in HdisjointRangeBisL.
                destruct HdisjointRangeBisL as (HaddrNotInRange & HdisjointRangeBisLRec).
                specialize(IHl6 HdisjointRangeBisLRec). split; trivial. intro Hcontra.
                apply getAllPaddrBlockInclRev in Hcontra. destruct Hcontra as (HlebStartAddr & HltAddrEnd).
                assert(HpropsOrContra: In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)
                  \/ In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)))).
                {
                  destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
                  - apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. right. apply getAllPaddrBlockIncl; lia.
                  - apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. left. apply getAllPaddrBlockIncl; lia.
                }
                destruct HpropsOrContra; congruence.
            --- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                destruct (lookup a3 (memory s1) beqAddr); try(apply IHl6; assumption).
                destruct v; try(apply IHl6; assumption). apply Lib.in_app_or_neg in HdisjointRangeBisL.
                apply Lib.in_or_app_neg. destruct HdisjointRangeBisL as (HaddrNotInRange & HHdisjointRangeBisLRec).
                split; auto.
        + rewrite <-beqAddrFalse in *.
          destruct HpropsOrBlock2 as [HaIsBlock2 | Hblock2InLRec]; try(exfalso; congruence).
          destruct (beqAddr block1InCurrPartAddr a2) eqn:HbeqBlock1A.
          * rewrite <-DTL.beqAddrTrue in HbeqBlock1A. subst a2. rewrite HlookupBlock1Eqss2 in *.
            rewrite HlookupBlock1s2. rewrite HnewB. simpl. unfold bentryPFlag in *. rewrite HlookupBlock1s1 in *.
            rewrite <-HPflag1s1 in *. simpl in *. rewrite HlookupBlock1s1 in *. rewrite HlookupBlock1Eqss2.
            rewrite HlookupBlock1s2. rewrite HnewB. simpl. apply Lib.NoDupSplitInclIff in HnoDupMappedPs1.
            apply Lib.NoDupSplitInclIff. destruct HnoDupMappedPs1 as ((HnoDupRange1 & _) & HdisjointRange1L).
            rewrite HallPaddrEqss4. clear HallPaddrEqss4. clear HfilterEqss4. clear HpropsOrBlock1.
            assert(NoDup (getAllPaddrBlock (startAddr (blockrange bentry1)) block2End)) by (apply NoDupPaddrBlock).
            assert(HallPaddrEqs2s1: getAllPaddrAux (filterPresent l s4) s2 = getAllPaddrAux (filterPresent l s4) s1).
            { rewrite Hs2. apply getAllPaddrAuxEqBENoInList. apply NotInListNotInFilterPresent; assumption. }
            rewrite HallPaddrEqs2s1. clear HallPaddrEqs2s1.
            assert(HfiltEqs3s1: filterPresent l s3 = filterPresent l s1).
            {
              assert(Heqs2: filterPresent l s3 = filterPresent l s2).
              { rewrite Hs3. apply filterPresentEqPDT. unfold isPDT. rewrite HlookupCurrs2. trivial. }
              rewrite Heqs2. rewrite Hs2. apply filterPresentEqBENoChange with bentry1; trivial. rewrite HnewB. auto.
            }
            rewrite <-HfiltEqs3s1 in *. clear HfiltEqs3s1. clear IHl. clear HmappedIsPresRec. clear HmappedIsPres.
            assert(Hdisjoint: Lib.disjoint (getAllPaddrBlock (startAddr (blockrange bentry1)) block2End)
              (getAllPaddrAux (filterPresent l s4) s1)).
            {
              intros addr HaddrInRangeGlob. assert(HpropsOr:
                In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)))
                \/ In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)).
              {
                apply getAllPaddrBlockInclRev in HaddrInRangeGlob.
                destruct HaddrInRangeGlob as (HlebStart1Addr & HltAddrEnd2 & _).
                destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
                - apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. left. apply getAllPaddrBlockIncl; lia.
                - apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. right. apply getAllPaddrBlockIncl; lia.
              }
              destruct HpropsOr as [HaddrIn1 | HaddrIn2].
              - specialize(HdisjointRange1L addr HaddrIn1). contradict HdisjointRange1L. clear HnoDupKSs1.
                clear Ha2NotInL. clear HnoDupMappedPs1Rec. clear Hblock2InLRec.
                induction l; simpl in *; try(congruence). rewrite Hs4 in HdisjointRange1L. simpl in *.
                rewrite <-Hs4 in *. destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A2.
                + rewrite <-DTL.beqAddrTrue in HbeqBlock2A2. subst a2. rewrite HlookupBlock1Eqs3s1.
                  destruct (lookup block2InCurrPartAddr (memory s1) beqAddr) eqn:Hlookup2; try(exfalso; congruence).
                  destruct v; try(exfalso; congruence). rewrite <-HPflag2s1. simpl. rewrite Hlookup2.
                  apply in_or_app. right. rewrite HnewB2 in HdisjointRange1L. simpl in *. apply IHl; assumption.
                + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                  destruct (lookup a2 (memory s3) beqAddr); try(apply IHl; assumption).
                  destruct v; try(apply IHl; assumption). destruct (present b); try(apply IHl; assumption).
                  simpl in *. destruct (lookup a2 (memory s1) beqAddr); try(apply IHl; assumption).
                  destruct v; try(apply IHl; assumption). apply in_or_app. apply in_app_or in HdisjointRange1L.
                  destruct HdisjointRange1L as [HaddrInA | HdisjointRange1LRec]; auto.
              - clear HdisjointRange1L. clear HnoDupKSs1.
                induction l; simpl in *; try(congruence). apply Decidable.not_or in Ha2NotInL.
                destruct Ha2NotInL as (HbeqA2Block1 & Hblock1NotInLRec). rewrite Hs4. simpl. rewrite <-Hs4.
                assert(HnoDupLRec: NoDup (getAllPaddrAux (filterPresent l s3) s1)).
                {
                  destruct (lookup a2 (memory s3) beqAddr); try(assumption). destruct v; try(assumption).
                  destruct (present b); try(assumption). simpl in *.
                  destruct (lookup a2 (memory s1) beqAddr); try(assumption). destruct v; try(assumption).
                  apply Lib.NoDupSplitInclIff in HnoDupMappedPs1Rec. apply HnoDupMappedPs1Rec.
                }
                destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A2.
                + rewrite <-DTL.beqAddrTrue in HbeqBlock2A2. subst a2. rewrite HnewB2. simpl.
                  rewrite HlookupBlock1Eqs3s1 in *. unfold bentryEndAddr in *. unfold bentryStartAddr in *.
                  rewrite HlookupBlock2Eqs1s0 in *.
                  destruct (lookup block2InCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlock2;
                    try(exfalso; congruence). destruct v; try(exfalso; congruence). rewrite <-HPflag2s0 in *.
                  simpl in *. rewrite HlookupBlock2Eqs1s0 in *. rewrite <-Hend2s0 in *. rewrite <-Hstart2s0 in *.
                  apply Lib.NoDupSplitInclIff in HnoDupMappedPs1Rec.
                  destruct HnoDupMappedPs1Rec as (_ & HdisjointRangeLRec). apply HdisjointRangeLRec in HaddrIn2.
                  clear Hblock1NotInLRec. clear HnoDupLRec. clear Hblock2InLRec. clear HdisjointRangeLRec.
                  clear IHl. contradict HaddrIn2. induction l; simpl in *; try(congruence). rewrite Hs4 in HaddrIn2.
                  simpl in *. rewrite <-Hs4 in *. destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A2.
                  * rewrite HnewB2 in HaddrIn2. simpl in *. rewrite <-DTL.beqAddrTrue in HbeqBlock2A2. subst a2.
                    rewrite HlookupBlock1Eqs3s1. rewrite <-HPflag2s0. simpl. rewrite HlookupBlock2Eqs1s0.
                    apply in_or_app. right. apply IHl; assumption.
                  * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                    destruct (lookup a2 (memory s3) beqAddr); try(apply IHl; assumption).
                    destruct v; try(apply IHl; assumption). destruct (present b0); try(apply IHl; assumption).
                    simpl in *. destruct (lookup a2 (memory s1) beqAddr); try(apply IHl; assumption).
                    destruct v; try(apply IHl; assumption). apply in_or_app. apply in_app_or in HaddrIn2.
                    destruct HaddrIn2 as [HaddrInA | HaddrInLRec]; auto.
                + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  destruct (lookup a2 (memory s3) beqAddr); try(apply IHl; assumption).
                  destruct v; try(apply IHl; assumption). destruct (present b); try(apply IHl; assumption).
                  simpl in *. destruct Hblock2InLRec as [Hcontra | Hblock2InLRec]; try(exfalso; congruence).
                  destruct (lookup a2 (memory s1) beqAddr); try(apply IHl; assumption).
                  destruct v; try(apply IHl; assumption). apply Lib.in_or_app_neg. split; try(apply IHl; assumption).
                  apply Lib.NoDupSplitInclIff in HnoDupMappedPs1Rec.
                  destruct HnoDupMappedPs1Rec as (_ & HdisjointRangeBisLRec). intro Hcontra.
                  apply HdisjointRangeBisLRec in Hcontra. contradict Hcontra.
                  apply blockIsMappedAddrInPaddrList with block2InCurrPartAddr; trivial. simpl.
                  unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlock2Eqs1s0 in *.
                  destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite <-Hend2s0. rewrite <-Hstart2s0. rewrite app_nil_r.
                  assumption.
            }
            split; try(split); trivial. clear HnoDupKSs1. clear Hblock2InLRec. clear HdisjointRange1L.
            clear Ha2NotInL. clear Hdisjoint. induction l; simpl in *; try(apply NoDup_nil). rewrite Hs4. simpl.
            rewrite <-Hs4. destruct (beqAddr block2InCurrPartAddr a2) eqn:HbeqBlock2A2.
            --- rewrite <-DTL.beqAddrTrue in HbeqBlock2A2. subst a2. rewrite HnewB2. simpl.
                rewrite HlookupBlock1Eqs3s1 in *.
                destruct (lookup block2InCurrPartAddr (memory s1) beqAddr) eqn:Hlookup2; try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HPflag2s1 in *. simpl in *. rewrite Hlookup2 in *.
                apply Lib.NoDupSplitInclIff in HnoDupMappedPs1Rec. destruct HnoDupMappedPs1Rec as ((_ & HnoDup) & _).
                apply IHl; assumption.
            --- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                destruct (lookup a2 (memory s3) beqAddr); try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). destruct (present b); try(apply IHl; assumption).
                simpl in *. destruct (lookup a2 (memory s1) beqAddr); try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplitInclIff in HnoDupMappedPs1Rec.
                apply Lib.NoDupSplitInclIff. destruct HnoDupMappedPs1Rec as ((HnoDupRange & HnoDup) & Hdisjoint).
                split; try(split); auto. intros addr HaddrInA. apply Hdisjoint in HaddrInA. contradict HaddrInA.
                clear HnoDup. clear IHl. clear Hdisjoint. induction l; simpl in *; try(congruence).
                rewrite Hs4 in HaddrInA. simpl in *. rewrite <-Hs4 in *.
                destruct (beqAddr block2InCurrPartAddr a3) eqn:HbeqBlock2A3.
                +++ rewrite <-DTL.beqAddrTrue in HbeqBlock2A3. subst a3. rewrite HnewB2 in HaddrInA. simpl in *.
                    rewrite HlookupBlock1Eqs3s1.
                    destruct (lookup block2InCurrPartAddr (memory s1) beqAddr) eqn:Hlookup2; try(exfalso; congruence).
                    destruct v; try(exfalso; congruence). rewrite <-HPflag2s1. simpl. rewrite Hlookup2.
                    apply in_or_app. right. apply IHl; assumption.
                +++ rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                    destruct (lookup a3 (memory s3) beqAddr); try(apply IHl; assumption).
                    destruct v; try(apply IHl; assumption). destruct (present b1); try(apply IHl; assumption).
                    simpl in *. destruct (lookup a3 (memory s1) beqAddr); try(apply IHl; assumption).
                    destruct v; try(apply IHl; assumption). apply in_or_app. apply in_app_or in HaddrInA.
                    destruct HaddrInA as [HaddrInA3 | HaddrInARec]; auto.
          * rewrite <-beqAddrFalse in *.
            destruct HpropsOrBlock1 as [Hcontra | Hblock1InLRec]; try(exfalso; congruence).
            specialize(IHl HnoDupMappedPs1Rec Hblock2InLRec Hblock1InLRec HmappedIsPresRec HnoDupKSs1).
            destruct (lookup a2 (memory s) beqAddr) eqn:HlookupA; try(rewrite HallPaddrEqss4; trivial).
            destruct v; try(rewrite HallPaddrEqss4; trivial).
            destruct (present b) eqn:Hpres; try(rewrite HallPaddrEqss4; trivial). simpl in *. rewrite HlookupA.
            apply Lib.NoDupSplitInclIff. rewrite HallPaddrEqss4.
            assert(HpropsA: a2 = a2 \/ In a2 (filterPresent l s4)) by (auto). specialize(HmappedIsPres a2 HpropsA).
            assert(NoDup (getAllPaddrBlock (startAddr (blockrange b)) (endAddr (blockrange b))))
              by (apply NoDupPaddrBlock). split; try(split); trivial.
            unfold bentryPFlag in *. rewrite Hs in HmappedIsPres.
            rewrite Hs8 in HmappedIsPres. rewrite Hs in HlookupA. rewrite Hs8 in HlookupA. simpl in *.
            destruct (beqAddr currentPart a2) eqn:HbeqCurrA; try(exfalso; congruence). rewrite beqAddrTrue in *.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HmappedIsPres.
            rewrite Hs7 in HlookupA. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2A in *.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite Hs6 in HmappedIsPres. rewrite Hs6 in HlookupA. simpl in *.
            destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) a2) eqn:HbeqSceA; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite Hs5 in HmappedIsPres. rewrite Hs5 in HlookupA. simpl in *.
            destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) a2) eqn:HbeqSh1A; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite Hs4 in HmappedIsPres. rewrite Hs4 in HlookupA. simpl in *. rewrite beqAddrFalse in *.
            rewrite HbeqBlock2A in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HmappedIsPres.
            rewrite Hs3 in HlookupA. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrA in *.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite Hs2 in HmappedIsPres. rewrite Hs2 in HlookupA. simpl in *. rewrite beqAddrFalse in *.
            rewrite HbeqBlock1A in *.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite HlookupA in *. rewrite <-HmappedIsPres in *. simpl in *. rewrite HlookupA in *.
            apply Lib.NoDupSplitInclIff in HnoDupMappedPs1.
            destruct HnoDupMappedPs1 as ((HnoDupRange & HnoDupFiltL) & HdisjointRangeL). intros addr HaddrInRange.
            specialize(HdisjointRangeL addr HaddrInRange).
            assert(HfiltEqs3s1: filterPresent l s3 = filterPresent l s1).
            {
              assert(Heqs2: filterPresent l s3 = filterPresent l s2).
              { rewrite Hs3. apply filterPresentEqPDT. unfold isPDT. rewrite HlookupCurrs2. trivial. }
              rewrite Heqs2. rewrite Hs2. apply filterPresentEqBENoChange with bentry1; trivial. rewrite HnewB.
              reflexivity.
            }
            rewrite <-HfiltEqs3s1 in *. clear HfiltEqs3s1. clear HnoDupKSs1. clear Ha2NotInL. clear HnoDupFiltL.
            clear IHl. clear HnoDupMappedPs1Rec. clear HfilterEqss4. clear HpropsA. clear HallPaddrEqss4.
            clear HmappedIsPresRec. contradict HdisjointRangeL. induction l; simpl in *; try(congruence).
            rewrite Hs4 in HdisjointRangeL. simpl in *. rewrite <-Hs4 in *.
            destruct (beqAddr block2InCurrPartAddr a3) eqn:HbeqBlock2A3.
            --- rewrite <-DTL.beqAddrTrue in HbeqBlock2A3. subst a3. rewrite HnewB2 in HdisjointRangeL.
                simpl in *. rewrite HlookupBlock1Eqs3s1 in *. unfold bentryStartAddr in *.
                unfold bentryEndAddr in *. rewrite HlookupBlock2Eqs1s0 in *.
                destruct (lookup block2InCurrPartAddr (memory s0) beqAddr) eqn:HlookupB2;
                  try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HPflag2s1 in *. simpl in *.
                rewrite HlookupBlock2Eqs1s0 in *. rewrite <-Hend2s0. rewrite <-Hstart2s0. apply in_or_app.
                destruct Hblock1InLRec as [Hcontra | Hblock1InLRec]; try(exfalso; congruence). clear IHl.
                clear Hblock2InLRec. induction l; simpl in *; try(exfalso; congruence).
                rewrite Hs4 in HdisjointRangeL. simpl in *. rewrite <-Hs4 in *.
                destruct (beqAddr block2InCurrPartAddr a3) eqn:HbeqBlock2A3.
                +++ rewrite <-DTL.beqAddrTrue in HbeqBlock2A3. subst a3. rewrite HnewB2 in HdisjointRangeL.
                    simpl in *. rewrite HlookupBlock1Eqs3s1 in *. rewrite <-HPflag2s1 in *. simpl in *.
                    rewrite HlookupBlock2Eqs1s0.
                    destruct Hblock1InLRec as [Hcontra | Hblock1InLRec]; try(exfalso; congruence).
                    specialize(IHl Hblock1InLRec HdisjointRangeL).
                    destruct IHl as [HaddrInRange2 | IHl]; auto. right. apply in_or_app. auto.
                +++ rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                    destruct (lookup a3 (memory s3) beqAddr); try(apply IHl; assumption).
                    destruct v; try(apply IHl; assumption). destruct (present b1); try(apply IHl; assumption).
                    simpl in *. rewrite Hs2 in HdisjointRangeL. simpl in *. rewrite <-Hs2 in *.
                    destruct (beqAddr block1InCurrPartAddr a3) eqn:HbeqBlock1A3.
                    *** rewrite <-DTL.beqAddrTrue in HbeqBlock1A3. subst a3. rewrite HlookupBlock1s1.
                        rewrite HnewB in HdisjointRangeL. simpl in *. apply in_app_or in HdisjointRangeL.
                        assert(HpropsOrRange: In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)
                          \/ ~In addr (getAllPaddrBlock (endAddr (blockrange bentry1)) block2End)).
                        { apply Classical_Prop.classic. }
                        destruct HpropsOrRange as [HaddrInRange2 | HaddrNotInRange2]; auto. right. apply in_or_app.
                        destruct HdisjointRangeL as [HaddrInRangeFull | HaddrInLRec].
                        ----- left. apply getAllPaddrBlockInclRev in HaddrInRangeFull.
                              destruct HaddrInRangeFull as (HlebStartAddr & HltAddrEnd2 & _).
                              destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
                              +++++ apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. apply getAllPaddrBlockIncl; lia.
                              +++++ apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. contradict HaddrNotInRange2.
                                    apply getAllPaddrBlockIncl; lia.
                        ----- clear Hblock1InLRec. clear IHl. induction l; simpl in *; try(exfalso; congruence).
                              rewrite Hs4 in HaddrInLRec. simpl in *. rewrite <-Hs4 in *.
                              destruct (beqAddr block2InCurrPartAddr a3) eqn:HbeqBlock2A3Bis.
                              +++++ rewrite <-DTL.beqAddrTrue in HbeqBlock2A3Bis. subst a3.
                                    rewrite HlookupBlock1Eqs3s1. rewrite HnewB2 in HaddrInLRec. simpl in *.
                                    rewrite <-HPflag2s1. simpl. rewrite HlookupBlock2Eqs1s0.
                                    specialize(IHl HaddrInLRec).
                                    destruct IHl as [HaddrInRange1 | HaddrInLRecs3]; auto. right. apply in_or_app.
                                    auto.
                              +++++ rewrite <-beqAddrFalse in *.
                                    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                                    destruct (lookup a3 (memory s3) beqAddr); try(apply IHl; assumption).
                                    destruct v; try(apply IHl; assumption).
                                    destruct (present b2); try(apply IHl; assumption). simpl in *.
                                    rewrite Hs2 in HaddrInLRec. simpl in *. rewrite <-Hs2 in *.
                                    destruct (beqAddr block1InCurrPartAddr a3) eqn:HbeqBlock1A3.
                                    ***** rewrite <-DTL.beqAddrTrue in HbeqBlock1A3. subst a3.
                                          rewrite HlookupBlock1s1. rewrite HnewB in HaddrInLRec. simpl in *.
                                          apply in_app_or in HaddrInLRec.
                                          destruct HaddrInLRec as [HaddrInRangeFull | HaddrInLRec].
                                          ------- left. apply getAllPaddrBlockInclRev in HaddrInRangeFull.
                                                  destruct HaddrInRangeFull as (HlebStartAddr & HltAddrEnd2 & _).
                                                  destruct (Nat.ltb addr (endAddr (blockrange bentry1)))
                                                      eqn:HltAddrEnd1.
                                                  +++++++ apply PeanoNat.Nat.ltb_lt in HltAddrEnd1.
                                                          apply getAllPaddrBlockIncl; lia.
                                                  +++++++ apply PeanoNat.Nat.ltb_ge in HltAddrEnd1.
                                                          contradict HaddrNotInRange2.
                                                          apply getAllPaddrBlockIncl; lia.
                                          ------- specialize(IHl HaddrInLRec). destruct IHl as [Hleft | IHl]; auto.
                                                  right. apply in_or_app. auto.
                                    ***** rewrite <-beqAddrFalse in *.
                                          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                                          destruct (lookup a3 (memory s1) beqAddr); auto. destruct v; auto.
                                          apply in_app_or in HaddrInLRec.
                                          destruct HaddrInLRec as [Hleft | HaddrInLRec].
                                          ------- right. apply in_or_app. auto.
                                          ------- specialize(IHl HaddrInLRec). destruct IHl as [Hleft | IHl]; auto.
                                                  right. apply in_or_app. auto.
                    *** rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                        destruct Hblock1InLRec as [Hcontra | Hblock1InLRec]; try(exfalso; congruence).
                        destruct (lookup a3 (memory s1) beqAddr); try(apply IHl; assumption).
                        destruct v; try(apply IHl; assumption). apply in_app_or in HdisjointRangeL.
                        destruct HdisjointRangeL as [Hleft | HaddrInLRec].
                        ----- right. apply in_or_app. auto.
                        ----- specialize(IHl Hblock1InLRec HaddrInLRec). destruct IHl as [Hleft | IHl]; auto.
                              right. apply in_or_app. auto.
            --- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                destruct (lookup a3 (memory s3) beqAddr); try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). destruct (present b0); try(apply IHl; assumption). simpl in *.
                rewrite Hs2 in HdisjointRangeL. simpl in *. rewrite <-Hs2 in *.
                destruct (beqAddr block1InCurrPartAddr a3) eqn:HbeqBlock1A3.
                +++ rewrite <-DTL.beqAddrTrue in HbeqBlock1A3. subst a3. rewrite HlookupBlock1s1.
                    rewrite HnewB in HdisjointRangeL. simpl in *. apply in_app_or in HdisjointRangeL.
                    destruct Hblock2InLRec as [Hcontra | Hblock2InLRec]; try(exfalso; congruence). apply in_or_app.
                    clear Hblock1InLRec. clear IHl.
                    assert(HpropsOrRange:
                      In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)))
                      \/ ~In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1)))).
                    { apply Classical_Prop.classic. }
                    destruct HpropsOrRange as [HaddrInBlock1 | HaddrNotInBlock1]; auto. right.
                    destruct HdisjointRangeL as [HaddrInBlockFull | HaddrInLRec].
                    *** apply blockIsMappedAddrInPaddrList with block2InCurrPartAddr; trivial. simpl.
                        unfold bentryStartAddr in *. rewrite HlookupBlock2Eqs1s0 in *. unfold bentryEndAddr in *.
                        destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
                        destruct v; try(exfalso; congruence). rewrite <-Hend2s0. rewrite <-Hstart2s0.
                        rewrite app_nil_r. apply getAllPaddrBlockInclRev in HaddrInBlockFull.
                        destruct HaddrInBlockFull as (HlebStartAddr & HltAddrEnd2 & _).
                        destruct (Nat.ltb addr (endAddr (blockrange bentry1)))
                            eqn:HltAddrEnd1.
                        ----- apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. contradict HaddrNotInBlock1.
                              apply getAllPaddrBlockIncl; lia.
                        ----- apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. apply getAllPaddrBlockIncl; lia.
                    *** induction l; simpl in *; try(congruence). rewrite Hs4 in HaddrInLRec. simpl in *.
                        rewrite <-Hs4 in *.
                        destruct (beqAddr block2InCurrPartAddr a3) eqn:HbeqBlock2A3Bis.
                        ----- rewrite <-DTL.beqAddrTrue in HbeqBlock2A3Bis. subst a3. rewrite HnewB2 in HaddrInLRec.
                              simpl in *. rewrite HlookupBlock1Eqs3s1 in *. unfold bentryStartAddr in *.
                              rewrite HlookupBlock2Eqs1s0 in *. unfold bentryEndAddr in *.
                              destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); auto. destruct v; auto.
                              rewrite <-HPflag2s0 in *. simpl in *. rewrite HlookupBlock2Eqs1s0. clear IHl.
                              clear Hblock2InLRec. rewrite <-Hend2s0. rewrite <-Hstart2s0. apply in_or_app.
                              induction l; simpl in *; try(exfalso; congruence). rewrite Hs4 in HaddrInLRec.
                              simpl in *. rewrite <-Hs4 in *.
                              destruct (beqAddr block2InCurrPartAddr a3) eqn:HbeqBlock2A3Bis.
                              +++++ rewrite <-DTL.beqAddrTrue in HbeqBlock2A3Bis. subst a3.
                                    rewrite HlookupBlock1Eqs3s1. rewrite <-HPflag2s0. rewrite HnewB2 in HaddrInLRec.
                                    simpl in *. rewrite HlookupBlock2Eqs1s0. rewrite <-Hend2s0. rewrite <-Hstart2s0.
                                    right. apply in_or_app. auto.
                              +++++ rewrite <-beqAddrFalse in *.
                                    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                                    destruct (lookup a3 (memory s3) beqAddr); auto. destruct v; auto.
                                    destruct (present b2); auto. simpl in *. rewrite Hs2 in HaddrInLRec. simpl in *.
                                    rewrite <-Hs2 in *. destruct (beqAddr block1InCurrPartAddr a3) eqn:HbeqBlock1A3.
                                    ***** rewrite <-DTL.beqAddrTrue in HbeqBlock1A3. subst a3.
                                          rewrite HlookupBlock1s1. rewrite HnewB in HaddrInLRec. simpl in *.
                                          apply in_app_or in HaddrInLRec.
                                          destruct HaddrInLRec as [HaddrInRangeFull | HaddrInLRec].
                                          ------- apply getAllPaddrBlockInclRev in HaddrInRangeFull.
                                                  destruct HaddrInRangeFull as (HlebStartAddr & HltAddrEnd2 & _).
                                                  destruct (Nat.ltb addr (endAddr (blockrange bentry1)))
                                                    eqn:HltAddrEnd1.
                                                  +++++++ apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. right.
                                                          apply in_or_app. left. apply getAllPaddrBlockIncl; lia.
                                                  +++++++ apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. left.
                                                          apply getAllPaddrBlockIncl; lia.
                                          ------- specialize(IHl HaddrInLRec). destruct IHl as [Hleft | IHl]; auto.
                                                  right. apply in_or_app. auto.
                                    ***** rewrite <-beqAddrFalse in *.
                                          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                                          destruct (lookup a3 (memory s1) beqAddr); auto. destruct v; auto.
                                          apply in_app_or in HaddrInLRec.
                                          destruct HaddrInLRec as [Hleft | HaddrInLRec];
                                            try(right; apply in_or_app; left; assumption).
                                          specialize(IHl HaddrInLRec). destruct IHl as [Hleft | IHl]; auto. right.
                                          apply in_or_app. auto.
                        ----- rewrite <-beqAddrFalse in *.
                              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                              destruct (lookup a3 (memory s3) beqAddr); try(apply IHl; assumption).
                              destruct v; try(apply IHl; assumption).
                              destruct (present b1); try(apply IHl; assumption). simpl in *.
                              rewrite Hs2 in HaddrInLRec. simpl in *. rewrite <-Hs2 in *.
                              destruct (beqAddr block1InCurrPartAddr a3) eqn:HbeqBlock1A3.
                              +++++ rewrite <-DTL.beqAddrTrue in HbeqBlock1A3. subst a3. rewrite HlookupBlock1s1.
                                    rewrite HnewB in HaddrInLRec. simpl in *. apply in_app_or in HaddrInLRec.
                                    apply in_or_app.
                                    destruct Hblock2InLRec as [Hcontra | Hblock2InLRec]; try(exfalso; congruence).
                                    destruct HaddrInLRec as [HaddrInRangeFull | HaddrInLRec]; auto. right.
                                    apply blockIsMappedAddrInPaddrList with block2InCurrPartAddr; trivial. simpl.
                                    unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                                    rewrite HlookupBlock2Eqs1s0.
                                    destruct (lookup block2InCurrPartAddr (memory s0) beqAddr);
                                      try(simpl; congruence). destruct v; try(simpl; congruence). rewrite app_nil_r.
                                    rewrite <-Hend2s0. rewrite <-Hstart2s0.
                                    apply getAllPaddrBlockInclRev in HaddrInRangeFull.
                                    destruct HaddrInRangeFull as (HlebStartAddr & HltAddrEnd2 & _).
                                    destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
                                    ***** apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. contradict HaddrNotInBlock1.
                                          apply getAllPaddrBlockIncl; lia.
                                    ***** apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. apply getAllPaddrBlockIncl; lia.
                              +++++ rewrite <-beqAddrFalse in *.
                                    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                                    destruct Hblock2InLRec as [Hcontra | Hblock2InLRec]; try(exfalso; congruence).
                                    destruct (lookup a3 (memory s1) beqAddr); try(apply IHl; assumption).
                                    destruct v; try(apply IHl; assumption). apply in_app_or in HaddrInLRec.
                                    apply in_or_app. destruct HaddrInLRec as [Hleft | HaddrInLRec]; auto.
                +++ rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                    destruct Hblock1InLRec as [Hcontra | Hblock1InLRec]; try(exfalso; congruence).
                    destruct Hblock2InLRec as [Hcontra | Hblock2InLRec]; try(exfalso; congruence).
                    destruct (lookup a3 (memory s1) beqAddr); auto. destruct v; auto. apply in_or_app.
                    apply in_app_or in HdisjointRangeL. destruct HdisjointRangeL as [Hleft | HdisjointRangeL]; auto.
      - rewrite <-beqAddrFalse in *. rewrite HgetMappedPNotCurrEqss1; assumption.
      (* END noDupMappedPaddrList *)
    }

    assert(accessibleParentPaddrIsAccessibleIntoChild s).
    { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
      intros pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
      assert(isPDT pdparent s) by (apply partitionsArePDT; unfold cons1Free in *; intuition).
      assert(isPDT child s) by (apply childrenArePDT with pdparent; unfold cons1Free in *; intuition).
      rewrite HgetPartsEqss2 in *.
      assert(isPDT pdparent s3) by (rewrite <-HgetPartsEqs3s2 in *; apply partitionsArePDT; intuition).
      rewrite HgetChildrenEqss2 in *; trivial. rewrite HgetPartsEqs2s1 in *.
      assert(isPDT pdparent s1) by (apply partitionsArePDT; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEqs2s1 in *; trivial.
      assert(HaddrAccMappedParents1: In addr (getAccessibleMappedPaddr pdparent s1)).
      {
        destruct (beqAddr currentPart pdparent) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. rewrite HbeqParts in *. apply HgetAccMappedPCurrEqss1; trivial.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetAccMappedPNotCurrEqss1; assumption.
      }
      assert(HaddrMappedChilds1: In addr (getMappedPaddr child s1)).
      {
        destruct (beqAddr currentPart child) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. rewrite HbeqParts in *. apply HgetMappedPCurrEqss1; trivial.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedPNotCurrEqss1; assumption.
      }
      specialize(Haccesss1 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParents1 HaddrMappedChilds1).
      destruct (beqAddr currentPart child) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. rewrite HbeqParts in *. apply HgetAccMappedPCurrEqss1; trivial.
      - rewrite <-beqAddrFalse in *. rewrite HgetAccMappedPNotCurrEqss1; assumption.
      (* END accessibleParentPaddrIsAccessibleIntoChild *)
    }

    assert(sharedBlockPointsToChild s).
    { (* BEGIN sharedBlockPointsToChild s *)
      intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParent HblockParentMapped Hsh1.
      assert(isPDT pdparent s) by (apply partitionsArePDT; unfold cons1Free in *; intuition).
      rewrite HgetPartsEqss2 in *.
      assert(isPDT child s) by (apply childrenArePDT with pdparent; unfold cons1Free in *; intuition).
      assert(isPDT pdparent s3) by (rewrite <-HgetPartsEqs3s2 in *; apply partitionsArePDT; intuition).
      rewrite HgetChildrenEqss2 in *; trivial. rewrite HgetPartsEqs2s1 in *.
      assert(HparentIsPDTs1: isPDT pdparent s1) by (apply partitionsArePDT; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEqs2s1 in *; trivial.
      assert(HaddrUsedChilds1: In addr (getUsedPaddr child s1)).
      {
        unfold getUsedPaddr in *. rewrite HgetConfigPEq in *; trivial.
        destruct (beqAddr currentPart child) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. rewrite HbeqParts in *. apply in_app_or in HaddrUsedChild.
          apply in_or_app. destruct HaddrUsedChild as [Hconfig | Hmapped]; auto. right.
          apply HgetMappedPCurrEqss1; trivial.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedPNotCurrEqss1; assumption.
      }
      assert(HblockParentMappeds1: In blockParent (getMappedBlocks pdparent s1)).
      {
        rewrite <-HgetMappedBEqs2s1. destruct (beqAddr currentPart pdparent) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. rewrite HbeqParts in *.
          specialize(HgetMappedBCurrEqss2 blockParent). destruct HgetMappedBCurrEqss2 as (_ & Hress2 & _).
          apply Hress2 in HblockParentMapped. assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial. unfold isPDT in *. rewrite Hs4.
          simpl. unfold isBE in *. destruct (beqAddr block2InCurrPartAddr pdparent) eqn:HbeqBlock2Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. rewrite HbeqBlock2Parent in *.
            destruct (lookup pdparent (memory s1) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      destruct (beqAddr block2InCurrPartAddr blockParent) eqn:HbeqBlock2BlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlock2BlockP. subst blockParent. apply mappedBlockIsBE in HblockParentMapped.
        rewrite HlookupBlock2Eqss7 in *. destruct HblockParentMapped as [bentry (Hlookup2s7 & Hpres)].
        rewrite Hs7 in Hlookup2s7. simpl in *. rewrite beqAddrTrue in *. injection Hlookup2s7 as HbentriesEq.
        subst bentry. rewrite HnewB3 in Hpres. simpl in *. rewrite HnewB2 in Hpres. simpl in *. exfalso; congruence.
      }
      assert(HlookupEqss2: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s2) beqAddr).
      {
        unfold sh1entryAddr in *. rewrite Hs in Hsh1. rewrite Hs8 in Hsh1. rewrite Hs. rewrite Hs8. simpl in *.
        destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in Hsh1. rewrite Hs7. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2BlockP in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6 in Hsh1. rewrite Hs6. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce2BlockP;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in Hsh1. rewrite Hs5. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh12BlockP;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in Hsh1. rewrite Hs4. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2BlockP in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hsh1. rewrite Hs3. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqCurrBlockP in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(Hsh1s1: sh1entryAddr blockParent sh1entryaddr s1).
      {
        unfold sh1entryAddr in *. rewrite HlookupEqss2 in Hsh1. rewrite Hs2 in Hsh1. simpl in *.
        destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1BlockP.
        - rewrite <-DTL.beqAddrTrue in HbeqBlock1BlockP. rewrite HbeqBlock1BlockP in *. rewrite HlookupBlock1s1.
          trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1BlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlock1BlockP. subst blockParent. simpl in *. rewrite HlookupBlock1Eqss2 in *.
        rewrite Hs2 in HaddrInBlockParent. simpl in *. rewrite beqAddrTrue in *. rewrite HnewB in HaddrInBlockParent.
        simpl in *. rewrite app_nil_r in *.
        assert(HpropsOrAddr: In addr (getAllPaddrAux [block1InCurrPartAddr] s1)
          \/ In addr (getAllPaddrAux [block2InCurrPartAddr] s1)).
        {
          apply getAllPaddrBlockInclRev in HaddrInBlockParent. simpl. rewrite HlookupBlock1s1.
          destruct HaddrInBlockParent as (HlebStart1Addr & HltAddrEnd2 & _). rewrite HlookupBlock2Eqs1s0.
          unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-Hend2s0. rewrite <-Hstart2s0. rewrite app_nil_r.
          rewrite app_nil_r. destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
          - left. apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. apply getAllPaddrBlockIncl; lia.
          - right. apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. apply getAllPaddrBlockIncl; lia.
        }
        exfalso. destruct HpropsOrAddr as [HaddrInBlock1 | HaddrInBlock2].
        - specialize(Hshareds1 pdparent child addr block1InCurrPartAddr sh1entryaddr1 HparentIsPart HchildIsChild
            HaddrUsedChilds1 HaddrInBlock1 HblockParentMappeds1 Hsh11s1).
          destruct Hshareds1 as [HcontraPDchild | HcontraPDflag].
          + unfold sh1entryAddr in *. rewrite HlookupBlock1s1 in *. subst sh1entryaddr1. unfold sh1entryPDchild in *.
            rewrite Hs1 in HcontraPDchild. simpl in *.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (CPaddr (block1InCurrPartAddr + sh1offset)))
              eqn:HbeqSceSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            destruct (lookup (CPaddr (block1InCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HPDchild1s0 in *. subst child.
            assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
            assert(isPDT nullAddr s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
            unfold isPDT in *. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence).
            destruct v; congruence.
          + assert(HnoPDs1: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
            assert(Hblock1IsBEs1: isBE block1InCurrPartAddr s1) by (unfold isBE; rewrite HlookupBlock1s1; trivial).
            specialize(HnoPDs1 block1InCurrPartAddr sh1entryaddr1 Hblock1IsBEs1 Hsh11s1 HAflag1s1).
            unfold sh1entryAddr in *. rewrite HlookupBlock1s1 in *. subst sh1entryaddr1. unfold sh1entryPDflag in *.
            destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s1) beqAddr); try(congruence).
            destruct v; congruence.
        - assert(Hblock2MappedParents1: In block2InCurrPartAddr (getMappedBlocks pdparent s1)).
          {
            unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock1Mappeds1.
            apply InFilterPresentInList in HblockParentMappeds1.
            assert(HdisjointKSs1: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
            destruct (beqAddr currentPart pdparent) eqn:HbeqParts.
            - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. assumption.
            - rewrite <-beqAddrFalse in *. 
              specialize(HdisjointKSs1 currentPart pdparent HcurrIsPDTs1 HparentIsPDTs1 HbeqParts).
              destruct HdisjointKSs1 as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
              specialize(Hdisjoint block1InCurrPartAddr Hblock1Mappeds1). exfalso; congruence.
          }
          specialize(Hshareds1 pdparent child addr block2InCurrPartAddr sh1entryaddr2 HparentIsPart HchildIsChild
            HaddrUsedChilds1 HaddrInBlock2 Hblock2MappedParents1 Hsh12s1).
          exfalso. destruct Hshareds1 as [HcontraPDchild | HcontraPDflag].
          + unfold sh1entryAddr in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlock2s0; try(congruence).
            destruct v; try(congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block2InCurrPartAddr+sh1offset)) (memory s1) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HPDchild2s1 in *. subst child.
            assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
            assert(isPDT nullAddr s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
            unfold isPDT in *. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence).
            destruct v; congruence.
          + assert(HnoPDs1: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
            specialize(HnoPDs1 block2InCurrPartAddr sh1entryaddr2 Hblock2IsBEs1 Hsh12s1 HAflag2s1).
            unfold sh1entryAddr in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlock2s0; try(congruence).
            destruct v; try(congruence). subst sh1entryaddr2. unfold sh1entryPDflag in *.
            destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s1) beqAddr); try(congruence).
            destruct v; congruence.
      }
      assert(HaddrInBlockParents1: In addr (getAllPaddrAux [blockParent] s1)).
      {
        simpl in *. rewrite HlookupEqss2 in HaddrInBlockParent. rewrite Hs2 in HaddrInBlockParent. simpl in *.
        rewrite HbeqBlock1BlockP in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hshareds1 pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChilds1
        HaddrInBlockParents1 HblockParentMappeds1 Hsh1s1). unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
      assert(HlookupSh1Eqss1: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
        = lookup (CPaddr (blockParent + sh1offset)) (memory s1) beqAddr).
      {
        assert(Hsh1IsSHE: isSHE (CPaddr (blockParent + sh1offset)) s1).
        {
          unfold isSHE.
          destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s1) beqAddr); try(destruct Hshareds1; congruence).
          destruct v; try(destruct Hshareds1; congruence). trivial.
        }
        unfold isSHE in *. rewrite Hs. rewrite Hs8. simpl.
        destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrSh1Bis.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrSh1Bis. rewrite <-HbeqCurrSh1Bis in *. rewrite HlookupCurrs1 in *.
          exfalso; congruence.
        }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
        destruct (beqAddr block2InCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlock2Sh1Bis.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Sh1Bis. rewrite <-HbeqBlock2Sh1Bis in *. exfalso. unfold isBE in *.
          destruct (lookup block2InCurrPartAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) (CPaddr (blockParent+sh1offset)))
          eqn:HbeqSceSh1Bis.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceSh1Bis. rewrite HbeqSceSh1Bis in *. rewrite <-HlookupSce2Eqs5s1 in *.
          rewrite HlookupSce2Eqs5s0 in *. unfold scentryNext in *. exfalso.
          destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset))) eqn:HbeqSh1s.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; try(congruence).
          assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
          assert(Hsh1PIsSHE: wellFormedFstShadowIfBlockEntry s1) by (unfold consistency1 in *; intuition).
          specialize(Hsh1PIsSHE block2InCurrPartAddr Hblock2IsBEs1). unfold isSHE in *. intro Hcontra.
          rewrite Hcontra in *. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence).
          destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2Sh1Bis. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqCurrSh1Bis. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        destruct (beqAddr block1InCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlock1Sh1Bis.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock1Sh1Bis. rewrite <-HbeqBlock1Sh1Bis in *. exfalso.
          rewrite HlookupBlock1s1 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupSh1Eqss1. assumption.
      (* END sharedBlockPointsToChild *)
    }

    assert(adressesRangePreservedIfOriginAndNextOk s).
    { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
      assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition pdentryPart block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE
        HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. rewrite HgetPartsEqss2 in *.
      rewrite HgetPartsEqs2s1 in *. rewrite HgetPartsEqs1s0 in *. assert(HpartIsPDTs0: isPDT partition s0).
      { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HlookupBlockEqss2: lookup block (memory s) beqAddr = lookup block (memory s2) beqAddr
        /\ beqAddr block2InCurrPartAddr block = false).
      {
        unfold bentryPFlag in *. rewrite Hs in HPflag. rewrite Hs8 in HPflag. rewrite Hs. rewrite Hs8. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HPflag. rewrite Hs7.
        simpl in *. destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        {
          rewrite HnewB3 in HPflag. simpl in *. rewrite HnewB2 in HPflag. simpl in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6.
        split; trivial. rewrite Hs6 in HPflag. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        rewrite Hs5 in HPflag. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4.
        rewrite Hs4 in HPflag. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Block in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3.
        rewrite Hs3 in HPflag. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HlookupParts0: exists pdentryParts0 pdentryParts4,
        lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
        /\ lookup partition (memory s4) beqAddr = Some (PDT pdentryParts4)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs8 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists pdentry. exists pdentry1.
          injection HlookupPart as HpdentriesEq. subst pdentryPart. rewrite Hpdentry3. simpl. rewrite Hpdentry2.
          simpl. rewrite Hpdentry1 in *. auto.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HlookupPart. simpl in *.
          destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock2Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs6 in HlookupPart. simpl in *. exists pdentryPart. exists pdentryPart.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. split; try(split); trivial.
          rewrite Hs4 in HlookupPart. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Part in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqParts in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HlookupPart. simpl in *.
          destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlock1Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqSce1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct HlookupParts0 as [pdentryParts0 [pdentryParts4 (HlookupParts0 & HlookupParts4 & HparentsEq)]].
      rewrite HparentsEq in *. destruct HlookupBlockEqss2 as (HlookupBlockEqss2 & HbeqBlock2Block).
      assert(HlookupSceEqss1: lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s1) beqAddr).
      {
        unfold scentryNext in *. rewrite Hs in Hnext. rewrite Hs8 in Hnext. rewrite Hs. rewrite Hs8. simpl in *.
        destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSceBis; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in Hnext. rewrite Hs7. simpl in *.
        destruct (beqAddr block2InCurrPartAddr scentryaddr) eqn:HbeqBlock2SceBis; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6.
        rewrite Hs6 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces.
        {
          subst scentryaddr. rewrite <-DTL.beqAddrTrue in HbeqSces. exfalso.
          apply CPaddrAddEq in HbeqSces; try(congruence). assert(isPADDR nullAddr s0).
          { unfold consistency in *; unfold consistency1 in *; intuition. }
          unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *.
          destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        rewrite Hs5 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) scentryaddr) eqn:HbeqSh12Sce;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. rewrite Hs4 in Hnext. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2SceBis in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. rewrite Hs3 in Hnext. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqCurrSceBis in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. rewrite Hs2 in Hnext. simpl in *.
        destruct (beqAddr block1InCurrPartAddr scentryaddr) eqn:HbeqBlock1SceBis; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      unfold isBE in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
      rewrite HlookupBlockEqss2 in *. unfold scentryNext in *. unfold scentryOrigin in *.
      rewrite HlookupSceEqss1 in *.
      assert(HblockMappeds0: In block (getMappedBlocks partition s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial. unfold isPDT.
          rewrite HlookupParts4. trivial.
      }
      rewrite Hs2 in HblockIsBE. rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. rewrite Hs2 in HPflag.
      simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
      - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. subst scentryaddr. rewrite Hs1 in Hnext.
        simpl in *. rewrite beqAddrTrue in *. simpl in *. subst block2Next. assert(HpartsEq: currentPart = partition).
        {
          destruct (beqAddr currentPart partition) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
          rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock1Mappeds0.
          apply InFilterPresentInList in HblockMappeds0.
          assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hdisjoint currentPart partition HcurrIsPDTs0 HpartIsPDTs0 HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint block1InCurrPartAddr Hblock1Mappeds0). congruence.
        }
        subst partition. specialize(HparentCurr HbeqPartRoot).
        destruct HparentCurr as [parentBlock12 [startP [endP (HparentBlockMapped & HstartP & HendP & HlebStarts &
          HgebEnd)]]]. exists parentBlock12. rewrite HlookupCurrs0 in HlookupParts0.
        injection HlookupParts0 as HpdentriesEq. subst pdentryParts0. rewrite HnewB in HstartBlock.
        rewrite HnewB in HendBlock. simpl in *. subst startBlock. subst endBlock.
        assert(HoriginIsPStart: originIsParentBlocksStart s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(Horigins0: scentryOrigin (CPaddr (block1InCurrPartAddr+scoffset)) (startAddr (blockrange bentry1)) s0).
        {
          unfold scentryOrigin. rewrite HlookupSce1s0. rewrite Hs1 in Horigin. simpl in *. rewrite beqAddrTrue in *.
          auto.
        }
        assert(HeqTriv: CPaddr (block1InCurrPartAddr+scoffset) = CPaddr (block1InCurrPartAddr+scoffset)) by trivial.
        specialize(HoriginIsPStart currentPart pdentry block1InCurrPartAddr (CPaddr (block1InCurrPartAddr+scoffset))
          (startAddr (blockrange bentry1)) HpartIsPart HlookupCurrs0 Hblock1Mappeds0 HeqTriv Horigins0).
        destruct HoriginIsPStart as (HoriginIsPStart & _). specialize(HoriginIsPStart HbeqPartRoot).
        destruct HoriginIsPStart as [blockParent (HblockPMapped & HstartPBis & HinclP)].
        assert(HblocksEq: parentBlock12 = blockParent).
        {
          destruct (beqAddr parentBlock12 blockParent) eqn:HbeqParents; try(apply DTL.beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. assert(HnoDupMappeds0: noDupMappedPaddrList s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HparentIsPDTs0: isPDT (parent pdentry) s0).
          {
            unfold getMappedBlocks in HblockPMapped. unfold getKSEntries in *. unfold isPDT.
            destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence).
          }
          assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
          specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
            HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
          assert(HstartInParent: In (startAddr (blockrange bentry1)) (getAllPaddrAux [parentBlock12] s0)).
          {
            simpl. destruct (lookup parentBlock12 (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartP. rewrite <-HendP. rewrite app_nil_r.
            apply getAllPaddrBlockIncl; lia.
          }
          pose proof (DisjointPaddrInPart (parent pdentry) parentBlock12 blockParent (startAddr (blockrange bentry1))
            s0 HnoDupMappeds0 HparentIsPDTs0 HparentBlockMapped HblockPMapped HbeqParents HstartInParent) as Hcontra.
          contradict Hcontra. apply HinclP. simpl. rewrite HlookupBlock1s0. rewrite app_nil_r.
          apply getAllPaddrBlockIncl; lia.
        }
        subst blockParent. assert(HnoNext: parentBlocksBoundsIfNoNext s0)
          by (unfold consistency in *; unfold consistency2 in *; intuition).
        assert(HeqTriv2: CPaddr (block2InCurrPartAddr+scoffset) = CPaddr (block2InCurrPartAddr+scoffset)) by trivial.
        specialize(HnoNext currentPart pdentry block2InCurrPartAddr (CPaddr (block2InCurrPartAddr+scoffset))
          (endAddr (blockrange bentry1)) block2End HpartIsPart Hblock2Mappeds0 Hstart2s0 Hend2s0 HeqTriv2 Hnext2s0
          HbeqPartRoot HlookupCurrs0). clear HblockPMapped.
        destruct HnoNext as [blockParent [startParent (HblockPMapped & HstartPTri & HendPBis & HlebStartPEnd1)]].
        assert(HblocksEq: parentBlock12 = blockParent).
        {
          destruct (beqAddr parentBlock12 blockParent) eqn:HbeqParents; try(apply DTL.beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. assert(HnoDupMappeds0: noDupMappedPaddrList s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HparentIsPDTs0: isPDT (parent pdentry) s0).
          {
            unfold getMappedBlocks in HblockPMapped. unfold getKSEntries in *. unfold isPDT.
            destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence).
          }
          assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
          specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
            HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
          assert(HendInParent: In (endAddr (blockrange bentry1)) (getAllPaddrAux [parentBlock12] s0)).
          {
            simpl. destruct (lookup parentBlock12 (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartP. rewrite <-HendP. rewrite app_nil_r.
            apply getAllPaddrBlockIncl; lia.
          }
          pose proof (DisjointPaddrInPart (parent pdentry) parentBlock12 blockParent (endAddr (blockrange bentry1))
            s0 HnoDupMappeds0 HparentIsPDTs0 HparentBlockMapped HblockPMapped HbeqParents HendInParent) as Hcontra.
          contradict Hcontra. simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite app_nil_r. rewrite <-HstartPTri. rewrite <-HendPBis.
          apply getAllPaddrBlockIncl; lia.
        }
        subst blockParent. clear HstartPTri. clear HlebStartPEnd1.
        assert(HparentOfParts0: parentOfPartitionIsPartition s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
        destruct HparentOfParts0 as (HparentIsPart & _ & HbeqParentCurr). specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & _).
        assert(HparentIsPDT: isPDT (parent pdentry) s0) by (unfold isPDT; rewrite HlookupParent; trivial).
        assert(HlookupPEqss0: lookup parentBlock12 (memory s) beqAddr = lookup parentBlock12 (memory s0) beqAddr).
        {
          rewrite Hs. rewrite Hs8. simpl. destruct (beqAddr currentPart parentBlock12) eqn:HbeqCurrP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrP. subst parentBlock12. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
          specialize(Hdisjoint (parent pdentry) currentPart HparentIsPDT HcurrIsPDTs0 HbeqParentCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          unfold getMappedBlocks in *. apply InFilterPresentInList in HparentBlockMapped.
          specialize(Hdisjoint parentBlock12 HparentBlockMapped). apply InFilterPresentInList in Hblock1Mappeds0.
          apply InFilterPresentInList in Hblock2Mappeds0.
          destruct (beqAddr block2InCurrPartAddr parentBlock12) eqn:HbeqBlock2P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2P. subst parentBlock12. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSce2P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2P. subst parentBlock12. exfalso.
            destruct (lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) parentBlock12) eqn:HbeqSh12P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSh12P. subst parentBlock12. exfalso. unfold sh1entryAddr in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2P. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrP. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr parentBlock12) eqn:HbeqBlock1P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1P. subst parentBlock12. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSce1P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1P. subst parentBlock12. exfalso. rewrite HlookupSce1s0 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupPEqss0. assert(isBE parentBlock12 s0).
        {
          unfold isBE. destruct (lookup parentBlock12 (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence).
        }
        split; auto. apply not_eq_sym in HbeqParentCurr. rewrite <-HgetMappedBEqs1s0 in HblockPMapped; trivial.
        rewrite <-HgetMappedBEqs2s1 in *. rewrite HgetMappedBNotCurrEqss2; trivial. unfold isPDT. rewrite Hs4. simpl.
        destruct (beqAddr block2InCurrPartAddr (parent pdentry)) eqn:HbeqBlock2Parent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. rewrite HbeqBlock2Parent in *. rewrite HlookupParent in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqParentCurr. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        destruct (beqAddr block1InCurrPartAddr (parent pdentry)) eqn:HbeqBlock1Parent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock1Parent. rewrite HbeqBlock1Parent in *. rewrite HlookupParent in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) (parent pdentry)) eqn:HbeqSceParent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceParent. rewrite HbeqSceParent in *. rewrite HlookupParent in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HblockIsBE. rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock. rewrite Hs1 in HPflag.
        simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSce1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in Horigin. rewrite Hs1 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces.
        {
          subst scentryaddr. rewrite <-DTL.beqAddrTrue in HbeqSces. exfalso.
          apply CPaddrAddEq in HbeqSces; try(congruence). intro Hcontra. rewrite Hcontra in *.
          assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          unfold isPADDR in *. rewrite HlookupSce1s0 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 partition pdentryParts0 block scentryaddr startBlock endBlock HpartIsPart HblockMappeds0
          HblockIsBE HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupParts0 HbeqPartRoot).
        destruct Hcons0 as [blockParent (HblockPMapped & HblockPIsBE & HstartP & HendP)]. exists blockParent.
        assert(HPDchildP: exists childpd, sh1entryPDchild (CPaddr (blockParent+sh1offset)) childpd s0
          /\ childpd <> nullAddr).
        {
          assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *. unfold sh1entryPDchild.
          destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1P;
            try(exfalso; congruence). destruct v; try(exfalso; congruence). exists (PDchild s9). split; trivial.
          assert(HparentOfParts0: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfParts0 partition pdentryParts0 HlookupParts0).
          destruct HparentOfParts0 as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
          destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
          assert(Hparent: pdentryParent partition (parent pdentryParts0) s0).
          { unfold pdentryParent. rewrite HlookupParts0. trivial. }
          assert(HisChilds0: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HisChilds0 partition (parent pdentryParts0) HpartIsPart Hparent HbeqPartRoot).
          assert(HPflagP: bentryPFlag blockParent true s0).
          {
            apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentryP (HlookupBP & Hpres)].
            unfold bentryPFlag. rewrite HlookupBP. auto.
          }
          assert(HlebStarts: startBlock <= startBlock) by lia.
          assert(HgebEnds: endBlock >= endBlock) by lia.
          assert(HchildBlockProps: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          specialize(HchildBlockProps partition (parent pdentryParts0) block startBlock endBlock blockParent
            startBlock endBlock HparentIsPart HisChilds0 HblockMappeds0 HstartBlock HendBlock HPflag HblockPMapped
            HstartP HendP HPflagP HlebStarts HgebEnds).
          destruct HchildBlockProps as (_ & Hres & _). apply Hres. unfold sh1entryPDchild. rewrite HlookupSh1P.
          trivial.
        }
        destruct HPDchildP as [childpd (HPDchildP & HbeqPDChildNull)].
        destruct (beqAddr block2InCurrPartAddr blockParent) eqn:HbeqBlock2P.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2P. subst blockParent. unfold sh1entryPDchild in *. exfalso.
          unfold sh1entryAddr in *.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          subst sh1entryaddr2. rewrite HlookupSh12Eqs1s0 in *.
          destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        assert(HlookupPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
        {
          unfold bentryStartAddr in *. rewrite Hs. rewrite Hs8. simpl.
          destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqBlock2P. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce2P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2P. rewrite HbeqSce2P in *. exfalso.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh12P.
          {
            unfold sh1entryAddr in *. exfalso. unfold sh1entryPDchild in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2. rewrite <-DTL.beqAddrTrue in HbeqSh12P. rewrite HbeqSh12P in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2P. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrBP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1P. subst blockParent. unfold sh1entryPDchild in *. exfalso.
            unfold sh1entryAddr in *.
            destruct (lookup block1InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr1.
            destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce1P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1P. rewrite HbeqSce1P in *. rewrite HlookupSce1s0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupPEq. split; auto.
        assert(isPDT (parent pdentryParts0) s0).
        {
          unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
          destruct (lookup (parent pdentryParts0) (memory s0) beqAddr); try(simpl in *; congruence).
          destruct v; try(simpl in *; congruence). trivial.
        }
        rewrite <-HgetMappedBEqs1s0 in HblockPMapped; trivial. rewrite <-HgetMappedBEqs2s1 in *.
        destruct (beqAddr currentPart (parent pdentryParts0)) eqn:HbeqCurrParent.
        + rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite <-HbeqCurrParent in *.
          specialize(HgetMappedBCurrEqss2 blockParent). destruct HgetMappedBCurrEqss2 as (Hres & _).
          apply Hres in HblockPMapped. rewrite <-beqAddrFalse in *.
          destruct HblockPMapped as [Hcontra | HblockPMappeds]; trivial. exfalso; congruence.
        + rewrite <-beqAddrFalse in *. rewrite HgetMappedBNotCurrEqss2; trivial.
          assert(HparentIsPDTs2: isPDT (parent pdentryParts0) s2).
          {
            unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
            destruct (lookup (parent pdentryParts0) (memory s2) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          unfold isPDT in *. rewrite Hs4. simpl.
          destruct (beqAddr block2InCurrPartAddr (parent pdentryParts0)) eqn:HbeqBlock2Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. rewrite <-HbeqBlock2Parent in *.
            destruct (lookup block2InCurrPartAddr (memory s2) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqCurrParent. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END adressesRangePreservedIfOriginAndNextOk *)
    }

    assert(childsBlocksPropsInParent s).
    { (* BEGIN childsBlocksPropsInParent s *)
      intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
        HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
        HPflagParent HlebStart HgebEnd. rewrite HgetPartsEqss2 in *. assert(HparentIsPDTs3: isPDT pdparent s3).
      { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
      assert(isPDT pdparent s4).
      {
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr pdparent) eqn:HbeqBlock2Parent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. subst pdparent. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetPartsEqs2s1 in *. assert(isPDT pdparent s1)
        by (apply partitionsArePDT; unfold consistency1 in *; intuition). rewrite HgetPartsEqs1s0 in *.
      assert(HparentIsPDTs0: isPDT pdparent s0)
        by (apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEqss2 in HchildIsChild; trivial. assert(HchildIsPDTs2: isPDT child s2).
      { apply childrenArePDT with pdparent; unfold cons1Free in *; intuition. }
      rewrite HgetChildrenEqs2s1 in HchildIsChild; trivial.
      assert(isPDT child s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEqs1s0 in HchildIsChild; trivial. assert(HchildIsPDTs0: isPDT child s0).
      { apply childrenArePDT with pdparent; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HblockParentMappeds0: In blockParent (getMappedBlocks pdparent s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart pdparent) eqn:HbeqCurrParent.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrParent. subst pdparent. specialize(HgetMappedBCurrEqss2 blockParent).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial.
      }
      assert(HblockChildMappeds0: In blockChild (getMappedBlocks child s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. specialize(HgetMappedBCurrEqss2 blockChild).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial. unfold isPDT in *. rewrite Hs4.
          simpl. destruct (beqAddr block2InCurrPartAddr child) eqn:HbeqBlock2Child.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Child. subst child. unfold isBE in *.
            destruct (lookup block2InCurrPartAddr (memory s2) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqCurrChild. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      assert(HlookupBlockPEqss2: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s2) beqAddr
        /\ beqAddr block2InCurrPartAddr blockParent = false).
      {
        unfold bentryPFlag in *. rewrite Hs in HPflagParent. rewrite Hs8 in HPflagParent. rewrite Hs. rewrite Hs8.
        simpl in *.
        destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP; try(exfalso; congruence).
        rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HPflagParent. rewrite Hs7.
        simpl in *. destruct (beqAddr block2InCurrPartAddr blockParent) eqn:HbeqBlock2BlockP.
        {
          rewrite HnewB3 in HPflagParent. simpl in *. rewrite HnewB2 in HPflagParent. simpl in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6.
        split; trivial. rewrite Hs6 in HPflagParent. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) blockParent) eqn:HbeqSceBP;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        rewrite Hs5 in HPflagParent. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) blockParent) eqn:HbeqSh1BP;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4.
        rewrite Hs4 in HPflagParent. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2BlockP in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3.
        rewrite Hs3 in HPflagParent. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlockP in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HlookupBlockCEqss2: lookup blockChild (memory s) beqAddr = lookup blockChild (memory s2) beqAddr
        /\ beqAddr block2InCurrPartAddr blockChild = false).
      {
        unfold bentryPFlag in *. rewrite Hs in HPflagChild. rewrite Hs8 in HPflagChild. rewrite Hs. rewrite Hs8.
        simpl in *.
        destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBlockC; try(exfalso; congruence).
        rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HPflagChild. rewrite Hs7.
        simpl in *. destruct (beqAddr block2InCurrPartAddr blockChild) eqn:HbeqBlock2BlockC.
        {
          rewrite HnewB3 in HPflagChild. simpl in *. rewrite HnewB2 in HPflagChild. simpl in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6.
        split; trivial. rewrite Hs6 in HPflagChild. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) blockChild) eqn:HbeqSceBC;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        rewrite Hs5 in HPflagChild. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) blockChild) eqn:HbeqSh1BC;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4.
        rewrite Hs4 in HPflagChild. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2BlockC in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3.
        rewrite Hs3 in HPflagChild. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlockC in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct HlookupBlockPEqss2 as (HlookupBlockPEqss2 & HbeqBlock2BP). unfold bentryStartAddr in *.
      destruct HlookupBlockCEqss2 as (HlookupBlockCEqss2 & HbeqBlock2BC). unfold bentryEndAddr in *.
      unfold bentryPFlag in *. unfold checkChild. unfold bentryAFlag. rewrite HlookupBlockPEqss2 in *.
      rewrite HlookupBlockCEqss2 in *.
      destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1BP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlock1BP. subst blockParent. exfalso.
        assert(pdparent = currentPart).
        {
          destruct (beqAddr pdparent currentPart) eqn:HbeqParentCurr; try(rewrite DTL.beqAddrTrue; assumption).
          exfalso. rewrite <-beqAddrFalse in *.
          assert(Hdisjoint: DisjointKSEntries s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
          specialize(Hdisjoint pdparent currentPart HparentIsPDTs0 HcurrIsPDTs0 HbeqParentCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          unfold getMappedBlocks in *. apply InFilterPresentInList in HblockParentMappeds0.
          apply InFilterPresentInList in Hblock1Mappeds0.
          specialize(Hdisjoint block1InCurrPartAddr HblockParentMappeds0). congruence.
        }
        subst pdparent. specialize(Hblock1HasNoChilds0 child startChild HchildIsChild).
        specialize(Hblock2HasNoChilds0 child startChild HchildIsChild).
        assert(HwellChild: wellFormedBlock s2) by (unfold cons1Free in *; intuition).
        specialize(HwellChild blockChild startChild endChild HPflagChild HstartChild HendChild).
        destruct HwellChild as (HwellChild & _).
        assert(Hcontra: ~ In startChild (getMappedPaddr child s0)).
        {
          rewrite HlookupBlock1s2 in *. rewrite HnewB in HstartParent. rewrite HnewB in HendParent. simpl in *.
          subst startParent. subst endParent.
          destruct (Nat.ltb startChild (endAddr (blockrange bentry1))) eqn:HltStartCEnd1.
          - apply PeanoNat.Nat.ltb_lt in HltStartCEnd1. apply Hblock1HasNoChilds0. simpl. rewrite HlookupBlock1s0.
            rewrite app_nil_r. apply getAllPaddrBlockIncl; lia.
          - apply PeanoNat.Nat.ltb_ge in HltStartCEnd1. apply Hblock2HasNoChilds0. simpl.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-Hend2s0. rewrite <-Hstart2s0. rewrite app_nil_r.
            apply getAllPaddrBlockIncl; lia.
        }
        contradict Hcontra. apply addrInBlockIsMapped with blockChild; trivial. simpl. rewrite Hs2 in HstartChild.
        rewrite Hs2 in HendChild. simpl in *.
        destruct (beqAddr block1InCurrPartAddr blockChild) eqn:HbeqBlock1BC.
        - rewrite <-DTL.beqAddrTrue in HbeqBlock1BC. subst blockChild. rewrite HlookupBlock1s0. rewrite app_nil_r.
          rewrite HnewB in HstartChild. rewrite HnewB in HendChild. simpl in *. subst startChild. subst endChild.
          assert(Hwell1: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
          specialize(Hwell1 block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
            HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell1 as (Hwell1 & _).
          apply getAllPaddrBlockIncl; lia.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HstartChild. rewrite Hs1 in HendChild. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockChild) eqn:HbeqSce1BC;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          destruct (lookup blockChild (memory s0) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. subst startChild. subst endChild.
          apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockPEqs2s0: lookup blockParent (memory s2) beqAddr = lookup blockParent (memory s0) beqAddr).
      {
        rewrite Hs2. rewrite Hs2 in HstartParent. simpl in *. rewrite HbeqBlock1BP in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. rewrite Hs1 in HstartParent.
        simpl in *. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce1BP;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupBlockPEqs2s0 in *. rewrite Hs2 in HstartChild. rewrite Hs2 in HendChild.
      assert(HchildBlockPropss0: childsBlocksPropsInParent s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      rewrite Hs2 in HPflagChild. simpl in *. destruct (beqAddr block1InCurrPartAddr blockChild) eqn:HbeqBlock1BC.
      - rewrite <-DTL.beqAddrTrue in HbeqBlock1BC. subst blockChild. rewrite HnewB in HstartChild.
        rewrite HnewB in HendChild. simpl in *. subst startChild. subst endChild.
        rewrite <-HlookupBlock1s0 in HlookupBlock1s1. rewrite HlookupBlock1s1 in *.
        assert(HgebEnd1: endParent >= endAddr (blockrange bentry1)) by lia.
        specialize(HchildBlockPropss0 child pdparent block1InCurrPartAddr (startAddr (blockrange bentry1))
          (endAddr (blockrange bentry1)) blockParent startParent endParent HparentIsPart HchildIsChild
          HblockChildMappeds0 Hstart1s1 Hend1s1 HPflag1s1 HblockParentMappeds0 HstartParent HendParent
          HPflagParent HlebStart HgebEnd1).
        destruct HchildBlockPropss0 as (HcheckChild & HchildNotNull & HlocNotNull & HAflagParent).
        assert(HlookupSh1Eqss0: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
          = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
        {
          assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockPIsBE: isBE blockParent s0).
          {
             unfold isBE. destruct (lookup blockParent (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). trivial.
          }
          specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *. rewrite Hs. rewrite Hs8. simpl.
          destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrSh1P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrSh1P. rewrite HbeqCurrSh1P in *. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
          destruct (beqAddr block2InCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlock2Sh1P.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Sh1P. rewrite <-HbeqBlock2Sh1P in *. unfold bentryAFlag in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) (CPaddr (blockParent+sh1offset)))
            eqn:HbeqSce2Sh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2Sh1. rewrite HbeqSce2Sh1 in *. unfold scentryNext in *. exfalso.
            destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset)))
            eqn:HbeqSh1s2.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqSh1s2. apply CPaddrAddEq in HbeqSh1s2; try(exfalso; congruence).
            assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *. unfold sh1entryPDchild in *.
            destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Sh1P. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrSh1P. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          destruct (beqAddr block1InCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlock1Sh1P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1Sh1P. rewrite <-HbeqBlock1Sh1P in *. rewrite HlookupBlock1s0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (blockParent+sh1offset)))
            eqn:HbeqSce1Sh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1Sh1. rewrite HbeqSce1Sh1 in *. rewrite HlookupSce1s0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        unfold sh1entryPDchild. unfold sh1entryInChildLocation. rewrite HlookupSh1Eqss0.
        split; try(split; try(split)); trivial.
        + intros blockIDInChild HchildLoc.
          assert(HchildLocs0: sh1entryInChildLocation (CPaddr (blockParent + sh1offset)) blockIDInChild s0).
          {
            unfold sh1entryInChildLocation.
            destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial.
            intro HbeqLocNull. specialize(HlocIsBE HbeqLocNull). unfold isBE in *. rewrite Hs in HlocIsBE.
            rewrite Hs8 in HlocIsBE. simpl in *.
            destruct (beqAddr currentPart blockIDInChild) eqn:HbeqCurrLoc; try(exfalso; congruence).
            rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HlocIsBE. simpl in *.
            destruct (beqAddr block2InCurrPartAddr blockIDInChild) eqn:HbeqBlock2Loc.
            - rewrite <-DTL.beqAddrTrue in HbeqBlock2Loc. rewrite HbeqBlock2Loc in *.
              rewrite HlookupBlock2Eqs1s0 in *. assumption.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite Hs6 in HlocIsBE. simpl in *.
              destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockIDInChild) eqn:HbeqSce2Loc;
                try(exfalso; congruence). rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlocIsBE. simpl in *.
              destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockIDInChild) eqn:HbeqSh1Loc;
                try(exfalso; congruence). rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HlocIsBE. simpl in *.
              rewrite beqAddrFalse in *. rewrite HbeqBlock2Loc in *. rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlocIsBE. simpl in *.
              rewrite beqAddrFalse in *. rewrite HbeqCurrLoc in *. rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HlocIsBE. simpl in *.
              destruct (beqAddr block1InCurrPartAddr blockIDInChild) eqn:HbeqBlock1Loc.
              + rewrite <-DTL.beqAddrTrue in HbeqBlock1Loc. rewrite HbeqBlock1Loc in *. rewrite HlookupBlock1s0.
                trivial.
              + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
                rewrite Hs1 in HlocIsBE. simpl in *.
                destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockIDInChild) eqn:HbeqSce1Loc;
                  try(exfalso; congruence). rewrite <-beqAddrFalse in *.
                rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          apply HlocNotNull; assumption.
        + intro HpropsOrBounds. apply HAflagParent. right. apply paddrNeqNatNeqEquiv. lia.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HstartChild. rewrite Hs1 in HendChild. rewrite Hs1 in HPflagChild. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockChild) eqn:HbeqSce1BC;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(HchildBlockPropss0 child pdparent blockChild startChild endChild blockParent startParent endParent
          HparentIsPart HchildIsChild HblockChildMappeds0 HstartChild HendChild HPflagChild HblockParentMappeds0
          HstartParent HendParent HPflagParent HlebStart HgebEnd).
        destruct HchildBlockPropss0 as (HcheckChild & HchildNotNull & HlocNotNull & HAflagParent).
        assert(HlookupSh1Eqss0: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
          = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
        {
          assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockPIsBE: isBE blockParent s0).
          {
             unfold isBE. destruct (lookup blockParent (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). trivial.
          }
          specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *. rewrite Hs. rewrite Hs8. simpl.
          destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrSh1P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrSh1P. rewrite HbeqCurrSh1P in *. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
          destruct (beqAddr block2InCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlock2Sh1P.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Sh1P. rewrite <-HbeqBlock2Sh1P in *. unfold bentryAFlag in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) (CPaddr (blockParent+sh1offset)))
            eqn:HbeqSce2Sh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2Sh1. rewrite HbeqSce2Sh1 in *. unfold scentryNext in *. exfalso.
            destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset)))
            eqn:HbeqSh1s2.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqSh1s2. apply CPaddrAddEq in HbeqSh1s2; try(exfalso; congruence).
            assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *. unfold sh1entryPDchild in *.
            destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Sh1P. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrSh1P. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          destruct (beqAddr block1InCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlock1Sh1P.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1Sh1P. rewrite <-HbeqBlock1Sh1P in *. rewrite HlookupBlock1s0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (CPaddr (blockParent+sh1offset)))
            eqn:HbeqSce1Sh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1Sh1. rewrite HbeqSce1Sh1 in *. rewrite HlookupSce1s0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        unfold sh1entryPDchild. unfold sh1entryInChildLocation. rewrite HlookupSh1Eqss0.
        split; try(split; try(split)); trivial. intros blockIDInChild HchildLoc.
        assert(HchildLocs0: sh1entryInChildLocation (CPaddr (blockParent + sh1offset)) blockIDInChild s0).
        {
          unfold sh1entryInChildLocation.
          destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial.
          intro HbeqLocNull. specialize(HlocIsBE HbeqLocNull). unfold isBE in *. rewrite Hs in HlocIsBE.
          rewrite Hs8 in HlocIsBE. simpl in *.
          destruct (beqAddr currentPart blockIDInChild) eqn:HbeqCurrLoc; try(exfalso; congruence).
          rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HlocIsBE. simpl in *.
          destruct (beqAddr block2InCurrPartAddr blockIDInChild) eqn:HbeqBlock2Loc.
          - rewrite <-DTL.beqAddrTrue in HbeqBlock2Loc. rewrite HbeqBlock2Loc in *.
            rewrite HlookupBlock2Eqs1s0 in *. assumption.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite Hs6 in HlocIsBE. simpl in *.
            destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockIDInChild) eqn:HbeqSce2Loc;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlocIsBE. simpl in *.
            destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockIDInChild) eqn:HbeqSh1Loc;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HlocIsBE. simpl in *.
            rewrite beqAddrFalse in *. rewrite HbeqBlock2Loc in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlocIsBE. simpl in *.
            rewrite beqAddrFalse in *. rewrite HbeqCurrLoc in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HlocIsBE. simpl in *.
            destruct (beqAddr block1InCurrPartAddr blockIDInChild) eqn:HbeqBlock1Loc.
            + rewrite <-DTL.beqAddrTrue in HbeqBlock1Loc. rewrite HbeqBlock1Loc in *. rewrite HlookupBlock1s0.
              trivial.
            + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite Hs1 in HlocIsBE. simpl in *.
              destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockIDInChild) eqn:HbeqSce1Loc;
                try(exfalso; congruence). rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        }
        apply HlocNotNull; assumption.
      (* END childsBlocksPropsInParent *)
    }

    assert(noChildImpliesAddressesNotShared s).
    { (* BEGIN noChildImpliesAddressesNotShared s *)
      intros partition pdentryPart block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild child addr
        HchildIsChild HaddrInBlock. assert(HpartIsPDT: isPDT partition s).
      { unfold isPDT. rewrite HlookupPart. trivial. }
      rewrite HgetPartsEqss2 in *. assert(HpartIsPDTs3: isPDT partition s3).
      { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; intuition. }
      assert(isPDT partition s4).
      {
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock2Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Part. subst partition. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      assert(isPDT child s).
      { apply childrenArePDT with partition; unfold cons1Free in *; intuition. }
      rewrite HgetPartsEqs2s1 in *. assert(HpartIsPDTs1: isPDT partition s1).
      { apply partitionsArePDT; unfold consistency1 in *; intuition. }
      assert(HlookupParts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)).
      {
        unfold isPDT in *. destruct (lookup partition (memory s1) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists p. reflexivity.
      }
      destruct HlookupParts1 as [pdentryParts1 HlookupParts1].
      assert(HblockMappeds1: In block (getMappedBlocks partition s1)).
      {
        rewrite <-HgetMappedBEqs2s1. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial.
      }
      rewrite HgetChildrenEqss2 in HchildIsChild; trivial. rewrite HgetChildrenEqs2s1 in HchildIsChild; trivial.
      assert(HPDchilds1: sh1entryPDchild sh1entryaddr nullAddr s1).
      {
        unfold sh1entryPDchild in *. unfold sh1entryAddr in *. rewrite HlookupBlock1s0 in Hsh11s0.
        destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst sh1entryaddr1. subst sh1entryaddr2. rewrite Hs in HPDchild.
        rewrite Hs8 in HPDchild. simpl in *.
        destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HPDchild. simpl in *.
        destruct (beqAddr block2InCurrPartAddr sh1entryaddr) eqn:HbeqBlock2Sh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in HPDchild. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) sh1entryaddr) eqn:HbeqSce2Sh1;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDchild. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
        - rewrite <-DTL.beqAddrTrue in HbeqSh1s. rewrite HbeqSh1s in *. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs4 in HPDchild. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Sh1 in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs3 in HPDchild. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrSh1 in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HPDchild. simpl in *.
          destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlock1Sh1; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HpropsOrAddr: In addr (getAllPaddrAux [block] s1)
        \/ (In addr (getAllPaddrAux [block2InCurrPartAddr] s0) /\ block = block1InCurrPartAddr)).
      {
        rewrite Hs in HaddrInBlock. rewrite Hs8 in HaddrInBlock. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(simpl in *; exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HaddrInBlock. simpl in *.
        destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Block. subst block. apply mappedBlockIsBE in HblockMapped.
          destruct HblockMapped as [bentry (HlookupBlock2 & Hpres)]. rewrite HlookupBlock2Eqss7 in *. exfalso.
          rewrite Hs7 in HlookupBlock2. simpl in *. rewrite beqAddrTrue in *. injection HlookupBlock2 as HbentriesEq.
          subst bentry. rewrite HnewB3 in Hpres. simpl in *. rewrite HnewB2 in Hpres. simpl in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in HaddrInBlock. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block) eqn:HbeqSce2Block;
          try(simpl in *; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HaddrInBlock. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) block) eqn:HbeqSh12Block;
          try(simpl in *; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HaddrInBlock. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2Block in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HaddrInBlock. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HaddrInBlock. simpl in *.
        destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
        - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. rewrite HnewB in HaddrInBlock. simpl in *.
          rewrite app_nil_r in HaddrInBlock. apply getAllPaddrBlockInclRev in HaddrInBlock.
          destruct HaddrInBlock as (HlebStartAddr & HltAddrEnd & _).
          destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
          + apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. left. rewrite HlookupBlock1s1. rewrite app_nil_r.
            apply getAllPaddrBlockIncl; lia.
          + apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. right. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            rewrite HlookupBlock2Eqs1s0 in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite app_nil_r. rewrite <-Hend2s0. rewrite <-Hstart2s0.
            split; trivial. apply getAllPaddrBlockIncl; lia.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HpropsOrAddr as [HaddrInBlocks1 | (HaddrInBlock2s1 & HblockIsBlock1)].
      - specialize(HnoChilds1 partition pdentryParts1 block sh1entryaddr HpartIsPart HlookupParts1 HblockMappeds1 Hsh1
          HPDchilds1 child addr HchildIsChild HaddrInBlocks1). contradict HnoChilds1.
        destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
        + rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. apply HgetMappedPCurrEqss1; assumption.
        + rewrite <-beqAddrFalse in *. rewrite <-HgetMappedPNotCurrEqss1; trivial.
      - subst block. assert(partition = currentPart).
        {
          destruct (beqAddr partition currentPart) eqn:HbeqPartCurr; try(rewrite DTL.beqAddrTrue; assumption).
          exfalso. rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *.
          apply InFilterPresentInList in HblockMappeds1. apply InFilterPresentInList in Hblock1Mappeds1.
          assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
          specialize(Hdisjoint partition currentPart HpartIsPDTs1 HcurrIsPDTs1 HbeqPartCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint block1InCurrPartAddr HblockMappeds1). congruence.
        }
        subst partition. assert(isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
        rewrite HgetChildrenEqs1s0 in HchildIsChild; trivial.
        specialize(Hblock2HasNoChilds0 child addr HchildIsChild HaddrInBlock2s1). contradict Hblock2HasNoChilds0.
        assert(isPDT child s0).
        { apply childrenArePDT with currentPart; unfold consistency in *; unfold consistency1 in *; intuition. }
        rewrite <-HgetMappedPEqs1s0; trivial. destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
        + rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. apply HgetMappedPCurrEqss1; assumption.
        + rewrite <-beqAddrFalse in *. rewrite <-HgetMappedPNotCurrEqss1; trivial.
      (* END noChildImpliesAddressesNotShared *)
    }

    assert(kernelsAreNotAccessible s).
    { (* BEGIN kernelsAreNotAccessible s *)
      intros block startaddr Hstart HPflag HstartIsKSs.
      assert(Hblock: bentryPFlag block true s1
        /\ lookup block (memory s) beqAddr = lookup block (memory s2) beqAddr).
      {
        unfold bentryPFlag in *. rewrite Hs in HPflag. rewrite Hs8 in HPflag. rewrite Hs. rewrite Hs8. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HPflag. rewrite Hs7.
        simpl in *. destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        {
          rewrite HnewB3 in HPflag. simpl in *. rewrite HnewB2 in HPflag. simpl in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in HPflag. rewrite Hs6. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) block) eqn:HbeqSce2Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs5 in HPflag. rewrite Hs5. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh12Block;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HPflag. rewrite Hs4.
        simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Block in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPflag. rewrite Hs3.
        simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. split; trivial. rewrite Hs2 in HPflag.
        simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
        - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct Hblock as (HPflags1 & HlookupBEqss2). assert(HstartIsKSs1: isKS startaddr s1).
      {
        unfold isKS in *. rewrite Hs in HstartIsKSs. rewrite Hs8 in HstartIsKSs. simpl in *.
        destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HstartIsKSs. simpl in *.
        destruct (beqAddr block2InCurrPartAddr startaddr) eqn:HbeqBlock2Start.
        - rewrite <-DTL.beqAddrTrue in HbeqBlock2Start. subst startaddr. rewrite HnewB3 in HstartIsKSs. simpl in *.
          rewrite HnewB2 in HstartIsKSs. simpl in *. subst blockToFreeIdx. unfold bentryBlockIndex in *.
          rewrite <-HlookupBlock1Eqs3s1. destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence).
          destruct v; try(congruence).
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs6 in HstartIsKSs. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) startaddr) eqn:HbeqSce2Start;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HstartIsKSs. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh12Start;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HstartIsKSs. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Start in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HstartIsKSs. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqCurrStart in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HstartIsKSs. simpl in *.
          destruct (beqAddr block1InCurrPartAddr startaddr) eqn:HbeqBlock1Start.
          + rewrite <-DTL.beqAddrTrue in HbeqBlock1Start. subst startaddr. rewrite HnewB in HstartIsKSs. simpl in *.
            rewrite HlookupBlock1s1. assumption.
          + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      unfold bentryStartAddr in *. unfold bentryAFlag. rewrite HlookupBEqss2 in *.
      assert(Hstarts1: bentryStartAddr block startaddr s1).
      {
        unfold bentryStartAddr. rewrite Hs2 in Hstart. simpl in *.
        destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
        - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. rewrite HlookupBlock1s1. rewrite HnewB in Hstart.
          auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(HkernNotAccs1 block startaddr Hstarts1 HPflags1 HstartIsKSs1). unfold bentryAFlag in *. rewrite Hs2.
      simpl. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
      - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. rewrite HlookupBlock1s1 in *. rewrite HnewB. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END kernelsAreNotAccessible *)
    }

    assert(blockAndNextAreSideBySide s).
    { (* BEGIN blockAndNextAreSideBySide s *)
      assert(Hcons0: blockAndNextAreSideBySide s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
        Hnext. rewrite HgetPartsEqss2 in *. assert(HpartIsPDTs4: isPDT partition s4).
      {
        assert(HpartIsPDTs3: isPDT partition s3).
        { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock3Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock3Part. subst partition. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetPartsEqs2s1 in *. rewrite HgetPartsEqs1s0 in *. assert(HpartIsPDT: isPDT partition s0).
      { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HblockMappeds0: In block (getMappedBlocks partition s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; assumption.
      }
      unfold bentryEndAddr in *. rewrite Hs in HendBlock. rewrite Hs8 in HendBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HendBlock. simpl in *.
      destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlock2Block. subst block. exfalso. apply mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite HlookupBlock2Eqss7 in *. rewrite Hs7 in Hlookup.
        simpl in *. rewrite beqAddrTrue in *. injection Hlookup as HbentriesEq. subst bentry. rewrite HnewB3 in Hpres.
        simpl in *. rewrite HnewB2 in Hpres. simpl in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HendBlock. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block) eqn:HbeqSce2Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HendBlock. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh12Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HendBlock. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Block in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HendBlock. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      unfold scentryNext in *. rewrite Hs in Hnext. rewrite Hs8 in Hnext. simpl in *.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in Hnext. simpl in *.
      destruct (beqAddr block2InCurrPartAddr scentryaddr) eqn:HbeqBlock2Sce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in Hnext. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSce2Sce.
      {
        subst scentryaddr. rewrite <-DTL.beqAddrTrue in HbeqSce2Sce.
        apply CPaddrAddEq in HbeqSce2Sce; try(exfalso; congruence). intro Hcontra. rewrite Hcontra in *.
        assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in Hnext. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh11Sce;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in Hnext. simpl in *.
      rewrite beqAddrFalse in *. rewrite HbeqBlock2Sce in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hnext. simpl in *.
      rewrite beqAddrFalse in *. rewrite HbeqCurrSce in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in Hnext. simpl in *.
      destruct (beqAddr block1InCurrPartAddr scentryaddr) eqn:HbeqBlock1Sce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HendBlock. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
      - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. subst scentryaddr. rewrite Hs1 in Hnext.
        simpl in *. rewrite beqAddrTrue in *. simpl in *. subst scnext. rewrite HnewB in HendBlock. simpl in *.
        subst endaddr. rewrite Hs1 in Hcurr. simpl in *.
        assert(HcurrIsParts0: In (currentPartition s0) (getPartitions multiplexer s0)).
        { unfold consistency in *; unfold consistency1 in *; intuition. }
        rewrite <-Hcurr in *.
        assert(HeqTriv: CPaddr (block2InCurrPartAddr+scoffset) = CPaddr (block2InCurrPartAddr+scoffset)) by trivial.
        specialize(Hcons0 currentPart block2InCurrPartAddr (CPaddr (block2InCurrPartAddr+scoffset)) block2Next
          block2End HcurrIsParts0 Hblock2Mappeds0 Hend2s0 HeqTriv HbeqNextNull Hnext2s0).
        destruct Hcons0 as (Hcons0 & Hblock2NMappeds0). unfold bentryStartAddr in *.
        rewrite Hs at 1. rewrite Hs8. simpl. destruct (beqAddr currentPart block2Next) eqn:HbeqCurrNext.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrNext. subst block2Next. rewrite HlookupCurrs0 in *.
          exfalso; congruence.
        }
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
        destruct (beqAddr block2InCurrPartAddr block2Next) eqn:HbeqBlock2Next.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Next. subst block2Next.
          assert(Hwells0: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hwells0 block2InCurrPartAddr block2End block2End HPflag2s0 Hcons0 Hend2s0).
          destruct Hwells0 as (Hcontra & _). exfalso. lia.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block2Next) eqn:HbeqSce2Next.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSce2Next. rewrite HbeqSce2Next in *. exfalso.
          destruct (lookup block2Next (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) block2Next) eqn:HbeqSh12Next.
        {
          unfold sh1entryAddr in *. exfalso.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *.
          rewrite <-DTL.beqAddrTrue in HbeqSh12Next. rewrite HbeqSh12Next in *.
          destruct (lookup block2Next (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2Next. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqCurrNext. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        assert(partition = currentPart).
        {
          destruct (beqAddr partition currentPart) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption).
          exfalso. rewrite <-beqAddrFalse in *.
          assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hdisjoint partition currentPart HpartIsPDT HcurrIsPDTs0 HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock1Mappeds0.
          apply InFilterPresentInList in HblockMappeds0. specialize(Hdisjoint block1InCurrPartAddr HblockMappeds0).
          congruence.
        }
        subst partition. rewrite <-HgetMappedBEqs1s0 in Hblock2NMappeds0; trivial.
        rewrite <-HgetMappedBEqs2s1 in Hblock2NMappeds0. specialize(HgetMappedBCurrEqss2 block2Next).
        destruct HgetMappedBCurrEqss2 as (HgetMappedBCurrEqss2 & _). apply HgetMappedBCurrEqss2 in Hblock2NMappeds0.
        destruct Hblock2NMappeds0 as [Hcontra | Hblock2NMappeds]; try(exfalso; congruence). split; trivial.
        rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr block2Next) eqn:HbeqBlock1Next.
        + rewrite <-DTL.beqAddrTrue in HbeqBlock1Next. subst block2Next. rewrite HlookupBlock1s0 in *.
          rewrite HnewB. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block2Next) eqn:HbeqSce1Next.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1Next. subst block2Next. rewrite HlookupSce1s0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HendBlock. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSce1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSce1Sce.
        {
          subst scentryaddr. rewrite <-DTL.beqAddrTrue in HbeqSce1Sce. exfalso.
          apply CPaddrAddEq in HbeqSce1Sce; try(congruence). intro Hcontra. rewrite Hcontra in *.
        assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold isPADDR in *. rewrite HlookupSce1s0 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockMappeds0 HendBlock Hsce
          HbeqNextNull Hnext). destruct Hcons0 as (Hcons0 & Hblock2NMappeds0). unfold bentryStartAddr in *.
        rewrite Hs at 1. rewrite Hs8. simpl. destruct (beqAddr currentPart scnext) eqn:HbeqCurrNext.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrNext. subst scnext. rewrite HlookupCurrs0 in *. exfalso. congruence.
        }
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
        destruct (beqAddr block2InCurrPartAddr scnext) eqn:HbeqBlock2Next.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Next. subst scnext. exfalso. unfold bentryStartAddr in *.
          rewrite HlookupBlock2Eqs1s0 in *.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          rewrite <-Hstart2s0 in *. subst endaddr.
          assert(Hend1Min1: p (CPaddr (endAddr (blockrange bentry1) - 1)) = endAddr (blockrange bentry1) - 1).
          {
            unfold CPaddr. assert(endAddr (blockrange bentry1) <= maxAddr) by (apply Hp).
            destruct (le_dec (endAddr (blockrange bentry1) - 1) maxAddr); try(lia). reflexivity.
          }
          assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
          specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
            HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
          assert(HendMinInBlock1:
            In (CPaddr (endAddr (blockrange bentry1)-1)) (getAllPaddrAux [block1InCurrPartAddr] s0)).
          {
            simpl. rewrite HlookupBlock1s0. rewrite app_nil_r. apply getAllPaddrBlockIncl; lia.
          }
          assert(HlookupBlock: exists bentry, lookup block (memory s0) beqAddr = Some (BE bentry)).
          {
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists b0. reflexivity.
          }
          destruct HlookupBlock as [bentry HlookupBlock].
          assert(HstartBlock: bentryStartAddr block (startAddr (blockrange bentry)) s0).
          { unfold bentryStartAddr. rewrite HlookupBlock. reflexivity. }
          assert(HwellB: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HPflag: bentryPFlag block true s0).
          {
            apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentryBis (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          specialize(HwellB block (startAddr (blockrange bentry)) (endAddr (blockrange bentry1)) HPflag
            HstartBlock HendBlock). destruct HwellB as (HwellB & _).
          assert(HendMinInBlock: In (CPaddr (endAddr (blockrange bentry1)-1)) (getAllPaddrAux [block] s0)).
          {
            simpl. rewrite HlookupBlock in *. rewrite app_nil_r. rewrite <-HendBlock. apply getAllPaddrBlockIncl; lia.
          }
          assert(HpartitionIsCurrsAnc:
            In partition (currentPart::(filterOptionPaddr (completeParentsList currentPart s0)))).
          {
            apply addressesBloodlineIfNotShared with (CPaddr (endAddr (blockrange bentry1) -1)) block1InCurrPartAddr;
              trivial.
            14: rewrite Hs1 in Hcurr; simpl in Hcurr; rewrite Hcurr.
            1,2,3,4,5,6,7,8,9,10,11,12,13,14: unfold consistency in *; unfold consistency1 in *;
              unfold consistency2 in *; intuition.
            - unfold sh1entryAddr in *. rewrite HlookupBlock1s0 in *. subst sh1entryaddr1. assumption.
            - apply addrInBlockIsMapped with block; assumption.
          }
          assert(HbeqPartCurr: partition <> currentPart).
          {
            assert(HnoDupMappedPs0: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
            intro Hcontra. subst partition. pose proof (DisjointPaddrInPart currentPart block1InCurrPartAddr block
              (CPaddr (endAddr (blockrange bentry1)-1)) s0 HnoDupMappedPs0 HcurrIsPDTs0 Hblock1Mappeds0
              HblockMappeds0 HbeqBlock1Block HendMinInBlock1) as Hcontra. congruence.
          }
          simpl in HpartitionIsCurrsAnc.
          destruct HpartitionIsCurrsAnc as [Hcontra | HpartitionIsCurrsAnc]; try(exfalso; congruence).
          assert(Hend1NotInBlock: ~In (endAddr (blockrange bentry1)) (getAllPaddrAux [block] s0)).
          {
            simpl. rewrite HlookupBlock in *. rewrite <-HendBlock. rewrite app_nil_r. intro Hcontra.
            apply getAllPaddrBlockInclRev in Hcontra. destruct Hcontra as (_ & Hcontra & _). lia.
          }
          destruct (beqAddr currentPart constantRootPartM) eqn:HbeqCurrRoot.
          {
            unfold completeParentsList in *. rewrite <-PeanoNat.Nat.add_1_r in HpartitionIsCurrsAnc.
            simpl in HpartitionIsCurrsAnc. rewrite HlookupCurrs0 in *. rewrite HbeqCurrRoot in *. simpl in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. specialize(HparentCurr HbeqCurrRoot).
          destruct HparentCurr as [parentBlock12 [startP [endP (HblockPMapped & HstartP & HendP & HlebStarts &
            HgebEnds)]]].
          assert(Hend1InBlockParent: In (endAddr (blockrange bentry1)) (getAllPaddrAux [parentBlock12] s0)).
          {
            simpl. destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-HstartP. rewrite <-HendP. rewrite app_nil_r.
            apply getAllPaddrBlockIncl; lia.
          }
          assert(HendMinInBP: In (CPaddr (endAddr (blockrange bentry1)-1)) (getAllPaddrAux [parentBlock12] s0)).
          {
            simpl. destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendP.
            apply getAllPaddrBlockIncl; lia.
          }
          assert(HpartitionIsCurrsAncRec:
            In partition ([parent pdentry] ++ filterOptionPaddr (completeParentsList (parent pdentry) s0))).
          {
            assert(HparentOfParts0: parentOfPartitionIsPartition s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            rewrite <-completeParentsListAdd with (pdbasepartition := currentPart); trivial.
            - unfold consistency in *; unfold consistency1 in *; intuition.
            - simpl. specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
              destruct HparentOfParts0 as (HparentIsPart & _). specialize(HparentIsPart HbeqCurrRoot).
              destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HlookupParent.
              split; trivial. split; trivial. exists pdentry. auto.
          }
          apply in_app_or in HpartitionIsCurrsAncRec. simpl in HpartitionIsCurrsAncRec.
          destruct HpartitionIsCurrsAncRec as [Hcontra | HpartitionIsCurrsAncRec].
          {
            destruct Hcontra as [Hcontra | Hcontra]; try(congruence). subst partition.
            destruct (beqAddr block parentBlock12) eqn:HbeqBlockBP.
            - rewrite <-DTL.beqAddrTrue in HbeqBlockBP. subst block. congruence.
            - rewrite <-beqAddrFalse in *. assert(HnoDupMappedPs0: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              pose proof (DisjointPaddrInPart (parent pdentry) block parentBlock12
                (CPaddr (endAddr (blockrange bentry1)-1)) s0 HnoDupMappedPs0 HpartIsPDT HblockMappeds0 HblockPMapped
                HbeqBlockBP HendMinInBlock). congruence.
          }
          assert(HisChilds0: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HPDTIfPDFlags0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HmultIsPDTs0: multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HparentOfParts0: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
          destruct HparentOfParts0 as (HparentIsPart & _). specialize(HparentIsPart HbeqCurrRoot).
          destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
          assert(HparentOfParts0: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockEquivs0: blockInChildHasAtLeastEquivalentBlockInParent s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          pose proof (equivalentAncestorsBlock (parent pdentry) parentBlock12 startP endP partition s0
            HisChilds0 HPDTIfPDFlags0 HmultIsPDTs0 HparentOfParts0 HblockEquivs0 HparentIsPart HpartIsPart
            HpartitionIsCurrsAncRec HstartP HendP HblockPMapped) as HblockBis.
          destruct HblockBis as [blockBis [startBis [endBis (HblockBisMapped & HstartBis & HendBis & HlebStartsBis &
            HgebEndsBis)]]].
          destruct (beqAddr blockBis block) eqn:HbeqBlocks.
          - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockBis. contradict Hend1NotInBlock. simpl.
            unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
            rewrite app_nil_r. rewrite <-HstartBis. rewrite <-HendBis. apply getAllPaddrBlockIncl; lia.
          - rewrite <-beqAddrFalse in *. assert(HnoDupMappedPs0: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            assert(HendMinInBlockBis: In (CPaddr (endAddr (blockrange bentry1)-1)) (getAllPaddrAux [blockBis] s0)).
            {
              simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              destruct (lookup blockBis (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence).
              rewrite app_nil_r. rewrite <-HstartBis. rewrite <-HendBis. apply getAllPaddrBlockIncl; lia.
            }
            pose proof (DisjointPaddrInPart partition blockBis block (CPaddr (endAddr (blockrange bentry1)-1)) s0
              HnoDupMappedPs0 HpartIsPDT HblockBisMapped HblockMappeds0 HbeqBlocks HendMinInBlockBis).
            congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) scnext) eqn:HbeqSce2Next.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSce2Next. rewrite HbeqSce2Next in *. exfalso.
          destruct (lookup scnext (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) scnext) eqn:HbeqSh12Next.
        {
          unfold sh1entryAddr in *. exfalso.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). subst sh1entryaddr2. unfold sh1entryPDchild in *.
          rewrite <-DTL.beqAddrTrue in HbeqSh12Next. rewrite HbeqSh12Next in *.
          destruct (lookup scnext (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2Next. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqCurrNext. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite <-HgetMappedBEqs1s0 in Hblock2NMappeds0; trivial. rewrite <-HgetMappedBEqs2s1 in Hblock2NMappeds0.
        assert(In scnext (getMappedBlocks partition s)).
        {
          destruct (beqAddr currentPart partition) eqn:HbeqParts.
          - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. specialize(HgetMappedBCurrEqss2 scnext).
            destruct HgetMappedBCurrEqss2 as (HgetMappedBCurrEqss2 & _).
            apply HgetMappedBCurrEqss2 in Hblock2NMappeds0.
            destruct Hblock2NMappeds0 as [Hcontra | Hblock2NMappeds]; try(exfalso; congruence). assumption.
          - rewrite <-beqAddrFalse in *. rewrite HgetMappedBNotCurrEqss2; trivial.
        }
        split; trivial. rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr scnext) eqn:HbeqBlock1Next.
        + rewrite <-DTL.beqAddrTrue in HbeqBlock1Next. subst scnext. rewrite HlookupBlock1s0 in *.
          rewrite HnewB. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scnext) eqn:HbeqSce1Next.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1Next. subst scnext. rewrite HlookupSce1s0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END blockAndNextAreSideBySide *)
    }

    assert(parentBlocksBoundsIfNoNext s).
    { (* BEGIN parentBlocksBoundsIfNoNext s *)
      assert(Hcons0: parentBlocksBoundsIfNoNext s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition pdentryPart block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock HendBlock
        Hsce Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEqss2 in *. assert(HpartIsPDTs4: isPDT partition s4).
      {
        assert(isPDT partition s3).
        { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock3Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock3Part. subst partition. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetPartsEqs2s1 in *. rewrite HgetPartsEqs1s0 in *. assert(HpartIsPDTs0: isPDT partition s0).
      { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs8 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists pdentry.
          injection HlookupPart as HpdentriesEq. subst pdentryPart. rewrite Hpdentry3. simpl. rewrite Hpdentry2.
          simpl. rewrite Hpdentry1 in *. auto.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HlookupPart. simpl in *.
          destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock2Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs6 in HlookupPart. simpl in *. exists pdentryPart.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. split; try(split); trivial.
          rewrite Hs4 in HlookupPart. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Part in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqParts in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HlookupPart. simpl in *.
          destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlock1Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqSce1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq in *.
      assert(HblockMappeds0: In block (getMappedBlocks partition s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial.
      }
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs in HstartBlock. rewrite Hs in HendBlock.
      rewrite Hs8 in HstartBlock. rewrite Hs8 in HendBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HstartBlock.
      rewrite Hs7 in HendBlock. simpl in *. destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlock2Block. subst block. exfalso. apply mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite HlookupBlock2Eqss7 in *. rewrite Hs7 in Hlookup.
        simpl in *. rewrite beqAddrTrue in *. injection Hlookup as HbentriesEq. subst bentry. rewrite HnewB3 in Hpres.
        simpl in *. rewrite HnewB2 in Hpres. simpl in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HstartBlock. rewrite Hs6 in HendBlock. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block) eqn:HbeqSce2Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HstartBlock. rewrite Hs5 in HendBlock. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh12Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HstartBlock. rewrite Hs4 in HendBlock. simpl in *. rewrite beqAddrFalse in *.
      rewrite HbeqBlock2Block in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HstartBlock.
      rewrite Hs3 in HendBlock. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
      rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. simpl in *.
      destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
      - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. rewrite HnewB in HstartBlock.
        rewrite HnewB in HendBlock. simpl in *. subst startaddr. subst endaddr. assert(partition = currentPart).
        {
          destruct (beqAddr partition currentPart) eqn:HbeqPartCurr; try(rewrite DTL.beqAddrTrue; assumption).
          exfalso. rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *.
          apply InFilterPresentInList in HblockMappeds0. apply InFilterPresentInList in Hblock1Mappeds0.
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hdisjoint partition currentPart HpartIsPDTs0 HcurrIsPDTs0 HbeqPartCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint block1InCurrPartAddr HblockMappeds0). congruence.
        }
        subst partition. specialize(HparentCurr HbeqPartRoot). rewrite HlookupCurrs0 in HlookupParts0.
        injection HlookupParts0 as HpdentriesEq. subst pdentryParts0.
        destruct HparentCurr as [parentBlock12 [startP [endP (HparentBlockMapped & HstartP & HendP & HlebStarts &
          HgebEnds)]]]. exists parentBlock12. exists startP.
        assert(HlookupBPEqss0: lookup parentBlock12 (memory s) beqAddr = lookup parentBlock12 (memory s0) beqAddr).
        {
          rewrite Hs. rewrite Hs8. simpl. destruct (beqAddr currentPart parentBlock12) eqn:HbeqCurrPB.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrPB. rewrite HbeqCurrPB in *. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
          destruct (beqAddr block2InCurrPartAddr parentBlock12) eqn:HbeqBlock2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2BP. rewrite HbeqBlock2BP in *. exfalso.
            assert(HparentOfParts0: parentOfPartitionIsPartition s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
            destruct HparentOfParts0 as (HparentIsPart & _ & HbeqParentCurr). specialize(HparentIsPart HbeqPartRoot).
            assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
            assert(HparentIsPDT: isPDT (parent pdentry) s0) by (unfold isPDT; rewrite HlookupParent; trivial).
            specialize(Hdisjoint (parent pdentry) currentPart HparentIsPDT HcurrIsPDTs0 HbeqParentCurr).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock2Mappeds0.
            apply InFilterPresentInList in HparentBlockMapped. specialize(Hdisjoint parentBlock12 HparentBlockMapped).
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSce2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2BP. rewrite HbeqSce2BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) parentBlock12) eqn:HbeqSh12BP.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqSh12BP. rewrite HbeqSh12BP in *. unfold sh1entryPDchild in *.
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrPB. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr parentBlock12) eqn:HbeqBlock1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1BP. rewrite HbeqBlock1BP in *. exfalso.
            assert(HparentOfParts0: parentOfPartitionIsPartition s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
            destruct HparentOfParts0 as (HparentIsPart & _ & HbeqParentCurr). specialize(HparentIsPart HbeqPartRoot).
            assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
            assert(HparentIsPDT: isPDT (parent pdentry) s0) by (unfold isPDT; rewrite HlookupParent; trivial).
            specialize(Hdisjoint (parent pdentry) currentPart HparentIsPDT HcurrIsPDTs0 HbeqParentCurr).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock1Mappeds0.
            apply InFilterPresentInList in HparentBlockMapped. specialize(Hdisjoint parentBlock12 HparentBlockMapped).
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSce1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1BP. rewrite HbeqSce1BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        assert(HparentOfParts0: parentOfPartitionIsPartition s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
        destruct HparentOfParts0 as (HparentIsPart & _ & HbeqParentCurr). specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
        assert(HparentIsPDTs0: isPDT (parent pdentry) s0) by (unfold isPDT; rewrite HlookupParent; trivial).
        rewrite HlookupBPEqss0. split; try(split; try(split)); trivial.
        + rewrite <-HgetMappedBEqs1s0 in HparentBlockMapped; trivial. rewrite <-HgetMappedBEqs2s1 in *.
          apply not_eq_sym in HbeqParentCurr. rewrite HgetMappedBNotCurrEqss2; trivial. unfold isPDT.
          rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr (parent pdentry)) eqn:HbeqBlock2Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. rewrite HbeqBlock2Parent in *. unfold bentryAFlag in *.
            rewrite HlookupParent in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite <-HgetPartsEqs1s0 in *. rewrite <-HgetPartsEqs2s1 in *. rewrite <-HgetPartsEqs3s2 in *.
          apply partitionsArePDT; trivial.
        + subst scentryaddr. unfold scentryNext in *. rewrite Hs in Hnext. rewrite Hs8 in Hnext. simpl in *.
          destruct (beqAddr currentPart (CPaddr (block1InCurrPartAddr + scoffset))) eqn:HbeqCurrSce1;
            try(exfalso; congruence). rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in Hnext. simpl in *.
          destruct (beqAddr block2InCurrPartAddr (CPaddr (block1InCurrPartAddr + scoffset))) eqn:HbeqBlock2Sce1;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6 in Hnext. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) (CPaddr (block1InCurrPartAddr + scoffset)))
            eqn:HbeqSces.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSces. apply CPaddrAddEq in HbeqSces; try(exfalso; congruence).
            assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *.
            destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs5 in Hnext. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) (CPaddr (block1InCurrPartAddr + scoffset)))
            eqn:HbeqSh12Sce; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in Hnext. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Sce1 in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hnext. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqCurrSce1 in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in Hnext. simpl in *.
          destruct (beqAddr block1InCurrPartAddr (CPaddr (block1InCurrPartAddr + scoffset))) eqn:HbeqBlock1Sce1;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in Hnext. simpl in *.
          rewrite beqAddrTrue in *. simpl in *. subst block2Next.
          assert(HeqTriv: CPaddr (block2InCurrPartAddr+scoffset) = CPaddr (block2InCurrPartAddr+scoffset)) by trivial.
          specialize(Hcons0 currentPart pdentry block2InCurrPartAddr (CPaddr (block2InCurrPartAddr+scoffset))
            (endAddr (blockrange bentry1)) block2End HpartIsPart Hblock2Mappeds0 Hstart2s0 Hend2s0
            HeqTriv Hnext2s0 HbeqPartRoot HlookupCurrs0).
          destruct Hcons0 as [blockParent [startParent (HblockPMapped & HstartParent & HendParent & HlebStartsBis)]].
          assert(blockParent = parentBlock12).
          {
            destruct (beqAddr blockParent parentBlock12) eqn:HbeqBPs; try(rewrite DTL.beqAddrTrue; assumption).
            exfalso. rewrite <-beqAddrFalse in *.
            assert(HnoDupMappedPs0: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            assert(Hstart2InParent: In (endAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s0)).
            {
              simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartParent. rewrite <-HendParent.
              apply getAllPaddrBlockIncl; lia.
            }
            pose proof (DisjointPaddrInPart (parent pdentry) blockParent parentBlock12 (endAddr (blockrange bentry1))
              s0 HnoDupMappedPs0 HparentIsPDTs0 HblockPMapped HparentBlockMapped HbeqBPs Hstart2InParent) as Hcontra.
            contradict Hcontra. simpl.
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HendP. rewrite <-HstartP.
            assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
            specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
              HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
            apply getAllPaddrBlockIncl; lia.
          }
          subst blockParent. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSce1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        unfold scentryNext in *. rewrite Hs in Hnext. rewrite Hs8 in Hnext. simpl in *. simpl in *.
        destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in Hnext. simpl in *.
        destruct (beqAddr block2InCurrPartAddr scentryaddr) eqn:HbeqBlock2Sce;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces.
        {
          subst scentryaddr.
          rewrite <-DTL.beqAddrTrue in HbeqSces. apply CPaddrAddEq in HbeqSces; try(exfalso; congruence).
          assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *.
          destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs5 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) scentryaddr)
          eqn:HbeqSh12Sce; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in Hnext. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2Sce in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hnext. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqCurrSce in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in Hnext. simpl in *.
        destruct (beqAddr block1InCurrPartAddr scentryaddr) eqn:HbeqBlock1Sce1;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces1.
        {
          subst scentryaddr.
          rewrite <-DTL.beqAddrTrue in HbeqSces1. apply CPaddrAddEq in HbeqSces1; try(exfalso; congruence).
          assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *.
          destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 partition pdentryParts0 block scentryaddr startaddr endaddr HpartIsPart HblockMappeds0
          HstartBlock HendBlock Hsce Hnext HbeqPartRoot HlookupParts0).
        destruct Hcons0 as [blockParent [startP (HblockPMapped & HstartP & HendP & HlebStarts)]].
        assert(HparentOfParts0: parentOfPartitionIsPartition s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HparentOfParts0 partition pdentryParts0 HlookupParts0).
        destruct HparentOfParts0 as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
        assert(HchildPNotNull: exists childP, sh1entryPDchild (CPaddr (blockParent+sh1offset)) childP s0
          /\ childP <> nullAddr).
        {
          assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockPIsBE: isBE blockParent s0).
          {
            unfold isBE. unfold bentryStartAddr in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence). trivial.
          }
          specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *. unfold sh1entryPDchild.
          destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1;
            try(exfalso; congruence). destruct v; try(exfalso; congruence). exists (PDchild s9). split; trivial.
          assert(HchildBlockPropss0: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HpartIsChild: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HparentIsParent: pdentryParent partition (parent pdentryParts0) s0).
          { unfold pdentryParent. rewrite HlookupParts0. reflexivity. }
          specialize(HpartIsChild partition (parent pdentryParts0) HpartIsPart HparentIsParent HbeqPartRoot).
          assert(HPflag: bentryPFlag block true s0).
          {
            apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(HPflagP: bentryPFlag blockParent true s0).
          {
            apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(HgebEnds: endaddr >= endaddr) by lia.
          specialize(HchildBlockPropss0 partition (parent pdentryParts0) block startaddr endaddr blockParent startP
            endaddr HparentIsPart HpartIsChild HblockMappeds0 HstartBlock HendBlock HPflag HblockPMapped HstartP HendP
            HPflagP HlebStarts HgebEnds). destruct HchildBlockPropss0 as (_ & Hres & _). apply Hres.
          unfold sh1entryPDchild. rewrite HlookupSh1. reflexivity.
        }
        destruct HchildPNotNull as [childP (HPDchildP & HbeqPDChildNull)]. exists blockParent. exists startP.
        assert(HlookupBPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr
          /\ block2InCurrPartAddr <> blockParent).
        {
          unfold bentryStartAddr in *. rewrite Hs. rewrite Hs8. simpl.
          destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
          destruct (beqAddr block2InCurrPartAddr blockParent) eqn:HbeqBlock2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2BP. subst blockParent. unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2BP. rewrite HbeqSce2BP in *. exfalso.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          split; trivial.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh12BP.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2. unfold sh1entryPDchild in *.
            rewrite <-DTL.beqAddrTrue in HbeqSh12BP. rewrite HbeqSh12BP in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrBP. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1BP. subst blockParent. unfold sh1entryAddr in *. exfalso.
            rewrite HlookupBlock1s0 in *. subst sh1entryaddr1. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1BP. rewrite HbeqSce1BP in *. exfalso. rewrite HlookupSce1s0 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        destruct HlookupBPEq as (HlookupBPEq & HbeqBlock2BP). rewrite HlookupBPEq. split; auto.
        assert(isPDT (parent pdentryParts0) s0).
        { unfold isPDT. rewrite HlookupParent. trivial. }
        rewrite <-HgetMappedBEqs1s0 in HblockPMapped; trivial. rewrite <-HgetMappedBEqs2s1 in *.
        destruct (beqAddr currentPart (parent pdentryParts0)) eqn:HbeqCurrParent.
        + rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite HbeqCurrParent in *.
          specialize(HgetMappedBCurrEqss2 blockParent). destruct HgetMappedBCurrEqss2 as (Hres & _).
          specialize(Hres HblockPMapped). destruct Hres as [Hcontra | Hres]; try(exfalso; congruence). assumption.
        + rewrite <-beqAddrFalse in *. rewrite HgetMappedBNotCurrEqss2; trivial. unfold isPDT. rewrite Hs4. simpl.
        destruct (beqAddr block2InCurrPartAddr (parent pdentryParts0)) eqn:HbeqBlock2Parent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. rewrite HbeqBlock2Parent in *. rewrite HlookupParent in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite <-HgetPartsEqs1s0 in *. rewrite <-HgetPartsEqs2s1 in *. rewrite <-HgetPartsEqs3s2 in *.
        apply partitionsArePDT; trivial.
      (* END parentBlocksBoundsIfNoNext *)
    }

    assert(isSHE (CPaddr (block2InCurrPartAddr + sh1offset)) s0).
    {
      unfold isBE in *. rewrite HlookupBlock2Eqs1s0 in *. assert(Hres: wellFormedFstShadowIfBlockEntry s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      specialize(Hres block2InCurrPartAddr Hblock2IsBEs1). assumption.
    }

    assert(childLocMappedInChild s).
    { (* BEGIN childLocMappedInChild s *)
      assert(Hcons0: childLocMappedInChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1 HPDchild Hloc
        HbeqIdChildNull Hstart HstartNotKS. rewrite HgetPartsEqss2 in *. assert(HpartIsPDTs4: isPDT part s4).
      {
        assert(isPDT part s3).
        { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock3Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock3Part. subst part. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetPartsEqs2s1 in *. rewrite HgetPartsEqs1s0 in *. assert(HpartIsPDTs0: isPDT part s0).
      { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HblockMappeds0: In block (getMappedBlocks part s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial.
      }
      unfold sh1entryAddr in *. unfold bentryStartAddr in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s2) beqAddr).
      {
        rewrite Hs in Hsh1. rewrite Hs8 in Hsh1. rewrite Hs. rewrite Hs8. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in Hsh1. rewrite Hs7.
        simpl in *. destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Block. subst block. exfalso. apply mappedBlockIsBE in HblockMapped.
          destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite HlookupBlock2Eqss7 in *.
          rewrite Hs7 in Hlookup. simpl in *. rewrite beqAddrTrue in *. injection Hlookup as HbentriesEq.
          subst bentry. rewrite HnewB3 in Hpres. simpl in *. rewrite HnewB2 in Hpres. simpl in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in Hsh1. rewrite Hs6. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block) eqn:HbeqSce2Block;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs5 in Hsh1. rewrite Hs5. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh12Block;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs4 in Hsh1. rewrite Hs4. simpl in *. rewrite beqAddrFalse in *.
        rewrite HbeqBlock2Block in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hsh1. rewrite Hs3.
        simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupBlockEq in *. assert(Hblocks0: sh1entryAddr block sh1entryaddr s0
        /\ bentryStartAddr block startaddr s0).
      {
        unfold sh1entryAddr. unfold bentryStartAddr. rewrite Hs2 in Hsh1. rewrite Hs2 in Hstart. simpl in *.
        destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in Hstart. simpl in *.
          rewrite HlookupBlock1s0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in Hsh1. rewrite Hs1 in Hstart. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct Hblocks0 as (Hsh1s0 & Hstarts0). unfold sh1entryInChildLocationWeak in *.
      unfold sh1entryPDchild in *. rewrite Hs in HPDchild. rewrite Hs in Hloc. rewrite Hs8 in HPDchild.
      rewrite Hs8 in Hloc. simpl in *. rewrite beqAddrTrue in *.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HPDchild. rewrite Hs7 in Hloc.
      simpl in *. destruct (beqAddr block2InCurrPartAddr sh1entryaddr) eqn:HbeqBlock2Sh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HPDchild. rewrite Hs6 in Hloc. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSceSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDchild. rewrite Hs5 in Hloc.
      simpl in *. destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) sh1entryaddr) eqn:Hsh1s.
      { simpl in *. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HPDchild. rewrite Hs4 in Hloc. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Sh1 in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HPDchild. rewrite Hs3 in Hloc. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrSh1 in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HPDchild. rewrite Hs2 in Hloc. simpl in *.
      destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlock1Sh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HPDchild. rewrite Hs1 in Hloc. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSce1Sh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (*assert(Hlocs0: sh1entryInChildLocation sh1entryaddr blockChild s0).
      {
        unfold sh1entryInChildLocation. destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). destruct Hloc as (Hloc & HlocIsBE). split; trivial. intro HbeqBCNull.
        specialize(HlocIsBE HbeqBCNull). unfold isBE in *. simpl in *. rewrite beqAddrTrue in *.
        destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        destruct (beqAddr block2InCurrPartAddr currentPart) eqn:HbeqBlock2Curr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlock2Curr. rewrite HbeqBlock2Curr in *. exfalso; congruence. }
        simpl in *. clear Hloc. destruct (beqAddr block2InCurrPartAddr blockChild) eqn:HbeqBlock2BC.
        - rewrite <-DTL.beqAddrTrue in HbeqBlock2BC. subst blockChild. rewrite <-HlookupBlock2Eqs1s0. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) block2InCurrPartAddr) eqn:HbeqSce2Block2.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2Block2. rewrite HbeqSce2Block2 in *. unfold scentryNext in *.
            exfalso. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          simpl in *. destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockChild) eqn:HbeqSce2BC;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) (CPaddr (block2InCurrPartAddr + scoffset)))
            eqn:HbeqSh12Sce2.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSh12Sce2. rewrite HbeqSh12Sce2 in *. unfold isSHE in *.
            unfold scentryNext in *. exfalso.
            destruct (lookup (CPaddr (block2InCurrPartAddr + scoffset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          simpl in *. destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockChild) eqn:HbeqSh1BC;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          destruct (beqAddr block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + sh1offset))) eqn:HbeqBlock2Sh12.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Sh12. rewrite <-HbeqBlock2Sh12 in *. unfold isSHE in *. exfalso.
            rewrite HlookupSh12Eqs1s0 in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2BC in *. rewrite beqAddrSym in HbeqBlock2Curr.
          rewrite HbeqBlock2Curr in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in *. rewrite beqAddrFalse in *.
          rewrite HbeqCurrBC in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          destruct (beqAddr block1InCurrPartAddr currentPart) eqn:HbeqBlock1Curr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1Curr. rewrite HbeqBlock1Curr in *. exfalso; congruence.
          }
          simpl in *. destruct (beqAddr block1InCurrPartAddr blockChild) eqn:HbeqBlock1BC.
          + rewrite <-DTL.beqAddrTrue in HbeqBlock1BC. subst blockChild. rewrite HlookupBlock1s0. trivial.
          + destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block1InCurrPartAddr) eqn:HbeqSce1Block1.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSce1Block1. rewrite HbeqSce1Block1 in *. exfalso; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in *.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) blockChild) eqn:HbeqSce1BC;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }*)
      assert(HstartNotKSs0: ~isKS startaddr s0).
      {
        contradict HstartNotKS. unfold isKS in *. rewrite Hs. rewrite Hs8. simpl. rewrite beqAddrTrue.
        destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart.
        { rewrite <-DTL.beqAddrTrue in HbeqCurrStart. subst startaddr. rewrite HlookupCurrs0 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
        destruct (lookup startaddr (memory s0) beqAddr) eqn:HlookupStarts0; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        assert(Hlookups3: exists bentrys3, lookup startaddr (memory s3) beqAddr = Some(BE bentrys3)
          /\ blockindex b = blockindex bentrys3).
        {
          rewrite Hs3. simpl. rewrite beqAddrFalse in *. rewrite HbeqCurrStart.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          destruct (beqAddr block1InCurrPartAddr startaddr) eqn:HbeqBlock1Start.
          - rewrite <-DTL.beqAddrTrue in HbeqBlock1Start. subst startaddr. rewrite HlookupBlock1s0 in *.
            injection HlookupStarts0 as HbentriesEq. subst b. exists (CBlockEntry (read bentry1) (write bentry1)
              (exec bentry1) (present bentry1) (accessible bentry1) (blockindex bentry1)
              (CBlock (startAddr (blockrange bentry1)) block2End)). rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1.
            simpl. destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) startaddr) eqn:HbeqSce1Start.
            { rewrite <-DTL.beqAddrTrue in HbeqSce1Start. subst startaddr. exfalso; congruence. }
            exists b. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
        }
        destruct Hlookups3 as [bentrys3 (HlookupStarts3 & HidxEq)]. rewrite HidxEq in *.
        destruct (beqAddr block2InCurrPartAddr startaddr) eqn:HbeqBlock2Start.
        - rewrite <-DTL.beqAddrTrue in HbeqBlock2Start. subst startaddr. rewrite HnewB3. simpl. rewrite HnewB2. simpl.
          unfold bentryBlockIndex in *. rewrite HlookupStarts3 in *. subst blockToFreeIdx. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) startaddr) eqn:HbeqSce2Start.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2Start. subst startaddr. unfold scentryNext in *.
            rewrite HlookupStarts0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh12Start.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSh12Start. subst startaddr. unfold isSHE in *.
            rewrite HlookupStarts0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Start. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupStarts3. assumption.
      }
      specialize(Hcons0 part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMappeds0 Hsh1s0
        HPDchild Hloc HbeqIdChildNull Hstarts0 HstartNotKSs0).
      destruct Hcons0 as (HbeqBCNull & HBCMapped & HstartChild). split; trivial.
      assert(HbeqBlock2BC: block2InCurrPartAddr <> blockChild).
      {
        intro. subst blockChild. assert(idchild = currentPart).
        {
          destruct (beqAddr idchild currentPart) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock2Mappeds0.
          apply InFilterPresentInList in HBCMapped. assert(HchildIsPDT: isPDT idchild s0).
          {
            unfold getKSEntries in *. unfold isPDT.
            destruct (lookup idchild (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          assert(HcurrIsPDT: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
          specialize(Hdisjoint idchild currentPart HchildIsPDT HcurrIsPDT HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint block2InCurrPartAddr HBCMapped). congruence.
        }
        subst idchild. assert(HchildIsChild: pdchildIsPDT s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HchildIsChild part block sh1entryaddr currentPart HpartBisIsPart HblockMappeds0 Hsh1s0 HPDchild
          HbeqIdChildNull).
        assert(HisParent: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HisParent currentPart part HpartBisIsPart HchildIsChild). unfold pdentryParent in *.
        rewrite HlookupCurrs0 in *. assert(HbeqCurrRoot: currentPart <> constantRootPartM).
        {
          intro Hcontra. assert(HparentOfPart: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfPart currentPart pdentry HlookupCurrs0).
          destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot Hcontra).
          rewrite HparentOfRoot in *. subst part. assert(isPADDR nullAddr s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition). unfold isPDT in *. unfold isPADDR in *.
          destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        assert(HparentBlock: nextImpliesBlockWasCut s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HcurrIsPart: In currentPart (getPartitions multiplexer s0)).
        {
          apply childrenPartitionInPartitionList with part; trivial; unfold consistency in *;
            unfold consistency1 in *; intuition.
        }
        assert(HeqTriv: CPaddr (block1InCurrPartAddr+scoffset) = CPaddr (block1InCurrPartAddr+scoffset)) by trivial.
        unfold bentryEndAddr in *. rewrite <-HlookupBlock1s0 in *. rewrite HlookupBlock1s1 in *.
        specialize(HparentBlock currentPart pdentry block1InCurrPartAddr (CPaddr (block1InCurrPartAddr+scoffset))
          block2InCurrPartAddr (endAddr (blockrange bentry1)) HcurrIsPart HlookupCurrs0 Hblock1Mappeds0 Hend1s1
          HeqTriv HbeqBCNull Hnext1s0 HbeqCurrRoot). rewrite <-HisParent in *.
        destruct HparentBlock as [blockParent [endP (HblockPMapped & HendP & HltEndsP & Hincl)]].
        assert(HstartBlock: bentryStartAddr block (endAddr (blockrange bentry1)) s0).
        {
          unfold bentryStartAddr in *.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-Hstart2s0 in *. subst startaddr. assumption.
        }
        assert(HendInBlock: In (endAddr (blockrange bentry1)) (getAllPaddrAux [block] s0)).
        {
          assert(HendBlock: exists endaddr, bentryEndAddr block endaddr s0).
          {
            unfold bentryEndAddr. unfold sh1entryAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
          }
          destruct HendBlock as [endaddr HendBlock].
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HPflag: bentryPFlag block true s0).
          {
            apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          specialize(Hwell block (endAddr (blockrange bentry1)) endaddr HPflag HstartBlock HendBlock).
          destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup block (memory s0) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
          rewrite app_nil_r. rewrite <-HstartBlock. rewrite <-HendBlock. apply getAllPaddrBlockIncl; lia.
        }
        assert(HstartP: exists startP, bentryStartAddr blockParent startP s0).
        {
          unfold bentryStartAddr. unfold bentryEndAddr in *.
          destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
        }
        destruct HstartP as [startP HstartP].
        assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition). rewrite <-HlookupBlock1s1 in *.
        specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
          HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
        assert(startP <= startAddr (blockrange bentry1)).
        {
          assert(HstartIn1: In (startAddr (blockrange bentry1)) (getAllPaddrAux [block1InCurrPartAddr] s0)).
          {
            simpl. unfold bentryStartAddr in *. rewrite <-HlookupBlock1s1.
            destruct (lookup block1InCurrPartAddr (memory s1) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-Hstart1s1. rewrite <-Hend1s1.
            apply getAllPaddrBlockIncl; lia.
          }
          specialize(Hincl (startAddr (blockrange bentry1)) HstartIn1). simpl in *. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite app_nil_r in *. rewrite <-HstartP in *. rewrite <-HendP in *.
          apply getAllPaddrBlockInclRev in Hincl. destruct Hincl. assumption.
        }
        assert(HendInBlockP: In (endAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s0)).
        {
          unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
          destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendP.
          apply getAllPaddrBlockIncl; lia.
        }
        destruct (beqAddr blockParent block) eqn:HbeqBPs.
        - rewrite <-DTL.beqAddrTrue in HbeqBPs. subst block. unfold bentryStartAddr in *.
          destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          rewrite <-HstartBlock in *. subst startP. lia.
        - rewrite <-beqAddrFalse in *. assert(HnoDupMappedPs0: noDupMappedPaddrList s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          pose proof (DisjointPaddrInPart part blockParent block (endAddr (blockrange bentry1)) s0 HnoDupMappedPs0
            HpartIsPDTs0 HblockPMapped HblockMappeds0 HbeqBPs HendInBlockP). congruence.
      }
      split.
      - assert(isPDT idchild s0).
        {
          unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
          destruct (lookup idchild (memory s0) beqAddr); try(simpl in *; congruence).
          destruct v; try(simpl in *; congruence). trivial.
        }
        rewrite <-HgetMappedBEqs1s0 in HBCMapped; trivial. rewrite <-HgetMappedBEqs2s1 in *.
        destruct (beqAddr currentPart idchild) eqn:HbeqParts.
        + rewrite <-DTL.beqAddrTrue in HbeqParts. subst idchild. specialize(HgetMappedBCurrEqss2 blockChild).
          destruct HgetMappedBCurrEqss2 as (HgetMappedBCurrEqss2 & _). apply HgetMappedBCurrEqss2 in HBCMapped.
          destruct HBCMapped; try(exfalso; congruence). assumption.
        + rewrite <-beqAddrFalse in *. rewrite HgetMappedBNotCurrEqss2; trivial. unfold isPDT in *.
          unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite Hs4. simpl.
          destruct (beqAddr block2InCurrPartAddr idchild) eqn:HbeqBlock2Child.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Child. subst idchild.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqParts. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup idchild (memory s2) beqAddr); try(simpl in *; congruence).
          destruct v; try(simpl in *; congruence). trivial.
      - unfold bentryStartAddr in *. rewrite Hs. rewrite Hs8. simpl.
        rewrite beqAddrTrue. destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC.
        { rewrite <-DTL.beqAddrTrue in HbeqCurrBC. subst blockChild. rewrite HlookupCurrs0 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqBlock2BC. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite Hs6. simpl. destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockChild) eqn:HbeqSceBC.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceBC. rewrite HbeqSceBC in *. unfold scentryNext in *.
          destruct (lookup blockChild (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockChild) eqn:HbeqSh1BC.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1BC. rewrite HbeqSh1BC in *. unfold isSHE in *.
          destruct (lookup blockChild (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2BC. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqCurrBC. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr blockChild) eqn:HbeqBlock1BC.
        + rewrite <-DTL.beqAddrTrue in HbeqBlock1BC. subst blockChild. rewrite HlookupBlock1s0 in *. rewrite HnewB.
          auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockChild) eqn:HbeqSce1BC.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1BC. rewrite HbeqSce1BC in *. unfold scentryNext in *.
            destruct (lookup blockChild (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END childLocMappedInChild *)
    }

    assert(childLocHasSameStart s).
    { (* BEGIN childLocHasSameStart s *)
      assert(Hcons0: childLocHasSameStart s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1 HPDchild Hloc
        HbeqIdChildNull HbeqBCNull startaddr Hstart. rewrite HgetPartsEqss2 in *. assert(HpartIsPDTs4: isPDT part s4).
      {
        assert(isPDT part s3).
        { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr part) eqn:HbeqBlock3Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock3Part. subst part. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetPartsEqs2s1 in *. rewrite HgetPartsEqs1s0 in *. assert(HpartIsPDTs0: isPDT part s0).
      { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HblockMappeds0: In block (getMappedBlocks part s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial.
      }
      unfold sh1entryAddr in *. unfold bentryStartAddr in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s2) beqAddr).
      {
        rewrite Hs in Hsh1. rewrite Hs8 in Hsh1. rewrite Hs. rewrite Hs8. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in Hsh1. rewrite Hs7.
        simpl in *. destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2Block. subst block. exfalso. apply mappedBlockIsBE in HblockMapped.
          destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite HlookupBlock2Eqss7 in *.
          rewrite Hs7 in Hlookup. simpl in *. rewrite beqAddrTrue in *. injection Hlookup as HbentriesEq.
          subst bentry. rewrite HnewB3 in Hpres. simpl in *. rewrite HnewB2 in Hpres. simpl in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in Hsh1. rewrite Hs6. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block) eqn:HbeqSce2Block;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs5 in Hsh1. rewrite Hs5. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh12Block;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs4 in Hsh1. rewrite Hs4. simpl in *. rewrite beqAddrFalse in *.
        rewrite HbeqBlock2Block in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hsh1. rewrite Hs3.
        simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupBlockEq in *. assert(Hblocks0: sh1entryAddr block sh1entryaddr s0
        /\ bentryStartAddr block startaddr s0).
      {
        unfold sh1entryAddr. unfold bentryStartAddr. rewrite Hs2 in Hsh1. rewrite Hs2 in Hstart. simpl in *.
        destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in Hstart. simpl in *.
          rewrite HlookupBlock1s0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in Hsh1. rewrite Hs1 in Hstart. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSceBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct Hblocks0 as (Hsh1s0 & Hstarts0). unfold sh1entryInChildLocationWeak in *.
      unfold sh1entryPDchild in *. rewrite Hs in HPDchild. rewrite Hs in Hloc. rewrite Hs8 in HPDchild.
      rewrite Hs8 in Hloc. simpl in *. rewrite beqAddrTrue in *.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HPDchild. rewrite Hs7 in Hloc.
      simpl in *. destruct (beqAddr block2InCurrPartAddr sh1entryaddr) eqn:HbeqBlock2Sh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HPDchild. rewrite Hs6 in Hloc. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSceSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDchild. rewrite Hs5 in Hloc.
      simpl in *. destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) sh1entryaddr) eqn:Hsh1s.
      { simpl in *. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HPDchild. rewrite Hs4 in Hloc. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Sh1 in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HPDchild. rewrite Hs3 in Hloc. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrSh1 in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HPDchild. rewrite Hs2 in Hloc. simpl in *.
      destruct (beqAddr block1InCurrPartAddr sh1entryaddr) eqn:HbeqBlock1Sh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HPDchild. rewrite Hs1 in Hloc. simpl in *.
      destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) sh1entryaddr) eqn:HbeqSce1Sh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMappeds0 Hsh1s0
        HPDchild Hloc HbeqIdChildNull HbeqBCNull startaddr Hstarts0).
      assert(HbeqBlock2BC: block2InCurrPartAddr <> blockChild).
      {
        intro. subst blockChild. assert(HstartNotKSs0: ~isKS startaddr s0).
        {
          assert(HkernsNotAcc: kernelsAreNotAccessible s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition). intro Hcontra.
          specialize(HkernsNotAcc block2InCurrPartAddr startaddr Hcons0 HPflag2s0 Hcontra).
          unfold bentryAFlag in *. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        assert(HchildLoc: childLocMappedInChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
        specialize(HchildLoc part block sh1entryaddr block2InCurrPartAddr idchild startaddr HpartBisIsPart
          HblockMappeds0 Hsh1s0 HPDchild Hloc HbeqIdChildNull Hstarts0 HstartNotKSs0).
        destruct HchildLoc as (_ & HBCMapped & _).
        assert(idchild = currentPart).
        {
          destruct (beqAddr idchild currentPart) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock2Mappeds0.
          apply InFilterPresentInList in HBCMapped. assert(HchildIsPDT: isPDT idchild s0).
          {
            unfold getKSEntries in *. unfold isPDT.
            destruct (lookup idchild (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          assert(HcurrIsPDT: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
          specialize(Hdisjoint idchild currentPart HchildIsPDT HcurrIsPDT HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint block2InCurrPartAddr HBCMapped). congruence.
        }
        subst idchild. assert(HchildIsChild: pdchildIsPDT s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HchildIsChild part block sh1entryaddr currentPart HpartBisIsPart HblockMappeds0 Hsh1s0 HPDchild
          HbeqIdChildNull).
        assert(HisParent: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HisParent currentPart part HpartBisIsPart HchildIsChild). unfold pdentryParent in *.
        rewrite HlookupCurrs0 in *. assert(HbeqCurrRoot: currentPart <> constantRootPartM).
        {
          intro Hcontra. assert(HparentOfPart: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfPart currentPart pdentry HlookupCurrs0).
          destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot Hcontra).
          rewrite HparentOfRoot in *. subst part. assert(isPADDR nullAddr s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition). unfold isPDT in *. unfold isPADDR in *.
          destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        assert(HparentBlock: nextImpliesBlockWasCut s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HcurrIsPart: In currentPart (getPartitions multiplexer s0)).
        {
          apply childrenPartitionInPartitionList with part; trivial; unfold consistency in *;
            unfold consistency1 in *; intuition.
        }
        assert(HeqTriv: CPaddr (block1InCurrPartAddr+scoffset) = CPaddr (block1InCurrPartAddr+scoffset)) by trivial.
        unfold bentryEndAddr in *. rewrite <-HlookupBlock1s0 in *. rewrite HlookupBlock1s1 in *.
        specialize(HparentBlock currentPart pdentry block1InCurrPartAddr (CPaddr (block1InCurrPartAddr+scoffset))
          block2InCurrPartAddr (endAddr (blockrange bentry1)) HcurrIsPart HlookupCurrs0 Hblock1Mappeds0 Hend1s1
          HeqTriv HbeqBCNull Hnext1s0 HbeqCurrRoot). rewrite <-HisParent in *.
        destruct HparentBlock as [blockParent [endP (HblockPMapped & HendP & HltEndsP & Hincl)]].
        assert(HstartBlock: bentryStartAddr block (endAddr (blockrange bentry1)) s0).
        {
          unfold bentryStartAddr in *.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-Hstart2s0 in *. subst startaddr. assumption.
        }
        assert(HendInBlock: In (endAddr (blockrange bentry1)) (getAllPaddrAux [block] s0)).
        {
          assert(HendBlock: exists endaddr, bentryEndAddr block endaddr s0).
          {
            unfold bentryEndAddr. unfold sh1entryAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
          }
          destruct HendBlock as [endaddr HendBlock].
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HPflag: bentryPFlag block true s0).
          {
            apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          specialize(Hwell block (endAddr (blockrange bentry1)) endaddr HPflag HstartBlock HendBlock).
          destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup block (memory s0) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
          rewrite app_nil_r. rewrite <-HstartBlock. rewrite <-HendBlock. apply getAllPaddrBlockIncl; lia.
        }
        assert(HstartP: exists startP, bentryStartAddr blockParent startP s0).
        {
          unfold bentryStartAddr. unfold bentryEndAddr in *.
          destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
        }
        destruct HstartP as [startP HstartP].
        assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition). rewrite <-HlookupBlock1s1 in *.
        specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
          HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
        assert(startP <= startAddr (blockrange bentry1)).
        {
          assert(HstartIn1: In (startAddr (blockrange bentry1)) (getAllPaddrAux [block1InCurrPartAddr] s0)).
          {
            simpl. unfold bentryStartAddr in *. rewrite <-HlookupBlock1s1.
            destruct (lookup block1InCurrPartAddr (memory s1) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-Hstart1s1. rewrite <-Hend1s1.
            apply getAllPaddrBlockIncl; lia.
          }
          specialize(Hincl (startAddr (blockrange bentry1)) HstartIn1). simpl in *. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite app_nil_r in *. rewrite <-HstartP in *. rewrite <-HendP in *.
          apply getAllPaddrBlockInclRev in Hincl. destruct Hincl. assumption.
        }
        assert(HendInBlockP: In (endAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s0)).
        {
          unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
          destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendP.
          apply getAllPaddrBlockIncl; lia.
        }
        destruct (beqAddr blockParent block) eqn:HbeqBPs.
        - rewrite <-DTL.beqAddrTrue in HbeqBPs. subst block. unfold bentryStartAddr in *.
          destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          rewrite <-HstartBlock in *. subst startP. lia.
        - rewrite <-beqAddrFalse in *. assert(HnoDupMappedPs0: noDupMappedPaddrList s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          pose proof (DisjointPaddrInPart part blockParent block (endAddr (blockrange bentry1)) s0 HnoDupMappedPs0
            HpartIsPDTs0 HblockPMapped HblockMappeds0 HbeqBPs HendInBlockP). congruence.
      }
      unfold bentryStartAddr in *. rewrite Hs. rewrite Hs8. simpl.
      rewrite beqAddrTrue. destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrBC. subst blockChild. rewrite HlookupCurrs0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqBlock2BC. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite Hs6. simpl. destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockChild) eqn:HbeqSceBC.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceBC. rewrite HbeqSceBC in *. unfold scentryNext in *.
        destruct (lookup blockChild (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockChild) eqn:HbeqSh1BC.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1BC. rewrite HbeqSh1BC in *. unfold isSHE in *.
        destruct (lookup blockChild (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqBlock2BC. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqCurrBC. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr blockChild) eqn:HbeqBlock1BC.
      + rewrite <-DTL.beqAddrTrue in HbeqBlock1BC. subst blockChild. rewrite HlookupBlock1s0 in *. rewrite HnewB.
        auto.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockChild) eqn:HbeqSce1BC.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSce1BC. rewrite HbeqSce1BC in *. unfold scentryNext in *.
          destruct (lookup blockChild (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END childLocHasSameStart *)
    }
    unfold consistency2. intuition.
  }

  assert(Hconsists: consistency s).
  {
    destruct HnewB as [l0 [l1 HnewB]]. destruct HnewB2 as [l2 [l3 HnewB2]]. destruct HnewB3 as [l4 [l5 HnewB3]].
    unfold consistency. unfold consistency1. unfold cons1Free in *. intuition.
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition). intros pdparent child block startChild
        endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild.
      rewrite HgetPartsEqss2 in *. assert(isPDT pdparent s3).
      { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
      assert(isPDT pdparent s4).
      {
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr pdparent) eqn:HbeqBlock3Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock3Part. subst pdparent. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetPartsEqs2s1 in *. assert(isPDT pdparent s1).
      { apply partitionsArePDT; unfold consistency1 in *; intuition. }
      rewrite HgetPartsEqs1s0 in *. assert(HparentIsPDTs0: isPDT pdparent s0).
      { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
      rewrite HgetChildrenEqss2 in HchildIsChild; trivial. assert(isPDT child s4).
      {
        assert(isPDT child s2).
        { apply childrenArePDT with pdparent; unfold consistency1 in *; intuition. }
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr child) eqn:HbeqBlock3Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock3Part. subst child. unfold isBE in *.
          destruct (lookup block2InCurrPartAddr (memory s2) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr currentPart child) eqn:HbeqCurrChild; trivial.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetChildrenEqs2s1 in HchildIsChild; trivial. rewrite HgetChildrenEqs1s0 in HchildIsChild; trivial.
      assert(HchildIsPDTs0: isPDT child s0).
      { apply childrenArePDT with pdparent; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HblockMappedChilds0: In block (getMappedBlocks child s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart child) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst child. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial.
      }
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartChild.
      rewrite Hs in HendChild. rewrite Hs in HPflagChild. rewrite Hs8 in HstartChild. rewrite Hs8 in HendChild.
      rewrite Hs8 in HPflagChild. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HstartChild.
      rewrite Hs7 in HendChild. rewrite Hs7 in HPflagChild. simpl in *.
      destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlock2Block. subst block. exfalso. rewrite HnewB3 in HPflagChild. simpl in *.
        rewrite HnewB2 in HPflagChild. simpl in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs6 in HstartChild. rewrite Hs6 in HendChild. rewrite Hs6 in HPflagChild. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) block) eqn:HbeqSce2Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HstartChild. rewrite Hs5 in HendChild. rewrite Hs5 in HPflagChild. simpl in *.
      destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh12Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HstartChild. rewrite Hs4 in HendChild. rewrite Hs4 in HPflagChild. simpl in *.
      rewrite beqAddrFalse in *. rewrite HbeqBlock2Block in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HstartChild.
      rewrite Hs3 in HendChild. rewrite Hs3 in HPflagChild. simpl in *. rewrite beqAddrFalse in *.
      rewrite HbeqCurrBlock in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
      rewrite Hs2 in HstartChild. rewrite Hs2 in HendChild. rewrite Hs2 in HPflagChild. simpl in *.
      destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
      - rewrite HnewB in HstartChild. rewrite HnewB in HendChild. simpl in *. subst startChild. subst endChild.
        rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. assert(child = currentPart).
        {
          destruct (beqAddr child currentPart) eqn:HbeqChildCurr; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *.
          specialize(Hdisjoint child currentPart HchildIsPDTs0 HcurrIsPDTs0 HbeqChildCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          apply InFilterPresentInList in HblockMappedChilds0. apply InFilterPresentInList in Hblock1Mappeds0.
          specialize(Hdisjoint block1InCurrPartAddr HblockMappedChilds0). congruence.
        }
        subst child. assert(Hparent: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(Hparent currentPart pdparent HparentIsPart HchildIsChild). unfold pdentryParent in *.
        rewrite HlookupCurrs0 in *. subst pdparent. assert(HparentOfParts0: parentOfPartitionIsPartition s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
        destruct HparentOfParts0 as (HparentCIsPart & HparentOfRoot & HbeqParentCurr).
        assert(HbeqCurrRoot: currentPart <> constantRootPartM).
        {
          intro Hcontra. specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *. unfold isPDT in *.
          assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        specialize(HparentCurr HbeqCurrRoot). destruct HparentCurr as [parentBlock12 [startP [endP (HblockPMapped &
          HstartP & HendP & Hbounds)]]]. exists parentBlock12. exists startP. exists endP.
        specialize(HparentCIsPart HbeqCurrRoot).
        destruct HparentCIsPart as ([parentEntry HlookupParent] & HparentCIsPart).
        assert(HlookupBPEqss0: lookup parentBlock12 (memory s) beqAddr = lookup parentBlock12 (memory s0) beqAddr).
        {
          rewrite Hs. rewrite Hs8. simpl. destruct (beqAddr currentPart parentBlock12) eqn:HbeqCurrPB.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrPB. rewrite HbeqCurrPB in *. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
          destruct (beqAddr block2InCurrPartAddr parentBlock12) eqn:HbeqBlock2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2BP. rewrite HbeqBlock2BP in *. exfalso.
            assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HparentIsPDT: isPDT (parent pdentry) s0) by (unfold isPDT; rewrite HlookupParent; trivial).
            specialize(Hdisjoint (parent pdentry) currentPart HparentIsPDT HcurrIsPDTs0 HbeqParentCurr).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock2Mappeds0.
            apply InFilterPresentInList in HblockPMapped. specialize(Hdisjoint parentBlock12 HblockPMapped).
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSce2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2BP. rewrite HbeqSce2BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) parentBlock12) eqn:HbeqSh12BP.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqSh12BP. rewrite HbeqSh12BP in *. unfold sh1entryPDchild in *.
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrPB. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr parentBlock12) eqn:HbeqBlock1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1BP. rewrite HbeqBlock1BP in *. exfalso.
            assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HparentIsPDT: isPDT (parent pdentry) s0) by (unfold isPDT; rewrite HlookupParent; trivial).
            specialize(Hdisjoint (parent pdentry) currentPart HparentIsPDT HcurrIsPDTs0 HbeqParentCurr).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            unfold getMappedBlocks in *. apply InFilterPresentInList in Hblock1Mappeds0.
            apply InFilterPresentInList in HblockPMapped. specialize(Hdisjoint parentBlock12 HblockPMapped).
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) parentBlock12) eqn:HbeqSce1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1BP. rewrite HbeqSce1BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupBPEqss0. split; auto. rewrite <-HgetMappedBEqs1s0 in HblockPMapped; trivial.
        rewrite <-HgetMappedBEqs2s1 in HblockPMapped. apply not_eq_sym in HbeqParentCurr.
        rewrite HgetMappedBNotCurrEqss2; trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HstartChild. rewrite Hs1 in HendChild. rewrite Hs1 in HPflagChild. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSce1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild
          HblockMappedChilds0 HstartChild HendChild HPflagChild).
        destruct Hcons0 as [blockParent [startParent [endParent (HblockPMapped & HstartP & HendP & Hbounds)]]].
        exists blockParent. exists startParent. exists endParent.
        assert(HPDchildPs0: exists childPD, sh1entryPDchild (CPaddr (blockParent+sh1offset)) childPD s0
          /\ childPD <> nullAddr).
        {
          assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockPIsBE: isBE blockParent s0).
          {
            unfold isBE. unfold bentryStartAddr in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            trivial.
          }
          specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *. unfold sh1entryPDchild.
          destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1;
            try(exfalso; congruence). destruct v; try(exfalso; congruence). exists (PDchild s9). split; trivial.
          assert(Hres: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          destruct Hbounds as (HlebStarts & HgebEnds).
          assert(HPflagP: bentryPFlag blockParent true s0).
          {
            apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          specialize(Hres child pdparent block startChild endChild blockParent startParent endParent HparentIsPart
            HchildIsChild HblockMappedChilds0 HstartChild HendChild HPflagChild HblockPMapped HstartP HendP
            HPflagP HlebStarts HgebEnds). destruct Hres as (_ & Hres & _). apply Hres. unfold sh1entryPDchild.
          rewrite HlookupSh1. reflexivity.
        }
        destruct HPDchildPs0 as [childPD (HPDchildPs0 & HbeqChilPdNull)].
        assert(HlookupBPEqss0: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr
          /\ block2InCurrPartAddr <> blockParent).
        {
          unfold bentryEndAddr in *. rewrite Hs. rewrite Hs8. simpl.
          destruct (beqAddr currentPart blockParent) eqn:HbeqCurrPB.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrPB. rewrite HbeqCurrPB in *. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl.
          destruct (beqAddr block2InCurrPartAddr blockParent) eqn:HbeqBlock2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2BP. rewrite HbeqBlock2BP in *. exfalso. unfold sh1entryAddr in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          split; trivial.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2BP. rewrite HbeqSce2BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh12BP.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqSh12BP. rewrite HbeqSh12BP in *. unfold sh1entryPDchild in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrPB. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1BP. rewrite HbeqBlock1BP in *. exfalso. unfold sh1entryAddr in *.
            rewrite HlookupBlock1s0 in *. subst sh1entryaddr1. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1BP. rewrite HbeqSce1BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        destruct HlookupBPEqss0 as (HlookupBPEqss0 & HbeqBlock2BP).
        rewrite HlookupBPEqss0. split; auto. rewrite <-HgetMappedBEqs1s0 in HblockPMapped; trivial.
        rewrite <-HgetMappedBEqs2s1 in HblockPMapped.
        destruct (beqAddr currentPart pdparent) eqn:HbeqCurrParent.
        + rewrite <-DTL.beqAddrTrue in HbeqCurrParent. subst pdparent. specialize(HgetMappedBCurrEqss2 blockParent).
          destruct HgetMappedBCurrEqss2 as (Hres & _). specialize(Hres HblockPMapped).
          destruct Hres as [Hcontra | Hres]; try(exfalso; congruence). assumption.
        + rewrite <-beqAddrFalse in *. rewrite HgetMappedBNotCurrEqss2; trivial.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEqss2 in *. assert(HpartIsPDTs4: isPDT partition s4).
      {
        assert(isPDT partition s3).
        { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock3Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock3Part. subst partition. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetPartsEqs2s1 in *. rewrite HgetPartsEqs1s0 in *. assert(HpartIsPDTs0: isPDT partition s0).
      { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs8 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists pdentry.
          injection HlookupPart as HpdentriesEq. subst pdentryPart. rewrite Hpdentry3. simpl. rewrite Hpdentry2.
          simpl. rewrite Hpdentry1 in *. auto.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HlookupPart. simpl in *.
          destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock2Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs6 in HlookupPart. simpl in *. exists pdentryPart.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. split; try(split); trivial.
          rewrite Hs4 in HlookupPart. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Part in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqParts in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HlookupPart. simpl in *.
          destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlock1Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqSce1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq in *.
      assert(HblockMappeds0: In block (getMappedBlocks partition s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial.
      }
      assert(Horigins0: scentryOrigin scentryaddr scorigin s0).
      {
        unfold scentryOrigin in *. rewrite Hs in Horigin. rewrite Hs8 in Horigin. simpl in *.
        destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in Horigin. simpl in *.
        destruct (beqAddr block2InCurrPartAddr scentryaddr) eqn:HbeqBlock2Sce; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs6 in Horigin. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces2.
        {
          subst scentryaddr. rewrite <-DTL.beqAddrTrue in HbeqSces2. apply CPaddrAddEq in HbeqSces2.
          - subst block. exfalso. apply mappedBlockIsBE in HblockMapped.
            destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite HlookupBlock2Eqss7 in *.
            rewrite Hs7 in Hlookup. simpl in *. rewrite beqAddrTrue in *. injection Hlookup as HbentriesEq.
            subst bentry. rewrite HnewB3 in Hpres. simpl in *. rewrite HnewB2 in Hpres. simpl in *. congruence.
          - intro Hcontra. rewrite Hcontra in *. unfold scentryNext in *.
            assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs5 in Horigin. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in Horigin. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2Sce in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Horigin. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqCurrSce in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in Horigin. simpl in *.
        destruct (beqAddr block1InCurrPartAddr scentryaddr) eqn:HbeqBlock1Sce; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in Horigin. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces1.
        - rewrite <-DTL.beqAddrTrue in HbeqSces1. rewrite HbeqSces1 in *. simpl in *. rewrite HlookupSce1s0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition pdentryParts0 block scentryaddr scorigin HpartIsPart HlookupParts0 HblockMappeds0
        Hsce Horigins0). destruct Hcons0 as (Hparent & HlebOriginStart).
      assert(HlookupBlockEqss2: lookup block (memory s) beqAddr = lookup block (memory s2) beqAddr).
      {
        apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite Hs.
        rewrite Hs in Hlookup. rewrite Hs8. rewrite Hs8 in Hlookup. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7. rewrite Hs7 in Hlookup.
        simpl in *. destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        {
          injection Hlookup as HbentriesEq. subst bentry. rewrite HnewB3 in Hpres. simpl in *.
          rewrite HnewB2 in Hpres. simpl in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6.
        rewrite Hs6 in Hlookup. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) block) eqn:HbeqSce2Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        rewrite Hs5 in Hlookup. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh12Block;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. rewrite Hs4 in Hlookup.
        simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Block in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. rewrite Hs3 in Hlookup.
        simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      split.
      - intro HbeqPartRoot. specialize(Hparent HbeqPartRoot).
        destruct Hparent as [blockParent (HblockPMapped & HstartP & Hincl)]. exists blockParent.
        assert(HPDchildPs0: exists childPD, sh1entryPDchild (CPaddr (blockParent+sh1offset)) childPD s0
          /\ childPD <> nullAddr).
        {
          assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockPIsBE: isBE blockParent s0).
          {
            unfold isBE. unfold bentryStartAddr in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            trivial.
          }
          specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *. unfold sh1entryPDchild.
          destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1;
            try(exfalso; congruence). destruct v; try(exfalso; congruence). exists (PDchild s9). split; trivial.
          assert(Hres: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HPflagP: bentryPFlag blockParent true s0).
          {
            apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(HlookupBlock: exists bentry, lookup block (memory s0) beqAddr = Some (BE bentry)).
          {
            apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & _)]. exists bentry.
            assumption.
          }
          destruct HlookupBlock as [bentry HlookupBlock].
          assert(HstartChild: bentryStartAddr block (startAddr (blockrange bentry)) s0).
          { unfold bentryStartAddr. rewrite HlookupBlock. reflexivity. }
          assert(HendChild: bentryEndAddr block (endAddr (blockrange bentry)) s0).
          { unfold bentryEndAddr. rewrite HlookupBlock. reflexivity. }
          assert(HlookupBP: exists bentryBP, lookup blockParent (memory s0) beqAddr = Some (BE bentryBP)).
          {
            unfold isBE in *. destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists b. reflexivity.
          }
          destruct HlookupBP as [bentryBP HlookupBP].
          assert(HendP: bentryEndAddr blockParent (endAddr (blockrange bentryBP)) s0).
          { unfold bentryEndAddr. rewrite HlookupBP. reflexivity. }
          assert(HchildIsChild: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(Hparent: pdentryParent partition (parent pdentryParts0) s0).
          { unfold pdentryParent. rewrite HlookupParts0. reflexivity. }
          specialize(HchildIsChild partition (parent pdentryParts0) HpartIsPart Hparent HbeqPartRoot).
          assert(HPflagChild: bentryPFlag block true s0).
          {
            apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentryBis (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hwell block (startAddr (blockrange bentry)) (endAddr (blockrange bentry)) HPflagChild
            HstartChild HendChild). destruct Hwell as (HwellChild & _).
          assert(HlebStarts: scorigin <= startAddr (blockrange bentry)).
          {
            assert(HstartChildIn: In (startAddr (blockrange bentry)) (getAllPaddrAux [block] s0)).
            {
              simpl. rewrite HlookupBlock. rewrite app_nil_r. apply getAllPaddrBlockIncl; lia.
            }
            specialize(Hincl (startAddr (blockrange bentry)) HstartChildIn). simpl in Hincl.
            unfold bentryStartAddr in *. rewrite HlookupBP in *. rewrite app_nil_r in *. rewrite <-HstartP in *.
            apply getAllPaddrBlockInclRev in Hincl. auto.
          }
          assert(HendMin: p (CPaddr (endAddr (blockrange bentry)-1)) = endAddr (blockrange bentry)-1).
          {
            unfold CPaddr. assert (endAddr (blockrange bentry) <= maxAddr) by (apply Hp).
            destruct (le_dec (endAddr (blockrange bentry) - 1) maxAddr); try(lia). reflexivity.
          }
          assert(HgebEnds: endAddr (blockrange bentryBP) >= endAddr (blockrange bentry)).
          {
            assert(HendChildIn: In (CPaddr (endAddr (blockrange bentry)-1)) (getAllPaddrAux [block] s0)).
            {
              simpl. rewrite HlookupBlock. rewrite app_nil_r. apply getAllPaddrBlockIncl; lia.
            }
            specialize(Hincl (CPaddr (endAddr (blockrange bentry)-1)) HendChildIn). simpl in Hincl.
            rewrite HlookupBP in *. rewrite app_nil_r in *. apply getAllPaddrBlockInclRev in Hincl.
            destruct Hincl as (_ & Hincl & _). lia.
          }
          assert(HparentOfParts0: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfParts0 partition pdentryParts0 HlookupParts0).
          destruct HparentOfParts0 as (HparentIsPart & _). specialize(HparentIsPart HbeqPartRoot).
          destruct HparentIsPart as (_ & HparentIsPart).
          specialize(Hres partition (parent pdentryParts0) block (startAddr (blockrange bentry))
            (endAddr (blockrange bentry)) blockParent scorigin (endAddr (blockrange bentryBP))
            HparentIsPart HchildIsChild HblockMappeds0 HstartChild HendChild HPflagChild HblockPMapped HstartP
            HendP HPflagP HlebStarts HgebEnds). destruct Hres as (_ & Hres & _). apply Hres. unfold sh1entryPDchild.
          rewrite HlookupSh1. reflexivity.
        }
        destruct HPDchildPs0 as [childPD (HPDchildPs0 & HbeqChildPDNull)].
        destruct (beqAddr block2InCurrPartAddr blockParent) eqn:HbeqBlock2BP.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2BP. subst blockParent. unfold sh1entryAddr in *. exfalso.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          subst sh1entryaddr2. unfold sh1entryPDchild in *.
          destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        assert(HlookupBPEqss0: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
        {
          unfold bentryStartAddr in *. rewrite Hs. rewrite Hs8. simpl.
          destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2BP. rewrite HbeqSce2BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh12BP.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqSh12BP. rewrite HbeqSh12BP in *. unfold sh1entryPDchild in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrBP. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1BP. subst blockParent. unfold sh1entryAddr in *. exfalso.
            rewrite HlookupBlock1s0 in *. subst sh1entryaddr1. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1BP. rewrite HbeqSce1BP in *. rewrite HlookupSce1s0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        unfold bentryStartAddr. rewrite HlookupBPEqss0. split; try(split); trivial.
        + assert(HparentIsPDTs0: isPDT (parent pdentryParts0) s0).
          {
            unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
            destruct (lookup (parent pdentryParts0) (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          rewrite <-HgetMappedBEqs1s0 in HblockPMapped; trivial. rewrite <-HgetMappedBEqs2s1 in HblockPMapped.
          destruct (beqAddr currentPart (parent pdentryParts0)) eqn:HbeqCurrParent.
          * rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite <-HbeqCurrParent in *. rewrite <-beqAddrFalse in *.
            specialize(HgetMappedBCurrEqss2 blockParent). destruct HgetMappedBCurrEqss2 as (Hres & _).
            specialize(Hres HblockPMapped). destruct Hres as [Hcontra | Hres]; try(exfalso; congruence). assumption.
          * rewrite <-beqAddrFalse in *. rewrite HgetMappedBNotCurrEqss2; trivial. unfold isPDT in *. rewrite Hs4.
            simpl. destruct (beqAddr block2InCurrPartAddr (parent pdentryParts0)) eqn:HbeqBlock2Parent.
            {
              rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. rewrite <-HbeqBlock2Parent in *.
              unfold bentryEndAddr in *. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
              destruct v; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3.
            simpl. rewrite beqAddrFalse in *. rewrite HbeqCurrParent. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
            destruct (beqAddr block1InCurrPartAddr (parent pdentryParts0)) eqn:HbeqBlock1Parent.
            {
              rewrite <-DTL.beqAddrTrue in HbeqBlock1Parent. rewrite <-HbeqBlock1Parent in *.
              rewrite HlookupBlock1s0 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1.
            simpl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (parent pdentryParts0)) eqn:HbeqSce1Parent.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSce1Parent. rewrite HbeqSce1Parent in *. rewrite HlookupSce1s0 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrInBlock. simpl in *. rewrite HlookupBPEqss0. rewrite HlookupBlockEqss2 in *.
          rewrite Hs2 in HaddrInBlock. simpl in *. destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
          * rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. rewrite HnewB in HaddrInBlock. simpl in *.
            rewrite app_nil_r in HaddrInBlock. apply getAllPaddrBlockInclRev in HaddrInBlock.
            destruct HaddrInBlock as (HlebStartAddr & HltAddrEnd2 & HltStartEnd2).
            destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
            --- apply PeanoNat.Nat.ltb_lt in HltAddrEnd1. apply Hincl. rewrite HlookupBlock1s0. rewrite app_nil_r.
                apply getAllPaddrBlockIncl; lia.
            --- apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. assert(partition = currentPart).
                {
                  destruct (beqAddr partition currentPart) eqn:HbeqPartCurr; try(apply DTL.beqAddrTrue; assumption).
                  exfalso. rewrite <-beqAddrFalse in *. assert(Hdisjoint: DisjointKSEntries s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
                  assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
                  specialize(Hdisjoint partition currentPart HpartIsPDTs0 HcurrIsPDTs0 HbeqPartCurr).
                  destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
                  unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMappeds0.
                  apply InFilterPresentInList in Hblock1Mappeds0.
                  specialize(Hdisjoint block1InCurrPartAddr HblockMappeds0). congruence.
                }
                subst partition. rewrite HlookupCurrs0 in HlookupParts0. injection HlookupParts0 as HpdentriesEq.
                subst pdentryParts0. specialize(HparentCurr HbeqPartRoot).
                destruct HparentCurr as [parentBlock12 [startP [endP (HparentBlockMapped & HstartPBis & HendPBis &
                  HlebStarts & HgebEnds)]]]. assert(blockParent = parentBlock12).
                {
                  destruct (beqAddr blockParent parentBlock12) eqn:HbeqBPs; try(apply DTL.beqAddrTrue; assumption).
                  exfalso. rewrite <-beqAddrFalse in *. assert(HnoDupMappedPs0: noDupMappedPaddrList s0)
                    by (unfold consistency in *; unfold consistency2 in *; intuition).
                  assert(HparentIsPDT: isPDT (parent pdentry) s0).
                  {
                    unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
                    destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
                    destruct v; try(simpl in *; congruence). trivial.
                  }
                  assert(HstartInBP: In (startAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s0)).
                  {
                    apply Hincl. rewrite HlookupBlock1s0. rewrite app_nil_r. assert(Hwell: wellFormedBlock s1)
                      by (unfold consistency1 in *; intuition).
                    specialize(Hwell block1InCurrPartAddr (startAddr (blockrange bentry1))
                      (endAddr (blockrange bentry1)) HPflag1s1 Hstart1s1 Hend1s1). destruct Hwell as (Hwell & _).
                    apply getAllPaddrBlockIncl; lia.
                  }
                  pose proof (DisjointPaddrInPart (parent pdentry) blockParent parentBlock12
                    (startAddr (blockrange bentry1)) s0 HnoDupMappedPs0 HparentIsPDT HblockPMapped HparentBlockMapped
                    HbeqBPs HstartInBP) as Hcontra. apply Hcontra. simpl. unfold bentryStartAddr in *.
                  unfold bentryEndAddr in *.
                  destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite <-HstartPBis. rewrite <-HendPBis. rewrite app_nil_r.
                  apply getAllPaddrBlockIncl; lia.
                }
                subst blockParent. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
                destruct v; try(simpl; congruence). rewrite <-HstartPBis. rewrite <-HendPBis. rewrite app_nil_r.
                apply getAllPaddrBlockIncl; lia.
          * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite Hs1 in HaddrInBlock. simpl in *. apply Hincl.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) block) eqn:HbeqSce1Block;
              try(exfalso; simpl in *; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      - intros startaddr Hstart. unfold bentryStartAddr in *. rewrite HlookupBlockEqss2 in *.
        assert(Hstarts0: bentryStartAddr block startaddr s0).
        {
          unfold bentryStartAddr. rewrite Hs2 in Hstart. simpl in *.
          destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
          - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. rewrite HlookupBlock1s0.
            rewrite HnewB in Hstart. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite Hs1 in Hstart. simpl in *.
            destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSce1Block;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        }
        apply HlebOriginStart; assumption.
      (* END originIsParentBlocksStart *)
    }

    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
        Hsce HbeqNextNull Hnext HbeqPartRoot.
      rewrite HgetPartsEqss2 in *. assert(HpartIsPDTs4: isPDT partition s4).
      {
        assert(isPDT partition s3).
        { rewrite <-HgetPartsEqs3s2 in *. apply partitionsArePDT; trivial. }
        unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock3Part.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock3Part. subst partition. unfold bentryBlockIndex in *.
          destruct (lookup block2InCurrPartAddr (memory s3) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HgetPartsEqs2s1 in *. rewrite HgetPartsEqs1s0 in *. assert(HpartIsPDTs0: isPDT partition s0).
      { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
      assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs8 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists pdentry.
          injection HlookupPart as HpdentriesEq. subst pdentryPart. rewrite Hpdentry3. simpl. rewrite Hpdentry2.
          simpl. rewrite Hpdentry1 in *. auto.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7 in HlookupPart. simpl in *.
          destruct (beqAddr block2InCurrPartAddr partition) eqn:HbeqBlock2Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs6 in HlookupPart. simpl in *. exists pdentryPart.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) partition) eqn:HbeqScePart;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. split; try(split); trivial.
          rewrite Hs4 in HlookupPart. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2Part in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart. simpl in *.
          rewrite beqAddrFalse in *. rewrite HbeqParts in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HlookupPart. simpl in *.
          destruct (beqAddr block1InCurrPartAddr partition) eqn:HbeqBlock1Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) partition) eqn:HbeqSce1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq in *.
      assert(HblockMappeds0: In block (getMappedBlocks partition s0)).
      {
        rewrite <-HgetMappedBEqs1s0; trivial. rewrite <-HgetMappedBEqs2s1.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. specialize(HgetMappedBCurrEqss2 block).
          destruct HgetMappedBCurrEqss2 as (_ & Hres & _). apply Hres; assumption.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBNotCurrEqss2; trivial.
      }
      assert(HlookupBlockEqss2: lookup block (memory s) beqAddr = lookup block (memory s2) beqAddr
        /\ block2InCurrPartAddr <> block).
      {
        apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite Hs.
        rewrite Hs in Hlookup. rewrite Hs8. rewrite Hs8 in Hlookup. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7. rewrite Hs7 in Hlookup.
        simpl in *. destruct (beqAddr block2InCurrPartAddr block) eqn:HbeqBlock2Block.
        {
          injection Hlookup as HbentriesEq. subst bentry. rewrite HnewB3 in Hpres. simpl in *.
          rewrite HnewB2 in Hpres. simpl in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6.
        rewrite Hs6 in Hlookup. split; trivial. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+scoffset)) block) eqn:HbeqSce2Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        rewrite Hs5 in Hlookup. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) block) eqn:HbeqSh12Block;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. rewrite Hs4 in Hlookup.
        simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlock2Block in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. rewrite Hs3 in Hlookup.
        simpl in *. rewrite beqAddrFalse in *. rewrite HbeqCurrBlock in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct HlookupBlockEqss2 as (HlookupBlockEqss2 & HbeqBlock2Block).
      assert(HlookupSceEqss1: lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s1) beqAddr).
      {
        unfold scentryNext in *. rewrite Hs. rewrite Hs in Hnext. rewrite Hs8. rewrite Hs8 in Hnext. simpl in *.
        destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs7. rewrite Hs7 in Hnext. simpl in *.
        destruct (beqAddr block2InCurrPartAddr scentryaddr) eqn:HbeqBlock2Sce; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs6.
        rewrite Hs6 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces1.
        {
          subst scentryaddr. rewrite <-DTL.beqAddrTrue in HbeqSces1. exfalso.
          apply CPaddrAddEq in HbeqSces1; try(congruence). intro Hcontra. rewrite Hcontra in *.
          assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5.
        rewrite Hs5 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block2InCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. rewrite Hs4 in Hnext. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqBlock2Sce in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. rewrite Hs3 in Hnext. simpl in *.
        rewrite beqAddrFalse in *. rewrite HbeqCurrSce in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. rewrite Hs2 in Hnext. simpl in *.
        destruct (beqAddr block1InCurrPartAddr scentryaddr) eqn:HbeqBlock1Sce; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      unfold scentryNext in *. rewrite HlookupSceEqss1 in *. unfold bentryEndAddr in *. simpl.
      rewrite HlookupBlockEqss2 in *. rewrite Hs2 in HendBlock. simpl in *.
      destruct (beqAddr block1InCurrPartAddr block) eqn:HbeqBlock1Block.
      - rewrite <-DTL.beqAddrTrue in HbeqBlock1Block. subst block. rewrite HnewB in HendBlock. simpl in *.
        subst endaddr. assert(partition = currentPart).
        {
          destruct (beqAddr partition currentPart) eqn:HbeqPartCurr; try(apply DTL.beqAddrTrue; assumption).
          exfalso. rewrite <-beqAddrFalse in *. assert(Hdisjoint: DisjointKSEntries s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurrs0; trivial).
          specialize(Hdisjoint partition currentPart HpartIsPDTs0 HcurrIsPDTs0 HbeqPartCurr).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMappeds0.
          apply InFilterPresentInList in Hblock1Mappeds0.
          specialize(Hdisjoint block1InCurrPartAddr HblockMappeds0). congruence.
        }
        subst partition. rewrite HlookupCurrs0 in HlookupParts0. injection HlookupParts0 as HpdentriesEq.
        subst pdentryParts0. specialize(HparentCurr HbeqPartRoot). rewrite Hsce in Hnext. rewrite Hs1 in Hnext.
        simpl in *. rewrite beqAddrTrue in *. simpl in *. subst scnext.
        assert(HeqTriv: CPaddr (block2InCurrPartAddr+scoffset) = CPaddr (block2InCurrPartAddr+scoffset)) by trivial.
        specialize(Hcons0 currentPart pdentry block2InCurrPartAddr (CPaddr (block2InCurrPartAddr + scoffset))
          block2Next block2End HpartIsPart HlookupCurrs0 Hblock2Mappeds0 Hend2s0 HeqTriv HbeqNextNull Hnext2s0
          HbeqPartRoot).
        destruct Hcons0 as [blockParent [endParent (HblockPMapped & HendP & HltEnd2EndP & Hincl)]].
        exists blockParent. exists endParent.
        assert(HPDchildPs0: exists childPD, sh1entryPDchild (CPaddr (blockParent+sh1offset)) childPD s0
          /\ childPD <> nullAddr).
        {
          assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockPIsBE: isBE blockParent s0).
          {
            unfold isBE. unfold bentryEndAddr in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            trivial.
          }
          specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *. unfold sh1entryPDchild.
          destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1;
            try(exfalso; congruence). destruct v; try(exfalso; congruence). exists (PDchild s9). split; trivial.
          assert(Hres: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HPflagP: bentryPFlag blockParent true s0).
          {
            apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(HlookupBP: exists bentryBP, lookup blockParent (memory s0) beqAddr = Some (BE bentryBP)).
          {
            unfold bentryEndAddr in *. destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists b. reflexivity.
          }
          destruct HlookupBP as [bentryBP HlookupBP].
          assert(HstartP: bentryStartAddr blockParent (startAddr (blockrange bentryBP)) s0).
          { unfold bentryStartAddr. rewrite HlookupBP. reflexivity. }
          assert(HchildIsChild: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(Hparent: pdentryParent currentPart (parent pdentry) s0).
          { unfold pdentryParent. rewrite HlookupCurrs0. reflexivity. }
          specialize(HchildIsChild currentPart (parent pdentry) HpartIsPart Hparent HbeqPartRoot).
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hwell block2InCurrPartAddr (endAddr (blockrange bentry1)) block2End HPflag2s0 Hstart2s0
            Hend2s0). destruct Hwell as (HwellChild & _).
          assert(HlebStarts: startAddr (blockrange bentryBP) <= endAddr (blockrange bentry1)).
          {
            assert(HstartChildIn: In (endAddr (blockrange bentry1)) (getAllPaddrAux [block2InCurrPartAddr] s0)).
            {
              simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite <-Hstart2s0. rewrite <-Hend2s0. rewrite app_nil_r.
              apply getAllPaddrBlockIncl; lia.
            }
            specialize(Hincl (endAddr (blockrange bentry1)) HstartChildIn). simpl in Hincl.
            rewrite HlookupBP in *. rewrite app_nil_r in *. apply getAllPaddrBlockInclRev in Hincl. apply Hincl.
          }
          assert(HgebEnds: endParent >= block2End) by lia.
          assert(HparentOfParts0: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
          destruct HparentOfParts0 as (HparentIsPart & _). specialize(HparentIsPart HbeqPartRoot).
          destruct HparentIsPart as (_ & HparentIsPart).
          specialize(Hres currentPart (parent pdentry) block2InCurrPartAddr (endAddr (blockrange bentry1))
            block2End blockParent (startAddr (blockrange bentryBP)) endParent HparentIsPart HchildIsChild
            Hblock2Mappeds0 Hstart2s0 Hend2s0 HPflag2s0 HblockPMapped HstartP HendP HPflagP HlebStarts
            HgebEnds). destruct Hres as (_ & Hres & _). apply Hres. unfold sh1entryPDchild.
          rewrite HlookupSh1. reflexivity.
        }
        destruct HPDchildPs0 as [childPD (HPDchildPs0 & HbeqChildPDNull)].
        destruct (beqAddr block2InCurrPartAddr blockParent) eqn:HbeqBlock2BP.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2BP. subst blockParent. unfold sh1entryAddr in *. exfalso.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          subst sh1entryaddr2. unfold sh1entryPDchild in *.
          destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        assert(HlookupBPEqss0: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
        {
          unfold bentryEndAddr in *. rewrite Hs. rewrite Hs8. simpl.
          destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2BP. rewrite HbeqSce2BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh12BP.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqSh12BP. rewrite HbeqSh12BP in *. unfold sh1entryPDchild in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrBP. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1BP. subst blockParent. unfold sh1entryAddr in *. exfalso.
            rewrite HlookupBlock1s0 in *. subst sh1entryaddr1. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1BP. rewrite HbeqSce1BP in *. rewrite HlookupSce1s0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupBPEqss0. split; try(split; try(split)); trivial.
        + assert(HparentIsPDTs0: isPDT (parent pdentry) s0).
          {
            unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
            destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          rewrite <-HgetMappedBEqs1s0 in HblockPMapped; trivial. rewrite <-HgetMappedBEqs2s1 in HblockPMapped.
          assert(HparentOfParts0: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfParts0 currentPart pdentry HlookupCurrs0).
          destruct HparentOfParts0 as (_ & _ & HbeqParentCurr). apply not_eq_sym in HbeqParentCurr.
          rewrite HgetMappedBNotCurrEqss2; trivial. unfold isPDT in *. rewrite Hs4.
          simpl. destruct (beqAddr block2InCurrPartAddr (parent pdentry)) eqn:HbeqBlock2Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. rewrite <-HbeqBlock2Parent in *.
            unfold bentryEndAddr in *. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3.
          simpl. rewrite beqAddrFalse in *. rewrite HbeqParentCurr. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          destruct (beqAddr block1InCurrPartAddr (parent pdentry)) eqn:HbeqBlock1Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1Parent. rewrite <-HbeqBlock1Parent in *.
            rewrite HlookupBlock1s0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1.
          simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (parent pdentry)) eqn:HbeqSce1Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1Parent. rewrite HbeqSce1Parent in *. rewrite HlookupSce1s0 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrInBlock. rewrite Hs2 in HaddrInBlock. simpl in *. rewrite beqAddrTrue in *.
          rewrite HnewB in HaddrInBlock. simpl in *.
          rewrite app_nil_r in HaddrInBlock. apply getAllPaddrBlockInclRev in HaddrInBlock.
          destruct HaddrInBlock as (HlebStartAddr & HltAddrEnd2 & HltStartEnd2).
          destruct (Nat.ltb addr (endAddr (blockrange bentry1))) eqn:HltAddrEnd1.
          * apply PeanoNat.Nat.ltb_lt in HltAddrEnd1.
            destruct HparentCurr as [parentBlock12 [startP [endP (HparentBlockMapped & HstartPBis & HendPBis &
              HlebStarts & HgebEnds)]]]. assert(blockParent = parentBlock12).
            {
              destruct (beqAddr blockParent parentBlock12) eqn:HbeqBPs; try(apply DTL.beqAddrTrue; assumption).
              exfalso. rewrite <-beqAddrFalse in *. assert(HnoDupMappedPs0: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              assert(HparentIsPDT: isPDT (parent pdentry) s0).
              {
                unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
                destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
                destruct v; try(simpl in *; congruence). trivial.
              }
              assert(HendInBP: In (endAddr (blockrange bentry1)) (getAllPaddrAux [blockParent] s0)).
              {
                apply Hincl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
                destruct v; try(simpl; congruence). rewrite <-Hstart2s0. rewrite <-Hend2s0.
                rewrite app_nil_r. apply getAllPaddrBlockIncl; lia.
              }
              pose proof (DisjointPaddrInPart (parent pdentry) blockParent parentBlock12
                (endAddr (blockrange bentry1)) s0 HnoDupMappedPs0 HparentIsPDT HblockPMapped HparentBlockMapped
                HbeqBPs HendInBP) as Hcontra. apply Hcontra. simpl. unfold bentryStartAddr in *.
              unfold bentryEndAddr in *.
              destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite <-HstartPBis. rewrite <-HendPBis. rewrite app_nil_r.
              apply getAllPaddrBlockIncl; lia.
            }
            subst blockParent. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup parentBlock12 (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-HstartPBis. rewrite <-HendPBis. rewrite app_nil_r.
            apply getAllPaddrBlockIncl; lia.
          * apply PeanoNat.Nat.ltb_ge in HltAddrEnd1. apply Hincl. unfold bentryStartAddr in *.
            unfold bentryEndAddr in *.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-Hstart2s0. rewrite <-Hend2s0.
            rewrite app_nil_r. apply getAllPaddrBlockIncl; lia.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HendBlock. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) block) eqn:HbeqSce1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in Hnext. simpl in *.
        destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) scentryaddr) eqn:HbeqSces1.
        {
          subst scentryaddr. rewrite <-DTL.beqAddrTrue in HbeqSces1. exfalso.
          apply CPaddrAddEq in HbeqSces1; try(congruence). intro Hcontra. rewrite Hcontra in *.
          assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 partition pdentryParts0 block scentryaddr scnext endaddr HpartIsPart HlookupParts0
          HblockMappeds0 HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
        destruct Hcons0 as [blockParent [endParent (HblockPMapped & HendP & HltEndP & Hincl)]]. exists blockParent.
        exists endParent.
        assert(HlookupBlockEqs2s0: lookup block (memory s2) beqAddr = lookup block (memory s0) beqAddr).
        {
          rewrite Hs2. simpl. rewrite beqAddrFalse in *. rewrite HbeqBlock1Block. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqSce1Block. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupBlockEqs2s0.
        assert(HPDchildPs0: exists childPD, sh1entryPDchild (CPaddr (blockParent+sh1offset)) childPD s0
          /\ childPD <> nullAddr).
        {
          assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockPIsBE: isBE blockParent s0).
          {
            unfold isBE. unfold bentryEndAddr in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            trivial.
          }
          specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *. unfold sh1entryPDchild.
          destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1;
            try(exfalso; congruence). destruct v; try(exfalso; congruence). exists (PDchild s9). split; trivial.
          assert(Hres: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HPflagP: bentryPFlag blockParent true s0).
          {
            apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(HlookupBP: exists bentryBP, lookup blockParent (memory s0) beqAddr = Some (BE bentryBP)).
          {
            unfold bentryEndAddr in *. destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists b. reflexivity.
          }
          destruct HlookupBP as [bentryBP HlookupBP].
          assert(HstartP: bentryStartAddr blockParent (startAddr (blockrange bentryBP)) s0).
          { unfold bentryStartAddr. rewrite HlookupBP. reflexivity. }
          assert(HchildIsChild: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(Hparent: pdentryParent partition (parent pdentryParts0) s0).
          { unfold pdentryParent. rewrite HlookupParts0. reflexivity. }
          specialize(HchildIsChild partition (parent pdentryParts0) HpartIsPart Hparent HbeqPartRoot).
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HPflagBlock: bentryPFlag block true s0).
          {
            apply mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(HlookupBlock: exists bentry, lookup block (memory s0) beqAddr = Some (BE bentry)).
          {
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists b. reflexivity.
          }
          destruct HlookupBlock as [bentry HlookupBlock].
          assert(HstartBlock: bentryStartAddr block (startAddr (blockrange bentry)) s0).
          { unfold bentryStartAddr. rewrite HlookupBlock. reflexivity. }
          specialize(Hwell block (startAddr (blockrange bentry)) endaddr HPflagBlock HstartBlock
            HendBlock). destruct Hwell as (HwellChild & _).
          assert(HlebStarts: startAddr (blockrange bentryBP) <= startAddr (blockrange bentry)).
          {
            assert(HstartChildIn: In (startAddr (blockrange bentry)) (getAllPaddrAux [block] s0)).
            {
              simpl. unfold bentryEndAddr in *. rewrite HlookupBlock in *. rewrite <-HendBlock. rewrite app_nil_r.
              apply getAllPaddrBlockIncl; lia.
            }
            specialize(Hincl (startAddr (blockrange bentry)) HstartChildIn). simpl in Hincl.
            rewrite HlookupBP in *. rewrite app_nil_r in *. apply getAllPaddrBlockInclRev in Hincl. apply Hincl.
          }
          assert(HgebEnds: endParent >= endaddr) by lia.
          assert(HparentOfParts0: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfParts0 partition pdentryParts0 HlookupParts0).
          destruct HparentOfParts0 as (HparentIsPart & _). specialize(HparentIsPart HbeqPartRoot).
          destruct HparentIsPart as (_ & HparentIsPart).
          specialize(Hres partition (parent pdentryParts0) block (startAddr (blockrange bentry))
            endaddr blockParent (startAddr (blockrange bentryBP)) endParent HparentIsPart HchildIsChild
            HblockMappeds0 HstartBlock HendBlock HPflagBlock HblockPMapped HstartP HendP HPflagP HlebStarts
            HgebEnds). destruct Hres as (_ & Hres & _). apply Hres. unfold sh1entryPDchild.
          rewrite HlookupSh1. reflexivity.
        }
        destruct HPDchildPs0 as [childPD (HPDchildPs0 & HbeqChildPDNull)].
        destruct (beqAddr block2InCurrPartAddr blockParent) eqn:HbeqBlock2BP.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlock2BP. subst blockParent. unfold sh1entryAddr in *. exfalso.
          destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          subst sh1entryaddr2. unfold sh1entryPDchild in *.
          destruct (lookup (CPaddr (block2InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        assert(HlookupBPEqss0: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
        {
          unfold bentryEndAddr in *. rewrite Hs. rewrite Hs8. simpl.
          destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs7. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce2BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce2BP. rewrite HbeqSce2BP in *. unfold scentryNext in *. exfalso.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
          destruct (beqAddr (CPaddr (block2InCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh12BP.
          {
            unfold sh1entryAddr in *. exfalso.
            destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr2.
            rewrite <-DTL.beqAddrTrue in HbeqSh12BP. rewrite HbeqSh12BP in *. unfold sh1entryPDchild in *.
            destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqBlock2BP. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
          rewrite HbeqCurrBP. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite Hs2. simpl. destruct (beqAddr block1InCurrPartAddr blockParent) eqn:HbeqBlock1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1BP. subst blockParent. unfold sh1entryAddr in *. exfalso.
            rewrite HlookupBlock1s0 in *. subst sh1entryaddr1. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block1InCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr + scoffset)) blockParent) eqn:HbeqSce1BP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1BP. rewrite HbeqSce1BP in *. rewrite HlookupSce1s0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupBPEqss0. split; auto. assert(HparentIsPDTs0: isPDT (parent pdentryParts0) s0).
        {
          unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
          destruct (lookup (parent pdentryParts0) (memory s0) beqAddr); try(simpl in *; congruence).
          destruct v; try(simpl in *; congruence). trivial.
        }
        rewrite <-HgetMappedBEqs1s0 in HblockPMapped; trivial. rewrite <-HgetMappedBEqs2s1 in HblockPMapped.
        destruct (beqAddr currentPart (parent pdentryParts0)) eqn:HbeqCurrParent.
        * rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite <-HbeqCurrParent in *. rewrite <-beqAddrFalse in *.
          specialize(HgetMappedBCurrEqss2 blockParent). destruct HgetMappedBCurrEqss2 as (Hres & _).
          specialize(Hres HblockPMapped). destruct Hres as [Hcontra | Hres]; try(exfalso; congruence). assumption.
        * rewrite <-beqAddrFalse in *. rewrite HgetMappedBNotCurrEqss2; trivial. unfold isPDT in *. rewrite Hs4.
          simpl. destruct (beqAddr block2InCurrPartAddr (parent pdentryParts0)) eqn:HbeqBlock2Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock2Parent. rewrite <-HbeqBlock2Parent in *.
            unfold bentryEndAddr in *. destruct (lookup block2InCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3.
          simpl. rewrite beqAddrFalse in *. rewrite HbeqCurrParent. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          destruct (beqAddr block1InCurrPartAddr (parent pdentryParts0)) eqn:HbeqBlock1Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlock1Parent. rewrite <-HbeqBlock1Parent in *.
            rewrite HlookupBlock1s0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1.
          simpl.
          destruct (beqAddr (CPaddr (block1InCurrPartAddr+scoffset)) (parent pdentryParts0)) eqn:HbeqSce1Parent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSce1Parent. rewrite HbeqSce1Parent in *. rewrite HlookupSce1s0 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END nextImpliesBlockWasCut *)
    }
  }
  split; trivial. split; trivial. split; trivial.
  assert(Hcurrs: currentPart = currentPartition s).
  {
    rewrite Hs. simpl. rewrite Hs8. simpl. rewrite Hs7. simpl. rewrite Hs6. simpl. rewrite Hs5. simpl. rewrite Hs4.
    simpl. rewrite Hs3. simpl. rewrite Hs2. simpl. assumption.
  }
  unfold currentPartitionInPartitionsList in *.
  instantiate(1 := fun s => consistency s /\ partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ isPDT currentPart s /\ In currentPart (getPartitions multiplexer s)
    /\ In block1InCurrPartAddr (getMappedBlocks currentPart s) /\ bentryAFlag block1InCurrPartAddr true s).
  assert(In block1InCurrPartAddr (getMappedBlocks currentPart s)).
  {
    rewrite <-HgetMappedBEqs2s1 in Hblock1Mappeds1.
    specialize(HgetMappedBCurrEqss2 block1InCurrPartAddr). destruct HgetMappedBCurrEqss2 as (Hres & _).
    specialize(Hres Hblock1Mappeds1). destruct Hres as [Hcontra | Hres]; try(exfalso; congruence). assumption.
  }
  (*TODO complete that depending on what's needed*)
  rewrite Hcurrs at 1. rewrite Hcurrs at 2. simpl. unfold cons1Free in *. split. intuition.
  split. unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *; intuition.
  unfold bentryPFlag. rewrite HlookupBlock1Eqss2. intuition.
  - exists pdentry3. rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity.
  - exists (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) (present bentry1) (accessible bentry1)
      (blockindex bentry1) (CBlock (startAddr (blockrange bentry1)) block2End)). rewrite Hs2. simpl.
    rewrite beqAddrTrue. reflexivity.
  - destruct HnewB as [l0 [l1 HnewB]]. rewrite Hs2. simpl. rewrite beqAddrTrue. rewrite HnewB. simpl.
    unfold bentryPFlag in *. rewrite HlookupBlock1s0 in *. assumption.
}
intro. eapply bindRev.
{ (** MAL.removeBlockFromPhysicalMPU **)
  eapply weaken. apply removeBlockFromPhysicalMPU. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as (HPI & HKDI & HVS & Hconsist & [s0 [pdentry4 [blockOrigin [blockStart [blockEnd [blockNext
    [parentsList [statesList [blockBase [bentryBase [bentryBases0 (HPIs0 & HKDIs0 & HVSs0 & HparentsList & Hs &
    HisBuilt & HcurrIsPDTs0 & HcurrIsParts0 & HlookupCurrs0 & _ & HpropsCont & Hconsists0 & HlookupBases0 &
    HPflagBases0 & HAflagBases0 & HbaseMappeds0 & HbaseAccMappeds0 & HstartBases0 & HendBases0 & Hprops)]]]]]]]]]]]).
  apply isBuiltFromWriteAccessibleRec.stablePDTIsBuilt with statesList s0 parentsList currentPart blockStart blockEnd
    true; trivial.
}
intro. eapply bindRev.
{ (** MAL.removeBlockFromPhysicalMPU **)
  eapply weaken. apply removeBlockFromPhysicalMPU. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s0 [pdentry5 [realMPU (HMPUs0 & Hprops & HlookupCurrs0 & Hs)]]]. unfold isPDT. rewrite Hs.
  simpl. rewrite beqAddrTrue. trivial.
}
intro. eapply bindRev.
{ (** Internal.enableBlockInMPU **)
  eapply weaken. apply enableBlockInMPU. intros s Hprops. simpl.
  destruct Hprops as [s2 [pdentry2 [realMPU2 (HMPUs2 & [s1 [pdentry1 [realMPU1 (HMPUs1 & (HPIs1 & HKDIs1 & HVSs1 &
    Hconsists1 & Hprops) & HlookupCurrs1 & Hs2)]]] & HlookupCurrs2 & Hs)]]].
  destruct Hprops as [s0 [pdentry [blockOrigin [blockStart [blockEnd [blockNext [parentsList [statesList [blockBase
    [bentryBase [bentryBase0 (HPIs0 & _ & _ & HparentsList & Hs1 & HisBuilt & _ & _ & _ & _ & (Hconsists0 & _ & _ & _
    & HcurrIsPDTs0 & HcurrIsParts0 & Hblock1Mapped & HAflag1s0) & _ & HlookupBases0 & HPflagBases0 & HAflagBases0 &
    HbaseMapped & HbaseAccMapped & HstartBase & HendBase & HcheckChildBase & Hprops)]]]]]]]]]]].
  destruct (beqAddr currentPart nullAddr) eqn:HbeqCurrNull.
  {
    assert(Hcons0: isPADDR nullAddr s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold isPADDR in *. rewrite <-DTL.beqAddrTrue in HbeqCurrNull. rewrite HbeqCurrNull in *.
    rewrite HlookupCurrs1 in *. exfalso; congruence.
  }
  assert(Hpdentry2: pdentry2 = {|
                                 structure := structure pdentry1;
                                 firstfreeslot := firstfreeslot pdentry1;
                                 nbfreeslots := nbfreeslots pdentry1;
                                 nbprepare := nbprepare pdentry1;
                                 parent := parent pdentry1;
                                 MPU := MAL.removeBlockFromPhysicalMPUAux block1InCurrPartAddr realMPU1;
                                 vidtAddr := vidtAddr pdentry1
                               |}).
  {
    rewrite Hs2 in HlookupCurrs2. simpl in *. rewrite beqAddrTrue in *. injection HlookupCurrs2 as Hres. auto.
  }
  assert(HcurrEq: currentPartition s = currentPartition s1).
  { rewrite Hs. rewrite Hs2. reflexivity. }
  assert(HgetPartsEqs2s1: getPartitions multiplexer s2 = getPartitions multiplexer s1).
  {
    rewrite Hs2. apply getPartitionsEqPDT with pdentry1; auto; unfold consistency in *; unfold consistency1 in *;
      intuition.
  }
  assert(PDTIfPDFlag s2).
  {
    assert(Hcons0: PDTIfPDFlag s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros idPDchild sh1entryaddr HcheckChild.
    assert(HlookupChildEq: lookup idPDchild (memory s2) beqAddr = lookup idPDchild (memory s1) beqAddr).
    {
      destruct HcheckChild as (_ & Hsh1). unfold sh1entryAddr in *. rewrite Hs2. rewrite Hs2 in Hsh1. simpl in *.
      destruct (beqAddr currentPart idPDchild) eqn:HbeqCurrChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(HcheckChilds1: true = checkChild idPDchild s1 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s1).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. rewrite HlookupChildEq in *.
      destruct HcheckChild as (HcheckChild & Hsh1). split; trivial.
      destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite Hs2 in HcheckChild. simpl in *.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds1). unfold bentryAFlag. unfold bentryPFlag.
    destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HStartIsPDT)]). unfold bentryStartAddr.
    unfold entryPDT in *. rewrite HlookupChildEq. split; trivial. split; trivial. exists startaddr. split; trivial.
    destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence). rewrite Hs2.
    simpl. destruct (beqAddr currentPart (startAddr (blockrange b))) eqn:HbeqCurrStart.
    - destruct (lookup (startAddr (blockrange b)) (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(StructurePointerIsKS s2).
  {
    assert(Hcons0: StructurePointerIsKS s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
      /\ structure pdentryPart = structure pdentryParts0).
    {
      rewrite Hs2 in HlookupPart. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
        subst pdentryPart. exists pdentry1. auto.
      - rewrite <-beqAddrFalse in *. exists pdentryPart.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HstructEq)]. rewrite HstructEq in *.
    specialize(Hcons0 partition pdentryParts1 HlookupParts1 HbeqStructNull).
    unfold isKS in *. rewrite Hs2. simpl. destruct (beqAddr currentPart (structure pdentryParts1)) eqn:HbeqCurrStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrStruct. rewrite HbeqCurrStruct in *. rewrite HlookupCurrs1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HgetPartsEqss1: getPartitions multiplexer s = getPartitions multiplexer s1).
  {
    rewrite <-HgetPartsEqs2s1. rewrite Hs. apply getPartitionsEqPDT with pdentry2; auto.
  }
  assert(HgetFreeEq: forall partition, getFreeSlotsList partition s = getFreeSlotsList partition s1).
  {
    intro partition. assert(Heqs2: getFreeSlotsList partition s2 = getFreeSlotsList partition s1).
    {
      rewrite Hs2. unfold getFreeSlotsList. simpl. rewrite <-Hs2.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs1. simpl.
        destruct (beqAddr (firstfreeslot pdentry1) nullAddr) eqn:HbeqFirstFreeNull; trivial. rewrite Hs2.
        apply getFreeSlotsListRecEqPDT. 2,3: unfold isBE; unfold isPADDR; rewrite HlookupCurrs1; auto.
        rewrite <-beqAddrFalse in *. assert(HfirstFreeIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s1)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HfirstFreeIsBE currentPart pdentry1 HlookupCurrs1 HbeqFirstFreeNull).
        destruct HfirstFreeIsBE as (HfirstFreeIsBE & _). intro Hcontra. rewrite Hcontra in *. unfold isBE in *.
        rewrite HlookupCurrs1 in *. congruence.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        destruct (lookup partition (memory s1) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; trivial. rewrite Hs2.
        apply getFreeSlotsListRecEqPDT. 2,3: unfold isBE; unfold isPADDR; rewrite HlookupCurrs1; auto.
        rewrite <-beqAddrFalse in *. assert(HfirstFreeIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s1)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HfirstFreeIsBE partition p HlookupPart HbeqFirstFreeNull).
        destruct HfirstFreeIsBE as (HfirstFreeIsBE & _). intro Hcontra. rewrite Hcontra in *. unfold isBE in *.
        rewrite HlookupCurrs1 in *. congruence.
    }
    rewrite <-Heqs2. unfold getFreeSlotsList. rewrite Hs. simpl. rewrite <-Hs.
    destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
    - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs2. simpl.
      destruct (beqAddr (firstfreeslot pdentry2) nullAddr) eqn:HbeqFirstFreeNull; trivial. rewrite Hs.
      apply getFreeSlotsListRecEqPDT. 2,3: unfold isBE; unfold isPADDR; rewrite HlookupCurrs2; auto.
      rewrite <-beqAddrFalse in *. assert(HfirstFreeIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition). rewrite Hpdentry2 in HbeqFirstFreeNull.
      simpl in *. specialize(HfirstFreeIsBE currentPart pdentry1 HlookupCurrs1 HbeqFirstFreeNull).
      destruct HfirstFreeIsBE as (HfirstFreeIsBE & _). rewrite Hpdentry2. simpl. intro Hcontra. rewrite Hcontra in *.
      unfold isBE in *. rewrite HlookupCurrs1 in *. congruence.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup partition (memory s2) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
      destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; trivial. rewrite Hs.
      apply getFreeSlotsListRecEqPDT. 2,3: unfold isBE; unfold isPADDR; rewrite HlookupCurrs2; auto.
      rewrite <-beqAddrFalse in *. assert(HfirstFreeIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition). rewrite Hs2 in HlookupPart. simpl in *.
      rewrite beqAddrFalse in *. rewrite HbeqCurrPart in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(HfirstFreeIsBE partition p HlookupPart HbeqFirstFreeNull).
      destruct HfirstFreeIsBE as (HfirstFreeIsBE & _). intro Hcontra. rewrite Hcontra in *. unfold isBE in *.
      rewrite HlookupCurrs1 in *. congruence.
  }
  assert(HgetKSEq: forall partition, getKSEntries partition s = getKSEntries partition s1).
  {
    intro partition. assert(Heqs2: getKSEntries partition s2 = getKSEntries partition s1).
    {
      rewrite Hs2. apply getKSEntriesEqPDT with pdentry1; trivial.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite <-Heqs2. rewrite Hs. apply getKSEntriesEqPDT with pdentry2; trivial.
  }
  assert(HgetChildrenEq: forall partition, getChildren partition s = getChildren partition s1).
  {
    intro partition. assert(Heqs2: getChildren partition s2 = getChildren partition s1).
    {
      rewrite Hs2. apply getChildrenEqPDT with pdentry1; trivial.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite <-Heqs2. rewrite Hs. apply getChildrenEqPDT with pdentry2; trivial.
  }
  assert(HgetMappedBEq: forall partition, getMappedBlocks partition s = getMappedBlocks partition s1).
  {
    intro partition. assert(Heqs2: getMappedBlocks partition s2 = getMappedBlocks partition s1).
    {
      rewrite Hs2. apply getMappedBlocksEqPDT with pdentry1; trivial.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite <-Heqs2. rewrite Hs. apply getMappedBlocksEqPDT with pdentry2; trivial.
  }
  assert(HkernListEq: forall partition kernList, isListOfKernels kernList partition s
    -> isListOfKernels kernList partition s1).
  {
    intros partition kernList HkernList. assert(HkernLists2: isListOfKernels kernList partition s2).
    {
      revert HkernList. rewrite Hs. apply isListOfKernelsEqPDT with pdentry2; trivial.
    }
    revert HkernLists2. rewrite Hs2. apply isListOfKernelsEqPDT with pdentry1; trivial.
  }
  assert(parentOfPartitionIsPartition s2).
  {
    assert(Hcons0: parentOfPartitionIsPartition s1)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart.
    assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
      /\ parent pdentryPart = parent pdentryParts0).
    {
      rewrite Hs2 in HlookupPart. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
        subst pdentryPart. exists pdentry1. auto.
      - rewrite <-beqAddrFalse in *. exists pdentryPart.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HparentsEq)]. rewrite HparentsEq in *.
    specialize(Hcons0 partition pdentryParts1 HlookupParts1).
    destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split; auto. intro HbeqPartRoot.
    specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
    rewrite HgetPartsEqs2s1. split; trivial. rewrite Hs2. simpl.
    destruct (beqAddr currentPart (parent pdentryParts1)) eqn:HbeqCurrParent.
    - exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := MAL.removeBlockFromPhysicalMPUAux block1InCurrPartAddr realMPU1;
               vidtAddr := vidtAddr pdentry1
             |}. reflexivity.
    - exists parentEntry. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }

  assert(consistency1 s).
  {
    assert(nullAddrExists s).
    { (* BEGIN nullAddrExists s *)
      assert(Hcons0: isPADDR nullAddr s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold nullAddrExists. unfold isPADDR in *. rewrite Hs. rewrite Hs2. simpl. rewrite HbeqCurrNull.
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END nullAddrExists *)
    }

    assert(wellFormedFstShadowIfBlockEntry s).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition). intros block HblockIsBE. unfold isBE in *.
      rewrite Hs in HblockIsBE. rewrite Hs2 in HblockIsBE. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 block HblockIsBE).
      unfold isSHE in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(PDTIfPDFlag s).
    { (* BEGIN PDTIfPDFlag s *)
      assert(Hcons0: PDTIfPDFlag s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros idPDchild sh1entryaddr HcheckChild.
      assert(HlookupChildEq: lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s1) beqAddr).
      {
        destruct HcheckChild as (_ & Hsh1). unfold sh1entryAddr in *. rewrite Hs. rewrite Hs2. rewrite Hs in Hsh1.
        rewrite Hs2 in Hsh1. simpl in *.
        destruct (beqAddr currentPart idPDchild) eqn:HbeqCurrChild; try(exfalso; congruence).
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      assert(HcheckChilds1: true = checkChild idPDchild s1 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s1).
      {
        unfold checkChild in *. unfold sh1entryAddr in *. rewrite HlookupChildEq in *.
        destruct HcheckChild as (HcheckChild & Hsh1). split; trivial.
        destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
        rewrite Hs in HcheckChild. rewrite Hs2 in HcheckChild. simpl in *.
        destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds1). unfold bentryAFlag. unfold bentryPFlag.
      destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HStartIsPDT)]). unfold bentryStartAddr.
      unfold entryPDT in *. rewrite HlookupChildEq. split; trivial. split; trivial. exists startaddr. split; trivial.
      destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence). rewrite Hs.
      rewrite Hs2. simpl. destruct (beqAddr currentPart (startAddr (blockrange b))) eqn:HbeqCurrStart.
      - destruct (lookup (startAddr (blockrange b)) (memory s1) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). assumption.
      - rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag s).
    { (* BEGIN AccessibleNoPDFlag s *)
      assert(Hcons0: AccessibleNoPDFlag s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block sh1entryaddr HblockIsBE Hsh1 HAflag. unfold isBE in *. unfold sh1entryAddr in *.
      unfold bentryAFlag in *. rewrite Hs in HblockIsBE. rewrite Hs in Hsh1. rewrite Hs in HAflag.
      rewrite Hs2 in HblockIsBE. rewrite Hs2 in Hsh1. rewrite Hs2 in HAflag. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAflag). unfold sh1entryPDflag in *. rewrite Hs.
      rewrite Hs2. simpl. destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart HbeqFirstNull.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
        /\ firstfreeslot pdentryPart = firstfreeslot pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. split; trivial. simpl. rewrite Hpdentry2. reflexivity.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *. exists pdentryPart.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HfirstFreeEq)]. rewrite HfirstFreeEq in *.
      specialize(Hcons0 partition pdentryParts1 HlookupParts1 HbeqFirstNull). destruct Hcons0 as (_ & Hcons0).
      unfold isFreeSlot in *. unfold isBE. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart (firstfreeslot pdentryParts1)) eqn:HbeqCurrFirstFree.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrFirstFree. rewrite HbeqCurrFirstFree in *. rewrite HlookupCurrs1 in *.
        exfalso; congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (firstfreeslot pdentryParts1) (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split; trivial.
      destruct (beqAddr currentPart (CPaddr (firstfreeslot pdentryParts1 + sh1offset))) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (firstfreeslot pdentryParts1+sh1offset)) (memory s1) beqAddr);
        try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct (beqAddr currentPart (CPaddr (firstfreeslot pdentryParts1 + scoffset))) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT s).
    { (* BEGIN multiplexerIsPDT s *)
      assert(Hcons0: multiplexerIsPDT s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart multiplexer) eqn:HbeqParts; trivial.
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END multiplexerIsPDT *)
    }

    assert(currentPartitionInPartitionsList s).
    { (* BEGIN currentPartitionInPartitionsList s *)
      assert(Hcons0: currentPartitionInPartitionsList s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold currentPartitionInPartitionsList in *. rewrite HcurrEq. rewrite HgetPartsEqss1. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry s).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition). intros block HblockIsBE. unfold isBE in *.
      rewrite Hs in HblockIsBE. rewrite Hs2 in HblockIsBE. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 block HblockIsBE).
      destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr. split; trivial. unfold isSCE in *.
      rewrite Hs. rewrite Hs2. simpl. destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE s).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros kernel idx HkernIsKS HltIdxKernEntries. unfold isKS in *.
      rewrite Hs in HkernIsKS. rewrite Hs2 in HkernIsKS. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart (CPaddr (kernel + idx))) eqn:HbeqCurrIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrIdx. rewrite HbeqCurrIdx in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS s).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition). intros block idx HblockIsBE Hidx.
      unfold isBE in *. unfold bentryBlockIndex in *. rewrite Hs in Hidx. rewrite Hs2 in Hidx.
      rewrite Hs in HblockIsBE. rewrite Hs2 in HblockIsBE. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 block idx HblockIsBE Hidx).
      unfold isKS in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart (CPaddr (block-idx))) eqn:HbeqCurrKern.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrKern. rewrite HbeqCurrKern in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(sh1InChildLocationIsBE s).
    { (* BEGIN sh1InChildLocationIsBE s *)
      assert(Hcons0: sh1InChildLocationIsBE s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull. rewrite Hs in HlookupSh1. rewrite Hs2 in HlookupSh1.
      simpl in *. destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). unfold isBE in *. rewrite Hs. rewrite Hs2.
      simpl. destruct (beqAddr currentPart (inChildLocation sh1entry)) eqn:HbeqCurrLoc.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrLoc. rewrite HbeqCurrLoc in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END sh1InChildLocationIsBE *)
    }

    assert(StructurePointerIsKS s).
    { (* BEGIN StructurePointerIsKS s *)
      assert(Hcons0: StructurePointerIsKS s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart HbeqStructNull.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
        /\ structure pdentryPart = structure pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. rewrite Hpdentry2. auto.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HstructEq)]. rewrite HstructEq in *.
      specialize(Hcons0 partition pdentryParts1 HlookupParts1 HbeqStructNull).
      unfold isKS in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart (structure pdentryParts1)) eqn:HbeqCurrStruct.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrStruct. rewrite HbeqCurrStruct in *. rewrite HlookupCurrs1 in *.
        congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END StructurePointerIsKS *)
    }

    assert(NextKSIsKS s).
    { (* BEGIN NextKSIsKS s *)
      assert(Hcons0: NextKSIsKS s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull. unfold isKS in *.
      unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr. rewrite Hs2 in HkernIsKS.
      rewrite Hs2 in HnextAddr. unfold nextKSentry in *. rewrite Hs in HnextKSAddr. rewrite Hs2 in HnextKSAddr.
      simpl in *. destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      destruct (beqAddr currentPart nextKSaddr) eqn:HbeqCurrNextAddr; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull). unfold isKS in *.
      rewrite Hs. rewrite Hs2. simpl. destruct (beqAddr currentPart nextKS) eqn:HbeqCurrNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. rewrite HlookupCurrs1 in *.
        congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR s).
    { (* BEGIN NextKSOffsetIsPADDR s *)
      assert(Hcons0: NextKSOffsetIsPADDR s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros kernel nextKSaddr HkernIsKS HnextAddr. unfold isKS in *. unfold nextKSAddr in *.
      rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr. rewrite Hs2 in HkernIsKS. rewrite Hs2 in HnextAddr.
      simpl in *. destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel nextKSaddr HkernIsKS HnextAddr). destruct Hcons0 as (Hcons0 & HbeqNextAddrNull).
      unfold isPADDR in *. split; trivial.
      rewrite Hs. rewrite Hs2. simpl. destruct (beqAddr currentPart nextKSaddr) eqn:HbeqCurrNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. rewrite HlookupCurrs1 in *.
        congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(NoDupInFreeSlotsList s).
    { (* BEGIN NoDupInFreeSlotsList s *)
      assert(Hcons0: NoDupInFreeSlotsList s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. trivial.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 HlookupParts1].
      specialize(Hcons0 partition pdentryParts1 HlookupParts1).
      destruct Hcons0 as [optFreeList (Hlist & HwellFormed & HnoDup)]. exists optFreeList. split; auto.
      subst optFreeList. apply eq_sym. apply HgetFreeEq.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot s).
    { (* BEGIN freeSlotsListIsFreeSlot s *)
      assert(Hcons0: freeSlotsListIsFreeSlot s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
      rewrite HgetFreeEq in *. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs2 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDTs1 HwellFormed HaddrInList
        HbeqAddrNull). unfold isFreeSlot in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup addr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr currentPart (CPaddr (addr + sh1offset))) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (addr + sh1offset)) (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr currentPart (CPaddr (addr + scoffset))) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(DisjointFreeSlotsLists s).
    { (* BEGIN DisjointFreeSlotsLists s *)
      assert(Hcons0: DisjointFreeSlotsLists s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. assert(Hpart1IsPDTs1: isPDT part1 s1).
      {
        unfold isPDT in *. rewrite Hs in Hpart1IsPDT. rewrite Hs2 in Hpart1IsPDT. simpl in *.
        destruct (beqAddr currentPart part1) eqn:HbeqParts1.
        - rewrite <-DTL.beqAddrTrue in HbeqParts1. subst part1. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(Hpart2IsPDTs1: isPDT part2 s1).
      {
        unfold isPDT in *. rewrite Hs in Hpart2IsPDT. rewrite Hs2 in Hpart2IsPDT. simpl in *.
        destruct (beqAddr currentPart part2) eqn:HbeqParts2.
        - rewrite <-DTL.beqAddrTrue in HbeqParts2. subst part2. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part1 part2 Hpart1IsPDTs1 Hpart2IsPDTs1 HbeqParts).
      rewrite HgetFreeEq. rewrite HgetFreeEq. assumption.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries s).
    { (* BEGIN inclFreeSlotsBlockEntries s *)
      assert(Hcons0: inclFreeSlotsBlockEntries s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs2 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition HpartIsPDTs1). rewrite HgetFreeEq. rewrite HgetKSEq. assumption.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries s).
    { (* BEGIN DisjointKSEntries s *)
      assert(Hcons0: DisjointKSEntries s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. assert(Hpart1IsPDTs1: isPDT part1 s1).
      {
        unfold isPDT in *. rewrite Hs in Hpart1IsPDT. rewrite Hs2 in Hpart1IsPDT. simpl in *.
        destruct (beqAddr currentPart part1) eqn:HbeqParts1.
        - rewrite <-DTL.beqAddrTrue in HbeqParts1. subst part1. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(Hpart2IsPDTs1: isPDT part2 s1).
      {
        unfold isPDT in *. rewrite Hs in Hpart2IsPDT. rewrite Hs2 in Hpart2IsPDT. simpl in *.
        destruct (beqAddr currentPart part2) eqn:HbeqParts2.
        - rewrite <-DTL.beqAddrTrue in HbeqParts2. subst part2. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part1 part2 Hpart1IsPDTs1 Hpart2IsPDTs1 HbeqParts). rewrite HgetKSEq. rewrite HgetKSEq.
      assumption.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree s).
    { (* BEGIN noDupPartitionTree s *)
      assert(Hcons0: noDupPartitionTree s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold noDupPartitionTree. rewrite HgetPartsEqss1. assumption.
      (* END noDupPartitionTree *)
    }

    assert(isParent s).
    { (* BEGIN isParent s *)
      assert(Hcons0: isParent s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEqss1 in *. rewrite HgetChildrenEq in *.
      specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent in *. rewrite Hs.
      rewrite Hs2. simpl. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. rewrite HbeqCurrPart in *. rewrite HlookupCurrs1 in *.
        subst pdparent. rewrite Hpdentry2. reflexivity.
      - rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END isParent *)
    }

    assert(isChild s).
    { (* BEGIN isChild s *)
      assert(Hcons0: isChild s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEqss1 in *.
      rewrite HgetChildrenEq. assert(HparentIsParents1: pdentryParent partition pdparent s1).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. rewrite Hs2 in HparentIsParent. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupCurrs1. simpl in *. subst pdparent.
          rewrite Hpdentry2. reflexivity.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParents1 HbeqPartRoot). assumption.
      (* END isChild *)
    }

    assert(noDupKSEntriesList s).
    { (* BEGIN noDupKSEntriesList s *)
      assert(Hcons0: noDupKSEntriesList s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs2 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition HpartIsPDTs1). rewrite HgetKSEq. assumption.
      (* END noDupKSEntriesList *)
    }

    assert(noDupMappedBlocksList s).
    { (* BEGIN noDupMappedBlocksList s *)
      assert(Hcons0: noDupMappedBlocksList s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs2 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition HpartIsPDTs1). rewrite HgetMappedBEq. assumption.
      (* END noDupMappedBlocksList *)
    }

    assert(wellFormedBlock s).
    { (* BEGIN wellFormedBlock s *)
      assert(Hcons0: wellFormedBlock s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block startaddr endaddr HPflag HstartBlock HendBlock. unfold bentryStartAddr in *.
      unfold bentryPFlag in *. unfold bentryEndAddr in *. rewrite Hs in HPflag. rewrite Hs in HstartBlock.
      rewrite Hs in HendBlock. rewrite Hs2 in HPflag. rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock.
      simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
      (* END wellFormedBlock *)
    }

    assert(parentOfPartitionIsPartition s).
    { (* BEGIN parentOfPartitionIsPartition s *)
      assert(Hcons0: parentOfPartitionIsPartition s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. rewrite Hpdentry2. auto.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HparentsEq)]. rewrite HparentsEq in *.
      specialize(Hcons0 partition pdentryParts1 HlookupParts1).
      destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split; auto. intro HbeqPartRoot.
      specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
      rewrite HgetPartsEqss1. split; trivial. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart (parent pdentryParts1)) eqn:HbeqCurrParent.
      - exists {|
                 structure := structure pdentry2;
                 firstfreeslot := firstfreeslot pdentry2;
                 nbfreeslots := nbfreeslots pdentry2;
                 nbprepare := nbprepare pdentry2;
                 parent := parent pdentry2;
                 MPU := MAL.removeBlockFromPhysicalMPUAux block2InCurrPartAddr realMPU2;
                 vidtAddr := vidtAddr pdentry2
               |}. reflexivity.
      - exists parentEntry. rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END parentOfPartitionIsPartition *)
    }

    assert(NbFreeSlotsISNbFreeSlotsInList s).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition nbfreeslots HpartIsPDT HnbFree. rewrite HgetFreeEq.
      assert(Hparts1: isPDT partition s1 /\ pdentryNbFreeSlots partition nbfreeslots s1).
      {
        unfold isPDT in *. unfold pdentryNbFreeSlots in *. rewrite Hs in HpartIsPDT. rewrite Hs2 in HpartIsPDT.
        rewrite Hs in HnbFree. rewrite Hs2 in HnbFree. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupCurrs1.
          rewrite Hpdentry2 in HnbFree. auto.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct Hparts1 as (HpartIsPDTs1 & HnbFrees1).
      specialize(Hcons0 partition nbfreeslots HpartIsPDTs1 HnbFrees1). assumption.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(maxNbPrepareIsMaxNbKernels s).
    { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. apply HkernListEq in HlistOfKerns.
      specialize(Hcons0 partition kernList HlistOfKerns). assumption.
      (* END maxNbPrepareIsMaxNbKernels *)
    }

    assert(blockInChildHasAtLeastEquivalentBlockInParent s).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s1)
        by (unfold consistency in *; unfold consistency1 in *; intuition). intros pdparent child block startChild
        endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild.
      rewrite HgetPartsEqss1 in *. rewrite HgetChildrenEq in *. rewrite HgetMappedBEq in *. unfold bentryPFlag in *.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs in HstartChild. rewrite Hs in HendChild.
      rewrite Hs in HPflagChild. rewrite Hs2 in HstartChild. rewrite Hs2 in HendChild. rewrite Hs2 in HPflagChild.
      simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        HstartChild HendChild HPflagChild).
      destruct Hcons0 as [blockParent [startP [endP (HblockPMapped & HstartP & HendP & Hbounds)]]].
      exists blockParent. exists startP. exists endP. unfold bentryStartAddr in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs1 in *. exfalso; congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); auto.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(partitionTreeIsTree s).
    { (* BEGIN partitionTreeIsTree s *)
      assert(Hcons0: partitionTreeIsTree s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros child pdparent parentsListBis HbeqChildRoot HchildIsPart HparentIsParent HparentsListBis.
      rewrite HgetPartsEqss1 in *. assert(HparentIsParents1: pdentryParent child pdparent s1).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. rewrite Hs2 in HparentIsParent. simpl in *.
        destruct (beqAddr currentPart child) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst child. rewrite HlookupCurrs1.
          rewrite Hpdentry2 in HparentIsParent. auto.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HparentsListBiss2: isParentsList s2 parentsListBis pdparent).
      {
        revert HparentsListBis.
        apply isParentsListEqPDTSameParent with currentPart {|
                                                              structure := structure pdentry2;
                                                              firstfreeslot := firstfreeslot pdentry2;
                                                              nbfreeslots := nbfreeslots pdentry2;
                                                              nbprepare := nbprepare pdentry2;
                                                              parent := parent pdentry2;
                                                              MPU := MAL.removeBlockFromPhysicalMPUAux
                                                                block2InCurrPartAddr realMPU2;
                                                              vidtAddr := vidtAddr pdentry2
                                                            |}; trivial.
        assert(HparentOfPart: parentOfPartitionIsPartition s1)
          by (unfold consistency in *; unfold consistency1 in *; intuition). unfold pdentryParent in *.
        destruct (lookup child (memory s1) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild).
        destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqChildRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & _). rewrite Hs. rewrite Hs2. simpl.
        destruct (beqAddr currentPart pdparent) eqn:HbeqCurrParent.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite <-HbeqCurrParent in *.
          exists {|
                   structure := structure pdentry1;
                   firstfreeslot := firstfreeslot pdentry1;
                   nbfreeslots := nbfreeslots pdentry1;
                   nbprepare := nbprepare pdentry1;
                   parent := parent pdentry1;
                   MPU := MAL.removeBlockFromPhysicalMPUAux block1InCurrPartAddr realMPU1;
                   vidtAddr := vidtAddr pdentry1
                 |}. exists {|
                               structure := structure pdentry2;
                               firstfreeslot := firstfreeslot pdentry2;
                               nbfreeslots := nbfreeslots pdentry2;
                               nbprepare := nbprepare pdentry2;
                               parent := parent pdentry2;
                               MPU := MAL.removeBlockFromPhysicalMPUAux block2InCurrPartAddr realMPU2;
                               vidtAddr := vidtAddr pdentry2
                             |}. rewrite beqAddrTrue.
          exists {|
                   structure := structure pdentry1;
                   firstfreeslot := firstfreeslot pdentry1;
                   nbfreeslots := nbfreeslots pdentry1;
                   nbprepare := nbprepare pdentry1;
                   parent := parent pdentry1;
                   MPU := MAL.removeBlockFromPhysicalMPUAux block1InCurrPartAddr realMPU1;
                   vidtAddr := vidtAddr pdentry1
                 |}. split; trivial. split; trivial. split; trivial. rewrite Hpdentry2 at 1. split; auto.
          split; try(intro Hcontra; exfalso; congruence). split; auto. rewrite Hpdentry2 at 1. reflexivity.
        - rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. exists parentEntry. exists parentEntry.
          exists {|
                   structure := structure pdentry1;
                   firstfreeslot := firstfreeslot pdentry1;
                   nbfreeslots := nbfreeslots pdentry1;
                   nbprepare := nbprepare pdentry1;
                   parent := parent pdentry1;
                   MPU := MAL.removeBlockFromPhysicalMPUAux block1InCurrPartAddr realMPU1;
                   vidtAddr := vidtAddr pdentry1
                 |}. rewrite <-HparentIsParents1 in *. split; trivial. split; trivial. split; trivial.
          rewrite Hpdentry2 at 1. split; auto. split; auto. intro Hcontra; exfalso; congruence.
      }
      assert(HparentsListBiss1: isParentsList s1 parentsListBis pdparent).
      {
        revert HparentsListBiss2.
        assert(HparentOfPart: parentOfPartitionIsPartition s1)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        apply isParentsListEqPDTSameParent with currentPart {|
                                                              structure := structure pdentry1;
                                                              firstfreeslot := firstfreeslot pdentry1;
                                                              nbfreeslots := nbfreeslots pdentry1;
                                                              nbprepare := nbprepare pdentry1;
                                                              parent := parent pdentry1;
                                                              MPU := MAL.removeBlockFromPhysicalMPUAux
                                                                block1InCurrPartAddr realMPU1;
                                                              vidtAddr := vidtAddr pdentry1
                                                            |}; trivial. unfold pdentryParent in *.
        destruct (lookup child (memory s1) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild).
        destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqChildRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & _). rewrite Hs2. simpl.
        destruct (beqAddr currentPart pdparent) eqn:HbeqCurrParent.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite <-HbeqCurrParent in *. exists pdentry1.
          exists {|
                   structure := structure pdentry1;
                   firstfreeslot := firstfreeslot pdentry1;
                   nbfreeslots := nbfreeslots pdentry1;
                   nbprepare := nbprepare pdentry1;
                   parent := parent pdentry1;
                   MPU := MAL.removeBlockFromPhysicalMPUAux block1InCurrPartAddr realMPU1;
                   vidtAddr := vidtAddr pdentry1
                 |}.
          exists pdentry1. split; trivial. split; trivial. split; trivial. split; trivial.
          split; try(intro Hcontra; exfalso; congruence). split; auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          exists parentEntry. exists parentEntry. exists pdentry1. rewrite <-HparentIsParents1 in *.
          split; trivial. split; trivial. split; trivial. split; trivial.
          split; auto. intro Hcontra; exfalso; congruence.
      }
      specialize(Hcons0 child pdparent parentsListBis HbeqChildRoot HchildIsPart HparentIsParents1 HparentsListBiss1).
      assumption.
      (* END partitionTreeIsTree *)
    }

    assert(kernelEntriesAreValid s).
    { (* BEGIN kernelEntriesAreValid s *)
      assert(Hcons0: kernelEntriesAreValid s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros kernel idx HkernIsKS Hidx. unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs2 in HkernIsKS.
      simpl in *. destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel idx HkernIsKS Hidx). unfold isBE in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart (CPaddr (kernel + idx))) eqn:HbeqCurrIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrIdx. rewrite HbeqCurrIdx in *. rewrite HlookupCurrs1 in *.
        exfalso; congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END kernelEntriesAreValid *)
    }

    assert(nextKernelIsValid s).
    { (* BEGIN nextKernelIsValid s *)
      assert(Hcons0: nextKernelIsValid s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros kernel HkernIsKS. unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs2 in HkernIsKS.
      simpl in *. destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 kernel HkernIsKS).
      destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNextA & Hnext)]). split; trivial. exists nextAddr. split.
      - intro Hp. specialize(HlookupNextA Hp). rewrite Hs. rewrite Hs2. simpl.
        destruct (beqAddr currentPart {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqCurrNext.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. exfalso; congruence.
        }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - destruct Hnext as [HnextIsKS | HnextIsNull]; auto. left. rewrite Hs. rewrite Hs2. simpl.
        unfold isKS in *. destruct (beqAddr currentPart nextAddr) eqn:HbeqCurrNext.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. rewrite HlookupCurrs1 in *.
          congruence.
        }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns s).
    { (* BEGIN noDupListOfKerns s *)
      assert(Hcons0: noDupListOfKerns s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. apply HkernListEq in HlistOfKerns.
      specialize(Hcons0 partition kernList HlistOfKerns). assumption.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax s).
    { (* BEGIN MPUsizeIsBelowMax s *)
      assert(Hcons0: MPUsizeIsBelowMax s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition MPUlist HMPU. unfold pdentryMPU in *. rewrite Hs in HMPU. rewrite Hs2 in HMPU. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqParts.
      - simpl in *. subst MPUlist. specialize(Hcons0 currentPart realMPU1 HMPUs1).
        pose proof (removeBlockFromPhysicalMPUAuxLenEq block2InCurrPartAddr realMPU2). rewrite Hs2 in HMPUs2.
        simpl in *. rewrite beqAddrTrue in *. simpl in *.
        pose proof (removeBlockFromPhysicalMPUAuxLenEq block1InCurrPartAddr realMPU1). rewrite <-HMPUs2 in *. lia.
      - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 partition MPUlist HMPU).
        assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart s).
    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. rewrite Hpdentry2. auto.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HparentsEq)]. rewrite HparentsEq in *.
      unfold scentryOrigin in *. rewrite Hs in Horigin. rewrite Hs2 in Horigin. simpl in *.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentryParts1 block scentryaddr scorigin HpartIsPart HlookupParts1 HblockMapped Hsce
        Horigin). destruct Hcons0 as (HblockP & HlebStartOrigin). split.
      - intro HbeqPartRoot. specialize(HblockP HbeqPartRoot).
        destruct HblockP as [blockParent (HblockPMapped & HstartP & Hincl)]. exists blockParent. rewrite Hs.
        rewrite Hs2. unfold bentryStartAddr in *. simpl. destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs1 in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. split; trivial. split; trivial.
        intros addr HaddrInBlock. apply Hincl.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(simpl in *; exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      - intros startaddr Hstart. unfold bentryStartAddr in *. rewrite Hs in Hstart. rewrite Hs2 in Hstart. simpl in *.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. auto.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut s).
    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
        Hsce HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. rewrite Hpdentry2. auto.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HparentsEq)]. rewrite HparentsEq in *.
      unfold scentryNext in *. rewrite Hs in Hnext. rewrite Hs2 in Hnext. simpl in *.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold bentryEndAddr in *. rewrite Hs.
      rewrite Hs in HendBlock. rewrite Hs2. rewrite Hs2 in HendBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentryParts1 block scentryaddr scnext endaddr HpartIsPart HlookupParts1
        HblockMapped HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockPMapped & HendP & HltEnds & Hincl)]]. exists blockParent.
      exists endParent. unfold bentryEndAddr in *. destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs1 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      (* END nextImpliesBlockWasCut *)
    }

    assert(blocksAddressesTypes s).
    { (* BEGIN blocksAddressesTypes s *)
      assert(Hcons0: blocksAddressesTypes s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartBlock. rewrite Hs in HendBlock.
      rewrite Hs in HPflagBlock. rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. rewrite Hs2 in HPflagBlock.
      simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
      rewrite Hs in HPDchildBlock. rewrite Hs2 in HPDchildBlock. simpl in *.
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock).
      destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hnone]].
      - left. split.
        + unfold isKS in *. rewrite Hs. rewrite Hs2. simpl.
          destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart.
          { rewrite <-DTL.beqAddrTrue in HbeqCurrStart. subst startaddr. rewrite HlookupCurrs1 in *. congruence. }
          rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
          destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
          * left. unfold isBE in *. rewrite Hs. rewrite Hs2. simpl.
            destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            { rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs1 in *. congruence. }
            rewrite <-beqAddrFalse in *. rewrite beqAddrTrue.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. left. unfold isSHE in *. rewrite Hs. rewrite Hs2. simpl.
            destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            { rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs1 in *. congruence. }
            rewrite <-beqAddrFalse in *. rewrite beqAddrTrue.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. left. unfold isSCE in *. rewrite Hs. rewrite Hs2. simpl.
            destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            { rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs1 in *. congruence. }
            rewrite <-beqAddrFalse in *. rewrite beqAddrTrue.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. right. left. unfold isPADDR in *. rewrite Hs. rewrite Hs2. simpl.
            destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            { rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs1 in *. congruence. }
            rewrite <-beqAddrFalse in *. rewrite beqAddrTrue.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. right. right. rewrite Hs. rewrite Hs2. simpl.
            destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            { rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. congruence. }
            rewrite <-beqAddrFalse in *. rewrite beqAddrTrue.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. left. split.
        + unfold isPDT in *. rewrite Hs. rewrite Hs2. simpl.
          destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart; trivial.
          rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). rewrite Hs. rewrite Hs2. simpl.
          destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
          { rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. congruence. }
          rewrite <-beqAddrFalse in *. rewrite beqAddrTrue.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. right. intros addr HaddrInRange. specialize(Hnone addr HaddrInRange). rewrite Hs. rewrite Hs2. simpl.
        destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. congruence. }
        rewrite <-beqAddrFalse in *. rewrite beqAddrTrue.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END blocksAddressesTypes *)
    }

    assert(notPDTIfNotPDflag s).
    { (* BEGIN notPDTIfNotPDflag s *)
      assert(Hcons0: notPDTIfNotPDflag s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild. unfold bentryStartAddr in *.
      unfold sh1entryAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartBlock. rewrite Hs in HPflag.
      rewrite Hs in Hsh1. rewrite Hs2 in HstartBlock. rewrite Hs2 in HPflag. rewrite Hs2 in Hsh1. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
      unfold sh1entryPDflag in *. rewrite Hs in HPDchild. rewrite Hs2 in HPDchild. rewrite Hs in HPDflag.
      rewrite Hs2 in HPDflag. simpl in *.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild). contradict Hcons0.
      unfold isPDT in *. rewrite Hs in Hcons0. rewrite Hs2 in Hcons0. simpl in *.
      destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrStart. rewrite HbeqCurrStart in *. rewrite HlookupCurrs1. trivial.
      - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END notPDTIfNotPDflag *)
    }

    assert(nextKernAddrIsInSameBlock s).
    { (* BEGIN nextKernAddrIsInSameBlock s *)
      assert(Hcons0: nextKernAddrIsInSameBlock s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock HkernIsKS.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartBlock.
      rewrite Hs in HendBlock. rewrite Hs in HPflagBlock. rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock.
      rewrite Hs2 in HPflagBlock. simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
      rewrite Hs in HPDchildBlock. rewrite Hs2 in HPDchildBlock. simpl in *.
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold isKS in *. rewrite Hs in HkernIsKS.
      rewrite Hs2 in HkernIsKS. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock HkernIsKS).
      assumption.
      (* END nextKernAddrIsInSameBlock *)
    }

    assert(blockBelongsToAPart s).
    { (* BEGIN blockBelongsToAPart s *)
      assert(Hcons0: blockBelongsToAPart s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block HPflagBlock. unfold bentryPFlag in *. rewrite Hs in HPflagBlock. rewrite Hs2 in HPflagBlock.
      simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 block HPflagBlock).
      rewrite HgetPartsEqss1. destruct Hcons0 as [part Hcons0]. exists part. rewrite HgetMappedBEq. assumption.
      (* END blockBelongsToAPart *)
    }

    assert(PDflagMeansNoChild s).
    { (* BEGIN PDflagMeansNoChild s *)
      assert(Hcons0: PDflagMeansNoChild s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block HblockIsBE HPDflagBlock. unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs2 in HblockIsBE.
      simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *. unfold sh1entryPDchild.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDflag in *.
      rewrite Hs in HPDflagBlock. rewrite Hs2 in HPDflagBlock. rewrite Hs. rewrite Hs2. simpl in *.
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block HblockIsBE HPDflagBlock). assumption.
      (* END PDflagMeansNoChild *)
    }

    assert(nbPrepareIsNbKern s).
    { (* BEGIN nbPrepareIsNbKern s *)
      assert(Hcons0: nbPrepareIsNbKern s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
        /\ structure pdentryPart = structure pdentryParts0 /\ nbprepare pdentryPart = nbprepare pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. rewrite Hpdentry2. auto.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HstructEq & HnbPrepEq)]. rewrite HstructEq.
      rewrite HnbPrepEq. specialize(Hcons0 partition pdentryParts1 HlookupParts1).
      assert(Heq: completeListOfKernels (structure pdentryParts1) s
        = completeListOfKernels (structure pdentryParts1) s1).
      {
        assert(Heqs2: completeListOfKernels (structure pdentryParts1) s2
          = completeListOfKernels (structure pdentryParts1) s1).
        { rewrite Hs2. apply completeListOfKernelsEqPDT. unfold isPDT. rewrite HlookupCurrs1. trivial. }
        rewrite <-Heqs2. rewrite Hs. apply completeListOfKernelsEqPDT. unfold isPDT. rewrite HlookupCurrs2. trivial.
      }
      rewrite Heq. assumption.
     (* END nbPrepareIsNbKern *)
    }

    assert(pdchildIsPDT s).
    { (* BEGIN pdchildIsPDT s *)
      assert(Hcons0: pdchildIsPDT s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part block sh1entryaddr idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
      rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *. unfold sh1entryAddr in *. unfold sh1entryPDchild in *.
      rewrite Hs in Hsh1. rewrite Hs2 in Hsh1. rewrite Hs in HPDchild. rewrite Hs2 in HPDchild. simpl in *.
      rewrite beqAddrTrue in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull).
      rewrite HgetChildrenEq. assumption.
      (* END pdchildIsPDT *)
    }

    assert(childBlockNullIfChildNull s).
    { (* BEGIN childBlockNullIfChildNull s *)
      assert(Hcons0: childBlockNullIfChildNull s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part block sh1entryaddr HpartBisIsPart HblockMapped Hsh1 HPDchild.
      rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *. unfold sh1entryAddr in *. unfold sh1entryPDchild in *.
      unfold sh1entryInChildLocation. rewrite Hs in Hsh1. rewrite Hs2 in Hsh1. rewrite Hs in HPDchild.
      rewrite Hs2 in HPDchild. rewrite Hs. rewrite Hs2. simpl in *.
      rewrite beqAddrTrue in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr HpartBisIsPart HblockMapped Hsh1 HPDchild).
      unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). destruct Hcons0. split; trivial. intro. exfalso; congruence.
      (* END pdchildIsPDT *)
    }

    assert(accessibleBlocksArePresent s).
    { (* BEGIN accessibleBlocksArePresent s *)
      assert(Hcons0: accessibleBlocksArePresent s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block HAflag. unfold bentryAFlag in *. unfold bentryPFlag. rewrite Hs in HAflag. rewrite Hs2 in HAflag.
      rewrite Hs. rewrite Hs2. simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. apply Hcons0; assumption.
      (* END childLocHasSameStart *)
    }

    unfold consistency1. intuition.
  }

  assert(HgetMappedPEq: forall partition, getMappedPaddr partition s = getMappedPaddr partition s1).
  {
    intro partition. assert(Heqs2: getMappedPaddr partition s2 = getMappedPaddr partition s1).
    {
      rewrite Hs2. apply getMappedPaddrEqPDT with pdentry1; trivial.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite <-Heqs2. rewrite Hs. apply getMappedPaddrEqPDT with pdentry2; trivial.
  }
  assert(HgetAccMappedPEq: forall partition, getAccessibleMappedPaddr partition s
    = getAccessibleMappedPaddr partition s1).
  {
    intro partition. assert(Heqs2: getAccessibleMappedPaddr partition s2 = getAccessibleMappedPaddr partition s1).
    {
      rewrite Hs2. apply getAccessibleMappedPaddrEqPDT with pdentry1; trivial.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite <-Heqs2. rewrite Hs. apply getAccessibleMappedPaddrEqPDT with pdentry2; trivial.
  }
  assert(HgetConfigPEq: forall partition, isPDT partition s1
    -> getConfigPaddr partition s = getConfigPaddr partition s1).
  {
    intros partition HpartIsPDT. assert(Heqs2: getConfigPaddr partition s2 = getConfigPaddr partition s1).
    {
      rewrite Hs2. apply getConfigPaddrEqPDT with pdentry1; trivial.
    }
    rewrite <-Heqs2. rewrite Hs. apply getConfigPaddrEqPDT with pdentry2; trivial. unfold isPDT. rewrite Hs2. simpl.
    destruct (beqAddr currentPart partition) eqn:HbeqParts; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HgetAccMappedBEq: forall partition, getAccessibleMappedBlocks partition s
    = getAccessibleMappedBlocks partition s1).
  {
    intro partition. assert(Heqs2: getAccessibleMappedBlocks partition s2 = getAccessibleMappedBlocks partition s1).
    {
      rewrite Hs2. apply getAccessibleMappedBlocksEqPDT with pdentry1; trivial.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    rewrite <-Heqs2. rewrite Hs. apply getAccessibleMappedBlocksEqPDT with pdentry2; trivial.
  }

  assert(consistency2 s).
  {
    assert(noDupMappedPaddrList s).
    { (* BEGIN noDupMappedPaddrList s *)
      assert(Hcons0: noDupMappedPaddrList s1) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition HpartIsPDT. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs2 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition HpartIsPDTs1). rewrite HgetMappedPEq. assumption.
      (* END noDupMappedPaddrList *)
    }

    assert(accessibleParentPaddrIsAccessibleIntoChild s).
    { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
      assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s1)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
      rewrite HgetPartsEqss1 in *. rewrite HgetChildrenEq in *. rewrite HgetAccMappedPEq in *.
      rewrite HgetMappedPEq in *. specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild). auto.
      (* END accessibleParentPaddrIsAccessibleIntoChild *)
    }

    assert(sharedBlockPointsToChild s).
    { (* BEGIN sharedBlockPointsToChild s *)
      assert(Hcons0: sharedBlockPointsToChild s1) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParent HblockParentMapped Hsh1. rewrite HgetPartsEqss1 in *. rewrite HgetChildrenEq in *.
      assert(isPDT child s1).
      { apply childrenArePDT with pdparent; unfold consistency in *; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *. unfold getUsedPaddr in *. rewrite HgetMappedPEq in *.
      rewrite HgetConfigPEq in *; trivial.
      assert(HBP: In addr (getAllPaddrAux [blockParent] s1) /\ sh1entryAddr blockParent sh1entryaddr s1).
      {
        unfold sh1entryAddr in *. rewrite Hs in HaddrInBlockParent. rewrite Hs2 in HaddrInBlockParent.
        rewrite Hs in Hsh1. rewrite Hs2 in Hsh1. simpl in *.
        destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HBP as (HaddrInBlockParents1 & Hsh1s1).
      specialize(Hcons0 pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParents1 HblockParentMapped Hsh1s1). unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
      rewrite Hs. rewrite Hs2. simpl. destruct (beqAddr currentPart (CPaddr (blockParent+sh1offset))) eqn:HbeqCurrSh1.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. assumption. }
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END sharedBlockPointsToChild *)
    }

    assert(adressesRangePreservedIfOriginAndNextOk s).
    { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
      assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s1)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition pdentryPart block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE
        HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. rewrite HgetPartsEqss1 in *.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. rewrite Hpdentry2. auto.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HparentsEq)]. rewrite HparentsEq.
      rewrite HgetMappedBEq in *. unfold isBE in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      unfold bentryPFlag in *. rewrite Hs in HblockIsBE. rewrite Hs in HstartBlock. rewrite Hs in HendBlock.
      rewrite Hs in HPflag. rewrite Hs2 in HblockIsBE. rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock.
      rewrite Hs2 in HPflag. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *. unfold sh1entryPDchild.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold scentryOrigin in *.
      unfold scentryNext in *. rewrite Hs in Horigin. rewrite Hs2 in Horigin. rewrite Hs in Hnext.
      rewrite Hs2 in Hnext. simpl in *.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentryParts1 block scentryaddr startBlock endBlock HpartIsPart HblockMapped
        HblockIsBE HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupParts1 HbeqPartRoot).
      destruct Hcons0 as [blockParent (HblockPMapped & HBPIsBE & Hcons0)]. exists blockParent. unfold isBE in *.
      rewrite Hs. rewrite Hs2. simpl. destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs1 in *. exfalso; congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); auto.
      (* END adressesRangePreservedIfOriginAndNextOk *)
    }

    assert(childsBlocksPropsInParent s).
    { (* BEGIN childsBlocksPropsInParent s *)
      assert(Hcons0: childsBlocksPropsInParent s1) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
        HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
        HPflagParent HlebStart HgebEnd. rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *.
      rewrite HgetChildrenEq in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
      rewrite Hs in HstartChild. rewrite Hs in HendChild. rewrite Hs in HPflagChild. rewrite Hs2 in HstartChild.
      rewrite Hs2 in HendChild. rewrite Hs2 in HPflagChild. simpl in *.
      destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(HlookupBPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
      {
        rewrite Hs in HendParent. rewrite Hs2 in HendParent. rewrite Hs. rewrite Hs2. simpl in *.
        destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold checkChild. unfold bentryAFlag. rewrite HlookupBPEq in *.
      specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
        HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
        HPflagParent HlebStart HgebEnd).
      destruct Hcons0 as (HcheckChild & HPDchildNotNull & HlocNotNull & HAflag).
      assert(HlookupSh1Eq: lookup (CPaddr (blockParent+sh1offset)) (memory s) beqAddr
        = lookup (CPaddr (blockParent+sh1offset)) (memory s1) beqAddr).
      {
        assert(HBPIsBE: isBE blockParent s1).
        {
          unfold isBE. destruct (lookup blockParent (memory s1) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
        }
        assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s1)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(Hsh1IsSHE blockParent HBPIsBE). unfold isSHE in *. rewrite Hs. rewrite Hs2. simpl.
        destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold sh1entryPDchild. unfold sh1entryInChildLocation in *. rewrite HlookupSh1Eq.
      split; try(split; try(split)); auto. intros blockIDInChild Hloc. apply HlocNotNull.
      destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). destruct Hloc as (Hloc & HlocNotNulls). split; trivial. intro HbeqLocNull.
      specialize(HlocNotNulls HbeqLocNull). unfold isBE in *. rewrite Hs in HlocNotNulls. rewrite Hs2 in HlocNotNulls.
      simpl in *. destruct (beqAddr currentPart blockIDInChild) eqn:HbeqCurrLoc; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END childsBlocksPropsInParent *)
    }

    assert(noChildImpliesAddressesNotShared s).
    { (* BEGIN noChildImpliesAddressesNotShared s *)
      assert(Hcons0: noChildImpliesAddressesNotShared s1)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition pdentryPart block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild child addr
        HchildIsChild HaddrInBlock. rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *. rewrite HgetMappedPEq.
      rewrite HgetChildrenEq in *. unfold sh1entryPDchild in *. rewrite Hs in HPDchild. rewrite Hs2 in HPDchild.
      rewrite Hs in HaddrInBlock. rewrite Hs2 in HaddrInBlock. simpl in *.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(simpl in *; exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. assumption.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct HlookupParts1 as [pdentryParts1 HlookupParts1].
      specialize(Hcons0 partition pdentryParts1 block sh1entryaddr HpartIsPart HlookupParts1 HblockMapped Hsh1
        HPDchild child addr HchildIsChild HaddrInBlock). assumption.
      (* END noChildImpliesAddressesNotShared *)
    }

    assert(kernelsAreNotAccessible s).
    { (* BEGIN kernelsAreNotAccessible s *)
      assert(Hcons0: kernelsAreNotAccessible s1) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros block startaddr Hstart HPflag HstartIsKS. unfold bentryStartAddr in *. unfold bentryPFlag in *.
      unfold isKS in *. unfold bentryAFlag. rewrite Hs in Hstart. rewrite Hs in HPflag. rewrite Hs in HstartIsKS.
      rewrite Hs. rewrite Hs2 in Hstart. rewrite Hs2 in HPflag. rewrite Hs2 in HstartIsKS. rewrite Hs2. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(congruence).
      destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr Hstart HPflag HstartIsKS). assumption.
      (* END kernelsAreNotAccessible *)
    }

    assert(blockAndNextAreSideBySide s).
    { (* BEGIN blockAndNextAreSideBySide s *)
      assert(Hcons0: blockAndNextAreSideBySide s1) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
        Hnext. rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *. unfold bentryEndAddr in *.
      unfold scentryNext in *. rewrite Hs in HendBlock. rewrite Hs in Hnext. rewrite Hs2 in HendBlock.
      rewrite Hs2 in Hnext. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce
        HbeqNextNull Hnext). unfold bentryStartAddr in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart scnext) eqn:HbeqCurrNext.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrNext. subst scnext. rewrite HlookupCurrs1 in *. congruence. }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END blockAndNextAreSideBySide *)
    }

    assert(parentBlocksBoundsIfNoNext s).
    { (* BEGIN parentBlocksBoundsIfNoNext s *)
      assert(Hcons0: parentBlocksBoundsIfNoNext s1) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition pdentryPart block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock HendBlock
        Hsce Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *.
      assert(HlookupParts1: exists pdentryParts0, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts0)
        /\ parent pdentryPart = parent pdentryParts0).
      {
        rewrite Hs in HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. exists pdentry1. rewrite Hpdentry2. auto.
        - rewrite <-beqAddrFalse in *. exists pdentryPart. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HparentsEq)]. rewrite HparentsEq.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold scentryNext in *. rewrite Hs in Hnext.
      rewrite Hs in HstartBlock. rewrite Hs in HendBlock. rewrite Hs2 in Hnext. rewrite Hs2 in HstartBlock.
      rewrite Hs2 in HendBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentryParts1 block scentryaddr startaddr endaddr HpartIsPart HblockMapped
        HstartBlock HendBlock Hsce Hnext HbeqPartRoot HlookupParts1).
      destruct Hcons0 as [blockParent [startP (HblockPMapped & HstartP & Hcons0)]]. exists blockParent. exists startP.
      unfold bentryStartAddr in *. rewrite Hs. rewrite Hs2. simpl.
      destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrBP. subst blockParent. rewrite HlookupCurrs1 in *. exfalso; congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); auto.
      (* END parentBlocksBoundsIfNoNext *)
    }

    assert(HlocPropss1: childLocMappedInChild s1).
    { (* BEGIN childLocMappedInChild s1 *)
      assert(Hcons0: childLocMappedInChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros part block sh1entryaddr blockChild idchild startaddr. revert HisBuilt. unfold isPDT in *.
      destruct (lookup currentPart (memory s0) beqAddr) eqn:HlookupCurrs0; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). specialize(Hcons0 part block sh1entryaddr blockChild idchild startaddr).
      apply isBuiltFromWriteAccessibleRec.childLocMappedInChildPartialPreservedIsBuiltRec with p blockBase; trivial.
      1,2,3,4,5,6,7,8,9: unfold consistency in *; unfold consistency1 in *; intuition.
      1,2: unfold consistency in *; unfold consistency2 in *; intuition.
    }

    assert(childLocMappedInChild s).
    { (* BEGIN childLocMappedInChild s *)
      intros part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1 HPDchild Hloc
        HbeqIdChildNull Hstart HstartNotKern. rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *.
      unfold sh1entryAddr in *. rewrite Hs in Hstart. rewrite Hs2 in Hstart.
      unfold sh1entryPDchild in *. unfold sh1entryInChildLocationWeak in *. unfold bentryStartAddr in *.
      rewrite Hs in Hsh1. rewrite Hs2 in Hsh1.
      rewrite Hs in HPDchild. rewrite Hs2 in HPDchild. rewrite Hs in Hloc. rewrite Hs2 in Hloc. simpl in *.
      rewrite beqAddrTrue in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (*assert(Hlocs1: sh1entryInChildLocation sh1entryaddr blockChild s1).
      {
        unfold sh1entryInChildLocation. destruct (lookup sh1entryaddr (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence). destruct Hloc as (Hloc & HlocIsBE). split; trivial. intro HbeqLocNull.
        specialize(HlocIsBE HbeqLocNull). unfold isBE in *. simpl in *. rewrite beqAddrTrue in *.
        destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }*)
      assert(HstartNotKerns1: ~isKS startaddr s1).
      {
        unfold isKS in *. contradict HstartNotKern. rewrite Hs. rewrite Hs2. simpl. rewrite beqAddrTrue.
        destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart.
        { rewrite <-DTL.beqAddrTrue in HbeqCurrStart. subst startaddr. rewrite HlookupCurrs1 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(HlocPropss1 part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1
        HPDchild Hloc HbeqIdChildNull Hstart HstartNotKerns1).
      destruct HlocPropss1 as (HbeqBCNull & HBCMapped & HstartChild). split; trivial.
      split; trivial. unfold bentryStartAddr in *. rewrite Hs. rewrite Hs2.
      simpl. rewrite beqAddrTrue. destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrBC. subst blockChild. rewrite HlookupCurrs1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END childLocMappedInChild *)
    }

    assert(HsameStarts1: childLocHasSameStart s1).
    { (* BEGIN childLocHasSameStart s1 *)
      assert(Hcons0: childLocHasSameStart s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros part block sh1entryaddr blockChild idchild. revert HisBuilt.
      specialize(Hcons0 part block sh1entryaddr blockChild idchild).
      apply isBuiltFromWriteAccessibleRec.childLocHasSameStartPartialPreservedIsBuiltRec with blockBase; trivial.
      1,2,3,4,5,6,7,8,9: unfold consistency in *; unfold consistency1 in *; intuition.
      1,2: unfold consistency in *; unfold consistency2 in *; intuition.
      (* END childLocHasSameStart *)
    }

    assert(childLocHasSameStart s).
    { (* BEGIN childLocHasSameStart s *)
      intros part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1 HPDchild Hloc
        HbeqIdChildNull HbeqBCNull startaddr Hstart. rewrite HgetPartsEqss1 in *. rewrite HgetMappedBEq in *.
      unfold sh1entryAddr in *. rewrite Hs in Hstart. rewrite Hs2 in Hstart.
      unfold sh1entryPDchild in *. unfold sh1entryInChildLocationWeak in *. unfold bentryStartAddr in *.
      rewrite Hs in Hsh1. rewrite Hs2 in Hsh1.
      rewrite Hs in HPDchild. rewrite Hs2 in HPDchild. rewrite Hs in Hloc. rewrite Hs2 in Hloc. simpl in *.
      rewrite beqAddrTrue in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(HsameStarts1 part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1
        HPDchild Hloc HbeqIdChildNull HbeqBCNull startaddr Hstart).
      unfold bentryStartAddr in *. rewrite Hs. rewrite Hs2.
      simpl. rewrite beqAddrTrue. destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrBC. subst blockChild. rewrite HlookupCurrs1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END childLocHasSameStart *)
    }

    unfold consistency2. intuition.
  }

  instantiate(1 := fun s => partitionsIsolation s /\ verticalSharing s /\ kernelDataIsolation s).
  assert(verticalSharing s).
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild. rewrite HgetPartsEqss1 in *. rewrite HgetChildrenEq in *.
    specialize(HVSs1 pdparent child HparentIsPart HchildIsChild). unfold getUsedPaddr. rewrite HgetMappedPEq.
    rewrite HgetMappedPEq. rewrite HgetConfigPEq; trivial.
    apply childrenArePDT with pdparent; trivial. unfold consistency in *; unfold consistency1 in *; intuition.
    (* END verticalSharing *)
  }

  assert(partitionsIsolation s).
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
    rewrite HgetPartsEqss1 in *. rewrite HgetChildrenEq in *.
    specialize(HPIs1 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
    unfold getUsedPaddr. rewrite HgetMappedPEq. rewrite HgetMappedPEq. assert(isPDT child1 s1).
    { apply childrenArePDT with pdparent; trivial. unfold consistency in *; unfold consistency1 in *; intuition. }
    assert(isPDT child2 s1).
    { apply childrenArePDT with pdparent; trivial. unfold consistency in *; unfold consistency1 in *; intuition. }
    rewrite HgetConfigPEq; trivial. rewrite HgetConfigPEq; trivial.
    (* END partitionsIsolation *)
  }

  assert(kernelDataIsolation s).
  { (* BEGIN kernelDataIsolation s *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart. rewrite HgetPartsEqss1 in *.
    specialize(HKDIs1 part1 part2 Hpart1IsPart Hpart2IsPart). rewrite HgetAccMappedPEq.
    rewrite HgetConfigPEq; trivial.
    apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
    (* END kernelDataIsolation *)
  }
  split; auto.

  rewrite <-beqAddrFalse in *. unfold consistency. split; auto. split; trivial. split.
  - unfold isPDT. rewrite Hs. simpl. rewrite beqAddrTrue. trivial.
  - rewrite HgetAccMappedBEq.
    assert(Heq: getAccessibleMappedBlocks currentPart s1 = getAccessibleMappedBlocks currentPart s0).
    {
      revert HisBuilt.
      apply isBuiltFromWriteAccessibleRec.getAccessibleMappedBlocksEqBuiltWithWriteAccAccessNoChange with blockBase
        blockBase bentryBase0; auto; unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *;
        intuition.
    }
    rewrite Heq. intro. apply accessibleBlockIsAccessibleMapped; assumption.
}

intro enable_succeeded. eapply weaken. apply WP.ret. intros s Hprops. simpl.
destruct Hprops as [s0 ((HPIs0 & HVSs0 & HKDIs0) & Hconsists0 & HcurrIsPDTs0 & Hconsists & HbeqCurrNull & _ &
  HcurrIsPDTs & [pdentry (HlookupCurrs0 & HgetKSCurrEq & (HmultIsPDT & HgetKSEq & HgetMappedPEq & HgetConfigPEq &
  HgetPartsEq & HgetChildrenEq & HgetMappedBEq & HgetAccMappedBEq & HgetAccMappedPEq) & HisPDTEq & HenableSucc &
  HenableNotSucc)])].
assert(HgetKSEqs: forall partition, getKSEntries partition s = getKSEntries partition s0).
{
  intro partition. unfold is_true in *. destruct enable_succeeded.
  - assert(HeqTriv: true = true) by reflexivity. specialize(HenableSucc HeqTriv).
    destruct HenableSucc as [pdentry1 (Hs & _)]. rewrite Hs. apply getKSEntriesEqPDT with pdentry; trivial.
    unfold consistency in *; unfold consistency1 in *; intuition.
  - assert(HeqTriv: false <> true) by auto. specialize(HenableNotSucc HeqTriv). subst s. reflexivity.
}
assert(HgetMappedBEqs: forall partition, getMappedBlocks partition s = getMappedBlocks partition s0).
{
  intro partition. unfold is_true in *. destruct enable_succeeded.
  - assert(HeqTriv: true = true) by reflexivity. specialize(HenableSucc HeqTriv).
    destruct HenableSucc as [pdentry1 (Hs & _)]. rewrite Hs. apply getMappedBlocksEqPDT with pdentry; trivial.
    unfold consistency in *; unfold consistency1 in *; intuition.
  - assert(HeqTriv: false <> true) by auto. specialize(HenableNotSucc HeqTriv). subst s. reflexivity.
}
assert(HgetMappedPEqs: forall partition, getMappedPaddr partition s = getMappedPaddr partition s0).
{
  intro partition. unfold is_true in *. destruct enable_succeeded.
  - assert(HeqTriv: true = true) by reflexivity. specialize(HenableSucc HeqTriv).
    destruct HenableSucc as [pdentry1 (Hs & _)]. rewrite Hs. apply getMappedPaddrEqPDT with pdentry; trivial.
    unfold consistency in *; unfold consistency1 in *; intuition.
  - assert(HeqTriv: false <> true) by auto. specialize(HenableNotSucc HeqTriv). subst s. reflexivity.
}
assert(HgetAccMappedPEqs: forall partition, getAccessibleMappedPaddr partition s
  = getAccessibleMappedPaddr partition s0).
{
  intro partition. unfold is_true in *. destruct enable_succeeded.
  - assert(HeqTriv: true = true) by reflexivity. specialize(HenableSucc HeqTriv).
    destruct HenableSucc as [pdentry1 (Hs & _)]. rewrite Hs.
    apply getAccessibleMappedPaddrEqPDT with pdentry; trivial.
    unfold consistency in *; unfold consistency1 in *; intuition.
  - assert(HeqTriv: false <> true) by auto. specialize(HenableNotSucc HeqTriv). subst s. reflexivity.
}
assert(HgetConfigPEqs: forall partition, isPDT partition s0
  -> getConfigPaddr partition s = getConfigPaddr partition s0).
{
  intros partition HpartIsPDT. unfold is_true in *. destruct enable_succeeded.
  - assert(HeqTriv: true = true) by reflexivity. specialize(HenableSucc HeqTriv).
    destruct HenableSucc as [pdentry1 (Hs & _)]. rewrite Hs. apply getConfigPaddrEqPDT with pdentry; trivial.
  - assert(HeqTriv: false <> true) by auto. specialize(HenableNotSucc HeqTriv). subst s. reflexivity.
}
assert(HgetPartsEqs: forall partition, getPartitions partition s = getPartitions partition s0).
{
  intro partition. unfold is_true in *. destruct enable_succeeded.
  - assert(HeqTriv: true = true) by reflexivity. specialize(HenableSucc HeqTriv).
    destruct HenableSucc as [pdentry1 (Hs & _)]. rewrite Hs. apply getPartitionsEqPDT with pdentry; trivial.
    1,2: unfold consistency in *; unfold consistency1 in *; intuition.
  - assert(HeqTriv: false <> true) by auto. specialize(HenableNotSucc HeqTriv). subst s. reflexivity.
}
assert(HgetChildrenEqs: forall partition, getChildren partition s = getChildren partition s0).
{
  intro partition. unfold is_true in *. destruct enable_succeeded.
  - assert(HeqTriv: true = true) by reflexivity. specialize(HenableSucc HeqTriv).
    destruct HenableSucc as [pdentry1 (Hs & _)]. rewrite Hs. apply getChildrenEqPDT with pdentry; trivial.
    unfold consistency in *; unfold consistency1 in *; intuition.
  - assert(HeqTriv: false <> true) by auto. specialize(HenableNotSucc HeqTriv). subst s. reflexivity.
}

assert(verticalSharing s).
{ (* BEGIN verticalSharing s *)
  intros pdparent child HparentIsPart HchildIsChild. rewrite HgetPartsEqs in *. rewrite HgetChildrenEqs in *.
  specialize(HVSs0 pdparent child HparentIsPart HchildIsChild). unfold getUsedPaddr. rewrite HgetMappedPEqs.
  rewrite HgetMappedPEqs. rewrite HgetConfigPEqs; trivial.
  apply childrenArePDT with pdparent; trivial. unfold consistency in *; unfold consistency1 in *; intuition.
  (* END verticalSharing *)
}

assert(partitionsIsolation s).
{ (* BEGIN partitionsIsolation s *)
  intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
  rewrite HgetPartsEqs in *. rewrite HgetChildrenEqs in *.
  specialize(HPIs0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
  unfold getUsedPaddr. rewrite HgetMappedPEqs. rewrite HgetMappedPEqs. assert(isPDT child1 s0).
  { apply childrenArePDT with pdparent; trivial. unfold consistency in *; unfold consistency1 in *; intuition. }
  assert(isPDT child2 s0).
  { apply childrenArePDT with pdparent; trivial. unfold consistency in *; unfold consistency1 in *; intuition. }
  rewrite HgetConfigPEqs; trivial. rewrite HgetConfigPEqs; trivial.
  (* END partitionsIsolation *)
}

assert(kernelDataIsolation s).
{ (* BEGIN kernelDataIsolation s *)
  intros part1 part2 Hpart1IsPart Hpart2IsPart. rewrite HgetPartsEqs in *.
  specialize(HKDIs0 part1 part2 Hpart1IsPart Hpart2IsPart). rewrite HgetAccMappedPEqs.
  rewrite HgetConfigPEqs; trivial.
  apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
  (* END kernelDataIsolation *)
}
auto.
Qed.