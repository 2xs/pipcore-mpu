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
Require Import Invariants getGlobalIdPDCurrentOrChild findBlockInKSWithAddr.
From Stdlib Require Import Compare_dec Bool List Logic.ProofIrrelevance.

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
      assert(Hparent: parentOfPartitionIsPartition s) by intuition. specialize(Hparent ). (*TODO HERE*)
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      (* END partitionTreeIsTree *)
    }

    assert(kernelEntriesAreValid newS).
    { (* BEGIN kernelEntriesAreValid newS *)
      assert(Hcons0: kernelEntriesAreValid s) by intuition.
      intros kernel idx HkernIsKS Hidx.
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      
      (* END kernelEntriesAreValid *)
    }

    assert(nextKernelIsValid newS).
    { (* BEGIN nextKernelIsValid newS *)
      assert(Hcons0: nextKernelIsValid s) by intuition.
      intros kernel HkernIsKS.
      
      
      
      
      
      
      
      
      
      
      
      
      
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns newS).
    { (* BEGIN noDupListOfKerns newS *)
      assert(Hcons0: noDupListOfKerns s) by intuition.
      intros partition kernList HlistOfKerns.
      
      
      
      
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax newS).
    { (* BEGIN MPUsizeIsBelowMax newS *)
      assert(Hcons0: MPUsizeIsBelowMax s) by intuition.
      intros partition MPUlist HMPU.
      
      
      
      
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart newS).
    { (* BEGIN originIsParentBlocksStart newS *)
      assert(Hcons0: originIsParentBlocksStart s) by intuition.
      intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      
      
      
      
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut newS).
    { (* BEGIN nextImpliesBlockWasCut newS *)
      assert(Hcons0: nextImpliesBlockWasCut s) by intuition.
      intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock Hsce
        HbeqNextNull Hnext HbeqPartRoot.
      
      
      
      
      (* END nextImpliesBlockWasCut *)
    }

    assert(blocksAddressesTypes newS).
    { (* BEGIN blocksAddressesTypes newS *)
      assert(Hcons0: blocksAddressesTypes s) by intuition.
      intros block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock.
      
      
      
      
      (* END blocksAddressesTypes *)
    }

    assert(notPDTIfNotPDflag newS).
    { (* BEGIN notPDTIfNotPDflag newS *)
      assert(Hcons0: notPDTIfNotPDflag s) by intuition.
      intros block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild.
      
      
      
      
      (* END notPDTIfNotPDflag *)
    }

    assert(nextKernAddrIsInSameBlock newS).
    { (* BEGIN nextKernAddrIsInSameBlock newS *)
      assert(Hcons0: nextKernAddrIsInSameBlock s) by intuition.
      intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HnextInRange HkernIsKS.
      
      
      
      
      (* END nextKernAddrIsInSameBlock *)
    }

    assert(blockBelongsToAPart newS).
    { (* BEGIN blockBelongsToAPart newS *)
      assert(Hcons0: blockBelongsToAPart s) by intuition.
      intros block HPflagBlock.
      
      
      
      
      (* END blockBelongsToAPart *)
    }

    assert(PDflagMeansNoChild newS).
    { (* BEGIN PDflagMeansNoChild newS *)
      assert(Hcons0: PDflagMeansNoChild s) by intuition.
      intros block HblockIsBE HPDflagBlock.
      
      
      
      
      (* END PDflagMeansNoChild *)
    }

    assert(nbPrepareIsNbKern newS).
    { (* BEGIN nbPrepareIsNbKern newS *)
      assert(Hcons0: nbPrepareIsNbKern s) by intuition.
      intros partition pdentry HlookupPart.
      
      
      
      
     (* END nbPrepareIsNbKern *)
    }
  }
  instantiate(1 := fun _ s =>
    exists s0 scentry1,
      s = {|
            currentPartition := currentPartition s0;
            memory :=
              add (CPaddr (block1InCurrPartAddr + scoffset))
                (SCE {| origin := origin scentry1; next := block2Next |}) (memory s0) beqAddr
          |}
    ).
    exists s. exists scentry1.
}

