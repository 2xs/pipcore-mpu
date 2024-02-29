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

Require Import Model.ADT Model.Lib Model.MAL Model.Monad.

Require Import Proof.StateLib Proof.Isolation Proof.Consistency Proof.DependentTypeLemmas Proof.InternalLemmas.

Require Import List.

Definition MapMPUPropagatedProperties
globalIdPD blockToEnableAddr
MPURegionNb
is_mapped
s0 s1
s
entry0
entry1
  :=
globalIdPD <> nullAddr
(* s0 *)
/\ partitionsIsolation s0
/\ kernelDataIsolation s0
/\ verticalSharing s0
/\ consistency s0
/\ isPDT globalIdPD s0
/\ lookup globalIdPD (memory s0) beqAddr = Some (PDT entry0)
(*/\ (blockToEnableAddr <> nullAddr ->
        exists bentry0, lookup blockToEnableAddr (memory s0) beqAddr = Some (BE bentry0)
        /\ blockToEnableAddr = idBlockToEnable)*)

(* s1 *)
/\ (s1 = s0 \/
    (exists MPURegionNb0 : nat, (*TODO properties of MPURegionNb0?*)
       s1 =
       {|
         currentPartition := currentPartition s0;
         memory :=
           add globalIdPD
             (PDT
                {|
                  structure := structure entry0;
                  firstfreeslot := firstfreeslot entry0;
                  nbfreeslots := nbfreeslots entry0;
                  nbprepare := nbprepare entry0;
                  parent := parent entry0;
                  MPU := addElementAt MPURegionNb0 nullAddr (MPU entry0) nullAddr;
                  vidtAddr := vidtAddr entry0
                |}) (memory s0) beqAddr
       |}))
/\ isPDT globalIdPD s1
/\ consistency s1
/\ lookup globalIdPD (memory s1) beqAddr = Some (PDT entry1)

(* s *)
/\ isPDT globalIdPD s
/\ consistency s
/\ getKSEntries globalIdPD s = getKSEntries globalIdPD s1
/\ (isPDT multiplexer s /\
     (forall partition : paddr,
      partition <> globalIdPD ->
      isPDT partition s1 -> getKSEntries partition s = getKSEntries partition s1) /\
     (forall partition : paddr,
      partition <> globalIdPD ->
      isPDT partition s1 -> getMappedPaddr partition s = getMappedPaddr partition s1) /\
     (forall partition : paddr,
      partition <> globalIdPD ->
      isPDT partition s1 -> getConfigPaddr partition s = getConfigPaddr partition s1) /\
     (forall partition : paddr,
      partition <> globalIdPD ->
      isPDT partition s1 -> getPartitions partition s = getPartitions partition s1) /\
     (forall partition : paddr,
      partition <> globalIdPD ->
      isPDT partition s1 -> getChildren partition s = getChildren partition s1) /\
     (forall partition : paddr,
      partition <> globalIdPD ->
      isPDT partition s1 -> getMappedBlocks partition s = getMappedBlocks partition s1) /\
     (forall partition : paddr,
      partition <> globalIdPD ->
      isPDT partition s1 ->
      getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s1) /\
     (forall partition : paddr,
      partition <> globalIdPD ->
      isPDT partition s1 ->
      getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s1))
/\ (forall partition : paddr, isPDT partition s = isPDT partition s1)
/\ (is_true is_mapped ->
     exists pdentry : PDTable,
       s =
       {|
         currentPartition := currentPartition s1;
         memory :=
           add globalIdPD
             (PDT
                {|
                  structure := structure entry1;
                  firstfreeslot := firstfreeslot entry1;
                  nbfreeslots := nbfreeslots entry1;
                  nbprepare := nbprepare entry1;
                  parent := parent entry1;
                  MPU := addElementAt MPURegionNb blockToEnableAddr (MPU entry1) nullAddr;
                  vidtAddr := vidtAddr entry1
                |}) (memory s1) beqAddr
       |} /\
       lookup globalIdPD (memory s) beqAddr = Some (PDT pdentry) /\
       pdentry =
       {|
         structure := structure entry1;
         firstfreeslot := firstfreeslot entry1;
         nbfreeslots := nbfreeslots entry1;
         nbprepare := nbprepare entry1;
         parent := parent entry1;
         MPU := addElementAt MPURegionNb blockToEnableAddr (MPU entry1) nullAddr;
         vidtAddr := vidtAddr entry1
       |} /\ pdentryNbFreeSlots globalIdPD (nbfreeslots entry1) s)
/\ (~ is_true is_mapped -> s = s1).

Lemma MapMPUVS
globalIdPD blockToEnableAddr
MPURegionNb
is_mapped
s0 s1
s
entry0
entry1 :

MapMPUPropagatedProperties
globalIdPD blockToEnableAddr
MPURegionNb
is_mapped
s0 s1
s
entry0
entry1
-> verticalSharing s.
Proof.
intro hyps. unfold MapMPUPropagatedProperties in *.
(* reconstuct hypotheses *)
destruct hyps as [HglobNotNull (HPIs0 & (HKIs0 & (HVSs0 & (Hconsts0 & (HPDTs0 & (Hlookups0 &
(Hlinks0s1 & (HPDTs1 & (Hconsts1 & (Hlookups1 & (HPDTs & (Hconsts & (HgetKSEqs & (HhelpConsts &
(HisPDTEq & (Hlinks1sIfMapped & Hlinks1sIfNotMapped))))))))))))))))].
destruct HhelpConsts as [HmultiPDT (HgetKSEq & (HgetMappedPaddrEq & (HgetConfigEq & (HgetPartitionsEq &
                          (HgetChildrenEq & (HgetMappedBlocksEq & (HgetAccMappedBlocksEq &
                                                                  HgetAccMappedPaddrEq)))))))].

(* Useful properties *)
assert(HstructIsKSs0: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HPDTIfPDFlags0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).

assert(HstructIsKSs1: StructurePointerIsKS s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HPDTIfPDFlags1: PDTIfPDFlag s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HmultiPDTs1: multiplexerIsPDT s1) by (unfold consistency in *; unfold consistency1 in *; intuition).

(* verticalSharing s *)
unfold verticalSharing in *.
intros parent child HparentPartTree HchildIsChild addr HnAddrInUsedChild.

assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s0).
{
  assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s1).
  {
    destruct (beqAddr multiplexer globalIdPD) eqn:HbeqMultiGlob.
    - (* multiplexer = globalIdPD *)
      rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqMultiGlob. rewrite HbeqMultiGlob in *.
      destruct is_mapped eqn:Hmapped.
      + (* is_mapped = true *)
        assert(Htrue: is_true true) by intuition.
        apply Hlinks1sIfMapped in Htrue.
        destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
        rewrite Hs. apply getPartitionsEqPDT with entry1; intuition.
      + (* is_mapped = false *)
        assert(Htrue: ~ is_true false) by intuition.
        apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
    - (* multiplexer <> globalIdPD *)
      rewrite <-DependentTypeLemmas.beqAddrFalse in HbeqMultiGlob.
      apply HgetPartitionsEq. assumption.
      assert(HmultiPDTEq: isPDT multiplexer s = isPDT multiplexer s1) by intuition.
      rewrite <-HmultiPDTEq. assumption.
  }
  rewrite HparentEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getPartitionsEqPDT with entry0; intuition.
}
rewrite HparentEq in *.

assert(HPartitionsEqs1s0: forall partition, getPartitions partition s1 = getPartitions partition s0).
{
  destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getPartitionsEqPDT with entry0; intuition.
}

assert(HChildrenEqs1s0: forall partition, getChildren partition s1 = getChildren partition s0).
{
  destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getChildrenEqPDT with entry0; intuition.
}

assert(HpdChildrenEq : getChildren globalIdPD s = getChildren globalIdPD s0).
{
  assert(HpdChildrenEq : getChildren globalIdPD s = getChildren globalIdPD s1).
  {
    destruct is_mapped eqn:Hmapped.
    - (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      rewrite Hs. apply getChildrenEqPDT with entry1; intuition.
    - (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  }
  rewrite HpdChildrenEq. apply HChildrenEqs1s0.
}

assert(HusedPaddrGlobEq: getUsedPaddr globalIdPD s = getUsedPaddr globalIdPD s0).
{
  assert(HusedPaddrGlobEq: getUsedPaddr globalIdPD s = getUsedPaddr globalIdPD s1).
  {
    unfold getUsedPaddr.
    destruct is_mapped eqn:Hmapped.
    - (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      assert(HconfigEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s1)
                    by (rewrite Hs; apply getConfigPaddrEqPDT with entry1; intuition).
      assert(HmappedEq: getMappedPaddr globalIdPD s = getMappedPaddr globalIdPD s1)
                    by (rewrite Hs; apply getMappedPaddrEqPDT with entry1; intuition).
      rewrite HconfigEq. rewrite HmappedEq. reflexivity.
    - (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  }
  rewrite HusedPaddrGlobEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
  assert(HconfigEq: getConfigPaddr globalIdPD s1 = getConfigPaddr globalIdPD s0)
                by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
  assert(HmappedEq: getMappedPaddr globalIdPD s1 = getMappedPaddr globalIdPD s0)
                by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
  rewrite HconfigEq. rewrite HmappedEq. reflexivity.
}

(* verticalSharing s *)

assert(HPDTParents1: isPDT parent s1).
{
  eapply partitionsArePDT; try(assumption). specialize(HPartitionsEqs1s0 multiplexer).
  rewrite HPartitionsEqs1s0. assumption.
}
destruct (beqAddr child globalIdPD) eqn:HbeqChildGlob.
- (* child = globalIdPD *)
  rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqChildGlob. rewrite HbeqChildGlob in *.
  assert(HparentGlobNotEq : parent <> globalIdPD).
  {
    assert(noDupPartitionTree s0) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
    eapply childparentNotEq with s0; try(assumption).
	  assert(HchildrenParentEq : getChildren parent s = getChildren parent s0).
	  {
      destruct (beqAddr parent globalIdPD) eqn:HbeqParentGlob ; try(exfalso ; congruence).
		  - (* parent = globalIdPD *)
			  (* even in the false case, the children did not change for any partition *)
			  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqParentGlob.
			  rewrite HbeqParentGlob in *. assumption.
		  - (* parent <> globalIdPDChild *)
			  rewrite <- beqAddrFalse in *.
        assert(HgetChildrenEqParent: getChildren parent s = getChildren parent s1)
            by (apply HgetChildrenEq; try(assumption)).
			  rewrite HgetChildrenEqParent. apply HChildrenEqs1s0.
	  }
	  rewrite HchildrenParentEq in *. assumption.
  }
	assert(HchildrenParentEq : getChildren parent s = getChildren parent s0).
	{
    assert(H: getChildren parent s1 = getChildren parent s0) by (apply HChildrenEqs1s0).
    rewrite <-H.
    apply HgetChildrenEq; try(assumption).
  }
	rewrite HchildrenParentEq in *.
  assert(HmappedPaddrParentEq: getMappedPaddr parent s = getMappedPaddr parent s0).
  {
    assert(HmappedPaddrParentEq: getMappedPaddr parent s = getMappedPaddr parent s1).
    { apply HgetMappedPaddrEq; assumption. }
    rewrite HmappedPaddrParentEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
    destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
    apply getMappedPaddrEqPDT with entry0; intuition.
  }
  rewrite HmappedPaddrParentEq.
  rewrite HusedPaddrGlobEq in *.
  specialize(HVSs0 parent globalIdPD HparentPartTree HchildIsChild addr HnAddrInUsedChild).
  assumption.
- (* child <> globalIdPD *)
  rewrite <-DependentTypeLemmas.beqAddrFalse in HbeqChildGlob.
  destruct (beqAddr parent globalIdPD) eqn:HbeqParentGlob.
  + (* parent = globalIdPD *)
    rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqParentGlob. rewrite HbeqParentGlob in *.
	  rewrite HpdChildrenEq in *.
    assert(HmappedPaddrGlobEq: getMappedPaddr globalIdPD s = getMappedPaddr globalIdPD s0).
    {
      assert(HmappedPaddrGlobEq: getMappedPaddr globalIdPD s = getMappedPaddr globalIdPD s1).
      {
        destruct is_mapped eqn:Hmapped.
        - (* is_mapped = true *)
          assert(Htrue: is_true true) by intuition.
          apply Hlinks1sIfMapped in Htrue.
          destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
          rewrite Hs; apply getMappedPaddrEqPDT with entry1; intuition.
        - (* is_mapped = false *)
          assert(Htrue: ~ is_true false) by intuition.
          apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
      }
      rewrite HmappedPaddrGlobEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
      apply getMappedPaddrEqPDT with entry0; intuition.
    }
    rewrite HmappedPaddrGlobEq in *.
    assert(HPDTChilds1: isPDT child s1).
    {
      apply childrenArePDT with globalIdPD; try(assumption).
      assert(HChildrenEq: getChildren globalIdPD s1 = getChildren globalIdPD s0) by apply HChildrenEqs1s0.
      rewrite HChildrenEq. assumption.
    }
    assert(HPDTChilds0: isPDT child s0) by (apply childrenArePDT with globalIdPD; try(assumption)).
    assert(HusedPaddrChildEq: getUsedPaddr child s = getUsedPaddr child s0).
    {
      assert(HusedPaddrChildEq: getUsedPaddr child s = getUsedPaddr child s1).
      {
        unfold getUsedPaddr. destruct is_mapped eqn:Hmapped.
        - (* is_mapped = true *)
          assert(Htrue: is_true true) by intuition.
          apply Hlinks1sIfMapped in Htrue.
          destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
          assert(HconfigEq: getConfigPaddr child s = getConfigPaddr child s1)
                        by (apply HgetConfigEq; intuition).
          assert(HmappedEq: getMappedPaddr child s = getMappedPaddr child s1)
                        by (apply HgetMappedPaddrEq; intuition).
          rewrite HconfigEq. rewrite HmappedEq. reflexivity.
        - (* is_mapped = false *)
          assert(Htrue: ~ is_true false) by intuition.
          apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
      }
      rewrite HusedPaddrChildEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
      assert(HconfigEq: getConfigPaddr child s1 = getConfigPaddr child s0)
                    by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
      assert(HmappedEq: getMappedPaddr child s1 = getMappedPaddr child s0)
                    by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
      rewrite HconfigEq. rewrite HmappedEq. reflexivity.
    }
    rewrite HusedPaddrChildEq in *.
    specialize(HVSs0 globalIdPD child HparentPartTree HchildIsChild addr HnAddrInUsedChild). assumption.
  + (* parent <> globalIdPD *)
    rewrite <-DependentTypeLemmas.beqAddrFalse in HbeqParentGlob.
    assert(HChildrenEq: getChildren parent s = getChildren parent s0).
    {
      assert(HChildrenEq: getChildren parent s = getChildren parent s1) by (apply HgetChildrenEq; intuition).
      rewrite HChildrenEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
    }
	  rewrite HChildrenEq in *.
    assert(HmappedPaddrParentEq: getMappedPaddr parent s = getMappedPaddr parent s0).
    {
      assert(HmappedPaddrParentEq: getMappedPaddr parent s = getMappedPaddr parent s1)
                by (apply HgetMappedPaddrEq; intuition).
      rewrite HmappedPaddrParentEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
      apply getMappedPaddrEqPDT with entry0; intuition.
    }
    rewrite HmappedPaddrParentEq in *.
    assert(HPDTChilds1: isPDT child s1).
    {
      apply childrenArePDT with parent; try(assumption).
      assert(HChildrenParentEq: getChildren parent s1 = getChildren parent s0) by apply HChildrenEqs1s0.
      rewrite HChildrenParentEq. assumption.
    }
    assert(HPDTChilds0: isPDT child s0) by (apply childrenArePDT with parent; try(assumption)).
    assert(HusedPaddrChildEq: getUsedPaddr child s = getUsedPaddr child s0).
    {
      assert(HusedPaddrChildEq: getUsedPaddr child s = getUsedPaddr child s1).
      {
        unfold getUsedPaddr. destruct is_mapped eqn:Hmapped.
        - (* is_mapped = true *)
          assert(Htrue: is_true true) by intuition.
          apply Hlinks1sIfMapped in Htrue.
          destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
          assert(HconfigEq: getConfigPaddr child s = getConfigPaddr child s1)
                        by (apply HgetConfigEq; intuition).
          assert(HmappedEq: getMappedPaddr child s = getMappedPaddr child s1)
                        by (apply HgetMappedPaddrEq; intuition).
          rewrite HconfigEq. rewrite HmappedEq. reflexivity.
        - (* is_mapped = false *)
          assert(Htrue: ~ is_true false) by intuition.
          apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
      }
      rewrite HusedPaddrChildEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
      assert(HconfigEq: getConfigPaddr child s1 = getConfigPaddr child s0)
                    by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
      assert(HmappedEq: getMappedPaddr child s1 = getMappedPaddr child s0)
                    by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
      rewrite HconfigEq. rewrite HmappedEq. reflexivity.
    }
    rewrite HusedPaddrChildEq in *.
    specialize(HVSs0 parent child HparentPartTree HchildIsChild addr HnAddrInUsedChild). assumption.
Qed.

Lemma MapMPUKI
globalIdPD blockToEnableAddr
MPURegionNb
is_mapped
s0 s1
s
entry0
entry1 :

MapMPUPropagatedProperties
globalIdPD blockToEnableAddr
MPURegionNb
is_mapped
s0 s1
s
entry0
entry1
-> kernelDataIsolation s.
Proof.
intro hyps. unfold MapMPUPropagatedProperties in *.
(* reconstuct hypotheses *)
destruct hyps as [HglobNotNull (HPIs0 & (HKIs0 & (HVSs0 & (Hconsts0 & (HPDTs0 & (Hlookups0 &
(Hlinks0s1 & (HPDTs1 & (Hconsts1 & (Hlookups1 & (HPDTs & (Hconsts & (HgetKSEqs & (HhelpConsts &
(HisPDTEq & (Hlinks1sIfMapped & Hlinks1sIfNotMapped))))))))))))))))].
destruct HhelpConsts as [HmultiPDT (HgetKSEq & (HgetMappedPaddrEq & (HgetConfigEq & (HgetPartitionsEq &
                          (HgetChildrenEq & (HgetMappedBlocksEq & (HgetAccMappedBlocksEq &
                                                                  HgetAccMappedPaddrEq)))))))].

(* Useful properties *)
assert(HstructIsKSs0: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HPDTIfPDFlags0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HmultiPDTs0: multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).

assert(HstructIsKSs1: StructurePointerIsKS s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HPDTIfPDFlags1: PDTIfPDFlag s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HmultiPDTs1: multiplexerIsPDT s1) by (unfold consistency in *; unfold consistency1 in *; intuition).

(* kernelDataIsolation s *)
unfold kernelDataIsolation in *.
intros part1 part2 Hpart1PartTree Hpart2PartTree.
assert(HparentEqs1 : getPartitions multiplexer s = getPartitions multiplexer s1).
{
  destruct (beqAddr multiplexer globalIdPD) eqn:HbeqMultiGlob.
  - (* multiplexer = globalIdPD *)
    rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqMultiGlob. rewrite HbeqMultiGlob in *.
    destruct is_mapped eqn:Hmapped.
    + (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      rewrite Hs. apply getPartitionsEqPDT with entry1; intuition.
    + (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  - (* multiplexer <> globalIdPD *)
    rewrite <-DependentTypeLemmas.beqAddrFalse in HbeqMultiGlob.
    apply HgetPartitionsEq. assumption.
    assert(HmultiPDTEq: isPDT multiplexer s = isPDT multiplexer s1) by intuition.
    rewrite <-HmultiPDTEq. assumption.
}
assert(HaccessPaddrEq: getAccessibleMappedPaddr globalIdPD s = getAccessibleMappedPaddr globalIdPD s0).
{
  assert(HaccessPaddrEq: getAccessibleMappedPaddr globalIdPD s = getAccessibleMappedPaddr globalIdPD s1).
  {
    destruct is_mapped eqn:Hmapped.
    - (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      assert(HconfigEq: getAccessibleMappedPaddr globalIdPD s = getAccessibleMappedPaddr globalIdPD s1)
                by (rewrite Hs; apply getAccessibleMappedPaddrEqPDT with entry1; intuition).
      rewrite HconfigEq. reflexivity.
    - (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  }
  rewrite HaccessPaddrEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getAccessibleMappedPaddrEqPDT with entry0; intuition.
}
assert(HconfigPaddrEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s0).
{
  assert(HconfigPaddrEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s1).
  {
    destruct is_mapped eqn:Hmapped.
    - (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      assert(HconfigEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s1)
                by (rewrite Hs; apply getConfigPaddrEqPDT with entry1; intuition).
      rewrite HconfigEq. reflexivity.
    - (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  }
  rewrite HconfigPaddrEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getConfigPaddrEqPDT with entry0; intuition.
}
assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s0).
{
  rewrite HparentEqs1. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getPartitionsEqPDT with entry0; intuition.
}
rewrite HparentEq in *.

destruct (beqAddr part1 globalIdPD) eqn:HbeqPart1Glob.
- (* part1 = globalIdPD *)
  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqPart1Glob.
	rewrite HbeqPart1Glob in *.
	destruct (beqAddr part2 globalIdPD) eqn:HbeqPart2Glob.
  + (* part2 = globalIdPD *)
    rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqPart2Glob.
	  rewrite HbeqPart2Glob in *.
		specialize (HKIs0 globalIdPD globalIdPD Hpart1PartTree Hpart2PartTree).
    rewrite HconfigPaddrEq.
    rewrite HaccessPaddrEq. assumption.
  + (* part2 <> globalIdPD *)
    rewrite <- DependentTypeLemmas.beqAddrFalse in HbeqPart2Glob.
		specialize (HKIs0 globalIdPD part2 Hpart1PartTree Hpart2PartTree).
		assert(HPDTpart2s0 : isPDT part2 s0) by (eapply partitionsArePDT ; intuition).
		assert(HPDTpart2s1 : isPDT part2 s1)
            by (eapply partitionsArePDT; try(assumption); rewrite <-HparentEqs1; assumption).
		assert(HconfigPart2Eq: getConfigPaddr part2 s = getConfigPaddr part2 s0).
    {
      assert(HconfigPart2Eq: getConfigPaddr part2 s = getConfigPaddr part2 s1) by (apply HgetConfigEq; intuition).
      rewrite HconfigPart2Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
      apply getConfigPaddrEqPDT with entry0; intuition.
    }
    rewrite HconfigPart2Eq. rewrite HaccessPaddrEq. assumption.
- (* part1 <> globalIdPD *)
  rewrite <- DependentTypeLemmas.beqAddrFalse in HbeqPart1Glob.
  destruct (beqAddr part2 globalIdPD) eqn:HbeqPart2Glob.
  + (* part2 = globalIdPD *)
    rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqPart2Glob.
	  rewrite HbeqPart2Glob in *.
		specialize (HKIs0 part1 globalIdPD Hpart1PartTree Hpart2PartTree).
		assert(HPDTpart1s0 : isPDT part1 s0) by (eapply partitionsArePDT ; intuition).
		assert(HPDTpart1s1 : isPDT part1 s1)
            by (eapply partitionsArePDT; try(assumption); rewrite <-HparentEqs1; assumption).
    rewrite HconfigPaddrEq.
    assert(HaccessPaddrPart1Eq: getAccessibleMappedPaddr part1 s = getAccessibleMappedPaddr part1 s0).
    {
      assert(HaccessPart1Eq: getAccessibleMappedPaddr part1 s = getAccessibleMappedPaddr part1 s1)
                        by (apply HgetAccMappedPaddrEq; intuition).
      rewrite HaccessPart1Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
      apply getAccessibleMappedPaddrEqPDT with entry0; intuition.
    }
    rewrite HaccessPaddrPart1Eq. assumption.
  + (* part2 <> globalIdPD *)
    rewrite <- DependentTypeLemmas.beqAddrFalse in HbeqPart2Glob.
		specialize (HKIs0 part1 part2 Hpart1PartTree Hpart2PartTree).
		assert(HPDTpart1s0 : isPDT part1 s0) by (eapply partitionsArePDT ; intuition).
		assert(HPDTpart1s1 : isPDT part1 s1)
            by (eapply partitionsArePDT; try(assumption); rewrite <-HparentEqs1; assumption).
		assert(HPDTpart2s0 : isPDT part2 s0) by (eapply partitionsArePDT ; intuition).
		assert(HPDTpart2s1 : isPDT part2 s1)
            by (eapply partitionsArePDT; try(assumption); rewrite <-HparentEqs1; assumption).
    (* DUP *)
    assert(HaccessPaddrPart1Eq: getAccessibleMappedPaddr part1 s = getAccessibleMappedPaddr part1 s0).
    {
      assert(HaccessPart1Eq: getAccessibleMappedPaddr part1 s = getAccessibleMappedPaddr part1 s1)
                        by (apply HgetAccMappedPaddrEq; intuition).
      rewrite HaccessPart1Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
      apply getAccessibleMappedPaddrEqPDT with entry0; intuition.
    }
    rewrite HaccessPaddrPart1Eq.
		assert(HconfigPart2Eq: getConfigPaddr part2 s = getConfigPaddr part2 s0).
    {
      assert(HconfigPart2Eq: getConfigPaddr part2 s = getConfigPaddr part2 s1) by (apply HgetConfigEq; intuition).
      rewrite HconfigPart2Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
      apply getConfigPaddrEqPDT with entry0; intuition.
    }
    rewrite HconfigPart2Eq. assumption.
Qed.

Lemma MapMPUHI
globalIdPD blockToEnableAddr
MPURegionNb
is_mapped
s0 s1
s
entry0
entry1 :

MapMPUPropagatedProperties
globalIdPD blockToEnableAddr
MPURegionNb
is_mapped
s0 s1
s
entry0
entry1
-> partitionsIsolation s.
Proof.
intro hyps. unfold MapMPUPropagatedProperties in *.
(* reconstuct hypotheses *)
destruct hyps as [HglobNotNull (HPIs0 & (HKIs0 & (HVSs0 & (Hconsts0 & (HPDTs0 & (Hlookups0 &
(Hlinks0s1 & (HPDTs1 & (Hconsts1 & (Hlookups1 & (HPDTs & (Hconsts & (HgetKSEqs & (HhelpConsts &
(HisPDTEq & (Hlinks1sIfMapped & Hlinks1sIfNotMapped))))))))))))))))].
destruct HhelpConsts as [HmultiPDT (HgetKSEq & (HgetMappedPaddrEq & (HgetConfigEq & (HgetPartitionsEq &
                          (HgetChildrenEq & (HgetMappedBlocksEq & (HgetAccMappedBlocksEq &
                                                                  HgetAccMappedPaddrEq)))))))].

(* Useful properties *)
assert(HstructIsKSs0: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HPDTIfPDFlags0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
(*assert(HmultiPDTs0: multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).*)

assert(HstructIsKSs1: StructurePointerIsKS s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HPDTIfPDFlags1: PDTIfPDFlag s1) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HmultiPDTs1: multiplexerIsPDT s1) by (unfold consistency in *; unfold consistency1 in *; intuition).

assert(HPDTIfPDFlags: PDTIfPDFlag s) by (unfold consistency in *; unfold consistency1 in *; intuition).
assert(HNoDupPartTree : noDupPartitionTree s) by (unfold consistency in * ; unfold consistency1 in * ; intuition).

(* partitionsIsolation s *)
unfold partitionsIsolation in *.
intros parent child1 child2 HparentPartTree Hchild1IsChild Hchild2IsChild Hchild1child2NotEq.

assert(HPDTparents : isPDT parent s) by (eapply partitionsArePDT; intuition).
assert(HPDTchild1s : isPDT child1 s) by (eapply childrenArePDT; try(assumption); apply Hchild1IsChild).
assert(HPDTchild2s : isPDT child2 s) by (eapply childrenArePDT; try(assumption); apply Hchild2IsChild).
assert(HparentEqs1 : getPartitions multiplexer s = getPartitions multiplexer s1).
{
  destruct (beqAddr multiplexer globalIdPD) eqn:HbeqMultiGlob.
  - (* multiplexer = globalIdPD *)
    rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqMultiGlob. rewrite HbeqMultiGlob in *.
    destruct is_mapped eqn:Hmapped.
    + (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      rewrite Hs. apply getPartitionsEqPDT with entry1; intuition.
    + (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  - (* multiplexer <> globalIdPD *)
    rewrite <-DependentTypeLemmas.beqAddrFalse in HbeqMultiGlob.
    apply HgetPartitionsEq. assumption.
    assert(HmultiPDTEq: isPDT multiplexer s = isPDT multiplexer s1) by intuition.
    rewrite <-HmultiPDTEq. assumption.
}
assert(HparentEq : getPartitions multiplexer s = getPartitions multiplexer s0).
{
  rewrite HparentEqs1. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getPartitionsEqPDT with entry0; intuition.
}
rewrite HparentEq in *.
assert(HChildrenEqs1s0: forall partition, getChildren partition s1 = getChildren partition s0).
{
  destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getChildrenEqPDT with entry0; intuition.
}
assert(HpdChildrenEq : getChildren globalIdPD s = getChildren globalIdPD s0).
{
  assert(HpdChildrenEq : getChildren globalIdPD s = getChildren globalIdPD s1).
  {
    destruct is_mapped eqn:Hmapped.
    - (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      rewrite Hs. apply getChildrenEqPDT with entry1; intuition.
    - (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  }
  rewrite HpdChildrenEq. apply HChildrenEqs1s0.
}
assert(HconfigPaddrEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s0).
{
  assert(HconfigPaddrEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s1).
  {
    destruct is_mapped eqn:Hmapped.
    - (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      assert(HconfigEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s1)
                by (rewrite Hs; apply getConfigPaddrEqPDT with entry1; intuition).
      rewrite HconfigEq. reflexivity.
    - (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  }
  rewrite HconfigPaddrEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. rewrite Hs1.
  apply getConfigPaddrEqPDT with entry0; intuition.
}
assert(HusedPaddrGlobEq: getUsedPaddr globalIdPD s = getUsedPaddr globalIdPD s0).
{
  assert(HusedPaddrGlobEq: getUsedPaddr globalIdPD s = getUsedPaddr globalIdPD s1).
  {
    unfold getUsedPaddr.
    destruct is_mapped eqn:Hmapped.
    - (* is_mapped = true *)
      assert(Htrue: is_true true) by intuition.
      apply Hlinks1sIfMapped in Htrue.
      destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
      assert(HconfigEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s1)
                    by (rewrite Hs; apply getConfigPaddrEqPDT with entry1; intuition).
      assert(HmappedEq: getMappedPaddr globalIdPD s = getMappedPaddr globalIdPD s1)
                    by (rewrite Hs; apply getMappedPaddrEqPDT with entry1; intuition).
      rewrite HconfigEq. rewrite HmappedEq. reflexivity.
    - (* is_mapped = false *)
      assert(Htrue: ~ is_true false) by intuition.
      apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
  }
  rewrite HusedPaddrGlobEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
  assert(HconfigEq: getConfigPaddr globalIdPD s1 = getConfigPaddr globalIdPD s0)
                by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
  assert(HmappedEq: getMappedPaddr globalIdPD s1 = getMappedPaddr globalIdPD s0)
                by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
  rewrite HconfigEq. rewrite HmappedEq. reflexivity.
}

destruct (beqAddr child1 globalIdPD) eqn:HbeqChild1Glob.
- (* child1 = globalIdPD *)
  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqChild1Glob. rewrite HbeqChild1Glob in *.
		assert(HPDTpart1s1 : isPDT parent s1)
            by (eapply partitionsArePDT; try(assumption); rewrite <-HparentEqs1; assumption).
	assert(HglobalChildNotEq : parent <> globalIdPD).
	{ eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }
  assert(HChildrenEq: getChildren parent s = getChildren parent s0).
  {
    assert(HChildrenEq: getChildren parent s = getChildren parent s1) by (apply HgetChildrenEq; intuition).
    rewrite HChildrenEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
  }
  rewrite HChildrenEq in *.
  assert(HPDTChilds1: isPDT child2 s1).
  {
    apply childrenArePDT with parent; try(assumption).
    assert(HChildrenParentEq: getChildren parent s1 = getChildren parent s0) by apply HChildrenEqs1s0.
    rewrite HChildrenParentEq. assumption.
  }
  assert(HPDTChilds0: isPDT child2 s0) by (apply childrenArePDT with parent; try(assumption)).

  specialize(HPIs0 parent globalIdPD child2 HparentPartTree Hchild1IsChild Hchild2IsChild Hchild1child2NotEq).
  rewrite HusedPaddrGlobEq.
  assert(HusedPaddrChild2Eq: getUsedPaddr child2 s = getUsedPaddr child2 s0).
  {
    assert(HusedPaddrChild2Eq: getUsedPaddr child2 s = getUsedPaddr child2 s1).
    {
      unfold getUsedPaddr. destruct is_mapped eqn:Hmapped.
      - (* is_mapped = true *)
        assert(Htrue: is_true true) by intuition.
        apply Hlinks1sIfMapped in Htrue.
        destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
        assert(HconfigEq: getConfigPaddr child2 s = getConfigPaddr child2 s1)
                      by (apply HgetConfigEq; intuition).
        assert(HmappedEq: getMappedPaddr child2 s = getMappedPaddr child2 s1)
                      by (apply HgetMappedPaddrEq; intuition).
        rewrite HconfigEq. rewrite HmappedEq. reflexivity.
      - (* is_mapped = false *)
        assert(Htrue: ~ is_true false) by intuition.
        apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
    }
    rewrite HusedPaddrChild2Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
    destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
    assert(HconfigEq: getConfigPaddr child2 s1 = getConfigPaddr child2 s0)
                  by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
    assert(HmappedEq: getMappedPaddr child2 s1 = getMappedPaddr child2 s0)
                  by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
    rewrite HconfigEq. rewrite HmappedEq. reflexivity.
  }
  rewrite HusedPaddrChild2Eq. assumption.
- (* child1 <> globalIdPD *)
  rewrite <- DependentTypeLemmas.beqAddrFalse in HbeqChild1Glob.
  destruct (beqAddr child2 globalIdPD) eqn:HbeqChild2Glob.
  + (* child2 = globalIdPD *)
    rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqChild2Glob. rewrite HbeqChild2Glob in *.
	  assert(HPDTpart1s1 : isPDT parent s1)
            by (eapply partitionsArePDT; try(assumption); rewrite <-HparentEqs1; assumption).
	  assert(HglobalChildNotEq : parent <> globalIdPD).
	  { eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }
    assert(HChildrenEq: getChildren parent s = getChildren parent s0).
    {
      assert(HChildrenEq: getChildren parent s = getChildren parent s1) by (apply HgetChildrenEq; intuition).
      rewrite HChildrenEq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
    }
    rewrite HChildrenEq in *.
    assert(HPDTChilds1: isPDT child1 s1).
    {
      apply childrenArePDT with parent; try(assumption).
      assert(HChildrenParentEq: getChildren parent s1 = getChildren parent s0) by apply HChildrenEqs1s0.
      rewrite HChildrenParentEq. assumption.
    }
    assert(HPDTChilds0: isPDT child1 s0) by (apply childrenArePDT with parent; try(assumption)).

    specialize(HPIs0 parent child1 globalIdPD HparentPartTree Hchild1IsChild Hchild2IsChild Hchild1child2NotEq).
    rewrite HusedPaddrGlobEq.
    assert(HusedPaddrChild1Eq: getUsedPaddr child1 s = getUsedPaddr child1 s0).
    {
      assert(HusedPaddrChild1Eq: getUsedPaddr child1 s = getUsedPaddr child1 s1).
      {
        unfold getUsedPaddr. destruct is_mapped eqn:Hmapped.
        - (* is_mapped = true *)
          assert(Htrue: is_true true) by intuition.
          apply Hlinks1sIfMapped in Htrue.
          destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
          assert(HconfigEq: getConfigPaddr child1 s = getConfigPaddr child1 s1)
                        by (apply HgetConfigEq; intuition).
          assert(HmappedEq: getMappedPaddr child1 s = getMappedPaddr child1 s1)
                        by (apply HgetMappedPaddrEq; intuition).
          rewrite HconfigEq. rewrite HmappedEq. reflexivity.
        - (* is_mapped = false *)
          assert(Htrue: ~ is_true false) by intuition.
          apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
      }
      rewrite HusedPaddrChild1Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
      destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
      assert(HconfigEq: getConfigPaddr child1 s1 = getConfigPaddr child1 s0)
                    by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
      assert(HmappedEq: getMappedPaddr child1 s1 = getMappedPaddr child1 s0)
                    by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
      rewrite HconfigEq. rewrite HmappedEq. reflexivity.
    }
    rewrite HusedPaddrChild1Eq. assumption.
  + (* child2 <> globalIdPD *)
    rewrite <- DependentTypeLemmas.beqAddrFalse in HbeqChild2Glob.
		assert(HglobalChildNotEq1 : parent <> child1).
		{ eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }
		assert(HglobalChildNotEq2 : parent <> child2).
		{ eapply childparentNotEq with s ; try (rewrite HparentEq in *) ; intuition. }
    destruct (beqAddr parent globalIdPD) eqn:HbeqParentGlob.
    * (* parent = globalIdPD *)
      rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqParentGlob. rewrite HbeqParentGlob in *.
      rewrite HpdChildrenEq in *.
      assert(HPDTChilds1: isPDT child1 s1).
      {
        apply childrenArePDT with globalIdPD; try(assumption).
        assert(HChildrenParentEq: getChildren globalIdPD s1 = getChildren globalIdPD s0) by apply HChildrenEqs1s0.
        assert(H: getChildren globalIdPD s1 = getChildren globalIdPD s0) by (apply HChildrenEqs1s0).
        rewrite H. assumption.
      }
      assert(HPDTChilds0: isPDT child1 s0) by (apply childrenArePDT with globalIdPD; try(assumption)).
      assert(HPDTChild2s1: isPDT child2 s1).
      {
        apply childrenArePDT with globalIdPD; try(assumption).
        assert(HChildrenParentEq: getChildren globalIdPD s1 = getChildren globalIdPD s0) by apply HChildrenEqs1s0.
        assert(H: getChildren globalIdPD s1 = getChildren globalIdPD s0) by (apply HChildrenEqs1s0).
        rewrite H. assumption.
      }
      assert(HPDTChild2s0: isPDT child2 s0) by (apply childrenArePDT with globalIdPD; try(assumption)).

			specialize (HPIs0 globalIdPD child1 child2 HparentPartTree Hchild1IsChild Hchild2IsChild
									Hchild1child2NotEq).
      assert(HusedPaddrChild1Eq: getUsedPaddr child1 s = getUsedPaddr child1 s0).
      {
        assert(HusedPaddrChild1Eq: getUsedPaddr child1 s = getUsedPaddr child1 s1).
        {
          unfold getUsedPaddr. destruct is_mapped eqn:Hmapped.
          - (* is_mapped = true *)
            assert(Htrue: is_true true) by intuition.
            apply Hlinks1sIfMapped in Htrue.
            destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
            assert(HconfigEq: getConfigPaddr child1 s = getConfigPaddr child1 s1)
                          by (apply HgetConfigEq; intuition).
            assert(HmappedEq: getMappedPaddr child1 s = getMappedPaddr child1 s1)
                          by (apply HgetMappedPaddrEq; intuition).
            rewrite HconfigEq. rewrite HmappedEq. reflexivity.
          - (* is_mapped = false *)
            assert(Htrue: ~ is_true false) by intuition.
            apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
        }
        rewrite HusedPaddrChild1Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
        destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
        assert(HconfigEq: getConfigPaddr child1 s1 = getConfigPaddr child1 s0)
                      by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
        assert(HmappedEq: getMappedPaddr child1 s1 = getMappedPaddr child1 s0)
                      by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
        rewrite HconfigEq. rewrite HmappedEq. reflexivity.
      }
      rewrite HusedPaddrChild1Eq.
      assert(HusedPaddrChild2Eq: getUsedPaddr child2 s = getUsedPaddr child2 s0).
      {
        assert(HusedPaddrChild2Eq: getUsedPaddr child2 s = getUsedPaddr child2 s1).
        {
          unfold getUsedPaddr. destruct is_mapped eqn:Hmapped.
          - (* is_mapped = true *)
            assert(Htrue: is_true true) by intuition.
            apply Hlinks1sIfMapped in Htrue.
            destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
            assert(HconfigEq: getConfigPaddr child2 s = getConfigPaddr child2 s1)
                          by (apply HgetConfigEq; intuition).
            assert(HmappedEq: getMappedPaddr child2 s = getMappedPaddr child2 s1)
                          by (apply HgetMappedPaddrEq; intuition).
            rewrite HconfigEq. rewrite HmappedEq. reflexivity.
          - (* is_mapped = false *)
            assert(Htrue: ~ is_true false) by intuition.
            apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
        }
        rewrite HusedPaddrChild2Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
        destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
        assert(HconfigEq: getConfigPaddr child2 s1 = getConfigPaddr child2 s0)
                      by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
        assert(HmappedEq: getMappedPaddr child2 s1 = getMappedPaddr child2 s0)
                      by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
        rewrite HconfigEq. rewrite HmappedEq. reflexivity.
      }
      rewrite HusedPaddrChild2Eq. assumption.
    * (* parent <> globalIdPD *)
      rewrite <- DependentTypeLemmas.beqAddrFalse in HbeqParentGlob.
		  assert(HPDTpart1s1 : isPDT parent s1)
              by (eapply partitionsArePDT; try(assumption); rewrite <-HparentEqs1; assumption).
      assert(HChildrenParentEq: getChildren parent s = getChildren parent s0).
      {
        assert(HChildrenParentEq: getChildren parent s = getChildren parent s1)
                        by (apply HgetChildrenEq; intuition).
        rewrite HChildrenParentEq. apply HChildrenEqs1s0.
      }
      rewrite HChildrenParentEq in *.
      assert(HPDTChilds1: isPDT child1 s1).
      {
        apply childrenArePDT with parent; try(assumption).
        assert(H: getChildren parent s1 = getChildren parent s0) by (apply HChildrenEqs1s0).
        rewrite H. assumption.
      }
      assert(HPDTChilds0: isPDT child1 s0) by (apply childrenArePDT with parent; try(assumption)).
      assert(HPDTChild2s1: isPDT child2 s1).
      {
        apply childrenArePDT with parent; try(assumption).
        assert(H: getChildren parent s1 = getChildren parent s0) by (apply HChildrenEqs1s0).
        rewrite H. assumption.
      }
      assert(HPDTChild2s0: isPDT child2 s0) by (apply childrenArePDT with parent; try(assumption)).

			specialize (HPIs0 parent child1 child2 HparentPartTree Hchild1IsChild Hchild2IsChild
									Hchild1child2NotEq).
      assert(HusedPaddrChild1Eq: getUsedPaddr child1 s = getUsedPaddr child1 s0).
      {
        assert(HusedPaddrChild1Eq: getUsedPaddr child1 s = getUsedPaddr child1 s1).
        {
          unfold getUsedPaddr. destruct is_mapped eqn:Hmapped.
          - (* is_mapped = true *)
            assert(Htrue: is_true true) by intuition.
            apply Hlinks1sIfMapped in Htrue.
            destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
            assert(HconfigEq: getConfigPaddr child1 s = getConfigPaddr child1 s1)
                          by (apply HgetConfigEq; intuition).
            assert(HmappedEq: getMappedPaddr child1 s = getMappedPaddr child1 s1)
                          by (apply HgetMappedPaddrEq; intuition).
            rewrite HconfigEq. rewrite HmappedEq. reflexivity.
          - (* is_mapped = false *)
            assert(Htrue: ~ is_true false) by intuition.
            apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
        }
        rewrite HusedPaddrChild1Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
        destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
        assert(HconfigEq: getConfigPaddr child1 s1 = getConfigPaddr child1 s0)
                      by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
        assert(HmappedEq: getMappedPaddr child1 s1 = getMappedPaddr child1 s0)
                      by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
        rewrite HconfigEq. rewrite HmappedEq. reflexivity.
      }
      rewrite HusedPaddrChild1Eq.
      assert(HusedPaddrChild2Eq: getUsedPaddr child2 s = getUsedPaddr child2 s0).
      {
        assert(HusedPaddrChild2Eq: getUsedPaddr child2 s = getUsedPaddr child2 s1).
        {
          unfold getUsedPaddr. destruct is_mapped eqn:Hmapped.
          - (* is_mapped = true *)
            assert(Htrue: is_true true) by intuition.
            apply Hlinks1sIfMapped in Htrue.
            destruct Htrue as [pdentry (Hs & (Hlookups & (Hpdentry & HnbFreeSlots)))].
            assert(HconfigEq: getConfigPaddr child2 s = getConfigPaddr child2 s1)
                          by (apply HgetConfigEq; intuition).
            assert(HmappedEq: getMappedPaddr child2 s = getMappedPaddr child2 s1)
                          by (apply HgetMappedPaddrEq; intuition).
            rewrite HconfigEq. rewrite HmappedEq. reflexivity.
          - (* is_mapped = false *)
            assert(Htrue: ~ is_true false) by intuition.
            apply Hlinks1sIfNotMapped in Htrue. subst s. reflexivity.
        }
        rewrite HusedPaddrChild2Eq. destruct Hlinks0s1 as [Heqs0s1 | Hlinks0s1]; try(subst; intuition).
        destruct Hlinks0s1 as [MPURegionNb0 Hs1]. unfold getUsedPaddr.
        assert(HconfigEq: getConfigPaddr child2 s1 = getConfigPaddr child2 s0)
                      by (rewrite Hs1; apply getConfigPaddrEqPDT with entry0; intuition).
        assert(HmappedEq: getMappedPaddr child2 s1 = getMappedPaddr child2 s0)
                      by (rewrite Hs1; apply getMappedPaddrEqPDT with entry0; intuition).
        rewrite HconfigEq. rewrite HmappedEq. reflexivity.
      }
      rewrite HusedPaddrChild2Eq. assumption.
Qed.