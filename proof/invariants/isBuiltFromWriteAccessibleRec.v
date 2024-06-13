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

Require Import Model.ADT Model.Monad Model.Lib Model.MALInternal.
Require Import Proof.WeakestPreconditions Proof.Consistency Proof.StateLib Proof.DependentTypeLemmas
              Proof.InternalLemmas Proof.Isolation.
Require Import Hoare Invariants findBlockInKS.
Require Import FunctionalExtensionality List Lia Coq.Logic.ProofIrrelevance Coq.Bool.Bool Coq.Bool.BoolEq.
Import List.ListNotations.

Module WP := WeakestPreconditions.
Module DTL := DependentTypeLemmas.

(** Properties of isBuiltFromWriteAccessibleRec **)

Fixpoint isBuiltFromWriteAccessibleRec (s0 s: state) (statesList: list state) (pdEntriesList: list paddr)
(pdbasepartition startaddr endaddr: paddr) (flag: bool) :=
match statesList with
| nil => pdEntriesList = nil /\ s = s0
| s2::newStatesList =>
        exists pdAddr newPdEntriesList,
            pdEntriesList = pdAddr::newPdEntriesList
            /\ exists (realMPU : list paddr) (pdentry0 pdentry1 : PDTable) (blockInParentPartitionAddr: paddr)
                  (bentry newBentry: BlockEntry) (s1: state),
                 s1 =
                  {|
                    currentPartition := currentPartition s0;
                    memory :=
                      add blockInParentPartitionAddr
                        (BE
                           (CBlockEntry (read bentry) (write bentry) (exec bentry)
                              (present bentry) flag (blockindex bentry) (blockrange bentry)))
                        (memory s0) beqAddr
                  |}
                 /\ ((s2 = s1) \/ (s2 =
                     {|
                       currentPartition := currentPartition s0;
                       memory :=
                         add pdAddr
                           (PDT
                              {|
                                structure := structure pdentry1;
                                firstfreeslot := firstfreeslot pdentry1;
                                nbfreeslots := nbfreeslots pdentry1;
                                nbprepare := nbprepare pdentry1;
                                parent := parent pdentry1;
                                MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                                vidtAddr := vidtAddr pdentry1
                              |}) (memory s1) beqAddr
                     |}
                     /\ pdentryMPU pdAddr realMPU s1))
                  /\ newBentry =
                           CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                             (blockindex bentry) (blockrange bentry)
                  /\ lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
                  /\ lookup blockInParentPartitionAddr (memory s1) beqAddr = Some (BE newBentry)
                  /\ bentryPFlag blockInParentPartitionAddr true s0
                  /\ bentryStartAddr blockInParentPartitionAddr startaddr s0
                  /\ bentryEndAddr blockInParentPartitionAddr endaddr s0
                  /\ In blockInParentPartitionAddr (getMappedBlocks pdAddr s0)
                  /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentry0)
                  /\ lookup pdbasepartition (memory s1) beqAddr = Some (PDT pdentry0)
                  /\ lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
                  /\ lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)
                  /\ pdAddr = parent pdentry0
                  /\ pdbasepartition <> constantRootPartM
                  /\ isBuiltFromWriteAccessibleRec s2 s newStatesList newPdEntriesList pdAddr startaddr endaddr
                        flag(*)*)
end.

(* General properties *)

Lemma lookupPDTEqWriteAccess cutStatesList initState parentsList pdparent startaddr endaddr flag s partition:
isPDT partition initState
-> isPDT pdparent initState
-> ~In pdparent parentsList
-> isBuiltFromWriteAccessibleRec initState s cutStatesList parentsList partition startaddr endaddr flag
-> lookup pdparent (memory s) beqAddr = lookup pdparent (memory initState) beqAddr.
Proof.
revert parentsList. revert initState. revert partition. induction cutStatesList.
- (* cutStatesList = [] *)
  simpl.
  intros partition initState parentsList HlookupPartsInit HlookupParentsInit HpartNotParent Hprops.
  destruct Hprops as [HparentsList HssInitEq]. subst s. reflexivity.
- (* cutStatesList = a::l *)
  simpl.
  intros partition initState parentsList HlookupPartsInit HlookupParentsInit HpartNotParent Hprops.
  destruct Hprops as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HpdAddrIsPDTA: isPDT pdAddr a).
  {
    unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite HlookupPdAddrs1. trivial.
    - destruct Ha as [Ha HMPU]. rewrite Ha. simpl. rewrite beqAddrTrue. trivial.
  }
  assert(HlookupEqs1: lookup pdparent (memory s1) beqAddr = lookup pdparent (memory initState) beqAddr).
  {
    rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
      unfold isPDT in HlookupParentsInit. rewrite HlookupBlocks0 in HlookupParentsInit. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
  }
  rewrite HparentsList in HpartNotParent. simpl in HpartNotParent. apply Decidable.not_or in HpartNotParent.
  destruct HpartNotParent as [HpdAddrNotParent HpartNotParent].
  assert(HlookupEqA: lookup pdparent (memory a) beqAddr = lookup pdparent (memory initState) beqAddr).
  {
    rewrite <-HlookupEqs1. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrFalse in HpdAddrNotParent.
      rewrite HpdAddrNotParent. rewrite <-beqAddrFalse in HpdAddrNotParent. rewrite removeDupIdentity; intuition.
  }
  rewrite <-HlookupEqA.
  assert(HpdparentIsPDTA: isPDT pdparent a).
  {
    unfold isPDT in *. rewrite HlookupEqA. assumption.
  }
  specialize(IHcutStatesList pdAddr a newPdEntriesList HpdAddrIsPDTA HpdparentIsPDTA HpartNotParent HisBuilt).
  assumption.
Qed.

Lemma stablePDTIsBuilt statesList initState parentsList pdbasepartition startaddr endaddr flag s partition:
isPDT pdbasepartition initState
-> isBuiltFromWriteAccessibleRec initState s statesList parentsList pdbasepartition startaddr endaddr flag
-> isPDT partition initState
-> isPDT partition s.
Proof.
revert pdbasepartition. revert parentsList. revert initState. induction statesList.
- (* statesList = [] *)
  simpl.
  intros initState parentsList pdbasepartition HbaseIsPDTInit HisBuilt HpartIsPDTInit.
  destruct HisBuilt as [_ HssInitEq]. subst s. assumption.
- (* statesList = a::l *)
  simpl. intros initState parentsList pdbasepartition HbaseIsPDTInit HisBuilt HpartIsPDTInit.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HpdAddrIsPDTA: isPDT pdAddr a).
  {
    unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite HlookupPdAddrs1. trivial.
    - destruct Ha as [Ha HMPU]. rewrite Ha. simpl. rewrite beqAddrTrue. trivial.
  }
  assert(HpartIsPDTA: isPDT partition a).
  {
    assert(HpartIsPDTs1: isPDT partition s1).
    {
      unfold isPDT in *. rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HpartIsPDTInit. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; intuition.
    }
    unfold isPDT in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr partition) eqn:HbeqParentPart; try(trivial).
      rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity; intuition.
  }
  specialize(IHstatesList a newPdEntriesList pdAddr HpdAddrIsPDTA HisBuilt HpartIsPDTA).
  assumption.
Qed.

Lemma stablePDTParentIsBuilt statesList initState parentsList pdbasepartition pdentryPart startaddr endaddr flag
s partition:
isPDT pdbasepartition initState
-> isBuiltFromWriteAccessibleRec initState s statesList parentsList pdbasepartition startaddr endaddr flag
-> lookup partition (memory initState) beqAddr = Some(PDT pdentryPart)
-> exists pdentryParts, lookup partition (memory s) beqAddr = Some(PDT pdentryParts)
                        /\ parent pdentryPart = parent pdentryParts.
Proof.
revert pdentryPart. revert pdbasepartition. revert parentsList. revert initState. induction statesList.
- (* statesList = [] *)
  simpl.
  intros initState parentsList pdbasepartition pdentryPart HbaseIsPDTInit HisBuilt HlookupPartInit.
  destruct HisBuilt as [_ HssInitEq]. subst s. exists pdentryPart. intuition.
- (* statesList = a::l *)
  simpl. intros initState parentsList pdbasepartition pdentryPart HbaseIsPDTInit HisBuilt HlookupPartInit.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HpdAddrIsPDTA: isPDT pdAddr a).
  {
    unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite HlookupPdAddrs1. trivial.
    - destruct Ha as [Ha HMPU]. rewrite Ha. simpl. rewrite beqAddrTrue. trivial.
  }
  assert(HlookupEqs1: lookup partition (memory s1) beqAddr = lookup partition (memory initState) beqAddr).
  {
    rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst blockInParentPartitionAddr.
      rewrite HlookupBlocks0 in HlookupPartInit. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; intuition.
  }
  rewrite <-HlookupEqs1 in HlookupPartInit.
  destruct HpropsOr as [Has1Eq | Ha].
  + subst a.
    specialize(IHstatesList s1 newPdEntriesList pdAddr pdentryPart HpdAddrIsPDTA HisBuilt HlookupPartInit).
    assumption.
  + destruct Ha as [Ha _].
    assert(HlookupPartA: exists pdentryPartA, lookup partition (memory a) beqAddr = Some(PDT pdentryPartA)
                                              /\ parent pdentryPartA = parent pdentryPart).
    {
      rewrite Ha. simpl.
      destruct (beqAddr pdAddr partition) eqn:HbeqParentPart.
      * rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
        rewrite HlookupPartInit in HlookupPdAddrs1. injection HlookupPdAddrs1 as HpdentriesEq. subst pdentryPart.
        exists {|
                 structure := structure pdentryPdAddr;
                 firstfreeslot := firstfreeslot pdentryPdAddr;
                 nbfreeslots := nbfreeslots pdentryPdAddr;
                 nbprepare := nbprepare pdentryPdAddr;
                 parent := parent pdentryPdAddr;
                 MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                 vidtAddr := vidtAddr pdentryPdAddr
               |}. intuition.
      * rewrite <-beqAddrFalse in HbeqParentPart. exists pdentryPart. rewrite removeDupIdentity; intuition.
    }
    destruct HlookupPartA as [pdentryPartA (HlookupPartA & HparentsEq)].
    rewrite <-HparentsEq.
    specialize(IHstatesList a newPdEntriesList pdAddr pdentryPartA HpdAddrIsPDTA HisBuilt HlookupPartA).
    assumption.
Qed.

Lemma stablePDTParentIsBuiltRev statesList initState parentsList pdbasepartition pdentryPart startaddr endaddr
flag s partition:
(*isPDT pdbasepartition initState
-> *) isBuiltFromWriteAccessibleRec initState s statesList parentsList pdbasepartition startaddr endaddr flag
-> lookup partition (memory s) beqAddr = Some(PDT pdentryPart)
-> exists pdentryPartInit, lookup partition (memory initState) beqAddr = Some(PDT pdentryPartInit)
                        /\ parent pdentryPart = parent pdentryPartInit.
Proof.
revert pdentryPart. revert pdbasepartition. revert parentsList. revert initState. induction statesList.
- (* statesList = [] *)
  simpl.
  intros initState parentsList pdbasepartition pdentryPart HisBuilt HlookupPartInit.
  destruct HisBuilt as [_ HssInitEq]. subst s. exists pdentryPart. intuition.
- (* statesList = a::l *)
  simpl. intros initState parentsList pdbasepartition pdentryPart HisBuilt HlookupPartInit.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  specialize(IHstatesList a newPdEntriesList pdAddr pdentryPart HisBuilt HlookupPartInit).
  destruct IHstatesList as [pdentryPartInit (HlookupPartA & HparentsEq)]. destruct HpropsOr as [Has1Eq | Ha].
  + subst a.
    assert(HlookupEqs1: lookup partition (memory s1) beqAddr = lookup partition (memory initState) beqAddr).
    {
      rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks1 in HlookupPartA. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; intuition.
    }
    rewrite HlookupEqs1 in HlookupPartA. exists pdentryPartInit. intuition.
  + destruct Ha as [Ha _]. rewrite Ha in HlookupPartA. simpl in HlookupPartA.
    destruct (beqAddr pdAddr partition) eqn:HbeqParentPart.
    * rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *. exists pdentryPdAddr.
      split. assumption. rewrite HparentsEq. injection HlookupPartA as HpdentriesLink.
      rewrite <-HpdentriesLink. simpl. reflexivity.
    * rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HlookupPartA; intuition.
      exists pdentryPartInit. split; try(assumption). rewrite Hs1 in HlookupPartA. simpl in HlookupPartA.
      destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPartA; intuition.
Qed.

Lemma stableBEIsBuiltRev statesList initState parentsList pdbasepartition startaddr endaddr flag s block:
isBE block s
-> isBuiltFromWriteAccessibleRec initState s statesList parentsList pdbasepartition startaddr endaddr flag
-> isBE block initState.
Proof.
intro HblockIsBE. revert pdbasepartition. revert parentsList. revert initState. induction statesList.
- (* statesList = [] *)
  simpl. intros initState parentsList pdbasepartition HisBuilt.
  destruct HisBuilt as [_ HssInitEq]. subst s. assumption.
- (* statesList = a::l *)
  simpl. intros initState parentsList pdbasepartition HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  specialize(IHstatesList a newPdEntriesList pdAddr HisBuilt).
  assert(HblockIsBEs1: isBE block s1).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. unfold isBE in IHstatesList. rewrite Ha in IHstatesList. simpl in IHstatesList.
      destruct (beqAddr pdAddr block) eqn:HbeqParentBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in IHstatesList; intuition.
  }
  unfold isBE in *. rewrite Hs1 in HblockIsBEs1. simpl in HblockIsBEs1.
  destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
  + rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block. rewrite HlookupBlocks0. trivial.
  + rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HblockIsBEs1; intuition.
Qed.


Lemma getAllPaddrAuxEqBuiltWithWriteAcc s0 s blocklist statesList parentsList startaddr endaddr buildPart flag:
isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> getAllPaddrAux blocklist s = getAllPaddrAux blocklist s0.
Proof.
revert buildPart. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [_ Hss0Eq]. subst s. reflexivity.
- (* statesList = a::l *)
  intros s0 parentsList buildPart HisBuilt.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HcurPart: currentPartition s0 = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPart in HpropsOr.
  specialize(IHstatesList a newPdEntriesList pdAddr HisBuilt).
  rewrite IHstatesList.
  assert(HgetPaddrAuxEqs1: getAllPaddrAux blocklist s1 = getAllPaddrAux blocklist s0).
  {
    rewrite Hs1.
    apply getAllPaddrAuxEqBEStartEndNoChange with bentry; try(assumption);
        try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
            try(lia); simpl; reflexivity).
  }
  rewrite <-HgetPaddrAuxEqs1.
  destruct HpropsOr as [Has1Eq | Ha].
  + (* a = s1 *)
    rewrite Has1Eq. reflexivity.
  + (* a <> s1 *)
    destruct Ha as [Ha _]. rewrite Ha. apply getAllPaddrAuxEqPDT; intuition. unfold isPDT.
    rewrite HlookupAncestors1. trivial.
Qed.

Lemma blockrangeEqBuiltWithWriteAcc s0 s blockaddr bentry bentrys0 statesList parentsList startaddr endaddr
buildPart flag:
lookup blockaddr (memory s) beqAddr = Some (BE bentry)
-> lookup blockaddr (memory s0) beqAddr = Some (BE bentrys0)
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> blockrange bentry = blockrange bentrys0.
Proof.
revert buildPart. revert parentsList. revert bentrys0. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 bentrys0 parentsList buildPart HlookupBlocks HlookupBlocks0 HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [_ Hss0Eq]. subst s. rewrite HlookupBlocks in HlookupBlocks0.
  injection HlookupBlocks0 as HbentriesEq. rewrite HbentriesEq. reflexivity.
- (* statesList = a::l *)
  intros s0 bentrys0 parentsList buildPart HlookupBlocks HlookupBlocks0 HisBuilt.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry' & (newBentry & (s1 & (Hs1 & (HpropsOr
                      (*& (HlastCase*)
                       & (HnewB & (HlookupBlock's0 & HlookupBlock's1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HlowerThanMax: blockindex bentry' < kernelStructureEntriesNb) by (apply Hidx).
  assert(HcurPart: currentPartition s0 = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPart in HpropsOr.
  assert(HlookupBlockA: exists bentryA, lookup blockaddr (memory a) beqAddr = Some (BE bentryA)
                        /\ blockrange bentryA = blockrange bentrys0).
  {
    destruct (beqAddr blockInParentPartitionAddr blockaddr) eqn:HbeqBlockBlock.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockInParentPartitionAddr.
      exists newBentry. split.
      destruct HpropsOr as [Has1Eq | Ha]; try(subst a; assumption).
      destruct Ha as [Ha _]. rewrite Ha. simpl.
      + destruct (beqAddr pdAddr blockaddr) eqn:HbeqPdAddrBlock.
        {
          rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlock. rewrite HbeqPdAddrBlock in *.
          rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity; intuition.
      + rewrite HnewB.
        unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry') kernelStructureEntriesNb);
            try(lia). simpl. rewrite HlookupBlock's0 in HlookupBlocks0. injection HlookupBlocks0 as HbentriesEq.
        rewrite HbentriesEq. reflexivity.
    - exists bentrys0. split; try(reflexivity).
      assert(HlookupBlocks1: lookup blockaddr (memory s1) beqAddr = Some (BE bentrys0)).
      {
        rewrite Hs1. simpl. rewrite HbeqBlockBlock.
        rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
      }
      destruct HpropsOr as [Has1Eq | Ha]; try(subst a; assumption).
      destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockaddr) eqn:HbeqPdAddrBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlock. rewrite HbeqPdAddrBlock in *.
        rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity; intuition.
  }
  destruct HlookupBlockA as [bentryA (HlookupBlockA & HrangesEqA)].
  rewrite <-HrangesEqA.
  specialize(IHstatesList a bentryA newPdEntriesList pdAddr HlookupBlocks HlookupBlockA HisBuilt).
  assumption.
Qed.

Lemma bentryStartAddrEqIsBuilt block startBlock s0 s statesList parentsList partition start endaddr flag:
isBuiltFromWriteAccessibleRec s0 s statesList parentsList partition start endaddr flag
-> isBE block s0
-> bentryStartAddr block startBlock s0
-> bentryStartAddr block startBlock s.
Proof.
revert partition. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList partition HisBuilt HblockIsBE Hstarts0. simpl in HisBuilt.
  destruct HisBuilt as [_ Hss0Eq]. subst s. assumption.
- (* statesList = a::l *)
  intros s0 parentsList partition HisBuilt HblockIsBE Hstarts0. simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr
                        (*& HbaseCase*) &
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(Hstarts1: bentryStartAddr block startBlock s1).
  {
    unfold bentryStartAddr in *. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
    + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockInParentPartitionAddr.
      rewrite HlookupBlocks0 in Hstarts0. unfold CBlockEntry.
      assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption.
    + rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; intuition.
  }
  assert(HstartA: bentryStartAddr block startBlock a).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + unfold bentryStartAddr in *. destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr block) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. rewrite HbeqParentBlock in *.
        rewrite HlookupPdAddrs0 in Hstarts0. congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HblockIsBEs1: isBE block s1).
  {
    unfold isBE in *. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
    + trivial.
    + rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; intuition.
  }
  assert(HblockIsBEA: isBE block a).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + unfold isBE in *. destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr block) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. rewrite HbeqParentBlock in *.
        rewrite HlookupPdAddrs1 in HblockIsBEs1. congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  specialize(IHstatesList a newPdEntriesList pdAddr HisBuilt HblockIsBEA HstartA). assumption.
Qed.

Lemma bentryPFlagEqIsBuilt block presentFlag s0 s statesList parentsList partition start endaddr flag:
isBuiltFromWriteAccessibleRec s0 s statesList parentsList partition start endaddr flag
-> isBE block s0
-> bentryPFlag block presentFlag s0
-> bentryPFlag block presentFlag s.
Proof.
revert partition. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList partition HisBuilt HblockIsBE Hstarts0. simpl in HisBuilt.
  destruct HisBuilt as [_ Hss0Eq]. subst s. assumption.
- (* statesList = a::l *)
  intros s0 parentsList partition HisBuilt HblockIsBE Hstarts0. simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(Hpresents1: bentryPFlag block presentFlag s1).
  {
    unfold bentryPFlag in *. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
    + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockInParentPartitionAddr.
      rewrite HlookupBlocks0 in Hstarts0. unfold CBlockEntry.
      assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption.
    + rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; intuition.
  }
  assert(HpresentA: bentryPFlag block presentFlag a).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + unfold bentryPFlag in *. destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr block) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. rewrite HbeqParentBlock in *.
        rewrite HlookupPdAddrs0 in Hstarts0. congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HblockIsBEs1: isBE block s1).
  {
    unfold isBE in *. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
    + trivial.
    + rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; intuition.
  }
  assert(HblockIsBEA: isBE block a).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + unfold isBE in *. destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr block) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. rewrite HbeqParentBlock in *.
        rewrite HlookupPdAddrs1 in HblockIsBEs1. congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  specialize(IHstatesList a newPdEntriesList pdAddr HisBuilt HblockIsBEA HpresentA). assumption.
Qed.

(* Partial consistency properties *)

Lemma currentPartitionEqIsBuilt partition statesList initState parentsList startaddr endaddr flag s:
isBuiltFromWriteAccessibleRec initState s statesList parentsList partition startaddr endaddr flag
-> currentPartition s = currentPartition initState.
Proof.
revert parentsList. revert partition. revert initState. induction statesList.
- (* statesList = [] *)
  intros initState partition parentsList HisBuilt. simpl in HisBuilt.
  destruct HisBuilt as [_ HsinitStateEq]. subst s. reflexivity.
- (* statesList = a::l *)
  intros initState partition parentsList HisBuilt. simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryParent &
                         (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr & HnewB &
                          HlookupBlockInit & HlookupBlocks1 & HPFlag & Hstart & Hend & HblockIsMapped &
                           HlookupPartInit & HlookupParts1 & HlookupParentInit & HlookupParents1 & Hparent &
                            HbaseNotRoot & HisBuilt))))))))))].
  specialize(IHstatesList a pdAddr newPdEntriesList HisBuilt).
  rewrite IHstatesList.
  assert(HcurrPartEq: currentPartition s1 = currentPartition initState).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  destruct HpropsOr as [Has1Eq | Ha].
  + subst a. assumption.
  + destruct Ha as [Ha _]. rewrite Ha. simpl. reflexivity.
Qed.

Lemma DisjointKSEntriesPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag:
DisjointKSEntries s0
-> StructurePointerIsKS s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> (StructurePointerIsKS s /\ DisjointKSEntries s /\ StructurePointerIsKS s1).
Proof.
intros Hdisjoint Hstruct HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(Hstructs1: StructurePointerIsKS s1).
{
  unfold StructurePointerIsKS in *. intros entryaddr pdentry HlookupEntry HstructNotNull.
  assert(HlookupEntrysInit: lookup entryaddr (memory s0) beqAddr = Some (PDT pdentry)).
  {
    rewrite Hs1 in HlookupEntry. simpl in HlookupEntry.
    destruct (beqAddr blockInParentPartitionAddr entryaddr) eqn:HbeqBlockEntry; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HlookupEntry; intuition.
  }
  specialize(Hstruct entryaddr pdentry HlookupEntrysInit HstructNotNull). rewrite Hs1. unfold isKS in *. simpl.
  destruct (beqAddr blockInParentPartitionAddr (structure pdentry)) eqn:HbeqBlockStruct.
  - rewrite <-DTL.beqAddrTrue in HbeqBlockStruct. rewrite HbeqBlockStruct in *.
    rewrite HlookupBlock in Hstruct. rewrite <-Hstruct. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
  - rewrite <-beqAddrFalse in HbeqBlockStruct. rewrite removeDupIdentity; intuition.
}
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
split.
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. assumption.
  - unfold StructurePointerIsKS in *.
    intros entryaddr pdentry HlookupEntry HstructNotNull.
    assert(HlookupEntrys1: exists pdentrys1, lookup entryaddr (memory s1) beqAddr = Some (PDT pdentrys1)
                                             /\ structure pdentrys1 = structure pdentry).
    {
      rewrite Hs in HlookupEntry. simpl in HlookupEntry.
      destruct (beqAddr pdAddr entryaddr) eqn:HbeqPdaddrEntry.
      + rewrite <-DTL.beqAddrTrue in HbeqPdaddrEntry. rewrite HbeqPdaddrEntry in *.
        rewrite HlookupPdAddrs1. exists pdentry1. injection HlookupEntry as HpdentriesEq.
        rewrite <-HpdentriesEq. simpl. split. reflexivity. reflexivity.
      + rewrite <-beqAddrFalse in HbeqPdaddrEntry. exists pdentry.
        rewrite removeDupIdentity in HlookupEntry; intuition.
    }
    destruct HlookupEntrys1 as [pdentrys1 (HlookupEntrys1 & HstructEq)].
    rewrite <-HstructEq in HstructNotNull.
    specialize(Hstructs1 entryaddr pdentrys1 HlookupEntrys1 HstructNotNull).
    rewrite <-HstructEq. unfold isKS in *. rewrite Hs. simpl.
    destruct (beqAddr pdAddr (structure pdentrys1)) eqn:HbeqPdaddrStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqPdaddrStruct. rewrite HbeqPdaddrStruct in *.
      rewrite HlookupPdAddrs1 in Hstructs1. congruence.
    }
    rewrite <-beqAddrFalse in HbeqPdaddrStruct. rewrite removeDupIdentity; intuition.
}
(**) split.
unfold DisjointKSEntries in *. intros pd1 pd2 HisPDT1 HisPDT2 Hpd1NotPd2.
assert(HisPDT1A: isPDT pd1 s0).
{
  unfold isPDT in *. destruct HpropsOr as [Has1Eq | Hs].
  - subst s. rewrite Hs1 in HisPDT1. simpl in HisPDT1.
    destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity in HisPDT1; intuition.
  - rewrite Hs in HisPDT1. rewrite Hs1 in HisPDT1. simpl in HisPDT1.
    destruct (beqAddr pdAddr pd1) eqn:HbeqPdaddrPd1.
    + rewrite <-DTL.beqAddrTrue in HbeqPdaddrPd1. rewrite HbeqPdaddrPd1 in *. rewrite HlookupPdAddr.
      trivial.
    + rewrite HbeqBlockPdAddr in HisPDT1. simpl in HisPDT1.
      destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HisPDT1; intuition.
      rewrite removeDupIdentity in HisPDT1; intuition.
}
assert(HisPDT2A: isPDT pd2 s0).
{
  unfold isPDT in *. destruct HpropsOr as [Has1Eq | Hs].
  - subst s. rewrite Hs1 in HisPDT2. simpl in HisPDT2.
    destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity in HisPDT2; intuition.
  - rewrite Hs in HisPDT2. rewrite Hs1 in HisPDT2. simpl in HisPDT2.
    destruct (beqAddr pdAddr pd2) eqn:HbeqPdaddrPd2.
    + rewrite <-DTL.beqAddrTrue in HbeqPdaddrPd2. rewrite HbeqPdaddrPd2 in *. rewrite HlookupPdAddr.
      trivial.
    + rewrite HbeqBlockPdAddr in HisPDT2. simpl in HisPDT2.
      destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HisPDT2; intuition.
      rewrite removeDupIdentity in HisPDT2; intuition.
}
specialize(Hdisjoint pd1 pd2 HisPDT1A HisPDT2A Hpd1NotPd2).
destruct Hdisjoint as [optionEntriesList1 (optionEntriesList2 & (Hlist1 & Hlist2 & Hdisjoint))].
exists optionEntriesList1. exists optionEntriesList2.
split. subst optionEntriesList1. destruct HpropsOr as [Hss1Eq | Hs].
{
  subst s. apply eq_sym. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock. trivial.
}
{
  assert(HgetKSEq: getKSEntries pd1 s = getKSEntries pd1 s1).
  {
    rewrite Hs. apply getKSEntriesEqPDT with pdentry1; try(assumption). unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
  }
  rewrite HgetKSEq. apply eq_sym. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock.
  trivial.
}
split. subst optionEntriesList2. destruct HpropsOr as [Hss1Eq | Hs].
{
  subst s. apply eq_sym. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock. trivial.
}
{
  assert(HgetKSEq: getKSEntries pd2 s = getKSEntries pd2 s1).
  {
    rewrite Hs.
    apply getKSEntriesEqPDT with pdentry1; try(assumption). unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
  }
  rewrite HgetKSEq. apply eq_sym. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock.
  trivial.
}
assumption. assumption.
Qed.

Lemma DisjointKSEntriesPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr flag:
DisjointKSEntries s0
-> StructurePointerIsKS s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> (StructurePointerIsKS s /\ DisjointKSEntries s).
Proof.
revert s0. revert parentsList. revert buildPart. induction statesList.
- simpl. intros buildPart parentsList s0 Hdisjoint Hstruct HisBuilt. destruct HisBuilt as [_ Hss0Eq].
  subst s. intuition.
- simpl. intros buildPart parentsList s0 Hdisjoint Hstruct HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HpropsA: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  {
    assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
    { rewrite Hs1. simpl. reflexivity. }
    rewrite HcurrPartEq in HpropsOr.
    apply DisjointKSEntriesPreservedIsBuilt with s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
        (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  apply IHstatesList with pdAddr newPdEntriesList a; intuition.
Qed.

Lemma StructurePointerIsKSPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag:
StructurePointerIsKS s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> StructurePointerIsKS s.
Proof.
intros Hstruct HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(Hstructs1: StructurePointerIsKS s1).
{
  unfold StructurePointerIsKS in *. intros entryaddr pdentry HlookupEntry HstructNotNull.
  assert(HlookupEntrysInit: lookup entryaddr (memory s0) beqAddr = Some (PDT pdentry)).
  {
    rewrite Hs1 in HlookupEntry. simpl in HlookupEntry.
    destruct (beqAddr blockInParentPartitionAddr entryaddr) eqn:HbeqBlockEntry; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HlookupEntry; intuition.
  }
  specialize(Hstruct entryaddr pdentry HlookupEntrysInit HstructNotNull). rewrite Hs1. unfold isKS in *. simpl.
  destruct (beqAddr blockInParentPartitionAddr (structure pdentry)) eqn:HbeqBlockStruct.
  - rewrite <-DTL.beqAddrTrue in HbeqBlockStruct. rewrite HbeqBlockStruct in *.
    rewrite HlookupBlock in Hstruct. rewrite <-Hstruct. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
  - rewrite <-beqAddrFalse in HbeqBlockStruct. rewrite removeDupIdentity; intuition.
}
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
destruct HpropsOr as [Hss1Eq | Hs].
- subst s. assumption.
- unfold StructurePointerIsKS in *.
  intros entryaddr pdentry HlookupEntry HstructNotNull.
  assert(HlookupEntrys1: exists pdentrys1, lookup entryaddr (memory s1) beqAddr = Some (PDT pdentrys1)
                                           /\ structure pdentrys1 = structure pdentry).
  {
    rewrite Hs in HlookupEntry. simpl in HlookupEntry.
    destruct (beqAddr pdAddr entryaddr) eqn:HbeqPdaddrEntry.
    + rewrite <-DTL.beqAddrTrue in HbeqPdaddrEntry. rewrite HbeqPdaddrEntry in *.
      rewrite HlookupPdAddrs1. exists pdentry1. injection HlookupEntry as HpdentriesEq.
      rewrite <-HpdentriesEq. simpl. split. reflexivity. reflexivity.
    + rewrite <-beqAddrFalse in HbeqPdaddrEntry. exists pdentry.
      rewrite removeDupIdentity in HlookupEntry; intuition.
  }
  destruct HlookupEntrys1 as [pdentrys1 (HlookupEntrys1 & HstructEq)].
  rewrite <-HstructEq in HstructNotNull.
  specialize(Hstructs1 entryaddr pdentrys1 HlookupEntrys1 HstructNotNull).
  rewrite <-HstructEq. unfold isKS in *. rewrite Hs. simpl.
  destruct (beqAddr pdAddr (structure pdentrys1)) eqn:HbeqPdaddrStruct.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPdaddrStruct. rewrite HbeqPdaddrStruct in *.
    rewrite HlookupPdAddrs1 in Hstructs1. congruence.
  }
  rewrite <-beqAddrFalse in HbeqPdaddrStruct. rewrite removeDupIdentity; intuition.
Qed.

Lemma StructurePointerIsKSPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr flag:
StructurePointerIsKS s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> StructurePointerIsKS s.
Proof.
revert s0. revert parentsList. revert buildPart. induction statesList.
- simpl. intros buildPart parentsList s0 Hstruct HisBuilt. destruct HisBuilt as [_ Hss0Eq].
  subst s. intuition.
- simpl. intros buildPart parentsList s0 Hstruct HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HstructA: StructurePointerIsKS a).
  {
    assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
    { rewrite Hs1. simpl. reflexivity. }
    rewrite HcurrPartEq in HpropsOr.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
        (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  apply IHstatesList with pdAddr newPdEntriesList a; intuition.
Qed.

Lemma wellFormedFstShadowIfBlockEntryPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
newMPU flag:
wellFormedFstShadowIfBlockEntry s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> wellFormedFstShadowIfBlockEntry s.
Proof.
intros HwellFormed HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(HwellFormeds1: wellFormedFstShadowIfBlockEntry s1).
{
  unfold wellFormedFstShadowIfBlockEntry in *. intros pa HpaIsBE.
  assert(HpaIsBEs0: isBE pa s0).
  {
    unfold isBE in *. rewrite Hs1 in HpaIsBE. simpl in HpaIsBE.
    destruct (beqAddr blockInParentPartitionAddr pa) eqn:HbeqBlockPa.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockPa. subst pa. rewrite HlookupBlock. trivial.
    - rewrite <-beqAddrFalse in HbeqBlockPa. rewrite removeDupIdentity in HpaIsBE; intuition.
  }
  specialize(HwellFormed pa HpaIsBEs0). unfold isSHE in *. rewrite Hs1. simpl.
  destruct (beqAddr blockInParentPartitionAddr (CPaddr (pa + sh1offset))) eqn:HbeqBlockPaSh1.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockPaSh1. rewrite HbeqBlockPaSh1 in *.
    rewrite HlookupBlock in HwellFormed. congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockPaSh1. rewrite removeDupIdentity; intuition.
}
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
destruct HpropsOr as [Hss1Eq | Hs].
- subst s. assumption.
- unfold wellFormedFstShadowIfBlockEntry in *.
  intros pa HpaIsBE.
  assert(HpaIsBEs1: isBE pa s1).
  {
    unfold isBE in *. rewrite Hs in HpaIsBE. simpl in HpaIsBE.
    destruct (beqAddr pdAddr pa) eqn:HbeqPdAddrPa; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqPdAddrPa. rewrite removeDupIdentity in HpaIsBE; intuition.
  }
  specialize(HwellFormeds1 pa HpaIsBEs1). unfold isSHE in *. rewrite Hs. simpl.
  destruct (beqAddr pdAddr (CPaddr (pa + sh1offset))) eqn:HbeqPdaddrPaSh1.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPdaddrPaSh1. rewrite HbeqPdaddrPaSh1 in *.
    rewrite HlookupPdAddrs1 in HwellFormeds1. congruence.
  }
  rewrite <-beqAddrFalse in HbeqPdaddrPaSh1. rewrite removeDupIdentity; intuition.
Qed.

Lemma wellFormedFstShadowIfBlockEntryPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr
flag:
wellFormedFstShadowIfBlockEntry s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> wellFormedFstShadowIfBlockEntry s.
Proof.
revert s0. revert parentsList. revert buildPart. induction statesList.
- simpl. intros buildPart parentsList s0 Hstruct HisBuilt. destruct HisBuilt as [_ Hss0Eq].
  subst s. intuition.
- simpl. intros buildPart parentsList s0 Hstruct HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HstructA: wellFormedFstShadowIfBlockEntry a).
  {
    assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
    { rewrite Hs1. simpl. reflexivity. }
    rewrite HcurrPartEq in HpropsOr.
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  apply IHstatesList with pdAddr newPdEntriesList a; intuition.
Qed.

Lemma noDupUsedPaddrListPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
newMPU flag:
noDupUsedPaddrList s0
-> StructurePointerIsKS s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> noDupUsedPaddrList s.
Proof.
intros HnoDup Hstruct HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
assert(HnoDups1: noDupUsedPaddrList s1).
{
  intros partition HpartIsPDT. unfold isPDT in HpartIsPDT. rewrite Hs1 in HpartIsPDT. simpl in HpartIsPDT.
  destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
  rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HpartIsPDT;
      try(apply not_eq_sym; assumption). specialize(HnoDup partition HpartIsPDT). unfold getUsedPaddr in *.
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  {
    unfold isBE. rewrite HlookupBlock. trivial.
  }
  assert(HgetConfigEq: getConfigPaddr partition s1 = getConfigPaddr partition s0).
  {
    rewrite Hs1. apply getConfigPaddrEqBE; assumption.
  }
  assert(HgetMappedEq: getMappedPaddr partition s1 = getMappedPaddr partition s0).
  {
    rewrite Hs1. apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
        try(assumption);
        unfold CBlockEntry;
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
        simpl; reflexivity.
  }
  rewrite HgetConfigEq. rewrite HgetMappedEq. assumption.
}
destruct HpropsOr as [Hss1Eq | Hs].
- subst s. assumption.
- unfold noDupUsedPaddrList in *. intros part HpartIsPDT.
  assert(HpartIsPDTs1: isPDT part s1).
  {
    unfold isPDT. unfold isPDT in HpartIsPDT. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
    destruct (beqAddr pdAddr part) eqn:HbeqParentPart.
    + rewrite <-DTL.beqAddrTrue in HbeqParentPart. subst part. rewrite HlookupPdAddrs1. trivial.
    + rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
  }
  specialize(HnoDups1 part HpartIsPDTs1). unfold getUsedPaddr in *.
  assert(HgetConfigEq: getConfigPaddr part s = getConfigPaddr part s1).
  {
    rewrite Hs. apply getConfigPaddrEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  assert(HgetMappedEq: getMappedPaddr part s = getMappedPaddr part s1).
  {
    rewrite Hs. apply getMappedPaddrEqPDT with pdentry1; try(assumption). simpl. reflexivity.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
        newMPU flag; intuition.
  }
  rewrite HgetConfigEq. rewrite HgetMappedEq. assumption.
Qed.

Lemma noDupUsedPaddrListPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr flag:
noDupUsedPaddrList s0
-> StructurePointerIsKS s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> noDupUsedPaddrList s.
Proof.
revert s0. revert parentsList. revert buildPart. induction statesList.
- simpl. intros buildPart parentsList s0 HnoDup Hstruct HisBuilt. destruct HisBuilt as [_ Hss0Eq].
  subst s. intuition.
- simpl. intros buildPart parentsList s0 HnoDup Hstruct HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
  { rewrite Hs1. simpl. reflexivity. }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  apply IHstatesList with pdAddr newPdEntriesList a; intuition.
Qed.

Lemma noDupMappedBlocksListPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
newMPU flag:
noDupMappedBlocksList s0
-> StructurePointerIsKS s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> noDupMappedBlocksList s.
Proof.
intros HnoDup Hstruct HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
assert(HnoDups1: noDupMappedBlocksList s1).
{
  intros partition HpartIsPDT.
  assert(HpartIsPDTs0: isPDT partition s0).
  {
    unfold isPDT in *. rewrite Hs1 in HpartIsPDT. simpl in HpartIsPDT.
    destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
  }
  assert(HgetMappedEq: getMappedBlocks partition s1 = getMappedBlocks partition s0).
  {
    rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. reflexivity.
  }
  rewrite HgetMappedEq. apply HnoDup. assumption.
}
destruct HpropsOr as [Hss1Eq | Hs].
- subst s. assumption.
- intros partition HpartIsPDT.
  assert(HpartIsPDTs1: isPDT partition s1).
  {
    unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
    destruct (beqAddr pdAddr partition) eqn:HbeqBlockPart.
    + rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst pdAddr. rewrite HlookupPdAddrs1. trivial.
    + rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
  }
  assert(HgetMappedEq: getMappedBlocks partition s = getMappedBlocks partition s1).
  {
    rewrite Hs. apply getMappedBlocksEqPDT with pdentry1. assumption.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          newMPU flag; intuition.
    simpl. reflexivity.
  }
  rewrite HgetMappedEq. apply HnoDups1. assumption.
Qed.

Lemma noDupMappedBlocksListPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr flag:
noDupMappedBlocksList s0
-> StructurePointerIsKS s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> noDupMappedBlocksList s.
Proof.
revert s0. revert parentsList. revert buildPart. induction statesList.
- simpl. intros buildPart parentsList s0 HnoDup Hstruct HisBuilt. destruct HisBuilt as [_ Hss0Eq].
  subst s. intuition.
- simpl. intros buildPart parentsList s0 HnoDup Hstruct HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
  { rewrite Hs1. simpl. reflexivity. }
  assert(HnoDupA: noDupMappedBlocksList a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply noDupMappedBlocksListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  apply IHstatesList with pdAddr newPdEntriesList a; intuition.
Qed.

Lemma wellFormedBlockPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
newMPU flag:
wellFormedBlock s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> bentryPFlag blockInParentPartitionAddr true s0
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> wellFormedBlock s.
Proof.
intros HwellFormed HlookupPdAddr HlookupBlock HPFlag HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
assert(HwellFormeds1: wellFormedBlock s1).
{
  unfold wellFormedBlock in *. intros block1 startaddr endaddr HPFlagBlock1 HstartBlock1 HendBlock1.
  assert(HPFlagBlock1s0: bentryPFlag block1 true s0).
  {
    unfold bentryPFlag in *. rewrite Hs1 in HPFlagBlock1. simpl in HPFlagBlock1.
    destruct (beqAddr blockInParentPartitionAddr block1) eqn:HbeqBlockBlock.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block1. rewrite HlookupBlock in *. assumption.
    - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HPFlagBlock1; intuition.
  }
  assert(HstartBlock1s0: bentryStartAddr block1 startaddr s0).
  {
    unfold bentryStartAddr in *. rewrite Hs1 in HstartBlock1. simpl in HstartBlock1.
    destruct (beqAddr blockInParentPartitionAddr block1) eqn:HbeqBlockBlock.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block1. rewrite HlookupBlock.
      unfold CBlockEntry in HstartBlock1.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl in HstartBlock1. assumption.
    - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HstartBlock1; intuition.
  }
  assert(HendBlock1s0: bentryEndAddr block1 endaddr s0).
  {
    unfold bentryEndAddr in *. rewrite Hs1 in HendBlock1. simpl in HendBlock1.
    destruct (beqAddr blockInParentPartitionAddr block1) eqn:HbeqBlockBlock.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block1. rewrite HlookupBlock.
      unfold CBlockEntry in HendBlock1.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl in HendBlock1. assumption.
    - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HendBlock1; intuition.
  }
  specialize(HwellFormed block1 startaddr endaddr HPFlagBlock1s0 HstartBlock1s0 HendBlock1s0).
  assumption.
}
destruct HpropsOr as [Hss1Eq | Hs].
{ subst s. assumption. }
unfold wellFormedBlock in *.
intros block1 startaddr endaddr HPFlagBlock1 HstartBlock1 HendBlock1.
assert(HPFlagBlock1s1: bentryPFlag block1 true s1).
{
  unfold bentryPFlag in *. rewrite Hs in HPFlagBlock1. simpl in HPFlagBlock1.
  destruct (beqAddr pdAddr block1) eqn:HbeqPdAddrBlock; try(exfalso; congruence).
  rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity in HPFlagBlock1; intuition.
}
assert(HstartBlock1s1: bentryStartAddr block1 startaddr s1).
{
  unfold bentryStartAddr in *. rewrite Hs in HstartBlock1. simpl in HstartBlock1.
  destruct (beqAddr pdAddr block1) eqn:HbeqPdAddrBlock; try(exfalso; congruence).
  rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity in HstartBlock1; intuition.
}
assert(HendBlock1s1: bentryEndAddr block1 endaddr s1).
{
  unfold bentryEndAddr in *. rewrite Hs in HendBlock1. simpl in HendBlock1.
  destruct (beqAddr pdAddr block1) eqn:HbeqPdAddrBlock; try(exfalso; congruence).
  rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity in HendBlock1; intuition.
}
specialize(HwellFormeds1 block1 startaddr endaddr HPFlagBlock1s1 HstartBlock1s1 HendBlock1s1).
assumption.
Qed.

Lemma wellFormedBlockPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr
flag:
wellFormedBlock s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> wellFormedBlock s.
Proof.
revert s0. revert parentsList. revert buildPart. induction statesList.
- simpl. intros buildPart parentsList s0 HwellFormed HisBuilt. destruct HisBuilt as [_ Hss0Eq].
  subst s. intuition.
- simpl. intros buildPart parentsList s0 HwellFormed HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HwellFormedA: wellFormedBlock a).
  {
    assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
    { rewrite Hs1. simpl. reflexivity. }
    rewrite HcurrPartEq in HpropsOr.
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  apply IHstatesList with pdAddr newPdEntriesList a; intuition.
Qed.

Lemma AccessibleNoPDFlagPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
newMPU flag:
AccessibleNoPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> AccessibleNoPDFlag s.
Proof.
intros Haccess HwellFormed HlookupPdAddr HlookupBlock HcheckChild HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}

assert(Haccessible: AccessibleNoPDFlag s1).
{
  unfold AccessibleNoPDFlag in *. intros block sh1entryaddr HBEblock Hsh1entry Haccessible.
  assert(HBEblockEq: isBE block s1 = isBE block s0).
  {
    rewrite Hs1. unfold isBE. simpl.
    destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockParentBlock.
    - (* blockInParentPartitionAddr = block *)
      rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlock. rewrite HbeqBlockParentBlock in *.
      rewrite HlookupBlock. reflexivity.
    - (* blockInParentPartitionAddr <> block *)
      rewrite <-beqAddrFalse in HbeqBlockParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(Hsh1entryEq: sh1entryAddr block sh1entryaddr s1 = sh1entryAddr block sh1entryaddr s0).
  {
    rewrite Hs1. unfold sh1entryAddr. simpl.
    destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockParentBlock.
    - (* blockInParentPartitionAddr = block *)
      rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlock. rewrite HbeqBlockParentBlock in *.
      rewrite HlookupBlock. reflexivity.
    - (* blockInParentPartitionAddr <> block *)
      rewrite <-beqAddrFalse in HbeqBlockParentBlock. rewrite removeDupIdentity; intuition.
  }
  rewrite HBEblockEq in HBEblock.
  assert(HSH1: isSHE sh1entryaddr s1).
  {
    unfold wellFormedFstShadowIfBlockEntry in HwellFormed. specialize(HwellFormed block HBEblock).
    unfold sh1entryAddr in Hsh1entry.
    unfold isBE in HBEblock. destruct (lookup block (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    rewrite Hsh1entry in *. unfold isSHE. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. subst blockInParentPartitionAddr.
      unfold isSHE in HwellFormed. rewrite HlookupBlock in HwellFormed. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HlookupSh1Eq: lookup sh1entryaddr (memory s1) beqAddr
                      = lookup sh1entryaddr (memory s0) beqAddr).
  {
    rewrite Hs1. simpl. unfold sh1entryAddr in Hsh1entry.
    unfold isBE in HBEblock. destruct (lookup block (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockParentSh1.
    - (* blockInParentPartitionAddr = sh1entryaddr *)
      rewrite <-DTL.beqAddrTrue in HbeqBlockParentSh1. rewrite HbeqBlockParentSh1 in *.
      unfold isSHE in HSH1. rewrite Hs1 in HSH1. simpl in HSH1. rewrite beqAddrTrue in HSH1. exfalso; congruence.
    - (* blockInParentPartitionAddr <> sh1entryaddr *)
      rewrite <-beqAddrFalse in HbeqBlockParentSh1. rewrite removeDupIdentity; intuition.
  }
  rewrite Hsh1entryEq in *.
  destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
  ++ (* blockInParentPartitionAddr = block *)
     rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block. unfold checkChild in HcheckChild.
     rewrite HlookupBlock in HcheckChild. unfold sh1entryAddr in Hsh1entry. rewrite HlookupBlock in Hsh1entry.
     subst sh1entryaddr. unfold sh1entryPDflag. rewrite Hs1. simpl. unfold isSHE in HSH1. rewrite Hs1 in HSH1.
     simpl in HSH1.
     destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1; try(congruence).
     rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
     rewrite removeDupIdentity in HSH1; try(apply not_eq_sym; assumption).
     destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr) eqn:HlookupBlockSh1;
            try(congruence). destruct v; try(exfalso; congruence). assumption.
  ++ (* blockInParentPartitionAddr <> block *)
    assert(HaccessibleEq: bentryAFlag block true s1 = bentryAFlag block true s0).
    {
      rewrite Hs1. unfold bentryAFlag. simpl. rewrite HbeqBlockBlock.
      - (* blockInParentPartitionAddr = block *)
        rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
    }
    rewrite HaccessibleEq in Haccessible.
    specialize(Haccess block sh1entryaddr HBEblock Hsh1entry Haccessible).
    unfold sh1entryPDflag in *. rewrite Hs1. simpl. unfold isSHE in HSH1. rewrite Hs1 in HSH1.
    simpl in HSH1.
    destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1; try(congruence).
    rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition.
  (* END AccessibleNoPDFlag *)
}
destruct HpropsOr as [Hss1Eq | Hs].
{ subst s. assumption. }
unfold AccessibleNoPDFlag in *.
intros block sh1entryaddr HblockIsBE Hsh1IsSh1 HAFlagBlock.
assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
{
  rewrite Hs. simpl. destruct (beqAddr pdAddr block) eqn:HbeqParentBlock.
  {
    (* pdAddr = block *)
    unfold isBE in HblockIsBE. rewrite Hs in HblockIsBE. simpl in HblockIsBE.
    rewrite HbeqParentBlock in HblockIsBE. exfalso; congruence.
  }
  (* pdAddr <> block *)
  rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
}
assert(HblockIsBEs1: isBE block s1).
{
  unfold isBE in *. rewrite HlookupBlockEq in HblockIsBE. assumption.
}
assert(Hsh1IsSh1s1: sh1entryAddr block sh1entryaddr s1).
{
  unfold sh1entryAddr in *. rewrite HlookupBlockEq in Hsh1IsSh1. assumption.
}
assert(HAFlags1: bentryAFlag block true s1).
{
  unfold bentryAFlag in *. rewrite HlookupBlockEq in HAFlagBlock. assumption.
}
specialize(Haccessible block sh1entryaddr HblockIsBEs1 Hsh1IsSh1s1 HAFlags1).
unfold sh1entryPDflag in *. rewrite Hs. simpl.
destruct (beqAddr pdAddr sh1entryaddr) eqn:HbeqParentSh1.
{ (* pdAddr = sh1entryaddr *)
  rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqParentSh1. rewrite HbeqParentSh1 in *.
  rewrite HlookupPdAddrs1 in Haccessible. congruence.
}
(* pdAddr <> sh1entryaddr *)
rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity; intuition.
Qed.

Lemma PDTIfPDFlagPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
flag:
PDTIfPDFlag s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> PDTIfPDFlag s.
Proof.
intros HPDTIfPDFlag HlookupPdAddr HlookupBlock HPDFlagFalse HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(HPDTIfPDFlags1: PDTIfPDFlag s1).
{
  unfold PDTIfPDFlag in *. intros idPDchild sh1entryaddr HcheckChild.
  assert(HcheckChilds0: true = checkChild idPDchild s0 sh1entryaddr
                        /\ sh1entryAddr idPDchild sh1entryaddr s0).
  {
    destruct HcheckChild as [HcheckChild Hsh1].
    unfold checkChild in *. unfold sh1entryAddr in *. rewrite Hs1 in HcheckChild. simpl in HcheckChild.
    rewrite Hs1 in Hsh1. simpl in Hsh1.
    destruct (beqAddr blockInParentPartitionAddr idPDchild) eqn:HbeqBlockIdChild.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockIdChild. subst idPDchild. rewrite HlookupBlock.
      destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity in HcheckChild; intuition.
    - rewrite <-beqAddrFalse in HbeqBlockIdChild. rewrite removeDupIdentity in Hsh1; try(intuition; congruence).
      rewrite removeDupIdentity in HcheckChild; try(intuition; congruence).
      destruct (lookup idPDchild (memory s0) beqAddr) eqn:HlookupIdPdChild; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1;
            try(exfalso; intuition; congruence).
      rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity in HcheckChild; intuition.
  }
  specialize(HPDTIfPDFlag idPDchild sh1entryaddr HcheckChilds0).
  destruct HPDTIfPDFlag as (HAFlag & HPFlag & [startaddr (Hstart & Hentry)]). unfold bentryAFlag in *.
  unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold entryPDT in *.
  rewrite Hs1. simpl.
  destruct (beqAddr blockInParentPartitionAddr idPDchild) eqn:HbeqBlockIdChild.
  - rewrite <-DTL.beqAddrTrue in HbeqBlockIdChild. rewrite HbeqBlockIdChild in *.
    destruct HcheckChilds0 as [HcheckChilds0 HchildSh1].
    unfold sh1entryAddr in HchildSh1. rewrite HlookupBlock in HchildSh1. subst sh1entryaddr.
    rewrite <-HcheckChilds0 in HPDFlagFalse. exfalso; congruence.
  - rewrite <-beqAddrFalse in HbeqBlockIdChild. rewrite removeDupIdentity; try(intuition; congruence).
    destruct (lookup idPDchild (memory s0) beqAddr) eqn:HlookupIdPdChild; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct (beqAddr blockInParentPartitionAddr (startAddr (blockrange b))) eqn:HbeqBlockStart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite HbeqBlockStart in *.
      rewrite HlookupBlock in Hentry. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockStart. split. assumption. split. assumption. exists startaddr.
    split. assumption. rewrite removeDupIdentity; try(intuition; congruence).
}
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
destruct HpropsOr as [Hss1Eq | Hs].
- subst s. assumption.
- unfold PDTIfPDFlag in *. intros idPDchild sh1entryaddr HcheckChild.
  assert(HcheckChilds1: true = checkChild idPDchild s1 sh1entryaddr
                        /\ sh1entryAddr idPDchild sh1entryaddr s1).
  {
    destruct HcheckChild as [HcheckChild Hsh1].
    unfold checkChild in *. unfold sh1entryAddr in *. rewrite Hs in HcheckChild. simpl in HcheckChild.
    rewrite Hs in Hsh1. simpl in Hsh1.
    destruct (beqAddr pdAddr idPDchild) eqn:HbeqPdAddrChild; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqPdAddrChild. rewrite removeDupIdentity in Hsh1; try(intuition; congruence).
    rewrite removeDupIdentity in HcheckChild; try(intuition; congruence).
    destruct (lookup idPDchild (memory s1) beqAddr) eqn:HlookupIdPdChild; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct (beqAddr pdAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; intuition; congruence).
    rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity in HcheckChild; intuition.
  }
  specialize(HPDTIfPDFlags1 idPDchild sh1entryaddr HcheckChilds1).
  destruct HPDTIfPDFlags1 as (HAFlag & HPFlag & [startaddr (Hstart & Hentry)]). unfold bentryAFlag in *.
  unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold entryPDT in *.
  rewrite Hs. simpl.
  destruct (beqAddr pdAddr idPDchild) eqn:HbeqPdaddrChild.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPdaddrChild. rewrite HbeqPdaddrChild in *.
    rewrite HlookupPdAddrs1 in Hstart. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in HbeqPdaddrChild. rewrite removeDupIdentity; intuition.
  destruct (lookup idPDchild (memory s1) beqAddr) eqn:HlookupIdChilds1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). split. reflexivity.
  destruct (beqAddr pdAddr (startAddr (blockrange b))) eqn:HbeqPdAddrStart; try(reflexivity).
  rewrite <-beqAddrFalse in HbeqPdAddrStart. rewrite removeDupIdentity; intuition.
  destruct (lookup (startAddr (blockrange b)) (memory s1) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
Qed.

Lemma multiplexerIsPDTPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
flag:
multiplexerIsPDT s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> multiplexerIsPDT s.
Proof.
intros HmultPDT HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HmultIsPDTA: multiplexerIsPDT s1).
{
  unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs1. simpl.
  destruct (beqAddr blockInParentPartitionAddr multiplexer) eqn:HbeqBlockMult.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockMult. rewrite HbeqBlockMult in *.
    rewrite HlookupBlock in HmultPDT. congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockMult. rewrite removeDupIdentity; intuition.
}
destruct HpropsOr as [Hss1Eq | Hs].
+ (* s = s1 *)
  rewrite Hss1Eq. assumption.
+ (* s <> s1 *)
  unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. simpl.
  destruct (beqAddr pdAddr multiplexer) eqn:HbeqPdAddrMult; try(trivial).
  rewrite <-beqAddrFalse in HbeqPdAddrMult. rewrite removeDupIdentity; intuition.
Qed.

Lemma multiplexerIsPDTPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr
flag:
multiplexerIsPDT s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> multiplexerIsPDT s.
Proof.
revert s0. revert parentsList. revert buildPart. induction statesList.
- simpl. intros buildPart parentsList s0 HmultPDT HisBuilt. destruct HisBuilt as [_ Hss0Eq].
  subst s. intuition.
- simpl. intros buildPart parentsList s0 HmultPDT HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
    { rewrite Hs1. simpl. reflexivity. }
    rewrite HcurrPartEq in HpropsOr.
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  apply IHstatesList with pdAddr newPdEntriesList a; intuition.
Qed.

Lemma isChildPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
flag:
isChild s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> parentOfPartitionIsPartition s0
-> StructurePointerIsKS s0
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> isChild s.
Proof.
intros HisChild HmultIsPDT HPDTIfPDFlag HwellFormed HparentIsPart Hstruct HnoPDFlag HlookupPdAddr HlookupBlock
  HpropsOr Hs1.
assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
{ unfold isBE. rewrite HlookupBlock. trivial. }
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
{
  rewrite Hs1. unfold multiplexerIsPDT in HmultIsPDT.
  apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
       with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
     try(assumption);
     try(unfold CBlockEntry;
         destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
         simpl; reflexivity).
  - unfold sh1entryAddr. rewrite HlookupBlock. reflexivity.
  - simpl. destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
    {
      specialize(HwellFormed blockInParentPartitionAddr HblockIsBE).
      rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
      unfold isSHE in HwellFormed. rewrite HlookupBlock in HwellFormed. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. subst blockInParentPartitionAddr.
    rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockPdAddr. rewrite removeDupIdentity; intuition.
}
assert(HisChilds1: isChild s1).
{
  unfold isChild in *.
  intros part parent HpartIsPart HparentIsParent.
  rewrite HgetPartEq in HpartIsPart.
  assert(HparentIsParents0: StateLib.pdentryParent part parent s0).
  {
    unfold StateLib.pdentryParent in *. rewrite Hs1 in HparentIsParent. simpl in HparentIsParent.
    destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart.
    { (* blockInParentPartitionAddr = part *)
      rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *.
      exfalso; congruence.
    }
    (* blockInParentPartitionAddr <> part *)
    rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HparentIsParent; intuition.
  }
  specialize(HisChild part parent HpartIsPart HparentIsParents0).
  assert(HgetChildrenEq: getChildren parent s1 = getChildren parent s0).
  {
    rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry.
    - unfold isPDT. unfold StateLib.pdentryParent in HparentIsParents0.
      destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      unfold parentOfPartitionIsPartition in HparentIsPart.
      specialize(HparentIsPart part p HlookupPart).
      destruct HparentIsPart as [HparentIsPart (HparentOfRoot & HparentPartNotEq)].
      destruct (beqAddr part constantRootPartM) eqn:HbeqPartRoot.
      { (* part = constantRootPartM *)
        rewrite <-DTL.beqAddrTrue in HbeqPartRoot. specialize(HparentOfRoot HbeqPartRoot).
        rewrite HparentOfRoot in *. subst parent.
        assert(Hnull: nullAddrExists s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
        unfold getChildren in HisChild.
        assert(Hcontra: ~In part []) by (apply in_nil).
        destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
      }
      (* part <> constantRootPartM *)
      rewrite <-beqAddrFalse in HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HparentIsPart] & _). subst parent.
      rewrite HparentIsPart. trivial.
    - assumption.
    - unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
    - unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
  }
  rewrite HgetChildrenEq. assumption.
}
destruct HpropsOr as [Hss1Eq | Hs].
+ (* s = s1 *)
  subst s. assumption.
+ (* s <> s1 *)
  unfold isChild in *. intros part parent HpartIsPart HparentIsParent.
  assert(HgetPartEqs: getPartitions multiplexer s = getPartitions multiplexer s1).
  {
    rewrite Hs. apply getPartitionsEqPDT with pdentry1.
    * assumption.
    * simpl. reflexivity.
    * apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          newMPU flag; intuition.
    * apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          newMPU flag; intuition.
  }
  assert(HpdentryParentEq: pdentryParent part parent s = pdentryParent part parent s1).
  {
    unfold pdentryParent. rewrite Hs. simpl.
    destruct (beqAddr pdAddr part) eqn:HbeqParentPart.
    - (* pdAddr = part *)
      rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
      rewrite HlookupPdAddrs1. simpl. reflexivity.
    - (* pdAddr = part *)
      rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity; intuition.
  }
  rewrite HgetPartEqs in HpartIsPart. rewrite HpdentryParentEq in HparentIsParent.
  specialize(HisChilds1 part parent HpartIsPart HparentIsParent).
  assert(HgetChildrenEq: getChildren parent s = getChildren parent s1).
  {
    rewrite Hs. apply getChildrenEqPDT with pdentry1; try(assumption). simpl. reflexivity.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          newMPU flag; intuition.
  }
  rewrite HgetChildrenEq. assumption.
Qed.

Lemma parentOfPartitionIsPartitionPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
newMPU flag:
parentOfPartitionIsPartition s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> parentOfPartitionIsPartition s.
Proof.
intros HparentOfPart HmultPDT HPDTIfPDFlag HwellFormedShadow Hstruct HnoPDFlag HlookupPdAddr HlookupBlock
    HpropsOr Hs1.
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. subst blockInParentPartitionAddr.
    rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockPdAddr. rewrite removeDupIdentity; intuition.
}
assert(parentOfPartitionIsPartition s1).
{
  assert(Hcons0: parentOfPartitionIsPartition s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
  unfold parentOfPartitionIsPartition in *.
  intros part entry HlookupPart.
  assert(HlookupParts0: lookup part (memory s0) beqAddr = Some (PDT entry)).
  {
    rewrite Hs1 in HlookupPart. simpl in HlookupPart.
    destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart;
         try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPart; intuition.
  }
  specialize(Hcons0 part entry HlookupParts0).
  destruct Hcons0 as [HparentIsPart (HparentOfRoot & HparentPartNotEq)]. split.
  - intro Hpart'NotRoot. specialize(HparentIsPart Hpart'NotRoot).
    destruct HparentIsPart as ([parentEntry HparentIsPart] & HparentIsPartMult). split. exists parentEntry.
    rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr (parent entry)) eqn:HbeqBlockParent.
    { (* blockInParentPartitionAddr = parent entry *)
      rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *.
      rewrite HlookupBlock in HparentIsPart. exfalso; congruence.
    }
    (* blockInParentPartitionAddr <> parent entry *)
    rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
    assert(HgetPartsEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1.
      apply getPartitionsEqBEPDflagFalse with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption).
      apply lookupSh1EntryAddr with bentry. assumption.
      unfold sh1entryPDflag. unfold checkChild in HnoPDFlag. rewrite HlookupBlock in HnoPDFlag.
      assert(HblockIsBE: isBE blockInParentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlock; trivial).
      specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
      destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence).
    }
    rewrite HgetPartsEq. assumption.
  - split. intro HpartIsRoot. specialize(HparentOfRoot HpartIsRoot). assumption. assumption.
}
destruct HpropsOr as [Hss1Eq | Hs].
+ (* s = s1 *)
  rewrite Hss1Eq. assumption.
+ (* s <> s1 *)
  assert(Hcons0: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
  unfold parentOfPartitionIsPartition in *. intros part pdentry HlookupPart.
  assert(HlookupPart's1: exists pdentrys1,
                           lookup part (memory s1) beqAddr = Some (PDT pdentrys1)
                           /\ parent pdentrys1 = parent pdentry).
  {
    rewrite Hs in HlookupPart. simpl in HlookupPart.
    destruct (beqAddr pdAddr part) eqn:HbeqParentPart.
    - (* pdAddr = part *)
      rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
      exists pdentry1. split. assumption. injection HlookupPart as Hpdentry.
      rewrite <-Hpdentry. simpl. reflexivity.
    - (* pdAddr <> part *)
      rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HlookupPart; intuition.
      exists pdentry. split. assumption. reflexivity.
  }
  destruct HlookupPart's1 as [pdentrys1 (HlookupPart's1 & HparentPartEq)].
  specialize(Hcons0 part pdentrys1 HlookupPart's1).
  destruct Hcons0 as [HparentOfParts1 (HparentOfRoot & HparentPartNotEq)].
  split.
  - intro Hpart'NotRoot. specialize(HparentOfParts1 Hpart'NotRoot). rewrite Hs. simpl.
    destruct (beqAddr pdAddr (parent pdentry)) eqn:HbeqParentEntryParent.
    * (* pdAddr = parent pdentry *)
      rewrite <-DTL.beqAddrTrue in HbeqParentEntryParent. rewrite HbeqParentEntryParent in *. split.
      exists ({|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}). reflexivity.
      assert(HgetPartsEq: getPartitions multiplexer {|
                                                      currentPartition := currentPartition s1;
                                                      memory :=
                                                        add (parent pdentry)
                                                          (PDT
                                                             {|
                                                               structure := structure pdentry1;
                                                               firstfreeslot := firstfreeslot pdentry1;
                                                               nbfreeslots := nbfreeslots pdentry1;
                                                               nbprepare := nbprepare pdentry1;
                                                               parent := parent pdentry1;
                                                               MPU := newMPU;
                                                               vidtAddr := vidtAddr pdentry1
                                                             |}) (memory s1) beqAddr
                                                    |} = getPartitions multiplexer s1).
      {
        rewrite Hs1. rewrite <-HbeqParentEntryParent in *.
        apply getPartitionsEqPDT with pdentry1; try(rewrite <-Hs1); try(assumption).
        simpl. reflexivity.
        apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
            bentry newMPU flag; intuition.
        apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
            newMPU flag; intuition.
      }
      rewrite HgetPartsEq. rewrite <-HparentPartEq. intuition.
    * (* pdAddr <> parent pdentry *)
      rewrite <-beqAddrFalse in HbeqParentEntryParent. rewrite removeDupIdentity; intuition.
      rewrite HparentPartEq in *. assumption.
      assert(HgetPartsEq: getPartitions multiplexer {|
                                                      currentPartition := currentPartition s1;
                                                      memory :=
                                                        add pdAddr
                                                          (PDT
                                                             {|
                                                               structure := structure pdentry1;
                                                               firstfreeslot := firstfreeslot pdentry1;
                                                               nbfreeslots := nbfreeslots pdentry1;
                                                               nbprepare := nbprepare pdentry1;
                                                               parent := parent pdentry1;
                                                               MPU := newMPU;
                                                               vidtAddr := vidtAddr pdentry1
                                                             |}) (memory s1) beqAddr
                                                    |} = getPartitions multiplexer s1).
      {
        apply getPartitionsEqPDT with pdentry1; try(assumption).
        simpl. reflexivity.
        apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
            bentry newMPU flag; intuition.
        apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
            newMPU flag; intuition.
      }
      rewrite HgetPartsEq. rewrite <-HparentPartEq. assumption.
  - split. intro HpartIsRoot. specialize(HparentOfRoot HpartIsRoot). rewrite HparentPartEq in *.
    assumption. rewrite <-HparentPartEq. assumption.
Qed.

Lemma childsBlocksPropsInParentPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
flag startaddr endaddr:
childsBlocksPropsInParent s0
-> wellFormedFstShadowIfBlockEntry s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> StructurePointerIsKS s0
-> DisjointKSEntries s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> bentryStartAddr blockInParentPartitionAddr startaddr s0
-> bentryEndAddr blockInParentPartitionAddr endaddr s0
-> In blockInParentPartitionAddr (getMappedBlocks pdAddr s0)
-> In pdAddr (getPartitions multiplexer s0)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> (forall child blockChild startChild endChild,
            In child (getChildren pdAddr s0)
            -> In blockChild (getMappedBlocks child s0)
            -> bentryStartAddr blockChild startChild s0
            -> bentryEndAddr blockChild endChild s0
            -> bentryPFlag blockChild true s0
            -> startaddr <= startChild
            -> endaddr >= endChild
            -> startaddr = startChild /\ endaddr = endChild)
-> childsBlocksPropsInParent s.
Proof.
intros HchildsBlocksProps HwellFormed HPDTIfPDFlag HmultIsPDT Hstruct Hdisjoint HlookupPdAddr HlookupBlock
    HstartBlock HendBlock HblockMapped HpdAddrIsPart HpropsOr Hs1 HPDFlag HblockNotCut child parentPart
    blockChild startChild endChild blockParent startParent endParent HparentIsPart HchildIsChild
    HblockChildMapped HstartChild HendChild HPFlagChild HblockParentMapped HstartParent HendParent HPFlagParent
    HstartsProp HendsProp.
assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
   eqn:HbeqBlockBlockSh1.
{
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0)
          by (unfold isBE; rewrite HlookupBlock; trivial).
  specialize(HwellFormed blockInParentPartitionAddr HblockIsBE).
  rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
  unfold isSHE in HwellFormed. rewrite HlookupBlock in HwellFormed. exfalso; congruence.
}
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
assert(HlookupPdAddrs: exists pdentry2, lookup pdAddr (memory s) beqAddr = Some (PDT pdentry2)).
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. exists pdentry1. assumption.
  - rewrite Hs. simpl. rewrite beqAddrTrue. exists {|
                                                     structure := structure pdentry1;
                                                     firstfreeslot := firstfreeslot pdentry1;
                                                     nbfreeslots := nbfreeslots pdentry1;
                                                     nbprepare := nbprepare pdentry1;
                                                     parent := parent pdentry1;
                                                     MPU := newMPU;
                                                     vidtAddr := vidtAddr pdentry1
                                                   |}. reflexivity.
}
destruct HlookupPdAddrs as [pdentry2 HlookupPdAddrs].
assert(Hstructs1: StructurePointerIsKS s1).
{
  apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
        (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr newMPU) flag; intuition.
}
assert(HgetPartMultEq: getPartitions multiplexer s = getPartitions multiplexer s1).
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. reflexivity.
  - rewrite Hs. apply getPartitionsEqPDT with pdentry1; try(assumption). simpl. reflexivity.
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr newMPU) flag; try(intuition; congruence).
}
rewrite HgetPartMultEq in HparentIsPart.
assert(HgetPartMultEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
{
  rewrite Hs1. unfold multiplexerIsPDT in HmultIsPDT.
  apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
       with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
     try(assumption);
     try(unfold CBlockEntry;
         destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
         simpl; reflexivity).
  - unfold sh1entryAddr. rewrite HlookupBlock. reflexivity.
  - simpl. rewrite HbeqBlockBlockSh1. rewrite <-beqAddrFalse in HbeqBlockBlockSh1.
    rewrite removeDupIdentity; intuition.
}
rewrite HgetPartMultEqs1 in HparentIsPart.
assert(HgetChildrenEq: getChildren parentPart s = getChildren parentPart s1).
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. reflexivity.
  - rewrite Hs. apply getChildrenEqPDT with pdentry1; try(assumption). simpl. reflexivity.
}
rewrite HgetChildrenEq in HchildIsChild.
assert(HgetChildrenEqs1: getChildren parentPart s1 = getChildren parentPart s0).
{
  rewrite Hs1.
  apply getChildrenEqBENoStartNoPresentChange with bentry;
        try(assumption);
        try(unfold CBlockEntry;
            destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
            simpl; reflexivity).
  apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
}
rewrite HgetChildrenEqs1 in HchildIsChild.
assert(HgetMappedEq: forall partition, getMappedBlocks partition s = getMappedBlocks partition s0).
{
  intro partition.
  assert(HgetMappedEq: getMappedBlocks partition s = getMappedBlocks partition s1).
  {
    destruct HpropsOr as [Hss1Eq | Hs].
    - subst s. reflexivity.
    - rewrite Hs. apply getMappedBlocksEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetMappedEq. rewrite Hs1.
  apply getMappedBlocksEqBENoChange with bentry; try(assumption);
        try(unfold CBlockEntry;
            destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
            simpl; reflexivity).
}
rewrite HgetMappedEq in HblockChildMapped. rewrite HgetMappedEq in HblockParentMapped.
assert(HlookupBlockChilds: exists bentryChild, lookup blockChild (memory s) beqAddr = Some(BE bentryChild)).
{
  unfold bentryStartAddr in HstartChild.
  destruct (lookup blockChild (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. reflexivity.
}
destruct HlookupBlockChilds as [bentryChilds HlookupBlockChilds].
assert(HlookupBlockChilds0: exists bentryChilds0, lookup blockChild (memory s0) beqAddr = Some(BE bentryChilds0)
                                                  /\ blockrange bentryChilds0 = blockrange bentryChilds
                                                  /\ present bentryChilds0 = present bentryChilds).
{
  assert(HlookupEq: lookup blockChild (memory s) beqAddr = lookup blockChild (memory s1) beqAddr).
  {
    destruct HpropsOr as [Hss1Eq | Hs].
    - subst s. reflexivity.
    - rewrite Hs. simpl. destruct (beqAddr pdAddr blockChild) eqn:HbeqPdAddrBlockChild.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlockChild. subst blockChild.
        rewrite HlookupBlockChilds in HlookupPdAddrs. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdAddrBlockChild. rewrite removeDupIdentity; intuition.
  }
  rewrite HlookupEq in *. rewrite Hs1 in *. simpl in *.
  destruct (beqAddr blockInParentPartitionAddr blockChild) eqn:HbeqBlockBlockChild.
  - (* blockInParentPartitionAddr = blockChild *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockBlockChild. subst blockChild. exists bentry.
    injection HlookupBlockChilds as HbentriesEq. split. assumption. rewrite <-HbentriesEq. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
    intuition.
  - (* blockInParentPartitionAddr <> blockChild *)
    rewrite <-beqAddrFalse in HbeqBlockBlockChild.
    rewrite removeDupIdentity in HlookupBlockChilds; try(apply not_eq_sym; assumption). exists bentryChilds.
    intuition.
}
destruct HlookupBlockChilds0 as [bentryChilds0 (HlookupBlockChilds0 & HblockrangeChildEq & HpresentChildEq)].
assert(HlookupBlockParents: exists bentryParent, lookup blockParent (memory s) beqAddr = Some(BE bentryParent)).
{
  unfold bentryStartAddr in HstartParent.
  destruct (lookup blockParent (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. reflexivity.
}
destruct HlookupBlockParents as [bentryParents HlookupBlockParents].
assert(HlookupBlockParentEqs1: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. reflexivity.
  - rewrite Hs. simpl. destruct (beqAddr pdAddr blockParent) eqn:HbeqPdAddrBlockParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlockParent. subst blockParent.
      rewrite HlookupBlockParents in HlookupPdAddrs. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqPdAddrBlockParent. rewrite removeDupIdentity; intuition.
}
assert(HlookupBlockParents0: exists bentryParents0, lookup blockParent (memory s0) beqAddr =
                                                      Some(BE bentryParents0)
                                                  /\ blockrange bentryParents0 = blockrange bentryParents
                                                  /\ present bentryParents0 = present bentryParents).
{
  rewrite HlookupBlockParentEqs1 in *. rewrite Hs1 in *. simpl in *.
  destruct (beqAddr blockInParentPartitionAddr blockParent) eqn:HbeqBlockBlockParent.
  - (* blockInParentPartitionAddr = blockParent *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockBlockParent. subst blockParent. exists bentry.
    injection HlookupBlockParents as HbentriesEq. split. assumption. rewrite <-HbentriesEq. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
    intuition.
  - (* blockInParentPartitionAddr <> blockParent *)
    rewrite <-beqAddrFalse in HbeqBlockBlockParent.
    rewrite removeDupIdentity in HlookupBlockParents; try(apply not_eq_sym; assumption). exists bentryParents.
    intuition.
}
destruct HlookupBlockParents0 as [bentryParents0 (HlookupBlockParents0 & HblockrangeParentEq &
                                  HpresentParentEq)].
assert(HstartChilds0: bentryStartAddr blockChild startChild s0).
{
  unfold bentryStartAddr in *. rewrite HlookupBlockChilds in HstartChild. rewrite HlookupBlockChilds0.
  rewrite HblockrangeChildEq. assumption.
}
assert(HendChilds0: bentryEndAddr blockChild endChild s0).
{
  unfold bentryEndAddr in *. rewrite HlookupBlockChilds in HendChild. rewrite HlookupBlockChilds0.
  rewrite HblockrangeChildEq. assumption.
}
assert(HPFlagChilds0: bentryPFlag blockChild true s0).
{
  unfold bentryPFlag in *. rewrite HlookupBlockChilds in HPFlagChild. rewrite HlookupBlockChilds0.
  rewrite HpresentChildEq. assumption.
}
assert(HstartParents0: bentryStartAddr blockParent startParent s0).
{
  unfold bentryStartAddr in *. rewrite HlookupBlockParents in HstartParent. rewrite HlookupBlockParents0.
  rewrite HblockrangeParentEq. assumption.
}
assert(HendParents0: bentryEndAddr blockParent endParent s0).
{
  unfold bentryEndAddr in *. rewrite HlookupBlockParents in HendParent. rewrite HlookupBlockParents0.
  rewrite HblockrangeParentEq. assumption.
}
assert(HPFlagParents0: bentryPFlag blockParent true s0).
{
  unfold bentryPFlag in *. rewrite HlookupBlockParents in HPFlagParent. rewrite HlookupBlockParents0.
  rewrite HpresentParentEq. assumption.
}
specialize(HchildsBlocksProps child parentPart blockChild startChild endChild blockParent startParent endParent
    HparentIsPart HchildIsChild HblockChildMapped HstartChilds0 HendChilds0 HPFlagChilds0 HblockParentMapped
    HstartParents0 HendParents0 HPFlagParents0 HstartsProp HendsProp).
destruct HchildsBlocksProps as (HcheckChild & HPDchild & HchildLoc & HAFlag).
assert(HlookupBlockParentSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                                = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
{
  assert(HblockParentIsBE: isBE blockParent s0).
  {
    unfold isBE. rewrite HlookupBlockParents0. trivial.
  }
  specialize(HwellFormed blockParent HblockParentIsBE).
  assert(HlookupBlockParentSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                                  = lookup (CPaddr (blockParent + sh1offset)) (memory s1) beqAddr).
  {
    destruct HpropsOr as [Hss1Eq | Hs].
    - subst s. reflexivity.
    - rewrite Hs. simpl. destruct (beqAddr pdAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqPdAddrBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlockSh1. subst pdAddr. unfold isSHE in HwellFormed.
        rewrite HlookupPdAddr in HwellFormed. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdAddrBlockSh1. rewrite removeDupIdentity; intuition.
  }
  rewrite HlookupBlockParentSh1Eq. rewrite Hs1. simpl.
  destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlockBlockParentSh1.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockBlockParentSh1. subst blockInParentPartitionAddr.
    unfold isSHE in HwellFormed. rewrite HlookupBlock in HwellFormed. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockBlockParentSh1. rewrite removeDupIdentity; intuition.
}
split. unfold checkChild in *. rewrite HlookupBlockParents. rewrite HlookupBlockParents0 in HcheckChild.
rewrite HlookupBlockParentSh1Eq. assumption. split. intros childGlobalID HPDchilds. apply HPDchild.
unfold sh1entryPDchild in *. rewrite HlookupBlockParentSh1Eq in HPDchilds. assumption.
split. intros blockIDInChild HchildLocs. apply HchildLoc. unfold sh1entryInChildLocation in *.
rewrite HlookupBlockParentSh1Eq in HchildLocs.
destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr) eqn:HlookupBlockParentSh1;
    try(exfalso; congruence). destruct v; try(exfalso; congruence).
destruct HchildLocs as [HinChildLocVal HBEifNotNull]. split. assumption. intro HnotNull.
specialize(HBEifNotNull HnotNull).
assert(HBE: isBE blockIDInChild s1).
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. assumption.
  - rewrite Hs in HBEifNotNull. unfold isBE in *. simpl in HBEifNotNull.
    destruct (beqAddr pdAddr blockIDInChild) eqn:HbeqPdAddrBlockID; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqPdAddrBlockID. rewrite removeDupIdentity in HBEifNotNull; intuition.
}
unfold isBE in HBE. rewrite Hs1 in HBE. simpl in HBE.
destruct (beqAddr blockInParentPartitionAddr blockIDInChild) eqn:HbeqBlockBlockID.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockBlockID. subst blockInParentPartitionAddr. unfold isBE.
  rewrite HlookupBlock. trivial.
}
{
  rewrite <-beqAddrFalse in HbeqBlockBlockID. rewrite removeDupIdentity in HBE; intuition.
}
intro HboundsDiff. specialize(HAFlag HboundsDiff). unfold bentryAFlag in *. rewrite HlookupBlockParentEqs1.
rewrite Hs1. simpl.
destruct (beqAddr blockInParentPartitionAddr blockParent) eqn:HbeqBlockBlockParent.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockBlockParent. subst blockParent.
  assert(HstartsEq: startaddr = startParent).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlock in *. rewrite <-HstartBlock in HstartParents0.
    apply eq_sym. assumption.
  }
  subst startParent.
  assert(HendsEq: endaddr = endParent).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlock in *. rewrite <-HendBlock in HendParents0.
    apply eq_sym. assumption.
  }
  subst endParent.
  destruct (beqAddr parentPart pdAddr) eqn:HbeqParentParent.
  - rewrite <-DTL.beqAddrTrue in HbeqParentParent. subst parentPart.
    specialize(HblockNotCut child blockChild startChild endChild HchildIsChild HblockChildMapped HstartChilds0
                HendChilds0 HPFlagChilds0 HstartsProp HendsProp). intuition.
  - rewrite <-beqAddrFalse in HbeqParentParent.
    assert(HparentIsPDT: isPDT parentPart s0).
    {
      apply partitionsArePDT; assumption.
    }
    assert(HpdAddrIsPDT: isPDT pdAddr s0).
    {
      apply partitionsArePDT; assumption.
    }
    specialize(Hdisjoint parentPart pdAddr HparentIsPDT HpdAddrIsPDT HbeqParentParent).
    destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]].
    subst list1. subst list2. unfold getMappedBlocks in HblockParentMapped.
    apply DTL.InFilterPresentInList in HblockParentMapped.
    specialize(Hdisjoint blockInParentPartitionAddr HblockParentMapped). unfold getMappedBlocks in HblockMapped.
    apply DTL.InFilterPresentInList in HblockMapped. exfalso; congruence.
}
rewrite <-beqAddrFalse in HbeqBlockBlockParent. rewrite removeDupIdentity; intuition.
Qed.

Lemma partitionTreeIsTreePreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
flag startaddr endaddr:
partitionTreeIsTree s0
-> parentOfPartitionIsPartition s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> StructurePointerIsKS s0
-> wellFormedFstShadowIfBlockEntry s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> bentryStartAddr blockInParentPartitionAddr startaddr s0
-> bentryEndAddr blockInParentPartitionAddr endaddr s0
-> In blockInParentPartitionAddr (getMappedBlocks pdAddr s0)
-> In pdAddr (getPartitions multiplexer s0)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> partitionTreeIsTree s.
Proof.
intros Htree HparentOfPart HPDTIfPDFlag HmultPDT Hstruct HwellFormedShadow HlookupPdAddr HlookupBlock Hstart Hend
    HblockMapped HpdAddrIsPart HpropsOr Hs1 HnoPDFlag.
assert(Htrees1: partitionTreeIsTree s1).
{
  intros child pdparent parentsList HchildNotRoot Hparent HparentsList.
  assert(HlookupChild: exists pdentryChild, lookup child (memory s1) beqAddr = Some(PDT pdentryChild)).
  {
    unfold pdentryParent in Hparent. destruct (lookup child (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists p. reflexivity.
  }
  destruct HlookupChild as [pdentryChild HlookupChild].
  assert(HlookupChildEq: lookup child (memory s1) beqAddr = lookup child (memory s0) beqAddr).
  {
    rewrite Hs1. simpl. rewrite Hs1 in HlookupChild. simpl in HlookupChild.
    destruct (beqAddr blockInParentPartitionAddr child) eqn:HbeqBlockChild; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockChild. rewrite removeDupIdentity; intuition.
  }
  assert(HlookupChilds0: lookup child (memory s0) beqAddr = Some(PDT pdentryChild)).
  { rewrite <-HlookupChildEq. assumption. }
  assert(Hparents0: pdentryParent child pdparent s0).
  { unfold pdentryParent in *. rewrite <-HlookupChildEq. assumption. }
  assert(HparentIsParent: pdparent = parent pdentryChild).
  {
    unfold pdentryParent in Hparent. rewrite HlookupChild in Hparent. assumption.
  }
  assert(HlookupParent: exists pdentryPdparent, lookup pdparent (memory s0) beqAddr = Some (PDT pdentryPdparent)).
  {
    specialize(HparentOfPart child pdentryChild HlookupChilds0).
    destruct HparentOfPart as (HparentIsPart & _ & HparentNotChild). specialize(HparentIsPart HchildNotRoot).
    subst pdparent. destruct HparentIsPart. assumption.
  }
  assert(HparentsLists0: isParentsList s0 parentsList pdparent).
  {
    rewrite Hs1 in HparentsList.
    apply isParentsListEqBE with blockInParentPartitionAddr (CBlockEntry (read bentry) (write bentry)
                                  (exec bentry) (present bentry) flag (blockindex bentry) (blockrange bentry))
                                  bentry;
          assumption.
  }
  destruct HlookupParent as [pdentryPdparent HlookupParent].
  specialize(Htree child pdparent parentsList HchildNotRoot Hparents0 HparentsLists0). assumption.
}
destruct HpropsOr as [Hss1Eq | Hs].
- subst s. assumption.
- intros child pdparent parentsList HchildNotRoot Hparent HparentsList.
  assert(HlookupChild: exists pdentryChild, lookup child (memory s) beqAddr = Some(PDT pdentryChild)).
  {
    unfold pdentryParent in Hparent. destruct (lookup child (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists p. reflexivity.
  }
  destruct HlookupChild as [pdentryChild HlookupChild].
  assert(HlookupChilds1: exists pdentryChilds1, lookup child (memory s1) beqAddr = Some(PDT pdentryChilds1)
                                                /\ parent pdentryChilds1 = parent pdentryChild).
  {
    rewrite Hs in HlookupChild. simpl in HlookupChild.
    destruct (beqAddr pdAddr child) eqn:HbeqPdAddrChild.
    + rewrite <-DTL.beqAddrTrue in HbeqPdAddrChild. subst pdAddr. exists pdentry1.
      injection HlookupChild as HpdentriesEq. rewrite <-HpdentriesEq. rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr child) eqn:HbeqBlockChild.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockChild. subst blockInParentPartitionAddr.
        rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockChild. rewrite removeDupIdentity; intuition.
    + rewrite <-beqAddrFalse in HbeqPdAddrChild. exists pdentryChild.
      rewrite removeDupIdentity in HlookupChild; intuition.
  }
  destruct HlookupChilds1 as [pdentryChilds1 (HlookupChilds1 & HparentsEq)].
  assert(Hparents1: pdentryParent child pdparent s1).
  {
    unfold pdentryParent in *. rewrite HlookupChilds1. rewrite HlookupChild in Hparent. rewrite HparentsEq.
    assumption.
  }
  assert(HparentOfParts1: parentOfPartitionIsPartition s1).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry newMPU flag; intuition.
  }
  assert(HparentIsParent: pdparent = parent pdentryChilds1).
  {
    unfold pdentryParent in Hparents1. rewrite HlookupChilds1 in Hparents1. assumption.
  }
  assert(HlookupParent: exists pdentryPdparent, lookup pdparent (memory s1) beqAddr = Some (PDT pdentryPdparent)).
  {
    specialize(HparentOfParts1 child pdentryChilds1 HlookupChilds1).
    destruct HparentOfParts1 as (HparentIsPart & _ & HparentNotChild). specialize(HparentIsPart HchildNotRoot).
    subst pdparent. destruct HparentIsPart. assumption.
  }
  destruct HlookupParent as [pdentryPdparent HlookupParent].
  assert(HparentsLists1: isParentsList s1 parentsList pdparent).
  {
    apply isParentsListEqPDTSameParent with pdAddr {|
                                                     structure := structure pdentry1;
                                                     firstfreeslot := firstfreeslot pdentry1;
                                                     nbfreeslots := nbfreeslots pdentry1;
                                                     nbprepare := nbprepare pdentry1;
                                                     parent := parent pdentry1;
                                                     MPU := newMPU;
                                                     vidtAddr := vidtAddr pdentry1
                                                   |} s;
          try(assumption).
    simpl. exists pdentryPdparent. destruct (beqAddr pdAddr pdparent) eqn:HbeqPdAddrParent.
    + rewrite <-DTL.beqAddrTrue in HbeqPdAddrParent. subst pdAddr.
      exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := newMPU;
               vidtAddr := vidtAddr pdentry1
             |}. exists pdentryPdparent.
      split. assumption. split. rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity. split. assumption.
      assert(HlookupParentPdAddr: lookup pdparent (memory s0) beqAddr = Some (PDT pdentryPdparent)).
      {
        rewrite Hs1 in HlookupParent. simpl in HlookupParent.
        destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent; try(exfalso; congruence).
        rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity in HlookupParent; intuition.
      }
      rewrite HlookupParentPdAddr in HlookupPdAddr. injection HlookupPdAddr as HpdentriesEq.
      subst pdentryPdparent. split. reflexivity. split. intuition. intro. split. reflexivity. reflexivity.
    + exists pdentryPdparent. exists pdentry1. split. assumption. split. rewrite Hs. simpl.
      rewrite HbeqPdAddrParent. rewrite <-beqAddrFalse in HbeqPdAddrParent. rewrite removeDupIdentity; intuition.
      split. rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. subst blockInParentPartitionAddr.
        rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockPdAddr. rewrite removeDupIdentity; intuition.
      rewrite <-beqAddrFalse in HbeqPdAddrParent. intuition.
  }
  specialize(Htrees1 child pdparent parentsList HchildNotRoot Hparents1 HparentsLists1). assumption.
Qed.

(* General properties on important tools *)

Lemma lookupBEEqWriteAccess addr startaddr endaddr cutStatesList initState parentsList parent flag s partition:
isPDT partition initState
-> isBE addr initState
-> DisjointKSEntries initState
-> StructurePointerIsKS initState
-> ~In partition parentsList
-> In addr (getMappedBlocks partition initState)
-> isBuiltFromWriteAccessibleRec initState s cutStatesList parentsList parent startaddr endaddr flag
-> lookup addr (memory s) beqAddr = lookup addr (memory initState) beqAddr.
Proof.
revert parent. revert parentsList. revert initState. revert partition. induction cutStatesList.
- (* cutStatesList = [] *)
  simpl.
  intros partition initState parentsList parent HpartIsPDT HaddrIsBE Hdisjoint Hstruct HpartNotParent
      HaddrIsMapped Hprops.
  destruct Hprops as [HparentsList HssInitEq]. subst s. reflexivity.
- (* cutStatesList = a::l *)
  simpl.
  intros partition initState parentsList parent HpartIsPDT HaddrIsBE Hdisjoint Hstruct HpartNotParent
      HaddrIsMapped Hprops.
  destruct Hprops as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr &
                      (*(HlastCase &*)
                       (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HpartNotPdaddr: partition <> pdAddr).
  {
    rewrite HparentsList in HpartNotParent. simpl in HpartNotParent. apply Decidable.not_or in HpartNotParent.
    intuition.
  }
  destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockOldBlock.
  { (* blockInParentPartitionAddr = addr *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockOldBlock. rewrite HbeqBlockOldBlock in *. unfold getMappedBlocks in *.
    unfold DisjointKSEntries in Hdisjoint.
    assert(HpdaddrIsPDT: isPDT pdAddr initState) by (unfold isPDT; rewrite HlookupAncestorsInit; trivial).
    specialize(Hdisjoint partition pdAddr HpartIsPDT HpdaddrIsPDT HpartNotPdaddr).
    destruct Hdisjoint as [optionEntriesList1 (optionEntriesList2 & (Hlist1 & Hlist2 & Hdisjoint))].
    subst optionEntriesList1. subst optionEntriesList2. unfold Lib.disjoint in Hdisjoint.
    assert(HaddrIsKS: In addr (filterOptionPaddr (getKSEntries partition initState))).
    {
      clear HblockIsMapped. clear Hdisjoint. induction (filterOptionPaddr (getKSEntries partition initState));
                try(simpl in HaddrIsMapped; exfalso; congruence).
      simpl. simpl in HaddrIsMapped.
      destruct (lookup a0 (memory initState) beqAddr); try(right; apply IHl; intuition; congruence).
      destruct v; try(right; apply IHl; intuition; congruence).
      destruct (present b); try(right; apply IHl; intuition; congruence). simpl in HaddrIsMapped.
      destruct HaddrIsMapped. left. assumption. right. apply IHl. assumption.
    }
    assert(HblockIsKS: In addr (filterOptionPaddr (getKSEntries pdAddr initState))).
    {
      clear HaddrIsMapped. clear Hdisjoint. induction (filterOptionPaddr (getKSEntries pdAddr initState));
                try(simpl in HblockIsMapped; exfalso; congruence).
      simpl. simpl in HblockIsMapped.
      destruct (lookup a0 (memory initState) beqAddr); try(right; apply IHl; intuition; congruence).
      destruct v; try(right; apply IHl; intuition; congruence).
      destruct (present b); try(right; apply IHl; intuition; congruence). simpl in HblockIsMapped.
      destruct HblockIsMapped. left. assumption. right. apply IHl. assumption.
    }
    specialize(Hdisjoint addr HaddrIsKS). exfalso; congruence.
  }
  (* blockInParentPartitionAddr <> addr *)
  destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
  { (* blockInParentPartitionAddr = partition *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *. unfold isPDT in HpartIsPDT.
    rewrite HlookupBlocks0 in HpartIsPDT. exfalso; congruence.
  }
  (* blockInParentPartitionAddr <> partition *)
  destruct (beqAddr pdAddr partition) eqn:HbeqAncestorPart.
  { (* pdAddr = partition *)
    rewrite <-DTL.beqAddrTrue in HbeqAncestorPart. subst partition. exfalso; congruence.
  }
  (* pdAddr <> partition *)
  destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdaddr.
  { (* blockInParentPartitionAddr = pdAddr *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockPdaddr. rewrite HbeqBlockPdaddr in *.
    rewrite HlookupBlocks0 in HlookupAncestorsInit. exfalso; congruence.
  }
  (* blockInParentPartitionAddr <> pdAddr *)
  assert(HpartIsPDTa: isPDT partition a).
  {
    unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite Hs1. simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in HbeqBlockPart.
      rewrite removeDupIdentity; intuition.
    - destruct Ha as [Ha HMPU]. rewrite Ha. rewrite Hs1. simpl. rewrite HbeqAncestorPart.
      rewrite HbeqBlockPdaddr. simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in *.
      repeat rewrite removeDupIdentity; intuition.
  }
  assert(HcurPartEq: currentPartition initState = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPartEq in HpropsOr.
  assert(HpartConsist: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  { apply DisjointKSEntriesPreservedIsBuilt with initState pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition. }
  destruct HpartConsist as [HstructA (HdisjointA & Hstructs1)].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HpartNotParentRec: ~ In partition newPdEntriesList).
  {
    rewrite HparentsList in HpartNotParent. simpl in HpartNotParent. apply Decidable.not_or in HpartNotParent.
    destruct HpartNotParent. assumption.
  }
  assert(HaddrIsMappedA: In addr (getMappedBlocks partition a)).
  {
    assert(HgetMappedEqs1: getMappedBlocks partition s1 = getMappedBlocks partition initState).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    assert(HgetMappedEq: getMappedBlocks partition a = getMappedBlocks partition initState).
    {
      rewrite <-HgetMappedEqs1. destruct HpropsOr as [Has1Eq | Ha].
      - subst a. reflexivity.
      - destruct Ha as [Ha HMPU]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1.
        assumption. assumption. unfold CBlockEntry.
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite HgetMappedEq. assumption.
  }
  assert(HlookupAddrEq: lookup addr (memory a) beqAddr = lookup addr (memory initState) beqAddr).
  {
    assert(HlookupEq: lookup addr (memory s1) beqAddr = lookup addr (memory initState) beqAddr).
    {
      rewrite Hs1. simpl. rewrite HbeqBlockOldBlock. rewrite <-beqAddrFalse in HbeqBlockOldBlock.
      rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupEq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha HMPU]. rewrite Ha. simpl. destruct (beqAddr pdAddr addr) eqn:HbeqPdaddrAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdaddrAddr. rewrite HbeqPdaddrAddr in *. unfold isBE in HaddrIsBE.
        rewrite HlookupAncestorsInit in HaddrIsBE. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdaddrAddr. rewrite removeDupIdentity; intuition.
  }
  assert(HaddrIsBEa: isBE addr a).
  {
    unfold isBE in *. rewrite HlookupAddrEq. assumption.
  }
  specialize(IHcutStatesList partition a newPdEntriesList pdAddr HpartIsPDTa HaddrIsBEa HdisjointA HstructA
               HpartNotParentRec HaddrIsMappedA HisBuilt).
  rewrite IHcutStatesList. assumption.
Qed.

Lemma baseBlockAccessibleImpliesNoPDWithPartialIsBuilt s0 s1 s buildPart parentPart pdentry pdentry1 blockBase
bentry newMPU startaddr endaddr flag:
childsBlocksPropsInParent s0
-> DisjointKSEntries s0
-> StructurePointerIsKS s0
-> wellFormedFstShadowIfBlockEntry s0
-> parentOfPartitionIsPartition s0
-> nullAddrExists s0
-> lookup blockBase (memory s0) beqAddr = Some (BE bentry)
-> lookup buildPart (memory s0) beqAddr = Some (PDT pdentry)
-> lookup parentPart (memory s0) beqAddr = Some (PDT pdentry1)
-> parentPart = parent pdentry
-> In buildPart (getChildren parentPart s0)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add parentPart
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockBase
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> bentryPFlag blockBase true s0
-> bentryAFlag blockBase true s0
-> In blockBase (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> (forall blockPart bentryPart,
      lookup blockPart (memory s) beqAddr = Some (BE bentryPart)
      -> bentryPFlag blockPart true s
      -> In blockPart (getMappedBlocks parentPart s)
      -> bentryStartAddr blockPart startaddr s
      -> bentryEndAddr blockPart endaddr s
      -> false = checkChild blockPart s (CPaddr (blockPart + sh1offset))).
Proof.
intros HchildBlockProps Hdisjoint Hstruct HwellFormed HparentOfPart HnullExists HlookupBlockBases0 HlookupBuilds0
    HlookupParents0 Hparent HbuildPartIsChild HpropsOr Hs1 HPFlagBase HAFlagBase HblockBaseMappeds0 Hstarts0
    Hends0 block bentryBlock HlookupBlocks HPFlagBlocks HblockMappeds HstartBlocks HendBlocks.
assert(HgetMappedEq: getMappedBlocks parentPart s = getMappedBlocks parentPart s0).
{
  assert(Heqs1: getMappedBlocks parentPart s1 = getMappedBlocks parentPart s0).
  {
    rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
    assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
  }
  rewrite <-Heqs1. destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. reflexivity.
  - rewrite Hs. apply getMappedBlocksEqPDT with pdentry1.
    + rewrite Hs1. simpl. destruct (beqAddr blockBase parentPart) eqn:HbeqBlockBaseParent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBaseParent. subst blockBase. unfold bentryPFlag in HPFlagBase.
        rewrite HlookupParents0 in HPFlagBase. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBaseParent. rewrite removeDupIdentity; intuition.
    + assert(StructurePointerIsKS s /\ DisjointKSEntries s /\ StructurePointerIsKS s1).
      {
        apply DisjointKSEntriesPreservedIsBuilt with s0 parentPart pdentry1 blockBase bentry newMPU flag;
            intuition.
      }
      intuition.
    + simpl. reflexivity.
}
rewrite HgetMappedEq in HblockMappeds.
assert(HbuildNotRoot: buildPart <> constantRootPartM).
{
  intro Hcontra. specialize(HparentOfPart buildPart pdentry HlookupBuilds0).
  destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot Hcontra).
  rewrite HparentOfRoot in Hparent. rewrite Hparent in HlookupParents0. unfold nullAddrExists in HnullExists.
  unfold isPADDR in HnullExists. rewrite HlookupParents0 in HnullExists. congruence.
}
assert(HparentIsPart: In parentPart (getPartitions multiplexer s0)).
{
  specialize(HparentOfPart buildPart pdentry HlookupBuilds0). destruct HparentOfPart as (HparentIsPart & _).
  specialize(HparentIsPart HbuildNotRoot). rewrite Hparent. intuition.
}
assert(HlookupBlockEqs1: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. reflexivity.
  - rewrite Hs. simpl. rewrite Hs in HlookupBlocks. simpl in HlookupBlocks.
    destruct (beqAddr parentPart block) eqn:HbeqParentBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
}
assert(HlookupBlocks0: exists bentryBlocks0, lookup block (memory s0) beqAddr = Some (BE bentryBlocks0)
                                              /\ blockrange bentryBlock = blockrange bentryBlocks0
                                              /\ present bentryBlock = present bentryBlocks0).
{
  rewrite HlookupBlockEqs1 in HlookupBlocks. rewrite Hs1 in HlookupBlocks. simpl in HlookupBlocks.
  destruct (beqAddr blockBase block) eqn:HbeqBlockBlock.
  - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block. exists bentry. split. assumption.
    injection HlookupBlocks as HbentriesEq. rewrite <-HbentriesEq. unfold CBlockEntry.
    assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. split. reflexivity. reflexivity.
  - rewrite <-beqAddrFalse in HbeqBlockBlock. exists bentryBlock.
    rewrite removeDupIdentity in HlookupBlocks; intuition.
}
destruct HlookupBlocks0 as [bentryBlocks0 (HlookupBlocks0 & HblockrangeEq & HpresentEq)].
assert(HstartBlocks0: bentryStartAddr block startaddr s0).
{
  unfold bentryStartAddr in *. rewrite HlookupBlocks0. rewrite HlookupBlocks in HstartBlocks.
  rewrite <-HblockrangeEq. assumption.
}
assert(HendBlocks0: bentryEndAddr block endaddr s0).
{
  unfold bentryEndAddr in *. rewrite HlookupBlocks0. rewrite HlookupBlocks in HendBlocks.
  rewrite <-HblockrangeEq. assumption.
}
assert(HPFlagBlocks0: bentryPFlag block true s0).
{
  unfold bentryPFlag in *. rewrite HlookupBlocks0. rewrite HlookupBlocks in HPFlagBlocks.
  rewrite <-HpresentEq. assumption.
}
assert(HstartTriv: startaddr <= startaddr) by intuition.
assert(HendTriv: endaddr >= endaddr) by intuition.
specialize(HchildBlockProps buildPart parentPart blockBase startaddr endaddr block startaddr endaddr HparentIsPart
            HbuildPartIsChild HblockBaseMappeds0 Hstarts0 Hends0 HPFlagBase HblockMappeds HstartBlocks0
            HendBlocks0 HPFlagBlocks0 HstartTriv HendTriv).
destruct HchildBlockProps as (Hprop & _). unfold checkChild in *.
rewrite HlookupBlocks0 in Hprop. rewrite HlookupBlocks.
assert(HlookupSh1Eq: lookup (CPaddr (block + sh1offset)) (memory s) beqAddr
                      = lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr).
{
  assert(HBE: isBE block s0).
  {
    unfold isBE. rewrite HlookupBlocks0. trivial.
  }
  specialize(HwellFormed block HBE).
  assert(HlookupSh1Eq: lookup (CPaddr (block + sh1offset)) (memory s1) beqAddr
                      = lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr).
  {
    rewrite Hs1. simpl. destruct (beqAddr blockBase (CPaddr (block + sh1offset))) eqn:HbeqBlockBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite HbeqBlockBlockSh1 in *. unfold isSHE in HwellFormed.
      rewrite HlookupBlockBases0 in HwellFormed. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
  }
  rewrite <-HlookupSh1Eq. destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. reflexivity.
  - rewrite Hs. simpl. destruct (beqAddr parentPart (CPaddr (block + sh1offset))) eqn:HbeqParentBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite HbeqParentBlockSh1 in *.
      unfold isSHE in HwellFormed. rewrite HlookupParents0 in HwellFormed. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
}
rewrite HlookupSh1Eq. assumption.
Qed.

Lemma getChildrenEqBuiltWithWriteAcc s0 s statesList parentsList startaddr endaddr buildPart flag pdbasepartition:
StructurePointerIsKS s0
-> isPDT pdbasepartition s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> getChildren pdbasepartition s = getChildren pdbasepartition s0.
Proof.
revert buildPart. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart Hstruct HbaseIsPDT HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [_ Hss0Eq]. subst s. reflexivity.
- (* statesList = a::l *)
  intros s0 parentsList buildPart Hstruct HbaseIsPDT HisBuilt.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HcurPart: currentPartition s0 = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPart in HpropsOr.
  assert(Hstructs1: StructurePointerIsKS s1).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HbaseIsPDTs1: isPDT pdbasepartition s1).
  {
    unfold isPDT in *. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr pdbasepartition) eqn:HbeqBlockBase.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBase. rewrite HbeqBlockBase in *. unfold isPDT in HbaseIsPDT.
      rewrite HlookupBlocks0 in HbaseIsPDT. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBase. rewrite removeDupIdentity; intuition.
  }
  assert(HbaseIsPDTA: isPDT pdbasepartition a).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. unfold isPDT in *. rewrite Ha. simpl.
      destruct (beqAddr pdAddr pdbasepartition) eqn:HbeqPdAddrBase.
      + trivial.
      + rewrite <-beqAddrFalse in HbeqPdAddrBase. rewrite removeDupIdentity; intuition.
  }
  specialize(IHstatesList a newPdEntriesList pdAddr HstructA HbaseIsPDTA HisBuilt).
  rewrite IHstatesList.
  assert(HgetChildrenEqs1: getChildren pdbasepartition s1 = getChildren pdbasepartition s0).
  {
    rewrite Hs1.
    apply getChildrenEqBENoStartNoPresentChange with bentry; try(assumption);
        try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
            try(lia); simpl; reflexivity).
  }
  rewrite <-HgetChildrenEqs1.
  destruct HpropsOr as [Has1Eq | Ha].
  + (* a = s1 *)
    rewrite Has1Eq. reflexivity.
  + (* a <> s1 *)
    destruct Ha as [Ha _]. rewrite Ha. apply getChildrenEqPDT with pdentry1; intuition.
Qed.

(* Isolation properties *)

Lemma partitionsIsolationPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
flag:
partitionsIsolation s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> partitionsIsolation s.
Proof.
intros HPI HPDTIfPDFlag HmultPDT HwellFormed Hstruct HnoPDFlag HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(HPIs1: partitionsIsolation s1).
{
  unfold partitionsIsolation in *. intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild
    HchildrenNotEq addr HaddrInChild1.
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  {
    unfold isBE. rewrite HlookupBlock. trivial.
  }
  assert(HgetUsedEq: forall partition, isPDT partition s0
                            -> getUsedPaddr partition s1 = getUsedPaddr partition s0).
  {
    intros partition HpartIsPDT. unfold getUsedPaddr.
    assert(HgetConfigEq: getConfigPaddr partition s1 = getConfigPaddr partition s0).
    {
      rewrite Hs1. apply getConfigPaddrEqBE; assumption.
    }
    assert(HgetMappedEq: getMappedPaddr partition s1 = getMappedPaddr partition s0).
    {
      rewrite Hs1. apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
            try(assumption);
            try(unfold CBlockEntry;
                destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                simpl; reflexivity).
    }
    rewrite HgetConfigEq. rewrite HgetMappedEq. reflexivity.
  }
  assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
  {
    rewrite Hs1.
    apply getPartitionsEqBEPDflagFalse with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
        try(assumption).
    apply lookupSh1EntryAddr with bentry; assumption.
    unfold sh1entryPDflag. unfold checkChild in HnoPDFlag. rewrite HlookupBlock in HnoPDFlag.
    specialize(HwellFormed blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormed.
    destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr);
        try(congruence). destruct v; try(congruence).
  }
  rewrite HgetPartEq in HparentIsPart.
  assert(isPDT pdparent s0).
  {
    apply partitionsArePDT; assumption.
  }
  assert(HgetChildrenEq: getChildren pdparent s1 = getChildren pdparent s0).
  {
    rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry;
            try(assumption);
            try(unfold CBlockEntry;
                destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                simpl; reflexivity).
  }
  rewrite HgetChildrenEq in *.
  assert(isPDT child1 s0).
  {
    apply childrenArePDT with pdparent; assumption.
  }
  assert(isPDT child2 s0).
  {
    apply childrenArePDT with pdparent; assumption.
  }
  rewrite HgetUsedEq in *; try(assumption).
  specialize(HPI pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HchildrenNotEq addr
      HaddrInChild1). assumption.
}
assert(Hstructs1: StructurePointerIsKS s1).
{
  apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
      flag; intuition.
}
assert(HPDTIfPDFlags1: PDTIfPDFlag s1).
{
  apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag;
      intuition.
}
destruct HpropsOr as [Hss1Eq | Hs].
+ (* s = s1 *)
  rewrite Hss1Eq. assumption.
+ (* s <> s1 *)
  unfold partitionsIsolation in *. intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild
    HchildrenNotEq addr HaddrInChild1.
  assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
  {
    rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
      rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
  }
  assert(HgetPartEq: getPartitions multiplexer s = getPartitions multiplexer s1).
  {
    rewrite Hs. apply getPartitionsEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetPartEq in HparentIsPart.
  assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s1).
  {
    rewrite Hs. apply getChildrenEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetChildrenEq in *.
  assert(HgetUsedEq: forall partition, isPDT partition s1
                            -> getUsedPaddr partition s = getUsedPaddr partition s1).
  {
    intros partition HpartIsPDT. unfold getUsedPaddr.
    assert(HgetConfigEq: getConfigPaddr partition s = getConfigPaddr partition s1).
    {
      rewrite Hs. apply getConfigPaddrEqPDT with pdentry1; try(assumption). simpl. reflexivity.
    }
    assert(HgetMappedEq: getMappedPaddr partition s = getMappedPaddr partition s1).
    {
      rewrite Hs. apply getMappedPaddrEqPDT with pdentry1; try(assumption). simpl. reflexivity.
    }
    rewrite HgetConfigEq. rewrite HgetMappedEq. reflexivity.
  }
  assert(isPDT child1 s1).
  {
    apply childrenArePDT with pdparent; assumption.
  }
  assert(isPDT child2 s1).
  {
    apply childrenArePDT with pdparent; assumption.
  }
  rewrite HgetUsedEq in *; try(assumption).
  specialize(HPIs1 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HchildrenNotEq addr
      HaddrInChild1). assumption.
Qed.

Lemma partitionsIsolationPreservedIsBuiltRec s s0 statesList parentsList buildPart pdentryBuild startaddr endaddr
flag blockBase bentryBase:
partitionsIsolation s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> DisjointKSEntries s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> childsBlocksPropsInParent s0
-> noDupUsedPaddrList s0
-> wellFormedBlock s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup buildPart (memory s0) beqAddr = Some (PDT pdentryBuild)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
-> In blockBase (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> partitionsIsolation s.
Proof.
revert bentryBase. revert blockBase. revert pdentryBuild. revert s0. revert parentsList. revert buildPart.
induction statesList.
- simpl. intros buildPart parentsList s0 _ _ _ HPI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HisBuilt.
  destruct HisBuilt as [_ Hss0Eq]. subst s. intuition.
- simpl. intros buildPart parentsList s0 pdentryBuild blockBase bentryBase HPI HPDTIfPDFlag HmultPDT
      HwellFormedShadow Hstruct Hdisjoint HparentOfPart HisChild HchildBlockProps HnoDup HwellFormedBlock
      HbuildIsPart HlookupBuild HlookupBlockBase HPFlagBase HnoPDFlagBase HblockBaseMapped HstartBase HendBase
      HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
  { rewrite Hs1. simpl. reflexivity. }
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    rewrite Hancestor. specialize(HparentOfPart buildPart pdentry0 HlookupParentsInit). intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupParentsInit. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupParentsInit. trivial.
  }
  assert(HnoPDFlag: false = checkChild blockInParentPartitionAddr s0
                                (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBase startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase HblockIsMapped HblockStart HblockEnd HPFlag HstartTriv HendTriv). intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
      try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HPI pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HPI. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPIA: partitionsIsolation a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    rewrite HcurrPartEq in HpropsOr.
    assert(HgetPartMultEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. unfold multiplexerIsPDT in HmultPDT.
      apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
           with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
         try(assumption);
         try(unfold CBlockEntry;
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
             simpl; reflexivity).
      - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
      - simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartMultEqs1. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartsEq in HpdAddrIsPart.
  assert(HlookupParentA: exists pdentry2, lookup pdAddr (memory a) beqAddr = Some (PDT pdentry2)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. exists pdentry1. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue.
      exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
               vidtAddr := vidtAddr pdentry1
             |}. reflexivity.
  }
  destruct HlookupParentA as [pdentry2 HlookupParentA].
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HPFlagA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlag. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HnoPDFlagA: false = checkChild blockInParentPartitionAddr a
                                        (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HnoPDFlag.
    assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                          = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
      assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
      {
        rewrite Hs1. simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
      }
      rewrite <-HlookupSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
      - subst a. reflexivity.
      - destruct Ha as [Ha _]. rewrite Ha. simpl.
        destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
          rewrite HlookupAncestorsInit in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite HlookupSh1Eq. assumption.
  }
  assert(HgetMappedEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    rewrite HcurrPartEq in HpropsOr.
    assert(HgetMappedEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite <-HgetMappedEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedEq in HblockIsMapped.
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  apply IHstatesList with pdAddr newPdEntriesList a pdentry2 blockInParentPartitionAddr newBentry; intuition.
Qed.

Lemma verticalSharingPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag:
verticalSharing s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> verticalSharing s.
Proof.
intros HVS HPDTIfPDFlag HmultPDT HwellFormed Hstruct HnoPDFlag HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(HVSs1: verticalSharing s1).
{
  unfold verticalSharing in *. intros pdparent child HparentIsPart HchildIsChild.
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  {
    unfold isBE. rewrite HlookupBlock. trivial.
  }
  assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
  {
    rewrite Hs1.
    apply getPartitionsEqBEPDflagFalse with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
        try(assumption).
    apply lookupSh1EntryAddr with bentry; assumption.
    unfold sh1entryPDflag. unfold checkChild in HnoPDFlag. rewrite HlookupBlock in HnoPDFlag.
    specialize(HwellFormed blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormed.
    destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr);
        try(congruence). destruct v; try(congruence).
  }
  rewrite HgetPartEq in HparentIsPart.
  assert(isPDT pdparent s0).
  {
    apply partitionsArePDT; assumption.
  }
  assert(HgetChildrenEq: getChildren pdparent s1 = getChildren pdparent s0).
  {
    rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry;
            try(assumption);
            try(unfold CBlockEntry;
                destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                simpl; reflexivity).
  }
  rewrite HgetChildrenEq in HchildIsChild. specialize(HVS pdparent child HparentIsPart HchildIsChild).
  assert(HgetMappedEq: forall partition, isPDT partition s0
              -> getMappedPaddr partition s1 = getMappedPaddr partition s0).
  {
    intros partition HpartitionPDT. rewrite Hs1.
    apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
            try(assumption);
            try(unfold CBlockEntry;
                destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                simpl; reflexivity).
  }
  assert(isPDT child s0).
  {
    apply childrenArePDT with pdparent; assumption.
  }
  unfold getUsedPaddr in *. rewrite HgetMappedEq; try(assumption). rewrite HgetMappedEq; try(assumption).
  assert(HgetConfigEq: getConfigPaddr child s1 = getConfigPaddr child s0).
  {
    rewrite Hs1. apply getConfigPaddrEqBE; assumption.
  }
  rewrite HgetConfigEq. assumption.
}
assert(Hstructs1: StructurePointerIsKS s1).
{
  apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
      flag; intuition.
}
assert(HPDTIfPDFlags1: PDTIfPDFlag s1).
{
  apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag;
      intuition.
}
assert(HmultPDTs1: multiplexerIsPDT s1).
{
  apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag;
      intuition.
}
destruct HpropsOr as [Hss1Eq | Hs].
+ (* s = s1 *)
  rewrite Hss1Eq. assumption.
+ (* s <> s1 *)
  unfold verticalSharing in *. intros pdparent child HparentIsPart HchildIsChild.
  assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
  {
    rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
      rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
  }
  assert(HgetPartEq: getPartitions multiplexer s = getPartitions multiplexer s1).
  {
    rewrite Hs. apply getPartitionsEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetPartEq in HparentIsPart.
  assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s1).
  {
    rewrite Hs. apply getChildrenEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetChildrenEq in HchildIsChild.
  assert(HgetMappedEq: forall partition, isPDT partition s1
                            -> getMappedPaddr partition s = getMappedPaddr partition s1).
  {
    intros partition HpartIsPDT. rewrite Hs. apply getMappedPaddrEqPDT with pdentry1; try(assumption). simpl.
    reflexivity.
  }
  assert(isPDT pdparent s1).
  {
    apply partitionsArePDT; assumption.
  }
  assert(isPDT child s1).
  {
    apply childrenArePDT with pdparent; assumption.
  }
  unfold getUsedPaddr. rewrite HgetMappedEq; try(assumption). rewrite HgetMappedEq; try(assumption).
  assert(HgetConfigEq: getConfigPaddr child s = getConfigPaddr child s1).
  {
    rewrite Hs. apply getConfigPaddrEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetConfigEq. apply HVSs1; intuition.
Qed.

Lemma verticalSharingPreservedIsBuiltRec s s0 statesList parentsList buildPart pdentryBuild startaddr endaddr flag
blockBase bentryBase:
verticalSharing s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> DisjointKSEntries s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> childsBlocksPropsInParent s0
-> noDupUsedPaddrList s0
-> wellFormedBlock s0
-> partitionsIsolation s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup buildPart (memory s0) beqAddr = Some (PDT pdentryBuild)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
-> In blockBase (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> verticalSharing s.
Proof.
revert bentryBase. revert blockBase. revert pdentryBuild. revert s0. revert parentsList. revert buildPart.
induction statesList.
- simpl. intros buildPart parentsList s0 _ _ _ HVS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HisBuilt.
  destruct HisBuilt as [_ Hss0Eq]. subst s. intuition.
- simpl. intros buildPart parentsList s0 pdentryBuild blockBase bentryBase HVS HPDTIfPDFlag HmultPDT
      HwellFormedShadow Hstruct Hdisjoint HparentOfPart HisChild HchildBlockProps HnoDup HwellFormedBlock HPI
      HbuildIsPart HlookupBuild HlookupBlockBase HPFlagBase HnoPDFlagBase HblockBaseMapped HstartBase HendBase
      HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
  { rewrite Hs1. simpl. reflexivity. }
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    rewrite Hancestor. specialize(HparentOfPart buildPart pdentry0 HlookupParentsInit). intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupParentsInit. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupParentsInit. trivial.
  }
  assert(HnoPDFlag: false = checkChild blockInParentPartitionAddr s0
                                (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBase startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase HblockIsMapped HblockStart HblockEnd HPFlag HstartTriv HendTriv). intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
      try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HPI pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HPI. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPIA: partitionsIsolation a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HVSA: verticalSharing a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply verticalSharingPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    rewrite HcurrPartEq in HpropsOr.
    assert(HgetPartMultEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. unfold multiplexerIsPDT in HmultPDT.
      apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
           with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
         try(assumption);
         try(unfold CBlockEntry;
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
             simpl; reflexivity).
      - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
      - simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartMultEqs1. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartsEq in HpdAddrIsPart.
  assert(HlookupParentA: exists pdentry2, lookup pdAddr (memory a) beqAddr = Some (PDT pdentry2)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. exists pdentry1. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue.
      exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
               vidtAddr := vidtAddr pdentry1
             |}. reflexivity.
  }
  destruct HlookupParentA as [pdentry2 HlookupParentA].
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HPFlagA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlag. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HnoPDFlagA: false = checkChild blockInParentPartitionAddr a
                                        (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HnoPDFlag.
    assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                          = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
      assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
      {
        rewrite Hs1. simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
      }
      rewrite <-HlookupSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
      - subst a. reflexivity.
      - destruct Ha as [Ha _]. rewrite Ha. simpl.
        destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
          rewrite HlookupAncestorsInit in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite HlookupSh1Eq. assumption.
  }
  assert(HgetMappedEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    rewrite HcurrPartEq in HpropsOr.
    assert(HgetMappedEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite <-HgetMappedEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedEq in HblockIsMapped.
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  apply IHstatesList with pdAddr newPdEntriesList a pdentry2 blockInParentPartitionAddr newBentry; intuition.
Qed.

Lemma kernelDataIsolationPreservedIsBuilt s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
flag basePart blockBase bentryBase:
kernelDataIsolation s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> false = checkChild blockInParentPartitionAddr s0 (CPaddr (blockInParentPartitionAddr + sh1offset))
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> bentryPFlag blockInParentPartitionAddr true s0
-> In blockInParentPartitionAddr (getMappedBlocks pdAddr s0)
-> In basePart (getPartitions multiplexer s0)
-> In blockBase (getAccessibleMappedBlocks basePart s0)
-> lookup blockBase (memory s0) beqAddr = Some(BE bentryBase)
-> startAddr (blockrange bentryBase) = startAddr (blockrange bentry)
-> endAddr (blockrange bentryBase) = endAddr (blockrange bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> kernelDataIsolation s.
Proof.
intros HKDI HPDTIfPDFlag HmultPDT HwellFormed Hstruct HnoDup Hdisjoint HnoPDFlag HlookupPdAddr HlookupBlock HPFlag
    HblockMapped HbaseIsPart HblockAccessBase HlookupBlockBase HstartEq HendEq HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(HKDIs1: kernelDataIsolation s1).
{
  unfold kernelDataIsolation in *. intros part1 part2 Hpart1IsPart Hpart2IsPart addr HaddrAccMapped.
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  {
    unfold isBE. rewrite HlookupBlock. trivial.
  }
  assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
  {
    rewrite Hs1.
    apply getPartitionsEqBEPDflagFalse with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
        try(assumption).
    apply lookupSh1EntryAddr with bentry; assumption.
    unfold sh1entryPDflag. unfold checkChild in HnoPDFlag. rewrite HlookupBlock in HnoPDFlag.
    specialize(HwellFormed blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormed.
    destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr);
        try(congruence). destruct v; try(congruence).
  }
  rewrite HgetPartEq in *.
  assert(Hpart1PDT: isPDT part1 s0).
  {
    apply partitionsArePDT; assumption.
  }
  assert(Hpart2PDT: isPDT part2 s0).
  {
    apply partitionsArePDT; assumption.
  }
  assert(HgetConfigEq: getConfigPaddr part2 s1 = getConfigPaddr part2 s0).
  {
    rewrite Hs1. apply getConfigPaddrEqBE; assumption.
  }
  rewrite HgetConfigEq.
  destruct (eqb flag (accessible bentry)) eqn:HbeqFlagAcc.
  - (* flag = accessible bentry *)
    assert(HgetAccMappedEq: getAccessibleMappedPaddr part1 s1 = getAccessibleMappedPaddr part1 s0).
    {
      rewrite Hs1. apply getAccessibleMappedPaddrEqBEPresentAccessibleNoChange with bentry;
            try(assumption);
            try(unfold CBlockEntry;
                destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                simpl; try(reflexivity)).
      apply eqb_prop in HbeqFlagAcc. assumption.
    }
    rewrite HgetAccMappedEq in HaddrAccMapped. unfold Lib.disjoint in HKDI. apply HKDI with part1; assumption.
  - (* flag <> accessible bentry *)
    apply eqb_false_iff in HbeqFlagAcc. destruct (beqAddr part1 pdAddr) eqn:HbeqPart1Parent.
    + (* part1 = pdAddr *)
      rewrite <-DTL.beqAddrTrue in HbeqPart1Parent. subst part1. destruct flag.
      * (* flag = true *)
        rewrite Hs1 in HaddrAccMapped.
        assert(HaddrMappedEquiv: In addr (getAccessibleMappedPaddr pdAddr s1) <->
           In addr (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry)) ++
              getAccessibleMappedPaddr pdAddr s0)).
        {
          rewrite Hs1. apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence;
                try(assumption);
            try(unfold CBlockEntry;
                destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                simpl; try(reflexivity)).
            unfold bentryPFlag in HPFlag. rewrite HlookupBlock in HPFlag. intuition.
            assumption.
            unfold getMappedBlocks in HblockMapped. apply InFilterPresentInList in HblockMapped. assumption.
        }
        rewrite Hs1 in HaddrMappedEquiv. apply HaddrMappedEquiv in HaddrAccMapped.
        apply in_app_or in HaddrAccMapped. destruct HaddrAccMapped as [HaddrNotMappeds0 | HaddrMappeds0].
        -- assert(HaddrIsAcc: In addr (getAccessibleMappedPaddr basePart s0)).
           {
             apply addrInAccessibleBlockIsAccessibleMapped with blockBase.
             ++ simpl. rewrite HlookupBlockBase. rewrite app_nil_r. rewrite HstartEq. rewrite HendEq.
                assumption.
             ++ unfold getAccessibleMappedBlocks in HblockAccessBase.
                destruct (lookup basePart (memory s0) beqAddr); try(exfalso; simpl in *; congruence).
                destruct v; try(exfalso; simpl in *; congruence).
                apply InFilterAccessibleInList in HblockAccessBase. assumption.
             ++ unfold bentryAFlag. unfold getAccessibleMappedBlocks in HblockAccessBase.
                rewrite HlookupBlockBase.
                destruct (lookup basePart (memory s0) beqAddr); try(exfalso; simpl in *; congruence).
                destruct v; try(exfalso; simpl in *; congruence). induction (getMappedBlocks basePart s0).
                ** simpl in HblockAccessBase. exfalso; congruence.
                ** simpl in HblockAccessBase.
                   destruct (lookup a (memory s0) beqAddr) eqn:HlookupA; try(apply IHl; assumption).
                   destruct v; try(apply IHl; assumption).
                   destruct (accessible b) eqn:Haccess; try(apply IHl; assumption). simpl in HblockAccessBase.
                   destruct HblockAccessBase as [HblocksEq | Hrec]; try(apply IHl; assumption).
                   subst a. rewrite HlookupBlockBase in HlookupA. injection HlookupA as HbentriesEq. subst b.
                   intuition.
           }
           unfold Lib.disjoint in HKDI. apply HKDI with basePart; assumption.
        -- unfold Lib.disjoint in HKDI. apply HKDI with pdAddr; assumption.
      * (* flag = false *)
        assert(HaddrAccMappeds0: In addr (getAccessibleMappedPaddr pdAddr s0)).
        {
          rewrite Hs1 in HaddrAccMapped.
          apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleFalseChangeInclusion with
                blockInParentPartitionAddr
                (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) false
                  (blockindex bentry) (blockrange bentry))
                bentry; try(assumption);
              try(unfold CBlockEntry;
                  destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                  simpl; try(reflexivity)).
            unfold bentryPFlag in HPFlag. rewrite HlookupBlock in HPFlag. intuition.
            assumption.
            unfold getMappedBlocks in HblockMapped. apply InFilterPresentInList in HblockMapped. assumption.
        }
        unfold Lib.disjoint in HKDI. apply HKDI with pdAddr; assumption.
    + (* part1 <> pdAddr *)
      rewrite <-beqAddrFalse in HbeqPart1Parent.
      assert(HgetAccMappedEq: getAccessibleMappedPaddr part1 s1 = getAccessibleMappedPaddr part1 s0).
      {
        rewrite Hs1. apply getAccessibleMappedPaddrEqBENotInPart; try(assumption).
        unfold getMappedBlocks in HblockMapped. apply InFilterPresentInList in HblockMapped.
        assert(HparentPDT: isPDT pdAddr s0).
        { unfold isPDT. rewrite HlookupPdAddr. trivial. }
        specialize(Hdisjoint part1 pdAddr Hpart1PDT HparentPDT HbeqPart1Parent). intro Hcontra.
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        specialize(Hdisjoint blockInParentPartitionAddr Hcontra). congruence.
      }
      rewrite HgetAccMappedEq in HaddrAccMapped. unfold Lib.disjoint in HKDI. apply HKDI with part1; assumption.
}
assert(Hstructs1: StructurePointerIsKS s1).
{
  apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU
      flag; intuition.
}
assert(HPDTIfPDFlags1: PDTIfPDFlag s1).
{
  apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag;
      intuition.
}
assert(HmultPDTs1: multiplexerIsPDT s1).
{
  apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag;
      intuition.
}
destruct HpropsOr as [Hss1Eq | Hs].
+ (* s = s1 *)
  rewrite Hss1Eq. assumption.
+ (* s <> s1 *)
  unfold kernelDataIsolation in *. intros part1 part2 Hpart1IsPart Hpart2IsPart.
  assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
  {
    rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
      rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
  }
  assert(HgetPartEq: getPartitions multiplexer s = getPartitions multiplexer s1).
  {
    rewrite Hs. apply getPartitionsEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetPartEq in *.
  assert(isPDT part2 s1).
  { apply partitionsArePDT; assumption. }
  assert(HgetConfigEq: getConfigPaddr part2 s = getConfigPaddr part2 s1).
  {
    rewrite Hs. apply getConfigPaddrEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetConfigEq.
  assert(HgetAccMappedEq: getAccessibleMappedPaddr part1 s = getAccessibleMappedPaddr part1 s1).
  {
    rewrite Hs. apply getAccessibleMappedPaddrEqPDT with pdentry1; try(assumption). simpl. reflexivity.
  }
  rewrite HgetAccMappedEq. apply HKDIs1; assumption.
Qed.

Lemma kernelDataIsolationPreservedIsBuiltRec s s0 statesList parentsList buildPart basePart pdentryBuild startaddr
endaddr flag blockBuild bentryBuild blockBase bentryBase:
kernelDataIsolation s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> DisjointKSEntries s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> childsBlocksPropsInParent s0
-> noDupUsedPaddrList s0
-> wellFormedBlock s0
-> noDupMappedBlocksList s0
-> partitionsIsolation s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup buildPart (memory s0) beqAddr = Some (PDT pdentryBuild)
-> lookup blockBuild (memory s0) beqAddr = Some (BE bentryBuild)
-> bentryPFlag blockBuild true s0
-> false = checkChild blockBuild s0 (CPaddr (blockBuild + sh1offset))
-> In blockBuild (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBuild startaddr s0
-> bentryEndAddr blockBuild endaddr s0
-> In basePart (getPartitions multiplexer s0)
-> In blockBase (getAccessibleMappedBlocks basePart s0)
-> lookup blockBase (memory s0) beqAddr = Some(BE bentryBase)
-> startAddr (blockrange bentryBase) = startAddr (blockrange bentryBuild)
-> endAddr (blockrange bentryBase) = endAddr (blockrange bentryBuild)
-> (forall parentsList, isParentsList s0 parentsList buildPart
                        -> ~ In basePart parentsList)
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> kernelDataIsolation s.
Proof.
revert bentryBase. revert bentryBuild. revert blockBuild. revert pdentryBuild. revert s0. revert parentsList.
revert buildPart. induction statesList.
- simpl. intros buildPart parentsList s0 _ _ _ _ HKDI _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      HisBuilt.
  destruct HisBuilt as [_ Hss0Eq]. subst s. intuition.
- simpl. intros buildPart parentsList s0 pdentryBuild blockBuild bentryBuild bentryBase HKDI HPDTIfPDFlag
      HmultPDT HwellFormedShadow Hstruct Hdisjoint HparentOfPart HisChild HchildBlockProps HnoDup
      HwellFormedBlock HnoDupMapped HPI HbuildIsPart HlookupBuild HlookupBlockBuild HPFlagBuild HnoPDFlagBuild
      HblockBuildMapped HstartBuild HendBuild HbaseIsPart HblockBaseMapped HlookupBlockBase HstartBase HendBase
      HbaseNotAncestor HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
  { rewrite Hs1. simpl. reflexivity. }
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    rewrite Hancestor. specialize(HparentOfPart buildPart pdentry0 HlookupParentsInit). intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupParentsInit. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupParentsInit. trivial.
  }
  assert(HnoPDFlag: false = checkChild blockInParentPartitionAddr s0
                                (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBuild startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBuildMapped HstartBuild HendBuild
               HPFlagBuild HblockIsMapped HblockStart HblockEnd HPFlag HstartTriv HendTriv). intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
      try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBuild startaddr endaddr HPFlagBuild HstartBuild HendBuild).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBuild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBuild))
                                                                     (endAddr (blockrange bentryBuild)))).
      {
        unfold bentryStartAddr in HstartBuild. unfold bentryEndAddr in HendBuild.
        rewrite HlookupBlockBuild in *. rewrite <-HstartBuild. rewrite <-HendBuild.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBuild) eqn:HbeqBlockChildBlockBuild.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBuild. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBuild in *. rewrite <-HstartChild in HstartBuild.
          rewrite <-HendChild in HendBuild. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBuild.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBuildMapped as [Ha0IsBuild | HblockBuildMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBuild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBuild).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBuild. assumption. simpl.
                rewrite HlookupBlockBuild. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBuild; try(assumption). simpl. rewrite HlookupBlockBuild.
          rewrite app_nil_r. assumption.
        }
        specialize(HPI pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HPI. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply noDupMappedBlocksListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPIA: partitionsIsolation a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HstartEnd: startAddr (blockrange bentryBase) = startAddr (blockrange bentry)
                    /\ endAddr (blockrange bentryBase) = endAddr (blockrange bentry)).
  {
    rewrite HstartBase. rewrite HendBase. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    rewrite HlookupBlocks0 in *. rewrite HlookupBlockBuild in *. subst startaddr. subst endaddr. intuition.
  }
  destruct HstartEnd as [HstartBaseEq HendBaseEq].
  assert(HKDIA: kernelDataIsolation a).
  {
    rewrite HcurrPartEq in HpropsOr.
    apply kernelDataIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag basePart blockBase
        bentryBase; intuition.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    rewrite HcurrPartEq in HpropsOr.
    assert(HgetPartMultEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. unfold multiplexerIsPDT in HmultPDT.
      apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
           with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
         try(assumption);
         try(unfold CBlockEntry;
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
             simpl; reflexivity).
      - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
      - simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartMultEqs1. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartsEq in *.
  assert(HlookupParentA: exists pdentry2, lookup pdAddr (memory a) beqAddr = Some (PDT pdentry2)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. exists pdentry1. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue.
      exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
               vidtAddr := vidtAddr pdentry1
             |}. reflexivity.
  }
  destruct HlookupParentA as [pdentry2 HlookupParentA].
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HPFlagA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlag. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HnoPDFlagA: false = checkChild blockInParentPartitionAddr a
                                        (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HnoPDFlag.
    assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                          = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
      assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
      {
        rewrite Hs1. simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
      }
      rewrite <-HlookupSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
      - subst a. reflexivity.
      - destruct Ha as [Ha _]. rewrite Ha. simpl.
        destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
          rewrite HlookupAncestorsInit in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite HlookupSh1Eq. assumption.
  }
  assert(HgetMappedEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    rewrite HcurrPartEq in HpropsOr.
    assert(HgetMappedEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite <-HgetMappedEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HlookupBlockBaseA: exists bentryBaseBis, lookup blockBase (memory a) beqAddr = Some (BE bentryBaseBis)
                                                  /\ blockrange bentryBaseBis = blockrange bentryBase).
  {
    assert(HlookupBlockBases1: exists bentryBaseBis, lookup blockBase (memory s1) beqAddr
                                                          = Some (BE bentryBaseBis)
                                                      /\ blockrange bentryBaseBis = blockrange bentryBase).
    {
      rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr blockBase) eqn:HbeqBlockBlockBase.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockBlockBase. subst blockInParentPartitionAddr.
        rewrite HlookupBlockBase in HlookupBlocks0. injection HlookupBlocks0 as HbentriesEq. subst bentryBase.
        exists newBentry. rewrite HnewB. split. reflexivity. unfold CBlockEntry.
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
      - rewrite <-beqAddrFalse in HbeqBlockBlockBase. exists bentryBase. rewrite removeDupIdentity; intuition.
    }
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl. destruct (beqAddr pdAddr blockBase) eqn:HbeqParentBlockBase.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockBase. subst blockBase.
        rewrite HlookupAncestorsInit in HlookupBlockBase. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockBase. rewrite removeDupIdentity; intuition.
  }
  destruct HlookupBlockBaseA as [bentryBaseBis (HlookupBlockBaseA & HblockrangeBase)].
  rewrite <-HblockrangeBase in *.
  assert(HstartEnd: startAddr (blockrange bentryBaseBis) = startAddr (blockrange newBentry)
                    /\ endAddr (blockrange bentryBaseBis) = endAddr (blockrange newBentry)).
  {
    rewrite HstartBaseEq. rewrite HendBaseEq. rewrite HnewB. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. intuition.
  }
  assert(HgetAccessBaseEq: getAccessibleMappedBlocks basePart a = getAccessibleMappedBlocks basePart s0).
  {
    assert(HparentIsParentsList: isParentsList s0 [pdAddr] buildPart).
    {
      simpl. rewrite HlookupAncestorsInit. split. assumption. split; trivial. exists pdentry0. intuition.
    }
    specialize(HbaseNotAncestor [pdAddr] HparentIsParentsList). simpl in HbaseNotAncestor.
    apply Classical_Prop.not_or_and in HbaseNotAncestor. destruct HbaseNotAncestor as [HbaseNotAncestor _].
    rewrite HgetPartsEq in HbaseIsPart.
    assert(HbaseIsPDT: isPDT basePart s0) by (apply partitionsArePDT; assumption).
    assert(~ In blockInParentPartitionAddr (filterOptionPaddr (getKSEntries basePart s0))).
    {
      unfold getMappedBlocks in HblockIsMapped. apply InFilterPresentInList in HblockIsMapped.
      assert(HpdAddrIsPDT: isPDT pdAddr s0) by (unfold isPDT; rewrite HlookupAncestorsInit; trivial).
      specialize(Hdisjoint pdAddr basePart HpdAddrIsPDT HbaseIsPDT HbaseNotAncestor).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      specialize(Hdisjoint blockInParentPartitionAddr HblockIsMapped). assumption.
    }
    assert(HgetAccessBaseEq: getAccessibleMappedBlocks basePart s1 = getAccessibleMappedBlocks basePart s0).
    {
      rewrite Hs1. apply getAccessibleMappedBlocksEqBENotInPart; assumption.
    }
    rewrite <-HgetAccessBaseEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. rewrite HcurrPartEq. apply getAccessibleMappedBlocksEqPDT with pdentry1.
      assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetAccessBaseEq in HblockBaseMapped. rewrite <-HgetMappedEq in HblockIsMapped.
  assert(HbaseNotAncestorA: forall parentsList, isParentsList a parentsList buildPart
                                                -> ~ In basePart parentsList).
  {
    intros parentsListBis HparentsListBis. rewrite HcurrPartEq in HpropsOr.
    assert(HparentsListBiss1: isParentsList s1 parentsListBis buildPart).
    {
      destruct HpropsOr as [Has1Eq | Ha].
      - subst a. assumption.
      - destruct Ha as [Ha _].
        apply isParentsListEqPDTSameParent with pdAddr
                {|
                  structure := structure pdentry1;
                  firstfreeslot := firstfreeslot pdentry1;
                  nbfreeslots := nbfreeslots pdentry1;
                  nbprepare := nbprepare pdentry1;
                  parent := parent pdentry1;
                  MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                  vidtAddr := vidtAddr pdentry1
                |} a; try(assumption).
        specialize(HparentOfPart buildPart pdentry0 HlookupParentsInit). rewrite <-Hancestor in *.
        assert(HbeqPdAddrBuild: beqAddr pdAddr buildPart = false) by (rewrite <-beqAddrFalse; intuition).
        exists pdentry0. exists pdentry0. exists pdentry1. simpl. intuition.
        + rewrite Ha. simpl. rewrite HbeqPdAddrBuild. rewrite removeDupIdentity; intuition.
        + apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
              bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
    }
    assert(HparentsListBiss0: isParentsList s0 parentsListBis buildPart).
    {
      rewrite Hs1 in HparentsListBiss1.
      apply isParentsListEqBE with blockInParentPartitionAddr (CBlockEntry (read bentry) (write bentry)
                (exec bentry) (present bentry) flag (blockindex bentry) (blockrange bentry)) bentry;
          try(assumption). exists pdentry0. assumption.
    }
    specialize(HbaseNotAncestor parentsListBis HparentsListBiss0). assumption.
  }
  assert(forall parentsList, isParentsList a parentsList pdAddr -> ~ In basePart parentsList).
  {
    intros parentsListBis HparentsListBis.
    assert(HparentsListExtended: isParentsList a (pdAddr::parentsListBis) buildPart).
    {
      simpl. rewrite HlookupParentA. split. assumption. split; try(assumption). exists pdentry0.
      destruct HpropsOr as [Has1Eq | Ha].
      - subst a. intuition.
      - destruct Ha as [Ha _]. rewrite Ha. simpl.
        specialize(HparentOfPart buildPart pdentry0 HlookupParentsInit). rewrite <-Hancestor in *.
        assert(HbeqPdAddrBuild: beqAddr pdAddr buildPart = false) by (rewrite <-beqAddrFalse; intuition).
        rewrite HbeqPdAddrBuild. rewrite removeDupIdentity; intuition.
    }
    specialize(HbaseNotAncestorA (pdAddr::parentsListBis) HparentsListExtended). simpl in HbaseNotAncestorA.
    apply Classical_Prop.not_or_and in HbaseNotAncestorA. intuition.
  }
  apply IHstatesList with pdAddr newPdEntriesList a pdentry2 blockInParentPartitionAddr newBentry bentryBaseBis;
      intuition.
Qed.

(* General properties needing the isolation properties to be proven *)

Lemma baseBlockAccessibleImpliesNoPDWithIsBuilt s0 s statesList parentsList startaddr endaddr buildPart flag
blockBase bentryBase pdentryBuild:
childsBlocksPropsInParent s0
-> DisjointKSEntries s0
-> StructurePointerIsKS s0
-> wellFormedFstShadowIfBlockEntry s0
-> noDupUsedPaddrList s0
-> wellFormedBlock s0
-> AccessibleNoPDFlag s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> isChild s0
-> parentOfPartitionIsPartition s0
-> partitionsIsolation s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup buildPart (memory s0) beqAddr = Some (PDT pdentryBuild)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
-> In blockBase (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> exists partition,
      partition = last parentsList buildPart
      /\ forall blockPart bentryPart,
            lookup blockPart (memory s) beqAddr = Some (BE bentryPart)
            -> bentryPFlag blockPart true s
            -> In blockPart (getMappedBlocks partition s)
            -> bentryStartAddr blockPart startaddr s
            -> bentryEndAddr blockPart endaddr s
            -> false = checkChild blockPart s (CPaddr (blockPart + sh1offset)).
Proof.
revert bentryBase. revert blockBase. revert buildPart. revert pdentryBuild. revert parentsList. revert s0.
induction statesList.
- (* statesList = [] *)
  intros s0 parentsList pdentryBuild buildPart blockBase bentryBase HchildBlockProps Hdisjoint Hstruct
      HwellFormedShadow HnoDup HwellFormedBlock HaccessPD HPDTIfPDFlag HmultPDT HisChild HparentIsPart
      HpartIsolation HbuildIsPart HlookupBuild HlookupBlockBase HPFlagBase (*HAFlagBase*) HcheckChilcBase
      HblockBaseMapped HstartBase HendBase HisBuilt. simpl in *.
  destruct HisBuilt as [Hparents Hss0Eq]. subst s. subst parentsList. simpl. exists buildPart. split.
  reflexivity. intros blockPart bentryPart HlookupBlockPart HPFlagPart HblockPartMapped HstartPart HendPart.
  assert(HblocksEq: blockPart = blockBase).
  {
    apply uniqueBlockMapped with startaddr buildPart s0; try(assumption). unfold isPDT. rewrite HlookupBuild.
    trivial.
  }
  subst blockPart. assumption.
- (* statesList = a::l *)
  intros s0 parentsList pdentryBuild buildPart blockBase bentryBase HchildBlockProps Hdisjoint Hstruct
      HwellFormedShadow HnoDup HwellFormedBlock HaccessPD HPDTIfPDFlag HmultPDT HisChild HparentIsPart
      HpartIsolation HbuildIsPart HlookupBuild HlookupBlockBase HPFlagBase (*HAFlagBase*) HcheckChilcBase
      HblockBaseMapped HstartBase HendBase HisBuilt. simpl in *.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HcurrPartsEq: currentPartition s0 = currentPartition s1).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  rewrite HcurrPartsEq in HpropsOr. 
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    specialize(HparentIsPart buildPart pdentry0 HlookupParentsInit).
    destruct HparentIsPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite Hancestor. intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupParentsInit. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupBuild. trivial.
  }
  assert(HcheckChild: false = checkChild blockInParentPartitionAddr s0
                                  (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBase startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase HblockIsMapped HblockStart HblockEnd HPFlag HstartTriv HendTriv). intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HstructDisjoint: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
        (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  destruct HstructDisjoint as (HstructA & HdisjointA & Hstructs1).
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
        (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
        (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HaccessPDA: AccessibleNoPDFlag a).
  {
    apply AccessibleNoPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentIsPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite HlookupParentsInit in HlookupBuild. injection HlookupBuild as HpdentriesEq. subst pdentry0.
  assert(HlookupAncestorA: exists pdentry1A, lookup pdAddr (memory a) beqAddr = Some (PDT pdentry1A)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. exists pdentry1. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue.
      exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
               vidtAddr := vidtAddr pdentry1
             |}. reflexivity.
  }
  destruct HlookupAncestorA as [pdentry1A HlookupAncestorA].
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HlookupAncestorsInit. injection HlookupAncestorsInit as Hcontra.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HPFlagA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlag. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  { unfold isBE. rewrite HlookupBlocks0. trivial. }
  assert(HcheckChildA: false = checkChild blockInParentPartitionAddr a
                                  (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HcheckChild.
    specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
    assert(Heqs1: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                  = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr).
    {
      destruct HpropsOr as [Has1Eq | Ha].
      - subst a. reflexivity.
      - destruct Ha as [Ha _]. rewrite Ha. simpl.
        destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
          rewrite HlookupAncestorsInit in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite Heqs1. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
        eqn:HbeqBlockBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
      rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HgetMappedEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(Heqs1: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s1).
    {
      destruct HpropsOr as [Has1Eq | Ha].
      - subst a. reflexivity.
      - destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1; try(assumption).
        simpl. reflexivity.
    }
    rewrite Heqs1. rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. simpl.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. reflexivity.
  }
  rewrite <-HgetMappedEq in HblockIsMapped.
  assert(HblockStartA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockEndA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartMultEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. unfold multiplexerIsPDT in HmultPDT.
      apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
           with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
         try(assumption);
         try(unfold CBlockEntry;
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
             simpl; reflexivity).
      - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
      - simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartMultEqs1. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartEq in HpdAddrIsPart.
  specialize(IHstatesList a newPdEntriesList pdentry1A pdAddr blockInParentPartitionAddr newBentry
             HchildBlockPropsA HdisjointA HstructA HwellFormedShadowA HnoDupA HwellFormedBlockA HaccessPDA
             HPDTIfPDFlagA HmultPDTA HisChildA HparentIsPartA HpartIsolationA HpdAddrIsPart HlookupAncestorA
             HlookupBlockA HPFlagA HcheckChildA HblockIsMapped HblockStartA HblockEndA HisBuilt).
  destruct IHstatesList as [lastPart (HlastPart & IHstatesList)]. exists lastPart. split. rewrite HparentsList.
  apply lastRecInc. assumption. assumption.
Qed.

Lemma listWithIsBuiltIsParentsList s0 s statesList parentsList pdbasepartition startaddr endaddr flag blockBase
bentryBase:
parentOfPartitionIsPartition s0
-> nullAddrExists s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> isChild s0
-> childsBlocksPropsInParent s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> noDupUsedPaddrList s0
-> partitionsIsolation s0
-> In pdbasepartition (getPartitions multiplexer s0)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
-> In blockBase (getMappedBlocks pdbasepartition s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition startaddr endaddr flag
-> isParentsList s parentsList pdbasepartition.
Proof.
revert bentryBase. revert blockBase. revert pdbasepartition. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList pdbasepartition blockBase bentryBase HparentOfPart HnullExists _ _ _ _ _ _ _ _ _ _ _ _ _
      _ _ _ _ HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [HparentsList _]. subst parentsList. simpl. trivial.
- (* statesList = a::l *)
  intros s0 parentsList pdbasepartition blockBase bentryBase HparentOfPart HnullExists HmultPDT HPDTIfPDFlag
      HwellFormedShadow Hstruct HisChild HchildBlockProps Hdisjoint HwellFormedBlock HnoDup HpartIsolation
      HbaseIsPart HlookupBlockBase HPFlagBase HnoPDFlagBase HblockBaseMapped HstartBase HendBase HisBuilt.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a :: statesList) parentsList pdbasepartition
             startaddr endaddr flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  rewrite HparentsList in *. simpl.
  assert(HparentIsPDT: isPDT pdAddr s).
  {
    apply stablePDTIsBuilt with (a::statesList) s0 (pdAddr::newPdEntriesList) pdbasepartition startaddr endaddr
          flag; try(assumption).
    + unfold isPDT. rewrite HlookupBases0. trivial.
    + unfold isPDT. rewrite HlookupPdAddrs0. trivial.
  }
  unfold isPDT in HparentIsPDT. destruct (lookup pdAddr (memory s) beqAddr) eqn:HlookupParents; try(congruence).
  destruct v; try(congruence).
  split. intro Hcontra. specialize(HparentOfPart pdbasepartition pdentryBase HlookupBases0).
  destruct HparentOfPart as [HparentIsPart (HparentOfRoot & HparentNotPart)].
  specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *. rewrite HpdAddr in *.
  unfold nullAddrExists in HnullExists. unfold isPADDR in HnullExists. rewrite HlookupPdAddrs0 in HnullExists.
  congruence.
  split. rewrite HpdAddr.
  apply stablePDTParentIsBuilt with (a::statesList) s0 (pdAddr::newPdEntriesList) pdbasepartition startaddr
        endaddr flag; try(assumption). unfold isPDT. rewrite HlookupBases0. trivial.
  assert(HcurrPartsEq: currentPartition s0 = currentPartition s1).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  rewrite HcurrPartsEq in HpropsOr.
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    specialize(HparentOfPart pdbasepartition pdentryBase HlookupBases0).
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite HpdAddr. intuition.
  }
  assert(HbuildPartIsChild: In pdbasepartition (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupBases0. assumption.
  }
  assert(HbuildIsPDT: isPDT pdbasepartition s0).
  {
    unfold isPDT. rewrite HlookupBases0. trivial.
  }
  assert(HcheckChild: false = checkChild blockInParentPartitionAddr s0
                                  (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps pdbasepartition pdAddr blockBase startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase HblockMappedPdAddr HstartBlock HendBlock HPFlagBlock HstartTriv HendTriv). intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child pdbasepartition) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup pdbasepartition HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks pdbasepartition s0).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr pdbasepartition s0)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child pdbasepartition HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnullExistsA: nullAddrExists a).
  {
    assert(HnullExistss1: nullAddrExists s1).
    {
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr nullAddr) eqn:HbeqBlockNull.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockNull. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HnullExists. congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockNull. rewrite removeDupIdentity; intuition.
    }
    unfold nullAddrExists in *. unfold isPADDR in *. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr nullAddr) eqn:HbeqParentNull.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentNull. rewrite HbeqParentNull in *.
        rewrite HlookupPdAddrs1 in HnullExistss1. congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentNull. rewrite removeDupIdentity; intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr
      blockInParentPartitionAddr bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU)
      flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HlookupPdAddrs0. injection HlookupPdAddrs0 as HentriesEq.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HPFlagBlockA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlagBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  { unfold isBE. rewrite HlookupBlocks0. trivial. }
  assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
  {
    specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
    assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                              = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupBlockSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
        rewrite HlookupPdAddrs0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HcheckChildA: false = checkChild blockInParentPartitionAddr a
                                    (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HcheckChild.
    rewrite HlookupBlockSh1Eq. assumption.
  }
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HstartBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HendBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HgetMappedBlocksEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedBlocksEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
    }
    rewrite <-HgetMappedBlocksEq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentryPdAddr. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedBlocksEq in HblockMappedPdAddr.
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
            (CPaddr (blockInParentPartitionAddr + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption);
          try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
              try(lia); simpl; try(reflexivity)).
      apply lookupSh1EntryAddr with bentry. assumption.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentryPdAddr; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartEq in HpdAddrIsPart.
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HparentOfPartA
             HnullExistsA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HisChildA HchildBlockPropsA
             HdisjointA HwellFormedBlockA HnoDupA HpartIsolationA HpdAddrIsPart HlookupBlockA HPFlagBlockA
             HcheckChildA HblockMappedPdAddr HstartBlockA HendBlockA HisBuilt).
  assumption.
Qed.

Lemma partitionTreeIsTreePreservedIsBuiltRec s0 s statesList parentsList pdbasepartition startaddr endaddr flag
blockBase bentryBase:
partitionTreeIsTree s0
-> parentOfPartitionIsPartition s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> isChild s0
-> childsBlocksPropsInParent s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> noDupUsedPaddrList s0
-> partitionsIsolation s0
-> In pdbasepartition (getPartitions multiplexer s0)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
-> In blockBase (getMappedBlocks pdbasepartition s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition startaddr endaddr flag
-> partitionTreeIsTree s.
Proof.
revert bentryBase. revert blockBase. revert pdbasepartition. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList pdbasepartition blockBase bentryBase Htree _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [_ HparentsList]. subst s. assumption.
- (* statesList = a::l *)
  intros s0 parentsList pdbasepartition blockBase bentryBase Htree HparentOfPart HmultPDT HPDTIfPDFlag
      HwellFormedShadow Hstruct HisChild HchildBlockProps Hdisjoint HwellFormedBlock HnoDup HpartIsolation
      HbaseIsPart HlookupBlockBase HPFlagBase HnoPDFlagBase HblockBaseMapped HstartBase HendBase HisBuilt.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a :: statesList) parentsList pdbasepartition
             startaddr endaddr flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HcurrPartsEq: currentPartition s0 = currentPartition s1).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  rewrite HcurrPartsEq in HpropsOr.
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    specialize(HparentOfPart pdbasepartition pdentryBase HlookupBases0).
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite HpdAddr. intuition.
  }
  assert(HbuildPartIsChild: In pdbasepartition (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupBases0. assumption.
  }
  assert(HbuildIsPDT: isPDT pdbasepartition s0).
  {
    unfold isPDT. rewrite HlookupBases0. trivial.
  }
  assert(HcheckChild: false = checkChild blockInParentPartitionAddr s0
                                  (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps pdbasepartition pdAddr blockBase startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase HblockMappedPdAddr HstartBlock HendBlock HPFlagBlock HstartTriv HendTriv). intuition.
  }
  assert(HtreeA: partitionTreeIsTree a).
  {
    apply partitionTreeIsTreePreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
      intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr
      blockInParentPartitionAddr bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU)
      flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child pdbasepartition) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup pdbasepartition HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks pdbasepartition s0).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr pdbasepartition s0)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child pdbasepartition HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HlookupPdAddrs0. injection HlookupPdAddrs0 as HentriesEq.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HPFlagBlockA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlagBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  { unfold isBE. rewrite HlookupBlocks0. trivial. }
  assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
  {
    specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
    assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                              = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupBlockSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
        rewrite HlookupPdAddrs0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HcheckChildA: false = checkChild blockInParentPartitionAddr a
                                    (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HcheckChild.
    rewrite HlookupBlockSh1Eq. assumption.
  }
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HstartBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HendBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HgetMappedBlocksEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedBlocksEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
    }
    rewrite <-HgetMappedBlocksEq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentryPdAddr. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedBlocksEq in HblockMappedPdAddr.
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
            (CPaddr (blockInParentPartitionAddr + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption);
          try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
              try(lia); simpl; try(reflexivity)).
      apply lookupSh1EntryAddr with bentry. assumption.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentryPdAddr; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartEq in HpdAddrIsPart.
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HtreeA HparentOfPartA
             HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HisChildA HchildBlockPropsA HdisjointA
             HwellFormedBlockA HnoDupA HpartIsolationA HpdAddrIsPart HlookupBlockA HPFlagBlockA HcheckChildA
             HblockMappedPdAddr HstartBlockA HendBlockA HisBuilt).
  assumption.
Qed.

Lemma parentOfPartitionIsPartitionPreservedIsBuiltRec s s0 statesList parentsList pdbasepartition startaddr
endaddr flag blockBase bentryBase:
parentOfPartitionIsPartition s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> isChild s0
-> childsBlocksPropsInParent s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> noDupUsedPaddrList s0
-> partitionsIsolation s0
-> In pdbasepartition (getPartitions multiplexer s0)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
-> In blockBase (getMappedBlocks pdbasepartition s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition startaddr endaddr flag
-> parentOfPartitionIsPartition s.
Proof.
revert bentryBase. revert blockBase. revert pdbasepartition. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList pdbasepartition blockBase bentryBase HparentOfPart _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [_ HparentsList]. subst s. assumption.
- (* statesList = a::l *)
  intros s0 parentsList pdbasepartition blockBase bentryBase HparentOfPart HmultPDT HPDTIfPDFlag
      HwellFormedShadow Hstruct HisChild HchildBlockProps Hdisjoint HwellFormedBlock HnoDup HpartIsolation
      HbaseIsPart HlookupBlockBase HPFlagBase HnoPDFlagBase HblockBaseMapped HstartBase HendBase HisBuilt.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a :: statesList) parentsList pdbasepartition
             startaddr endaddr flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HcurrPartsEq: currentPartition s0 = currentPartition s1).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  rewrite HcurrPartsEq in HpropsOr.
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    specialize(HparentOfPart pdbasepartition pdentryBase HlookupBases0).
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite HpdAddr. intuition.
  }
  assert(HbuildPartIsChild: In pdbasepartition (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupBases0. assumption.
  }
  assert(HbuildIsPDT: isPDT pdbasepartition s0).
  {
    unfold isPDT. rewrite HlookupBases0. trivial.
  }
  assert(HcheckChild: false = checkChild blockInParentPartitionAddr s0
                                  (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps pdbasepartition pdAddr blockBase startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase HblockMappedPdAddr HstartBlock HendBlock HPFlagBlock HstartTriv HendTriv). intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr
      blockInParentPartitionAddr bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU)
      flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child pdbasepartition) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup pdbasepartition HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks pdbasepartition s0).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr pdbasepartition s0)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child pdbasepartition HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HlookupPdAddrs0. injection HlookupPdAddrs0 as HentriesEq.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HPFlagBlockA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlagBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  { unfold isBE. rewrite HlookupBlocks0. trivial. }
  assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
  {
    specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
    assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                              = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupBlockSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
        rewrite HlookupPdAddrs0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HcheckChildA: false = checkChild blockInParentPartitionAddr a
                                    (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HcheckChild.
    rewrite HlookupBlockSh1Eq. assumption.
  }
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HstartBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HendBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HgetMappedBlocksEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedBlocksEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
    }
    rewrite <-HgetMappedBlocksEq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentryPdAddr. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedBlocksEq in HblockMappedPdAddr.
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
            (CPaddr (blockInParentPartitionAddr + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption);
          try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
              try(lia); simpl; try(reflexivity)).
      apply lookupSh1EntryAddr with bentry. assumption.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentryPdAddr; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartEq in HpdAddrIsPart.
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HparentOfPartA
             HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HisChildA HchildBlockPropsA HdisjointA
             HwellFormedBlockA HnoDupA HpartIsolationA HpdAddrIsPart HlookupBlockA HPFlagBlockA HcheckChildA
             HblockMappedPdAddr HstartBlockA HendBlockA HisBuilt).
  assumption.
Qed.

Lemma isBuiltFromWriteAccessibleRecRec sInit s0 s1 s statesList parentsList partition pdparent pdbasepartition
startaddr endaddr flag pdentryPart pdentryPdparent pdentryBase blockInParentPartitionAddr bentry newBentry realMPU
blockBase:
parentOfPartitionIsPartition sInit
-> nullAddrExists sInit
-> multiplexerIsPDT sInit
-> PDTIfPDFlag sInit
-> wellFormedFstShadowIfBlockEntry sInit
-> StructurePointerIsKS sInit
-> isChild sInit
-> childsBlocksPropsInParent sInit
-> DisjointKSEntries sInit
-> wellFormedBlock sInit
-> noDupUsedPaddrList sInit
-> partitionTreeIsTree sInit
-> partitionsIsolation sInit
-> isBuiltFromWriteAccessibleRec sInit s0 statesList parentsList pdbasepartition startaddr endaddr flag
-> partition = last parentsList pdbasepartition
-> In pdbasepartition (getPartitions multiplexer sInit)
-> lookup pdbasepartition (memory sInit) beqAddr = Some (PDT pdentryBase)
-> lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase)
-> lookup partition (memory s0) beqAddr = Some(PDT pdentryPart)
-> lookup pdparent (memory sInit) beqAddr = Some(PDT pdentryPdparent)
-> lookup pdparent (memory s0) beqAddr = Some(PDT pdentryPdparent)
-> pdparent = parent pdentryPart
-> partition <> constantRootPartM
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> lookup blockInParentPartitionAddr (memory s1) beqAddr = Some (BE newBentry)
-> bentryPFlag blockInParentPartitionAddr true s0
-> bentryStartAddr blockInParentPartitionAddr startaddr s0
-> bentryEndAddr blockInParentPartitionAddr endaddr s0
-> In blockInParentPartitionAddr (getMappedBlocks pdparent s0)
-> In blockBase (getMappedBlocks pdbasepartition sInit)
-> bentryPFlag blockBase true sInit
-> bentryStartAddr blockBase startaddr sInit
-> bentryEndAddr blockBase endaddr sInit
-> false = checkChild blockBase sInit (CPaddr (blockBase + sh1offset))
-> s1 =
     {|
       currentPartition := currentPartition s0;
       memory :=
         add blockInParentPartitionAddr
           (BE
              (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                 (present bentry) flag (blockindex bentry) (blockrange bentry))) 
           (memory s0) beqAddr
     |}
-> (s = s1 \/
     s =
     {|
       currentPartition := currentPartition sInit;
       memory :=
         add pdparent
           (PDT
              {|
                structure := structure pdentryPdparent;
                firstfreeslot := firstfreeslot pdentryPdparent;
                nbfreeslots := nbfreeslots pdentryPdparent;
                nbprepare := nbprepare pdentryPdparent;
                parent := parent pdentryPdparent;
                MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                vidtAddr := vidtAddr pdentryPdparent
              |}) (memory s1) beqAddr
     |} /\ pdentryMPU pdparent realMPU s1)
-> isBuiltFromWriteAccessibleRec sInit s (statesList ++ [s]) (parentsList ++ [pdparent]) pdbasepartition
      startaddr endaddr flag.
Proof.
revert blockBase. revert pdbasepartition. revert pdentryBase. revert parentsList. revert sInit.
induction statesList.
- (* statesList = [] *)
  simpl. intros sInit parentsList pdentryBase pdbasepartition blockBase _ _ _ _ _ _ _ _ _ _ _ _ _ HisBuilt
      HpartIsLast HbaseIsPart HlookupBasesInit HlookupBases0
      HlookupParts0 HlookupParentsInit HlookupParents0 Hpdparent HpartNotRoot HlookupBlocks0 HlookupBlocks1
      HPFlag Hstart Hend HblockMapped _ _ _ _ _ Hs1 HpropsOr.
  destruct HisBuilt as [HparentsList Hs0sInitEq]. subst parentsList. subst s0. simpl. exists pdparent.
  exists []. split. reflexivity. exists realMPU. exists pdentryBase. exists pdentryPdparent.
  exists blockInParentPartitionAddr. exists bentry. exists newBentry. exists s1.
  assert(HnewB: newBentry = CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag 
              (blockindex bentry) (blockrange bentry)).
  {
    rewrite Hs1 in HlookupBlocks1. simpl in HlookupBlocks1. rewrite beqAddrTrue in HlookupBlocks1.
    injection HlookupBlocks1. intuition.
  }
  assert(HlookupBases1: lookup pdbasepartition (memory s1) beqAddr = Some (PDT pdentryBase)).
  {
    rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr pdbasepartition) eqn:HbeqBlockBase.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBase. rewrite HbeqBlockBase in *.
      rewrite HlookupBasesInit in HlookupBlocks0. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBase. rewrite removeDupIdentity; intuition.
  }
  assert(HlookupParents1: lookup pdparent (memory s1) beqAddr = Some (PDT pdentryPdparent)).
  {
    rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *.
      rewrite HlookupParents0 in HlookupBlocks0. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
  }
  simpl in HpartIsLast. subst partition. rewrite HlookupParts0 in HlookupBases0.
  injection HlookupBases0 as HpdentriesEq. rewrite HpdentriesEq in *.
  intuition.
- (* statesList = a::l *)
  intros sInit parentsList pdentryBase pdbasepartition blockBase HparentOfPart HnullExists HmultPDT HPDTIfPDFlag
      HwellFormedShadow Hstruct HisChild HchildBlockProps Hdisjoint HwellFormed HnoDup Htree HpartIsolation
      HisBuilt HpartIsLast HbaseIsPart HlookupBasesInit HlookupBases0 HlookupParts0 HlookupParentsInit
      HlookupParents0 Hpdparent HpartNotRoot HlookupBlocks0 HlookupBlocks1 HPFlag Hstart Hend HblockMapped
      HblockBaseMapped HPFlagBase HstartBase HendBase HnoPDFlagBase Hs1 HpropsOr.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec sInit s0 (a :: statesList) parentsList pdbasepartition
             startaddr endaddr flag) by assumption.
  simpl in HisBuilt. simpl.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU' & (pdentryBase' & (pdentryPdAddr &
                         (blockInParentPartitionAddr' & (bentry' & (newBentry' & (s' & (Hs' & HpropsOr' &
                          (*HlistEmpty &*) HnewB' & HlookupBlocksInit' & HlookupBlocks' & HPFlag' & Hstart' &
                           Hend' & Hblock'Mapped & HlookupBasesInit' & HlookupBases' & HlookupPdAddrsInit &
                            HlookupPdAddrs' & HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HcurrPartsEq: currentPartition sInit = currentPartition s').
  {
    rewrite Hs'. simpl. reflexivity.
  }
  rewrite HcurrPartsEq in HpropsOr'.
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer sInit)).
  {
    specialize(HparentOfPart pdbasepartition pdentryBase' HlookupBasesInit').
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite HpdAddr. intuition.
  }
  assert(HbuildPartIsChild: In pdbasepartition (getChildren pdAddr sInit)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupBasesInit'. assumption.
  }
  assert(HbuildIsPDT: isPDT pdbasepartition sInit).
  {
    unfold isPDT. rewrite HlookupBasesInit'. trivial.
  }
  assert(HcheckChild: false = checkChild blockInParentPartitionAddr' sInit
                                  (CPaddr (blockInParentPartitionAddr' + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps pdbasepartition pdAddr blockBase startaddr endaddr blockInParentPartitionAddr'
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase Hblock'Mapped Hstart' Hend' HPFlag' HstartTriv HendTriv). intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr
      blockInParentPartitionAddr' bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU')
      flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  assert(HtreeA: partitionTreeIsTree a).
  {
    apply partitionTreeIsTreePreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
        bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag startaddr endaddr;
      intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr
      blockInParentPartitionAddr' bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU')
      flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
      bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag startaddr endaddr;
        try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormed blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormed. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormed blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormed. assumption.
      }
      assert(HlookupBlockBase: exists bentryBase, lookup blockBase (memory sInit) beqAddr = Some(BE bentryBase)).
      {
        unfold bentryPFlag in HPFlagBase. destruct (lookup blockBase (memory sInit) beqAddr) eqn:HlookupBlockBase;
            try(exfalso; congruence). destruct v; try(exfalso; congruence). exists b. reflexivity.
      }
      destruct HlookupBlockBase as [bentryBase HlookupBlockBase].
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory sInit) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory sInit) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child pdbasepartition) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup pdbasepartition HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks pdbasepartition sInit).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory sInit) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child sInit)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child sInit)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr pdbasepartition sInit)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child pdbasepartition HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr' (memory a) beqAddr = Some (BE newBentry')).
  {
    destruct HpropsOr' as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr') eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr'.
        rewrite HlookupBlocksInit' in HlookupPdAddrsInit. injection HlookupPdAddrsInit as HentriesEq.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(blockindex bentry' < kernelStructureEntriesNb) by (apply Hidx).
  assert(HPFlagBlockA: bentryPFlag blockInParentPartitionAddr' true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocksInit' in HPFlag'. rewrite HnewB'.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry') kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr sInit).
  {
    apply stableBEIsBuiltRev with (a :: statesList) parentsList pdbasepartition startaddr endaddr flag s0.
    unfold isBE. rewrite HlookupBlocks0. trivial.
    assumption.
  }
  assert(Hblock'IsBE: isBE blockInParentPartitionAddr' sInit).
  { unfold isBE. rewrite HlookupBlocksInit'. trivial. }
  assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr' + sh1offset)) (memory a) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr' + sh1offset)) (memory sInit) beqAddr).
  {
    specialize(HwellFormedShadow blockInParentPartitionAddr' Hblock'IsBE). unfold isSHE in HwellFormedShadow.
    assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr' + sh1offset)) (memory s') beqAddr
                              = lookup (CPaddr (blockInParentPartitionAddr' + sh1offset)) (memory sInit) beqAddr).
    {
      rewrite Hs'. simpl.
      destruct (beqAddr blockInParentPartitionAddr' (CPaddr (blockInParentPartitionAddr' + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocksInit' in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupBlockSh1Eq. destruct HpropsOr' as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr' + sh1offset))) eqn:HbeqParentBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
        rewrite HlookupPdAddrsInit in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HcheckChildA: false = checkChild blockInParentPartitionAddr' a
                                    (CPaddr (blockInParentPartitionAddr' + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocksInit' in HcheckChild.
    rewrite HlookupBlockSh1Eq. assumption.
  }
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr' startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocksInit' in Hstart'. rewrite HnewB'.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry') kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr' endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocksInit' in Hend'. rewrite HnewB'.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry') kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HgetMappedBlocksEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr sInit).
  {
    assert(HgetMappedBlocksEq: getMappedBlocks pdAddr s' = getMappedBlocks pdAddr sInit).
    {
      rewrite Hs'. apply getMappedBlocksEqBENoChange with bentry'. assumption.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry') kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
    }
    rewrite <-HgetMappedBlocksEq. destruct HpropsOr' as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentryPdAddr. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
        bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedBlocksEq in Hblock'Mapped.
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer sInit).
  {
    assert(HgetPartEq: getPartitions multiplexer s' = getPartitions multiplexer sInit).
    {
      rewrite Hs'. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry'
            (CPaddr (blockInParentPartitionAddr' + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption);
          try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry') kernelStructureEntriesNb);
              try(lia); simpl; try(reflexivity)).
      apply lookupSh1EntryAddr with bentry'. assumption.
      destruct (beqAddr blockInParentPartitionAddr' (CPaddr (blockInParentPartitionAddr' + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        specialize(HwellFormedShadow blockInParentPartitionAddr' Hblock'IsBE). unfold isSHE in HwellFormedShadow.
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocksInit' in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartEq. destruct HpropsOr' as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentryPdAddr; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
        bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s' sInit pdAddr pdentryPdAddr blockInParentPartitionAddr'
        bentry' (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU') flag; intuition.
  }
  rewrite <-HgetPartEq in HpdAddrIsPart.
  assert(HnullExistsA: nullAddrExists a).
  {
    assert(HnullExistss1: nullAddrExists s').
    {
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs'. simpl.
      destruct (beqAddr blockInParentPartitionAddr' nullAddr) eqn:HbeqBlockNull.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockNull. subst blockInParentPartitionAddr'.
        rewrite HlookupBlocksInit' in HnullExists. congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockNull. rewrite removeDupIdentity; intuition.
    }
    unfold nullAddrExists in *. unfold isPADDR in *. destruct HpropsOr' as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr nullAddr) eqn:HbeqParentNull.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentNull. rewrite HbeqParentNull in *.
        rewrite HlookupPdAddrs' in HnullExistss1. congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentNull. rewrite removeDupIdentity; intuition.
  }
  assert(HisBuiltRec: isBuiltFromWriteAccessibleRec a s (statesList ++ [s]) (newPdEntriesList ++ [pdparent])
                          pdAddr startaddr endaddr flag).
  {
    assert(HpartIsNewLast: partition = last newPdEntriesList pdAddr).
    {
      apply lastRec with pdbasepartition. rewrite HparentsList in HpartIsLast. assumption.
    }
    assert(HlookupParents': lookup pdparent (memory s') beqAddr = Some (PDT pdentryPdparent)).
    {
      rewrite Hs'. simpl.
      destruct (beqAddr blockInParentPartitionAddr' pdparent) eqn:HbeqBlockParent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *.
        rewrite HlookupParentsInit in HlookupBlocksInit'. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
    }
    assert(HcurrPartEq: currentPartition s' = currentPartition sInit).
    {
      rewrite Hs'. simpl. reflexivity.
    }
    rewrite <-HcurrPartEq in HpropsOr.
    assert(HlookupBlockBase: exists bentryBase, lookup blockBase (memory sInit) beqAddr = Some(BE bentryBase)).
    {
      unfold bentryPFlag in HPFlagBase. destruct (lookup blockBase (memory sInit) beqAddr);
          try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists b. reflexivity.
    }
    destruct HlookupBlockBase as [bentryBase HlookupBlockBase].
    assert(HparentsListNoDup: NoDup parentsList).
    {
      apply parentOfPartNotInParentsListsTail with pdbasepartition s0.
      apply partitionTreeIsTreePreservedIsBuiltRec with sInit (a::statesList) parentsList pdbasepartition
            startaddr endaddr flag blockBase bentryBase; assumption.
      apply parentOfPartitionIsPartitionPreservedIsBuiltRec with sInit (a::statesList) parentsList pdbasepartition
            startaddr endaddr flag blockBase bentryBase; assumption.
      apply listWithIsBuiltIsParentsList with sInit (a::statesList) startaddr endaddr flag blockBase bentryBase;
            assumption.
    }
    destruct HpropsOr' as [Has'Eq | Ha].
    + subst a.
      assert(HlookupPdAddrEq: lookup pdAddr (memory s0) beqAddr = lookup pdAddr (memory s') beqAddr).
      {
        apply lookupPDTEqWriteAccess with statesList newPdEntriesList startaddr endaddr flag pdAddr;
            try(assumption);
            try(unfold isPDT; rewrite HlookupPdAddrs'; trivial).
        rewrite HparentsList in HparentsListNoDup. apply NoDup_cons_iff in HparentsListNoDup. intuition.
      }
      assert(HlookupPdAddrs0: lookup pdAddr (memory s0) beqAddr = Some (PDT pdentryPdAddr)).
      {
        rewrite <-HlookupPdAddrEq in HlookupPdAddrs'. assumption.
      }
      specialize(IHstatesList s' newPdEntriesList pdentryPdAddr pdAddr blockInParentPartitionAddr' HparentOfPartA
        HnullExistsA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HisChildA HchildBlockPropsA HdisjointA
        HwellFormedBlockA HnoDupA HtreeA HpartIsolationA HisBuilt HpartIsNewLast HpdAddrIsPart HlookupPdAddrs'
        HlookupPdAddrs0 HlookupParts0 HlookupParents' HlookupParents0 Hpdparent HpartNotRoot HlookupBlocks0
        HlookupBlocks1 HPFlag Hstart Hend HblockMapped Hblock'Mapped HPFlagBlockA HstartBlockA HendBlockA
        HcheckChildA Hs1 HpropsOr).
      assumption.
    + destruct Ha as [Ha HMPU].
      assert(HlookupPdAddrEq: lookup pdAddr (memory s0) beqAddr = lookup pdAddr (memory a) beqAddr).
      {
        apply lookupPDTEqWriteAccess with statesList newPdEntriesList startaddr endaddr flag pdAddr;
            try(assumption);
            try(unfold isPDT; rewrite Ha; simpl; rewrite beqAddrTrue; trivial).
        rewrite HparentsList in HparentsListNoDup. apply NoDup_cons_iff in HparentsListNoDup. intuition.
      }
      assert(HlookupPdAddrA: lookup pdAddr (memory a) beqAddr
                          = Some(PDT
                              {|
                                structure := structure pdentryPdAddr;
                                firstfreeslot := firstfreeslot pdentryPdAddr;
                                nbfreeslots := nbfreeslots pdentryPdAddr;
                                nbprepare := nbprepare pdentryPdAddr;
                                parent := parent pdentryPdAddr;
                                MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU';
                                vidtAddr := vidtAddr pdentryPdAddr
                              |})).
      {
        rewrite Ha. simpl. rewrite beqAddrTrue. reflexivity.
      }
      set(pdentryPdAddrA:= {|
                             structure := structure pdentryPdAddr;
                             firstfreeslot := firstfreeslot pdentryPdAddr;
                             nbfreeslots := nbfreeslots pdentryPdAddr;
                             nbprepare := nbprepare pdentryPdAddr;
                             parent := parent pdentryPdAddr;
                             MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr' realMPU';
                             vidtAddr := vidtAddr pdentryPdAddr
                           |}).
      fold pdentryPdAddrA in HlookupPdAddrA. rewrite HlookupPdAddrA in HlookupPdAddrEq.
      assert(HcurrPartEqA: currentPartition a = currentPartition s').
      {
        rewrite Ha. simpl. rewrite HcurrPartEq. reflexivity.
      }
      rewrite <-HcurrPartEqA in HpropsOr.
      destruct (beqAddr pdAddr pdparent) eqn:HbeqPdAddrParent.
      * rewrite <-DTL.beqAddrTrue in HbeqPdAddrParent. rewrite HbeqPdAddrParent in *.
        rewrite HlookupParents' in HlookupPdAddrs'. injection HlookupPdAddrs' as HpdentriesEq.
        rewrite HpdentriesEq in *.
        rewrite HlookupPdAddrEq in HlookupParents0. injection HlookupParents0 as HpdentriesEq2.
        rewrite HpdentriesEq2 in *.
        specialize(IHstatesList a newPdEntriesList pdentryPdAddr pdparent blockInParentPartitionAddr'
              HparentOfPartA HnullExistsA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HisChildA
              HchildBlockPropsA HdisjointA HwellFormedBlockA HnoDupA HtreeA HpartIsolationA HisBuilt
              HpartIsNewLast HpdAddrIsPart HlookupPdAddrA HlookupPdAddrEq HlookupParts0 HlookupPdAddrA
              HlookupPdAddrEq Hpdparent HpartNotRoot HlookupBlocks0 HlookupBlocks1 HPFlag Hstart Hend
              HblockMapped Hblock'Mapped HPFlagBlockA HstartBlockA HendBlockA HcheckChildA Hs1 HpropsOr).
        assumption.
      * assert(HlookupParentA: lookup pdparent (memory a) beqAddr = Some (PDT pdentryPdparent)).
        {
          rewrite Ha. simpl. rewrite HbeqPdAddrParent. rewrite <-beqAddrFalse in HbeqPdAddrParent.
          rewrite removeDupIdentity; intuition.
        }
        specialize(IHstatesList a newPdEntriesList pdentryPdAddrA pdAddr blockInParentPartitionAddr'
          HparentOfPartA HnullExistsA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HisChildA
          HchildBlockPropsA HdisjointA HwellFormedBlockA HnoDupA HtreeA HpartIsolationA HisBuilt HpartIsNewLast
          HpdAddrIsPart HlookupPdAddrA HlookupPdAddrEq HlookupParts0 HlookupParentA HlookupParents0 Hpdparent
          HpartNotRoot HlookupBlocks0 HlookupBlocks1 HPFlag Hstart Hend HblockMapped Hblock'Mapped HPFlagBlockA
          HstartBlockA HendBlockA HcheckChildA Hs1 HpropsOr).
        assumption.
  }
  rewrite HgetMappedBlocksEq in Hblock'Mapped.
  rewrite <-HcurrPartsEq in HpropsOr'.
  exists pdAddr. exists (newPdEntriesList ++ [pdparent]). split. rewrite HparentsList. reflexivity.
  exists realMPU'. exists pdentryBase'. exists pdentryPdAddr. exists blockInParentPartitionAddr'.
  exists bentry'. exists newBentry'. exists s'. intuition.
Qed.

(*Lemma parentsAccSetToFlagIfIsBuiltFromWriteAccessibleRec pdbasepartition pdparent blockaddr startaddr endaddr s
s0 statesList parentsList flag:
noDupUsedPaddrList s0
-> wellFormedBlock s0
-> DisjointKSEntries s0
-> StructurePointerIsKS s0
-> parentOfPartitionIsPartition s0
-> partitionTreeIsTree s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition startaddr endaddr flag
-> In pdparent parentsList
-> In blockaddr (getMappedBlocks pdparent s)
-> bentryStartAddr blockaddr startaddr s
(*-> bentryEndAddr blockaddr endaddr s*)
-> bentryPFlag blockaddr true s
-> bentryAFlag blockaddr flag s.
Proof.
revert pdbasepartition. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList pdbasepartition HnoDup HwellFormed Hdisjoint Hstruct Hparent Htree HisBuilt HparentInList
        HblockMapped Hstart HPFlag.
  simpl in HisBuilt. destruct HisBuilt as [HparentsListEmpty Hss0Eq]. subst parentsList. simpl in HparentInList.
  exfalso; congruence.
- (* statesList = a::l *)
  intros s0 parentsList pdbasepartition HnoDup HwellFormed Hdisjoint Hstruct Hparent Htree HisBuilt HparentInList
        HblockMapped Hstart HPFlag.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a :: statesList) parentsList pdbasepartition
             startaddr endaddr flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBase & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBases0 & HlookupBases1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  rewrite HparentsList in HparentInList. simpl in HparentInList.
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HnewBentry: exists l, newBentry =
                {|
                  read := read bentry;
                  write := write bentry;
                  exec := exec bentry;
                  present := present bentry;
                  accessible := flag;
                  blockindex := blockindex bentry;
                  blockrange := blockrange bentry;
                  Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                |}).
  {
    rewrite HnewB. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    exists l. reflexivity.
  }
  destruct HnewBentry as [lBentry HnewBentry].
  assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
  { rewrite Hs1. simpl. reflexivity. }
  rewrite HcurrPartEq in HpropsOr.
  assert(HparentsListNoDup: NoDup parentsList).
  {
    apply parentOfPartNotInParentsListsTail with pdbasepartition s0.
    apply partitionTreeIsTreePreservedIsBuiltRec with s0 (a::statesList) parentsList pdbasepartition
          startaddr endaddr flag blockBase bentryBase; assumption.
    apply parentOfPartitionIsPartitionPreservedIsBuiltRec with sInit (a::statesList) parentsList pdbasepartition
          startaddr endaddr flag blockBase bentryBase; assumption.
    apply listWithIsBuiltIsParentsList with sInit (a::statesList) startaddr endaddr flag blockBase bentryBase;
          assumption.
  }
  destruct HparentInList as [HpdAddrIsParent | HparentRec].
  + (* pdAddr = pdparent, we must prove that blockaddr = blockInParentPartitionAddr *)
    rewrite HpdAddrIsParent in *.
    assert(HparentPDT: isPDT pdparent s).
    {
      assert(isPDT pdparent a).
      {
        unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
        * subst a. rewrite HlookupPdAddrs1. trivial.
        * destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue. trivial.
      }
      assert(HlookupEq: lookup pdparent (memory s) beqAddr = lookup pdparent (memory a) beqAddr).
      {
        apply lookupPDTEqWriteAccess with statesList newPdEntriesList startaddr endaddr flag pdparent;
            try(assumption).
        admit. (*TODO missing a consistency property on the fact that the partition tree is actually a tree*)
      }
      unfold isPDT in *. rewrite HlookupEq. assumption.
    }
    assert(HgetMappedEq: getMappedBlocks pdparent s = getMappedBlocks pdparent s0).
    {
      apply getMappedBlocksEqBuiltWithWriteAcc with (a::statesList) parentsList startaddr endaddr pdbasepartition
          flag; try(assumption). unfold isPDT. rewrite HlookupPdAddrs0. trivial.
    }
    rewrite <-HgetMappedEq in HblockMappedPdAddr.
    assert(Hstarts: bentryStartAddr blockInParentPartitionAddr startaddr s).
    {
      apply bentryStartAddrEqIsBuilt with s0 (a :: statesList) parentsList pdbasepartition startaddr endaddr flag;
            try(assumption). unfold isBE. rewrite HlookupBlocks0. trivial.
    }
    assert(Hpresents: bentryPFlag blockInParentPartitionAddr true s).
    {
      apply bentryPFlagEqIsBuilt with s0 (a :: statesList) parentsList pdbasepartition startaddr endaddr flag;
            try(assumption). unfold isBE. rewrite HlookupBlocks0. trivial.
    }
    assert(HblocksEq: blockaddr = blockInParentPartitionAddr).
    { apply mappedBlocksEqStartEq with pdparent startaddr s; intuition. }
    subst blockaddr.
    assert(HaccessA: bentryAFlag blockInParentPartitionAddr flag a).
    {
      destruct HpropsOr as [Has1Eq | Ha].
      + subst a. unfold bentryAFlag. rewrite HlookupBlocks1. rewrite HnewBentry. simpl. reflexivity.
      + destruct Ha as [Ha _]. rewrite Ha. unfold bentryAFlag. simpl.
        destruct (beqAddr pdparent blockInParentPartitionAddr) eqn:HbeqParentBlock.
        {
          rewrite <-DTL.beqAddrTrue in HbeqParentBlock. rewrite HbeqParentBlock in *.
          rewrite HlookupPdAddrs0 in HlookupBlocks0. congruence.
        }
        rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
        rewrite HlookupBlocks1. rewrite HnewBentry. simpl. reflexivity.
    }
    assert(HpreservedProps: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
    {
      apply DisjointKSEntriesPreservedIsBuilt with s0 pdparent pdentryPdAddr blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(assumption).
      intuition.
    }
    destruct HpreservedProps as [HstructA (HdisjointA & _)].
    assert(HparentA: parentOfPartitionIsPartition a).
    {
      apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdparent pdentryPdAddr
            blockInParentPartitionAddr bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr
            realMPU) flag; try(assumption).
      intuition.
    }
    assert(HlookupBlockEq: lookup blockInParentPartitionAddr (memory s) beqAddr
                            = lookup blockInParentPartitionAddr (memory a) beqAddr).
    {
      apply lookupBEEqWriteAccess with startaddr endaddr statesList newPdEntriesList pdparent flag pdparent;
            try(assumption).
      - unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
        + rewrite Has1Eq. rewrite HlookupPdAddrs1. trivial.
        + destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue. trivial.
      - unfold isBE. unfold bentryAFlag in HaccessA.
        destruct (lookup blockInParentPartitionAddr (memory a) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). trivial.
      - admit. (*TODO missing a consistency property on the fact that the partition tree is actually a tree*)
      - assert(HgetMappedEqA: getMappedBlocks pdparent s = getMappedBlocks pdparent a).
        {
          apply getMappedBlocksEqBuiltWithWriteAcc with statesList newPdEntriesList startaddr endaddr pdparent
                flag; try(assumption). unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
          + rewrite Has1Eq. rewrite HlookupPdAddrs1. trivial.
          + destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue. trivial.
        }
        rewrite <-HgetMappedEqA. assumption.
    }
    unfold bentryAFlag in *. rewrite HlookupBlockEq. assumption.
  + (* In pdparent newPdEntriesList *)
    assert(HpreservedProps: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
    {
      apply DisjointKSEntriesPreservedIsBuilt with s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(assumption).
      intuition.
    }
    destruct HpreservedProps as [HstructA (HdisjointA & _)].
    assert(HparentA: parentOfPartitionIsPartition a).
    {
      apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr
            blockInParentPartitionAddr bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr
            realMPU) flag; try(assumption).
      intuition.
    }
    specialize(IHstatesList a newPdEntriesList pdAddr HnoDup HwellFormed HdisjointA HstructA HparentA HisBuilt
          HparentRec HblockMapped Hstart HPFlag).
    assumption.
Admitted.*)

Lemma getPartitionsEqBuiltWithWriteAcc s0 s statesList parentsList startaddr endaddr buildPart flag blockBase
bentryBase:
wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> partitionsIsolation s0
-> childsBlocksPropsInParent s0
-> DisjointKSEntries s0
-> noDupUsedPaddrList s0
-> wellFormedBlock s0
-> AccessibleNoPDFlag s0
-> isChild s0
-> parentOfPartitionIsPartition s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> bentryAFlag blockBase true s0
-> In blockBase (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> getPartitions multiplexer s = getPartitions multiplexer s0.
Proof.
intros HwellFormedShadow Hstruct HPDTIfPDFlag HmultIsPDT HPartIsolation HparentBlockProps Hdisjoint HnoDup
       HwellFormed HaccessNoPD HisChild HparentIsPart HbuildPartIsPart HlookupBlockBase HPFlagBase HAFlagBase
       HblockBaseMapped HstartBase HendBase HisBuilt.
assert(HcheckChildBlockBase: false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))).
{
  assert(HbaseIsBE: isBE blockBase s0).
  { unfold isBE. rewrite HlookupBlockBase. trivial. }
  assert(Hsh1Base: sh1entryAddr blockBase (CPaddr (blockBase + sh1offset)) s0).
  { apply lookupSh1EntryAddr with bentryBase. assumption. }
  specialize(HaccessNoPD blockBase (CPaddr (blockBase + sh1offset)) HbaseIsBE Hsh1Base HAFlagBase).
  unfold sh1entryPDflag in HaccessNoPD. unfold checkChild. rewrite HlookupBlockBase.
  destruct (lookup (CPaddr (blockBase + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). assumption.
}
clear HAFlagBase. revert HcheckChildBlockBase. revert HisBuilt. revert HendBase. revert HstartBase.
revert HblockBaseMapped. revert HPFlagBase. revert HlookupBlockBase. revert HbuildPartIsPart.
revert HparentIsPart. revert HisChild. revert HaccessNoPD. revert HwellFormed. revert HnoDup. revert Hdisjoint.
revert HparentBlockProps. revert HPartIsolation. revert HmultIsPDT. revert HPDTIfPDFlag. revert Hstruct.
revert HwellFormedShadow.
revert bentryBase. revert blockBase. revert buildPart. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros. simpl in *. assert(s = s0) by intuition. subst s. reflexivity.
- (* statesList = a::l *)
  intros. (*s0 parentsList buildPart blockBase bentryBase HwellFormedShadow Hstruct HPDTIfPDFlag HmultIsPDT
      HPartIsolation HparentBlockProps Hdisjoint HnoDup HwellFormed HaccessNoPD HisChild HparentIsPart
      HbuildPartIsPart HlookupBlockBase HPFlagBase HAFlagBase HblockBaseMapped HstartBase HendBase HisBuilt.*)
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a :: statesList) parentsList buildPart startaddr
                          endaddr flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HcurPart: currentPartition s0 = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPart in HpropsOr.
  assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
  { rewrite Hs1. simpl. reflexivity. }
  assert(HpropsA: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  destruct HpropsA as (HstructA & HdisjointA & Hstructs1).
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HgetMappedEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite <-HgetMappedEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
  }
  assert(HcheckChildBlockA: false = checkChild blockInParentPartitionAddr a
                                        (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HlastPart: exists partition,
                         partition = last [pdAddr] buildPart /\
                         (forall (blockPart : paddr) (bentryPart : BlockEntry),
                          lookup blockPart (memory a) beqAddr = Some (BE bentryPart) ->
                          bentryPFlag blockPart true a ->
                          In blockPart (getMappedBlocks partition a) ->
                          bentryStartAddr blockPart startaddr a ->
                          bentryEndAddr blockPart endaddr a ->
                          false = checkChild blockPart a (CPaddr (blockPart + sh1offset)))).
    {
      apply baseBlockAccessibleImpliesNoPDWithIsBuilt with s0 [a] flag blockBase bentryBase pdentry0;
          try(assumption). simpl. exists pdAddr. exists []. split. reflexivity. exists realMPU. exists pdentry0.
      exists pdentry1. exists blockInParentPartitionAddr. exists bentry. exists newBentry. exists s1.
      rewrite <-HcurrPartEq in HpropsOr. intuition.
    }
    destruct HlastPart as [partition (HpartIsLast & Hforall)]. simpl in HpartIsLast. subst partition.
    apply Hforall with newBentry. assumption. unfold bentryPFlag in *. rewrite HlookupBlockA.
    rewrite HlookupBlocks0 in HPFlag. rewrite HnewB. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. assumption.
    rewrite HgetMappedEq. assumption.
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  { unfold isBE. rewrite HlookupBlocks0. trivial. }
  assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                        = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
  {
    specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
    assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                        = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
        rewrite HlookupAncestorsInit in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HcheckChildBlock: false = checkChild blockInParentPartitionAddr s0
                                        (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlocks0. rewrite HlookupBlockA in HcheckChildBlockA.
    rewrite <-HlookupSh1Eq. assumption.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlags1: PDTIfPDFlag s1).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(intuition; congruence).
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(intuition; congruence).
  }
  assert(HmultIsPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(intuition; congruence).
  }
  assert(HPartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(intuition; congruence).
  }
  assert(HparentIsPartMult: In pdAddr (getPartitions multiplexer s0)).
  {
    specialize(HparentIsPart buildPart pdentry0 HlookupParentsInit).
    destruct HparentIsPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite Hancestor. intuition.
  }
  assert(HparentBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(intuition; congruence).
    (*TODO factorize that*)
    intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
        HPFlagChild HstartProp HendProp.
    assert(startaddr < endaddr).
    {
      specialize(HwellFormed blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
      destruct HwellFormed. assumption.
    }
    assert(startChild < endChild).
    {
      specialize(HwellFormed blockChild startChild endChild HPFlagChild HstartChild HendChild).
      destruct HwellFormed. assumption.
    }
    assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                   (endAddr (blockrange bentryBase)))).
    {
      unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
      rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
      apply getAllPaddrBlockIncl; lia.
    }
    assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                  = Some (BE bentryChild)
                                                  /\ startChild = startAddr (blockrange bentryChild)
                                                  /\ endChild = endAddr (blockrange bentryChild)).
    {
      unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
      unfold bentryEndAddr in HendChild.
      destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists b. intuition.
    }
    destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
    assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                    (endAddr (blockrange bentryChild)))).
    {
      subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
    }
    destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
    + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
      destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
      * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
        unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
        rewrite <-HendChild in HendBase. split. assumption. assumption.
      * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
        assert(HbuildIsPDT: isPDT buildPart s0).
        { unfold isPDT. rewrite HlookupParentsInit. trivial. }
        specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
        apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
        induction (getMappedBlocks buildPart s0).
        { intuition. }
        simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
        -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
           rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
           destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
           contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
           rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
        -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
           ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
              destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
              contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
              rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
           ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
              destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
              destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
    + rewrite <-beqAddrFalse in HbeqChildBuild.
      assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
      {
        apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
        rewrite app_nil_r. assumption.
      }
      assert(HstartInChild: In startChild (getUsedPaddr child s0)).
      {
        unfold getUsedPaddr. apply in_or_app. right. assumption.
      }
      assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
      {
        apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
        rewrite app_nil_r. assumption.
      }
      assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
      {
        apply HisChild. assumption. unfold pdentryParent. rewrite HlookupParentsInit. assumption.
      }
      specialize(HPartIsolation pdAddr child buildPart HparentIsPartMult HchildIsChild HbuildPartIsChild
                  HbeqChildBuild startChild HstartInChild).
      contradict HPartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(intuition; congruence).
  }
  assert(HwellFormedA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(intuition; congruence).
  }
  assert(HaccessNoPDA: AccessibleNoPDFlag a).
  {
    apply AccessibleNoPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(intuition; congruence).
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; try(intuition; congruence).
  }
  assert(HparentIsPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag;
        try(intuition; congruence).
  }
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
            (CPaddr (blockInParentPartitionAddr + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption);
          try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
              try(lia); simpl; try(reflexivity)).
      apply lookupSh1EntryAddr with bentry. assumption.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
  }
  rewrite <-HgetPartEq in HparentIsPartMult.
  assert(HPFlagA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlag. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  rewrite <-HgetMappedEq in HblockIsMapped.
  assert(HblockStartA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockEndA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HwellFormedShadowA
              HstructA HPDTIfPDFlagA HmultIsPDTA HPartIsolationA HparentBlockPropsA HdisjointA HnoDupA
              HwellFormedA HaccessNoPDA HisChildA HparentIsPartA HparentIsPartMult HlookupBlockA HPFlagA
              HblockIsMapped HblockStartA HblockEndA HisBuilt HcheckChildBlockA).
  rewrite IHstatesList. assumption.
Qed.

Lemma getMappedBlocksEqBuiltWithWriteAcc s0 s statesList parentsList pdbasepartition startaddr endaddr buildPart
flag blockBase bentryBase:
DisjointKSEntries s0
-> StructurePointerIsKS s0
-> parentOfPartitionIsPartition s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> childsBlocksPropsInParent s0
-> isChild s0
-> wellFormedBlock s0
-> noDupUsedPaddrList s0
-> AccessibleNoPDFlag s0
-> partitionsIsolation s0
-> isPDT pdbasepartition s0
(*-> buildPart <> constantRootPartM*)
-> In buildPart (getPartitions multiplexer s0)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
-> In blockBase (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> getMappedBlocks pdbasepartition s = getMappedBlocks pdbasepartition s0.
Proof.
revert bentryBase. revert blockBase. revert buildPart. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart _ _ Hdisjoint Hstruct Hparent HmultPDT HPDTIfPDFlag HwellFormedShadow
      HchildBlockProps _ _ _ _ _ HbaseIsPDT _ _ _ _ _ _ _ HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [HparentsList Hss0Eq]. subst s. reflexivity.
- (* statesList = a::l *)
  intros s0 parentsList buildPart blockBase bentryBase Hdisjoint Hstruct Hparent HmultPDT HPDTIfPDFlag
      HwellFormedShadow HchildBlockProps HisChild HwellFormedBlock HnoDup HaccessNoPD HpartIsolation HbaseIsPDT
      HbuildIsPart HlookupBlockBase HPFlagBase HnoPDFlagBase HblockBaseMapped HstartBase HendBase HisBuilt.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HcurPart: currentPartition s0 = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPart in HpropsOr.
  assert(HpartConsist: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  destruct HpartConsist as [HstructA (HdisjointA & Hstructs1)].
  assert(HbaseAndParentArePDT: isPDT pdbasepartition s0 /\ isPDT pdAddr s0).
  {
    unfold isPDT in *. rewrite HlookupAncestorsInit. intuition.
  }
  destruct HbaseAndParentArePDT as [HbaseIsPDTs0 HpdAddrIsPDTs0].
  assert(HbaseIsPDTs1: isPDT pdbasepartition s1).
  {
    unfold isPDT. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr pdbasepartition) eqn:HbeqBlockBase.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBase. rewrite HbeqBlockBase in *. unfold isPDT in HbaseIsPDT.
      rewrite HlookupBlocks0 in HbaseIsPDT. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBase. rewrite removeDupIdentity; intuition.
  }
  assert(HbaseAndParentArePDT: isPDT pdbasepartition a /\ isPDT pdAddr a).
  {
    unfold isPDT in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite HlookupAncestors1. intuition.
    - destruct Ha as [Ha HMPU]. rewrite Ha. simpl. rewrite beqAddrTrue.
      destruct (beqAddr pdAddr pdbasepartition) eqn:HbeqPdAddrBase; try(intuition; congruence).
      rewrite <-beqAddrFalse in HbeqPdAddrBase. rewrite removeDupIdentity; intuition.
  }
  destruct HbaseAndParentArePDT as [HbaseIsPDTA HpdAddrIsPDTA].
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    rewrite Hancestor. specialize(Hparent buildPart pdentry0 HlookupParentsInit). intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupParentsInit. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupParentsInit. trivial.
  }
  assert(HnoPDFlag: false = checkChild blockInParentPartitionAddr s0
                                (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBase startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase HblockIsMapped HblockStart HblockEnd HPFlag HstartTriv HendTriv). intuition.
  }
  assert(HparentA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HaccessNoPDA: AccessibleNoPDFlag a).
  {
    apply AccessibleNoPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(intuition; congruence).
    intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HgetMappedEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite <-HgetMappedEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
  }
  assert(HcheckChildBlockA: false = checkChild blockInParentPartitionAddr a
                                        (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HlastPart: exists partition,
                         partition = last [pdAddr] buildPart /\
                         (forall (blockPart : paddr) (bentryPart : BlockEntry),
                          lookup blockPart (memory a) beqAddr = Some (BE bentryPart) ->
                          bentryPFlag blockPart true a ->
                          In blockPart (getMappedBlocks partition a) ->
                          bentryStartAddr blockPart startaddr a ->
                          bentryEndAddr blockPart endaddr a ->
                          false = checkChild blockPart a (CPaddr (blockPart + sh1offset)))).
    {
      apply baseBlockAccessibleImpliesNoPDWithIsBuilt with s0 [a] flag blockBase bentryBase pdentry0;
          try(assumption). simpl. exists pdAddr. exists []. split. reflexivity. exists realMPU. exists pdentry0.
      exists pdentry1. exists blockInParentPartitionAddr. exists bentry. exists newBentry. exists s1.
      rewrite <-HcurPart in HpropsOr. intuition.
    }
    destruct HlastPart as [partition (HpartIsLast & Hforall)]. simpl in HpartIsLast. subst partition.
    apply Hforall with newBentry. assumption. unfold bentryPFlag in *. rewrite HlookupBlockA.
    rewrite HlookupBlocks0 in HPFlag. rewrite HnewB. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. assumption.
    rewrite HgetMappedEq. assumption.
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartMultEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. unfold multiplexerIsPDT in HmultPDT.
      apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
           with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
         try(assumption);
         try(unfold CBlockEntry;
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
             simpl; reflexivity).
      - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
      - simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartMultEqs1. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartsEq in HpdAddrIsPart.
  assert(HlookupParentA: exists pdentry2, lookup pdAddr (memory a) beqAddr = Some (PDT pdentry2)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. exists pdentry1. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue.
      exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
               vidtAddr := vidtAddr pdentry1
             |}. reflexivity.
  }
  destruct HlookupParentA as [pdentry2 HlookupParentA].
  assert(HPFlagA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlag. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  rewrite <-HgetMappedEq in HblockIsMapped.
  assert(HblockStartA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockEndA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HdisjointA HstructA
              HparentA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HchildBlockPropsA HisChildA HwellFormedBlockA
              HnoDupA HaccessNoPDA HpartIsolationA HbaseIsPDTA HpdAddrIsPart HlookupBlockA HPFlagA
              HcheckChildBlockA HblockIsMapped HblockStartA HblockEndA HisBuilt).
  rewrite IHstatesList.
  assert(HgetMappedEqs1: getMappedBlocks pdbasepartition s1 = getMappedBlocks pdbasepartition s0).
  {
    rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. reflexivity.
  }
  rewrite <-HgetMappedEqs1.
  destruct HpropsOr as [Has1Eq | Ha].
  + (* a = s1 *)
    rewrite Has1Eq. reflexivity.
  + (* a <> s1 *)
    destruct Ha as [Ha HMPU]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1; intuition.
Qed.

Lemma getAccessibleMappedBlocksEqBuiltWithWriteAccAccessNoChange s0 s statesList parentsList pdbasepartition
startaddr endaddr buildPart flag block blockBuild bentryBuild:
DisjointKSEntries s0
-> StructurePointerIsKS s0
-> parentOfPartitionIsPartition s0
-> noDupUsedPaddrList s0
-> wellFormedBlock s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> childsBlocksPropsInParent s0
-> isChild s0
-> AccessibleNoPDFlag s0
-> partitionsIsolation s0
-> isPDT pdbasepartition s0
-> bentryAFlag block flag s0
-> bentryStartAddr block startaddr s0
-> bentryEndAddr block endaddr s0
-> bentryPFlag block true s0
-> In block (getMappedBlocks pdbasepartition s0)
-> In buildPart (getPartitions multiplexer s0)
-> bentryStartAddr blockBuild startaddr s0
-> bentryEndAddr blockBuild endaddr s0
-> bentryPFlag blockBuild true s0
-> lookup blockBuild (memory s0) beqAddr = Some(BE bentryBuild)
-> In blockBuild (getMappedBlocks buildPart s0)
-> false = checkChild blockBuild s0 (CPaddr (blockBuild + sh1offset))
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> getAccessibleMappedBlocks pdbasepartition s = getAccessibleMappedBlocks pdbasepartition s0.
Proof.
revert bentryBuild. revert blockBuild. revert buildPart. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart _ _ Hdisjoint Hstruct Hparent HnoDup HwellFormed _ _ _ _ _ _ _ HbaseIsPDT
        HAFlag Hstart Hend HPFlag HblockMapped _ _ _ _ _ _ _ HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [HparentsList Hss0Eq]. subst s. reflexivity.
- (* statesList = a::l *)
  intros s0 parentsList buildPart blockBuild bentryBuild Hdisjoint Hstruct Hparent HnoDup HwellFormed HmultPDT
        HPDTIfPDFlag HwellFormedShadow HchildBlockProps HisChild HaccessNoPD HPI HbaseIsPDT HAFlagBlock
        HstartBlock HendBlock HPFlagBlock HblockMapped HbuildIsPart HstartBuild HendBuild HPFlagBuild
        HlookupBlockBuild HblockBuildMapped HnoPDFlagBuild HisBuilt.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a::statesList) parentsList buildPart startaddr endaddr
                            flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HcurPart: currentPartition s0 = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPart in HpropsOr.
  assert(HpartConsist: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  destruct HpartConsist as [HstructA (HdisjointA & Hstructs1)].
  assert(HbaseAndParentArePDT: isPDT pdbasepartition s0 /\ isPDT pdAddr s0).
  {
    unfold isPDT in *. rewrite HlookupAncestorsInit. intuition.
  }
  destruct HbaseAndParentArePDT as [HbaseIsPDTs0 HpdAddrIsPDTs0].
  assert(HbaseIsPDTs1: isPDT pdbasepartition s1).
  {
    unfold isPDT. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr pdbasepartition) eqn:HbeqBlockBase.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBase. rewrite HbeqBlockBase in *. unfold isPDT in HbaseIsPDT.
      rewrite HlookupBlocks0 in HbaseIsPDT. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBase. rewrite removeDupIdentity; intuition.
  }
  assert(HbaseAndParentArePDT: isPDT pdbasepartition a /\ isPDT pdAddr a).
  {
    unfold isPDT in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite HlookupAncestors1. intuition.
    - destruct Ha as [Ha HMPU]. rewrite Ha. simpl. rewrite beqAddrTrue.
      destruct (beqAddr pdAddr pdbasepartition) eqn:HbeqPdAddrBase; try(intuition; congruence).
      rewrite <-beqAddrFalse in HbeqPdAddrBase. rewrite removeDupIdentity; intuition.
  }
  destruct HbaseAndParentArePDT as [HbaseIsPDTA HpdAddrIsPDTA].
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    rewrite Hancestor. specialize(Hparent buildPart pdentry0 HlookupParentsInit). intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupParentsInit. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupParentsInit. trivial.
  }
  assert(HnoPDFlag: false = checkChild blockInParentPartitionAddr s0
                                (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBuild startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBuildMapped HstartBuild HendBuild
               HPFlagBuild HblockIsMapped HblockStart HblockEnd HPFlag HstartTriv HendTriv). intuition.
  }
  assert(HparentA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag;
      try(intuition; congruence).
  }
  assert(HaccessNoPDA: AccessibleNoPDFlag a).
  {
    apply AccessibleNoPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPIA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(intuition; congruence).
    intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormed blockBuild startaddr endaddr HPFlagBuild HstartBuild HendBuild).
        destruct HwellFormed. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormed blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormed. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBuild))
                                                                     (endAddr (blockrange bentryBuild)))).
      {
        unfold bentryStartAddr in HstartBuild. unfold bentryEndAddr in HendBuild.
        rewrite HlookupBlockBuild in *. rewrite <-HstartBuild. rewrite <-HendBuild.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBuild) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBuild in *. rewrite <-HstartChild in HstartBuild.
          rewrite <-HendChild in HendBuild. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBuildMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBuild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBuild. assumption. simpl.
                rewrite HlookupBlockBuild. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBuild; try(assumption). simpl. rewrite HlookupBlockBuild.
          rewrite app_nil_r. assumption.
        }
        specialize(HPI pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HPI. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnewBentry: exists l, newBentry =
                {|
                  read := read bentry;
                  write := write bentry;
                  exec := exec bentry;
                  present := present bentry;
                  accessible := flag;
                  blockindex := blockindex bentry;
                  blockrange := blockrange bentry;
                  Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                |}).
  {
    rewrite HnewB. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    exists l. reflexivity.
  }
  destruct HnewBentry as [lBentry HnewBentry].
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HAFlagBlockA: bentryAFlag block flag a).
  {
    assert(HAFlags1: bentryAFlag block flag s1).
    {
      unfold bentryAFlag in *. rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *. rewrite <-HnewB.
        rewrite HnewBentry. simpl. reflexivity.
      - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
    }
    unfold bentryAFlag in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr block) eqn:HbeqPdAddrBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlock. rewrite HbeqPdAddrBlock in *.
        rewrite HlookupAncestorsInit in HAFlagBlock. congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HstartBlockA: bentryStartAddr block startaddr a).
  {
    assert(Hstarts1: bentryStartAddr block startaddr s1).
    {
      unfold bentryStartAddr in *. rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *. rewrite <-HnewB.
        rewrite HnewBentry. simpl. rewrite HlookupBlocks0 in HstartBlock. assumption.
      - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
    }
    unfold bentryStartAddr in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr block) eqn:HbeqPdAddrBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlock. rewrite HbeqPdAddrBlock in *.
        rewrite HlookupAncestorsInit in HstartBlock. congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HendBlockA: bentryEndAddr block endaddr a).
  {
    assert(Hends1: bentryEndAddr block endaddr s1).
    {
      unfold bentryEndAddr in *. rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *. rewrite <-HnewB.
        rewrite HnewBentry. simpl. rewrite HlookupBlocks0 in HendBlock. assumption.
      - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
    }
    unfold bentryEndAddr in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr block) eqn:HbeqPdAddrBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlock. rewrite HbeqPdAddrBlock in *.
        rewrite HlookupAncestorsInit in HendBlock. congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HPFlagBlockA: bentryPFlag block true a).
  {
    assert(HPFlags1: bentryPFlag block true s1).
    {
      unfold bentryPFlag in *. rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *. rewrite <-HnewB.
        rewrite HnewBentry. simpl. rewrite HlookupBlocks0 in HPFlagBlock. assumption.
      - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
    }
    unfold bentryPFlag in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr block) eqn:HbeqPdAddrBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdAddrBlock. rewrite HbeqPdAddrBlock in *.
        rewrite HlookupAncestorsInit in HPFlagBlock. congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdAddrBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HblockMappeds0: In block (getMappedBlocks pdbasepartition s0)) by assumption.
  assert(HgetMappedEqs1: getMappedBlocks pdbasepartition s1 = getMappedBlocks pdbasepartition s0).
  {
    rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. reflexivity.
  }
  rewrite <-HgetMappedEqs1 in HblockMapped.
  assert(HgetMappedEq: getMappedBlocks pdbasepartition a = getMappedBlocks pdbasepartition s1).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + (* a = s1 *)
      subst a. reflexivity.
    + (* a <> s1 *)
      destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1; intuition.
  }
  rewrite <-HgetMappedEq in HblockMapped.
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HgetMappedParentEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedParentEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite <-HgetMappedParentEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
  }
  assert(HcheckChildBlockA: false = checkChild blockInParentPartitionAddr a
                                        (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HlastPart: exists partition,
                         partition = last [pdAddr] buildPart /\
                         (forall (blockPart : paddr) (bentryPart : BlockEntry),
                          lookup blockPart (memory a) beqAddr = Some (BE bentryPart) ->
                          bentryPFlag blockPart true a ->
                          In blockPart (getMappedBlocks partition a) ->
                          bentryStartAddr blockPart startaddr a ->
                          bentryEndAddr blockPart endaddr a ->
                          false = checkChild blockPart a (CPaddr (blockPart + sh1offset)))).
    {
      apply baseBlockAccessibleImpliesNoPDWithIsBuilt with s0 [a] flag blockBuild bentryBuild pdentry0;
          try(assumption). simpl. exists pdAddr. exists []. split. reflexivity. exists realMPU. exists pdentry0.
      exists pdentry1. exists blockInParentPartitionAddr. exists bentry. exists newBentry. exists s1.
      rewrite <-HcurPart in HpropsOr. intuition.
    }
    destruct HlastPart as [partition (HpartIsLast & Hforall)]. simpl in HpartIsLast. subst partition.
    apply Hforall with newBentry. assumption. unfold bentryPFlag in *. rewrite HlookupBlockA.
    rewrite HlookupBlocks0 in HPFlag. rewrite HnewB. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. assumption.
    rewrite HgetMappedParentEq. assumption.
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartMultEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. unfold multiplexerIsPDT in HmultPDT.
      apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
           with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
         try(assumption);
         try(unfold CBlockEntry;
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
             simpl; reflexivity).
      - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
      - simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartMultEqs1. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartsEq in HpdAddrIsPart.
  assert(HlookupParentA: exists pdentry2, lookup pdAddr (memory a) beqAddr = Some (PDT pdentry2)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. exists pdentry1. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue.
      exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
               vidtAddr := vidtAddr pdentry1
             |}. reflexivity.
  }
  destruct HlookupParentA as [pdentry2 HlookupParentA].
  assert(HPFlagA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlag. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  rewrite <-HgetMappedParentEq in HblockIsMapped.
  assert(HblockStartA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockEndA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HdisjointA HstructA
              HparentA HnoDupA HwellFormedA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HchildBlockPropsA
              HisChildA HaccessNoPDA HPIA HbaseIsPDTA HAFlagBlockA HstartBlockA HendBlockA HPFlagBlockA
              HblockMapped HpdAddrIsPart HblockStartA HblockEndA HPFlagA HlookupBlockA HblockIsMapped
              HcheckChildBlockA HisBuilt).
  rewrite IHstatesList.
  assert(HgetAccMappedEqs1: getAccessibleMappedBlocks pdbasepartition s1
                            = getAccessibleMappedBlocks pdbasepartition s0).
  {
    rewrite HgetMappedParentEq in *.
    destruct (beqAddr pdbasepartition pdAddr) eqn:HbeqBasePdAddr.
    - rewrite <-DTL.beqAddrTrue in HbeqBasePdAddr. subst pdbasepartition.
      rewrite Hs1. apply getAccessibleMappedBlocksEqBEAccessiblePresentNoChange with bentry. assumption.
      rewrite <-HnewB. rewrite HnewBentry. simpl. reflexivity.
      rewrite <-HnewB. rewrite HnewBentry. simpl.
      assert(HblocksEq: block = blockInParentPartitionAddr).
      {
        apply mappedBlocksEqStartEq with pdAddr startaddr s0; assumption.
      }
      subst block. unfold bentryAFlag in HAFlagBlock. rewrite HlookupBlocks0 in HAFlagBlock. assumption.
    - rewrite <-beqAddrFalse in HbeqBasePdAddr. rewrite Hs1. apply getAccessibleMappedBlocksEqBENotInPart.
      assumption. unfold isBE. rewrite HlookupBlocks0. trivial.
      intro Hcontra. unfold getMappedBlocks in HblockIsMapped. apply InFilterPresentInList in HblockIsMapped.
      specialize(Hdisjoint pdbasepartition pdAddr HbaseIsPDTs0 HpdAddrIsPDTs0 HbeqBasePdAddr).
      destruct Hdisjoint as [list1 (list2 & (Hlist1 & Hlist2 & Hdisjoint))]. subst list1. subst list2.
      specialize(Hdisjoint blockInParentPartitionAddr Hcontra). congruence.
  }
  rewrite <-HgetAccMappedEqs1. destruct HpropsOr as [Has1Eq | Ha].
  { subst a. reflexivity. }
  destruct Ha as [Ha _]. rewrite Ha. apply getAccessibleMappedBlocksEqPDT with pdentry1; try(assumption).
  simpl. reflexivity.
Qed.

Lemma getAccessibleMappedPaddrEqBuiltWithWriteAcc s0 s statesList parentsList pdbasepartition startaddr endaddr
buildPart flag blockBase bentryBase:
DisjointKSEntries s0
-> StructurePointerIsKS s0
-> parentOfPartitionIsPartition s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> childsBlocksPropsInParent s0
-> isChild s0
-> wellFormedBlock s0
-> noDupUsedPaddrList s0
-> AccessibleNoPDFlag s0
-> partitionsIsolation s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
-> bentryPFlag blockBase true s0
-> false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
-> In blockBase (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBase startaddr s0
-> bentryEndAddr blockBase endaddr s0
-> isPDT pdbasepartition s0
-> ~In pdbasepartition parentsList
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> getAccessibleMappedPaddr pdbasepartition s = getAccessibleMappedPaddr pdbasepartition s0.
Proof.
revert bentryBase. revert blockBase. revert buildPart. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart blockBase bentryBase Hdisjoint Hstruct HparentOfPart _ _ _ _ _ _ _ _ _ _ _ _ _
        _ _ _ HbaseIsPDT HbaseNotInList HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [HparentsList Hss0Eq]. subst s. reflexivity.
- (* statesList = a::l *)
  intros s0 parentsList buildPart blockBase bentryBase Hdisjoint Hstruct HparentOfPart HmultPDT HPDTIfPDFlag
        HwellFormedShadow HchildBlockProps HisChild HwellFormedBlock HnoDup HaccessNoPD HPI HbuildIsPart
        HlookupBlockBase HPFlagBase HnoPDFlagBase HblockBaseMapped HstartBase HendBase HbaseIsPDT HbaseNotInList
        HisBuilt.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr (*& (HlastCase*)
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockStart & HblockEnd &
                        HblockIsMapped & HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit &
                         HlookupAncestors1 & Hancestor & HbaseNotRoot & HisBuilt))))))))))))(*)*)].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HcurPart: currentPartition s0 = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPart in HpropsOr.
  assert(HpartConsist: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  destruct HpartConsist as [HstructA (HdisjointA & Hstructs1)].
  assert(HbaseAndParentArePDT: isPDT pdbasepartition s0 /\ isPDT pdAddr s0).
  {
    unfold isPDT in *. rewrite HlookupAncestorsInit. intuition.
  }
  destruct HbaseAndParentArePDT as [HbaseIsPDTs0 HpdAddrIsPDTs0].
  assert(HbaseIsPDTs1: isPDT pdbasepartition s1).
  {
    unfold isPDT. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr pdbasepartition) eqn:HbeqBlockBase.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBase. rewrite HbeqBlockBase in *. unfold isPDT in HbaseIsPDT.
      rewrite HlookupBlocks0 in HbaseIsPDT. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBase. rewrite removeDupIdentity; intuition.
  }
  assert(HbaseAndParentArePDT: isPDT pdbasepartition a /\ isPDT pdAddr a).
  {
    unfold isPDT in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite HlookupAncestors1. intuition.
    - destruct Ha as [Ha HMPU]. rewrite Ha. simpl. rewrite beqAddrTrue.
      destruct (beqAddr pdAddr pdbasepartition) eqn:HbeqPdAddrBase; try(intuition; congruence).
      rewrite <-beqAddrFalse in HbeqPdAddrBase. rewrite removeDupIdentity; intuition.
  }
  destruct HbaseAndParentArePDT as [HbaseIsPDTA HpdAddrIsPDTA].
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    rewrite Hancestor. specialize(HparentOfPart buildPart pdentry0 HlookupParentsInit). intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupParentsInit. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupParentsInit. trivial.
  }
  assert(HnoPDFlag: false = checkChild blockInParentPartitionAddr s0
                                (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBase startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBaseMapped HstartBase HendBase
               HPFlagBase HblockIsMapped HblockStart HblockEnd HPFlag HstartTriv HendTriv). intuition.
  }
  assert(HparentA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HaccessNoPDA: AccessibleNoPDFlag a).
  {
    apply AccessibleNoPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPIA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
          bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(intuition; congruence).
    intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBase startaddr endaddr HPFlagBase HstartBase HendBase).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBase))
                                                                     (endAddr (blockrange bentryBase)))).
      {
        unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
        rewrite HlookupBlockBase in *. rewrite <-HstartBase. rewrite <-HendBase.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBase) eqn:HbeqBlockChildBlockBase.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBase. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBase in *. rewrite <-HstartChild in HstartBase.
          rewrite <-HendChild in HendBase. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBase.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBaseMapped as [Ha0IsBase | HblockBaseMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBase in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBase. assumption. simpl.
                rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBase; try(assumption). simpl. rewrite HlookupBlockBase.
          rewrite app_nil_r. assumption.
        }
        specialize(HPI pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HPI. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnewBentry: exists l, newBentry =
                {|
                  read := read bentry;
                  write := write bentry;
                  exec := exec bentry;
                  present := present bentry;
                  accessible := flag;
                  blockindex := blockindex bentry;
                  blockrange := blockrange bentry;
                  Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                |}).
  {
    rewrite HnewB. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    exists l. reflexivity.
  }
  destruct HnewBentry as [lBentry HnewBentry].
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupAncestorsInit in HlookupBlocks0. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(HgetMappedParentEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedParentEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite <-HgetMappedParentEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
  }
  assert(HcheckChildBlockA: false = checkChild blockInParentPartitionAddr a
                                        (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HlastPart: exists partition,
                         partition = last [pdAddr] buildPart /\
                         (forall (blockPart : paddr) (bentryPart : BlockEntry),
                          lookup blockPart (memory a) beqAddr = Some (BE bentryPart) ->
                          bentryPFlag blockPart true a ->
                          In blockPart (getMappedBlocks partition a) ->
                          bentryStartAddr blockPart startaddr a ->
                          bentryEndAddr blockPart endaddr a ->
                          false = checkChild blockPart a (CPaddr (blockPart + sh1offset)))).
    {
      apply baseBlockAccessibleImpliesNoPDWithIsBuilt with s0 [a] flag blockBase bentryBase pdentry0;
          try(assumption). simpl. exists pdAddr. exists []. split. reflexivity. exists realMPU. exists pdentry0.
      exists pdentry1. exists blockInParentPartitionAddr. exists bentry. exists newBentry. exists s1.
      rewrite <-HcurPart in HpropsOr. intuition.
    }
    destruct HlastPart as [partition (HpartIsLast & Hforall)]. simpl in HpartIsLast. subst partition.
    apply Hforall with newBentry. assumption. unfold bentryPFlag in *. rewrite HlookupBlockA.
    rewrite HlookupBlocks0 in HPFlag. rewrite HnewB. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. assumption.
    rewrite HgetMappedParentEq. assumption.
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartMultEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. unfold multiplexerIsPDT in HmultPDT.
      apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
           with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
         try(assumption);
         try(unfold CBlockEntry;
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
             simpl; reflexivity).
      - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
      - simpl.
        destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
        {
          specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
          rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartMultEqs1. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentry1; try(assumption).
      simpl. reflexivity.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartsEq in HpdAddrIsPart.
  assert(HlookupParentA: exists pdentry2, lookup pdAddr (memory a) beqAddr = Some (PDT pdentry2)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    - subst a. exists pdentry1. assumption.
    - destruct Ha as [Ha _]. rewrite Ha. simpl. rewrite beqAddrTrue.
      exists {|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
               vidtAddr := vidtAddr pdentry1
             |}. reflexivity.
  }
  destruct HlookupParentA as [pdentry2 HlookupParentA].
  assert(HPFlagA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlag. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  rewrite <-HgetMappedParentEq in HblockIsMapped.
  assert(HblockStartA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockStart. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockEndA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HblockEnd. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  rewrite HparentsList in HbaseNotInList. simpl in HbaseNotInList. apply Decidable.not_or in HbaseNotInList.
  destruct HbaseNotInList as [HbeqPdAddrBase HbaseNotInListRec]. apply not_eq_sym in HbeqPdAddrBase.
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HdisjointA HstructA
              HparentA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HchildBlockPropsA HisChildA HwellFormedA
              HnoDupA HaccessNoPDA HPIA HpdAddrIsPart HlookupBlockA HPFlagA HcheckChildBlockA HblockIsMapped
              HblockStartA HblockEndA HbaseIsPDTA HbaseNotInListRec HisBuilt).
  rewrite IHstatesList.
  assert(HgetAccMappedEqs1: getAccessibleMappedPaddr pdbasepartition s1
                            = getAccessibleMappedPaddr pdbasepartition s0).
  {
    rewrite HgetMappedParentEq in HblockIsMapped. rewrite Hs1.
    apply getAccessibleMappedPaddrEqBENotInPart; try(assumption). unfold isBE.
    intro Hcontra. unfold getMappedBlocks in HblockIsMapped. apply InFilterPresentInList in HblockIsMapped.
    specialize(Hdisjoint pdbasepartition pdAddr HbaseIsPDTs0 HpdAddrIsPDTs0 HbeqPdAddrBase).
    destruct Hdisjoint as [list1 (list2 & (Hlist1 & Hlist2 & Hdisjoint))]. subst list1. subst list2.
    specialize(Hdisjoint blockInParentPartitionAddr Hcontra). congruence.
  }
  rewrite <-HgetAccMappedEqs1.
  destruct HpropsOr as [Has1Eq | Ha].
  + (* a = s1 *)
    rewrite Has1Eq. reflexivity.
  + (* a <> s1 *)
    destruct Ha as [Ha _]. rewrite Ha. apply getAccessibleMappedPaddrEqPDT with pdentry1; intuition.
Qed.

Lemma AccessibleNoPDFlagPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr
flag blockBuild bentryBuild:
AccessibleNoPDFlag s0
-> parentOfPartitionIsPartition s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> isChild s0
-> childsBlocksPropsInParent s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> noDupUsedPaddrList s0
-> partitionsIsolation s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup blockBuild (memory s0) beqAddr = Some (BE bentryBuild)
-> bentryPFlag blockBuild true s0
-> false = checkChild blockBuild s0 (CPaddr (blockBuild + sh1offset))
-> In blockBuild (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBuild startaddr s0
-> bentryEndAddr blockBuild endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> AccessibleNoPDFlag s.
Proof.
revert bentryBuild. revert blockBuild. revert buildPart. revert parentsList. revert s0.
induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart blockBuild bentryBuild HaccessNoPD _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [_ HparentsList]. subst s. assumption.
- (* statesList = a::l *)
  intros s0 parentsList buildPart blockBuild bentryBuild HaccessNoPD HparentOfPart HmultPDT HPDTIfPDFlag
      HwellFormedShadow Hstruct HisChild HchildBlockProps Hdisjoint HwellFormedBlock HnoDup HpartIsolation
      HbaseIsPart HlookupBlockBuild HPFlagBuild HnoPDFlagBuild HblockBuildMapped HstartBuild HendBuild HisBuilt.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a :: statesList) parentsList buildPart
             startaddr endaddr flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBuild & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBuilds0 & HlookupBuilds1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HcurrPartsEq: currentPartition s0 = currentPartition s1).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  rewrite HcurrPartsEq in HpropsOr.
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    specialize(HparentOfPart buildPart pdentryBuild HlookupBuilds0).
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite HpdAddr. intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupBuilds0. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupBuilds0. trivial.
  }
  assert(HcheckChild: false = checkChild blockInParentPartitionAddr s0
                                  (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBuild startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBuildMapped HstartBuild HendBuild
               HPFlagBuild HblockMappedPdAddr HstartBlock HendBlock HPFlagBlock HstartTriv HendTriv). intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr
      blockInParentPartitionAddr bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU)
      flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HaccessNoPDA: AccessibleNoPDFlag a).
  {
    apply AccessibleNoPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBuild startaddr endaddr HPFlagBuild HstartBuild HendBuild).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBuild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBuild))
                                                                     (endAddr (blockrange bentryBuild)))).
      {
        unfold bentryStartAddr in HstartBuild. unfold bentryEndAddr in HendBuild.
        rewrite HlookupBlockBuild in *. rewrite <-HstartBuild. rewrite <-HendBuild.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBuild) eqn:HbeqBlockChildBlockBuild.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBuild. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBuild in *. rewrite <-HstartChild in HstartBuild.
          rewrite <-HendChild in HendBuild. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBuild.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBuildMapped as [Ha0IsBuild | HblockBuildMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBuild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBuild).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBuild. assumption. simpl.
                rewrite HlookupBlockBuild. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBuild; try(assumption). simpl. rewrite HlookupBlockBuild.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HlookupPdAddrs0. injection HlookupPdAddrs0 as HentriesEq.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HPFlagBlockA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlagBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  { unfold isBE. rewrite HlookupBlocks0. trivial. }
  assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
  {
    specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
    assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                              = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupBlockSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
        rewrite HlookupPdAddrs0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HcheckChildA: false = checkChild blockInParentPartitionAddr a
                                    (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HcheckChild.
    rewrite HlookupBlockSh1Eq. assumption.
  }
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HstartBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HendBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HgetMappedBlocksEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedBlocksEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
    }
    rewrite <-HgetMappedBlocksEq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentryPdAddr. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedBlocksEq in HblockMappedPdAddr.
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
            (CPaddr (blockInParentPartitionAddr + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption);
          try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
              try(lia); simpl; try(reflexivity)).
      apply lookupSh1EntryAddr with bentry. assumption.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentryPdAddr; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartEq in HpdAddrIsPart.
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HaccessNoPDA
             HparentOfPartA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HisChildA HchildBlockPropsA
             HdisjointA HwellFormedBlockA HnoDupA HpartIsolationA HpdAddrIsPart HlookupBlockA HPFlagBlockA
             HcheckChildA HblockMappedPdAddr HstartBlockA HendBlockA HisBuilt).
  assumption.
Qed.

Lemma isChildPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr flag blockBuild
bentryBuild:
isChild s0
-> parentOfPartitionIsPartition s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> childsBlocksPropsInParent s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> noDupUsedPaddrList s0
-> partitionsIsolation s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup blockBuild (memory s0) beqAddr = Some (BE bentryBuild)
-> bentryPFlag blockBuild true s0
-> false = checkChild blockBuild s0 (CPaddr (blockBuild + sh1offset))
-> In blockBuild (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBuild startaddr s0
-> bentryEndAddr blockBuild endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> isChild s.
Proof.
revert bentryBuild. revert blockBuild. revert buildPart. revert parentsList. revert s0.
induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart blockBuild bentryBuild HisChild _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [_ HparentsList]. subst s. assumption.
- (* statesList = a::l *)
  intros s0 parentsList buildPart blockBuild bentryBuild HisChild HparentOfPart HmultPDT HPDTIfPDFlag
      HwellFormedShadow Hstruct HchildBlockProps Hdisjoint HwellFormedBlock HnoDup HpartIsolation
      HbaseIsPart HlookupBlockBuild HPFlagBuild HnoPDFlagBuild HblockBuildMapped HstartBuild HendBuild HisBuilt.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a :: statesList) parentsList buildPart
             startaddr endaddr flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBuild & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBuilds0 & HlookupBuilds1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HcurrPartsEq: currentPartition s0 = currentPartition s1).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  rewrite HcurrPartsEq in HpropsOr.
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    specialize(HparentOfPart buildPart pdentryBuild HlookupBuilds0).
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite HpdAddr. intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupBuilds0. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupBuilds0. trivial.
  }
  assert(HcheckChild: false = checkChild blockInParentPartitionAddr s0
                                  (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBuild startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBuildMapped HstartBuild HendBuild
               HPFlagBuild HblockMappedPdAddr HstartBlock HendBlock HPFlagBlock HstartTriv HendTriv). intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr
      blockInParentPartitionAddr bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU)
      flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBuild startaddr endaddr HPFlagBuild HstartBuild HendBuild).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBuild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBuild))
                                                                     (endAddr (blockrange bentryBuild)))).
      {
        unfold bentryStartAddr in HstartBuild. unfold bentryEndAddr in HendBuild.
        rewrite HlookupBlockBuild in *. rewrite <-HstartBuild. rewrite <-HendBuild.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBuild) eqn:HbeqBlockChildBlockBuild.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBuild. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBuild in *. rewrite <-HstartChild in HstartBuild.
          rewrite <-HendChild in HendBuild. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBuild.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBuildMapped as [Ha0IsBuild | HblockBuildMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBuild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBuild).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBuild. assumption. simpl.
                rewrite HlookupBlockBuild. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBuild; try(assumption). simpl. rewrite HlookupBlockBuild.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HlookupPdAddrs0. injection HlookupPdAddrs0 as HentriesEq.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HPFlagBlockA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlagBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  { unfold isBE. rewrite HlookupBlocks0. trivial. }
  assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
  {
    specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
    assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                              = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupBlockSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
        rewrite HlookupPdAddrs0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HcheckChildA: false = checkChild blockInParentPartitionAddr a
                                    (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HcheckChild.
    rewrite HlookupBlockSh1Eq. assumption.
  }
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HstartBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HendBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HgetMappedBlocksEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedBlocksEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
    }
    rewrite <-HgetMappedBlocksEq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentryPdAddr. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedBlocksEq in HblockMappedPdAddr.
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
            (CPaddr (blockInParentPartitionAddr + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption);
          try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
              try(lia); simpl; try(reflexivity)).
      apply lookupSh1EntryAddr with bentry. assumption.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentryPdAddr; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartEq in HpdAddrIsPart.
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HisChildA
             HparentOfPartA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HchildBlockPropsA
             HdisjointA HwellFormedBlockA HnoDupA HpartIsolationA HpdAddrIsPart HlookupBlockA HPFlagBlockA
             HcheckChildA HblockMappedPdAddr HstartBlockA HendBlockA HisBuilt).
  assumption.
Qed.

Lemma childsBlocksPropsInParentPreservedIsBuiltRec s s0 statesList parentsList buildPart startaddr endaddr
flag blockBuild bentryBuild:
childsBlocksPropsInParent s0
-> parentOfPartitionIsPartition s0
-> multiplexerIsPDT s0
-> PDTIfPDFlag s0
-> wellFormedFstShadowIfBlockEntry s0
-> StructurePointerIsKS s0
-> isChild s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> noDupUsedPaddrList s0
-> partitionsIsolation s0
-> In buildPart (getPartitions multiplexer s0)
-> lookup blockBuild (memory s0) beqAddr = Some (BE bentryBuild)
-> bentryPFlag blockBuild true s0
-> false = checkChild blockBuild s0 (CPaddr (blockBuild + sh1offset))
-> In blockBuild (getMappedBlocks buildPart s0)
-> bentryStartAddr blockBuild startaddr s0
-> bentryEndAddr blockBuild endaddr s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart startaddr endaddr flag
-> childsBlocksPropsInParent s.
Proof.
revert bentryBuild. revert blockBuild. revert buildPart. revert parentsList. revert s0.
induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart blockBuild bentryBuild HchildBlockProps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [_ HparentsList]. subst s. assumption.
- (* statesList = a::l *)
  intros s0 parentsList buildPart blockBuild bentryBuild HchildBlockProps HparentOfPart HmultPDT HPDTIfPDFlag
      HwellFormedShadow Hstruct HisChild Hdisjoint HwellFormedBlock HnoDup HpartIsolation
      HbaseIsPart HlookupBlockBuild HPFlagBuild HnoPDFlagBuild HblockBuildMapped HstartBuild HendBuild HisBuilt.
  assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s (a :: statesList) parentsList buildPart
             startaddr endaddr flag) by assumption.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBuild & (pdentryPdAddr &
                        (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & HpropsOr &
                        (*HbaseCase &*)
                        HnewB & HlookupBlocks0 & HlookupBlocks1 & HPFlagBlock & HstartBlock & HendBlock &
                        HblockMappedPdAddr & HlookupBuilds0 & HlookupBuilds1 & HlookupPdAddrs0 & HlookupPdAddrs1 &
                        HpdAddr & HbaseNotRoot & HisBuilt))))))))))].
  assert(HcurrPartsEq: currentPartition s0 = currentPartition s1).
  {
    rewrite Hs1. simpl. reflexivity.
  }
  rewrite HcurrPartsEq in HpropsOr.
  assert(HpdAddrIsPart: In pdAddr (getPartitions multiplexer s0)).
  {
    specialize(HparentOfPart buildPart pdentryBuild HlookupBuilds0).
    destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbaseNotRoot).
    rewrite HpdAddr. intuition.
  }
  assert(HbuildPartIsChild: In buildPart (getChildren pdAddr s0)).
  {
    apply HisChild. assumption. unfold pdentryParent. rewrite HlookupBuilds0. assumption.
  }
  assert(HbuildIsPDT: isPDT buildPart s0).
  {
    unfold isPDT. rewrite HlookupBuilds0. trivial.
  }
  assert(HcheckChild: false = checkChild blockInParentPartitionAddr s0
                                  (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    assert(HstartTriv: startaddr <= startaddr) by lia.
    assert(HendTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps buildPart pdAddr blockBuild startaddr endaddr blockInParentPartitionAddr
               startaddr endaddr HpdAddrIsPart HbuildPartIsChild HblockBuildMapped HstartBuild HendBuild
               HPFlagBuild HblockMappedPdAddr HstartBlock HendBlock HPFlagBlock HstartTriv HendTriv). intuition.
  }
  assert(HmultPDTA: multiplexerIsPDT a).
  {
    apply multiplexerIsPDTPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HPDTIfPDFlagA: PDTIfPDFlag a).
  {
    apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedShadowA: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr
      blockInParentPartitionAddr bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU)
      flag; intuition.
  }
  assert(HstructA: StructurePointerIsKS a).
  {
    apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HwellFormedBlockA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HnoDupA: noDupUsedPaddrList a).
  {
    apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HpartIsolationA: partitionsIsolation a).
  {
    apply partitionsIsolationPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
      bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  {
    apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
            bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
        try(assumption).
    - intuition.
    - intros child blockChild startChild endChild HchildIsChild HblockChildIsMapped HstartChild HendChild
      HPFlagChild HstartPropChild HendPropChild.
      assert(startaddr < endaddr).
      {
        specialize(HwellFormedBlock blockBuild startaddr endaddr HPFlagBuild HstartBuild HendBuild).
        destruct HwellFormedBlock. assumption.
      }
      assert(startChild < endChild).
      {
        specialize(HwellFormedBlock blockChild startChild endChild HPFlagChild HstartChild HendChild).
        destruct HwellFormedBlock. assumption.
      }
      assert(HstartChildInBlockBuild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryBuild))
                                                                     (endAddr (blockrange bentryBuild)))).
      {
        unfold bentryStartAddr in HstartBuild. unfold bentryEndAddr in HendBuild.
        rewrite HlookupBlockBuild in *. rewrite <-HstartBuild. rewrite <-HendBuild.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                    = Some (BE bentryChild)
                                                    /\ startChild = startAddr (blockrange bentryChild)
                                                    /\ endChild = endAddr (blockrange bentryChild)).
      {
        unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
        unfold bentryEndAddr in HendChild.
        destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. intuition.
      }
      destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
      assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                      (endAddr (blockrange bentryChild)))).
      {
        subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
      }
      destruct (beqAddr child buildPart) eqn:HbeqChildBuild.
      + rewrite <-DTL.beqAddrTrue in HbeqChildBuild. subst child.
        destruct (beqAddr blockChild blockBuild) eqn:HbeqBlockChildBlockBuild.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockBuild. subst blockChild. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockBuild in *. rewrite <-HstartChild in HstartBuild.
          rewrite <-HendChild in HendBuild. split. assumption. assumption.
        * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockBuild.
          specialize(HnoDup buildPart HbuildIsPDT). unfold getUsedPaddr in HnoDup.
          apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
          induction (getMappedBlocks buildPart s0).
          { intuition. }
          simpl in *. destruct HblockBuildMapped as [Ha0IsBuild | HblockBuildMappedRec].
          -- subst a0. destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
             rewrite HlookupBlockBuild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
             destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBuild).
             contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
             rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
          -- destruct HblockChildIsMapped as [Hcontra | HblockChildIsMappedRec].
             ++ subst a0. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockBuild. assumption. simpl.
                rewrite HlookupBlockBuild. rewrite app_nil_r. assumption.
             ++ destruct (lookup a0 (memory s0) beqAddr) eqn:HlookupA0; try(apply IHl; assumption).
                destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
      + rewrite <-beqAddrFalse in HbeqChildBuild.
        assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
        {
          apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
          rewrite app_nil_r. assumption.
        }
        assert(HstartInChild: In startChild (getUsedPaddr child s0)).
        {
          unfold getUsedPaddr. apply in_or_app. right. assumption.
        }
        assert(HstartInMappedBuild: In startChild (getMappedPaddr buildPart s0)).
        {
          apply addrInBlockIsMapped with blockBuild; try(assumption). simpl. rewrite HlookupBlockBuild.
          rewrite app_nil_r. assumption.
        }
        specialize(HpartIsolation pdAddr child buildPart HpdAddrIsPart HchildIsChild HbuildPartIsChild
                    HbeqChildBuild startChild HstartInChild).
        contradict HpartIsolation. unfold getUsedPaddr. apply in_or_app. right. assumption.
  }
  assert(HlookupBlockA: lookup blockInParentPartitionAddr (memory a) beqAddr = Some (BE newBentry)).
  {
    destruct HpropsOr as [Has1Eq | Ha].
    + subst a. assumption.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockInParentPartitionAddr.
        rewrite HlookupBlocks0 in HlookupPdAddrs0. injection HlookupPdAddrs0 as HentriesEq.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
  }
  assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HPFlagBlockA: bentryPFlag blockInParentPartitionAddr true a).
  {
    unfold bentryPFlag in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HPFlagBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
  { unfold isBE. rewrite HlookupBlocks0. trivial. }
  assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory a) beqAddr
                            = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
  {
    specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
    assert(HlookupBlockSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                              = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupBlockSh1Eq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. simpl.
      destruct (beqAddr pdAddr (CPaddr (blockInParentPartitionAddr + sh1offset))) eqn:HbeqParentBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
        rewrite HlookupPdAddrs0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
  }
  assert(HcheckChildA: false = checkChild blockInParentPartitionAddr a
                                    (CPaddr (blockInParentPartitionAddr + sh1offset))).
  {
    unfold checkChild in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HcheckChild.
    rewrite HlookupBlockSh1Eq. assumption.
  }
  assert(HstartBlockA: bentryStartAddr blockInParentPartitionAddr startaddr a).
  {
    unfold bentryStartAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HstartBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HendBlockA: bentryEndAddr blockInParentPartitionAddr endaddr a).
  {
    unfold bentryEndAddr in *. rewrite HlookupBlockA. rewrite HlookupBlocks0 in HendBlock. rewrite HnewB.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. assumption.
  }
  assert(HgetMappedBlocksEq: getMappedBlocks pdAddr a = getMappedBlocks pdAddr s0).
  {
    assert(HgetMappedBlocksEq: getMappedBlocks pdAddr s1 = getMappedBlocks pdAddr s0).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. reflexivity.
    }
    rewrite <-HgetMappedBlocksEq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha _]. rewrite Ha. apply getMappedBlocksEqPDT with pdentryPdAddr. assumption.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      simpl. reflexivity.
  }
  rewrite <-HgetMappedBlocksEq in HblockMappedPdAddr.
  assert(HgetPartEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  {
    assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
            (CPaddr (blockInParentPartitionAddr + sh1offset));
          try(unfold multiplexerIsPDT in *; assumption);
          try(unfold CBlockEntry; destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
              try(lia); simpl; try(reflexivity)).
      apply lookupSh1EntryAddr with bentry. assumption.
      destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
      {
        specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE). unfold isSHE in HwellFormedShadow.
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
        rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
    }
    rewrite <-HgetPartEq. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. reflexivity.
    - destruct Ha as [Ha _]. rewrite Ha. apply getPartitionsEqPDT with pdentryPdAddr; try(assumption).
      simpl. reflexivity.
      apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
      apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdAddr pdentryPdAddr blockInParentPartitionAddr
        bentry (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  rewrite <-HgetPartEq in HpdAddrIsPart.
  specialize(IHstatesList a newPdEntriesList pdAddr blockInParentPartitionAddr newBentry HchildBlockPropsA
             HparentOfPartA HmultPDTA HPDTIfPDFlagA HwellFormedShadowA HstructA HisChildA
             HdisjointA HwellFormedBlockA HnoDupA HpartIsolationA HpdAddrIsPart HlookupBlockA HPFlagBlockA
             HcheckChildA HblockMappedPdAddr HstartBlockA HendBlockA HisBuilt).
  assumption.
Qed.