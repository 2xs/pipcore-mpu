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
    This file contains the invariant of [setVIDT].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
  Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas Proof.InternalLemmas2.
Require Import Invariants getGlobalIdPDCurrentOrChild findBlockInKS findBlockInKSWithAddr.
From Stdlib Require Import Compare_dec Bool List Logic.ProofIrrelevance.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Import ListNotations.

Module WP := WeakestPreconditions.

Lemma writePDVidt pdpart vidtaddr P:
{{ fun s => P s /\ consistency s /\ partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ isPDT pdpart s }}
MAL.writePDVidt pdpart vidtaddr
{{ fun _ s => exists s0 pdentry newPDEntry, P s0 /\ lookup pdpart (memory s0) beqAddr = Some(PDT pdentry)
      /\ s = {|
               currentPartition := currentPartition s0;
               memory := add pdpart (PDT newPDEntry) (memory s0) beqAddr
             |}
      /\ consistency s /\ partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
      /\ newPDEntry = {|
                        structure := structure pdentry;
                        firstfreeslot := firstfreeslot pdentry;
                        nbfreeslots := nbfreeslots pdentry;
                        nbprepare := nbprepare pdentry;
                        parent := parent pdentry;
                        MPU := MPU pdentry;
                        vidtAddr := vidtaddr
                      |}
}}.
Proof.
unfold MAL.writePDVidt. eapply bindRev.
{ (** get **)
  eapply weaken. apply WP.get. intros s Hprops. simpl.
  instantiate(1 := fun s0 s1 => P s0 /\ isPDT pdpart s0 /\ s1 = s0 /\ consistency s0 /\ partitionsIsolation s0
    /\ kernelDataIsolation s0 /\ verticalSharing s0). intuition.
}
intro s. destruct (lookup pdpart (memory s) beqAddr) eqn:HlookupPart; try(eapply weaken; try(apply WP.undefined);
  intros sBis Hprops; simpl; destruct Hprops as (_ & HPDT & Hs & _); subst sBis; unfold isPDT in *;
  rewrite HlookupPart in *; congruence).
destruct v; try(eapply weaken; try(apply WP.undefined); intros sBis Hprops; simpl;
  destruct Hprops as (_ & HPDT & Hs & _); subst sBis; unfold isPDT in *; rewrite HlookupPart in *; congruence).
eapply weaken. apply WP.modify. intros sBis Hprops. simpl.
destruct Hprops as (HP & _ & Hs & Hconsist & HPI & HKDI & HVS). subst sBis. exists s. exists p.
exists {|
         structure := structure p;
         firstfreeslot := firstfreeslot p;
         nbfreeslots := nbfreeslots p;
         nbprepare := nbprepare p;
         parent := parent p;
         MPU := MPU p;
         vidtAddr := vidtaddr
       |}.
set(newS := {|
      currentPartition := currentPartition s;
      memory :=
        add pdpart
          (PDT
             {|
               structure := structure p;
               firstfreeslot := firstfreeslot p;
               nbfreeslots := nbfreeslots p;
               nbprepare := nbprepare p;
               parent := parent p;
               MPU := MPU p;
               vidtAddr := vidtaddr
             |})
          (memory s) beqAddr
    |}). unfold consistency in *. unfold consistency1 in *. unfold consistency2 in *.

assert(HgetPartsEq: getPartitions multiplexer newS = getPartitions multiplexer s).
{
  apply getPartitionsEqPDT with p; trivial; intuition.
}
assert(HgetKSEq: forall partition, getKSEntries partition newS = getKSEntries partition s).
{
  intro partition. apply getKSEntriesEqPDT with p; trivial. intuition.
}
assert(HgetMappedBEq: forall partition, getMappedBlocks partition newS = getMappedBlocks partition s).
{
  intro partition. apply getMappedBlocksEqPDT with p; trivial. intuition.
}
assert(HgetMappedPEq: forall partition, getMappedPaddr partition newS = getMappedPaddr partition s).
{
  intro partition. apply getMappedPaddrEqPDT with p; trivial. intuition.
}
assert(HgetAccMappedBEq: forall partition, getAccessibleMappedBlocks partition newS
  = getAccessibleMappedBlocks partition s).
{
  intro partition. apply getAccessibleMappedBlocksEqPDT with p; trivial. intuition.
}
assert(HgetAccMappedPEq: forall partition, getAccessibleMappedPaddr partition newS
  = getAccessibleMappedPaddr partition s).
{
  intro partition. apply getAccessibleMappedPaddrEqPDT with p; trivial. intuition.
}
assert(HgetConfigBEq: forall partition, isPDT partition s
  -> getConfigBlocks partition newS = getConfigBlocks partition s).
{
  intros partition HpartIsPDT. apply getConfigBlocksEqPDT with p; trivial.
}
assert(HgetConfigPEq: forall partition, isPDT partition s
  -> getConfigPaddr partition newS = getConfigPaddr partition s).
{
  intros partition HpartIsPDT. apply getConfigPaddrEqPDT with p; trivial.
}
assert(HgetChildrenEq: forall partition, getChildren partition newS = getChildren partition s).
{
  intros partition. apply getChildrenEqPDT with p; trivial. intuition.
}

assert(nullAddrExists newS).
{ (* BEGIN nullAddrExists newS *)
  assert(Hcons0: nullAddrExists s) by intuition. unfold nullAddrExists in *. unfold isPADDR in *.
  simpl. destruct (beqAddr pdpart nullAddr) eqn:HbeqGlobNull.
  {
    rewrite <-DTL.beqAddrTrue in HbeqGlobNull. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END nullAddrExists *)
}

assert(wellFormedFstShadowIfBlockEntry newS).
{ (* BEGIN wellFormedFstShadowIfBlockEntry newS *)
  assert(Hcons0: wellFormedFstShadowIfBlockEntry s) by intuition. intros block HblockIsBE. unfold isBE in *.
  simpl in HblockIsBE.
  destruct (beqAddr pdpart block) eqn:HbeqGlobBlock; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block HblockIsBE). unfold isSHE in *. simpl.
  destruct (beqAddr pdpart (CPaddr (block + sh1offset))) eqn:HbeqGlobSh1.
  {
    rewrite <-DTL.beqAddrTrue in HbeqGlobSh1. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END wellFormedFstShadowIfBlockEntry *)
}

assert(PDTIfPDFlag newS).
{ (* BEGIN PDTIfPDFlag newS *)
  assert(Hcons0: PDTIfPDFlag s) by intuition. intros idPDchild sh1entryaddr HcheckChild.
  unfold sh1entryAddr in *. unfold checkChild in *.
  assert(HlookupBlockEq: lookup idPDchild (memory newS) beqAddr = lookup idPDchild (memory s) beqAddr).
  {
    destruct HcheckChild as (_ & Hsh1). simpl in *.
    destruct (beqAddr pdpart idPDchild) eqn:HbeqGlobBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HcheckChilds0: true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s).
  {
    unfold sh1entryAddr. unfold checkChild. rewrite HlookupBlockEq in *.
    destruct HcheckChild as (HcheckChild & Hsh1).
    destruct (lookup idPDchild (memory s) beqAddr); try(exfalso; congruence). split; trivial.
    destruct v; try(congruence). simpl in HcheckChild.
    destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds0). unfold bentryAFlag in *. unfold bentryPFlag in *.
  unfold bentryStartAddr in *. unfold entryPDT in *. rewrite HlookupBlockEq.
  destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
  exists startaddr. split; trivial. destruct (lookup idPDchild (memory s) beqAddr); try(congruence).
  destruct v; try(congruence). simpl.
  destruct (beqAddr pdpart (startAddr (blockrange b))) eqn:HbeqGlobStart; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END PDTIfPDFlag *)
}

assert(AccessibleNoPDFlag newS).
{ (* BEGIN AccessibleNoPDFlag newS *)
  assert(Hcons0: AccessibleNoPDFlag s) by intuition. intros block sh1entryaddr HblockIsBE Hsh1 HAflag.
  unfold isBE in *. assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqGlobBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold sh1entryAddr in *. unfold bentryAFlag in *. rewrite HlookupBlockEq in *.
  specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAflag). unfold sh1entryPDflag in *. simpl.
  destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqGlobSh1.
  {
    rewrite <-DTL.beqAddrTrue in HbeqGlobSh1. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END AccessibleNoPDFlag *)
}

assert(FirstFreeSlotPointerIsBEAndFreeSlot newS).
{ (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot newS *)
  assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
  intros partition pdentryPart HlookupPartBis HbeqFirstNull.
  assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s) beqAddr = Some (PDT pdentryParts0)
    /\ firstfreeslot pdentryPart = firstfreeslot pdentryParts0).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. split; trivial.
      injection HlookupPartBis as HlookupPartBis. subst pdentryPart. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentryPart. auto.
  }
  destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HfirstEq)]. rewrite HfirstEq in *.
  specialize(Hcons0 partition pdentryParts0 HlookupParts0 HbeqFirstNull). destruct Hcons0 as (HBE & Hfree).
  unfold isBE in *. unfold isFreeSlot in *. simpl.
  destruct (beqAddr pdpart (firstfreeslot pdentryParts0)) eqn:HbeqPartFirst.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartFirst. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial.
  destruct (lookup (firstfreeslot pdentryParts0) (memory s) beqAddr); try(congruence).
  destruct v; try(congruence).
  destruct (beqAddr pdpart (CPaddr (firstfreeslot pdentryParts0 + sh1offset))) eqn:HbeqPartSh1.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartSh1. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup (CPaddr (firstfreeslot pdentryParts0 + sh1offset)) (memory s) beqAddr); try(congruence).
  destruct v; try(congruence).
  destruct (beqAddr pdpart (CPaddr (firstfreeslot pdentryParts0 + scoffset))) eqn:HbeqPartSce.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartSce. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
}

assert(multiplexerIsPDT newS).
{ (* BEGIN multiplexerIsPDT newS *)
  assert(Hcons0: multiplexerIsPDT s) by intuition. unfold multiplexerIsPDT in *. unfold isPDT in *. simpl.
  destruct (beqAddr pdpart multiplexer) eqn:HbeqPartMult; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END multiplexerIsPDT *)
}

assert(currentPartitionInPartitionsList newS).
{ (* BEGIN currentPartitionInPartitionsList newS *)
  assert(Hcons0: currentPartitionInPartitionsList s) by intuition. unfold currentPartitionInPartitionsList in *.
  rewrite HgetPartsEq. simpl. assumption.
  (* END currentPartitionInPartitionsList *)
}

assert(wellFormedShadowCutIfBlockEntry newS).
{ (* BEGIN wellFormedShadowCutIfBlockEntry newS *)
  assert(Hcons0: wellFormedShadowCutIfBlockEntry s) by intuition. intros block HblockIsBE.
  unfold isBE in *. assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HlookupBlockEq in *. specialize(Hcons0 block HblockIsBE).
  destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr. split; trivial. unfold isSCE in *. simpl.
  destruct (beqAddr pdpart scentryaddr) eqn:HbeqPartSce.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartSce. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END wellFormedShadowCutIfBlockEntry *)
}

assert(BlocksRangeFromKernelStartIsBE newS).
{ (* BEGIN BlocksRangeFromKernelStartIsBE newS *)
  assert(Hcons0: BlocksRangeFromKernelStartIsBE s) by intuition. intros kernel idx HkernIsKS HltIdxKernEntries.
  unfold isKS in *. assert(HlookupKernEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart kernel) eqn:HbeqPartKern; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HlookupKernEq in *. specialize(Hcons0 kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *. simpl.
  destruct (beqAddr pdpart (CPaddr (kernel + idx))) eqn:HbeqPartIdx.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartIdx. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END BlocksRangeFromKernelStartIsBE *)
}

assert(KernelStructureStartFromBlockEntryAddrIsKS newS).
{ (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS newS *)
  assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s) by intuition. intros block idx HblockIsBE Hidx.
  unfold isBE in *. assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryBlockIndex in *. rewrite HlookupBlockEq in *. specialize(Hcons0 block idx HblockIsBE Hidx).
  unfold isKS in *. simpl. destruct (beqAddr pdpart (CPaddr (block - idx))) eqn:HbeqPartKern.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartKern. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END KernelStructureStartFromBlockEntryAddrIsKS *)
}

assert(sh1InChildLocationIsBE newS).
{ (* BEGIN sh1InChildLocationIsBE newS *)
  assert(Hcons0: sh1InChildLocationIsBE s) by intuition. intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull.
  simpl in HlookupSh1. destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqPartSh1; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). unfold isBE in *. simpl.
  destruct (beqAddr pdpart (inChildLocation sh1entry)) eqn:HbeqPartChildLoc.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartChildLoc. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END sh1InChildLocationIsBE *)
}

assert(StructurePointerIsKS newS).
{ (* BEGIN StructurePointerIsKS newS *)
  assert(Hcons0: StructurePointerIsKS s) by intuition. intros partition pdentry HlookupPartBis HbeqStructNull.
  assert(HlookupParts0: exists pdentrys0, lookup partition (memory s) beqAddr = Some (PDT pdentrys0)
    /\ structure pdentry = structure pdentrys0).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. split; trivial.
      injection HlookupPartBis as HlookupPartBis. subst pdentry. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentry. auto.
  }
  destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HstructEq)]. rewrite HstructEq in *.
  specialize(Hcons0 partition pdentryParts0 HlookupParts0 HbeqStructNull). unfold isKS in *. simpl.
  destruct (beqAddr pdpart (structure pdentryParts0)) eqn:HbeqPartStruct.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartStruct. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END StructurePointerIsKS *)
}

assert(NextKSIsKS newS).
{ (* BEGIN NextKSIsKS newS *)
  assert(Hcons0: NextKSIsKS s) by intuition.
  intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull. unfold isKS in *.
  assert(HlookupKernEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart kernel) eqn:HbeqPartKern; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold nextKSAddr in *. rewrite HlookupKernEq in *. unfold nextKSentry in *. simpl in HnextKSAddr.
  destruct (beqAddr pdpart nextKSaddr) eqn:HbeqPartNextKS; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull). unfold isKS in *. simpl.
  destruct (beqAddr pdpart nextKS) eqn:HbeqPartNext.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END NextKSIsKS *)
}

assert(NextKSOffsetIsPADDR newS).
{ (* BEGIN NextKSOffsetIsPADDR newS *)
  assert(Hcons0: NextKSOffsetIsPADDR s) by intuition. intros kernel nextKSaddr HkernIsKS HnextAddr. unfold isKS in *.
  assert(HlookupKernEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart kernel) eqn:HbeqPartKern; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold nextKSAddr in *. rewrite HlookupKernEq in *. specialize(Hcons0 kernel nextKSaddr HkernIsKS HnextAddr).
  destruct Hcons0 as (HnextIsPADDR & HbeqNextNull). split; trivial. unfold isPADDR in *. simpl.
  destruct (beqAddr pdpart nextKSaddr) eqn:HbeqPartNext.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END NextKSOffsetIsPADDR *)
}

assert(HgetFreeEq: forall partition, getFreeSlotsList partition newS = getFreeSlotsList partition s).
{
  unfold getFreeSlotsList. intro partition. simpl. destruct (beqAddr pdpart partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart. simpl.
    destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial. apply getFreeSlotsListRecEqPDT.
    2,3: unfold isBE; unfold isPADDR; rewrite HlookupPart; intuition. rewrite <-beqAddrFalse in *.
    assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
    specialize(HfirstIsBE pdpart p HlookupPart HbeqFirstNull). destruct HfirstIsBE as (HfirstIsBE & _).
    intro Hcontra. rewrite Hcontra in *. unfold isBE in *. rewrite HlookupPart in *. congruence.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    destruct (lookup partition (memory s) beqAddr) eqn:HlookupPartBis; trivial. destruct v; trivial.
    destruct (beqAddr (firstfreeslot p0) nullAddr) eqn:HbeqFirstNull; trivial. apply getFreeSlotsListRecEqPDT.
    2,3: unfold isBE; unfold isPADDR; rewrite HlookupPart; intuition. rewrite <-beqAddrFalse in *.
    assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s) by intuition.
    specialize(HfirstIsBE partition p0 HlookupPartBis HbeqFirstNull). destruct HfirstIsBE as (HfirstIsBE & _).
    intro Hcontra. rewrite Hcontra in *. unfold isBE in *. rewrite HlookupPart in *. congruence.
}

assert(NoDupInFreeSlotsList newS).
{ (* BEGIN NoDupInFreeSlotsList newS *)
  assert(Hcons0: NoDupInFreeSlotsList s) by intuition. intros partition pdentry HlookupPartBis.
  assert(HlookupParts0: exists pdentrys0, lookup partition (memory s) beqAddr = Some (PDT pdentrys0)).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentry. assumption.
  }
  destruct HlookupParts0 as [pdentryParts0 HlookupParts0]. specialize(Hcons0 partition pdentryParts0 HlookupParts0).
  rewrite HgetFreeEq. assumption.
  (* END NoDupInFreeSlotsList *)
}

assert(freeSlotsListIsFreeSlot newS).
{ (* BEGIN freeSlotsListIsFreeSlot newS *)
  assert(Hcons0: freeSlotsListIsFreeSlot s) by intuition.
  intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
  rewrite HgetFreeEq in *. assert(HpartIsPDTs0: isPDT partition s).
  {
    unfold isPDT in *. simpl in HpartIsPDT. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDTs0 HwellFormed HaddrInList
    HbeqAddrNull). unfold isFreeSlot in *. simpl. destruct (beqAddr pdpart addr) eqn:HbeqPartAddr.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup addr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  destruct (beqAddr pdpart (CPaddr (addr + sh1offset))) eqn:HbeqPartSh1.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartSh1. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup (CPaddr (addr + sh1offset)) (memory s) beqAddr); try(congruence).
  destruct v; try(congruence).
  destruct (beqAddr pdpart (CPaddr (addr + scoffset))) eqn:HbeqPartSce.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartSce. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END freeSlotsListIsFreeSlot *)
}

assert(DisjointFreeSlotsLists newS).
{ (* BEGIN DisjointFreeSlotsLists newS *)
  assert(Hcons0: DisjointFreeSlotsLists s) by intuition. intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
  rewrite HgetFreeEq. rewrite HgetFreeEq. assert(Hpart1IsPDTs0: isPDT part1 s).
  {
    unfold isPDT in *. simpl in Hpart1IsPDT. destruct (beqAddr pdpart part1) eqn:HbeqPdPart.
    - rewrite <-DTL.beqAddrTrue in HbeqPdPart. subst part1. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(Hpart2IsPDTs0: isPDT part2 s).
  {
    unfold isPDT in *. simpl in Hpart2IsPDT. destruct (beqAddr pdpart part2) eqn:HbeqPdPart.
    - rewrite <-DTL.beqAddrTrue in HbeqPdPart. subst part2. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts). assumption.
  (* END DisjointFreeSlotsLists *)
}

assert(inclFreeSlotsBlockEntries newS).
{ (* BEGIN inclFreeSlotsBlockEntries newS *)
  assert(Hcons0: inclFreeSlotsBlockEntries s) by intuition. intros partition HpartIsPDT. rewrite HgetKSEq.
  rewrite HgetFreeEq. assert(HpartIsPDTs0: isPDT partition s).
  {
    unfold isPDT in *. simpl in HpartIsPDT. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition HpartIsPDTs0). assumption.
  (* END inclFreeSlotsBlockEntries *)
}

assert(DisjointKSEntries newS).
{ (* BEGIN DisjointKSEntries newS *)
  assert(Hcons0: DisjointKSEntries s) by intuition. intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
  rewrite HgetKSEq. rewrite HgetKSEq. assert(Hpart1IsPDTs0: isPDT part1 s).
  {
    unfold isPDT in *. simpl in Hpart1IsPDT. destruct (beqAddr pdpart part1) eqn:HbeqPdPart.
    - rewrite <-DTL.beqAddrTrue in HbeqPdPart. subst part1. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(Hpart2IsPDTs0: isPDT part2 s).
  {
    unfold isPDT in *. simpl in Hpart2IsPDT. destruct (beqAddr pdpart part2) eqn:HbeqPdPart.
    - rewrite <-DTL.beqAddrTrue in HbeqPdPart. subst part2. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts). assumption.
  (* END DisjointKSEntries *)
}

assert(noDupPartitionTree newS).
{ (* BEGIN noDupPartitionTree newS *)
  assert(Hcons0: noDupPartitionTree s) by intuition. unfold noDupPartitionTree in *. rewrite HgetPartsEq. assumption.
  (* END noDupPartitionTree *)
}

assert(isParent newS).
{ (* BEGIN isParent newS *)
  assert(Hcons0: isParent s) by intuition. intros partition pdparent HparentIsPart HpartIsChild.
  rewrite HgetPartsEq in *. rewrite HgetChildrenEq in *.
  specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent in *. simpl.
  destruct (beqAddr pdpart partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart in *. simpl. assumption.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END isParent *)
}

assert(isChild newS).
{ (* BEGIN isChild newS *)
  assert(Hcons0: isChild s) by intuition. intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot.
  rewrite HgetPartsEq in *. rewrite HgetChildrenEq.
  assert(HparentIsParents0: pdentryParent partition pdparent s).
  {
    unfold pdentryParent in *. simpl in HparentIsParent. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart in *. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition pdparent HpartIsPart HparentIsParents0 HbeqPartRoot). assumption.
  (* END isChild *)
}

assert(noDupKSEntriesList newS).
{ (* BEGIN noDupKSEntriesList newS *)
  assert(Hcons0: noDupKSEntriesList s) by intuition. intros partition HpartIsPDT.
  rewrite HgetKSEq. assert(HpartIsPDTs0: isPDT partition s).
  {
    unfold isPDT in *. simpl in HpartIsPDT. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition HpartIsPDTs0). assumption.
  (* END noDupKSEntriesList *)
}

assert(noDupMappedBlocksList newS).
{ (* BEGIN noDupMappedBlocksList newS *)
  assert(Hcons0: noDupMappedBlocksList s) by intuition. intros partition HpartIsPDT.
  rewrite HgetMappedBEq. assert(HpartIsPDTs0: isPDT partition s).
  {
    unfold isPDT in *. simpl in HpartIsPDT. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition HpartIsPDTs0). assumption.
  (* END noDupMappedBlocksList *)
}

assert(wellFormedBlock newS).
{ (* BEGIN wellFormedBlock newS *)
  assert(Hcons0: wellFormedBlock s) by intuition. intros block startaddr endaddr HPflag HstartBlock HendBlock.
  unfold bentryPFlag in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockEq in *.
  specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
  (* END wellFormedBlock *)
}

assert(parentOfPartitionIsPartition newS).
{ (* BEGIN parentOfPartitionIsPartition newS *)
  assert(Hcons0: parentOfPartitionIsPartition s) by intuition. intros partition pdentry HlookupPartBis.
  assert(HlookupParts0: exists pdentrys0, lookup partition (memory s) beqAddr = Some (PDT pdentrys0)
    /\ parent pdentry = parent pdentrys0).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. split; trivial.
      injection HlookupPartBis as HlookupPartBis. subst pdentry. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentry. auto.
  }
  destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentEq)]. rewrite HparentEq in *.
  specialize(Hcons0 partition pdentryParts0 HlookupParts0). destruct Hcons0 as (HparentIsPart & Hrest).
  split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
  destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEq. split; trivial.
  simpl. destruct (beqAddr pdpart (parent pdentryParts0)) eqn:HbeqPartParent.
  - exists {|
             structure := structure p;
             firstfreeslot := firstfreeslot p;
             nbfreeslots := nbfreeslots p;
             nbprepare := nbprepare p;
             parent := parent p;
             MPU := MPU p;
             vidtAddr := vidtaddr
           |}. reflexivity.
  - rewrite <-beqAddrFalse in *. exists parentEntry. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END parentOfPartitionIsPartition *)
}

assert(NbFreeSlotsISNbFreeSlotsInList newS).
{ (* BEGIN NbFreeSlotsISNbFreeSlotsInList newS *)
  assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s) by intuition. intros partition nbfreeslots HpartIsPDT HnbFree.
  rewrite HgetFreeEq. assert(Hparts0: isPDT partition s /\ pdentryNbFreeSlots partition nbfreeslots s).
  {
    unfold isPDT in *. unfold pdentryNbFreeSlots in *. simpl in *. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct Hparts0 as (HpartIsPDTs0 & HnbFrees0). specialize(Hcons0 partition nbfreeslots HpartIsPDTs0 HnbFrees0).
  assumption.
  (* END NbFreeSlotsISNbFreeSlotsInList *)
}

assert(maxNbPrepareIsMaxNbKernels newS).
{ (* BEGIN maxNbPrepareIsMaxNbKernels newS *)
  assert(Hcons0: maxNbPrepareIsMaxNbKernels s) by intuition. intros partition kernList HlistOfKerns.
  apply isListOfKernelsEqPDT with partition pdpart {|
                                                     structure := structure p;
                                                     firstfreeslot := firstfreeslot p;
                                                     nbfreeslots := nbfreeslots p;
                                                     nbprepare := nbprepare p;
                                                     parent := parent p;
                                                     MPU := MPU p;
                                                     vidtAddr := vidtaddr
                                                   |} kernList p s in HlistOfKerns; trivial.
  specialize(Hcons0 partition kernList HlistOfKerns). assumption.
  (* END maxNbPrepareIsMaxNbKernels *)
}

assert(blockInChildHasAtLeastEquivalentBlockInParent newS).
{ (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent newS *)
  assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s) by intuition. intros pdparent child block startChild
    endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild.
  rewrite HgetPartsEq in *. rewrite HgetChildrenEq in *. rewrite HgetMappedBEq in *. unfold bentryPFlag in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockEq in *.
  specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild
    HendChild HPflagChild).
  destruct Hcons0 as [blockParent [startParent [endParent (HblockPMapped & HstartP & HendP & Hbounds)]]].
  exists blockParent. exists startParent. exists endParent. unfold bentryStartAddr in *. simpl.
  destruct (beqAddr pdpart blockParent) eqn:HbeqPartBlockP.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartBlockP. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
  (* END blockInChildHasAtLeastEquivalentBlockInParent *)
}

assert(partitionTreeIsTree newS).
{ (* BEGIN partitionTreeIsTree newS *)
  assert(Hcons0: partitionTreeIsTree s) by intuition.
  intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
  rewrite HgetPartsEq in *. assert(HparentIsParents0: pdentryParent child pdparent s).
  {
    unfold pdentryParent in *. simpl in HparentIsParent. destruct (beqAddr pdpart child) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst child. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HparentsLists0: isParentsList s parentsList pdparent).
  {
    revert HparentsList. apply isParentsListEqPDTSameParent with pdpart {|
                                                                          structure := structure p;
                                                                          firstfreeslot := firstfreeslot p;
                                                                          nbfreeslots := nbfreeslots p;
                                                                          nbprepare := nbprepare p;
                                                                          parent := parent p;
                                                                          MPU := MPU p;
                                                                          vidtAddr := vidtaddr
                                                                        |}; trivial.
    - simpl. destruct (beqAddr pdpart pdparent) eqn:HbeqParts.
      + rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdpart. exists p. exists {|
                                                                                 structure := structure p;
                                                                                 firstfreeslot := firstfreeslot p;
                                                                                 nbfreeslots := nbfreeslots p;
                                                                                 nbprepare := nbprepare p;
                                                                                 parent := parent p;
                                                                                 MPU := MPU p;
                                                                                 vidtAddr := vidtaddr
                                                                               |}. exists p. split; trivial.
        split; trivial. split; trivial. split; trivial. split; intro Heq; try(exfalso; congruence). split; trivial.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        assert(HparentOfPart: parentOfPartitionIsPartition s) by intuition. unfold pdentryParent in *.
        destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst pdparent. specialize(HparentOfPart child p0 HlookupChild).
        destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqChildRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & _). exists parentEntry. exists parentEntry.
        exists p. split; trivial. split; trivial. split; trivial. split; trivial.
        split; intro Heq; try(exfalso; congruence). reflexivity.
    - intuition.
  }
  specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParents0 HparentsLists0).
  assumption.
  (* END partitionTreeIsTree *)
}

assert(kernelEntriesAreValid newS).
{ (* BEGIN kernelEntriesAreValid newS *)
  assert(Hcons0: kernelEntriesAreValid s) by intuition. intros kernel idx HkernIsKS Hidx. unfold isKS in *.
  assert(HlookupKernEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart kernel) eqn:HbeqPartKern; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HlookupKernEq in *. specialize(Hcons0 kernel idx HkernIsKS Hidx). unfold isBE in *. simpl.
  destruct (beqAddr pdpart (CPaddr (kernel + idx))) eqn:HbeqPartIdx.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartIdx. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END kernelEntriesAreValid *)
}

assert(nextKernelIsValid newS).
{ (* BEGIN nextKernelIsValid newS *)
  assert(Hcons0: nextKernelIsValid s) by intuition. intros kernel HkernIsKS. unfold isKS in *.
  assert(HlookupKernEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart kernel) eqn:HbeqPartKern; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HlookupKernEq in *. specialize(Hcons0 kernel HkernIsKS).
  destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]). split; trivial. exists nextAddr. split.
  - intro Hp. specialize(HlookupNext Hp). simpl.
    destruct (beqAddr pdpart {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqPartNext.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst pdpart. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - destruct Hnext as [HnextIsKS | HnextIsNull]; try(right; assumption). left. simpl. unfold isKS in *.
    destruct (beqAddr pdpart nextAddr) eqn:HbeqPartNext.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst pdpart. rewrite HlookupPart in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END nextKernelIsValid *)
}

assert(noDupListOfKerns newS).
{ (* BEGIN noDupListOfKerns newS *)
  assert(Hcons0: noDupListOfKerns s) by intuition. intros partition kernList HlistOfKerns.
  apply isListOfKernelsEqPDT with partition pdpart {|
                                                     structure := structure p;
                                                     firstfreeslot := firstfreeslot p;
                                                     nbfreeslots := nbfreeslots p;
                                                     nbprepare := nbprepare p;
                                                     parent := parent p;
                                                     MPU := MPU p;
                                                     vidtAddr := vidtaddr
                                                   |} kernList p s in HlistOfKerns; trivial.
  specialize(Hcons0 partition kernList HlistOfKerns). assumption.
  (* END noDupListOfKerns *)
}

assert(MPUsizeIsBelowMax newS).
{ (* BEGIN MPUsizeIsBelowMax newS *)
  assert(Hcons0: MPUsizeIsBelowMax s) by intuition. intros partition MPUlist HMPU.
  assert(HMPUs0: pdentryMPU partition MPUlist s).
  {
    unfold pdentryMPU in *. simpl in HMPU. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition MPUlist HMPUs0). assumption.
  (* END MPUsizeIsBelowMax *)
}

assert(originIsParentBlocksStart newS).
{ (* BEGIN originIsParentBlocksStart newS *)
  assert(Hcons0: originIsParentBlocksStart s) by intuition.
  intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPartBis HblockMapped Hsce Horigin.
  assert(HlookupParts0: exists pdentrys0, lookup partition (memory s) beqAddr = Some (PDT pdentrys0)
    /\ parent pdentry = parent pdentrys0).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. split; trivial.
      injection HlookupPartBis as HlookupPartBis. subst pdentry. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentry. auto.
  }
  destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentEq)]. rewrite HparentEq in *.
  rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. unfold scentryOrigin in *. simpl in Horigin.
  destruct (beqAddr pdpart scentryaddr) eqn:HbeqPartSce; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 partition pdentryParts0 block scentryaddr scorigin HpartIsPart HlookupParts0 HblockMapped Hsce
    Horigin). destruct Hcons0 as (HblockP & HlebOriginStart). split.
  - intro HbeqPartRoot. specialize(HblockP HbeqPartRoot).
    destruct HblockP as [blockParent (HblockPMapped & HstartP & Hincl)]. exists blockParent. split; trivial.
    unfold bentryStartAddr in *. simpl. destruct (beqAddr pdpart blockParent) eqn:HbeqPartBlockP.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartBlockP. subst pdpart. rewrite HlookupPart in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial.
    intros addr HaddrIn. destruct (beqAddr pdpart block) eqn:HbeqPartBlk; try(simpl in HaddrIn; exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in Hincl.
    apply Hincl; assumption.
  - intros startaddr Hstart. apply HlebOriginStart. unfold bentryStartAddr in *. simpl in Hstart.
    destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END originIsParentBlocksStart *)
}

assert(nextImpliesBlockWasCut newS).
{ (* BEGIN nextImpliesBlockWasCut newS *)
  assert(Hcons0: nextImpliesBlockWasCut s) by intuition.
  intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPartBis HblockMapped HendBlock Hsce
    HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *.
  assert(HlookupParts0: exists pdentrys0, lookup partition (memory s) beqAddr = Some (PDT pdentrys0)
    /\ parent pdentry = parent pdentrys0).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. split; trivial.
      injection HlookupPartBis as HlookupPartBis. subst pdentry. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentry. auto.
  }
  destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentEq)]. rewrite HparentEq in *.
  unfold bentryEndAddr in *. unfold scentryNext in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl. simpl in HendBlock. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HlookupBlockEq in *. simpl in Hnext.
  destruct (beqAddr pdpart scentryaddr) eqn:HbeqPartSce; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 partition pdentryParts0 block scentryaddr scnext endaddr HpartIsPart HlookupParts0 HblockMapped
    HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
  destruct Hcons0 as [blockParent [endParent (HblockPMapped & HendP & HltEnd & Hincl)]]. exists blockParent.
  exists endParent. split; trivial. unfold getAllPaddrAux. rewrite HlookupBlockEq. unfold bentryEndAddr in *. simpl.
  destruct (beqAddr pdpart blockParent) eqn:HbeqPartBlockP.
  {
    exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartBlockP. subst pdpart. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. auto.
  (* END nextImpliesBlockWasCut *)
}

assert(blocksAddressesTypes newS).
{ (* BEGIN blocksAddressesTypes newS *)
  assert(Hcons0: blocksAddressesTypes s) by intuition.
  intros block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock. unfold bentryPFlag in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockEq in *. unfold sh1entryPDchild in *.
  simpl in HPDchildBlock.
  destruct (beqAddr pdpart (CPaddr (block+sh1offset))) eqn:HbeqPartSh1; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock).
  destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hrange]].
  - left. split.
    + unfold isKS in *. simpl. destruct (beqAddr pdpart startaddr) eqn:HbeqPartStart.
      {
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartStart. subst pdpart. rewrite HlookupPart in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    + intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
      destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
      * left. unfold isBE in *. simpl. destruct (beqAddr pdpart addr) eqn:HbeqPartAddr.
        {
          exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst pdpart. rewrite HlookupPart in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      * right. left. unfold isSHE in *. simpl. destruct (beqAddr pdpart addr) eqn:HbeqPartAddr.
        {
          exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst pdpart. rewrite HlookupPart in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      * right. right. left. unfold isSCE in *. simpl. destruct (beqAddr pdpart addr) eqn:HbeqPartAddr.
        {
          exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst pdpart. rewrite HlookupPart in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      * right. right. right. left. unfold isPADDR in *. simpl. destruct (beqAddr pdpart addr) eqn:HbeqPartAddr.
        {
          exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst pdpart. rewrite HlookupPart in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      * right. right. right. right. simpl. destruct (beqAddr pdpart addr) eqn:HbeqPartAddr.
        {
          exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst pdpart. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - right. left. split.
    + unfold isPDT in *. simpl. destruct (beqAddr pdpart startaddr) eqn:HbeqPartStart; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    + intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). simpl.
      destruct (beqAddr pdpart addr) eqn:HbeqPartAddr.
      {
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst pdpart. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - right. right. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). simpl.
    destruct (beqAddr pdpart addr) eqn:HbeqPartAddr.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst pdpart. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END blocksAddressesTypes *)
}

assert(notPDTIfNotPDflag newS).
{ (* BEGIN notPDTIfNotPDflag newS *)
  assert(Hcons0: notPDTIfNotPDflag s) by intuition.
  intros block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild. unfold bentryPFlag in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryStartAddr in *. unfold sh1entryAddr in *. rewrite HlookupBlockEq in *. unfold sh1entryPDchild in *.
  unfold sh1entryPDflag in *. simpl in HPDchild. simpl in HPDflag.
  destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqPartSh1; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild). unfold isPDT in *.
  simpl. contradict Hcons0. destruct (beqAddr pdpart startaddr) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst startaddr. rewrite HlookupPart. trivial.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END notPDTIfNotPDflag *)
}

assert(nextKernAddrIsInSameBlock newS).
{ (* BEGIN nextKernAddrIsInSameBlock newS *)
  assert(Hcons0: nextKernAddrIsInSameBlock s) by intuition.
  intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HnextInRange HkernIsKS.
  unfold bentryPFlag in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockEq in *. unfold sh1entryPDchild in *.
  simpl in HnextInRange.
  destruct (beqAddr pdpart (CPaddr (block + sh1offset))) eqn:HbeqPartSh1; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold isKS in *.
  assert(HlookupKernEq: lookup kernel (memory newS) beqAddr = lookup kernel (memory s) beqAddr).
  {
    simpl in HkernIsKS. simpl. destruct (beqAddr pdpart kernel) eqn:HbeqPartKern; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HlookupKernEq in *. specialize(Hcons0 block kernel startaddr endaddr). apply Hcons0; assumption.
  (* END nextKernAddrIsInSameBlock *)
}

assert(blockBelongsToAPart newS).
{ (* BEGIN blockBelongsToAPart newS *)
  assert(Hcons0: blockBelongsToAPart s) by intuition. intros block HPflagBlock. unfold bentryPFlag in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HlookupBlockEq in *. specialize(Hcons0 block HPflagBlock). rewrite HgetPartsEq.
  destruct Hcons0 as [part (HpartIsPart & HblockMapped)]. exists part. rewrite HgetMappedBEq. auto.
  (* END blockBelongsToAPart *)
}

assert(PDflagMeansNoChild newS).
{ (* BEGIN PDflagMeansNoChild newS *)
  assert(Hcons0: PDflagMeansNoChild s) by intuition. intros block HblockIsBE HPDflagBlock. unfold isBE in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HlookupBlockEq in *. unfold sh1entryPDflag in *. unfold sh1entryPDchild. simpl in HPDflagBlock. simpl.
  destruct (beqAddr pdpart (CPaddr (block + sh1offset))) eqn:HbeqPartSh1; try(congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block HblockIsBE HPDflagBlock). assumption.
  (* END PDflagMeansNoChild *)
}

assert(nbPrepareIsNbKern newS).
{ (* BEGIN nbPrepareIsNbKern newS *)
  assert(Hcons0: nbPrepareIsNbKern s) by intuition. intros partition pdentry HlookupPartBis.
  assert(HlookupParts0: exists pdentrys0, lookup partition (memory s) beqAddr = Some (PDT pdentrys0)
    /\ structure pdentry = structure pdentrys0 /\ nbprepare pdentry = nbprepare pdentrys0).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. split; trivial.
      injection HlookupPartBis as HlookupPartBis. subst pdentry. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentry. auto.
  }
  destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HstructEq & HnbPrepEq)]. rewrite HstructEq in *.
  rewrite HnbPrepEq in *. specialize(Hcons0 partition pdentryParts0 HlookupParts0). unfold newS.
  rewrite completeListOfKernelsEqPDT; try(unfold isPDT; rewrite HlookupPart; trivial). assumption.
 (* END nbPrepareIsNbKern *)
}

assert(pdchildIsPDT newS).
{ (* BEGIN pdchildIsPDT newS *)
  assert(Hcons0: pdchildIsPDT s) by intuition.
  intros part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
  rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. rewrite HgetChildrenEq. unfold sh1entryAddr in *.
  unfold sh1entryPDchild in *. simpl in *.
  destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
  destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqPartSh1; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull).
  assumption.
  (* END pdchildIsPDT *)
}

assert(childBlockNullIfChildNull newS).
{ (* BEGIN childBlockNullIfChildNull newS *)
  assert(Hcons0: childBlockNullIfChildNull s) by intuition.
  intros part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchild. rewrite HgetPartsEq in *.
  rewrite HgetMappedBEq in *. unfold sh1entryAddr in *. unfold sh1entryPDchild in *. unfold sh1entryInChildLocation.
  simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
  destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqPartSh1; try(congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchild).
  unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence).
  destruct v; try(congruence). destruct Hcons0. split; trivial. intro. exfalso; congruence.
  (* END childBlockNullIfChildNull *)
}

assert(accessibleBlocksArePresent newS).
{ (* BEGIN accessibleBlocksArePresent newS *)
  assert(Hcons0: accessibleBlocksArePresent s) by intuition. intros block HAflag. unfold bentryAFlag in *.
  unfold bentryPFlag. simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. apply Hcons0; assumption.
  (* END accessibleBlocksArePresent *)
}

assert(noDupMappedPaddrList newS).
{ (* BEGIN noDupMappedPaddrList newS *)
  assert(Hcons0: noDupMappedPaddrList s) by intuition. intros partition HpartIsPDT. rewrite HgetMappedPEq.
  assert(HpartIsPDTs0: isPDT partition s).
  {
    unfold isPDT in *. simpl in HpartIsPDT. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupPart. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition HpartIsPDTs0). assumption.
  (* END noDupMappedPaddrList *)
}

assert(accessibleParentPaddrIsAccessibleIntoChild newS).
{ (* BEGIN accessibleParentPaddrIsAccessibleIntoChild newS *)
  assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s) by intuition.
  intros pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
  rewrite HgetPartsEq in *. rewrite HgetChildrenEq in *. rewrite HgetAccMappedPEq in *. rewrite HgetMappedPEq in *.
  specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild). trivial.
  (* END accessibleParentPaddrIsAccessibleIntoChild *)
}

assert(sharedBlockPointsToChild newS).
{ (* BEGIN sharedBlockPointsToChild newS *)
  assert(Hcons0: sharedBlockPointsToChild s) by intuition.
  intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild HaddrInBlockParent
    HblockParentMapped Hsh1. unfold getUsedPaddr in *. rewrite HgetPartsEq in *. rewrite HgetChildrenEq in *.
  rewrite HgetConfigPEq in *; try(apply childrenArePDT with pdparent; intuition). rewrite HgetMappedPEq in *.
  rewrite HgetMappedBEq in *. unfold sh1entryAddr in *.
  assert(HlookupBlockPEq: lookup blockParent (memory newS) beqAddr = lookup blockParent (memory s) beqAddr).
  {
    simpl in *. destruct (beqAddr pdpart blockParent) eqn:HbeqPartBlockP; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold getAllPaddrAux in HaddrInBlockParent. rewrite HlookupBlockPEq in *.
  specialize(Hcons0 pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
    HaddrInBlockParent HblockParentMapped Hsh1). unfold sh1entryPDchild in *. unfold sh1entryPDflag in *. simpl.
  destruct (beqAddr pdpart (CPaddr (blockParent+sh1offset))) eqn:HbeqPartSh1.
  {
    left. rewrite <-DTL.beqAddrTrue in HbeqPartSh1. subst pdpart. rewrite HlookupPart in *. destruct Hcons0; trivial.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END sharedBlockPointsToChild *)
}

assert(adressesRangePreservedIfOriginAndNextOk newS).
{ (* BEGIN adressesRangePreservedIfOriginAndNextOk newS *)
  assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s) by intuition.
  intros partition pdentry block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE HstartBlock
    HendBlock HPflag Hsce Horigin Hnext HlookupPartBis HbeqPartRoot. rewrite HgetPartsEq in *. unfold isBE in *.
  assert(HlookupBlockEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in HblockIsBE. simpl. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite HlookupBlockEq in *.
  rewrite HgetMappedBEq in *. unfold scentryNext in *. unfold scentryOrigin in *. simpl in Hnext. simpl in Horigin.
  destruct (beqAddr pdpart scentryaddr) eqn:HbeqPartSce; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  assert(HlookupParts0: exists pdentrys0, lookup partition (memory s) beqAddr = Some (PDT pdentrys0)
    /\ parent pdentry = parent pdentrys0).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. split; trivial.
      injection HlookupPartBis as HlookupPartBis. subst pdentry. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentry. auto.
  }
  destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentEq)]. rewrite HparentEq in *.
  specialize(Hcons0 partition pdentryParts0 block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE
    HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupParts0 HbeqPartRoot).
  destruct Hcons0 as [blockParent (HblockPMapped & HblockPIsBE & HstartP & HendP)]. exists blockParent. simpl.
  unfold isBE in *. destruct (beqAddr pdpart blockParent) eqn:HbeqPartBlockP.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPartBlockP. subst pdpart. rewrite HlookupPart in *. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
  (* END adressesRangePreservedIfOriginAndNextOk *)
}

assert(childsBlocksPropsInParent newS).
{ (* BEGIN childsBlocksPropsInParent newS *)
  assert(Hcons0: childsBlocksPropsInParent s) by intuition.
  intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart HchildIsChild
    HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent HPflagParent
    HlebStart HgebEnd. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. unfold bentryPFlag in *.
  assert(HlookupBlockChildEq: lookup blockChild (memory newS) beqAddr = lookup blockChild (memory s) beqAddr).
  {
    simpl in HPflagChild. simpl. destruct (beqAddr pdpart blockChild) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HlookupBlockPEq: lookup blockParent (memory newS) beqAddr = lookup blockParent (memory s) beqAddr).
  {
    simpl in HPflagParent. simpl. destruct (beqAddr pdpart blockParent) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockChildEq in *.
  rewrite HlookupBlockPEq in *. rewrite HgetChildrenEq in *.
  specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
    HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
    HPflagParent HlebStart HgebEnd).
  destruct Hcons0 as (HcheckChild & HchildNotNull & HlocIsChild & Hbounds).
  assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry newS) by assumption. assert(HblockPIsBE: isBE blockParent newS).
  {
    unfold isBE. rewrite HlookupBlockPEq. destruct (lookup blockParent (memory s) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  specialize(Hsh1IsSHE blockParent HblockPIsBE). unfold isSHE in *.
  assert(HlookupSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory newS) beqAddr
    = lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr).
  {
    simpl. simpl in Hsh1IsSHE.
    destruct (beqAddr pdpart (CPaddr (blockParent+sh1offset))) eqn:HbeqPartSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  unfold checkChild in *. unfold sh1entryPDchild in *. unfold sh1entryInChildLocation in *. rewrite HlookupSh1Eq.
  rewrite HlookupBlockPEq. split; trivial. split; trivial. split.
  - intros blockIDInChild HchildLoc.
    assert(HchildLocs0: sh1entryInChildLocation (CPaddr (blockParent + sh1offset)) blockIDInChild s).
    {
      unfold sh1entryInChildLocation.
      destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial. intro HbeqLocNull.
      specialize(HlocIsBE HbeqLocNull). unfold isBE in *. simpl in HlocIsBE.
      destruct (beqAddr pdpart blockIDInChild) eqn:HbeqPartLoc; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    apply HlocIsChild; assumption.
  - intro HboundsWrong. specialize(Hbounds HboundsWrong). unfold bentryAFlag. rewrite HlookupBlockPEq. assumption.
  (* END childsBlocksPropsInParent *)
}

assert(noChildImpliesAddressesNotShared newS).
{ (* BEGIN noChildImpliesAddressesNotShared newS *)
  assert(Hcons0: noChildImpliesAddressesNotShared s) by intuition.
  intros partition pdentry block sh1entryaddr HpartIsPart HlookupPartBis HblockMapped Hsh1 HPDchild child addr
    HchildIsChild HaddrInBlock. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. rewrite HgetChildrenEq in *.
  assert(HlookupParts0: exists pdentrys0, lookup partition (memory s) beqAddr = Some (PDT pdentrys0)).
  {
    simpl in HlookupPartBis. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists p. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      exists pdentry. assumption.
  }
  destruct HlookupParts0 as [pdentryParts0 HlookupParts0]. rewrite HgetMappedPEq. unfold sh1entryPDchild in *.
  simpl in HPDchild. destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqPartSh1; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s)).
  {
    simpl. simpl in HaddrInBlock.
    destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(simpl in HaddrInBlock; exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition pdentryParts0 block sh1entryaddr HpartIsPart HlookupParts0 HblockMapped Hsh1 HPDchild
    child addr HchildIsChild HaddrInBlocks0). assumption.
  (* END noChildImpliesAddressesNotShared *)
}

assert(kernelsAreNotAccessible newS).
{ (* BEGIN kernelsAreNotAccessible newS *)
  assert(Hcons0: kernelsAreNotAccessible s) by intuition. intros block startaddr Hstart HPflag HstartIsKS.
  unfold bentryPFlag in *. assert(HlookupBlkEq: lookup block (memory newS) beqAddr = lookup block (memory s) beqAddr).
  {
    simpl in HPflag. simpl. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryAFlag. rewrite HlookupBlkEq in *.
  unfold isKS in *. simpl in HstartIsKS.
  destruct (beqAddr pdpart startaddr) eqn:HbeqPartStart; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block startaddr Hstart HPflag HstartIsKS). assumption.
  (* END kernelsAreNotAccessible *)
}

assert(blockAndNextAreSideBySide newS).
{ (* BEGIN blockAndNextAreSideBySide newS *)
  assert(Hcons0: blockAndNextAreSideBySide s) by intuition.
  intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
    Hnext. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. unfold bentryEndAddr in *. unfold scentryNext in *.
  simpl in *. destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
  destruct (beqAddr pdpart scentryaddr) eqn:HbeqPartSce; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
    Hnext). unfold bentryStartAddr in *. simpl. destruct (beqAddr pdpart scnext) eqn:HbeqPartNext.
  { rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst scnext. rewrite HlookupPart in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END blockAndNextAreSideBySide *)
}

assert(parentBlocksBoundsIfNoNext newS).
{ (* BEGIN parentBlocksBoundsIfNoNext newS *)
  assert(Hcons0: parentBlocksBoundsIfNoNext s) by intuition.
  intros partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock HendBlock Hsce
    Hnext HbeqPartRoot HlookupPartBis. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *.
  assert(HlookupPartBiss: exists pdentrys, lookup partition (memory s) beqAddr = Some (PDT pdentrys)
    /\ parent pdentry = parent pdentrys).
  {
    simpl in *. destruct (beqAddr pdpart partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPartBis as HpdentriesEq.
      subst pdentry. exists p. auto.
    - exists pdentry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct HlookupPartBiss as [pdentrys (HlookupPartBiss & HparentsEq)]. rewrite HparentsEq. clear HlookupPartBis.
  unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold scentryNext in *. simpl in *.
  destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
  destruct (beqAddr pdpart scentryaddr) eqn:HbeqPartSce; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 partition pdentrys block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock
    HendBlock Hsce Hnext HbeqPartRoot HlookupPartBiss).
  destruct Hcons0 as [blockParent [startP (HblockPMapped & HstartP & HendP & HlebStarts)]]. exists blockParent.
  exists startP. destruct (beqAddr pdpart blockParent) eqn:HbeqPartBP.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPartBP. subst blockParent. unfold bentryEndAddr in *. rewrite HlookupPart in *.
    exfalso; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
  (* END parentBlocksBoundsIfNoNext *)
}

assert(childLocMappedInChild newS).
{ (* BEGIN childLocMappedInChild newS *)
  assert(Hcons0: childLocMappedInChild s) by intuition.
  intros part block sh1entryaddr blockChild idchild startaddr HpartIsPart HblockMapped Hsh1 HPDchild Hloc
    HbeqIdChildNull Hstart HstartNotKS.
  rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. unfold sh1entryAddr in *. unfold sh1entryPDchild in *.
  unfold sh1entryInChildLocationWeak in *. unfold bentryStartAddr in Hstart. simpl in *.
  destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
  destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqPartSh1; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  assert(HstartNotKSs: ~isKS startaddr s).
  {
    contradict HstartNotKS. unfold isKS in *. simpl. destruct (beqAddr pdpart startaddr) eqn:HbeqPartStart.
    { rewrite <-DTL.beqAddrTrue in HbeqPartStart. subst startaddr. rewrite HlookupPart in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 part block sh1entryaddr blockChild idchild startaddr HpartIsPart HblockMapped Hsh1 HPDchild Hloc
    HbeqIdChildNull Hstart HstartNotKSs). destruct Hcons0 as (HbeqBCNull & HBCMapped & HstartChild). split; trivial.
  split; trivial. unfold bentryStartAddr in *. simpl.
  destruct (beqAddr pdpart blockChild) eqn:HbeqPartBC.
  { rewrite <-DTL.beqAddrTrue in HbeqPartBC. subst blockChild. rewrite HlookupPart in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END childLocMappedInChild *)
}

assert(childLocHasSameStart newS).
{ (* BEGIN childLocHasSameStart newS *)
  assert(Hcons0: childLocHasSameStart s) by intuition.
  intros part block sh1entryaddr blockChild idchild HpartIsPart HblockMapped Hsh1 HPDchild Hloc
    HbeqIdChildNull HbeqBCNull startaddr Hstart.
  rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. unfold sh1entryAddr in *. unfold sh1entryPDchild in *.
  unfold sh1entryInChildLocationWeak in *. unfold bentryStartAddr in Hstart. simpl in *.
  destruct (beqAddr pdpart block) eqn:HbeqPartBlock; try(exfalso; congruence).
  destruct (beqAddr pdpart sh1entryaddr) eqn:HbeqPartSh1; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 part block sh1entryaddr blockChild idchild HpartIsPart HblockMapped Hsh1 HPDchild Hloc
    HbeqIdChildNull HbeqBCNull startaddr Hstart). unfold bentryStartAddr in *. simpl.
  destruct (beqAddr pdpart blockChild) eqn:HbeqPartBC.
  { rewrite <-DTL.beqAddrTrue in HbeqPartBC. subst blockChild. rewrite HlookupPart in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END childLocHasSameStart *)
}

assert(partitionsIsolation newS).
{ (* BEGIN partitionsIsolation newS *)
  intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
  rewrite HgetPartsEq in *. rewrite HgetChildrenEq in *. unfold getUsedPaddr. rewrite HgetMappedPEq.
  specialize(HPI pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
  rewrite HgetMappedPEq. rewrite HgetConfigPEq; try(apply childrenArePDT with pdparent; intuition).
  rewrite HgetConfigPEq; try(apply childrenArePDT with pdparent; intuition). assumption.
  (* END partitionsIsolation *)
}

assert(kernelDataIsolation newS).
{ (* BEGIN kernelDataIsolation newS *)
  intros part1 part2 Hpart1IsPart Hpart2IsPart. rewrite HgetPartsEq in *. rewrite HgetAccMappedPEq.
  specialize(HKDI part1 part2 Hpart1IsPart Hpart2IsPart).
  rewrite HgetConfigPEq; try(apply partitionsArePDT; intuition). assumption.
  (* END kernelDataIsolation *)
}

assert(verticalSharing newS).
{ (* BEGIN verticalSharing newS *)
  intros pdparent child HparentIsPart HchildIsChild. rewrite HgetPartsEq in *. rewrite HgetChildrenEq in *.
  specialize(HVS pdparent child HparentIsPart HchildIsChild). unfold getUsedPaddr. rewrite HgetMappedPEq.
  rewrite HgetConfigPEq; try(apply childrenArePDT with pdparent; intuition). rewrite HgetMappedPEq. assumption.
  (* END verticalSharing *)
}

intuition.
Qed.

Lemma setVIDT (pdpart vidtaddr: paddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.setVIDT pdpart vidtaddr
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold setVIDT. eapply bindRev.
{ (** MAL.getCurPartition **)
  eapply weaken. apply getCurPartition. intros s Hprops. simpl. apply Hprops.
}
intro curPd. eapply bindRev.
{ (** Internal.getGlobalIdPDCurrentOrChild **)
  eapply weaken. apply getGlobalIdPDCurrentOrChild. intros s Hprops. simpl. split. apply Hprops. intuition.
  subst curPd. apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
}
intro globalPd. eapply bindRev.
{ (** Internal.compareAddrToNull **)
  eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
}
intro globalPdNull. destruct globalPdNull.
{ (* case globalPdNull = true *)
  eapply weaken. apply WP.ret. intros s Hprops. intuition.
}
(* case globalPdNull = false *)
eapply bindRev.
{ (** Internal.compareAddrToNull **)
  eapply weaken. apply compareAddrToNull. intros s Hprops. simpl.
  instantiate(1:= fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
    /\ curPd = currentPartition s /\ isPDT globalPd s). rewrite <-beqAddrFalse in *. intuition.
}
intro vidtAddrNull. destruct vidtAddrNull.
- eapply bindRev.
  { (** MAL.writePDVidt **)
    eapply weaken. apply writePDVidt. intros s Hprops. simpl. split. apply Hprops. intuition.
  }
  intro. eapply weaken. apply WP.ret. intros s Hprops. simpl. destruct Hprops as [s0 [pdentry [newPDEntry (((HPI &
    HKDI & HVS & Hconsist & Hcurr & HglobIsPDT) & HbeqNullVidt) & HlookupGlob & Hs & HnewPD)]]]. intuition.
- eapply bindRev.
  { (** Internal.findBelongingBlock **)
    eapply weaken. apply findBelongingBlock. intros s Hprops. simpl. split. apply Hprops. unfold consistency in *.
    intuition.
  }
  intro vidtBlock. eapply bindRev.
  { (** Internal.compareAddrToNull **)
    eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
  }
  intro vidtBlockNull. destruct vidtBlockNull.
  { (* case vidtBlockNull = true *)
    eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
  }
  (* case vidtBlockNull = false *)
  eapply bindRev.
  { (** MAL.readBlockPresentFromBlockEntryAddr **)
    eapply weaken. apply readBlockPresentFromBlockEntryAddr. intros s Hprops. simpl.
    destruct Hprops as ((Hprops & Hconsist & HpropsOr) & HbeqNullBlock). rewrite <-beqAddrFalse in HbeqNullBlock.
    destruct HpropsOr as [Hcontra | ([bentry HlookupBlock] & HPflag & HvidtInKSE & Hlist)]; try(exfalso; congruence).
    instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s /\
      curPd = currentPartition s /\ isPDT globalPd s /\ beqAddr nullAddr vidtaddr = false /\ isBE vidtBlock s
      /\ bentryPFlag vidtBlock true s /\ In vidtBlock (filterOptionPaddr (getKSEntries globalPd s))
      /\ exists kernList firstKernList lastElem nidx blockStart bentryLast,
          bentryStartAddr vidtBlock blockStart s /\ isListOfKernels kernList globalPd s
          /\ kernList = firstKernList ++ [lastElem]
          /\ lookup (CPaddr (lastElem + blkoffset + nidx)) (memory s) beqAddr = Some (BE bentryLast)
          /\ paddrLe blockStart vidtaddr && paddrLt vidtaddr (endAddr (blockrange bentryLast)) = true). simpl.
    unfold isBE. rewrite HlookupBlock. intuition.
  }
  intro blockPresent. destruct (negb blockPresent) eqn:HnegPres.
  { (* case blockPresent = false *)
    eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
  }
  (* case blockPresent = true *)
  eapply bindRev.
  { (** MAL.readBlockAccessibleFromBlockEntryAddr **)
    eapply weaken. apply readBlockAccessibleFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
    intuition.
  }
  intro blockAcc. destruct (negb blockAcc) eqn:HnegAcc.
  { (* case blockAcc = false *)
    eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
  }
  (* case blockAcc = true *)
  apply negb_false_iff in HnegAcc. subst blockAcc. eapply bindRev.
  { (** getVidtSize **)
    unfold getVidtSize. eapply weaken. apply WP.ret. intros s Hprops.
    instantiate(1 := fun size s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\
      consistency s /\ curPd = currentPartition s /\ isPDT globalPd s /\  beqAddr nullAddr vidtaddr = false /\
      isBE vidtBlock s /\ bentryPFlag vidtBlock true s /\ bentryAFlag vidtBlock true s /\ size = Constants.vidtSize
      /\ In vidtBlock (filterOptionPaddr (getKSEntries globalPd s))
      /\ exists kernList firstKernList lastElem nidx blockStart bentryLast,
          bentryStartAddr vidtBlock blockStart s /\ isListOfKernels kernList globalPd s
          /\ kernList = firstKernList ++ [lastElem]
          /\ lookup (CPaddr (lastElem + blkoffset + nidx)) (memory s) beqAddr = Some (BE bentryLast)
          /\ paddrLe blockStart vidtaddr && paddrLt vidtaddr (endAddr (blockrange bentryLast)) = true).
    intuition.
  }
  intro vidtSize. eapply bindRev.
  { (** paddrAddIdx **)
    unfold MAL.paddrAddIdx. unfold paddrAddIdxMOpt. destruct (le_dec (vidtaddr + vidtSize) maxAddr) eqn:Hadd.
    - eapply weaken. apply WP.ret. intros s Hprops.
      instantiate(1 := fun endaddr s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\
        consistency s /\ curPd = currentPartition s /\ isPDT globalPd s /\  beqAddr nullAddr vidtaddr = false /\
        isBE vidtBlock s /\ bentryPFlag vidtBlock true s /\ bentryAFlag vidtBlock true s /\
        vidtSize = Constants.vidtSize /\ (endaddr <> nullAddr -> endaddr = CPaddr (vidtaddr + vidtSize))
        /\ In vidtBlock (filterOptionPaddr (getKSEntries globalPd s))
        /\ exists kernList firstKernList lastElem nidx blockStart bentryLast,
            bentryStartAddr vidtBlock blockStart s /\ isListOfKernels kernList globalPd s
            /\ kernList = firstKernList ++ [lastElem]
            /\ lookup (CPaddr (lastElem + blkoffset + nidx)) (memory s) beqAddr = Some (BE bentryLast)
            /\ paddrLe blockStart vidtaddr && paddrLt vidtaddr (endAddr (blockrange bentryLast)) = true). simpl.
      unfold CPaddr. rewrite Hadd. intuition.
    - eapply weaken. apply WP.ret. intros s Hprops. simpl.
      destruct Hprops as (HPI & HKDI & HVS & Hconsist & Hcurr & HglobIsPDT & HbeqNullVIDT & _ & HPflag & HAflag &
        Hsize & HblockInKSE & Hlist). intuition. unfold isBE. unfold bentryPFlag in *.
      destruct (lookup vidtBlock (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
  }
  intro vidtPotEndAddr. destruct (beqAddr vidtPotEndAddr nullAddr) eqn:HbeqVidtNull.
  + eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
  + rewrite <-beqAddrFalse in *. eapply bindRev.
    { (** MAL.readBlockEndFromBlockEntryAddr **)
      eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops. intuition.
    }
    intro vidtBlockEndAddr. eapply bindRev.
    { (** paddrLe **)
      eapply weaken. apply WP.ret. intros s Hprops. (*TODO transmit more info ?*)
      instantiate(1 := fun leEnds s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\
          consistency s /\ curPd = currentPartition s /\ isPDT globalPd s /\ beqAddr nullAddr vidtaddr = false /\
          isBE vidtBlock s /\ bentryPFlag vidtBlock true s /\ bentryAFlag vidtBlock true s /\
          vidtSize = Constants.vidtSize /\ vidtPotEndAddr = CPaddr (vidtaddr + vidtSize)
          /\ leEnds = paddrLe vidtBlockEndAddr vidtPotEndAddr). intuition.
    }
    intro overlap. destruct overlap.
    { (* case overlap = true *)
      eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
    }
    (* case overlap = false *)
    destruct (beqAddr globalPd curPd) eqn:HbeqGlobCurr.
    * eapply bindRev.
      { (** MAL.readSh1PDChildFromBlockEntryAddr **)
        eapply weaken. apply readSh1PDChildFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
        unfold consistency in *. unfold consistency1 in *. intuition. unfold isBE in *.
        destruct (lookup vidtBlock (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. reflexivity.
      }
      intro childPd. eapply bindRev.
      { (** Internal.compareAddrToNull **)
        eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
      }
      intro childPdNull. destruct (negb childPdNull) eqn:HnegNull.
      { eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition. }
      eapply bindRev.
      { (** MAL.writePDVidt **)
        eapply weaken. apply writePDVidt. intros s Hprops. simpl. split. apply Hprops. intuition.
      }
      intro. eapply weaken. apply WP.ret. intros s Hprops. simpl.
      destruct Hprops as [s0 [pdentry [newPDEntry Hprops]]]. intuition.
    * eapply bindRev.
      { (** MAL.readSh1InChildLocationFromBlockEntryAddr **)
        eapply weaken. apply readSh1InChildLocationFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
        unfold consistency in *. unfold consistency1 in *.
        intuition. unfold isBE in *. destruct (lookup vidtBlock (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. reflexivity.
      }
      intro vidtBlockChild. eapply bindRev.
      { (** Internal.compareAddrToNull **)
        eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
      }
      intro vidtBlockChildNull. destruct (negb vidtBlockChildNull) eqn:HnegNull.
      { eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition. }
      eapply bindRev.
      { (** MAL.writePDVidt **)
        eapply weaken. apply writePDVidt. intros s Hprops. simpl. split. apply Hprops. intuition.
      }
      intro. eapply weaken. apply WP.ret. intros s Hprops. simpl.
      destruct Hprops as [s0 [pdentry [newPDEntry Hprops]]]. intuition.
Qed.