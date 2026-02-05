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
Proof.StateLib (*Proof.InternalLemmas*) Proof.InternalLemmas2 Proof.DependentTypeLemmas.

Require Import Invariants findBlockInKSWithAddr eraseBlock checkBlockCut writeAccessibleToAncestorsIfNotCutRec.
Require Import deleteProps.

Require Import Model.Monad.

From Stdlib Require Import List Bool Lia.
Import List.ListNotations.

Lemma deletePartition idPDchildToDelete:
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
deletePartition idPDchildToDelete
{{fun _ s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold deletePartition. eapply bindRev.
{ (** MAL.getCurPartition **)
  eapply weaken. apply getCurPartition. intros s Hprops. apply Hprops.
}
intro currentPart. eapply bindRev.
{ (** Internal.findBlockInKSWithAddr **)
  eapply weaken. apply findBlockInKSWithAddr. intros s Hprops. simpl.
  destruct Hprops as (Hprops & Hcurr). assert(isPDT currentPart s).
  {
    subst currentPart.
    apply IL.partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
  }
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ currentPart = currentPartition s /\ isPDT currentPart s). intuition.
}
intro blockToDeleteInCurrPartAddr. eapply bindRev.
{ (** Internal.compareAddrToNull **)
  eapply weaken. apply compareAddrToNull. intros s Hprops. apply Hprops.
}
intro addrIsNull. destruct addrIsNull.
{ (* case addrIsNull = true *)
  eapply weaken. apply WP.ret. intros s Hprops. intuition.
}
(* case addrIsNull = false *)
eapply bindRev.
{ (** MAL.readSh1PDFlagFromBlockEntryAddr **)
  eapply weaken. apply readSh1PDFlagFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as (((HPI & HKDI & HVS & Hcurr & HcurrIsPDT) & Hconsist & HpropsOr) & HbeqNullBTD).
  rewrite <-beqAddrFalse in HbeqNullBTD. destruct HpropsOr as
    [Hcontra | [bentry (HlookupBTD & HblocksEq & HPflagBTD & HBTDMapped)]]; try(exfalso; congruence).
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ consistency s /\ currentPart = currentPartition s /\ isPDT currentPart s
    /\ blockToDeleteInCurrPartAddr = idPDchildToDelete
    /\ bentryPFlag blockToDeleteInCurrPartAddr true s
    /\ In blockToDeleteInCurrPartAddr (getMappedBlocks currentPart s)
    /\ blockToDeleteInCurrPartAddr <> nullAddr).
  split. intuition. split; trivial. exists bentry. assumption.
}
intro isChild. destruct (negb isChild) eqn:HneqChild.
{ (* case isChild = false *)
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
(* case isChild = true *)
apply negb_false_iff in HneqChild. subst isChild. eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr **)
  eapply weaken. apply readBlockStartFromBlockEntryAddr. intros s Hprops. split. apply Hprops.
  destruct Hprops as ((_ & _ & _ & _ & _ & _ & _ & HPflag & _) & _). unfold bentryPFlag in *. unfold isBE.
  destruct (lookup blockToDeleteInCurrPartAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  trivial.
}
intro blockStartAddr. eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr **)
  eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. split. apply Hprops.
  destruct Hprops as (_ & Hstart). unfold bentryStartAddr in *. unfold isBE.
  destruct (lookup blockToDeleteInCurrPartAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  trivial.
}
intro blockEndAddr. eapply bindRev.
{ (** MAL.eraseBlock **)
  eapply weaken. apply eraseBlock. intros s Hprops. apply Hprops.
}
intro eraseSucc. eapply bindRev.
{ (** MAL.readPDStructurePointer **)
  eapply weaken. apply readPDStructurePointer. intros s Hprops. simpl.
  destruct Hprops as [s0 (((((HPIs0 & HKDIs0 & HVSs0 & Hconsists0 & Hcurr & HcurrIsPDT & HblocksEq & HPflagBTDs0 &
    HBTDMapped & HbeqBTDNull) & [_ [sh1entryaddr (_ & HPDflag & Hsh1)]]) & HstartBTDs0) & HendBTDs0) & HcurrEq &
    HlookupRange & HlookupNotRange & _)].
  assert(HBTDIsBE: isBE blockToDeleteInCurrPartAddr s0).
  {
    unfold isBE. unfold bentryPFlag in *.
    destruct (lookup blockToDeleteInCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    trivial.
  }
  unfold sh1entryAddr in *.
  destruct (lookup blockToDeleteInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBTD; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). subst sh1entryaddr.
  assert(HPDchild: sh1entryPDchild (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) nullAddr s0).
  {
    assert(Hres: PDflagMeansNoChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(Hres blockToDeleteInCurrPartAddr HBTDIsBE HPDflag). assumption.
  }
  assert(HisPDT: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HcheckChild:
    true = checkChild blockToDeleteInCurrPartAddr s0 (CPaddr (blockToDeleteInCurrPartAddr+sh1offset))
    /\ sh1entryAddr blockToDeleteInCurrPartAddr (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) s0).
  {
    unfold checkChild. unfold sh1entryAddr. rewrite HlookupBTD. split; trivial. unfold sh1entryPDflag in *.
    destruct (lookup (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). auto.
  }
  specialize(HisPDT blockToDeleteInCurrPartAddr (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) HcheckChild).
  destruct HisPDT as (HAflagBTDs0 & _ & [startBTDBis (HstartBTDs0Bis & HisPDT)]).
  assert(startBTDBis = blockStartAddr).
  {
    unfold bentryStartAddr in *. rewrite HlookupBTD in *. rewrite <-HstartBTDs0 in *. assumption.
  }
  subst startBTDBis. clear HstartBTDs0Bis. assert(HstartIsPDT: isPDT blockStartAddr s0).
  {
    unfold entryPDT in *. unfold isPDT. unfold bentryStartAddr in *. rewrite HlookupBTD in *.
    rewrite <-HstartBTDs0 in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HcurrIsParts0: In currentPart (getPartitions multiplexer s0)).
  {
    subst currentPart. unfold consistency in *; unfold consistency1 in *; intuition.
  }
  assert(HrangeWereNone: forall addr, In addr (getAllPaddrBlock blockStartAddr blockEndAddr) -> addr <> blockStartAddr
    -> lookup addr (memory s0) beqAddr = None).
  {
    intros addr HaddrInRange HbeqAddrStart.
    assert(Htypes: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(Htypes blockToDeleteInCurrPartAddr blockStartAddr blockEndAddr currentPart HcurrIsParts0 HBTDMapped
      HstartBTDs0 HendBTDs0 HPDchild). destruct Htypes as [(Hcontra & _) | [(_ & Hres) | Hcontra]].
    - unfold isKS in *. unfold isPDT in *. exfalso.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    - apply Hres; auto.
    - (*false, but quicker to prove this way*) apply Hcontra; assumption.
  }
  assert(HlookupsEq: forall addr, addr <> blockStartAddr
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intros addr HbeqAddrStart. assert(HpropsOr: In addr (getAllPaddrBlock blockStartAddr blockEndAddr)
      \/ ~In addr (getAllPaddrBlock blockStartAddr blockEndAddr)) by (apply Classical_Prop.classic).
    destruct HpropsOr.
    - rewrite HrangeWereNone; trivial. apply HlookupRange; assumption.
    - apply HlookupNotRange; assumption.
  }
  assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  specialize(Hwell blockToDeleteInCurrPartAddr blockStartAddr blockEndAddr HPflagBTDs0 HstartBTDs0 HendBTDs0).
  destruct Hwell as (Hwell & _). assert(HlookupStarts: lookup blockStartAddr (memory s) beqAddr = None).
  {
    apply HlookupRange. apply IL.getAllPaddrBlockIncl; lia.
  }
  assert(blockToDeleteInCurrPartAddr <> blockStartAddr).
  { intro. subst blockStartAddr. unfold isPDT in *. rewrite HlookupBTD in *. congruence. }
  assert(HlookupBTDEq: lookup blockToDeleteInCurrPartAddr (memory s) beqAddr
    = lookup blockToDeleteInCurrPartAddr (memory s0) beqAddr).
  { apply HlookupsEq; assumption. }
  assert(CPaddr (blockToDeleteInCurrPartAddr+sh1offset) <> blockStartAddr).
  {
    intro. subst blockStartAddr. unfold isPDT in *. unfold sh1entryPDchild in *.
    destruct (lookup (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
  }
  assert(HlookupBTDSh1Eq: lookup (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) (memory s) beqAddr
    = lookup (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) (memory s0) beqAddr).
  { apply HlookupsEq; assumption. }
  assert(HstartIsChilds0: In blockStartAddr (getChildren currentPart s0)).
  {
    apply PDflagImpliesChild with blockToDeleteInCurrPartAddr; trivial;
      unfold consistency in *; unfold consistency1 in *; intuition.
  }
  assert(HcurrIsParent: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  specialize(HcurrIsParent blockStartAddr currentPart HcurrIsParts0 HstartIsChilds0).

  assert(nullAddrExists s).
  { (* BEGIN nullAddrExists s *)
    assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupsEq; trivial. unfold isPDT in *. intro.
    subst blockStartAddr. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END nullAddrExists *)
  }
  assert(wellFormedFstShadowIfBlockEntry s).
  { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
    assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block HblockIsBE. unfold isBE in *. assert(block <> blockStartAddr).
    {
      intro. subst blockStartAddr. rewrite HlookupStarts in *. congruence.
    }
    rewrite HlookupsEq in HblockIsBE; trivial. unfold isSHE. specialize(Hcons0 block HblockIsBE).
    rewrite HlookupsEq; trivial. unfold isSHE in *. intro. subst blockStartAddr. unfold isPDT in *.
    destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END wellFormedFstShadowIfBlockEntry *)
  }
  (* PDTIfPDFlag s false *)
  assert(AccessibleNoPDFlag s).
  { (* BEGIN AccessibleNoPDFlag s *)
    assert(Hcons0: AccessibleNoPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block sh1entryaddrBis HblockIsBE Hsh1Bis HAFlag. unfold isBE in *. unfold sh1entryAddr in *.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    {
      apply HlookupsEq. intro. subst blockStartAddr. rewrite HlookupStarts in *. congruence.
    }
    unfold bentryAFlag in *. rewrite HlookupBlockEq in *.
    specialize(Hcons0 block sh1entryaddrBis HblockIsBE Hsh1Bis HAFlag). unfold sh1entryPDflag in *.
    rewrite HlookupsEq; trivial. intro. subst blockStartAddr. unfold isPDT in *.
    destruct (lookup sh1entryaddrBis (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END AccessibleNoPDFlag *)
  }
  assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
  { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
    assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentry HlookupPart HbeqFirstNull.
    rewrite HlookupsEq in HlookupPart; try(intro; subst blockStartAddr; congruence).
    specialize(Hcons0 partition pdentry HlookupPart HbeqFirstNull). unfold isBE. unfold isFreeSlot in *.
    destruct Hcons0 as (HfirstIsBE & HfirstFree).
    assert(HlookupFirstEq: lookup (firstfreeslot pdentry) (memory s) beqAddr
      = lookup (firstfreeslot pdentry) (memory s0) beqAddr).
    {
      apply HlookupsEq. intro. subst blockStartAddr. unfold isPDT in *.
      destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupFirstEq. split; trivial.
    destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    assert(HlookupFirstSh1Eq: lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s) beqAddr
      = lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr).
    {
      apply HlookupsEq. intro. subst blockStartAddr. unfold isPDT in *.
      destruct (lookup (CPaddr (firstfreeslot pdentry+sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite HlookupFirstSh1Eq.
    destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). rewrite HlookupsEq; trivial. intro. subst blockStartAddr. unfold isPDT in *.
    destruct (lookup (CPaddr (firstfreeslot pdentry+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
    (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
  }
  unfold pdentryParent in *.
  destruct (lookup blockStartAddr (memory s0) beqAddr) eqn:HlookupStart; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  assert(multiplexerIsPDT s).
  { (* BEGIN multiplexerIsPDT s *)
    unfold multiplexerIsPDT. unfold isPDT. rewrite HlookupsEq.
    unfold consistency in *; unfold consistency1 in *; intuition. unfold multiplexer. intro Hcontra.
    assert(HparentOfPart: parentOfPartitionIsPartition s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition). apply eq_sym in Hcontra.
    specialize(HparentOfPart blockStartAddr p HlookupStart). destruct HparentOfPart as (_ & HparentOfRoot & _).
    specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *. rewrite HcurrIsParent in *. unfold isPDT in *.
    assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END multiplexerIsPDT *)
  }
  unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *.
  assert(HgetKSEq: forall part, part <> blockStartAddr -> getKSEntries part s = getKSEntries part s0).
  { intros part HbeqPartStart. apply getKSEntriesEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetMappedBEq: forall part, part <> blockStartAddr -> getMappedBlocks part s = getMappedBlocks part s0).
  { intros part HbeqPartStart. apply getMappedBlocksEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetMappedPEq: forall part, part <> blockStartAddr -> getMappedPaddr part s = getMappedPaddr part s0).
  { intros part HbeqPartStart. apply getMappedPaddrEqRemoveAddr with blockStartAddr; trivial. }
  assert(HAccgetMappedBEq: forall part, part <> blockStartAddr
    -> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s0).
  { intros part HbeqPartStart. apply getAccessibleMappedBlocksEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetAccMappedPEq: forall part, part <> blockStartAddr
    -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s0).
  { intros part HbeqPartStart. apply getAccessibleMappedPaddrEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetConfigEq: forall part, part <> blockStartAddr -> getConfigPaddr part s = getConfigPaddr part s0).
  { intros part HbeqPartStart. apply getConfigPaddrEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetChildrenEqNotStart: forall part, part <> blockStartAddr -> getChildren part s = getChildren part s0).
  { intros part HbeqPartStart. apply getChildrenEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetChildrenImpl: forall part partBase, In part (getChildren partBase s)
    -> In part (getChildren partBase s0)).
  { intros part partBase. apply getChildrenImplRemoveAddr with blockStartAddr; trivial. }
  assert(HgetPartsImpl: forall part, In part (getPartitions multiplexer s) -> In part (getPartitions multiplexer s0)).
  { intro part. apply getPartitionsImplRemoveAddr with blockStartAddr; trivial. }
  assert(HgetPartsImplRev: forall part, In part (getPartitions multiplexer s0)
     -> In part (getPartitions multiplexer s) \/ In part (getPartitions blockStartAddr s0)).
  { intro part. apply getPartitionsImplRemoveAddrRev; trivial. }
  assert(HgetFreeEq: forall part, part <> blockStartAddr -> getFreeSlotsList part s = getFreeSlotsList part s0).
  { intro part. apply getFreeSlotsListEqRemoveAddr; trivial. }
  assert(HcurrNotInDesc: ~In currentPart (getPartitions blockStartAddr s0)).
  {
    assert(HpartNoDup: NoDup (getPartitions currentPart s0)).
    { apply noDupPartitionTreeExt; trivial; intuition. }
    assert(Hlen: length (getPartitions currentPart s0) <= maxAddr+1).
    { apply IL.lengthNoDupPartitions; trivial. }
    assert(NoDup (getPartitions blockStartAddr s0)).
    {
      unfold getPartitions in *. apply noDupPartitionTreeExtAux with currentPart; trivial.
      - lia.
      - replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. right.
        induction (getChildren currentPart s0); simpl in *; try(congruence). apply in_or_app.
        destruct HstartIsChilds0 as [Heq | HstartIsChilds0]; try(right; apply IHl; assumption). subst a. left.
        rewrite PeanoNat.Nat.add_1_r. simpl. auto.
    }
    unfold getPartitions. unfold getPartitions in HpartNoDup. unfold getPartitions in Hlen.
    replace (maxAddr+2) with (S (maxAddr+1)) in *; try(lia). simpl in HpartNoDup. apply NoDup_cons_iff in HpartNoDup.
    destruct HpartNoDup as (HpartNotIn & _).
    assert(Hres: ~In currentPart (getPartitionsAux (maxAddr+1) blockStartAddr s0)).
    {
      induction (getChildren currentPart s0); simpl in *; try(exfalso; congruence).
      apply Lib.in_app_or_neg in HpartNotIn. destruct HpartNotIn as (HcurrNotInA & HcurrNotIn).
      destruct HstartIsChilds0 as [Heq | HstartIsChilds0]; try(apply IHl; assumption). subst a. assumption.
    }
    assert(HlenRec: length (flat_map (fun p : paddr => getPartitionsAux (maxAddr + 1) p s0)
      (getChildren currentPart s0)) <= maxAddr).
    { simpl in Hlen. lia. }
    rewrite getPartitionsEnd; trivial. clear HpartNotIn. clear Hlen.
    induction (getChildren currentPart s0); simpl in *; try(exfalso; congruence). rewrite length_app in HlenRec.
    assert(HnewLen: length (flat_map (fun p : paddr => getPartitionsAux (maxAddr + 1) p s0) l) <= maxAddr) by lia.
    destruct HstartIsChilds0 as [Heq | HstartIsChilds0]; try(apply IHl; assumption). subst a. lia.
  }
  assert(HstartIsParts0: In blockStartAddr (getPartitions multiplexer s0)).
  {
    apply IL.childrenPartitionInPartitionList with currentPart; trivial; intuition.
  }

  assert(currentPartitionInPartitionsList s).
  { (* BEGIN currentPartitionInPartitionsList s *)
    assert(Hcons0: currentPartitionInPartitionsList s0) by intuition. unfold currentPartitionInPartitionsList in *.
    rewrite HcurrEq. apply HgetPartsImplRev in Hcons0. rewrite <-Hcurr in *.
    destruct Hcons0; try(exfalso; congruence). assumption.
    (* END currentPartitionInPartitionsList *)
  }
  assert(wellFormedShadowCutIfBlockEntry s).
  { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
    assert(Hcons0: wellFormedShadowCutIfBlockEntry s0) by intuition.
    intros block HblockIsBE. unfold isBE in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. specialize(Hcons0 block HblockIsBE).
    destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr. unfold isSCE in *.
    rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END wellFormedShadowCutIfBlockEntry *)
  }
  assert(BlocksRangeFromKernelStartIsBE s).
  { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
    assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by intuition. intros kernel blockidx HkernIsKS Hblockidx.
    unfold isKS in *. assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. specialize(Hcons0 kernel blockidx HkernIsKS Hblockidx).
    unfold isBE in *. rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END BlocksRangeFromKernelStartIsBE *)
  }
  assert(KernelStructureStartFromBlockEntryAddrIsKS s).
  { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s*)
    assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0) by intuition.
    intros block blockidx HblockIsBE Hblockidx. unfold isBE in *. unfold bentryBlockIndex in *.
    assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. rewrite HlookupsEq in Hblockidx; trivial.
    specialize(Hcons0 block blockidx HblockIsBE Hblockidx). unfold isKS in *. rewrite HlookupsEq; auto. intro Hcontra.
    rewrite Hcontra in *. unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
    (* END KernelStructureStartFromBlockEntryAddrIsKS *)
  }
  assert(sh1InChildLocationIsBE s).
  { (* BEGIN sh1InChildLocationIsBE s*)
    assert(Hcons0: sh1InChildLocationIsBE s0) by intuition.
    intros sh1entryaddrBis sh1entryBis HlookupSh1Bis HbeqInChildNull. assert(sh1entryaddrBis <> blockStartAddr).
    { intro. subst sh1entryaddrBis. congruence. }
    rewrite HlookupsEq in HlookupSh1Bis; trivial.
    specialize(Hcons0 sh1entryaddrBis sh1entryBis HlookupSh1Bis HbeqInChildNull). unfold isBE in *.
    rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END sh1InChildLocationIsBE *)
  }
  assert(StructurePointerIsKS s).
  { (* BEGIN StructurePointerIsKS s *)
    assert(Hcons0: StructurePointerIsKS s0) by intuition. intros partition pdentry HlookupPart HbeqStructNull.
    assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HlookupPart; trivial. specialize(Hcons0 partition pdentry HlookupPart HbeqStructNull).
    unfold isKS in *. rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END StructurePointerIsKS *)
  }
  assert(NextKSIsKS s).
  { (* BEGIN NextKSIsKS s *)
    assert(Hcons0: NextKSIsKS s0) by intuition.
    intros kernel nextKSaddr nextKS HkernIsKS HnextKSAddr HnextKS HbeqNextNull.
    unfold isKS in *. unfold nextKSAddr in *. assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. rewrite HlookupsEq in HnextKSAddr; trivial.
    unfold nextKSentry in *. assert(nextKSaddr <> blockStartAddr).
    { intro. subst nextKSaddr. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HnextKS; trivial.
    specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextKSAddr HnextKS HbeqNextNull). rewrite HlookupsEq; auto.
    intro Hcontra. rewrite Hcontra in *. unfold isPDT in *. unfold isKS in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END NextKSIsKS *)
  }
  assert(NextKSOffsetIsPADDR s).
  { (* BEGIN NextKSOffsetIsPADDR s *)
    assert(Hcons0: NextKSOffsetIsPADDR s0) by intuition. intros kern nextksaddr HkernIsKS HnextIsNext.
    unfold isKS in *. unfold nextKSAddr in *. assert(kern <> blockStartAddr).
    { intro. subst kern. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. rewrite HlookupsEq in HnextIsNext; trivial.
    specialize(Hcons0 kern nextksaddr HkernIsKS HnextIsNext). destruct Hcons0 as (Hcons0 & HbeqNextNull).
    split; trivial. unfold isPADDR in *. rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *.
    unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END NextKSOffsetIsPADDR *)
  }
  assert(NoDupInFreeSlotsList s).
  { (* BEGIN NoDupInFreeSlotsList s *)
    assert(Hcons0: NoDupInFreeSlotsList s0) by intuition. intros partition pdentry HlookupPart.
    assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HlookupPart; trivial. specialize(Hcons0 partition pdentry HlookupPart).
    rewrite HgetFreeEq; trivial.
    (* END NoDupInFreeSlotsList *)
  }
  assert(freeSlotsListIsFreeSlot s).
  { (* BEGIN freeSlotsListIsFreeSlot s *)
    assert(Hcons0: freeSlotsListIsFreeSlot s0) by intuition.
    intros partition freeslot optionfreeslotslist freeslotslist HpartIsPDT Hoption HslotsList HbeqFreeNull.
    unfold isPDT in *. assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HpartIsPDT; trivial. rewrite HgetFreeEq in Hoption; trivial.
    specialize(Hcons0 partition freeslot optionfreeslotslist freeslotslist HpartIsPDT Hoption HslotsList
      HbeqFreeNull). unfold isFreeSlot in *. assert(freeslot <> blockStartAddr).
    {
      intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; trivial.
    destruct (lookup freeslot (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    assert(CPaddr (freeslot+sh1offset) <> blockStartAddr).
    {
      intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; trivial. destruct (lookup (CPaddr (freeslot+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END freeSlotsListIsFreeSlot *)
  }
  assert(DisjointFreeSlotsLists s).
  { (* BEGIN DisjointFreeSlotsLists s *)
    assert(Hcons0: DisjointFreeSlotsLists s0) by intuition.
    intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2. unfold isPDT in *. assert(part1 <> blockStartAddr).
    { intro. subst part1. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hpart1IsPDT; trivial. assert(part2 <> blockStartAddr).
    { intro. subst part2. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hpart2IsPDT; trivial. rewrite HgetFreeEq; trivial.
    specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2). rewrite HgetFreeEq; trivial.
    (* END DisjointFreeSlotsLists *)
  }
  assert(inclFreeSlotsBlockEntries s).
  { (* BEGIN inclFreeSlotsBlockEntries s *)
    assert(Hcons0: inclFreeSlotsBlockEntries s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
    assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HpartIsPDT; trivial. specialize(Hcons0 partition HpartIsPDT).
    rewrite HgetFreeEq; trivial. rewrite HgetKSEq; trivial.
    (* END inclFreeSlotsBlockEntries *)
  }
  assert(DisjointKSEntries s).
  { (* BEGIN DisjointKSEntries s *)
    assert(Hcons0: DisjointKSEntries s0) by intuition.
    intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2. unfold isPDT in *. assert(part1 <> blockStartAddr).
    { intro. subst part1. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hpart1IsPDT; trivial. assert(part2 <> blockStartAddr).
    { intro. subst part2. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hpart2IsPDT; trivial.
    specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2). rewrite HgetKSEq; trivial.
    rewrite HgetKSEq; trivial.
    (* END DisjointKSEntries *)
  }
  assert(noDupPartitionTree s).
  { (* BEGIN noDupPartitionTree s *)
    assert(Hcons0: noDupPartitionTree s0) by intuition. unfold noDupPartitionTree in *.
    apply noDupGetPartitionsEqRemoveAddr with s0 blockStartAddr; trivial.
    (* END noDupPartitionTree *)
  }
  assert(HpartialIsParent: forall partition pdparent, partition <> blockStartAddr
    -> In pdparent (getPartitions multiplexer s) -> In partition (getChildren pdparent s)
    -> pdentryParent partition pdparent s).
  { (* BEGIN partial isParent s *)
    assert(Hcons0: isParent s0) by intuition. intros partition pdparent HbeqPartStart HparentIsPart HpartIsChild.
    apply HgetPartsImpl in HparentIsPart. assert(pdparent <> blockStartAddr).
    {
      assert(isPDT pdparent s).
      {
        unfold getChildren in *. unfold isPDT.
        destruct (lookup pdparent (memory s) beqAddr); try(simpl in *; congruence).
        destruct v; try(simpl in *; congruence). trivial.
      }
      intro. subst pdparent. unfold isPDT in *. rewrite HlookupStarts in *. congruence.
    }
    rewrite HgetChildrenEqNotStart in HpartIsChild; trivial.
    specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent.
    rewrite HlookupsEq; trivial.
    (* END partial isParent *)
  }
  assert(isChild s).
  { (* BEGIN isChild s *)
    assert(Hcons0: isChild s0) by intuition. intros partition pdparent HpartIsPart HparentIsParent.
    unfold pdentryParent in *. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    rewrite HlookupsEq in HparentIsParent; trivial. apply HgetPartsImpl in HpartIsPart. intro HbeqPartRoot.
    specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
    assert(pdparent <> blockStartAddr).
    {
      intro. subst pdparent. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    rewrite HgetChildrenEqNotStart; assumption.
    (* END isChild *)
  }
  assert(noDupKSEntriesList s).
  { (* BEGIN noDupKSEntriesList s *)
    assert(Hcons0: noDupKSEntriesList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
    assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HpartIsPDT; trivial. specialize(Hcons0 partition HpartIsPDT).
    rewrite HgetKSEq; assumption.
    (* END noDupKSEntriesList *)
  }
  assert(noDupMappedBlocksList s).
  { (* BEGIN noDupMappedBlocksList s *)
    assert(Hcons0: noDupMappedBlocksList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
    assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HpartIsPDT; trivial. specialize(Hcons0 partition HpartIsPDT).
    rewrite HgetMappedBEq; assumption.
    (* END noDupMappedBlocksList *)
  }
  assert(wellFormedBlock s).
  { (* BEGIN wellFormedBlock s *)
    assert(Hcons0: wellFormedBlock s0) by intuition. intros block startaddr endaddr HPFlag Hstart Hend.
    unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    assert(HbeqBlockStart: block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    specialize(HlookupsEq block HbeqBlockStart). rewrite HlookupsEq in *.
    specialize(Hcons0 block startaddr endaddr HPFlag Hstart Hend). assumption.
    (* END wellFormedBlock *)
  }
  assert(HpartialParentOfPartIsPart: forall partition entry, ~In (parent entry) (getPartitions blockStartAddr s0)
    -> lookup partition (memory s) beqAddr = Some (PDT entry)
    -> (partition <> constantRootPartM
        -> (exists parentEntry, lookup (parent entry) (memory s) beqAddr = Some (PDT parentEntry))
            /\ In (parent entry) (getPartitions multiplexer s))
      /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition).
  { (* BEGIN partial parentOfPartitionIsPartition s *)
    assert(Hcons0: parentOfPartitionIsPartition s0) by intuition.
    intros partition pdentry HparentNotInSub HlookupPart. assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HlookupPart; trivial. specialize(Hcons0 partition pdentry HlookupPart).
    destruct Hcons0 as (HparentIsPart & HparentProps). split; trivial. intro HbeqPartRoot.
    specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as (HlookupParent & HparentIsPart).
    apply HgetPartsImplRev in HparentIsPart. assert(parent pdentry <> blockStartAddr).
    {
      unfold getPartitions in *. replace (maxAddr+2) with (S (maxAddr+1)) in *; try(lia). simpl in HparentNotInSub.
      apply Decidable.not_or in HparentNotInSub. destruct HparentNotInSub. auto.
    }
    destruct HparentIsPart as [HparentIsPart | Hcontra]; try(exfalso; congruence). rewrite HlookupsEq; auto.
    (* END partial parentOfPartitionIsPartition *)
  }
  assert(NbFreeSlotsISNbFreeSlotsInList s).
  { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
    assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0) by intuition.
    intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. unfold pdentryNbFreeSlots in *.
    assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HpartIsPDT; trivial. rewrite HlookupsEq in HnbFree; trivial.
    specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree).
    rewrite HgetFreeEq; assumption.
    (* END NbFreeSlotsISNbFreeSlotsInList *)
  }
  assert(maxNbPrepareIsMaxNbKernels s).
  { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
    assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by intuition. intros partition kernList HkernList.
    destruct kernList; try(simpl; lia).
    apply isListOfKernelsEqRemovedAddrRev with (s0:=s0) (removedAddr:=blockStartAddr) in HkernList; trivial.
    specialize(Hcons0 partition (p0::kernList) HkernList). assumption.
    (* END maxNbPrepareIsMaxNbKernels *)
  }
  assert(blockInChildHasAtLeastEquivalentBlockInParent s).
  { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
    assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0) by intuition.
    intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild Hstart Hend
      HPflag. assert(HbeqParentStart: pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetChildrenEqNotStart in HchildIsChild; trivial. rewrite HgetMappedBEq in *; trivial.
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    unfold bentryPFlag in *. rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq in Hend; trivial.
    rewrite HlookupsEq in HPflag; trivial.
    specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
      Hstart Hend HPflag). destruct Hcons0 as [blockParent [startParent [endParent Hcons0]]].
    exists blockParent. exists startParent. exists endParent. assert(blockParent <> blockStartAddr).
    {
      intro. subst blockParent. unfold bentryStartAddr in *. unfold isPDT in *. destruct Hcons0 as (_ & Hcons0 & _).
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; assumption.
    (* END blockInChildHasAtLeastEquivalentBlockInParent *)
  }
  assert(partitionTreeIsTree s).
  { (* BEGIN partitionTreeIsTree s *)
    assert(Hcons0: partitionTreeIsTree s0) by intuition.
    intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsparent HparentsList.
    unfold pdentryParent in *. apply HgetPartsImpl in HchildIsPart. assert(child <> blockStartAddr).
    { intro. subst child. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HparentIsparent; trivial.
    apply isParentsListImplRemovedAddrRev with (s0:=s0) (removedAddr:=blockStartAddr) in HparentsList; trivial.
    specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsparent HparentsList).
    assumption.
    (* END partitionTreeIsTree *)
  }
  assert(kernelEntriesAreValid s).
  { (* BEGIN kernelEntriesAreValid s *)
    assert(Hcons0: kernelEntriesAreValid s0) by intuition. intros kernel idx HkernIsKS Hidx. unfold isKS in *.
    assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. specialize(Hcons0 kernel idx HkernIsKS Hidx). unfold isBE in *.
    rewrite HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END kernelEntriesAreValid *)
  }
  assert(nextKernelIsValid s).
  { (* BEGIN nextKernelIsValid s *)
    assert(Hcons0: nextKernelIsValid s0) by intuition. intros kernel HkernIsKS. unfold isKS in *.
    assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. specialize(Hcons0 kernel HkernIsKS).
    destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]). split; trivial. exists nextAddr. split.
    - intro Hp. specialize(HlookupNext Hp). rewrite HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *.
      unfold isPDT in *. rewrite HlookupNext in *. congruence.
    - destruct Hnext as [HnextIsKS | HnextIsNull]; auto. left. rewrite HlookupsEq; trivial. intro. subst nextAddr.
      unfold isKS in *. unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    (* END nextKernelIsValid *)
  }
  assert(noDupListOfKerns s).
  { (* BEGIN noDupListOfKerns s *)
    assert(Hcons0: noDupListOfKerns s0) by intuition. intros partition kernList HkernList.
    apply isListOfKernelsEqRemovedAddrRev with (s0:=s0) (removedAddr:=blockStartAddr) in HkernList; trivial.
    specialize(Hcons0 partition kernList HkernList). assumption.
    (* END noDupListOfKerns *)
  }
  assert(MPUsizeIsBelowMax s).
  { (* BEGIN MPUsizeIsBelowMax s *)
    assert(Hcons0: MPUsizeIsBelowMax s0) by intuition. intros partition MPUlist HMPU. unfold pdentryMPU in *.
    assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HMPU; trivial. specialize(Hcons0 partition MPUlist HMPU). assumption.
    (* END MPUsizeIsBelowMax *)
  }
  assert(originIsParentBlocksStart s).
  { (* BEGIN originIsParentBlocksStart s *)
    assert(Hcons0: originIsParentBlocksStart s0) by intuition.
    intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    assert(block <> blockStartAddr).
    {
      intro. subst block. apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
      congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. rewrite HlookupsEq in HlookupPart; trivial.
    unfold scentryOrigin in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Horigin; trivial.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    { apply HlookupsEq; assumption. }
    specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
      Horigin). destruct Hcons0 as (Hleft & Hright). unfold bentryStartAddr. rewrite HlookupBlockEq.
    split; trivial. intro HbeqPartRoot. specialize(Hleft HbeqPartRoot).
    destruct Hleft as [blockParent (HBPMapped & HstartP & Hincl)]. assert(parent pdentry <> blockStartAddr).
    {
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s0)).
      {
        assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent. rewrite HlookupPart.
        reflexivity.
      }
      intro Hcontra. rewrite Hcontra in *. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    exists blockParent. rewrite HgetMappedBEq; trivial. simpl. rewrite HlookupBlockEq. rewrite HlookupsEq; auto.
    intro. subst blockParent. unfold bentryStartAddr in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END originIsParentBlocksStart *)
  }
  assert(nextImpliesBlockWasCut s).
  { (* BEGIN nextImpliesBlockWasCut s *)
    assert(Hcons0: nextImpliesBlockWasCut s0) by intuition.
    intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped Hend Hsce
      HbeqNextNull Hnext HbeqPartRoot.
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    assert(block <> blockStartAddr).
    {
      intro. subst block. apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
      congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. rewrite HlookupsEq in HlookupPart; trivial.
    unfold scentryNext in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hnext; trivial.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    { apply HlookupsEq; assumption. }
    unfold bentryEndAddr in *. simpl. rewrite HlookupBlockEq in *.
    specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
      Hend Hsce HbeqNextNull Hnext HbeqPartRoot).
    destruct Hcons0 as [blockParent [endParent (HBPMapped & HendP & HltEnds & Hincl)]].
    exists blockParent. exists endParent. assert(parent pdentry <> blockStartAddr).
    {
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s0)).
      {
        assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent. rewrite HlookupPart.
        reflexivity.
      }
      intro Hcontra. rewrite Hcontra in *. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    rewrite HgetMappedBEq; trivial. rewrite HlookupsEq; auto.
    intro. subst blockParent. unfold bentryEndAddr in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END nextImpliesBlockWasCut *)
  }
  assert(blocksAddressesTypes s).
  { (* BEGIN blocksAddressesTypes s *)
    assert(Hcons0: blocksAddressesTypes s0) by intuition.
    intros block startaddr endaddr part HpartIsPart HblockMapped Hstart Hend HPDchildB.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    unfold bentryEndAddr in *. rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq in Hend; trivial.
    unfold sh1entryPDchild in *. assert(CPaddr (block+sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial.
    specialize(Hcons0 block startaddr endaddr part HpartIsPart HblockMapped Hstart Hend HPDchildB).
    destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hrange]].
    - left. unfold isKS in *. assert(startaddr <> blockStartAddr).
      {
        intro. subst startaddr. unfold isPDT in *.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite HlookupsEq; trivial. split; trivial. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
      destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
      + left. unfold isBE in *. rewrite HlookupsEq; trivial. intro. subst addr.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      + right. left. unfold isSHE in *. rewrite HlookupsEq; trivial. intro. subst addr.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      + right. right. left. unfold isSCE in *. rewrite HlookupsEq; trivial. intro. subst addr.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      + right. right. right. left. unfold isPADDR in *. rewrite HlookupsEq; trivial. intro. subst addr.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      + right. right. right. right. rewrite HlookupsEq; trivial. intro. subst addr. congruence.
    - destruct (beqAddr startaddr blockStartAddr) eqn:HbeqStarts.
      + rewrite <-beqAddrTrue in HbeqStarts. subst startaddr. right. right. intros addr HaddrInRange.
        destruct (beqAddr addr blockStartAddr) eqn:HbeqAddrStart.
        * rewrite <-beqAddrTrue in HbeqAddrStart. subst addr. assumption.
        * rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. apply Hrange; auto.
      + rewrite <-beqAddrFalse in *. right. left. unfold isPDT. rewrite HlookupsEq; trivial. split; trivial.
        intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). rewrite HlookupsEq; trivial.
        intro. subst addr. unfold isPDT in *. rewrite Hrange in *. congruence.
    - right. right. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
      destruct (beqAddr addr blockStartAddr) eqn:HbeqAddrStart.
      + rewrite <-beqAddrTrue in HbeqAddrStart. subst addr. assumption.
      + rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
    (* END blocksAddressesTypes *)
  }
  assert(notPDTIfNotPDflag s).
  { (* BEGIN notPDTIfNotPDflag s *)
    assert(Hcons0: notPDTIfNotPDflag s0) by intuition.
    intros block startaddr sh1entryaddrBis part HpartIsPart HblockMapped Hstart Hsh1 HPDflagB HPDchildB.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hstart; trivial. unfold sh1entryAddr in *. rewrite HlookupsEq in Hsh1; trivial.
    unfold sh1entryPDchild in *. unfold sh1entryPDflag in *. assert(sh1entryaddrBis <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. rewrite HlookupsEq in HPDflagB; trivial.
    specialize(Hcons0 block startaddr sh1entryaddrBis part HpartIsPart HblockMapped Hstart Hsh1 HPDflagB HPDchildB).
    contradict Hcons0. unfold isPDT in *. rewrite <-HlookupsEq; trivial. intro. subst startaddr.
    rewrite HlookupStarts in *. congruence.
    (* END notPDTIfNotPDflag *)
  }
  assert(nextKernAddrIsInSameBlock s).
  { (* BEGIN nextKernAddrIsInSameBlock s *)
    assert(Hcons0: nextKernAddrIsInSameBlock s0) by intuition.
    intros block kernel startaddr endaddr part HpartIsPart HblockMapped Hstart Hend HPDchildB HkernIsKS HnextInBlock.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hstart; trivial. unfold bentryEndAddr in *. rewrite HlookupsEq in Hend; trivial.
    unfold sh1entryPDchild in *. assert(CPaddr (block+sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. unfold isKS in *. assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial.
    specialize(Hcons0 block kernel startaddr endaddr part HpartIsPart HblockMapped Hstart Hend HPDchildB HkernIsKS
      HnextInBlock). assumption.
    (* END nextKernAddrIsInSameBlock *)
  }
  assert(noDupMappedPaddrList s).
  { (* BEGIN noDupMappedPaddrList s *)
    assert(Hcons0: noDupMappedPaddrList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
    assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HpartIsPDT; trivial. specialize(Hcons0 partition HpartIsPDT).
    rewrite HgetMappedPEq; assumption.
    (* END noDupMappedPaddrList *)
  }
  assert(accessibleParentPaddrIsAccessibleIntoChild s).
  { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
    assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s0) by intuition.
    intros pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild.
    apply HgetPartsImpl in HparentIsPart. assert(pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetChildrenImpl in HchildIsChild. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedPaddr in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
      rewrite HlookupStarts in *. simpl in *. congruence.
    }
    rewrite HgetAccMappedPEq in *; trivial. rewrite HgetMappedPEq in *; trivial.
    specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild). assumption.
    (* END accessibleParentPaddrIsAccessibleIntoChild *)
  }
  assert(sharedBlockPointsToChild s).
  { (* BEGIN sharedBlockPointsToChild s *)
    assert(Hcons0: sharedBlockPointsToChild s0) by intuition.
    intros pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParent HblockParentMapped Hsh1Bis. unfold getUsedPaddr in *. assert(pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. apply HgetChildrenImpl in HchildIsChild. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedPaddr in *. unfold getMappedBlocks in *.
      unfold getKSEntries in *. unfold getConfigPaddr in *. unfold getConfigBlocks in *. simpl in *.
      rewrite HlookupStarts in *. simpl in *. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. rewrite HgetMappedPEq in *; trivial. rewrite HgetConfigEq in *; trivial.
    unfold sh1entryAddr in *. assert(blockParent <> blockStartAddr).
    { intro. subst blockParent. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1Bis; trivial. simpl in *. rewrite HlookupsEq in HaddrInBlockParent; trivial.
    specialize(Hcons0 pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParent HblockParentMapped Hsh1Bis). unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
    assert(CPaddr (blockParent + sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStart in *. destruct Hcons0; congruence. }
    rewrite HlookupsEq; assumption.
    (* END sharedBlockPointsToChild *)
  }
  assert(adressesRangePreservedIfOriginAndNextOk s).
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
    assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0) by intuition.
    intros partition pdentry block scentryaddr start endaddr HpartIsPart HblockMapped HblockIsBE Hstart Hend
      HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    apply HgetPartsImpl in HpartIsPart. rewrite HgetMappedBEq in HblockMapped; trivial. unfold isBE in *.
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. rewrite HlookupsEq in Hstart; trivial.
    rewrite HlookupsEq in Hend; trivial. rewrite HlookupsEq in HPflag; trivial. unfold scentryNext in *.
    rewrite HlookupsEq in HlookupPart; trivial. unfold scentryOrigin in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Horigin; trivial. rewrite HlookupsEq in Hnext; trivial.
    specialize(Hcons0 partition pdentry block scentryaddr start endaddr HpartIsPart HblockMapped HblockIsBE
      Hstart Hend HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot).
    destruct Hcons0 as [blockParent (HBPMapped & HBPIsBE & Hbounds)]. assert(parent pdentry <> blockStartAddr).
    {
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s0)).
      {
        assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent. rewrite HlookupPart.
        reflexivity.
      }
      intro Hcontra. rewrite Hcontra in *. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    exists blockParent. rewrite HgetMappedBEq; trivial. rewrite HlookupsEq; auto. intro. subst blockParent.
    unfold isBE in *. rewrite HlookupStart in *. congruence.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }
  assert(childsBlocksPropsInParent s).
  { (* BEGIN childsBlocksPropsInParent s *)
    assert(Hcons0: childsBlocksPropsInParent s0) by intuition.
    intros child parentPart blockChild startChild endChild blockParent startParent endParent HparentIsPart
      HchildIsChild HchildMapped HstartChild HendChild HPFlagChild HparentMapped HparentStart HparentEnd
      HPFlagParent HleStart HgeEnd. assert(parentPart <> blockStartAddr).
    { intro. subst parentPart. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. apply HgetChildrenImpl in HchildIsChild. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    assert(HlookupBPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
    { apply HlookupsEq. intro. subst blockParent. rewrite HlookupStarts in *. congruence. }
    unfold bentryPFlag in *. unfold checkChild. unfold bentryAFlag. rewrite HlookupBPEq in *.
    assert(HlookupBCEq: lookup blockChild (memory s) beqAddr = lookup blockChild (memory s0) beqAddr).
    { apply HlookupsEq. intro. subst blockChild. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupBCEq in *. specialize(Hcons0 child parentPart blockChild startChild endChild blockParent
      startParent endParent HparentIsPart HchildIsChild HchildMapped HstartChild HendChild HPFlagChild
      HparentMapped HparentStart HparentEnd HPFlagParent HleStart HgeEnd).
    destruct Hcons0 as (HcheckChildB & HPDchildB & HinChildLoc & HAflagParent). unfold checkChild in *.
    assert(HlookupSh1Eq: lookup (CPaddr (blockParent+sh1offset)) (memory s) beqAddr
      = lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr).
    {
      apply HlookupsEq. assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0) by intuition.
      assert(HBPIsBE: isBE blockParent s0).
      {
        unfold isBE. destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
        trivial.
      }
      apply Hsh1IsSHE in HBPIsBE. intro Hcontra. rewrite Hcontra in *. unfold isSHE in *. rewrite HlookupStart in *.
      congruence.
    }
    unfold sh1entryPDchild. unfold sh1entryInChildLocation in *. rewrite HlookupSh1Eq.
    split; try(split; try(split)); trivial. intros blockIDInChild HchildLoc. apply HinChildLoc.
    destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial. intro HbeqIdNull.
    specialize(HlocIsBE HbeqIdNull). unfold isBE in *. rewrite <-HlookupsEq; trivial. intro Hcontra.
    rewrite Hcontra in *. rewrite HlookupStarts in *. congruence.
    (* END childsBlocksPropsInParent *)
  }
  assert(noChildImpliesAddressesNotShared s).
  { (* BEGIN noChildImpliesAddressesNotShared s *)
    assert(Hcons0: noChildImpliesAddressesNotShared s0) by intuition.
    intros partition pdentry block sh1entryaddrBis HpartIsPart HlookupPart HblockMapped Hsh1Bis HPDChild child
      addr HchildIsChild HaddrInBlock. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    destruct (beqAddr child blockStartAddr) eqn:HbeqChildStart.
    - rewrite <-beqAddrTrue in HbeqChildStart. subst child. unfold getMappedPaddr. unfold getMappedBlocks.
      unfold getKSEntries. rewrite HlookupStarts. auto.
    - rewrite <-beqAddrFalse in *. apply HgetPartsImpl in HpartIsPart. rewrite HlookupsEq in HlookupPart; trivial.
      apply HgetChildrenImpl in HchildIsChild. simpl in *. assert(block <> blockStartAddr).
      { intro. subst block. rewrite HlookupStarts in *. simpl in *. congruence. }
      rewrite HlookupsEq in HaddrInBlock; trivial. rewrite HgetMappedBEq in *; trivial.
      rewrite HgetMappedPEq; trivial. unfold sh1entryPDchild in *. assert(sh1entryaddrBis <> blockStartAddr).
      { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
      rewrite HlookupsEq in HPDChild; trivial. specialize(Hcons0 partition pdentry block sh1entryaddrBis HpartIsPart
        HlookupPart HblockMapped Hsh1Bis HPDChild child addr HchildIsChild HaddrInBlock). assumption.
    (* END noChildImpliesAddressesNotShared *)
  }
  assert(kernelsAreNotAccessible s).
  { (* BEGIN kernelsAreNotAccessible s *)
    assert(Hcons0: kernelsAreNotAccessible s0) by intuition.
    intros block startaddr part HpartIsPart HblockMapped Hstart HstartIsKS.
    assert(HbeqPartStart: part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    unfold bentryAFlag. rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq; trivial. unfold isKS in *.
    rewrite HgetMappedBEq in *; trivial. assert(startaddr <> blockStartAddr).
    { intro. subst startaddr. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HstartIsKS; trivial.
    specialize(Hcons0 block startaddr part HpartIsPart HblockMapped Hstart HstartIsKS). assumption.
    (* END kernelsAreNotAccessible *)
  }
  assert(PDflagMeansNoChild s).
  { (* BEGIN PDflagMeansNoChild s *)
    assert(Hcons0: PDflagMeansNoChild s0) by intuition. intros block HblockIsBE HPDflagB. unfold isBE in *.
    assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. unfold sh1entryPDflag in *.
    assert(CPaddr (block+sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    unfold sh1entryPDchild. rewrite HlookupsEq in HPDflagB; trivial. specialize(Hcons0 block HblockIsBE HPDflagB).
    rewrite HlookupsEq; assumption.
    (* END PDflagMeansNoChild *)
  }

  assert(nbPrepareIsNbKern s).
  { (* BEGIN nbPrepareIsNbKern s *)
    assert(Hcons0: nbPrepareIsNbKern s0) by intuition. intros partition pdentry HlookupPart.
    assert(partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    rewrite HlookupsEq in HlookupPart; trivial. specialize(Hcons0 partition pdentry HlookupPart).
    rewrite completeListOfKernelsEqRemovedAddr with (s0:=s0) (removedAddr:=blockStartAddr); assumption.
   (* END nbPrepareIsNbKern *)
  }

  assert(blockAndNextAreSideBySide s).
  { (* BEGIN blockAndNextAreSideBySide s *)
    assert(Hcons0: blockAndNextAreSideBySide s0) by intuition.
    intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped Hend Hsce HbeqNextNull Hnext.
    assert(HbeqPartStart: partition <> blockStartAddr).
    {
      intro. subst partition. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold bentryEndAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hend; trivial. rewrite HgetMappedBEq in *; trivial.
    unfold scentryNext in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hnext; trivial.
    specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped Hend Hsce HbeqNextNull
      Hnext). destruct Hcons0 as (HstartNext & HnextMapped). unfold bentryStartAddr in *. rewrite HlookupsEq; auto.
    intro. subst scnext. unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
    (* END blockAndNextAreSideBySide *)
  }

  assert(parentBlocksBoundsIfNoNext s).
  { (* BEGIN parentBlocksBoundsIfNoNext s *)
    assert(Hcons0: parentBlocksBoundsIfNoNext s0) by intuition.
    intros partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped Hstart Hend Hsce
      Hnext HbeqPartRoot HlookupPart. unfold bentryStartAddr in *. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    apply HgetPartsImpl in HpartIsPart. unfold bentryEndAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq in Hend; trivial.
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold scentryNext in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hnext; trivial. rewrite HlookupsEq in HlookupPart; trivial.
    specialize(Hcons0 partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped Hstart Hend
      Hsce Hnext HbeqPartRoot HlookupPart).
    destruct Hcons0 as [blockParent [startParent (HBPMapped & HstartP & Hcons0)]]. exists blockParent.
    exists startParent. assert(parent pdentry <> blockStartAddr).
    {
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s0)).
      {
        assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent. rewrite HlookupPart.
        reflexivity.
      }
      intro Hcontra. rewrite Hcontra in *. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    rewrite HgetMappedBEq; trivial. unfold bentryStartAddr in *. assert(blockParent <> blockStartAddr).
    {
      intro. subst blockParent. unfold isPDT in *.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; auto.
    (* END parentBlocksBoundsIfNoNext *)
  }

  assert(pdchildIsPDT s).
  { (* BEGIN pdchildIsPDT s *)
    assert(Hcons0: pdchildIsPDT s0) by intuition.
    intros part block sh1entryaddrB idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull.
    assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1; trivial. rewrite HgetMappedBEq in *; trivial. unfold sh1entryPDchild in *.
    assert(sh1entryaddrB <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial.
    specialize(Hcons0 part block sh1entryaddrB idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull).
    rewrite HgetChildrenEqNotStart; trivial.
    (* END pdchildIsPDT *)
  }

  assert(childBlockNullIfChildNull s).
  { (* BEGIN childBlockNullIfChildNull s *)
    assert(Hcons0: childBlockNullIfChildNull s0) by intuition.
    intros part block sh1entryaddrB HpartIsPart HblockMapped Hsh1 HPDchildB. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1; trivial. rewrite HgetMappedBEq in *; trivial. unfold sh1entryPDchild in *.
    assert(sh1entryaddrB <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial.
    specialize(Hcons0 part block sh1entryaddrB HpartIsPart HblockMapped Hsh1 HPDchildB).
    unfold sh1entryInChildLocation in *. rewrite HlookupsEq; trivial.
    destruct (lookup sh1entryaddrB (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    destruct Hcons0 as (Hloc & HlocIsBE). split; trivial. intro Hcontra. exfalso; congruence.
    (* END pdchildIsPDT *)
  }

  assert(HpartialChildLocProps: forall partition block sh1entryaddr blockChild idchild startaddr,
    idchild <> blockStartAddr
    -> In partition (getPartitions multiplexer s) -> In block (getMappedBlocks partition s)
    -> sh1entryAddr block sh1entryaddr s -> sh1entryPDchild sh1entryaddr idchild s
    -> sh1entryInChildLocationWeak sh1entryaddr blockChild s -> idchild <> nullAddr
    -> bentryStartAddr block startaddr s -> ~ isKS startaddr s
    -> blockChild <> nullAddr /\ In blockChild (getMappedBlocks idchild s) /\ bentryStartAddr blockChild startaddr s).
  { (* BEGIN partial childLocMappedInChild s *)
    assert(Hcons0: childLocMappedInChild s0) by intuition.
    intros part block sh1entryaddrB blockChild idchild startaddr HbeqChildStart HpartIsPart HblockMapped Hsh1
      HPDchildB Hloc HbeqIdChildNull Hstart HstartNotKS. unfold bentryStartAddr in *. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1; trivial. rewrite HlookupsEq in Hstart; trivial.
    rewrite HgetMappedBEq in *; trivial. assert(HstartNotKSs0: ~isKS startaddr s0).
    {
      contradict HstartNotKS. unfold isKS in *. rewrite HlookupsEq; trivial. intro. subst startaddr.
      unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    unfold sh1entryInChildLocationWeak in *. unfold sh1entryPDchild in *. assert(sh1entryaddrB <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. rewrite HlookupsEq in Hloc; trivial.
    specialize(Hcons0 part block sh1entryaddrB blockChild idchild startaddr HpartIsPart HblockMapped Hsh1
      HPDchildB Hloc HbeqIdChildNull Hstart HstartNotKSs0). assert(blockChild <> blockStartAddr).
    {
      destruct Hcons0 as (_ & _ & HstartC). intro. subst blockChild. unfold bentryStartAddr in *.
      rewrite HlookupStart in *. congruence.
    }
    rewrite HlookupsEq; assumption.
    (* END partial childLocMappedInChild *)
  }

  assert(HpartialSameStart: forall partition block sh1entryaddr blockChild idchild,
    idchild <> blockStartAddr
    -> In partition (getPartitions multiplexer s) -> In block (getMappedBlocks partition s)
    -> sh1entryAddr block sh1entryaddr s -> sh1entryPDchild sh1entryaddr idchild s
    -> sh1entryInChildLocationWeak sh1entryaddr blockChild s -> idchild <> nullAddr
    -> blockChild <> nullAddr
    -> (forall startaddr, bentryStartAddr block startaddr s -> bentryStartAddr blockChild startaddr s)
          /\ In blockChild (getMappedBlocks idchild s)).
  { (* BEGIN partial childLocHasSameStart s *)
    assert(Hcons0: childLocHasSameStart s0) by intuition.
    intros part block sh1entryaddrB blockChild idchild HbeqChildStart HpartIsPart HblockMapped Hsh1 HPDchildB Hloc
      HbeqIdChildNull HbeqBCNull. unfold bentryStartAddr in *. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1; trivial. rewrite HlookupsEq; trivial. rewrite HgetMappedBEq in *; trivial.
    unfold sh1entryInChildLocationWeak in *. unfold sh1entryPDchild in *. assert(sh1entryaddrB <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. rewrite HlookupsEq in Hloc; trivial.
    specialize(Hcons0 part block sh1entryaddrB blockChild idchild HpartIsPart HblockMapped Hsh1
      HPDchildB Hloc HbeqIdChildNull HbeqBCNull). destruct Hcons0 as (HsameStart & HBCMapped). split; trivial.
    intros startaddr Hstart. specialize(HsameStart startaddr Hstart). unfold bentryStartAddr in *.
    rewrite HlookupsEq; trivial. intro. subst blockChild. rewrite HlookupStart in *. congruence.
    (* END partial childLocHasSameStart *)
  }

  assert(accessibleBlocksArePresent s).
  { (* BEGIN accessibleBlocksArePresent s *)
    assert(Hcons0: accessibleBlocksArePresent s0) by intuition.
    intros block HAflag. unfold bentryAFlag in *. unfold bentryPFlag. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HAflag; trivial. specialize(Hcons0 block HAflag). rewrite HlookupsEq; assumption.
    (* END accessibleBlocksArePresent *)
  }

  assert(isPDT currentPart s).
  {
    unfold isPDT. rewrite HlookupsEq; trivial. intro. subst blockStartAddr. unfold getPartitions in *.
    replace (maxAddr+2) with (S (maxAddr+1)) in HcurrNotInDesc; try(lia). simpl in HcurrNotInDesc.
    apply Decidable.not_or in HcurrNotInDesc. destruct HcurrNotInDesc. congruence.
  }

  assert(verticalSharing s).
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild. assert(pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. apply HgetChildrenImpl in HchildIsChild.
    rewrite HgetMappedPEq; trivial. specialize(HVSs0 pdparent child HparentIsPart HchildIsChild).
    unfold getUsedPaddr. intros addr HaddrUsedChild. destruct (beqAddr child blockStartAddr) eqn:HbeqChildStart.
    - rewrite <-beqAddrTrue in HbeqChildStart. subst child. unfold getConfigPaddr in *. unfold getMappedPaddr in *.
      unfold getConfigBlocks in *. unfold getMappedBlocks in *. unfold getKSEntries in *. exfalso. simpl in *.
      rewrite HlookupStarts in *. simpl in *. congruence.
    - rewrite <-beqAddrFalse in *. rewrite HgetConfigEq in *; trivial. rewrite HgetMappedPEq in *; trivial.
      apply HVSs0; assumption.
    (* END verticalSharing *)
  }

  assert(partitionsIsolation s).
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
    assert(pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. apply HgetChildrenImpl in Hchild1IsChild.
    apply HgetChildrenImpl in Hchild2IsChild.
    specialize(HPIs0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
    unfold getUsedPaddr. destruct (beqAddr child1 blockStartAddr) eqn:HbeqChild1Start.
    - rewrite <-beqAddrTrue in HbeqChild1Start. subst child1. unfold getConfigPaddr at 1. unfold getMappedPaddr at 1.
      intros addr HaddrUsed. unfold getConfigBlocks in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
      simpl in *. rewrite HlookupStarts in *. simpl in *. exfalso; congruence.
    - destruct (beqAddr child2 blockStartAddr) eqn:HbeqChild2Start.
      + rewrite <-beqAddrTrue in HbeqChild2Start. subst child2. apply Lib.disjointPermut. unfold getConfigPaddr at 1.
        unfold getMappedPaddr at 1. intros addr HaddrUsed. unfold getConfigBlocks in *. unfold getMappedBlocks in *.
        unfold getKSEntries in *. simpl in *. rewrite HlookupStarts in *. simpl in *. exfalso; congruence.
      + rewrite <-beqAddrFalse in *. rewrite HgetConfigEq; trivial. rewrite HgetMappedPEq; trivial.
        rewrite HgetConfigEq; trivial. rewrite HgetMappedPEq; trivial.
    (* END partitionsIsolation *)
  }

  assert(kernelDataIsolation s).
  { (* BEGIN kernelDataIsolation s *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart. apply HgetPartsImpl in Hpart1IsPart.
    apply HgetPartsImpl in Hpart2IsPart. specialize(HKDIs0 part1 part2 Hpart1IsPart Hpart2IsPart).
    destruct (beqAddr part1 blockStartAddr) eqn:HbeqPart1Start.
    - rewrite <-beqAddrTrue in HbeqPart1Start. subst part1. unfold getAccessibleMappedPaddr.
      unfold getAccessibleMappedBlocks. intros addr HaddrUsed. rewrite HlookupStarts in *. simpl in *.
      exfalso; congruence.
    - destruct (beqAddr part2 blockStartAddr) eqn:HbeqPart2Start.
      + rewrite <-beqAddrTrue in HbeqPart2Start. subst part2. apply Lib.disjointPermut. unfold getConfigPaddr.
        unfold getMappedPaddr. intros addr HaddrUsed. unfold getConfigBlocks in *. unfold getMappedBlocks in *.
        unfold getKSEntries in *. simpl in *. rewrite HlookupStarts in *. simpl in *. exfalso; congruence.
      + rewrite <-beqAddrFalse in *. rewrite HgetConfigEq; trivial. rewrite HgetAccMappedPEq; trivial.
    (* END kernelDataIsolation *)
  }

  assert(HpartialPDTIfPDFlag: forall idPDchild sh1entryaddr, idPDchild <> currentPart (*TODO HERE change that*)
    -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
    -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
        /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s)).
  { (* BEGIN partial PDTIfPDFlag s *)
    assert(Hcons0: PDTIfPDFlag s0) by intuition. intros idPDchild sh1entryaddr HbeqBlockCurr HcheckChildB.
    unfold sh1entryAddr in *. unfold checkChild in *. unfold bentryAFlag. unfold bentryPFlag. unfold entryPDT.
    assert(HlookupBlockEq: lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s0) beqAddr).
    { apply HlookupsEq. destruct HcheckChildB. intro. subst idPDchild. rewrite HlookupStarts in *. congruence. }
    unfold bentryStartAddr. rewrite HlookupBlockEq in *.
    assert(HcheckChildBs0: true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0).
    {
      destruct HcheckChildB as (HcheckChildB & Hsh1). split; trivial. unfold checkChild.
      destruct (lookup idPDchild (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite <-HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence.
    }
    specialize(Hcons0 idPDchild sh1entryaddr HcheckChildBs0).
    destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartBIsPDT)]). split; try(split); trivial.
    exists startaddr. split; trivial. unfold entryPDT in *.
    destruct (lookup idPDchild (memory s0) beqAddr) eqn:HlookupBlock; try(congruence). destruct v; try(congruence).
    rewrite HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *. rewrite HlookupStart in *. subst startaddr.
    assert(HPDchildB: sh1entryPDchild sh1entryaddr nullAddr s0).
    {
      destruct HcheckChildB. subst sh1entryaddr. assert(Hres: PDflagMeansNoChild s0) by intuition. apply Hres.
      - unfold isBE. rewrite HlookupBlock. trivial.
      - unfold sh1entryPDflag. destruct HcheckChildBs0. unfold checkChild in *. rewrite HlookupBlock in *.
        destruct (lookup (CPaddr (idPDchild+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    }
    (*TODO HERE use addressesBloodlineIfNotShared to prove that it's in a parent, but since it isn't shared in either,
      it must be in currentPart*)
    (* END partial PDTIfPDFlag *)
  }

  instantiate(1 := fun s => nullAddrExists s /\ wellFormedFstShadowIfBlockEntry s
    /\ (*partial PDTIfPDFlag*)
    /\ AccessibleNoPDFlag s /\ FirstFreeSlotPointerIsBEAndFreeSlot s /\ multiplexerIsPDT s
    /\ currentPartitionInPartitionsList s /\ wellFormedShadowCutIfBlockEntry s /\ BlocksRangeFromKernelStartIsBE s
    /\ KernelStructureStartFromBlockEntryAddrIsKS s /\ sh1InChildLocationIsBE s /\ StructurePointerIsKS s
    /\ NextKSIsKS s /\ NextKSOffsetIsPADDR s /\ NoDupInFreeSlotsList s /\ freeSlotsListIsFreeSlot s
    /\ DisjointFreeSlotsLists s /\ inclFreeSlotsBlockEntries s /\ DisjointKSEntries s /\ noDupPartitionTree s
    /\ (*partial isParent*)
    /\ isChild s /\ noDupKSEntriesList s /\ noDupMappedBlocksList s /\ wellFormedBlock s
    /\ (*partial parentOfPartitionIsPartition*)
    /\ NbFreeSlotsISNbFreeSlotsInList s /\ maxNbPrepareIsMaxNbKernels s
    /\ blockInChildHasAtLeastEquivalentBlockInParent s /\ partitionTreeIsTree s /\ kernelEntriesAreValid s
    /\ nextKernelIsValid s /\ noDupListOfKerns s /\ MPUsizeIsBelowMax s /\ originIsParentBlocksStart s
    /\ nextImpliesBlockWasCut s /\ blocksAddressesTypes s /\ notPDTIfNotPDflag s /\ nextKernAddrIsInSameBlock s
    /\ PDflagMeansNoChild s /\ nbPrepareIsNbKern s /\ pdchildIsPDT s /\ childBlockNullIfChildNull s
    /\ accessibleBlocksArePresent s /\ noDupMappedPaddrList s /\ accessibleParentPaddrIsAccessibleIntoChild s
    /\ sharedBlockPointsToChild s /\ adressesRangePreservedIfOriginAndNextOk s /\ childsBlocksPropsInParent s
    /\ noChildImpliesAddressesNotShared s /\ kernelsAreNotAccessible s /\ blockAndNextAreSideBySide s
    /\ parentBlocksBoundsIfNoNext s
    /\ (*partial childLocMappedInChild*)
    /\ (*partial childLocHasSameStart*)).

  (*TODO HERE*)
}
intro currKernelStructureStart. eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr **)
  eapply weaken. apply readBlockStartFromBlockEntryAddr. intros s Hprops.
  
}
intro globalIdPDChildToDelete. eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr **)
  eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops.
  
}
intro endPDChildToDelete. eapply bindRev.
{ (** Internal.deleteSharedBlocksRec **)
  eapply weaken. apply ?. intros s Hprops.
  
}
eapply bindRev.
{ (** MAL.writeBlockAccessibleFromBlockEntryAddr **)
  eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr. intros s Hprops.
  
}
eapply bindRev.
{ (** MAL.writeSh1EntryFromBlockEntryAddr **)
  eapply weaken. apply writeSh1EntryFromBlockEntryAddr. intros s Hprops.
  
}
eapply bindRev.
{ (** Internal.checkBlockCut **)
  eapply weaken. apply checkBlockCut. intros s Hprops.
  
}
intro isCut. destruct isCut.
- eapply weaken. apply WP.ret. intros s Hprops. simpl.
  
- eapply bindRev.
  { (** Internal.writeAccessibleRec **)
    eapply weaken. apply ?. intros s Hprops.
    
  }
  eapply weaken. apply WP.ret. intros s Hprops. simpl.
  
Qed.
