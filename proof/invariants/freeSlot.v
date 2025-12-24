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

(**  * Summary 
    In this file we formalize and prove all invariants of the MAL and MALInternal functions *)
Require Import Model.Monad Model.Lib Model.MAL Model.ADT.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare Proof.InternalLemmas Proof.InternalLemmas2
  Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants initStructure.
From Stdlib Require Import Compare_dec Bool Lia Logic.ProofIrrelevance List.
Import ListNotations.

(* Whatever the pd, be it a child or the current partition, removing a block
	doesn't change the security properties *)
(* no lemma to use :
1) create a temporary lemma with the desired output properties
2) admit the lemma and see if this is enough to continue the principal proof
3) if yes, then prove the lemma *)
(*Definition defaultBlockEntry defaultentry s: Prop :=
let emptyblock := CBlock nullAddr nullAddr in
let entriesnb := getKernelStructureEntriesNb in
defaultentry = 
match defaultentry with 
|Some (CBlockEntry false false false false false entriesnb emptyblock) => True
|_ => False
end.
*)

Definition cons1Free s :=
nullAddrExists s
/\ wellFormedFstShadowIfBlockEntry s
/\ PDTIfPDFlag s
/\ AccessibleNoPDFlag s
/\ FirstFreeSlotPointerIsBEAndFreeSlot s
/\ multiplexerIsPDT s
/\ currentPartitionInPartitionsList s
/\ wellFormedShadowCutIfBlockEntry s
/\ BlocksRangeFromKernelStartIsBE s
/\ KernelStructureStartFromBlockEntryAddrIsKS s
/\ sh1InChildLocationIsBE s
/\ StructurePointerIsKS s
/\ NextKSIsKS s
/\ NextKSOffsetIsPADDR s
/\ NoDupInFreeSlotsList s
/\ freeSlotsListIsFreeSlot s
/\ DisjointFreeSlotsLists s
/\ inclFreeSlotsBlockEntries s
/\ DisjointKSEntries s
/\ noDupPartitionTree s
/\ isParent s
/\ isChild s
/\ noDupKSEntriesList s
/\ noDupMappedBlocksList s
/\ wellFormedBlock s
/\ parentOfPartitionIsPartition s
/\ NbFreeSlotsISNbFreeSlotsInList s
/\ maxNbPrepareIsMaxNbKernels s
(*/\ blockInChildHasAtLeastEquivalentBlockInParent s*)
/\ partitionTreeIsTree s
/\ kernelEntriesAreValid s
/\ nextKernelIsValid s
/\ noDupListOfKerns s
/\ MPUsizeIsBelowMax s
(*/\ originIsParentBlocksStart s*)
(*/\ nextImpliesBlockWasCut s*)
/\ blocksAddressesTypes s
/\ notPDTIfNotPDflag s
/\ nextKernAddrIsInSameBlock s
/\ blockBelongsToAPart s
/\ PDflagMeansNoChild s
/\ nbPrepareIsNbKern s
/\ pdchildIsPDT s
/\ childBlockNullIfChildNull s
(*/\ childLocHasSameStart s*).


Lemma freeSlot (pd blockToFree: paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT pd s /\ isBE blockToFree s /\ cons1Free s
    /\ sh1entryPDflag (CPaddr (blockToFree+sh1offset)) false s
    /\ bentryPFlag blockToFree true s
    /\ In blockToFree (getMappedBlocks pd s)
}}
Internal.freeSlot pd blockToFree
{{fun _ (s : state) => exists s0 s1 s2 s3 s4 s5 s6 pdentry pdentry1 pdentry2 pdentry3 realMPU emptyBentry freeBentry
  currFirstFreeSlot blockToFreeIdx,
    s = {| currentPartition := currentPartition s6; memory := add pd (PDT pdentry3) (memory s6) beqAddr |}
    /\ s6 = {| currentPartition := currentPartition s5; memory := add pd (PDT pdentry2) (memory s5) beqAddr |}
    /\ s5 = {|
              currentPartition := currentPartition s4;
              memory := add blockToFree (BE freeBentry) (memory s4) beqAddr
            |}
    /\ s4 = {|
              currentPartition := currentPartition s3;
              memory :=
                add (CPaddr (blockToFree + scoffset)) (SCE {| origin := nullAddr; next := nullAddr |}) 
                  (memory s3) beqAddr
            |}
    /\ s3 = {|
              currentPartition := currentPartition s2;
              memory :=
                add (CPaddr (blockToFree + sh1offset))
                  (SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |}) 
                  (memory s2) beqAddr
            |}
    /\ s2 = {|
              currentPartition := currentPartition s1;
              memory := add blockToFree (BE emptyBentry) (memory s1) beqAddr
            |}
    /\ s1 = {|
              currentPartition := currentPartition s0;
              memory := add pd (PDT pdentry1) (memory s0) beqAddr
            |}
    /\ cons1Free s
    /\ StructurePointerIsKS s6
    /\ StructurePointerIsKS s5
    /\ lookup pd (memory s5) beqAddr = Some (PDT pdentry1)
    /\ lookup blockToFree (memory s4) beqAddr = Some (BE emptyBentry)
    /\ pdentryFirstFreeSlot pd currFirstFreeSlot s4
    /\ bentryBlockIndex blockToFree blockToFreeIdx s1
    /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
    /\ isBE blockToFree s0
    /\ pdentryMPU pd realMPU s0
    /\ cons1Free s0
    /\ getPartitions multiplexer s = getPartitions multiplexer s0
    /\ (forall part, isPDT part s1 -> getChildren part s = getChildren part s0)
    /\ (forall part, isPDT part s2
        -> pd <> part
        -> getMappedBlocks part s = getMappedBlocks part s0)
    /\ (forall block,
          (In block (getMappedBlocks pd s0) -> blockToFree = block \/ In block (getMappedBlocks pd s))
          /\ (In block (getMappedBlocks pd s) -> In block (getMappedBlocks pd s0))
          /\ (NoDup (getMappedBlocks pd s0) -> NoDup (getMappedBlocks pd s)))
    /\ (exists l l0, emptyBentry
          = {|
              read := false;
              write := false;
              exec := false;
              present := false;
              accessible := false;
              blockindex := blockToFreeIdx;
              blockrange := {|
                              startAddr := nullAddr;
                              endAddr := nullAddr;
                              Hsize := l0
                            |};
              Hidx := l
            |})
    /\ pdentry1 = {|
                    structure := structure pdentry;
                    firstfreeslot := firstfreeslot pdentry;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := removeBlockFromPhysicalMPUAux blockToFree realMPU;
                    vidtAddr := vidtAddr pdentry
                  |}
    /\ pdentry2 = {|
                    structure := structure pdentry1;
                    firstfreeslot := blockToFree;
                    nbfreeslots := nbfreeslots pdentry1;
                    nbprepare := nbprepare pdentry1;
                    parent := parent pdentry1;
                    MPU := MPU pdentry1;
                    vidtAddr := vidtAddr pdentry1
                  |}
    /\ pdentry3 = {|
                    structure := structure pdentry2;
                    firstfreeslot := firstfreeslot pdentry2;
                    nbfreeslots := CIndex (nbfreeslots pdentry1 +1);
                    nbprepare := nbprepare pdentry2;
                    parent := parent pdentry2;
                    MPU := MPU pdentry2;
                    vidtAddr := vidtAddr pdentry2
                  |}
    /\ nbfreeslots pdentry1 + 1 <= maxIdx
    /\ (exists l l0, freeBentry
        = {|
            read := read emptyBentry;
            write := write emptyBentry;
            exec := exec emptyBentry;
            present := present emptyBentry;
            accessible := accessible emptyBentry;
            blockindex := blockindex emptyBentry;
            blockrange := {|
                            startAddr := startAddr (blockrange emptyBentry);
                            endAddr := currFirstFreeSlot;
                            Hsize := l0
                          |};
            Hidx := l
          |})
    /\ P s0
    /\ getPartitions multiplexer s1 = getPartitions multiplexer s0
    /\ PDTIfPDFlag s1
    /\ multiplexerIsPDT s1
    /\ (forall part, isPDT part s2 -> getMappedBlocks part s = getMappedBlocks part s2)
    /\ (forall partition, isPDT partition s2 -> getKSEntries partition s = getKSEntries partition s0)
    /\ (forall pdparent parentsList, isParentsList s0 parentsList pdparent
          -> isParentsList s parentsList pdparent)
}}.
Proof.
unfold Internal.freeSlot. eapply bindRev.
{ (** MAL.removeBlockFromPhysicalMPU *)
	eapply weaken. apply removeBlockFromPhysicalMPU. intros s Hprops. simpl. split. apply Hprops. intuition.
}
intro. eapply bindRev.
{ (** MAL.readBlockIndexFromBlockEntryAddr *)
	eapply weaken. apply readBlockIndexFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
	destruct Hprops as [s0 [pdentry [realMPU (_ & (_ & _ & HblockIsBE & _) & HlookupPart & Hs)]]]. unfold isBE in *.
  rewrite Hs. simpl. destruct (beqAddr pd blockToFree) eqn:HbeqPartBlock.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPartBlock. subst pd. rewrite HlookupPart in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
intro blockToFreeIdx. eapply bindRev.
{ (** writeBlockEntryFromBlockEntryAddr *)
	eapply weaken. apply writeBlockEntryFromBlockEntryAddrLight. intros s Hprops. simpl.
	destruct Hprops as ([s0 [pdentry [realMPU (HMPU & (HP & HpartIsPDT & HblockIsBEs0 & Hconsists0 & HPDflags0 &
    HblockIsMappeds0) & HlookupPart & Hs)]]] & HblockIsBE & Hidx).
  instantiate(1 := fun _ s => exists s0 s1 pdentry realMPU,
    s = {|
          currentPartition := currentPartition s1;
          memory :=
            add blockToFree
              (BE (CBlockEntry false false false false false blockToFreeIdx (CBlock nullAddr nullAddr)))
              (memory s1) beqAddr
        |}
    /\ bentryBlockIndex blockToFree blockToFreeIdx s1
    /\ s1 = {|
              currentPartition := currentPartition s0;
              memory :=
                add pd
                  (PDT
                     {|
                       structure := structure pdentry;
                       firstfreeslot := firstfreeslot pdentry;
                       nbfreeslots := nbfreeslots pdentry;
                       nbprepare := nbprepare pdentry;
                       parent := parent pdentry;
                       MPU := removeBlockFromPhysicalMPUAux blockToFree realMPU;
                       vidtAddr := vidtAddr pdentry
                     |})
                  (memory s0) beqAddr
            |}
    /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
    /\ isBE blockToFree s0
    /\ pdentryMPU pd realMPU s0
    /\ cons1Free s0
    /\ sh1entryPDflag (CPaddr (blockToFree+sh1offset)) false s0
    /\ bentryPFlag blockToFree true s0
    /\ In blockToFree (getMappedBlocks pd s0)
    /\ pdentryMPU pd realMPU s0
    /\ P s0).
  simpl. exists s0. exists s. exists pdentry. exists realMPU. intuition.
}
intro. eapply bindRev.
{ (** MAL.writeSh1EntryFromBlockEntryAddrLight **)
  eapply weaken. apply writeSh1EntryFromBlockEntryAddrLight. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s0 [s1 [pdentry [realMPU (Hs & Hblkidx & Hs1 & HlookupParts0 & HblockIsBEs0 & HpdMPUs0 &
    Hconsists0 & _)]]]].
  assert(HkernIsKS: KernelStructureStartFromBlockEntryAddrIsKS s0) by (unfold cons1Free in *; intuition).
  unfold bentryBlockIndex in *. rewrite Hs1 in Hblkidx. simpl in *.
  destruct (beqAddr pd blockToFree) eqn:HbeqPartBlock; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(HkernIsKS blockToFree blockToFreeIdx HblockIsBEs0 Hblkidx). unfold isKS in *. rewrite Hs. rewrite Hs1.
  simpl. rewrite IL.beqAddrTrue.
  exists (CBlockEntry false false false false false blockToFreeIdx (CBlock nullAddr nullAddr)). split; trivial.
  unfold CBlockEntry. destruct (lookup blockToFree (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite Hblkidx in *.
  assert(blockindex b < kernelStructureEntriesNb) by (apply Hidx).
  destruct (lt_dec (blockindex b) kernelStructureEntriesNb); try(lia). simpl. split.
  - destruct (beqAddr blockToFree (CPaddr (blockToFree - blockindex b))) eqn:HbeqBlockKern.
    + simpl. rewrite <-DTL.beqAddrTrue in HbeqBlockKern. rewrite HbeqBlockKern in HlookupBlock.
      rewrite HlookupBlock in *. assumption.
    + rewrite beqAddrFalse in HbeqPartBlock. rewrite HbeqPartBlock. simpl.
      destruct (beqAddr pd (CPaddr (blockToFree - blockindex b))) eqn:HbeqPartKern.
      { rewrite <-DTL.beqAddrTrue in HbeqPartKern. subst pd. rewrite HlookupParts0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - destruct (le_dec (blockindex b) blockToFree); try(lia). exfalso. unfold CPaddr in HkernIsKS.
    assert(Hzero: blockToFree - blockindex b = 0) by lia. rewrite Hzero in *.
    destruct (le_dec 0 maxAddr); try(lia).
    assert(Hnull: isPADDR nullAddr s0) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
    assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_1 0 l0 |} = nullAddr).
    { cbn. f_equal. apply proof_irrelevance. }
    rewrite HnullEq in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
intro. eapply bindRev.
{ (** MAL.writeSCEntryFromBlockEntryAddrLight **)
  eapply weaken. apply writeSCEntryFromBlockEntryAddrLight. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s2 (Hs & [s0 [s1 [pdentry [realMPU (Hs2 & Hblkidx & Hs1 & HlookupParts0 & HblockIsBEs0 &
    HpdMPUs0 & Hconsists0 & _)]]]])].
  assert(HkernIsKS: KernelStructureStartFromBlockEntryAddrIsKS s0) by (unfold cons1Free in *; intuition).
  unfold bentryBlockIndex in *. rewrite Hs1 in Hblkidx. simpl in *.
  destruct (beqAddr pd blockToFree) eqn:HbeqPartBlock; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  assert(Hsh1: wellFormedFstShadowIfBlockEntry s0) by (unfold cons1Free in *; intuition).
  specialize(Hsh1 blockToFree HblockIsBEs0). specialize(HkernIsKS blockToFree blockToFreeIdx HblockIsBEs0 Hblkidx).
  unfold isKS in *. rewrite Hs. rewrite Hs2. rewrite Hs1. simpl. unfold isSHE in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) blockToFree) eqn:HbeqSh1Block.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1Block. rewrite HbeqSh1Block in *. exfalso.
    destruct (lookup blockToFree (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  exists (CBlockEntry false false false false false blockToFreeIdx (CBlock nullAddr nullAddr)).
  unfold CBlockEntry. destruct (lookup blockToFree (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite Hblkidx in *.
  assert(blockindex b < kernelStructureEntriesNb) by (apply Hidx).
  destruct (lt_dec (blockindex b) kernelStructureEntriesNb); try(lia). simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (blockToFree - blockindex b))) eqn:HbeqSh1Kern.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1Kern. rewrite HbeqSh1Kern in *. exfalso.
    destruct (lookup (CPaddr (blockToFree - blockindex b)) (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
  }
  assert(HbeqBlockSh1 : beqAddr blockToFree (CPaddr (blockToFree + sh1offset)) = false).
  { rewrite beqAddrSym. assumption. }
  rewrite HbeqBlockSh1. simpl. rewrite IL.beqAddrTrue. split; trivial. split.
  - destruct (beqAddr blockToFree (CPaddr (blockToFree - blockindex b))) eqn:HbeqBlockKern.
    + simpl. rewrite <-DTL.beqAddrTrue in HbeqBlockKern. rewrite HbeqBlockKern in HlookupBlock.
      rewrite HlookupBlock in *. assumption.
    + rewrite beqAddrFalse in HbeqPartBlock. rewrite HbeqPartBlock.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. simpl.
      destruct (beqAddr pd (CPaddr (blockToFree - blockindex b))) eqn:HbeqPartKern.
      { rewrite <-DTL.beqAddrTrue in HbeqPartKern. subst pd. rewrite HlookupParts0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - destruct (le_dec (blockindex b) blockToFree); try(lia). exfalso. unfold CPaddr in HkernIsKS.
    assert(Hzero: blockToFree - blockindex b = 0) by lia. rewrite Hzero in *.
    destruct (le_dec 0 maxAddr); try(lia).
    assert(Hnull: isPADDR nullAddr s0) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
    assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_1 0 l0 |} = nullAddr).
    { cbn. f_equal. apply proof_irrelevance. }
    rewrite HnullEq in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
intro. eapply bindRev.
{ (** MAL.readPDFirstFreeSlotPointer **)
  eapply weaken. apply readPDFirstFreeSlotPointer. intros s Hprops. simpl. split. apply Hprops. unfold isPDT.
  destruct Hprops as [s3 (Hs & [s2 (Hs3 & [s0 [s1 [pdentry [realMPU (Hs2 & Hblkidx & Hs1 & HlookupParts0 &
    HblockIsBEs0 & _ & Hconsists0 & _)]]]])])]. rewrite Hs. simpl.
  assert(Hsh1: wellFormedFstShadowIfBlockEntry s0) by (unfold cons1Free in *; intuition).
  specialize(Hsh1 blockToFree HblockIsBEs0). unfold isSHE in *.
  assert(Hsce: wellFormedShadowCutIfBlockEntry s0) by (unfold cons1Free in *; intuition).
  specialize(Hsce blockToFree HblockIsBEs0). unfold isSCE in *. destruct Hsce as [scentryaddr (Hsce & HsceVal)].
  subst scentryaddr. destruct (beqAddr (CPaddr (blockToFree + scoffset)) pd) eqn:HbeqScePart.
  { rewrite <-DTL.beqAddrTrue in HbeqScePart. rewrite HbeqScePart in *. rewrite HlookupParts0 in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) pd) eqn:HbeqSh1Part.
  { rewrite <-DTL.beqAddrTrue in HbeqSh1Part. rewrite HbeqSh1Part in *. rewrite HlookupParts0 in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  unfold isBE in *. destruct (beqAddr blockToFree pd) eqn:HbeqBlockPart.
  { rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *. rewrite HlookupParts0 in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
  rewrite beqAddrTrue. trivial.
}
intro currFirstFreeSlot. eapply bindRev.
{ (** MAL.writeBlockEndFromBlockEntryAddr **)
  eapply weaken. apply writeBlockEndFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as ([s3 (Hs & [s2 (Hs3 & [s0 [s1 [pdentry [realMPU (Hs2 & Hblkidx & Hs1 & HlookupParts0 &
    HblockIsBEs0 & HpdMPUs0 & Hconsists0 & HPDflags0 & HPflag & HblockMappeds0 & _ & HP)]]]])])] & HfirstFree).
  assert(HnewB: exists l l0, CBlockEntry false false false false false blockToFreeIdx (CBlock nullAddr nullAddr)
    = {|
        read := false;
        write := false;
        exec := false;
        present := false;
        accessible := false;
        blockindex := blockToFreeIdx;
        blockrange := {|
                        startAddr := nullAddr;
                        endAddr := nullAddr;
                        Hsize := l0
                      |};
        Hidx := l
      |}).
  {
    unfold CBlockEntry. unfold bentryBlockIndex in *.
    destruct (lookup blockToFree (memory s1) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite Hblkidx in *.
    assert(blockindex b < kernelStructureEntriesNb) by (apply Hidx).
    destruct (lt_dec (blockindex b) kernelStructureEntriesNb); try(lia). simpl. unfold CBlock. cbn.
    exists (ADT.CBlockEntry_obligation_1 (blockindex b) l). exists (ADT.CBlock_obligation_1
      {| p := 0; Hp := ADT.CPaddr_obligation_1 0 (PeanoNat.Nat.le_0_l maxAddr) |}
      {| p := 0; Hp := ADT.CPaddr_obligation_1 0 (PeanoNat.Nat.le_0_l maxAddr) |}
      (PeanoNat.Nat.le_0_l maxIdx)). reflexivity.
  }
  set(emptyBentry := CBlockEntry false false false false false blockToFreeIdx (CBlock nullAddr nullAddr)).
  fold emptyBentry in HnewB. fold emptyBentry in Hs2.
  assert(HlookupBlock: lookup blockToFree (memory s) beqAddr = Some (BE emptyBentry)).
  {
    assert(Hsh1: wellFormedFstShadowIfBlockEntry s0) by (unfold cons1Free in *; intuition).
    specialize(Hsh1 blockToFree HblockIsBEs0). unfold isSHE in *.
    assert(Hsce: wellFormedShadowCutIfBlockEntry s0) by (unfold cons1Free in *; intuition).
    specialize(Hsce blockToFree HblockIsBEs0). unfold isSCE in *. destruct Hsce as [scentryaddr (Hsce & HsceVal)].
    subst scentryaddr. unfold isBE in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) blockToFree) eqn:HbeqSceBlock.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceBlock. rewrite HbeqSceBlock in *.
      destruct (lookup blockToFree (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) blockToFree) eqn:HbeqSh1Block.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Block. rewrite HbeqSh1Block in *.
      destruct (lookup blockToFree (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite IL.beqAddrTrue. reflexivity.
  }
  exists emptyBentry. split; trivial.
  instantiate(1 := fun _ s => exists s0 s1 s2 s3 s4 pdentry realMPU emptyBentry,
    s = {|
          currentPartition := currentPartition s4;
          memory :=
            add blockToFree
              (BE
                 (CBlockEntry (read emptyBentry) (write emptyBentry) (exec emptyBentry) 
                    (present emptyBentry) (accessible emptyBentry) (blockindex emptyBentry)
                    (CBlock (startAddr (blockrange emptyBentry)) currFirstFreeSlot)))
              (memory s4) beqAddr
        |}
    /\ s4 = {|
              currentPartition := currentPartition s3;
              memory :=
                add (CPaddr (blockToFree + scoffset)) (SCE {| origin := nullAddr; next := nullAddr |}) 
                  (memory s3) beqAddr
            |}
    /\ s3 = {|
              currentPartition := currentPartition s2;
              memory :=
                add (CPaddr (blockToFree + sh1offset))
                  (SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |}) 
                  (memory s2) beqAddr
            |}
    /\ s2 = {|
              currentPartition := currentPartition s1;
              memory := add blockToFree (BE emptyBentry) (memory s1) beqAddr
            |}
    /\ s1 = {|
              currentPartition := currentPartition s0;
              memory :=
                add pd
                  (PDT
                     {|
                       structure := structure pdentry;
                       firstfreeslot := firstfreeslot pdentry;
                       nbfreeslots := nbfreeslots pdentry;
                       nbprepare := nbprepare pdentry;
                       parent := parent pdentry;
                       MPU := removeBlockFromPhysicalMPUAux blockToFree realMPU;
                       vidtAddr := vidtAddr pdentry
                     |})
                  (memory s0) beqAddr
            |}
    /\ lookup blockToFree (memory s4) beqAddr = Some (BE emptyBentry)
    /\ pdentryFirstFreeSlot pd currFirstFreeSlot s4
    /\ bentryBlockIndex blockToFree blockToFreeIdx s1
    /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
    /\ isBE blockToFree s0
    /\ sh1entryPDflag (CPaddr (blockToFree+sh1offset)) false s0
    /\ bentryPFlag blockToFree true s0
    /\ In blockToFree (getMappedBlocks pd s0)
    /\ pdentryMPU pd realMPU s0
    /\ cons1Free s0
    /\ (exists l l0, emptyBentry
          = {|
              read := false;
              write := false;
              exec := false;
              present := false;
              accessible := false;
              blockindex := blockToFreeIdx;
              blockrange := {|
                              startAddr := nullAddr;
                              endAddr := nullAddr;
                              Hsize := l0
                            |};
              Hidx := l
            |})
    /\ P s0).
  exists s0. exists s1. exists s2. exists s3. exists s. exists pdentry. exists realMPU. exists emptyBentry.
  intuition.
}
intro. eapply bindRev.
{ (** MAL.writePDFirstFreeSlotPointer **)
  eapply weaken. apply writePDFirstFreeSlotPointer. intros s Hprops. simpl.
  destruct Hprops as [s0 [s1 [s2 [s3 [s4 [pdentry [realMPU [emptyBentry (Hs & Hs4 & Hs3 & Hs2 & Hs1 & HlookupBlocks4
    & HfirstFrees4 & Hblkidxs1 & HlookupParts0 & HblockIsBEs0 & HPDflags0 & HPflags0 & HblockMappeds0 & HpdMPUs0 &
    Hconsists0 & HnewB & HP)]]]]]]]].
  set(pdentry1 := {|
                    structure := structure pdentry;
                    firstfreeslot := firstfreeslot pdentry;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := removeBlockFromPhysicalMPUAux blockToFree realMPU;
                    vidtAddr := vidtAddr pdentry
                  |}).
  fold pdentry1 in Hs1. exists pdentry1.
  set(pdentry2 := {|
                    structure := structure pdentry1;
                    firstfreeslot := blockToFree;
                    nbfreeslots := nbfreeslots pdentry1;
                    nbprepare := nbprepare pdentry1;
                    parent := parent pdentry1;
                    MPU := MPU pdentry1;
                    vidtAddr := vidtAddr pdentry1
                  |}).
  assert(lookup pd (memory s) beqAddr = Some (PDT pdentry1)).
  {
    assert(Hsh1: wellFormedFstShadowIfBlockEntry s0) by (unfold cons1Free in *; intuition).
    specialize(Hsh1 blockToFree HblockIsBEs0). unfold isSHE in *.
    assert(Hsce: wellFormedShadowCutIfBlockEntry s0) by (unfold cons1Free in *; intuition).
    specialize(Hsce blockToFree HblockIsBEs0). unfold isSCE in *. destruct Hsce as [scentryaddr (Hsce & HsceVal)].
    subst scentryaddr. unfold isBE in *. rewrite Hs. simpl. destruct (beqAddr blockToFree pd) eqn:HbeqBlockPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *. rewrite HlookupParts0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) pd) eqn:HbeqScePart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqScePart. rewrite HbeqScePart in *. rewrite HlookupParts0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) pd) eqn:HbeqSh1Part.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Part. rewrite HbeqSh1Part in *. rewrite HlookupParts0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in HbeqBlockPart. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite IL.beqAddrTrue. trivial.
  }
  split; trivial.
  instantiate(1 := fun _ s => exists s0 s1 s2 s3 s4 s5 pdentry pdentry1 pdentry2 realMPU emptyBentry,
    s = {| currentPartition := currentPartition s5; memory := add pd (PDT pdentry2) (memory s5) beqAddr |}
    /\ s5 = {|
              currentPartition := currentPartition s4;
              memory :=
                add blockToFree
                  (BE
                     (CBlockEntry (read emptyBentry) (write emptyBentry) (exec emptyBentry) 
                        (present emptyBentry) (accessible emptyBentry) (blockindex emptyBentry)
                        (CBlock (startAddr (blockrange emptyBentry)) currFirstFreeSlot)))
                  (memory s4) beqAddr
            |}
    /\ s4 = {|
              currentPartition := currentPartition s3;
              memory :=
                add (CPaddr (blockToFree + scoffset)) (SCE {| origin := nullAddr; next := nullAddr |}) 
                  (memory s3) beqAddr
            |}
    /\ s3 = {|
              currentPartition := currentPartition s2;
              memory :=
                add (CPaddr (blockToFree + sh1offset))
                  (SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |}) 
                  (memory s2) beqAddr
            |}
    /\ s2 = {|
              currentPartition := currentPartition s1;
              memory := add blockToFree (BE emptyBentry) (memory s1) beqAddr
            |}
    /\ s1 = {|
              currentPartition := currentPartition s0;
              memory := add pd (PDT pdentry1) (memory s0) beqAddr
            |}
    /\ lookup pd (memory s5) beqAddr = Some (PDT pdentry1)
    /\ lookup blockToFree (memory s4) beqAddr = Some (BE emptyBentry)
    /\ pdentryFirstFreeSlot pd currFirstFreeSlot s4
    /\ bentryBlockIndex blockToFree blockToFreeIdx s1
    /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
    /\ isBE blockToFree s0
    /\ sh1entryPDflag (CPaddr (blockToFree+sh1offset)) false s0
    /\ bentryPFlag blockToFree true s0
    /\ In blockToFree (getMappedBlocks pd s0)
    /\ pdentryMPU pd realMPU s0
    /\ cons1Free s0
    /\ (exists l l0, emptyBentry
          = {|
              read := false;
              write := false;
              exec := false;
              present := false;
              accessible := false;
              blockindex := blockToFreeIdx;
              blockrange := {|
                              startAddr := nullAddr;
                              endAddr := nullAddr;
                              Hsize := l0
                            |};
              Hidx := l
            |})
    /\ pdentry1 = {|
                    structure := structure pdentry;
                    firstfreeslot := firstfreeslot pdentry;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := removeBlockFromPhysicalMPUAux blockToFree realMPU;
                    vidtAddr := vidtAddr pdentry
                  |}
    /\ pdentry2 = {|
                    structure := structure pdentry1;
                    firstfreeslot := blockToFree;
                    nbfreeslots := nbfreeslots pdentry1;
                    nbprepare := nbprepare pdentry1;
                    parent := parent pdentry1;
                    MPU := MPU pdentry1;
                    vidtAddr := vidtAddr pdentry1
                  |}
    /\ P s0).
  simpl. exists s0. exists s1. exists s2. exists s3. exists s4. exists s. exists pdentry. exists pdentry1.
  exists pdentry2. exists realMPU. exists emptyBentry. intuition.
}
intro. eapply bindRev.
{ (** MAL.readPDNbFreeSlots **)
  eapply weaken. apply readPDNbFreeSlots. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s0 [s1 [s2 [s3 [s4 [s5 [pdentry [pdentry1 [pdentry2 [realMPU [emptyBentry (Hs &
    Hprops)]]]]]]]]]]]. unfold isPDT. rewrite Hs. simpl. rewrite IL.beqAddrTrue. trivial.
}
intro nbfree. eapply bindRev.
{ (** indexSuccM **)
  eapply weaken. apply Index.succ. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as ([s0 [s1 [s2 [s3 [s4 [s5 [pdentry [pdentry1 [pdentry2 [realMPU [emptyBentry (Hs & Hs5 & Hs4 &
    Hs3 & Hs2 & Hs1 & HlookupParts5 & Hprops)]]]]]]]]]]] & HnbFree).
  assert(Hpdentry2: pdentry2 = {|
                                 structure := structure pdentry1;
                                 firstfreeslot := blockToFree;
                                 nbfreeslots := nbfreeslots pdentry1;
                                 nbprepare := nbprepare pdentry1;
                                 parent := parent pdentry1;
                                 MPU := MPU pdentry1;
                                 vidtAddr := vidtAddr pdentry1
                               |}) by intuition.
  assert(Hpdentry1: pdentry1 = {|
                                 structure := structure pdentry;
                                 firstfreeslot := firstfreeslot pdentry;
                                 nbfreeslots := nbfreeslots pdentry;
                                 nbprepare := nbprepare pdentry;
                                 parent := parent pdentry;
                                 MPU := removeBlockFromPhysicalMPUAux blockToFree realMPU;
                                 vidtAddr := vidtAddr pdentry
                               |}) by intuition.
  assert(HnbIsLen: NbFreeSlotsISNbFreeSlotsInList s0) by (unfold cons1Free in *; intuition).
  assert(HlookupParts0: lookup pd (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
  assert(HnbFrees0: pdentryNbFreeSlots pd nbfree s0).
  {
    unfold pdentryNbFreeSlots in *. rewrite Hs in HnbFree. simpl in *. rewrite beqAddrTrue in *.
    rewrite Hpdentry2 in HnbFree. simpl in *. rewrite Hpdentry1 in HnbFree. simpl in *. rewrite HlookupParts0.
    assumption.
  }
  assert(HpartIsPDTs0: isPDT pd s0) by (unfold isPDT; rewrite HlookupParts0; trivial).
  specialize(HnbIsLen pd nbfree HpartIsPDTs0 HnbFrees0).
  destruct HnbIsLen as [optFreeList (Hlist & Hwell & HnbIsLen)]. subst optFreeList.
  assert(Hincl: inclFreeSlotsBlockEntries s0) by (unfold cons1Free in *; intuition).
  specialize(Hincl pd HpartIsPDTs0). apply inclFilterOption in Hincl.
  assert(HnoDup: NoDupInFreeSlotsList s0) by (unfold cons1Free in *; intuition).
  specialize(HnoDup pd pdentry HlookupParts0).
  destruct HnoDup as [optFreeList (Hlist & _ & HnoDup)]. subst optFreeList.
  assert(HblockMapped: In blockToFree (getMappedBlocks pd s0)) by intuition.
  assert(HinclBlock: incl (blockToFree::filterOptionPaddr (getFreeSlotsList pd s0))
    (filterOptionPaddr (getKSEntries pd s0))).
  {
    intros addr HaddrInList. simpl in *.
    destruct HaddrInList as [HaddrIsBlock | HaddrInListRec]; try(apply Hincl; assumption). subst addr.
    unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMapped. assumption.
  }
  assert(HnoDupBlock: NoDup (blockToFree::filterOptionPaddr (getFreeSlotsList pd s0))).
  {
    apply NoDup_cons; trivial. assert(Hfree: freeSlotsListIsFreeSlot s0) by (unfold cons1Free in *; intuition).
    intro Hcontra. specialize(Hfree pd blockToFree (getFreeSlotsList pd s0)
      (filterOptionPaddr (getFreeSlotsList pd s0)) HpartIsPDTs0). apply mappedBlockIsBE in HblockMapped.
    destruct HblockMapped as [bentry (HlookupBlock & Hpres)].
    assert(HblockFree: isFreeSlot blockToFree s0).
    {
      apply Hfree; auto. assert(isPADDR nullAddr s0) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
      intro HbeqBlockNull. subst blockToFree. rewrite HlookupBlock in *. congruence.
    }
    unfold isFreeSlot in *. rewrite HlookupBlock in *.
    destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). destruct HblockFree as (_ & _ & _ & _ & HcontraPres & _). congruence.
  }
  pose proof (NoDup_incl_length HnoDupBlock HinclBlock) as HlebLen. simpl in HlebLen.
  assert(HlenKSEq: length (filterOptionPaddr (getKSEntries pd s0)) =
       length (completeListOfKernels (structure pdentry) s0) * kernelStructureEntriesNb).
  { apply nbKernEq; unfold cons1Free in *; intuition. }
  assert(HlenKern: length (completeListOfKernels (structure pdentry) s0) <= S maxNbPrepare).
  {
    unfold completeListOfKernels.
    destruct (lookup (structure pdentry) (memory s0) beqAddr); try(simpl; lia). destruct v; try(simpl; lia).
    destruct (indexEq (blockindex b) (CIndex 0)); try(simpl; lia). cbn -[maxNbPrepare]. apply le_n_S.
    assert(Hres: forall n kern, length (completeListOfKernelsAux n kern s0) <= n).
    {
      intro n. induction n; simpl; try(lia). intro kern.
      destruct (lookup (CPaddr (kern + nextoffset)) (memory s0) beqAddr); try(simpl; lia).
      destruct v; try(simpl; lia). destruct (beqAddr p nullAddr); simpl; try(lia). apply le_n_S. apply IHn.
    }
    apply Hres.
  }
  pose proof (lenWellFormed (getFreeSlotsList pd s0) Hwell) as HlenFreeEq.
  assert(length (filterOptionPaddr (getKSEntries pd s0)) <= maxIdx).
  {
    pose proof maxNbFreeSlotsLessThanMaxIdx as HkernTotVal. rewrite kernelStructureTotalLengthVal in HkernTotVal.
    rewrite HlenKSEq. cbn in HlenKern. cbn in HkernTotVal. cbn. lia.
  }
  lia.
}
intro nbfreesucc. eapply bindRev.
{ (** MAL.writePDNbFreeSlots **)
  eapply weaken. apply writePDNbFreeSlots. intros s Hprops. simpl.
  destruct Hprops as (([s0 [s1 [s2 [s3 [s4 [s5 [pdentry [pdentry1 [pdentry2 [realMPU [emptyBentry (Hs & Hs5 & Hs4 &
    Hs3 & Hs2 & Hs1 & HlookupParts5 & Hprops)]]]]]]]]]]] & HnbFree) & Hsucc).
  assert(lookup pd (memory s) beqAddr = Some (PDT pdentry2)).
  { rewrite Hs. simpl. rewrite IL.beqAddrTrue. reflexivity. }
  exists pdentry2. split; trivial.
  instantiate(1 := fun _ s => exists s0 s1 s2 s3 s4 s5 s6 pdentry pdentry1 pdentry2 pdentry3 realMPU emptyBentry,
    s = {| currentPartition := currentPartition s6; memory := add pd (PDT pdentry3) (memory s6) beqAddr |}
    /\ s6 = {| currentPartition := currentPartition s5; memory := add pd (PDT pdentry2) (memory s5) beqAddr |}
    /\ s5 = {|
              currentPartition := currentPartition s4;
              memory :=
                add blockToFree
                  (BE
                     (CBlockEntry (read emptyBentry) (write emptyBentry) (exec emptyBentry) 
                        (present emptyBentry) (accessible emptyBentry) (blockindex emptyBentry)
                        (CBlock (startAddr (blockrange emptyBentry)) currFirstFreeSlot)))
                  (memory s4) beqAddr
            |}
    /\ s4 = {|
              currentPartition := currentPartition s3;
              memory :=
                add (CPaddr (blockToFree + scoffset)) (SCE {| origin := nullAddr; next := nullAddr |}) 
                  (memory s3) beqAddr
            |}
    /\ s3 = {|
              currentPartition := currentPartition s2;
              memory :=
                add (CPaddr (blockToFree + sh1offset))
                  (SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |}) 
                  (memory s2) beqAddr
            |}
    /\ s2 = {|
              currentPartition := currentPartition s1;
              memory := add blockToFree (BE emptyBentry) (memory s1) beqAddr
            |}
    /\ s1 = {|
              currentPartition := currentPartition s0;
              memory := add pd (PDT pdentry1) (memory s0) beqAddr
            |}
    /\ pdentryNbFreeSlots pd nbfree s6
    /\ lookup pd (memory s5) beqAddr = Some (PDT pdentry1)
    /\ lookup blockToFree (memory s4) beqAddr = Some (BE emptyBentry)
    /\ pdentryFirstFreeSlot pd currFirstFreeSlot s4
    /\ bentryBlockIndex blockToFree blockToFreeIdx s1
    /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
    /\ isBE blockToFree s0
    /\ sh1entryPDflag (CPaddr (blockToFree+sh1offset)) false s0
    /\ bentryPFlag blockToFree true s0
    /\ In blockToFree (getMappedBlocks pd s0)
    /\ pdentryMPU pd realMPU s0
    /\ cons1Free s0
    /\ (exists l l0, emptyBentry
          = {|
              read := false;
              write := false;
              exec := false;
              present := false;
              accessible := false;
              blockindex := blockToFreeIdx;
              blockrange := {|
                              startAddr := nullAddr;
                              endAddr := nullAddr;
                              Hsize := l0
                            |};
              Hidx := l
            |})
    /\ pdentry1 = {|
                    structure := structure pdentry;
                    firstfreeslot := firstfreeslot pdentry;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := removeBlockFromPhysicalMPUAux blockToFree realMPU;
                    vidtAddr := vidtAddr pdentry
                  |}
    /\ pdentry2 = {|
                    structure := structure pdentry1;
                    firstfreeslot := blockToFree;
                    nbfreeslots := nbfreeslots pdentry1;
                    nbprepare := nbprepare pdentry1;
                    parent := parent pdentry1;
                    MPU := MPU pdentry1;
                    vidtAddr := vidtAddr pdentry1
                  |}
    /\ pdentry3 = {|
                    structure := structure pdentry2;
                    firstfreeslot := firstfreeslot pdentry2;
                    nbfreeslots := nbfreesucc;
                    nbprepare := nbprepare pdentry2;
                    parent := parent pdentry2;
                    MPU := MPU pdentry2;
                    vidtAddr := vidtAddr pdentry2
                  |}
    /\ StateLib.Index.succ nbfree = Some nbfreesucc
    /\ P s0).
  exists s0. exists s1. exists s2. exists s3. exists s4. exists s5. exists s. exists pdentry. exists pdentry1.
  set(pdentry3 := {|
                    structure := structure pdentry2;
                    firstfreeslot := firstfreeslot pdentry2;
                    nbfreeslots := nbfreesucc;
                    nbprepare := nbprepare pdentry2;
                    parent := parent pdentry2;
                    MPU := MPU pdentry2;
                    vidtAddr := vidtAddr pdentry2
                  |}).
  exists pdentry2. exists pdentry3. exists realMPU. exists emptyBentry. intuition.
}
intro. eapply weaken. apply ret. intros s Hprops. simpl.
destruct Hprops as [s0 [s1 [s2 [s3 [s4 [s5 [s6 [pdentry [pdentry1 [pdentry2 [pdentry3 [realMPU [emptyBentry (Hs & Hs6
  & Hs5 & Hs4 & Hs3 & Hs2 & Hs1 & HnbFrees6 & HlookupParts5 & HlookupBlocks4 & HfirstFrees4 & Hblkidxs1 &
  HlookupParts0 & HblockIsBEs0 & HPDflags0 & HPflags0 & HblockToFMappeds0 & HpdMPUs0 & Hconsists0 & HnewB & Hpdentry1
  & Hpdentry2 & Hpdentry3 & Hsucc & HP)]]]]]]]]]]]]].
exists s0. exists s1. exists s2. exists s3. exists s4. exists s5. exists s6. exists pdentry. exists pdentry1.
exists pdentry2. exists pdentry3. exists realMPU. exists emptyBentry.
exists (CBlockEntry (read emptyBentry) (write emptyBentry) (exec emptyBentry) (present emptyBentry)
          (accessible emptyBentry) (blockindex emptyBentry)
          (CBlock (startAddr (blockrange emptyBentry)) currFirstFreeSlot)). exists currFirstFreeSlot.
exists blockToFreeIdx.
assert(HsuccEq: nbfreesucc = CIndex (nbfreeslots pdentry1 + 1) /\ nbfreeslots pdentry1 + 1 <= maxIdx).
{
  unfold pdentryNbFreeSlots in *. rewrite Hs6 in HnbFrees6. simpl in *. rewrite IL.beqAddrTrue in *.
  rewrite Hpdentry2 in HnbFrees6. simpl in *. subst nbfree. unfold StateLib.Index.succ in *. unfold CIndex.
  destruct (lt_dec (nbfreeslots pdentry1) maxIdx); try(exfalso; congruence). injection Hsucc as Hsucc.
  destruct (le_dec (nbfreeslots pdentry1 + 1) maxIdx); try(lia). subst nbfreesucc. split; try(lia). f_equal.
  apply proof_irrelevance.
}
assert(HnewB2: exists l l0, CBlockEntry (read emptyBentry) (write emptyBentry) (exec emptyBentry)
              (present emptyBentry) (accessible emptyBentry) (blockindex emptyBentry)
              (CBlock (startAddr (blockrange emptyBentry)) currFirstFreeSlot)
        = {|
            read := read emptyBentry;
            write := write emptyBentry;
            exec := exec emptyBentry;
            present := present emptyBentry;
            accessible := accessible emptyBentry;
            blockindex := blockindex emptyBentry;
            blockrange := {|
                            startAddr := startAddr (blockrange emptyBentry);
                            endAddr := currFirstFreeSlot;
                            Hsize := l0
                          |};
            Hidx := l
          |}).
{
  unfold CBlockEntry. assert(blockindex emptyBentry < kernelStructureEntriesNb) by (apply Hidx).
  destruct (lt_dec (blockindex emptyBentry) kernelStructureEntriesNb); try(lia).
  exists (ADT.CBlockEntry_obligation_1 (blockindex emptyBentry) l). unfold CBlock.
  assert(currFirstFreeSlot <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
  destruct (le_dec (currFirstFreeSlot - startAddr (blockrange emptyBentry)) maxIdx); try(lia).
  exists (ADT.CBlock_obligation_1 (startAddr (blockrange emptyBentry)) currFirstFreeSlot l0). reflexivity.
}
destruct HsuccEq as (HsuccEq & HlebSuccMax). rewrite HsuccEq in *.
assert(HcopyNewB2: exists l l0, CBlockEntry (read emptyBentry) (write emptyBentry) (exec emptyBentry)
              (present emptyBentry) (accessible emptyBentry) (blockindex emptyBentry)
              (CBlock (startAddr (blockrange emptyBentry)) currFirstFreeSlot)
        = {|
            read := read emptyBentry;
            write := write emptyBentry;
            exec := exec emptyBentry;
            present := present emptyBentry;
            accessible := accessible emptyBentry;
            blockindex := blockindex emptyBentry;
            blockrange := {|
                            startAddr := startAddr (blockrange emptyBentry);
                            endAddr := currFirstFreeSlot;
                            Hsize := l0
                          |};
            Hidx := l
          |}) by assumption.
assert(HcopyNewB: exists l l0, emptyBentry
          = {|
              read := false;
              write := false;
              exec := false;
              present := false;
              accessible := false;
              blockindex := blockToFreeIdx;
              blockrange := {|
                              startAddr := nullAddr;
                              endAddr := nullAddr;
                              Hsize := l0
                            |};
              Hidx := l
            |}) by assumption.

destruct (beqAddr pd nullAddr) eqn:HbeqPartNull.
{
  assert(Hnull: isPADDR nullAddr s0) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
  rewrite <-DTL.beqAddrTrue in HbeqPartNull. subst pd. rewrite HlookupParts0 in *. exfalso; congruence.
}
assert(HbeqNullPart: beqAddr nullAddr pd = false) by (rewrite beqAddrSym; assumption).
destruct (beqAddr blockToFree nullAddr) eqn:HbeqBlockNull.
{
  assert(Hnull: isPADDR nullAddr s0) by (unfold cons1Free in *; intuition). unfold isPADDR in *. unfold isBE in *.
  rewrite <-DTL.beqAddrTrue in HbeqBlockNull. subst blockToFree. exfalso.
  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
assert(HbeqNullBlock: beqAddr nullAddr blockToFree = false) by (rewrite beqAddrSym; assumption).
assert(HblockSh1IsSHEs0: wellFormedFstShadowIfBlockEntry s0) by (unfold cons1Free in *; intuition).
specialize(HblockSh1IsSHEs0 blockToFree HblockIsBEs0). unfold isSHE in *.
assert(HblockSceIsSCEs0: wellFormedShadowCutIfBlockEntry s0) by (unfold cons1Free in *; intuition).
specialize(HblockSceIsSCEs0 blockToFree HblockIsBEs0). unfold isSCE in *. unfold isBE in *.
destruct HblockSceIsSCEs0 as [scentryaddr (HblockSceIsSCEs0 & Hsce)]. subst scentryaddr.
destruct (beqAddr (CPaddr (blockToFree + sh1offset)) nullAddr) eqn:HbeqSh1Null.
{
  assert(Hnull: isPADDR nullAddr s0) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
  rewrite <-DTL.beqAddrTrue in HbeqSh1Null. rewrite HbeqSh1Null in *. exfalso.
  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
assert(HbeqNullSh1: beqAddr nullAddr (CPaddr (blockToFree + sh1offset)) = false) by (rewrite beqAddrSym; assumption).
destruct (beqAddr (CPaddr (blockToFree + scoffset)) nullAddr) eqn:HbeqSceNull.
{
  assert(Hnull: isPADDR nullAddr s0) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
  rewrite <-DTL.beqAddrTrue in HbeqSceNull. rewrite HbeqSceNull in *. exfalso.
  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
assert(HbeqNullSce: beqAddr nullAddr (CPaddr (blockToFree + scoffset)) = false) by (rewrite beqAddrSym; assumption).
destruct (beqAddr pd (CPaddr (blockToFree + sh1offset))) eqn:HbeqPartSh1.
{ rewrite <-DTL.beqAddrTrue in HbeqPartSh1. subst pd. rewrite HlookupParts0 in *. exfalso; congruence. }
destruct (beqAddr blockToFree (CPaddr (blockToFree + sh1offset))) eqn:HbeqBlockSh1.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. exfalso.
  destruct (lookup blockToFree (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (blockToFree + sh1offset))) eqn:HbeqSceSh1.
{
  rewrite <-DTL.beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. exfalso.
  destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
assert(HbeqSh1Sce: beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (blockToFree + scoffset)) = false)
  by (rewrite beqAddrSym; assumption).
destruct (beqAddr pd blockToFree) eqn:HbeqPartBlock.
{ rewrite <-DTL.beqAddrTrue in HbeqPartBlock. subst pd. rewrite HlookupParts0 in *. exfalso; congruence. }
assert(HbeqBlockPart: beqAddr blockToFree pd = false) by (rewrite beqAddrSym; assumption).
destruct (beqAddr pd (CPaddr (blockToFree + scoffset))) eqn:HbeqPartSce.
{ rewrite <-DTL.beqAddrTrue in HbeqPartSce. subst pd. rewrite HlookupParts0 in *. exfalso; congruence. }
destruct (beqAddr blockToFree (CPaddr (blockToFree + scoffset))) eqn:HbeqBlockSce.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *. exfalso.
  destruct (lookup blockToFree (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
assert(HbeqSceBlock: beqAddr (CPaddr (blockToFree + scoffset)) blockToFree = false) by (rewrite beqAddrSym; trivial).
assert(HcurrEq: currentPartition s = currentPartition s0).
{
  rewrite Hs. simpl. rewrite Hs6. simpl. rewrite Hs5. simpl. rewrite Hs4. simpl. rewrite Hs3. simpl. rewrite Hs2.
  simpl. rewrite Hs1. reflexivity.
}
assert(HgetPartsEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
{
  rewrite Hs1. apply getPartitionsEqPDT with pdentry; trivial. rewrite Hpdentry1. reflexivity.
  1, 2: unfold cons1Free in *; intuition.
}
assert(HlookupSh1Eqs1s0: lookup (CPaddr (blockToFree + sh1offset)) (memory s1) beqAddr
  = lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr).
{
  rewrite Hs1. simpl. rewrite HbeqPartSh1. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HPDTIfPDFlags1: PDTIfPDFlag s1).
{
  assert(Hcons0: PDTIfPDFlag s0) by (unfold cons1Free in *; intuition).
  intros idPDchild sh1entryaddr HcheckChild.
  assert(HlookupChildEq: lookup idPDchild (memory s1) beqAddr = lookup idPDchild (memory s0) beqAddr).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). unfold sh1entryAddr in *. rewrite Hs1 in Hsh1. rewrite Hs1.
    simpl in *. destruct (beqAddr pd idPDchild) eqn:HbeqPartBlockBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr.
  unfold entryPDT. rewrite HlookupChildEq in *.
  assert(HcheckChilds0: true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. unfold checkChild.
    destruct (lookup idPDchild (memory s0) beqAddr) eqn:HlookupChilds0; try(congruence). destruct v; try(congruence).
    rewrite Hs1 in HcheckChild. simpl in *.
    destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds0).
  destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
  exists startaddr. split; trivial. unfold entryPDT in *.
  destruct (lookup idPDchild (memory s0) beqAddr) eqn:HlookupChilds0; try(congruence). destruct v; try(congruence).
  rewrite Hs1. simpl. destruct (beqAddr pd (startAddr (blockrange b))) eqn:HbeqPartStart.
  - rewrite <-DTL.beqAddrTrue in HbeqPartStart. subst pd. rewrite HlookupParts0 in *. assumption.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HmultIsPDTs1: isPDT multiplexer s1).
{
  assert(Hcons0: isPDT multiplexer s0) by (unfold cons1Free in *; intuition). unfold isPDT. rewrite Hs1. simpl.
  destruct (beqAddr pd multiplexer) eqn:HbeqPartMult; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HPDflags1: sh1entryPDflag (CPaddr (blockToFree + sh1offset)) false s1).
{
  unfold sh1entryPDflag in *. rewrite Hs1. simpl. rewrite HbeqPartSh1.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HgetPartsEqs2: getPartitions multiplexer s2 = getPartitions multiplexer s0).
{
  rewrite <-HgetPartsEqs1. rewrite Hs2. unfold bentryBlockIndex in *.
  destruct (lookup blockToFree (memory s1) beqAddr) eqn:HlookupBlocks1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  apply getPartitionsEqBEPDflagFalse with b (CPaddr (blockToFree + sh1offset)); trivial.
  apply lookupSh1EntryAddr with b; trivial.
}
assert(HPDflags2: sh1entryPDflag (CPaddr (blockToFree + sh1offset)) false s2).
{
  unfold sh1entryPDflag in *. rewrite Hs2. simpl. rewrite HbeqBlockSh1.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HmultIsPDTs2: isPDT multiplexer s2).
{
  unfold isPDT in *. rewrite Hs2. simpl. destruct (beqAddr blockToFree multiplexer) eqn:HbeqBlockMult.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockMult. subst blockToFree. unfold bentryBlockIndex in *.
    destruct (lookup multiplexer (memory s1) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HPDTIfPDFlags2: PDTIfPDFlag s2).
{
  intros idPDchild sh1entryaddr HcheckChild.
  assert(HlookupChildEq: lookup idPDchild (memory s2) beqAddr = lookup idPDchild (memory s1) beqAddr
    /\ beqAddr blockToFree idPDchild = false).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). unfold checkChild in *. rewrite Hs2 in HcheckChild at 1.
    rewrite Hs2. unfold sh1entryAddr in *. rewrite Hs2 in Hsh1. simpl in *.
    destruct (beqAddr blockToFree idPDchild) eqn:HbeqBlocks.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst idPDchild. exfalso. subst sh1entryaddr.
      rewrite Hs2 in HcheckChild. simpl in *. rewrite HbeqBlockSh1 in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDflag in *.
      destruct (lookup (CPaddr (blockToFree+sh1offset)) (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct HlookupChildEq as (HlookupChildEq & HbeqBlocks). unfold checkChild in *. unfold sh1entryAddr in *.
  unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr. unfold entryPDT. rewrite HlookupChildEq in *.
  assert(HcheckChilds1: true = checkChild idPDchild s1 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s1).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. unfold checkChild.
    destruct (lookup idPDchild (memory s1) beqAddr) eqn:HlookupChilds1; try(congruence). destruct v; try(congruence).
    rewrite Hs2 in HcheckChild. simpl in *.
    destruct (beqAddr blockToFree sh1entryaddr) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(HPDTIfPDFlags1 idPDchild sh1entryaddr HcheckChilds1).
  destruct HPDTIfPDFlags1 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
  exists startaddr. split; trivial. unfold entryPDT in *.
  destruct (lookup idPDchild (memory s1) beqAddr) eqn:HlookupChilds1; try(congruence). destruct v; try(congruence).
  rewrite Hs2. simpl. destruct (beqAddr blockToFree (startAddr (blockrange b))) eqn:HbeqBlockStart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockStart. subst blockToFree. unfold bentryBlockIndex in *.
    destruct (lookup (startAddr (blockrange b)) (memory s1) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HgetPartsEqs3: getPartitions multiplexer s3 = getPartitions multiplexer s0).
{
  rewrite <-HgetPartsEqs2. rewrite Hs3. unfold sh1entryPDflag in *.
  destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s2) beqAddr) eqn:HlookupSh1s2; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  apply getPartitionsEqSHE with s7; trivial.
}
assert(HmultIsPDTs3: isPDT multiplexer s3).
{
  unfold isPDT in *. rewrite Hs3. simpl. rewrite <-HlookupSh1Eqs1s0 in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) multiplexer) eqn:HbeqSh1Mult.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1Mult. rewrite HbeqSh1Mult in *.
    destruct (lookup multiplexer (memory s1) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HlookupSh1Eqs2s0: lookup (CPaddr (blockToFree + sh1offset)) (memory s2) beqAddr
  = lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr).
{
  rewrite <-HlookupSh1Eqs1s0. rewrite Hs2. simpl. rewrite HbeqBlockSh1.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HPDTIfPDFlags3: PDTIfPDFlag s3).
{
  intros idPDchild sh1entryaddr HcheckChild.
  assert(HlookupChildEq: lookup idPDchild (memory s3) beqAddr = lookup idPDchild (memory s2) beqAddr).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). unfold sh1entryAddr in *. rewrite Hs3 in Hsh1. rewrite Hs3.
    simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) idPDchild) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr.
  unfold entryPDT. rewrite HlookupChildEq in *.
  assert(HcheckChilds2: true = checkChild idPDchild s2 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s2).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. unfold checkChild.
    destruct (lookup idPDchild (memory s2) beqAddr) eqn:HlookupChilds2; try(congruence). destruct v; try(congruence).
    rewrite Hs3 in HcheckChild. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree+sh1offset)) sh1entryaddr) eqn:HbeqSh1s;
      try(exfalso; simpl in *; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(HPDTIfPDFlags2 idPDchild sh1entryaddr HcheckChilds2).
  destruct HPDTIfPDFlags2 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
  exists startaddr. split; trivial. unfold entryPDT in *.
  destruct (lookup idPDchild (memory s2) beqAddr) eqn:HlookupChilds2; try(congruence). destruct v; try(congruence).
  rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (startAddr (blockrange b))) eqn:HbeqSh1Start.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *. rewrite <-HlookupSh1Eqs2s0 in *.
    destruct (lookup (startAddr (blockrange b)) (memory s2) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HlookupSceEqs3s0: lookup (CPaddr (blockToFree + scoffset)) (memory s3) beqAddr
  = lookup (CPaddr (blockToFree + scoffset)) (memory s0) beqAddr).
{
  rewrite Hs3. rewrite Hs2. rewrite Hs1. simpl. rewrite HbeqSh1Sce. rewrite HbeqBlockSh1. simpl. rewrite HbeqBlockSce.
  rewrite HbeqPartBlock. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  simpl. rewrite beqAddrFalse in *. rewrite HbeqPartSce. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HgetPartsEqs4: getPartitions multiplexer s4 = getPartitions multiplexer s0).
{
  rewrite <-HgetPartsEqs3. rewrite Hs4. apply getPartitionsEqSCE; trivial. unfold isSCE. rewrite HlookupSceEqs3s0.
  assumption.
}
assert(HmultIsPDTs4: isPDT multiplexer s4).
{
  unfold isPDT in *. rewrite Hs4. simpl. rewrite <-HlookupSceEqs3s0 in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) multiplexer) eqn:HbeqSceMult.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceMult. rewrite HbeqSceMult in *.
    destruct (lookup multiplexer (memory s3) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HPDTIfPDFlags4: PDTIfPDFlag s4).
{
  intros idPDchild sh1entryaddr HcheckChild.
  assert(HlookupChildEq: lookup idPDchild (memory s4) beqAddr = lookup idPDchild (memory s3) beqAddr).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). unfold sh1entryAddr in *. rewrite Hs4 in Hsh1. rewrite Hs4.
    simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) idPDchild) eqn:HbeqSceBlockBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr.
  unfold entryPDT. rewrite HlookupChildEq in *.
  assert(HcheckChilds3: true = checkChild idPDchild s3 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s3).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. unfold checkChild.
    destruct (lookup idPDchild (memory s3) beqAddr) eqn:HlookupChilds3; try(congruence). destruct v; try(congruence).
    rewrite Hs4 in HcheckChild. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree+scoffset)) sh1entryaddr) eqn:HbeqSceSh1Bis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(HPDTIfPDFlags3 idPDchild sh1entryaddr HcheckChilds3).
  destruct HPDTIfPDFlags3 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
  exists startaddr. split; trivial. unfold entryPDT in *.
  destruct (lookup idPDchild (memory s3) beqAddr) eqn:HlookupChilds3; try(congruence). destruct v; try(congruence).
  rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) (startAddr (blockrange b))) eqn:HbeqSceStart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceStart. rewrite HbeqSceStart in *. rewrite <-HlookupSceEqs3s0 in *.
    destruct (lookup (startAddr (blockrange b)) (memory s3) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HlookupSh1Eqs4s3: lookup (CPaddr (blockToFree + sh1offset)) (memory s4) beqAddr
  = lookup (CPaddr (blockToFree + sh1offset)) (memory s3) beqAddr).
{
  rewrite Hs4. simpl. rewrite HbeqSceSh1.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HPDflags3: sh1entryPDflag (CPaddr (blockToFree + sh1offset)) false s3).
{ unfold sh1entryPDflag. rewrite Hs3. simpl. rewrite beqAddrTrue. reflexivity. }
assert(HgetPartsEqs5: getPartitions multiplexer s5 = getPartitions multiplexer s0).
{
  rewrite <-HgetPartsEqs4. rewrite Hs5. destruct HnewB2 as [l [l0 HnewB2]]. rewrite HnewB2.
  apply getPartitionsEqBEPDflagFalse with emptyBentry (CPaddr (blockToFree+sh1offset)); trivial.
  - apply lookupSh1EntryAddr with emptyBentry; trivial.
  - unfold sh1entryPDflag. rewrite HlookupSh1Eqs4s3. assumption.
}
assert(HlookupSh1Eqs5s3: lookup (CPaddr (blockToFree + sh1offset)) (memory s5) beqAddr
  = lookup (CPaddr (blockToFree + sh1offset)) (memory s3) beqAddr).
{
  rewrite <-HlookupSh1Eqs4s3. rewrite Hs5. simpl. rewrite HbeqBlockSh1.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HbeqSh1Block: beqAddr (CPaddr (blockToFree + sh1offset)) blockToFree = false) by (rewrite beqAddrSym; trivial).
assert(HlookupBlockEqs3s2: lookup blockToFree (memory s3) beqAddr = lookup blockToFree (memory s2) beqAddr).
{
  rewrite Hs3. simpl. rewrite HbeqSh1Block.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HlookupBlockEqs4s3: lookup blockToFree (memory s4) beqAddr = lookup blockToFree (memory s2) beqAddr).
{
  rewrite <-HlookupBlockEqs3s2. rewrite Hs4. simpl. rewrite HbeqSceBlock.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HPDTIfPDFlags5: PDTIfPDFlag s5).
{
  intros idPDchild sh1entryaddr HcheckChild.
  assert(HlookupChildEq: lookup idPDchild (memory s5) beqAddr = lookup idPDchild (memory s4) beqAddr
    /\ beqAddr blockToFree idPDchild = false).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). unfold checkChild in *. rewrite Hs5 in HcheckChild at 1.
    rewrite Hs5. unfold sh1entryAddr in *. rewrite Hs5 in Hsh1. simpl in *.
    destruct (beqAddr blockToFree idPDchild) eqn:HbeqBlocks.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst idPDchild. exfalso. subst sh1entryaddr.
      rewrite HlookupSh1Eqs5s3 in *. unfold sh1entryPDflag in *.
      destruct (lookup (CPaddr (blockToFree+sh1offset)) (memory s3) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct HlookupChildEq as (HlookupChildEq & HbeqBlocks). unfold checkChild in *. unfold sh1entryAddr in *.
  unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr. unfold entryPDT. rewrite HlookupChildEq in *.
  assert(HcheckChilds4: true = checkChild idPDchild s4 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s4).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. unfold checkChild.
    destruct (lookup idPDchild (memory s4) beqAddr) eqn:HlookupChilds4; try(congruence). destruct v; try(congruence).
    rewrite Hs5 in HcheckChild. simpl in *.
    destruct (beqAddr blockToFree sh1entryaddr) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(HPDTIfPDFlags4 idPDchild sh1entryaddr HcheckChilds4).
  destruct HPDTIfPDFlags4 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
  exists startaddr. split; trivial. unfold entryPDT in *.
  destruct (lookup idPDchild (memory s4) beqAddr) eqn:HlookupChilds4; try(congruence). destruct v; try(congruence).
  rewrite Hs5. simpl. destruct (beqAddr blockToFree (startAddr (blockrange b))) eqn:HbeqBlockStart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite HbeqBlockStart in *. rewrite HlookupBlocks4 in *.
    congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HlookupBlockEqs1s0: lookup blockToFree (memory s1) beqAddr = lookup blockToFree (memory s0) beqAddr).
{
  rewrite Hs1. simpl. rewrite HbeqPartBlock.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HstructIsKSs5: StructurePointerIsKS s5).
{
  assert(Hcons0: StructurePointerIsKS s0) by (unfold cons1Free in *; intuition).
  intros partition pdentryBis HlookupPart HbeqStructNull.
  assert(HlookupPartBiss0: exists pdentryBiss0, lookup partition (memory s0) beqAddr = Some (PDT pdentryBiss0)
    /\ structure pdentryBiss0 = structure pdentryBis).
  {
    rewrite Hs5 in HlookupPart. simpl in *.
    destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs4 in HlookupPart. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs3 in HlookupPart. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs2 in HlookupPart. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HlookupPart. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. injection HlookupPart as HpdentriesEq. subst pdentryBis.
      exists pdentry. split; trivial. rewrite Hpdentry1. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists pdentryBis.
      split; trivial.
  }
  destruct HlookupPartBiss0 as [pdentryBiss0 (HlookupPartBiss0 & HstructEq)]. rewrite <-HstructEq in *.
  specialize(Hcons0 partition pdentryBiss0 HlookupPartBiss0 HbeqStructNull). unfold isKS in *. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree (structure pdentryBiss0)) eqn:HbeqBlockStruct.
  - destruct HnewB2 as [l [l0 HnewB2]]. rewrite HnewB2. simpl. rewrite <-DTL.beqAddrTrue in HbeqBlockStruct.
    rewrite <-HbeqBlockStruct in *. rewrite <-HlookupBlockEqs1s0 in Hcons0. unfold bentryBlockIndex in *.
    destruct (lookup blockToFree (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    rewrite <-Hblkidxs1 in *. destruct HnewB as [l1 [l2 HnewB]]. rewrite HnewB. simpl. assumption.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) (structure pdentryBiss0)) eqn:HbeqSceStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceStruct. rewrite HbeqSceStruct in *.
      destruct (lookup (structure pdentryBiss0) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (structure pdentryBiss0)) eqn:HbeqSh1Struct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Struct. rewrite HbeqSh1Struct in *.
      destruct (lookup (structure pdentryBiss0) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlockStruct. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr pd (structure pdentryBiss0)) eqn:HbeqPartStruct.
    { rewrite <-DTL.beqAddrTrue in HbeqPartStruct. subst pd. rewrite HlookupParts0 in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HgetPartsEqs6: getPartitions multiplexer s6 = getPartitions multiplexer s0).
{
  rewrite <-HgetPartsEqs5. rewrite Hs6. apply getPartitionsEqPDT with pdentry1; trivial.
  rewrite Hpdentry2. reflexivity.
}
assert(HlookupParts6: lookup pd (memory s6) beqAddr = Some (PDT pdentry2)).
{ rewrite Hs6. simpl. rewrite beqAddrTrue. reflexivity. }
assert(HstructIsKSs6: StructurePointerIsKS s6).
{
  intros partition pdentryBis HlookupPart HbeqStructNull.
  assert(HlookupPartBiss5: exists pdentryBiss5, lookup partition (memory s5) beqAddr = Some (PDT pdentryBiss5)
    /\ structure pdentryBiss5 = structure pdentryBis).
  {
    rewrite Hs6 in HlookupPart. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. injection HlookupPart as HpdentriesEq. subst pdentryBis.
      exists pdentry1. split; trivial. rewrite Hpdentry2. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists pdentryBis.
      split; trivial.
  }
  destruct HlookupPartBiss5 as [pdentryBiss5 (HlookupPartBiss5 & HstructEq)]. rewrite <-HstructEq in *.
  specialize(HstructIsKSs5 partition pdentryBiss5 HlookupPartBiss5 HbeqStructNull). unfold isKS in *. rewrite Hs6.
  simpl. destruct (beqAddr pd (structure pdentryBiss5)) eqn:HbeqPartStruct.
  { rewrite <-DTL.beqAddrTrue in HbeqPartStruct. subst pd. rewrite HlookupParts5 in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HPDTIfPDFlag: PDTIfPDFlag s6).
{
  intros idPDchild sh1entryaddr HcheckChild.
  assert(HlookupChildEq: lookup idPDchild (memory s6) beqAddr = lookup idPDchild (memory s5) beqAddr).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). rewrite Hs6. unfold sh1entryAddr in *. rewrite Hs6 in Hsh1.
    simpl in *. destruct (beqAddr pd idPDchild) eqn:HbeqPartBlockBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr.
  unfold entryPDT. rewrite HlookupChildEq in *.
  assert(HcheckChilds5: true = checkChild idPDchild s5 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s5).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. unfold checkChild.
    destruct (lookup idPDchild (memory s5) beqAddr) eqn:HlookupChilds4; try(congruence). destruct v; try(congruence).
    rewrite Hs6 in HcheckChild. simpl in *.
    destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(HPDTIfPDFlags5 idPDchild sh1entryaddr HcheckChilds5).
  destruct HPDTIfPDFlags5 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
  exists startaddr. split; trivial. unfold entryPDT in *.
  destruct (lookup idPDchild (memory s5) beqAddr) eqn:HlookupChilds5; try(congruence). destruct v; try(congruence).
  rewrite Hs6. simpl. destruct (beqAddr pd (startAddr (blockrange b))) eqn:HbeqPartStart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPartStart. rewrite HbeqPartStart in *. rewrite HlookupParts5 in *.
    congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HgetPartsEqs: getPartitions multiplexer s = getPartitions multiplexer s0).
{
  rewrite <-HgetPartsEqs6. rewrite Hs. apply getPartitionsEqPDT with pdentry2; trivial.
  rewrite Hpdentry3. reflexivity.
}
destruct HnewB as [l [l1 HnewB]]. destruct HnewB2 as [l2 [l3 HnewB2]].
assert(HblockIsNotFree: ~isFreeSlot blockToFree s0).
{
  unfold bentryPFlag in *. unfold isFreeSlot. destruct (lookup blockToFree (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence).
  destruct (lookup (CPaddr (blockToFree+sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence).
  destruct (lookup (CPaddr (blockToFree+scoffset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). intro Hcontra. destruct Hcontra as (_ & _ & _ & _ & Hcontra & _). congruence.
}
assert(HgetFreeEqs5s0: forall partition, isPDT partition s0
  -> getFreeSlotsList partition s5 = getFreeSlotsList partition s0).
{
  intros partition HpartIsPDT. unfold getFreeSlotsList. unfold isPDT in *.
  destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPartBiss0; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  assert(HLookupPartEq: exists ps5, lookup partition (memory s5) beqAddr = Some(PDT ps5)
    /\ firstfreeslot ps5 = firstfreeslot p /\ nbfreeslots ps5 = nbfreeslots p).
  {
    rewrite Hs5. simpl. destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockPartBis. subst partition. rewrite HlookupPartBiss0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqScePartBis. subst partition. rewrite HlookupPartBiss0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1PartBis. subst partition. rewrite HlookupPartBiss0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. rewrite HlookupParts0 in HlookupPartBiss0. exists pdentry1.
      injection HlookupPartBiss0 as HpdentriesEq. subst p. rewrite Hpdentry1. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. exists p. auto.
  }
  destruct HLookupPartEq as [ps5 (HlookupPartBiss5 & HfirstFreeEq & HnbFreeEq)]. rewrite HlookupPartBiss5.
  rewrite HfirstFreeEq. rewrite HnbFreeEq.
  destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; trivial.
  assert(HfirstIsFree: isFreeSlot (firstfreeslot p) s0).
  {
    assert(Hres: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold cons1Free in *; intuition).
    rewrite <-beqAddrFalse in *. specialize(Hres partition p HlookupPartBiss0 HbeqFirstFreeNull). destruct Hres.
    assumption.
  }
  assert(HbeqFirstFreeBlock: firstfreeslot p <> blockToFree).
  { intro Hcontra. rewrite Hcontra in *. congruence. }
  assert(Heqs1: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s1 (nbfreeslots p)
    = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
  {
    rewrite Hs1. apply getFreeSlotsListRecEqPDT; trivial.
    2,3: unfold isBE; unfold isPADDR; rewrite HlookupParts0; intro; congruence.
    intro Hcontra. rewrite Hcontra in *. unfold isFreeSlot in *. rewrite HlookupParts0 in *. congruence.
  }
  assert(HpropsFree: NoDupInFreeSlotsList s0) by (unfold cons1Free in *; intuition).
  specialize(HpropsFree partition p HlookupPartBiss0).
  destruct HpropsFree as [optFreeList (Hlist & HwellFormedList & HnoDupList)]. unfold getFreeSlotsList in *.
  rewrite HlookupPartBiss0 in *. rewrite HbeqFirstFreeNull in *. subst optFreeList.
  assert(HblockNotInFreeList: ~In blockToFree
      (filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)))).
  {
    assert(HfreeSlots: freeSlotsListIsFreeSlot s0) by (unfold cons1Free in *; intuition).
    contradict HblockIsNotFree.
    assert(HeqFree: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)
        = getFreeSlotsList partition s0
      /\ wellFormedFreeSlotsList (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)) <> False).
    {
      split; trivial. unfold getFreeSlotsList. rewrite HlookupPartBiss0. rewrite HbeqFirstFreeNull. reflexivity.
    }
    specialize(HfreeSlots partition blockToFree
      (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
      (filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)))).
    rewrite <-beqAddrFalse in *. apply HfreeSlots; auto. unfold isPDT. rewrite HlookupPartBiss0. trivial.
  }
  rewrite <-Heqs1 in *.
  assert(Heqs2: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s2 (nbfreeslots p)
    = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s1 (nbfreeslots p)).
  {
    rewrite Hs2. apply getFreeSlotsListRecEqBE; trivial. unfold isBE. unfold bentryBlockIndex in *.
    destruct (lookup blockToFree (memory s1) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-Heqs2 in *.
  assert(Heqs3: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s3 (nbfreeslots p)
    = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s2 (nbfreeslots p)).
  {
    rewrite Hs3. apply getFreeSlotsListRecEqSHE.
    2,3: unfold isBE; unfold isPADDR; rewrite HlookupSh1Eqs2s0;
      destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence); destruct v;
      congruence.
    intro Hcontra. rewrite Hcontra in *. unfold isFreeSlot in *.
    destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-Heqs3 in *.
  assert(Heqs4: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s4 (nbfreeslots p)
    = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s3 (nbfreeslots p)).
  {
    rewrite Hs4. apply getFreeSlotsListRecEqSCE.
    2,3: unfold isBE; unfold isPADDR; rewrite HlookupSceEqs3s0;
      destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s0) beqAddr); try(congruence); destruct v;
      congruence.
    intro Hcontra. rewrite Hcontra in *. unfold isFreeSlot in *.
    destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-Heqs4 in *. rewrite Hs5. apply getFreeSlotsListRecEqBE; trivial. unfold isBE. rewrite HlookupBlocks4.
  trivial.
}
assert(HgetFreeEqss0NotPd: forall partition, isPDT partition s0
  -> beqAddr pd partition = false
  -> getFreeSlotsList partition s = getFreeSlotsList partition s0).
{
  intros partition HpartIsPDTs0 HbeqParts. rewrite <-HgetFreeEqs5s0; trivial. unfold getFreeSlotsList.
  rewrite Hs at 1. rewrite Hs6. simpl. rewrite HbeqParts. rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup partition (memory s5) beqAddr) eqn:HlookupPartBiss5; trivial. destruct v; trivial.
  destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; trivial.
  assert(HlookupPartBiss0: lookup partition (memory s0) beqAddr = Some (PDT p)).
  {
    rewrite Hs5 in HlookupPartBiss5. simpl in *.
    destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs4 in HlookupPartBiss5. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs3 in HlookupPartBiss5. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs2 in HlookupPartBiss5. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HlookupPartBiss5. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(firstfreeslot p <> pd).
  {
    assert(HfirstFreeIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold cons1Free in *; intuition).
    rewrite <-beqAddrFalse in *. specialize(HfirstFreeIsFree partition p HlookupPartBiss0 HbeqFirstFreeNull).
    destruct HfirstFreeIsFree as (HfirstIsBE & _). unfold isBE in *. intro Hcontra. rewrite Hcontra in *.
    rewrite HlookupParts0 in *. congruence.
  }
  assert(Heqs6: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s6 (nbfreeslots p)
    = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s5 (nbfreeslots p)).
  {
    rewrite Hs6.
    apply getFreeSlotsListRecEqPDT; trivial; unfold isBE; unfold isPADDR; rewrite HlookupParts5; congruence.
  }
  rewrite <-Heqs6. rewrite Hs. apply getFreeSlotsListRecEqPDT; trivial;
    unfold isBE; unfold isPADDR; rewrite HlookupParts6; congruence.
}
assert(HlookupBlockEqss5: lookup blockToFree (memory s) beqAddr = lookup blockToFree (memory s5) beqAddr).
{
  rewrite Hs. rewrite Hs6. simpl. rewrite HbeqPartBlock. rewrite beqAddrTrue.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
}
assert(HlookupPartEqs5s4: lookup pd (memory s5) beqAddr = lookup pd (memory s4) beqAddr).
{
  rewrite Hs5. simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HnullIsPADDRs5: isPADDR nullAddr s5).
{
  assert(Hcons0: nullAddrExists s0) by (unfold cons1Free in *; intuition). unfold nullAddrExists in *.
  unfold isPADDR. rewrite Hs5. simpl.
  rewrite HbeqBlockNull. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite Hs4. simpl. rewrite beqAddrFalse in *. rewrite HbeqSceNull. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqSh1Null. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite Hs2. simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockNull. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartNull. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HgetFreeEqPdss0: getFreeSlotsList pd s = (SomePaddr blockToFree)::getFreeSlotsList pd s0).
{
  rewrite <-HgetFreeEqs5s0; try(unfold isPDT; rewrite HlookupParts0; trivial). unfold getFreeSlotsList.
  rewrite HlookupParts5. rewrite Hs at 1. rewrite Hs6. simpl. rewrite beqAddrTrue. rewrite Hpdentry3. simpl.
  rewrite Hpdentry2. simpl. rewrite HbeqBlockNull.
  assert(HancFreeEq: getFreeSlotsListRec maxIdx (firstfreeslot pdentry1) s5 (nbfreeslots pdentry1)
    = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry1) s5 (nbfreeslots pdentry1)).
  { apply getFreeSlotsListRecNBound; lia. }
  rewrite <-HancFreeEq. rewrite MaxIdxNextEq. simpl. rewrite HlookupBlockEqss5. rewrite Hs5 at 1. simpl.
  rewrite beqAddrTrue. unfold CIndex. destruct (le_dec (nbfreeslots pdentry1 + 1) maxIdx); try(lia). rewrite HnewB2.
  simpl. unfold StateLib.Index.pred. simpl. destruct (gt_dec (nbfreeslots pdentry1 + 1) 0); try(lia). f_equal.
  assert(HidxEq: {|
                   i := nbfreeslots pdentry1 + 1 - 1;
                   Hi :=
                     StateLib.Index.pred_obligation_1
                       {|
                         i := nbfreeslots pdentry1 + 1; Hi := ADT.CIndex_obligation_1 (nbfreeslots pdentry1 + 1) l0
                       |} g
                 |} = nbfreeslots pdentry1).
  { apply index_eq_i. simpl. lia. }
  rewrite HidxEq. unfold pdentryFirstFreeSlot in *. rewrite <-HlookupPartEqs5s4 in *. rewrite HlookupParts5 in *.
  subst currFirstFreeSlot. assert(HbeqFirst1Part: firstfreeslot pdentry1 <> pd).
  {
    assert(HfirstFreeIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold cons1Free in *; intuition).
    rewrite <-beqAddrFalse in *. specialize(HfirstFreeIsFree pd pdentry HlookupParts0). intro Hcontra. subst pd.
    assert(Hnull: isPADDR nullAddr s0) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
    destruct (beqAddr (firstfreeslot pdentry) nullAddr) eqn:HbeqFirstNull.
    - rewrite <-DTL.beqAddrTrue in HbeqFirstNull. rewrite HbeqFirstNull in *. rewrite Hpdentry1 in HlookupParts0.
      simpl in *. rewrite HlookupParts0 in *. congruence.
    - rewrite <-beqAddrFalse in *. specialize(HfirstFreeIsFree HbeqFirstNull).
      destruct HfirstFreeIsFree as (HfirstIsBE & _). unfold isBE in *. rewrite Hpdentry1 in HlookupParts0.
      simpl in *. rewrite HlookupParts0 in *. congruence.
  }
  assert(Heqs: getFreeSlotsListRec maxIdx (firstfreeslot pdentry1) s (nbfreeslots pdentry1)
    = getFreeSlotsListRec maxIdx (firstfreeslot pdentry1) s6 (nbfreeslots pdentry1)).
  {
    rewrite Hs. apply getFreeSlotsListRecEqPDT; trivial; unfold isBE; unfold isPADDR; rewrite HlookupParts6;
      congruence.
  }
  assert(Heqs6: getFreeSlotsListRec maxIdx (firstfreeslot pdentry1) s6 (nbfreeslots pdentry1)
    = getFreeSlotsListRec maxIdx (firstfreeslot pdentry1) s5 (nbfreeslots pdentry1)).
  {
    rewrite Hs6. apply getFreeSlotsListRecEqPDT; trivial; unfold isBE; unfold isPADDR; rewrite HlookupParts5;
      congruence.
  }
  rewrite Heqs. rewrite Heqs6. destruct (beqAddr (firstfreeslot pdentry1) nullAddr) eqn:HbeqFirstNull; trivial.
  rewrite <-DTL.beqAddrTrue in HbeqFirstNull. rewrite HbeqFirstNull in *. pose proof maxIdxNotZero.
  replace maxIdx with (S (maxIdx-1)); try(lia). simpl. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s5) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  reflexivity.
}
assert(HlookupSh1Eqss3: lookup (CPaddr (blockToFree + sh1offset)) (memory s) beqAddr
        = lookup (CPaddr (blockToFree + sh1offset)) (memory s3) beqAddr).
{
  rewrite <-HlookupSh1Eqs5s3. rewrite Hs. rewrite Hs6. simpl. rewrite beqAddrTrue. rewrite HbeqPartSh1.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HlookupSceEqss4: lookup (CPaddr (blockToFree + scoffset)) (memory s) beqAddr
        = lookup (CPaddr (blockToFree + scoffset)) (memory s4) beqAddr).
{
  rewrite Hs. rewrite Hs6. simpl. rewrite beqAddrTrue. rewrite HbeqPartSce.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqBlockSce. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HblockIsFrees: isFreeSlot blockToFree s).
{
  unfold isFreeSlot. rewrite HlookupBlockEqss5. rewrite Hs5. simpl. rewrite beqAddrTrue. rewrite HnewB2. simpl.
  rewrite HlookupSh1Eqss3. rewrite Hs3. simpl. rewrite beqAddrTrue. rewrite HlookupSceEqss4. rewrite Hs4. simpl.
  rewrite beqAddrTrue. simpl. rewrite HnewB. simpl. intuition.
}
assert(HbeqScePart: beqAddr (CPaddr (blockToFree + scoffset)) pd = false) by (rewrite beqAddrSym; assumption).
assert(HgetKSEntriesEqs1s0: forall partition, getKSEntries partition s1 = getKSEntries partition s0).
{
  intros partition. rewrite Hs1. apply getKSEntriesEqPDT with pdentry; trivial.
  - unfold cons1Free in *; intuition.
  - rewrite Hpdentry1. reflexivity.
}
assert(HgetKSEntriesEqss0: forall partition, isPDT partition s2
  -> getKSEntries partition s = getKSEntries partition s0).
{
  intros partition HpartIsPDT. assert(Heqs2: getKSEntries partition s2 = getKSEntries partition s0).
  {
    rewrite <-HgetKSEntriesEqs1s0. rewrite Hs2. apply getKSEntriesEqBE; trivial. unfold isBE.
    rewrite HlookupBlockEqs1s0. trivial.
  }
  unfold isPDT in *. destruct (lookup partition (memory s2) beqAddr) eqn:HlookupParts2; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  assert(Heqs3: getKSEntries partition s3 = getKSEntries partition s0).
  {
    rewrite <-Heqs2. rewrite Hs3. apply getKSEntriesEqSHE with p; trivial. unfold isSHE. rewrite HlookupSh1Eqs2s0.
    assumption.
  }
  assert(Heqs4: getKSEntries partition s4 = getKSEntries partition s0).
  {
    rewrite <-Heqs3. rewrite Hs4. apply getKSEntriesEqSCE with p.
    - rewrite Hs3. simpl. destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1PartBis. rewrite HbeqSh1PartBis in *. rewrite HlookupSh1Eqs2s0 in *.
        rewrite HlookupParts2 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - unfold isSCE. rewrite HlookupSceEqs3s0. assumption.
  }
  assert(Heqs5: getKSEntries partition s5 = getKSEntries partition s0).
  {
    rewrite <-Heqs4. rewrite Hs5. apply getKSEntriesEqBE; trivial. unfold isBE. rewrite HlookupBlockEqs4s3.
    rewrite Hs2. simpl. rewrite beqAddrTrue. trivial.
  }
  assert(Heqs6: getKSEntries partition s6 = getKSEntries partition s0).
  {
    rewrite <-Heqs5. rewrite Hs6. apply getKSEntriesEqPDT with pdentry1; trivial. rewrite Hpdentry2. reflexivity.
  }
  rewrite <-Heqs6. rewrite Hs. apply getKSEntriesEqPDT with pdentry2; trivial. rewrite Hpdentry3. reflexivity.
}
assert(HlookupBlockToF: exists bentryToF, lookup blockToFree (memory s0) beqAddr = Some(BE bentryToF)).
{
  destruct (lookup blockToFree (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  exists b. reflexivity.
}
destruct HlookupBlockToF as [bentryToF HlookupBlockToF].
assert(HpdIsPDTs0: isPDT pd s0) by (unfold isPDT; rewrite HlookupParts0; trivial).
assert(HgetMappedBEqs1s0: forall part, getMappedBlocks part s1 = getMappedBlocks part s0).
{
  intro part. rewrite Hs1. apply getMappedBlocksEqPDT with pdentry; trivial.
  - unfold cons1Free in *; intuition.
  - rewrite Hpdentry1. reflexivity.
}
assert(HgetMappedBEqs3s2: forall part, isPDT part s2 -> getMappedBlocks part s3 = getMappedBlocks part s2).
{
  intros part HpartIsPDTs2. rewrite Hs3. apply getMappedBlocksEqSHE; trivial. unfold isSHE. rewrite HlookupSh1Eqs2s0.
  assumption.
}
assert(HgetMappedBEqs4s2: forall part, isPDT part s2 -> getMappedBlocks part s4 = getMappedBlocks part s2).
{
  intros part HpartIsPDTs2. rewrite <-HgetMappedBEqs3s2; trivial. rewrite Hs4. apply getMappedBlocksEqSCE; trivial.
  - unfold isPDT in *. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree+sh1offset)) part) eqn:HbeqSh1PartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1PartBis. subst part. rewrite HlookupSh1Eqs2s0 in *.
      destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - unfold isSCE. rewrite HlookupSceEqs3s0. assumption.
}
assert(HgetMappedBEqs5s2: forall part, isPDT part s2 -> getMappedBlocks part s5 = getMappedBlocks part s2).
{
  intros part HpartIsPDTs2. rewrite <-HgetMappedBEqs4s2; trivial. rewrite Hs5.
  apply getMappedBlocksEqBENoChange with emptyBentry; trivial. rewrite HnewB2. reflexivity.
}
assert(HgetMappedBEqs6s2: forall part, isPDT part s2 -> getMappedBlocks part s6 = getMappedBlocks part s2).
{
  intros part HpartIsPDTs2. rewrite <-HgetMappedBEqs5s2; trivial. rewrite Hs6.
  apply getMappedBlocksEqPDT with pdentry1; trivial. rewrite Hpdentry2. reflexivity.
}
assert(HgetMappedBEqss2: forall part, isPDT part s2 -> getMappedBlocks part s = getMappedBlocks part s2).
{
  intros part HpartIsPDTs2. rewrite <-HgetMappedBEqs6s2; trivial. rewrite Hs.
  apply getMappedBlocksEqPDT with pdentry2; trivial. rewrite Hpdentry3. reflexivity.
}
assert(HgetMappedBEqss0: forall part, isPDT part s2
      -> pd <> part
      -> getMappedBlocks part s = getMappedBlocks part s0).
{
  intros part HpartIsPDTs2 HbeqPdPart. assert(HpartIsPDTs0: isPDT part s0).
  {
    unfold isPDT in *. rewrite Hs2 in HpartIsPDTs2. rewrite Hs1 in HpartIsPDTs2. simpl in *.
    rewrite beqAddrFalse in *. destruct (beqAddr blockToFree part) eqn:HbeqBlockPartBis; try(exfalso; congruence).
    rewrite HbeqPartBlock in *. simpl in *. rewrite HbeqPdPart in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(Heqs2: getMappedBlocks part s2 = getMappedBlocks part s0).
  {
    rewrite <-HgetMappedBEqs1s0. rewrite Hs2. apply getMappedBlocksEqBENotInPart.
    - unfold isBE. rewrite HlookupBlockEqs1s0. rewrite HlookupBlockToF. trivial.
    - assert(Hdisjoint: DisjointKSEntries s0) by (unfold cons1Free in *; intuition).
      specialize(Hdisjoint pd part HpdIsPDTs0 HpartIsPDTs0 HbeqPdPart).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      rewrite HgetKSEntriesEqs1s0. apply Hdisjoint. unfold getMappedBlocks in *.
      apply InFilterPresentInList in HblockToFMappeds0. assumption.
  }
  rewrite HgetMappedBEqss2; trivial.
}
assert(HpdIsPDTs1: isPDT pd s1).
{ unfold isPDT. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial. }
assert(HpdIsPDTs2: isPDT pd s2).
{
  unfold isPDT. rewrite Hs2. simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HnoDupKSs1: noDupKSEntriesList s1).
{
  assert(Hcons0: noDupKSEntriesList s0) by (unfold cons1Free in *; intuition).
  intros part HpartIsPDT. assert(HpartIsPDTs0: isPDT part s0).
  {
    unfold isPDT in *. rewrite Hs1 in HpartIsPDT. simpl in *. destruct (beqAddr pd part) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 part HpartIsPDTs0). rewrite HgetKSEntriesEqs1s0. assumption.
}
assert(HgetMappedBPdss0: forall block,
  (In block (getMappedBlocks pd s0) -> blockToFree = block \/ In block (getMappedBlocks pd s))
  /\ (In block (getMappedBlocks pd s) -> In block (getMappedBlocks pd s0))
  /\ (NoDup (getMappedBlocks pd s0) -> NoDup (getMappedBlocks pd s))).
{
  rewrite <-HgetMappedBEqs1s0. rewrite HgetMappedBEqss2; trivial. intro block. rewrite Hs2.
  apply getMappedBlocksEqBEPresentChangeFalse with bentryToF; trivial.
  - rewrite HlookupBlockEqs1s0. assumption.
  - rewrite HnewB. apply mappedBlockIsBE in HblockToFMappeds0.
    destruct HblockToFMappeds0 as [bentryToFBis (HlookupBlockToFBis & Hpres)].
    rewrite HlookupBlockToF in HlookupBlockToFBis. injection HlookupBlockToFBis as HbentriesEq. subst bentryToFBis.
    rewrite Hpres. simpl. intro Hcontra. congruence.
  - rewrite HnewB. reflexivity.
  - rewrite HgetMappedBEqs1s0. assumption.
}
assert(HPDflags4: sh1entryPDflag (CPaddr (blockToFree + sh1offset)) false s4).
{ unfold sh1entryPDflag. rewrite HlookupSh1Eqs4s3. assumption. }
assert(HgetChildrenEq: forall part, isPDT part s1
        -> getChildren part s = getChildren part s0).
{
  intros part HpartIsPDTs1. assert(Heqs1: getChildren part s1 = getChildren part s0).
  {
    rewrite Hs1. apply getChildrenEqPDT with pdentry; trivial.
    - rewrite Hpdentry1. reflexivity.
    - unfold cons1Free in *; intuition.
  }
  assert(Heqs2: getChildren part s2 = getChildren part s0).
  {
    rewrite <-Heqs1. rewrite Hs2.
    apply getChildrenEqBEPDflagFalse with bentryToF (CPaddr (blockToFree+sh1offset)); trivial.
    - rewrite HlookupBlockEqs1s0. assumption.
    - apply lookupSh1EntryAddr with bentryToF. rewrite HlookupBlockEqs1s0. assumption.
  }
  assert(HpartIsPDTs2: isPDT part s2).
  {
    unfold isPDT in *. rewrite Hs2. simpl. destruct (beqAddr blockToFree part) eqn:HbeqBlockPartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockPartBis. subst part. rewrite HlookupBlockEqs1s0 in *.
      rewrite HlookupBlockToF in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(Heqs3: getChildren part s3 = getChildren part s0).
  {
    rewrite <-Heqs2. rewrite Hs3. unfold sh1entryPDflag in *.
    destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply getChildrenEqSHE with s7; trivial.
  }
  assert(HpartIsPDTs3: isPDT part s3).
  {
    unfold isPDT in *. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) part) eqn:HbeqSh1PartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1PartBis. subst part. rewrite HlookupSh1Eqs1s0 in *.
      destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(Heqs4: getChildren part s4 = getChildren part s0).
  {
    rewrite <-Heqs3. rewrite Hs4. apply getChildrenEqSCE; trivial. unfold isSCE. rewrite HlookupSceEqs3s0. assumption.
  }
  assert(HpartIsPDTs4: isPDT part s4).
  {
    unfold isPDT in *. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) part) eqn:HbeqScePartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqScePartBis. subst part. rewrite HlookupSceEqs3s0 in *.
      destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(Heqs5: getChildren part s5 = getChildren part s0).
  {
    rewrite <-Heqs4. rewrite Hs5.
    apply getChildrenEqBEPDflagFalse with emptyBentry (CPaddr (blockToFree+sh1offset)); trivial.
    apply lookupSh1EntryAddr with emptyBentry; trivial.
  }
  assert(Heqs6: getChildren part s6 = getChildren part s0).
  {
    rewrite <-Heqs5. rewrite Hs6. apply getChildrenEqPDT with pdentry1; trivial. rewrite Hpdentry2. reflexivity.
  }
  rewrite <-Heqs6. rewrite Hs. apply getChildrenEqPDT with pdentry2; trivial. rewrite Hpdentry3. reflexivity.
}
assert(HnbFrees0: pdentryNbFreeSlots pd (nbfreeslots pdentry) s0).
{ apply lookupPDEntryNbFreeSlots. assumption. }
assert(HkernListEqss0: forall partition kernList,
  isListOfKernels kernList partition s -> isListOfKernels kernList partition s0).
{
  intros partition kernList HkernList. assert(HkernLists6: isListOfKernels kernList partition s6).
  {
    revert HkernList. rewrite Hs. apply isListOfKernelsEqPDT with pdentry2; trivial. rewrite Hpdentry3. reflexivity.
  }
  assert(HkernLists5: isListOfKernels kernList partition s5).
  {
    revert HkernLists6. rewrite Hs6. apply isListOfKernelsEqPDT with pdentry1; trivial. rewrite Hpdentry2.
    reflexivity.
  }
  assert(HkernLists4: isListOfKernels kernList partition s4).
  { revert HkernLists5. rewrite Hs5. apply isListOfKernelsEqBE. }
  assert(HkernLists3: isListOfKernels kernList partition s3).
  { revert HkernLists4. rewrite Hs4. apply isListOfKernelsEqSCE. }
  assert(HkernLists2: isListOfKernels kernList partition s2).
  { revert HkernLists3. rewrite Hs3. apply isListOfKernelsEqSHE. }
  assert(HkernLists1: isListOfKernels kernList partition s1).
  { revert HkernLists2. rewrite Hs2. apply isListOfKernelsEqBE. }
  revert HkernLists1. rewrite Hs1. apply isListOfKernelsEqPDT with pdentry; trivial. rewrite Hpdentry1. reflexivity.
}
assert(HparentOfParts1: parentOfPartitionIsPartition s1).
{
  assert(Hcons0: parentOfPartitionIsPartition s0) by (unfold cons1Free in *; intuition).
  intros partition pdentryPart HlookupPart.
  assert(HlookupPartBiss0: exists pdentryParts0,
    lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
    /\ parent pdentryParts0 = parent pdentryPart).
  {
    rewrite Hs1 in HlookupPart. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
      subst pdentryPart. exists pdentry. rewrite Hpdentry1. simpl. auto.
    - exists pdentryPart. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct HlookupPartBiss0 as [pdentryParts0 (HlookupPartBiss0 & HparentsEq)]. rewrite <-HparentsEq in *.
  specialize(Hcons0 partition pdentryParts0 HlookupPartBiss0). destruct Hcons0 as (HparentIsPart & Hother).
  split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
  destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEqs1.
  split; trivial. rewrite Hs1. simpl. destruct (beqAddr pd (parent pdentryParts0)) eqn:HbeqPdParent.
  - exists pdentry1. reflexivity.
  - exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HparentOfParts2: parentOfPartitionIsPartition s2).
{
  intros partition pdentryPart HlookupPart. rewrite Hs2 in HlookupPart. simpl in *.
    destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(HparentOfParts1 partition pdentryPart HlookupPart). destruct HparentOfParts1 as (HparentIsPart & Hother).
  split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
  destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEqs2.
  rewrite <-HgetPartsEqs1. split; trivial. rewrite Hs2. simpl.
  destruct (beqAddr blockToFree (parent pdentryPart)) eqn:HbeqBlockParent.
  { rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockToFree. exfalso; congruence. }
  exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HparentOfParts3: parentOfPartitionIsPartition s3).
{
  intros partition pdentryPart HlookupPart. rewrite Hs3 in HlookupPart. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(HparentOfParts2 partition pdentryPart HlookupPart). destruct HparentOfParts2 as (HparentIsPart & Hother).
  split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
  destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEqs3.
  rewrite <-HgetPartsEqs2. split; trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (parent pdentryPart)) eqn:HbeqSh1Parent.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1Parent. rewrite HbeqSh1Parent in *. rewrite HlookupSh1Eqs2s0 in *.
    rewrite HlookupParent in *. exfalso; congruence.
  }
  exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HparentOfParts4: parentOfPartitionIsPartition s4).
{
  intros partition pdentryPart HlookupPart. rewrite Hs4 in HlookupPart. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(HparentOfParts3 partition pdentryPart HlookupPart). destruct HparentOfParts3 as (HparentIsPart & Hother).
  split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
  destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEqs4.
  rewrite <-HgetPartsEqs3. split; trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) (parent pdentryPart)) eqn:HbeqSceParent.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceParent. rewrite HbeqSceParent in *. rewrite HlookupSceEqs3s0 in *.
    rewrite HlookupParent in *. exfalso; congruence.
  }
  exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HparentOfParts5: parentOfPartitionIsPartition s5).
{
  intros partition pdentryPart HlookupPart. rewrite Hs5 in HlookupPart. simpl in *.
  destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(HparentOfParts4 partition pdentryPart HlookupPart). destruct HparentOfParts4 as (HparentIsPart & Hother).
  split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
  destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEqs5.
  rewrite <-HgetPartsEqs4. split; trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree (parent pdentryPart)) eqn:HbeqBlockParent.
  { rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockToFree. exfalso; congruence. }
  exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
assert(HparentOfParts6: parentOfPartitionIsPartition s6).
{
  intros partition pdentryPart HlookupPart.
  assert(HlookupPartBiss5: exists pdentryParts5,
    lookup partition (memory s5) beqAddr = Some (PDT pdentryParts5)
    /\ parent pdentryParts5 = parent pdentryPart).
  {
    rewrite Hs6 in HlookupPart. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
      subst pdentryPart. exists pdentry1. rewrite Hpdentry2. simpl. auto.
    - exists pdentryPart. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct HlookupPartBiss5 as [pdentryParts5 (HlookupPartBiss5 & HparentsEq)]. rewrite <-HparentsEq in *.
  specialize(HparentOfParts5 partition pdentryParts5 HlookupPartBiss5).
  destruct HparentOfParts5 as (HparentIsPart & Hother). split; trivial. intro HbeqPartRoot.
  specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
  rewrite HgetPartsEqs6. rewrite <-HgetPartsEqs5. split; trivial. rewrite Hs6. simpl.
  destruct (beqAddr pd (parent pdentryParts5)) eqn:HbeqPdParent.
  - exists pdentry2. reflexivity.
  - exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
}
assert(HparentsListEqss0: forall pdparent parentsList, isParentsList s parentsList pdparent
  -> isParentsList s0 parentsList pdparent).
{
  intros pdparent parentsList HparentsList. assert(HparentsLists6: isParentsList s6 parentsList pdparent).
  {
    assert(HpropsOr: isPDT pdparent s \/ isParentsList s6 parentsList pdparent).
    {
      induction parentsList as [| part]; simpl in *; auto. unfold isPDT. left.
      destruct (lookup part (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct HparentsList as (_ & [parentEntry (HlookupParent & _)] & _). rewrite HlookupParent. trivial.
    }
    destruct HpropsOr as [HparentIsPDT | Hres]; trivial. apply isPDTLookupEq in HparentIsPDT.
    destruct HparentIsPDT as [parentEntry HlookupParent].
    apply isParentsListEqPDTSameParent with pd pdentry3 s; trivial. rewrite Hs. rewrite Hs in HlookupParent.
    simpl in *. destruct (beqAddr pd pdparent) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists pdentry2. exists pdentry3. exists pdentry2.
      rewrite Hpdentry3. intuition.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists parentEntry.
      exists parentEntry. exists pdentry2. rewrite Hpdentry3. apply not_eq_sym in HbeqParts. intuition.
  }
  assert(HparentsLists5: isParentsList s5 parentsList pdparent).
  {
    assert(HpropsOr: isPDT pdparent s6 \/ isParentsList s5 parentsList pdparent).
    {
      induction parentsList as [| part]; simpl in *; auto. unfold isPDT. left.
      destruct (lookup part (memory s6) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct HparentsLists6 as (_ & [parentEntry (HlookupParent & _)] & _). rewrite HlookupParent. trivial.
    }
    destruct HpropsOr as [HparentIsPDT | Hres]; trivial. apply isPDTLookupEq in HparentIsPDT.
    destruct HparentIsPDT as [parentEntry HlookupParent].
    apply isParentsListEqPDTSameParent with pd pdentry2 s6; trivial. rewrite Hs6. rewrite Hs6 in HlookupParent.
    simpl in *. destruct (beqAddr pd pdparent) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists pdentry1. exists pdentry2. exists pdentry1.
      rewrite Hpdentry2. intuition.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists parentEntry.
      exists parentEntry. exists pdentry1. rewrite Hpdentry2. apply not_eq_sym in HbeqParts. intuition.
  }
  assert(HparentsLists4: isParentsList s4 parentsList pdparent).
  {
    assert(HpropsOr: isPDT pdparent s5 \/ isParentsList s4 parentsList pdparent).
    {
      induction parentsList as [| part]; simpl in *; auto. unfold isPDT. left.
      destruct (lookup part (memory s5) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct HparentsLists5 as (_ & [parentEntry (HlookupParent & _)] & _). rewrite HlookupParent. trivial.
    }
    destruct HpropsOr as [HparentIsPDT | Hres]; trivial. apply isPDTLookupEq in HparentIsPDT.
    destruct HparentIsPDT as [parentEntry HlookupParent]. rewrite Hs5 in HparentsLists5.
    apply isParentsListEqBERev with blockToFree (CBlockEntry (read emptyBentry) (write emptyBentry)
          (exec emptyBentry) (present emptyBentry) (accessible emptyBentry) (blockindex emptyBentry)
          (CBlock (startAddr (blockrange emptyBentry)) currFirstFreeSlot)) emptyBentry; trivial.
    rewrite Hs5 in HlookupParent. simpl in *.
    destruct (beqAddr blockToFree pdparent) eqn:HbeqBlockParent; try(exfalso; congruence).
    exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HparentsLists3: isParentsList s3 parentsList pdparent).
  {
    assert(HpropsOr: isPDT pdparent s4 \/ isParentsList s3 parentsList pdparent).
    {
      induction parentsList as [| part]; simpl in *; auto. unfold isPDT. left.
      destruct (lookup part (memory s4) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct HparentsLists4 as (_ & [parentEntry (HlookupParent & _)] & _). rewrite HlookupParent. trivial.
    }
    destruct HpropsOr as [HparentIsPDT | Hres]; trivial. apply isPDTLookupEq in HparentIsPDT.
    destruct HparentIsPDT as [parentEntry HlookupParent]. rewrite Hs4 in HparentsLists4.
    rewrite <-HlookupSceEqs3s0 in *.
    destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s3) beqAddr) eqn:HlookupSce; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    apply isParentsListEqSCERev with (CPaddr (blockToFree + scoffset))
      {| origin := nullAddr; next := nullAddr |} s7; trivial.
    rewrite Hs4 in HlookupParent. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) pdparent) eqn:HbeqSceParent; try(exfalso; congruence).
    exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HparentsLists2: isParentsList s2 parentsList pdparent).
  {
    assert(HpropsOr: isPDT pdparent s3 \/ isParentsList s2 parentsList pdparent).
    {
      induction parentsList as [| part]; simpl in *; auto. unfold isPDT. left.
      destruct (lookup part (memory s3) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct HparentsLists3 as (_ & [parentEntry (HlookupParent & _)] & _). rewrite HlookupParent. trivial.
    }
    destruct HpropsOr as [HparentIsPDT | Hres]; trivial. apply isPDTLookupEq in HparentIsPDT.
    destruct HparentIsPDT as [parentEntry HlookupParent]. rewrite Hs3 in HparentsLists3.
    rewrite <-HlookupSh1Eqs2s0 in *.
    destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s2) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    apply isParentsListEqSHERev with (CPaddr (blockToFree + sh1offset))
      {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |} s7; trivial.
    rewrite Hs3 in HlookupParent. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) pdparent) eqn:HbeqSh1Parent; try(exfalso; congruence).
    exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HparentsLists1: isParentsList s1 parentsList pdparent).
  {
    assert(HpropsOr: isPDT pdparent s2 \/ isParentsList s1 parentsList pdparent).
    {
      induction parentsList as [| part]; simpl in *; auto. unfold isPDT. left.
      destruct (lookup part (memory s2) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct HparentsLists2 as (_ & [parentEntry (HlookupParent & _)] & _). rewrite HlookupParent. trivial.
    }
    destruct HpropsOr as [HparentIsPDT | Hres]; trivial. apply isPDTLookupEq in HparentIsPDT.
    destruct HparentIsPDT as [parentEntry HlookupParent]. rewrite Hs2 in HparentsLists2.
    rewrite <-HlookupBlockEqs1s0 in *. apply isParentsListEqBERev with blockToFree emptyBentry bentryToF; trivial.
    rewrite Hs2 in HlookupParent. simpl in *.
    destruct (beqAddr blockToFree pdparent) eqn:HbeqBlockParent; try(exfalso; congruence).
    exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HpropsOr: isPDT pdparent s1 \/ isParentsList s0 parentsList pdparent).
  {
    induction parentsList as [| part]; simpl in *; auto. unfold isPDT. left.
    destruct (lookup part (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    destruct HparentsLists1 as (_ & [parentEntry (HlookupParent & _)] & _). rewrite HlookupParent. trivial.
  }
  destruct HpropsOr as [HparentIsPDT | Hres]; trivial. apply isPDTLookupEq in HparentIsPDT.
  destruct HparentIsPDT as [parentEntry HlookupParent].
  apply isParentsListEqPDTSameParent with pd pdentry1 s1; trivial. 2: unfold cons1Free in *; intuition.
  rewrite Hs1. rewrite Hs1 in HlookupParent. simpl in *. destruct (beqAddr pd pdparent) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists pdentry. exists pdentry1. exists pdentry.
    rewrite Hpdentry1. intuition.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists parentEntry.
    exists parentEntry. exists pdentry. rewrite Hpdentry1. apply not_eq_sym in HbeqParts. intuition.
}
assert(HparentsListEqs0s: forall pdparent parentsList, isParentsList s0 parentsList pdparent
  -> isParentsList s parentsList pdparent).
{
  intros pdparent parentsList HparentsLists0.
  assert(HpropsOr: (parentsList = []) \/ isParentsList s1 parentsList pdparent).
  {
    revert pdparent HparentsLists0. induction parentsList as [| part]; simpl; intros; auto. right.
    destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct HparentsLists0 as (HbeqParentRoot & [parentEntry (HlookupParent & Hparent)] & HparentsLists0).
    specialize(IHparentsList part HparentsLists0). assert(isPDT part s1).
    {
      unfold isPDT. rewrite Hs1. simpl. destruct (beqAddr pd part) eqn:HbeqParts; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupPart.
      trivial.
    }
    unfold isPDT in *. destruct (lookup part (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
    split; trivial. assert(isParentsList s1 parentsList part).
    {
      destruct IHparentsList as [HbeqListNull | IHparentsList].
      - subst parentsList. simpl. trivial.
      - assumption.
    }
    split; trivial. rewrite Hs1. simpl. destruct (beqAddr pd pdparent) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. exists pdentry1. split; trivial. rewrite Hpdentry1.
      rewrite HlookupParts0 in *. injection HlookupParent as HpdentriesEq. subst parentEntry. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. exists parentEntry.
      auto.
  }
  assert(HpropsOrList: parentsList = [] \/ parentsList <> []) by (apply Classical_Prop.classic).
  destruct HpropsOrList as [HbeqListNull | HbeqListNull]; try(subst parentsList; auto).
  destruct HpropsOr as [Hcontra | HparentsLists1]; try(exfalso; congruence).
  assert(HparentsLists2: isParentsList s2 parentsList pdparent).
  {
    rewrite Hs2. apply isParentsListEqBE with bentryToF; trivial.
    - rewrite HlookupBlockEqs1s0. assumption.
    - destruct parentsList; try(exfalso; congruence). simpl in *.
      destruct (lookup p (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct HparentsLists1 as (_ & [parentEntry (HlookupParent & _)] & _). exists parentEntry. assumption.
  }
  assert(HparentsLists3: isParentsList s3 parentsList pdparent).
  {
    rewrite Hs3. rewrite <-HlookupSh1Eqs2s0 in *.
    destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s2) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply isParentsListEqSHE with s7; trivial.
    destruct parentsList; try(exfalso; congruence). simpl in *.
    destruct (lookup p (memory s2) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    destruct HparentsLists2 as (_ & [parentEntry (HlookupParent & _)] & _). exists parentEntry. assumption.
  }
  assert(HparentsLists4: isParentsList s4 parentsList pdparent).
  {
    rewrite Hs4. rewrite <-HlookupSceEqs3s0 in *.
    destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s3) beqAddr) eqn:HlookupSce; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply isParentsListEqSCE with s7; trivial.
    destruct parentsList; try(exfalso; congruence). simpl in *.
    destruct (lookup p (memory s3) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    destruct HparentsLists3 as (_ & [parentEntry (HlookupParent & _)] & _). exists parentEntry. assumption.
  }
  assert(HparentsLists5: isParentsList s5 parentsList pdparent).
  {
    rewrite Hs5. apply isParentsListEqBE with emptyBentry; trivial.
    destruct parentsList; try(exfalso; congruence). simpl in *.
    destruct (lookup p (memory s4) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    destruct HparentsLists4 as (_ & [parentEntry (HlookupParent & _)] & _). exists parentEntry. assumption.
  }
  assert(HparentsLists6: isParentsList s6 parentsList pdparent).
  {
    apply isParentsListEqPDTSameParentRev with pd pdentry2 s5; trivial.
    destruct parentsList; try(exfalso; congruence). simpl in *.
    destruct (lookup p (memory s5) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    destruct HparentsLists5 as (_ & [parentEntry (HlookupParent & _)] & _). rewrite Hs6. simpl.
    destruct (beqAddr pd pdparent) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists pdentry1. exists pdentry2. exists pdentry1.
      intuition. rewrite Hpdentry2. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. exists parentEntry.
      exists parentEntry. exists pdentry1. split; trivial. split; trivial. rewrite Hpdentry2. auto.
  }
  apply isParentsListEqPDTSameParentRev with pd pdentry3 s6; trivial.
  destruct parentsList; try(exfalso; congruence). simpl in *.
  destruct (lookup p (memory s6) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  destruct HparentsLists6 as (_ & [parentEntry (HlookupParent & _)] & _). rewrite Hs. simpl.
  destruct (beqAddr pd pdparent) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists pdentry2. exists pdentry3. exists pdentry2.
    intuition. rewrite Hpdentry3. reflexivity.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. exists parentEntry.
    exists parentEntry. exists pdentry2. split; trivial. split; trivial. rewrite Hpdentry3. auto.
}
intuition. unfold cons1Free. split.

{ (* BEGIN nullAddrExists s *)
  unfold nullAddrExists. unfold isPADDR. rewrite Hs. rewrite Hs6. simpl. rewrite HbeqPartNull. rewrite IL.beqAddrTrue.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END nullAddrExists *)
}

split.
{ (* BEGIN wellFormedFstShadowIfBlockEntry s *)
  assert(Hcons0: wellFormedFstShadowIfBlockEntry s0) by (unfold cons1Free in *; intuition).
  intros block HblockIsBE. assert(HblockBisIsBEs0: isBE block s0).
  {
    unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs6 in HblockIsBE. simpl in *.
    destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite IL.beqAddrTrue in HblockIsBE.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HblockIsBE. simpl in *.
    destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HblockIsBE. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in HblockIsBE.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HblockIsBE. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartBlockBis in HblockIsBE.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 block HblockBisIsBEs0). unfold isSHE in *. rewrite Hs. rewrite Hs6. simpl.
  destruct (beqAddr pd (CPaddr (block + sh1offset))) eqn:HbeqPartSh1Bis.
  { rewrite <-DTL.beqAddrTrue in HbeqPartSh1Bis. subst pd. rewrite HlookupParts0 in *. congruence. }
  rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1Bis.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Bis. subst blockToFree.
    destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (block + sh1offset))) eqn:HbeqSceSh1Bis.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceSh1Bis. rewrite HbeqSceSh1Bis in *.
    destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  rewrite beqAddrFalse in *. rewrite HbeqBlockSh1Bis. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartSh1Bis. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END wellFormedFstShadowIfBlockEntry *)
}

split.
{ (* BEGIN PDTIfPDFlag s *)
  intros idPDchild sh1entryaddr HcheckChild.
  assert(HlookupChildEq: lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s5) beqAddr).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). rewrite Hs. unfold sh1entryAddr in *. rewrite Hs in Hsh1.
    rewrite Hs6. rewrite Hs6 in Hsh1. simpl in *.
    destruct (beqAddr pd idPDchild) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite IL.beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr.
  unfold entryPDT. rewrite HlookupChildEq in *.
  assert(HcheckChilds5: true = checkChild idPDchild s5 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s5).
  {
    destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. unfold checkChild.
    destruct (lookup idPDchild (memory s5) beqAddr); try(congruence). destruct v; try(congruence).
    rewrite Hs in HcheckChild. rewrite Hs6 in HcheckChild. simpl in *.
    destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis; try(exfalso; congruence). rewrite IL.beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(HPDTIfPDFlags5 idPDchild sh1entryaddr HcheckChilds5).
  destruct HPDTIfPDFlags5 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
  exists startaddr. split; trivial. unfold entryPDT in *.
  destruct (lookup idPDchild (memory s5) beqAddr); try(congruence). destruct v; try(congruence).
  rewrite Hs. rewrite Hs6. simpl. destruct (beqAddr pd (startAddr (blockrange b))) eqn:HbeqPartStart.
  - rewrite <-DTL.beqAddrTrue in HbeqPartStart. subst pd. rewrite HlookupParts5 in *. assumption.
  - rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END PDTIfPDFlag *)
}

split.
{ (* BEGIN AccessibleNoPDFlag s *)
  assert(Hcons0: AccessibleNoPDFlag s0) by (unfold cons1Free in *; intuition).
  intros block sh1entryaddr HblockIsBE Hsh1 HAflag. unfold isBE in *. unfold sh1entryAddr in *.
  unfold bentryAFlag in *. rewrite Hs in HblockIsBE. rewrite Hs in Hsh1. rewrite Hs in HAflag. rewrite Hs6 in Hsh1.
  rewrite Hs6 in HblockIsBE. rewrite Hs6 in HAflag. simpl in *.
  destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite IL.beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HblockIsBE. rewrite Hs5 in Hsh1.
  rewrite Hs5 in HAflag. simpl in *. destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in HAflag. simpl in *. rewrite HnewB in HAflag. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in Hsh1.
  rewrite Hs4 in HblockIsBE. rewrite Hs4 in HAflag. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hsh1.
  rewrite Hs3 in HblockIsBE. rewrite Hs3 in HAflag. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in Hsh1.
  rewrite Hs2 in HblockIsBE. rewrite Hs2 in HAflag. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in Hsh1.
  rewrite Hs1 in HblockIsBE. rewrite Hs1 in HAflag. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAflag). unfold sh1entryPDflag in *. rewrite Hs. rewrite Hs6.
  simpl. destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPartSh1Bis. rewrite HbeqPartSh1Bis in *. rewrite HlookupParts0 in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite IL.beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree sh1entryaddr) eqn:HbeqBlockSh1Bis.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Bis. rewrite HbeqBlockSh1Bis in *.
    destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) sh1entryaddr) eqn:HbeqSceSh1Bis.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceSh1Bis. rewrite HbeqSceSh1Bis in *.
    destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) sh1entryaddr) eqn:HbeqSh1s; auto.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  rewrite beqAddrFalse in *. rewrite HbeqBlockSh1Bis. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartSh1Bis. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END AccessibleNoPDFlag *)
}

split.
{ (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
  assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold cons1Free in *; intuition).
  intros partition pdentryBis HlookupPart HbeqFirstNull. rewrite Hs in HlookupPart. rewrite Hs6 in HlookupPart.
  simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
  - injection HlookupPart as HpdentriesEq. subst pdentryBis. rewrite Hpdentry3. simpl. rewrite Hpdentry2. simpl.
    unfold isBE. unfold isFreeSlot. rewrite Hs. rewrite Hs6. simpl. rewrite HbeqPartBlock. rewrite IL.beqAddrTrue.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl. rewrite IL.beqAddrTrue.
    split; trivial. rewrite HnewB2. simpl. rewrite beqAddrFalse in *. rewrite HbeqPartSh1. rewrite HbeqBlockPart.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlockSh1. rewrite HbeqPartSce. rewrite HbeqBlockPart.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockSce.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl. rewrite IL.beqAddrTrue.
    rewrite beqAddrFalse in *. rewrite HbeqSceSh1. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite IL.beqAddrTrue.
    rewrite HnewB. simpl. intuition.
  - rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlookupPart. simpl in *.
    destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs4 in HlookupPart. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs3 in HlookupPart. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs2 in HlookupPart. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HlookupPart. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentryBis HlookupPart HbeqFirstNull). destruct Hcons0 as (HfirstIsBE & HfirstIsFree).
    unfold isBE in *. unfold isFreeSlot in *. rewrite Hs at 1. rewrite Hs at 1. rewrite Hs6. simpl.
    destruct (beqAddr pd (firstfreeslot pdentryBis)) eqn:HbeqPartFirst.
    { rewrite <-DTL.beqAddrTrue in HbeqPartFirst. subst pd. rewrite HlookupParts0 in *. exfalso; congruence. }
    rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
    destruct (beqAddr blockToFree (firstfreeslot pdentryBis)) eqn:HbeqBlockFirst.
    + (*technically impossible, but easier to prove that way*)
      split; trivial. rewrite HnewB2. simpl. rewrite HnewB. simpl. rewrite <-DTL.beqAddrTrue in HbeqBlockFirst.
      rewrite <-HbeqBlockFirst in *. rewrite Hs. rewrite Hs6. simpl. rewrite beqAddrFalse in *. rewrite HbeqPartSh1.
      rewrite HbeqPartSce. rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqBlockSh1. rewrite HbeqBlockSce. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqSceSh1. rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite IL.beqAddrTrue.
      intuition.
    + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) (firstfreeslot pdentryBis)) eqn:HbeqSceFirst.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceFirst. rewrite HbeqSceFirst in *. exfalso.
        destruct (lookup (firstfreeslot pdentryBis) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (firstfreeslot pdentryBis)) eqn:HbeqSh1First.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1First. rewrite HbeqSh1First in *. exfalso.
        destruct (lookup (firstfreeslot pdentryBis) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqBlockFirst. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqPartFirst. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. split; trivial.
      destruct (lookup (firstfreeslot pdentryBis) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite Hs. rewrite Hs6. simpl.
      destruct (beqAddr pd (CPaddr (firstfreeslot pdentryBis + sh1offset))) eqn:HbeqPartFirstSh1.
      { rewrite <-DTL.beqAddrTrue in HbeqPartFirstSh1. subst pd. rewrite HlookupParts0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite IL.beqAddrTrue.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
      destruct (beqAddr blockToFree (CPaddr (firstfreeslot pdentryBis + sh1offset))) eqn:HbeqBlockFirstSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockFirstSh1. rewrite <-HbeqBlockFirstSh1 in *.
        destruct (lookup blockToFree (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (blockToFree+scoffset)) (CPaddr (firstfreeslot pdentryBis+sh1offset)))
        eqn:HbeqSceFirstSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceFirstSh1. rewrite <-HbeqSceFirstSh1 in *.
        destruct (lookup (CPaddr (blockToFree+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr (CPaddr (blockToFree+sh1offset)) (CPaddr (firstfreeslot pdentryBis+sh1offset)))
        eqn:HbeqSh1FirstSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1FirstSh1. apply CPaddrAddEq in HbeqSh1FirstSh1; trivial.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqBlockFirstSh1. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqPartFirstSh1. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (firstfreeslot pdentryBis + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr pd (CPaddr (firstfreeslot pdentryBis + scoffset))) eqn:HbeqPartFirstSce.
      { rewrite <-DTL.beqAddrTrue in HbeqPartFirstSce. subst pd. rewrite HlookupParts0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqBlockPart. simpl.
      destruct (beqAddr blockToFree (CPaddr (firstfreeslot pdentryBis + scoffset))) eqn:HbeqBlockFirstSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockFirstSce. rewrite <-HbeqBlockFirstSce in *.
        destruct (lookup blockToFree (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqSceBlock. simpl. rewrite <-beqAddrFalse in *.
      destruct (beqAddr (CPaddr (blockToFree+scoffset)) (CPaddr (firstfreeslot pdentryBis+scoffset))) eqn:HbeqSces.
      { rewrite <-DTL.beqAddrTrue in HbeqSces. apply CPaddrAddEq in HbeqSces; trivial. exfalso; congruence. }
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite beqAddrFalse in *. rewrite HbeqSh1Sce.
      simpl. destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (firstfreeslot pdentryBis + scoffset)))
        eqn:HbeqSh1FirstSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1FirstSce. rewrite <-HbeqSh1FirstSce in *.
        destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqBlockSh1. simpl. rewrite HbeqBlockFirstSce. rewrite HbeqPartBlock.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqPartFirstSce. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
}

split.
{ (* BEGIN multiplexerIsPDT s *)
  unfold multiplexerIsPDT. unfold isPDT in *. rewrite Hs. rewrite Hs6. simpl.
  destruct (beqAddr pd multiplexer) eqn:HbeqParts; trivial.
  rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree multiplexer) eqn:HbeqBlockMult.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockMult. rewrite HbeqBlockMult in *. rewrite HlookupBlockEqs1s0 in *.
    destruct (lookup multiplexer (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END multiplexerIsPDT *)
}

split.
{ (* BEGIN currentPartitionInPartitionsList s *)
  assert(Hcons0: currentPartitionInPartitionsList s0) by (unfold cons1Free in *; intuition).
  unfold currentPartitionInPartitionsList. rewrite HcurrEq. rewrite HgetPartsEqs. assumption.
  (* END currentPartitionInPartitionsList *)
}

split.
{ (* BEGIN wellFormedShadowCutIfBlockEntry s *)
  assert(Hcons0: wellFormedShadowCutIfBlockEntry s0) by (unfold cons1Free in *; intuition).
  intros block HblockIsBE. assert(HblockBisIsBEs0: isBE block s0).
  {
    unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs6 in HblockIsBE. simpl in *.
    destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite IL.beqAddrTrue in HblockIsBE.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HblockIsBE. simpl in *.
    destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HblockIsBE. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in HblockIsBE.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HblockIsBE. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartBlockBis in HblockIsBE.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 block HblockBisIsBEs0). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr.
  split; trivial. unfold isSCE in *. rewrite Hs. rewrite Hs6. simpl. rewrite beqAddrTrue in *.
  destruct (beqAddr pd scentryaddr) eqn:HbeqPartSceBis.
  { rewrite <-DTL.beqAddrTrue in HbeqPartSceBis. subst pd. rewrite HlookupParts0 in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree scentryaddr) eqn:HbeqBlockSceBis.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockSceBis. rewrite HbeqBlockSceBis in *.
    destruct (lookup scentryaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) scentryaddr) eqn:HbeqSces; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) scentryaddr) eqn:HbeqSh1SceBis.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1SceBis. rewrite HbeqSh1SceBis in *.
    destruct (lookup scentryaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  rewrite beqAddrFalse in *. rewrite HbeqBlockSceBis. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartSceBis. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END wellFormedShadowCutIfBlockEntry *)
}

split.
{ (* BEGIN BlocksRangeFromKernelStartIsBE s *)
  assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by (unfold cons1Free in *; intuition).
  intros kernel idx HkernIsKS HltIdxKernEntries. assert(HkernIsKSs0: isKS kernel s0).
  {
    unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs6 in HkernIsKS. simpl in *.
    destruct (beqAddr pd kernel) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite IL.beqAddrTrue in HkernIsKS.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HkernIsKS. simpl in *.
    destruct (beqAddr blockToFree kernel) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst kernel. rewrite HnewB2 in HkernIsKS. simpl in *.
      rewrite HnewB in HkernIsKS. simpl in *. subst blockToFreeIdx. rewrite <-HlookupBlockEqs1s0.
      unfold bentryBlockIndex in *. destruct (lookup blockToFree (memory s1) beqAddr); try(congruence).
      destruct v; congruence.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) kernel) eqn:HbeqSceBlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) kernel) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HkernIsKS. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in HkernIsKS.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HkernIsKS. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartBlockBis in HkernIsKS.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 kernel idx HkernIsKSs0 HltIdxKernEntries). unfold isBE in *. rewrite Hs. rewrite Hs6. simpl.
  destruct (beqAddr pd (CPaddr (kernel + idx))) eqn:HbeqPartIdx.
  { rewrite <-DTL.beqAddrTrue in HbeqPartIdx. subst pd. rewrite HlookupParts0 in *. congruence. }
  rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree (CPaddr (kernel + idx))) eqn:HbeqBlockIdx; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (kernel + idx))) eqn:HbeqSceIdx.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceIdx. rewrite HbeqSceIdx in *.
    destruct (lookup (CPaddr (kernel + idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (kernel + idx))) eqn:HbeqSh1Idx.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1Idx. rewrite HbeqSh1Idx in *.
    destruct (lookup (CPaddr (kernel + idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  rewrite beqAddrFalse in *. rewrite HbeqBlockIdx. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartIdx. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END BlocksRangeFromKernelStartIsBE *)
}

split.
{ (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
  assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0) by (unfold cons1Free in *; intuition).
  intros block idx HblockIsBE Hidx. assert(Hblocks0: isBE block s0 /\ bentryBlockIndex block idx s0).
  {
    unfold isBE in *. unfold bentryBlockIndex in *. rewrite Hs in HblockIsBE. rewrite Hs6 in HblockIsBE.
    rewrite Hs in Hidx. rewrite Hs6 in Hidx. simpl in *.
    destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HblockIsBE. rewrite Hs5 in Hidx.
    simpl in *. destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. split; trivial. rewrite HnewB2 in Hidx. simpl in *.
      rewrite HnewB in Hidx. simpl in *. subst idx. rewrite <-HlookupBlockEqs1s0. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HblockIsBE. rewrite Hs4 in Hidx. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HblockIsBE. rewrite Hs3 in Hidx. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HblockIsBE. rewrite Hs2 in Hidx. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HblockIsBE. rewrite Hs1 in Hidx. simpl in *. rewrite beqAddrFalse in *.
      rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct Hblocks0 as (HblockBisIsBEs0 & Hidxs0). specialize(Hcons0 block idx HblockBisIsBEs0 Hidxs0).
  unfold isKS in *. rewrite Hs. rewrite Hs6. simpl. destruct (beqAddr pd (CPaddr (block - idx))) eqn:HbeqPartKern.
  { rewrite <-DTL.beqAddrTrue in HbeqPartKern. subst pd. rewrite HlookupParts0 in *. congruence. }
  rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree (CPaddr (block - idx))) eqn:HbeqBlockKern.
  - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. rewrite HbeqBlockKern in *. rewrite HnewB2. simpl. rewrite HnewB.
    simpl. unfold bentryBlockIndex in *. rewrite HlookupBlockEqs1s0 in *.
    destruct (lookup (CPaddr (block - idx)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite Hcons0 in *. assumption.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (block - idx))) eqn:HbeqSceKern.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceKern. rewrite HbeqSceKern in *.
      destruct (lookup (CPaddr (block - idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (block - idx))) eqn:HbeqSh1Kern.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Kern. rewrite HbeqSh1Kern in *.
      destruct (lookup (CPaddr (block - idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlockKern. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqPartKern. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END KernelStructureStartFromBlockEntryAddrIsKS *)
}

split.
{ (* BEGIN sh1InChildLocationIsBE s *)
  assert(Hcons0: sh1InChildLocationIsBE s0) by (unfold cons1Free in *; intuition).
  intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull. rewrite Hs in HlookupSh1. rewrite Hs6 in HlookupSh1.
  simpl in *. destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis; try(exfalso; congruence).
  rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlookupSh1. simpl in *.
  destruct (beqAddr blockToFree sh1entryaddr) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HlookupSh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) sh1entryaddr) eqn:HbeqSceSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HlookupSh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
  { injection HlookupSh1 as Hsh1entriesEq. subst sh1entry. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HlookupSh1. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockSh1Bis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs1 in HlookupSh1. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartSh1Bis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). unfold isBE in *. rewrite Hs. rewrite Hs6. simpl.
  destruct (beqAddr pd (inChildLocation sh1entry)) eqn:HbeqPartLoc.
  { rewrite <-DTL.beqAddrTrue in HbeqPartLoc. subst pd. rewrite HlookupParts0 in *. congruence. }
  rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree (inChildLocation sh1entry)) eqn:HbeqBlockLoc; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) (inChildLocation sh1entry)) eqn:HbeqSceLoc.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceLoc. rewrite HbeqSceLoc in *.
    destruct (lookup (inChildLocation sh1entry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (inChildLocation sh1entry)) eqn:HbeqSh1Loc.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1Loc. rewrite HbeqSh1Loc in *.
    destruct (lookup (inChildLocation sh1entry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  rewrite beqAddrFalse in *. rewrite HbeqBlockLoc. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartLoc. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END sh1InChildLocationIsBE *)
}

split.
{ (* BEGIN StructurePointerIsKS s *)
  intros partition pdentryBis HlookupPart HbeqStructNull.
  assert(HlookupPartBiss5: exists pdentryBiss5, lookup partition (memory s5) beqAddr = Some (PDT pdentryBiss5)
    /\ structure pdentryBiss5 = structure pdentryBis).
  {
    rewrite Hs in HlookupPart. rewrite Hs6 in HlookupPart. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. injection HlookupPart as HpdentriesEq. subst pdentryBis.
      exists pdentry1. split; trivial. rewrite Hpdentry3. simpl. rewrite Hpdentry2. reflexivity.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists pdentryBis. split; trivial.
  }
  destruct HlookupPartBiss5 as [pdentryBiss5 (HlookupPartBiss5 & HstructEq)]. rewrite <-HstructEq in *.
  specialize(HstructIsKSs5 partition pdentryBiss5 HlookupPartBiss5 HbeqStructNull). unfold isKS in *. rewrite Hs.
  rewrite Hs6. simpl. destruct (beqAddr pd (structure pdentryBiss5)) eqn:HbeqPartStruct.
  { rewrite <-DTL.beqAddrTrue in HbeqPartStruct. subst pd. rewrite HlookupParts5 in *. congruence. }
  rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END StructurePointerIsKS *)
}

split.
{ (* BEGIN NextKSIsKS s *)
  assert(Hcons0: NextKSIsKS s0) by (unfold cons1Free in *; intuition).
  intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull.
  assert(Hkerns0: isKS kernel s0 /\ nextKSAddr kernel nextKSaddr s0).
  {
    unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs6 in HkernIsKS.
    rewrite Hs in HnextAddr. rewrite Hs6 in HnextAddr. simpl in *.
    destruct (beqAddr pd kernel) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HkernIsKS.
    rewrite Hs5 in HnextAddr. simpl in *. destruct (beqAddr blockToFree kernel) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst kernel. rewrite HnewB2 in HkernIsKS. simpl in *.
      rewrite HnewB in HkernIsKS. simpl in *. subst blockToFreeIdx. rewrite <-HlookupBlockEqs1s0.
      unfold bentryBlockIndex in *. destruct (lookup blockToFree (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HkernIsKS. rewrite Hs4 in HnextAddr. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) kernel) eqn:HbeqSceBlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HkernIsKS. rewrite Hs3 in HnextAddr. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) kernel) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HkernIsKS. rewrite Hs2 in HnextAddr. simpl in *. rewrite beqAddrFalse in *.
      rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HkernIsKS.
      rewrite Hs1 in HnextAddr. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartBlockBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct Hkerns0 as (HkernIsKSs0 & HnextAddrs0). unfold nextKSentry in *. rewrite Hs in HnextKSAddr.
  rewrite Hs6 in HnextKSAddr. simpl in *. rewrite beqAddrTrue in *.
  destruct (beqAddr pd nextKSaddr) eqn:HbeqPartNextA; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HnextKSAddr. simpl in *.
  destruct (beqAddr blockToFree nextKSaddr) eqn:HbeqBlockNextA; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HnextKSAddr. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) nextKSaddr) eqn:HbeqSceNextA; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HnextKSAddr. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) nextKSaddr) eqn:HbeqSh1NextA; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HnextKSAddr. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockNextA in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs1 in HnextKSAddr. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartNextA in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKSs0 HnextAddrs0 HnextKSAddr HbeqNextNull).
  unfold isKS in *. rewrite Hs. rewrite Hs6. simpl. destruct (beqAddr pd nextKS) eqn:HbeqPartNext.
  { rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst pd. rewrite HlookupParts0 in *. congruence. }
  rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree nextKS) eqn:HbeqBlockNext.
  - rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite HbeqBlockNext in *. unfold bentryBlockIndex in *.
    rewrite HlookupBlockEqs1s0 in *. rewrite HnewB2. simpl. rewrite HnewB. simpl.
    destruct (lookup nextKS (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    rewrite Hcons0 in *. assumption.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) nextKS) eqn:HbeqSceNext.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceNext. rewrite HbeqSceNext in *.
      destruct (lookup nextKS (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) nextKS) eqn:HbeqSh1Next.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *.
      destruct (lookup nextKS (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlockNext. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqPartNext. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END NextKSIsKS *)
}

split.
{ (* BEGIN NextKSOffsetIsPADDR s *)
  assert(Hcons0: NextKSOffsetIsPADDR s0) by (unfold cons1Free in *; intuition).
  intros kernel nextKSaddr HkernIsKS HnextAddr.
  assert(Hkerns0: isKS kernel s0 /\ nextKSAddr kernel nextKSaddr s0).
  {
    unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs6 in HkernIsKS.
    rewrite Hs in HnextAddr. rewrite Hs6 in HnextAddr. simpl in *.
    destruct (beqAddr pd kernel) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HkernIsKS.
    rewrite Hs5 in HnextAddr. simpl in *. destruct (beqAddr blockToFree kernel) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst kernel. rewrite HnewB2 in HkernIsKS. simpl in *.
      rewrite HnewB in HkernIsKS. simpl in *. subst blockToFreeIdx. rewrite <-HlookupBlockEqs1s0.
      unfold bentryBlockIndex in *. destruct (lookup blockToFree (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HkernIsKS. rewrite Hs4 in HnextAddr. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) kernel) eqn:HbeqSceBlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HkernIsKS. rewrite Hs3 in HnextAddr. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) kernel) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HkernIsKS. rewrite Hs2 in HnextAddr. simpl in *. rewrite beqAddrFalse in *.
      rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HkernIsKS.
      rewrite Hs1 in HnextAddr. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartBlockBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
  }
  destruct Hkerns0 as (HkernIsKSs0 & HnextAddrs0). specialize(Hcons0 kernel nextKSaddr HkernIsKSs0 HnextAddrs0).
  destruct Hcons0 as (HnextAIsPADDR & HbeqNextANull). split; trivial. unfold isPADDR in *. rewrite Hs. rewrite Hs6.
  simpl. rewrite beqAddrTrue. destruct (beqAddr pd nextKSaddr) eqn:HbeqPartNextA.
  { rewrite <-DTL.beqAddrTrue in HbeqPartNextA. subst pd. rewrite HlookupParts0 in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree nextKSaddr) eqn:HbeqBlockNextA.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockNextA. rewrite HbeqBlockNextA in *.
    destruct (lookup nextKSaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) nextKSaddr) eqn:HbeqSceNextA.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceNextA. rewrite HbeqSceNextA in *.
    destruct (lookup nextKSaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) nextKSaddr) eqn:HbeqSh1NextA.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1NextA. rewrite HbeqSh1NextA in *.
    destruct (lookup nextKSaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  rewrite beqAddrFalse in *. rewrite HbeqBlockNextA. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartNextA. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END NextKSOffsetIsPADDR *)
}

split.
{ (* BEGIN NoDupInFreeSlotsList s *)
  assert(Hcons0: NoDupInFreeSlotsList s0) by (unfold cons1Free in *; intuition).
  intros partition pdentryBis HlookupPart.
  assert(HlookupPartBiss0: exists pdentryBiss0, lookup partition (memory s0) beqAddr = Some (PDT pdentryBiss0)).
  {
    rewrite Hs in HlookupPart. rewrite Hs6 in HlookupPart. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. exists pdentry. assumption.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HlookupPart. simpl in *.
      destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupPart. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HlookupPart. simpl in *. exists pdentryBis. rewrite beqAddrFalse in *. rewrite HbeqParts in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  destruct HlookupPartBiss0 as [pdentryBiss0 HlookupPartBiss0].
  specialize(Hcons0 partition pdentryBiss0 HlookupPartBiss0).
  destruct Hcons0 as [optFreeList (Hlist & HwellFormedList & HnoDupList)]. subst optFreeList.
  destruct (beqAddr pd partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HgetFreeEqPdss0.
    exists (SomePaddr blockToFree :: getFreeSlotsList pd s0). split; trivial. simpl. split; trivial.
    apply NoDup_cons; trivial.
    assert(HfreeSlots: freeSlotsListIsFreeSlot s0) by (unfold cons1Free in *; intuition).
    contradict HblockIsNotFree.
    assert(HeqFree: getFreeSlotsList pd s0 = getFreeSlotsList pd s0
      /\ wellFormedFreeSlotsList (getFreeSlotsList pd s0) <> False) by (split; trivial).
    specialize(HfreeSlots pd blockToFree (getFreeSlotsList pd s0) (filterOptionPaddr (getFreeSlotsList pd s0))).
    rewrite <-beqAddrFalse in *. apply HfreeSlots; auto.
  - assert(HpartIsPDT: isPDT partition s0) by (unfold isPDT; rewrite HlookupPartBiss0; trivial).
    pose proof (HgetFreeEqss0NotPd partition HpartIsPDT HbeqParts) as HgetFreeEq. rewrite HgetFreeEq.
    exists (getFreeSlotsList partition s0). auto.
  (* END NoDupInFreeSlotsList *)
}

split.
{ (* BEGIN freeSlotsListIsFreeSlot s *)
  assert(Hcons0: freeSlotsListIsFreeSlot s0) by (unfold cons1Free in *; intuition).
  intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
  assert(HpartIsPDTs0: isPDT partition s0).
  {
    unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs6 in HpartIsPDT. simpl in *.
    destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. rewrite HlookupParts0. trivial.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HpartIsPDT. simpl in *.
      destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  destruct (beqAddr pd partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HgetFreeEqPdss0 in HwellFormed.
    destruct HwellFormed as (HoptList & HwellFormedList). destruct HaddrInList as (HfreeList & HaddrInList).
    rewrite HfreeList in HaddrInList. rewrite HoptList in HaddrInList. simpl in *.
    destruct HaddrInList as [HaddrIsBlock | HaddrInListRec].
    + subst addr. assumption.
    + set(optionfreeslotslists0 := getFreeSlotsList pd s0). fold optionfreeslotslists0 in HaddrInListRec.
      set(freeslotslists0 := filterOptionPaddr optionfreeslotslists0). fold freeslotslists0 in HaddrInListRec.
      subst optionfreeslotslist. simpl in *. assert(Hopts0: optionfreeslotslists0 = getFreeSlotsList pd s0
        /\ wellFormedFreeSlotsList optionfreeslotslists0 <> False) by auto.
      assert(Hfrees0: freeslotslists0 = filterOptionPaddr optionfreeslotslists0 /\ In addr freeslotslists0) by auto.
      specialize(Hcons0 pd addr optionfreeslotslists0 freeslotslists0 HpartIsPDTs0 Hopts0 Hfrees0 HbeqAddrNull).
      unfold isFreeSlot in *. rewrite Hs. rewrite Hs6. simpl. destruct (beqAddr pd addr) eqn:HbeqPartAddr.
      { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
      destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr.
      { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *.
        destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *.
        destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr pd (CPaddr (addr + sh1offset))) eqn:HbeqPartSh1Bis.
      { rewrite <-DTL.beqAddrTrue in HbeqPartSh1Bis. subst pd. rewrite HlookupParts0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqPartBlock. rewrite HbeqBlockPart. simpl.
      destruct (beqAddr blockToFree (CPaddr (addr + sh1offset))) eqn:HbeqBlockSh1Bis.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Bis. rewrite HbeqBlockSh1Bis in *.
        destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite HbeqSceBlock. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      simpl. destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (addr + sh1offset))) eqn:HbeqSceSh1Bis.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceSh1Bis. rewrite HbeqSceSh1Bis in *.
        destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqSh1Sce. simpl.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (addr + sh1offset))) eqn:HbeqSh1s.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1s. exfalso. rewrite <-beqAddrFalse in *.
        apply CPaddrAddEq in HbeqSh1s; trivial. congruence.
      }
      rewrite HbeqBlockSh1. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockSh1Bis. rewrite HbeqPartSh1. simpl. rewrite HbeqPartSh1Bis.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr pd (CPaddr (addr + scoffset))) eqn:HbeqPartSceBis.
      { rewrite <-DTL.beqAddrTrue in HbeqPartSceBis. subst pd. rewrite HlookupParts0 in *. congruence. }
      rewrite beqAddrFalse in *. rewrite HbeqBlockPart. simpl.
      destruct (beqAddr blockToFree (CPaddr (addr + scoffset))) eqn:HbeqBlockSceBis.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSceBis. rewrite HbeqBlockSceBis in *.
        destruct (lookup (CPaddr (addr + scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite HbeqScePart. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      simpl. destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (addr + scoffset))) eqn:HbeqSces.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSces. exfalso. apply CPaddrAddEq in HbeqSces; trivial. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqSh1Block. simpl.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (addr + scoffset))) eqn:HbeqSh1SceBis.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1SceBis. rewrite HbeqSh1SceBis in *.
        destruct (lookup (CPaddr (addr + scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite HbeqBlockSce. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockSceBis. rewrite HbeqPartSce. simpl. rewrite HbeqPartSceBis.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - pose proof (HgetFreeEqss0NotPd partition HpartIsPDTs0 HbeqParts) as HgetFreeEq. rewrite HgetFreeEq in *.
    specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDTs0 HwellFormed HaddrInList
      HbeqAddrNull). unfold isFreeSlot in *. unfold isPDT in *. rewrite Hs. rewrite Hs6. simpl.
    destruct (beqAddr pd addr) eqn:HbeqPartAddr.
    { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
    destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr.
    { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. exfalso; congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *.
      destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *.
      destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    destruct (beqAddr pd (CPaddr (addr + sh1offset))) eqn:HbeqPartSh1Bis.
    { rewrite <-DTL.beqAddrTrue in HbeqPartSh1Bis. subst pd. rewrite HlookupParts0 in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite beqAddrFalse in *. rewrite HbeqPartBlock. rewrite HbeqBlockPart. simpl.
    destruct (beqAddr blockToFree (CPaddr (addr + sh1offset))) eqn:HbeqBlockSh1Bis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Bis. rewrite HbeqBlockSh1Bis in *.
      destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HbeqSceBlock. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    simpl. destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (addr + sh1offset))) eqn:HbeqSceSh1Bis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceSh1Bis. rewrite HbeqSceSh1Bis in *.
      destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite beqAddrFalse in *. rewrite HbeqSh1Sce. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (addr + sh1offset))) eqn:HbeqSh1s.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1s. exfalso. rewrite <-beqAddrFalse in *.
      apply CPaddrAddEq in HbeqSh1s; trivial. congruence.
    }
    rewrite HbeqBlockSh1. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockSh1Bis. rewrite HbeqPartSh1. simpl. rewrite HbeqPartSh1Bis.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    destruct (beqAddr pd (CPaddr (addr + scoffset))) eqn:HbeqPartSceBis.
    { rewrite <-DTL.beqAddrTrue in HbeqPartSceBis. subst pd. rewrite HlookupParts0 in *. congruence. }
    rewrite beqAddrFalse in *. rewrite HbeqBlockPart. simpl.
    destruct (beqAddr blockToFree (CPaddr (addr + scoffset))) eqn:HbeqBlockSceBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSceBis. rewrite HbeqBlockSceBis in *.
      destruct (lookup (CPaddr (addr + scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HbeqScePart. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    simpl. destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (addr + scoffset))) eqn:HbeqSces.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSces. exfalso. apply CPaddrAddEq in HbeqSces; trivial. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite beqAddrFalse in *. rewrite HbeqSh1Block. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (addr + scoffset))) eqn:HbeqSh1SceBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1SceBis. rewrite HbeqSh1SceBis in *.
      destruct (lookup (CPaddr (addr + scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HbeqBlockSce. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockSceBis. rewrite HbeqPartSce. simpl. rewrite HbeqPartSceBis.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END freeSlotsListIsFreeSlot *)
}

split.
{ (* BEGIN DisjointFreeSlotsLists s *)
  assert(Hcons0: DisjointFreeSlotsLists s0) by (unfold cons1Free in *; intuition).
  intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
  assert(Hpart1IsPDTs0: isPDT part1 s0).
  {
    unfold isPDT in *. rewrite Hs in Hpart1IsPDT. rewrite Hs6 in Hpart1IsPDT. simpl in *.
    destruct (beqAddr pd part1) eqn:HbeqPartsBis.
    - rewrite <-DTL.beqAddrTrue in HbeqPartsBis. subst pd. rewrite HlookupParts0. trivial.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in Hpart1IsPDT. simpl in *.
      destruct (beqAddr blockToFree part1) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in Hpart1IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) part1) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in Hpart1IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) part1) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in Hpart1IsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in Hpart1IsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartsBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(Hpart2IsPDTs0: isPDT part2 s0).
  {
    unfold isPDT in *. rewrite Hs in Hpart2IsPDT. rewrite Hs6 in Hpart2IsPDT. simpl in *.
    destruct (beqAddr pd part2) eqn:HbeqPartsBis.
    - rewrite <-DTL.beqAddrTrue in HbeqPartsBis. subst pd. rewrite HlookupParts0. trivial.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in Hpart2IsPDT. simpl in *.
      destruct (beqAddr blockToFree part2) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in Hpart2IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) part2) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in Hpart2IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) part2) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in Hpart2IsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in Hpart2IsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartsBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts). destruct (beqAddr pd part1) eqn:HbeqPdPart1.
  - rewrite <-DTL.beqAddrTrue in HbeqPdPart1. subst part1. rewrite HgetFreeEqPdss0. rewrite beqAddrFalse in *.
    rewrite HgetFreeEqss0NotPd; trivial.
    destruct Hcons0 as [optFreeList1 [optFreeList2 (Hlist1 & Hwell1 & Hlist2 & Hwell2 & Hdisjoint)]].
    subst optFreeList1. exists (SomePaddr blockToFree :: getFreeSlotsList pd s0). exists optFreeList2. simpl.
    split; trivial. split; trivial. split; trivial. split; trivial. intros addr HaddrInFree1. simpl in *.
    destruct HaddrInFree1 as [HaddrIsBlock | HaddrInFree1Rec].
    + subst addr. contradict HblockIsNotFree.
      assert(HfreeSlots: freeSlotsListIsFreeSlot s0) by (unfold cons1Free in *; intuition).
      assert(HeqFree: optFreeList2 = getFreeSlotsList part2 s0
        /\ wellFormedFreeSlotsList optFreeList2 <> False) by (split; trivial).
      specialize(HfreeSlots part2 blockToFree optFreeList2 (filterOptionPaddr optFreeList2)).
      rewrite <-beqAddrFalse in *. apply HfreeSlots; auto.
    + apply Hdisjoint; trivial.
  - destruct (beqAddr pd part2) eqn:HbeqPdPart2.
    + rewrite <-DTL.beqAddrTrue in HbeqPdPart2. subst part2. rewrite HgetFreeEqPdss0. rewrite beqAddrFalse in *.
      rewrite HgetFreeEqss0NotPd; trivial.
      destruct Hcons0 as [optFreeList1 [optFreeList2 (Hlist1 & Hwell1 & Hlist2 & Hwell2 & Hdisjoint)]].
      subst optFreeList2. exists optFreeList1. exists (SomePaddr blockToFree :: getFreeSlotsList pd s0). simpl.
      split; trivial. split; trivial. split; trivial. split; trivial. intros addr HaddrInFree1. simpl.
      apply Classical_Prop.and_not_or. specialize(Hdisjoint addr HaddrInFree1). split; trivial. intro Hcontra.
      subst addr. contradict HblockIsNotFree.
      assert(HfreeSlots: freeSlotsListIsFreeSlot s0) by (unfold cons1Free in *; intuition).
      assert(HeqFree: optFreeList1 = getFreeSlotsList part1 s0
        /\ wellFormedFreeSlotsList optFreeList1 <> False) by (split; trivial).
      specialize(HfreeSlots part1 blockToFree optFreeList1 (filterOptionPaddr optFreeList1)).
      rewrite <-beqAddrFalse in *. apply HfreeSlots; auto.
    + rewrite HgetFreeEqss0NotPd; trivial. rewrite HgetFreeEqss0NotPd; trivial.
  (* END DisjointFreeSlotsLists *)
}

split.
{ (* BEGIN inclFreeSlotsBlockEntries s *)
  assert(Hcons0: inclFreeSlotsBlockEntries s0) by (unfold cons1Free in *; intuition).
  intros partition HpartIsPDT.
  assert(HpartIsPDTs2s0: isPDT partition s2 /\ isPDT partition s0).
  {
    unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs6 in HpartIsPDT. simpl in *.
    destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. rewrite HlookupParts0. rewrite Hs2. rewrite Hs1. simpl.
      rewrite HbeqBlockPart. rewrite HbeqPartBlock. simpl. rewrite beqAddrTrue. auto.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HpartIsPDT. simpl in *.
      destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      rewrite Hs2 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  destruct HpartIsPDTs2s0 as (HpartIsPDTs2 & HpartIsPDTs0). specialize(Hcons0 partition HpartIsPDTs0).
  rewrite HgetKSEntriesEqss0; trivial. destruct (beqAddr pd partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HgetFreeEqPdss0. intros addr HaddrInFree.
    simpl in HaddrInFree. destruct HaddrInFree as [HaddrIsBlock | HaddrInFreeRec]; try(apply Hcons0; assumption).
    unfold getMappedBlocks in *. apply InFilterPresentInList in HblockToFMappeds0. subst addr.
    apply optionIsInFilter in HblockToFMappeds0. assumption.
  - rewrite HgetFreeEqss0NotPd; assumption.
  (* END inclFreeSlotsBlockEntries *)
}

split.
{ (* BEGIN DisjointKSEntries s *)
  assert(Hcons0: DisjointKSEntries s0) by (unfold cons1Free in *; intuition).
  intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
  assert(Hpart1IsPDTs2s0: isPDT part1 s2 /\ isPDT part1 s0).
  {
    unfold isPDT in *. rewrite Hs in Hpart1IsPDT. rewrite Hs6 in Hpart1IsPDT. simpl in *.
    destruct (beqAddr pd part1) eqn:HbeqParts1.
    - rewrite <-DTL.beqAddrTrue in HbeqParts1. subst pd. rewrite HlookupParts0. rewrite Hs2. rewrite Hs1. simpl.
      rewrite HbeqBlockPart. rewrite HbeqPartBlock. simpl. rewrite beqAddrTrue. auto.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in Hpart1IsPDT. simpl in *.
      destruct (beqAddr blockToFree part1) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in Hpart1IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) part1) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in Hpart1IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) part1) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      rewrite Hs2 in Hpart1IsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in Hpart1IsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts1 in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(Hpart2IsPDTs2s0: isPDT part2 s2 /\ isPDT part2 s0).
  {
    unfold isPDT in *. rewrite Hs in Hpart2IsPDT. rewrite Hs6 in Hpart2IsPDT. simpl in *.
    destruct (beqAddr pd part2) eqn:HbeqParts2.
    - rewrite <-DTL.beqAddrTrue in HbeqParts2. subst pd. rewrite HlookupParts0. rewrite Hs2. rewrite Hs1. simpl.
      rewrite HbeqBlockPart. rewrite HbeqPartBlock. simpl. rewrite beqAddrTrue. auto.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in Hpart2IsPDT. simpl in *.
      destruct (beqAddr blockToFree part2) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in Hpart2IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) part2) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in Hpart2IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) part2) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      rewrite Hs2 in Hpart2IsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in Hpart2IsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts2 in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  destruct Hpart1IsPDTs2s0 as (Hpart1IsPDTs2 & Hpart1IsPDTs0).
  destruct Hpart2IsPDTs2s0 as (Hpart2IsPDTs2 & Hpart2IsPDTs0). rewrite HgetKSEntriesEqss0; trivial.
  specialize(Hcons0 part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts). rewrite HgetKSEntriesEqss0; assumption.
  (* END DisjointKSEntries *)
}

split.
{ (* BEGIN noDupPartitionTree s *)
  assert(Hcons0: noDupPartitionTree s0) by (unfold cons1Free in *; intuition). unfold noDupPartitionTree.
  rewrite HgetPartsEqs. assumption.
  (* END noDupPartitionTree *)
}

split.
{ (* BEGIN isParent s *)
  assert(Hcons0: isParent s0) by (unfold cons1Free in *; intuition).
  intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEqs in *.
  assert(isPDT pdparent s1).
  { apply partitionsArePDT; try(rewrite HgetPartsEqs1); unfold cons1Free in *; intuition. }
  rewrite HgetChildrenEq in HpartIsChild; trivial. specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild).
  unfold pdentryParent in *. rewrite Hs. rewrite Hs6. rewrite Hs5. rewrite Hs4. rewrite Hs3. rewrite Hs2. rewrite Hs1.
  simpl. destruct (beqAddr pd partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupParts0 in *. rewrite Hpdentry3. simpl.
    rewrite Hpdentry2. simpl. rewrite Hpdentry1. auto.
  - rewrite beqAddrTrue. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. simpl.
    destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis.
    { rewrite <-DTL.beqAddrTrue in HbeqBlockPartBis. subst partition. rewrite HlookupBlockToF in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite beqAddrFalse in *.
    rewrite HbeqSceBlock. rewrite HbeqSh1Sce. rewrite HbeqBlockSh1. rewrite HbeqPartBlock. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqScePartBis. subst partition.
      destruct (lookup (CPaddr (blockToFree+scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HbeqSh1Block. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1PartBis. subst partition.
      destruct (lookup (CPaddr (blockToFree+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HbeqBlockSce. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis. rewrite HbeqPartSh1. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. simpl. rewrite beqAddrFalse in *. rewrite HbeqParts.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END isParent *)
}

split.
{ (* BEGIN isChild s *)
  assert(Hcons0: isChild s0) by (unfold cons1Free in *; intuition).
  intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEqs in *.
  assert(HparentIsParents0: pdentryParent partition pdparent s0).
  {
    unfold pdentryParent in *. rewrite Hs in HparentIsParent. rewrite Hs6 in HparentIsParent.
    rewrite Hs5 in HparentIsParent. rewrite Hs4 in HparentIsParent. rewrite Hs3 in HparentIsParent.
    rewrite Hs2 in HparentIsParent. rewrite Hs1 in HparentIsParent. simpl in *.
    destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupParts0. subst pdparent.
      rewrite Hpdentry3. simpl. rewrite Hpdentry2. rewrite Hpdentry1. reflexivity.
    - rewrite beqAddrTrue in *. rewrite HbeqBlockPart in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in *.
      destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqSceBlock in *. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite HbeqSh1Sce in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqBlockSh1 in *. simpl in *. rewrite HbeqBlockPartBis in *.
      rewrite HbeqPartBlock in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in *. rewrite beqAddrFalse in *.
      rewrite HbeqParts in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition pdparent HpartIsPart HparentIsParents0 HbeqPartRoot).
  assert(HparentIsPDTs0: isPDT pdparent s0).
  {
    unfold getChildren in *. unfold getMappedBlocks in Hcons0. unfold isPDT.
    destruct (lookup pdparent (memory s0) beqAddr); try(simpl in *; congruence).
    destruct v; try(simpl in *; congruence). trivial.
  }
  rewrite HgetChildrenEq; trivial. unfold isPDT in *. rewrite Hs1. simpl.
  destruct (beqAddr pd pdparent) eqn:HbeqParts; trivial. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END isChild *)
}

split.
{ (* BEGIN noDupKSEntriesList s *)
  intros partition HpartIsPDT. assert(HpartIsPDTs2: isPDT partition s2).
  {
    unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs6 in HpartIsPDT. rewrite Hs5 in HpartIsPDT.
    rewrite Hs4 in HpartIsPDT. rewrite Hs3 in HpartIsPDT. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. assumption.
    - rewrite beqAddrTrue in *. rewrite HbeqBlockPart in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in *.
      destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite beqAddrFalse in *. rewrite HbeqSceBlock in *. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite HbeqSh1Sce in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  rewrite HgetKSEntriesEqss0; trivial. rewrite <-HgetKSEntriesEqs1s0. unfold isPDT in HpartIsPDTs2.
  rewrite Hs2 in HpartIsPDTs2. simpl in *.
  destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(HnoDupKSs1 partition HpartIsPDTs2). assumption.
  (* END noDupKSEntriesList *)
}

split.
{ (* BEGIN noDupMappedBlocksList s *)
  assert(Hcons0: noDupMappedBlocksList s0) by (unfold cons1Free in *; intuition). intros partition HpartIsPDT.
  assert(HpartIsPDTs2: isPDT partition s2).
  {
    unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs6 in HpartIsPDT. simpl in *.
    destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. rewrite Hs2. rewrite Hs1. simpl. rewrite HbeqBlockPart.
      rewrite HbeqPartBlock. simpl. rewrite beqAddrTrue. trivial.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HpartIsPDT. simpl in *.
      destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HpartIsPDTs0: isPDT partition s0).
  {
    unfold isPDT in *. rewrite Hs2 in HpartIsPDTs2. simpl in *.
    destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HpartIsPDTs2. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. rewrite HlookupParts0. trivial.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 partition HpartIsPDTs0). destruct (beqAddr pd partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. specialize(HgetMappedBPdss0 blockToFree).
    destruct HgetMappedBPdss0 as (_ & _ & Hres). apply Hres. assumption.
  - rewrite <-beqAddrFalse in *. rewrite HgetMappedBEqss0; trivial.
  (* END noDupMappedBlocksList *)
}

split.
{ (* BEGIN wellFormedBlock s *)
  assert(Hcons0: wellFormedBlock s0) by (unfold cons1Free in *; intuition).
  intros block startaddr endaddr HPflag HstartBlock HendBlock. unfold bentryPFlag in *. unfold bentryStartAddr in *.
  unfold bentryEndAddr in *. rewrite Hs in HPflag. rewrite Hs in HstartBlock. rewrite Hs in HendBlock.
  rewrite Hs6 in HPflag. rewrite Hs6 in HstartBlock. rewrite Hs6 in HendBlock. simpl in *.
  destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HstartBlock.
  rewrite Hs5 in HPflag. rewrite Hs5 in HendBlock. simpl in *.
  destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in *. simpl in *. rewrite HnewB in *. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HPflag.
  rewrite Hs4 in HstartBlock. rewrite Hs4 in HendBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPflag.
  rewrite Hs3 in HstartBlock. rewrite Hs3 in HendBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HPflag.
  rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPflag. rewrite Hs1 in HstartBlock.
  rewrite Hs1 in HendBlock. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartBlockBis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
  (* END wellFormedBlock *)
}

split.
{ (* BEGIN parentOfPartitionIsPartition s *)
  intros partition pdentryPart HlookupPart.
  assert(HlookupPartBiss6: exists pdentryParts0,
    lookup partition (memory s6) beqAddr = Some (PDT pdentryParts0)
    /\ parent pdentryParts0 = parent pdentryPart).
  {
    rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
      subst pdentryPart. exists pdentry2. rewrite Hpdentry3. simpl. auto.
    - rewrite <-beqAddrFalse in *. exists pdentryPart. split; trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  destruct HlookupPartBiss6 as [pdentryParts6 (HlookupPartBiss6 & HparentsEq)]. rewrite <-HparentsEq in *.
  specialize(HparentOfParts6 partition pdentryParts6 HlookupPartBiss6).
  destruct HparentOfParts6 as (HparentIsPart & Hother). split; trivial. intro HbeqPartRoot.
  specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
  rewrite HgetPartsEqs. rewrite <-HgetPartsEqs6. split; trivial. rewrite Hs. simpl.
  destruct (beqAddr pd (parent pdentryParts6)) eqn:HbeqPdParent.
  - exists pdentry3. reflexivity.
  - exists parentEntry. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END parentOfPartitionIsPartition *)
}

split.
{ (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
  assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0) by (unfold cons1Free in *; intuition).
  intros partition nbfreeslots HpartIsPDT HnbFree.
  assert(HpartIsPDTs0: isPDT partition s0).
  {
    unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs6 in HpartIsPDT. simpl in *.
    destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pd. rewrite HlookupParts0. trivial.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs5 in HpartIsPDT. simpl in *.
      destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold pdentryNbFreeSlots in *. rewrite Hs in HnbFree. rewrite Hs6 in HnbFree. simpl in *.
  destruct (beqAddr pd partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite Hpdentry3 in HnbFree. simpl in *.
    subst nbfreeslots. unfold CIndex. destruct (le_dec (nbfreeslots pdentry1 + 1) maxIdx); try(lia).
    rewrite HgetFreeEqPdss0. specialize(Hcons0 pd (nbfreeslots pdentry) HpartIsPDTs0 HnbFrees0).
    destruct Hcons0 as [optFreeList (Hlist & Hwell & HlenList)]. exists ((SomePaddr blockToFree)::optFreeList).
    simpl. rewrite Hpdentry1. simpl. split; try(split); trivial; try(lia). f_equal. assumption.
  - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HnbFree. simpl in *.
    destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs4 in HnbFree. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs3 in HnbFree. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs2 in HnbFree. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HnbFree. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition nbfreeslots HpartIsPDTs0 HnbFree). rewrite beqAddrFalse in *.
    rewrite HgetFreeEqss0NotPd; trivial.
  (* END NbFreeSlotsISNbFreeSlotsInList *)
}

split.
{ (* BEGIN maxNbPrepareIsMaxNbKernels s *)
  assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by (unfold cons1Free in *; intuition).
  intros partition kernList HlistOfKerns. apply HkernListEqss0 in HlistOfKerns.
  specialize(Hcons0 partition kernList HlistOfKerns). assumption.
  (* END maxNbPrepareIsMaxNbKernels *)
}

split.
{ (* BEGIN partitionTreeIsTree s *)
  assert(Hcons0: partitionTreeIsTree s0) by (unfold cons1Free in *; intuition).
  intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
  rewrite HgetPartsEqs in *. assert(HparentIsParent0: pdentryParent child pdparent s0).
  {
    unfold pdentryParent in *. rewrite Hs in HparentIsParent. rewrite Hs6 in HparentIsParent. simpl in *.
    destruct (beqAddr pd child) eqn:HbeqPartChild.
    - rewrite <-DTL.beqAddrTrue in HbeqPartChild. subst child. rewrite HlookupParts0.
      rewrite Hpdentry3 in HparentIsParent. simpl in *. rewrite Hpdentry2 in HparentIsParent. simpl in *.
      rewrite Hpdentry1 in HparentIsParent. simpl in *. assumption.
    - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HparentIsParent. simpl in *.
      destruct (beqAddr blockToFree child) eqn:HbeqBlockChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HparentIsParent. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) child) eqn:HbeqSceChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HparentIsParent. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) child) eqn:HbeqSh1Child; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HparentIsParent. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockChild in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HparentIsParent. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartChild in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  apply HparentsListEqss0 in HparentsList. specialize(Hcons0 child pdparent parentsList). apply Hcons0; assumption.
  (* END partitionTreeIsTree *)
}

split.
{ (* BEGIN kernelEntriesAreValid s *)
  assert(Hcons0: kernelEntriesAreValid s0) by (unfold cons1Free in *; intuition). intros kernel idx HkernIsKS Hidx.
  assert(HkernIsKSs0: isKS kernel s0).
  {
    unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs6 in HkernIsKS. simpl in *.
    destruct (beqAddr pd kernel) eqn:HbeqPartKern; try(exfalso; congruence). rewrite beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HkernIsKS. simpl in *.
    destruct (beqAddr blockToFree kernel) eqn:HbeqBlocks.
    - rewrite HnewB2 in HkernIsKS. simpl in *. rewrite HnewB in HkernIsKS. simpl in *. subst blockToFreeIdx.
      rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst kernel. unfold bentryBlockIndex in *.
      rewrite HlookupBlockEqs1s0 in *. rewrite HlookupBlockToF in *. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) kernel) eqn:HbeqSh1Kern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HkernIsKS. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HkernIsKS. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartKern in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 kernel idx HkernIsKSs0 Hidx). unfold isBE in *. rewrite Hs. rewrite Hs6. simpl.
  destruct (beqAddr pd (CPaddr (kernel + idx))) eqn:HbeqPartIdx.
  { rewrite <-DTL.beqAddrTrue in HbeqPartIdx. subst pd. rewrite HlookupParts0 in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
  destruct (beqAddr blockToFree (CPaddr (kernel + idx))) eqn:HbeqBlockIdx; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) (CPaddr (kernel + idx))) eqn:HbeqSceIdx.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceIdx. rewrite HbeqSceIdx in *.
    destruct (lookup (CPaddr (kernel + idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (kernel + idx))) eqn:HbeqSh1Idx.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1Idx. rewrite HbeqSh1Idx in *.
    destruct (lookup (CPaddr (kernel + idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  rewrite beqAddrFalse in *. rewrite HbeqBlockIdx. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartIdx. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END kernelEntriesAreValid *)
}

split.
{ (* BEGIN nextKernelIsValid s *)
  assert(Hcons0: nextKernelIsValid s0) by (unfold cons1Free in *; intuition). intros kernel HkernIsKS.
  assert(HkernIsKSs0: isKS kernel s0).
  {
    unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs6 in HkernIsKS. simpl in *.
    destruct (beqAddr pd kernel) eqn:HbeqPartKern; try(exfalso; congruence). rewrite beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HkernIsKS. simpl in *.
    destruct (beqAddr blockToFree kernel) eqn:HbeqBlocks.
    - rewrite HnewB2 in HkernIsKS. simpl in *. rewrite HnewB in HkernIsKS. simpl in *. subst blockToFreeIdx.
      rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst kernel. unfold bentryBlockIndex in *.
      rewrite HlookupBlockEqs1s0 in *. rewrite HlookupBlockToF in *. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) kernel) eqn:HbeqSh1Kern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HkernIsKS. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HkernIsKS. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartKern in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 kernel HkernIsKSs0). destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNextA & HnextIsKern)]).
  split; trivial. exists nextAddr. split.
  - intro Hp. specialize(HlookupNextA Hp). rewrite Hs. rewrite Hs6. simpl.
    destruct (beqAddr pd {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqPartNextA.
    { rewrite <-DTL.beqAddrTrue in HbeqPartNextA. subst pd. exfalso; congruence. }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
    destruct (beqAddr blockToFree {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqBlockNextA.
    { rewrite <-DTL.beqAddrTrue in HbeqBlockNextA. subst blockToFree. exfalso; congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqSceNextA.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceNextA. rewrite HbeqSceNextA in *. rewrite HlookupNextA in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqSh1NextA.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1NextA. rewrite HbeqSh1NextA in *. rewrite HlookupNextA in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlockNextA. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqPartNextA. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - destruct HnextIsKern as [HnextIsKS | HkernIsNull]; try(right; assumption). left. unfold isKS in *. rewrite Hs.
    rewrite Hs6. simpl. destruct (beqAddr pd nextAddr) eqn:HbeqPartNext.
    { rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst nextAddr. rewrite HlookupParts0 in *. congruence. }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
    destruct (beqAddr blockToFree nextAddr) eqn:HbeqBlockNext.
    + rewrite <-DTL.beqAddrTrue in HbeqBlockNext. subst nextAddr. rewrite HnewB2. simpl. rewrite HnewB. simpl.
      unfold bentryBlockIndex in *. rewrite HlookupBlockEqs1s0 in *. rewrite HlookupBlockToF in *.
      subst blockToFreeIdx. assumption.
    + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) nextAddr) eqn:HbeqSceNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceNext. subst nextAddr.
        destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) nextAddr) eqn:HbeqSh1Next.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Next. subst nextAddr.
        destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqBlockNext. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqPartNext. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END nextKernelIsValid *)
}

split.
{ (* BEGIN noDupListOfKerns s *)
  assert(Hcons0: noDupListOfKerns s0) by (unfold cons1Free in *; intuition).
  intros partition kernList HlistOfKerns. apply HkernListEqss0 in HlistOfKerns. specialize(Hcons0 partition kernList).
  apply Hcons0; assumption.
  (* END noDupListOfKerns *)
}

split.
{ (* BEGIN MPUsizeIsBelowMax s *)
  assert(Hcons0: MPUsizeIsBelowMax s0) by (unfold cons1Free in *; intuition). intros partition MPUlist HMPU.
  unfold pdentryMPU in *. rewrite Hs in HMPU. rewrite Hs6 in HMPU. simpl in *.
  destruct (beqAddr pd partition) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite Hpdentry3 in HMPU. simpl in *.
    rewrite Hpdentry2 in HMPU. simpl in *. rewrite Hpdentry1 in HMPU. simpl in *.
    specialize(Hcons0 pd realMPU HpdMPUs0). subst MPUlist.
    pose proof (removeBlockFromPhysicalMPUAuxLenEq blockToFree realMPU) as HlebLens. lia.
  - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HMPU. simpl in *.
    destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HMPU.
    simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HMPU.
    simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HMPU.
    simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HMPU. simpl in *.
    rewrite beqAddrFalse in *. rewrite HbeqParts in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 partition MPUlist HMPU).
    assumption.
  (* END MPUsizeIsBelowMax *)
}

split.
{ (* BEGIN blocksAddressesTypes s *)
  assert(Hcons0: blocksAddressesTypes s0) by (unfold cons1Free in *; intuition).
  intros block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock. unfold bentryStartAddr in *.
  unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartBlock. rewrite Hs in HendBlock.
  rewrite Hs in HPflagBlock. rewrite Hs6 in HstartBlock. rewrite Hs6 in HendBlock. rewrite Hs6 in HPflagBlock.
  simpl in *. destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HstartBlock.
  rewrite Hs5 in HendBlock. rewrite Hs5 in HPflagBlock. simpl in *.
  destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in HPflagBlock. simpl in *. rewrite HnewB in HPflagBlock. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HstartBlock. rewrite Hs4 in HendBlock. rewrite Hs4 in HPflagBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HstartBlock. rewrite Hs3 in HendBlock. rewrite Hs3 in HPflagBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. rewrite Hs2 in HPflagBlock. simpl in *.
  rewrite beqAddrFalse in *. rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HstartBlock.
  rewrite Hs1 in HendBlock. rewrite Hs1 in HPflagBlock. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  unfold sh1entryPDchild in *. rewrite Hs in HPDchildBlock. rewrite Hs6 in HPDchildBlock. simpl in *.
  destruct (beqAddr pd (CPaddr (block + sh1offset))) eqn:HbeqPartSh1Bis; try(exfalso; congruence).
  rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDchildBlock. simpl in *.
  destruct (beqAddr blockToFree (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HPDchildBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree+scoffset)) (CPaddr (block+sh1offset))) eqn:HbeqSceSh1Bis;
    try(exfalso; congruence). rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPDchildBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s.
  { rewrite <-DTL.beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HPDchildBlock. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockSh1Bis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs1 in HPDchildBlock. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartSh1Bis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock).
  destruct Hcons0 as [(HKS & Hincl) | [(HPDT & Hincl) | Hnone]].
  - left. split.
    + unfold isKS in *. rewrite Hs. rewrite Hs6. simpl. destruct (beqAddr pd startaddr) eqn:HbeqPartStart.
      { rewrite <-DTL.beqAddrTrue in HbeqPartStart. subst pd. rewrite HlookupParts0 in *. congruence. }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
      destruct (beqAddr blockToFree startaddr) eqn:HbeqBlockStart.
      * rewrite <-DTL.beqAddrTrue in HbeqBlockStart. subst startaddr. rewrite HnewB2. simpl. rewrite HnewB. simpl.
        unfold bentryBlockIndex in *. rewrite HlookupBlockEqs1s0 in *. rewrite HlookupBlockToF in *.
        subst blockToFreeIdx. assumption.
      * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4.
        simpl. destruct (beqAddr (CPaddr (blockToFree + scoffset)) startaddr) eqn:HbeqSceStart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceStart. subst startaddr.
          destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3.
        simpl. destruct (beqAddr (CPaddr (blockToFree + sh1offset)) startaddr) eqn:HbeqSh1Start.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Start. subst startaddr.
          destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
        simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockStart. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqPartStart. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    + intros addr HaddrInBlock. specialize(Hincl addr HaddrInBlock).
      destruct Hincl as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
      * left. unfold isBE in *. rewrite Hs. rewrite Hs6. simpl. destruct (beqAddr pd addr) eqn:HbeqPartAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr; trivial.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *.
          destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *.
          destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      * right. left. unfold isSHE in *. rewrite Hs. rewrite Hs6. simpl. destruct (beqAddr pd addr) eqn:HbeqPartAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockToF in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *.
          destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr; trivial.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      * right. right. left. unfold isSCE in *. rewrite Hs. rewrite Hs6. simpl.
        destruct (beqAddr pd addr) eqn:HbeqPartAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockToF in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr; trivial.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *.
          destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      * right. right. right. left. unfold isPADDR in *. rewrite Hs. rewrite Hs6. simpl.
        destruct (beqAddr pd addr) eqn:HbeqPartAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockToF in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *.
          destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *.
          destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      * right. right. right. right. rewrite Hs. rewrite Hs6. simpl.
        destruct (beqAddr pd addr) eqn:HbeqPartAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
        destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockToF in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
        destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite Hnone in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite Hnone in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
        rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - right. left. split.
    + unfold isPDT in *. rewrite Hs. rewrite Hs6. simpl. destruct (beqAddr pd startaddr) eqn:HbeqPartStart; trivial.
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
      destruct (beqAddr blockToFree startaddr) eqn:HbeqBlockStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockStart. subst startaddr. rewrite HlookupBlockToF in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4.
      simpl. destruct (beqAddr (CPaddr (blockToFree + scoffset)) startaddr) eqn:HbeqSceStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceStart. subst startaddr.
        destruct (lookup (CPaddr (blockToFree + scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3.
      simpl. destruct (beqAddr (CPaddr (blockToFree + sh1offset)) startaddr) eqn:HbeqSh1Start.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Start. subst startaddr.
        destruct (lookup (CPaddr (blockToFree + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
      simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockStart. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqPartStart. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    + intros addr HaddrInBlock. specialize(Hincl addr HaddrInBlock). rewrite Hs. rewrite Hs6. simpl.
      destruct (beqAddr pd addr) eqn:HbeqPartAddr.
      { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
      destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr.
      { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockToF in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite Hincl in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite Hincl in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  - right. right. intros addr HaddrInBlock. specialize(Hnone addr HaddrInBlock). rewrite Hs. rewrite Hs6. simpl.
    destruct (beqAddr pd addr) eqn:HbeqPartAddr.
    { rewrite <-DTL.beqAddrTrue in HbeqPartAddr. subst addr. rewrite HlookupParts0 in *. congruence. }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
    destruct (beqAddr blockToFree addr) eqn:HbeqBlockAddr.
    { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockToF in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) addr) eqn:HbeqSceAddr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceAddr. rewrite HbeqSceAddr in *. rewrite Hnone in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) addr) eqn:HbeqSh1Addr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite Hnone in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in *. rewrite HbeqBlockAddr. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  (* END blocksAddressesTypes *)
}

split.
{ (* BEGIN notPDTIfNotPDflag s *)
  assert(Hcons0: notPDTIfNotPDflag s0) by (unfold cons1Free in *; intuition).
  intros block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild. unfold bentryStartAddr in *.
  unfold sh1entryAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartBlock. rewrite Hs6 in HstartBlock.
  rewrite Hs in HPflag. rewrite Hs in Hsh1. rewrite Hs6 in HPflag. rewrite Hs6 in Hsh1. simpl in *.
  destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPflag. rewrite Hs5 in Hsh1.
  rewrite Hs5 in HstartBlock. simpl in *. destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in HPflag. simpl in *. rewrite HnewB in HPflag. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HPflag.
  rewrite Hs4 in HstartBlock. rewrite Hs4 in Hsh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPflag.
  rewrite Hs3 in HstartBlock. rewrite Hs3 in Hsh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HPflag.
  rewrite Hs2 in HstartBlock. rewrite Hs2 in Hsh1. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPflag.
  rewrite Hs1 in HstartBlock. rewrite Hs1 in Hsh1. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
  unfold sh1entryPDflag in *. rewrite Hs in HPDchild. rewrite Hs in HPDflag. rewrite Hs6 in HPDflag.
  rewrite Hs6 in HPDchild. simpl in *.
  destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDflag. rewrite Hs5 in HPDchild.
  simpl in *. destruct (beqAddr blockToFree sh1entryaddr) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HPDflag. rewrite Hs4 in HPDchild. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) sh1entryaddr) eqn:HbeqSceSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HPDflag. rewrite Hs3 in HPDchild. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1s. subst sh1entryaddr. exfalso.
    destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    apply CPaddrAddEq in Hsh1; trivial. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HPDflag. rewrite Hs2 in HPDchild. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqBlockSh1Bis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPDflag. rewrite Hs1 in HPDchild.
  simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartSh1Bis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild). contradict Hcons0.
  unfold isPDT in *. rewrite Hs in Hcons0. rewrite Hs6 in Hcons0. simpl in *.
  destruct (beqAddr pd startaddr) eqn:HbeqPartStart.
  - rewrite <-DTL.beqAddrTrue in HbeqPartStart. subst pd. rewrite HlookupParts0. trivial.
  - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in Hcons0. simpl in *.
    destruct (beqAddr blockToFree startaddr) eqn:HbeqBlockStart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs4 in Hcons0. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + scoffset)) startaddr) eqn:HbeqSceStart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs3 in Hcons0. simpl in *.
    destruct (beqAddr (CPaddr (blockToFree + sh1offset)) startaddr) eqn:HbeqSh1Start; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs2 in Hcons0. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockStart in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in Hcons0. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartStart in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END notPDTIfNotPDflag *)
}

split.
{ (* BEGIN nextKernAddrIsInSameBlock s *)
  assert(Hcons0: nextKernAddrIsInSameBlock s0) by (unfold cons1Free in *; intuition).
  intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock HkernIsKS.
  unfold bentryStartAddr in *.
  unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartBlock. rewrite Hs in HendBlock.
  rewrite Hs in HPflagBlock. rewrite Hs6 in HstartBlock. rewrite Hs6 in HendBlock. rewrite Hs6 in HPflagBlock.
  simpl in *. destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HstartBlock.
  rewrite Hs5 in HendBlock. rewrite Hs5 in HPflagBlock. simpl in *.
  destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in HPflagBlock. simpl in *. rewrite HnewB in HPflagBlock. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HstartBlock. rewrite Hs4 in HendBlock. rewrite Hs4 in HPflagBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HstartBlock. rewrite Hs3 in HendBlock. rewrite Hs3 in HPflagBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. rewrite Hs2 in HPflagBlock. simpl in *.
  rewrite beqAddrFalse in *. rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HstartBlock.
  rewrite Hs1 in HendBlock. rewrite Hs1 in HPflagBlock. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  unfold sh1entryPDchild in *. rewrite Hs in HPDchildBlock. rewrite Hs6 in HPDchildBlock. simpl in *.
  destruct (beqAddr pd (CPaddr (block + sh1offset))) eqn:HbeqPartSh1Bis; try(exfalso; congruence).
  rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDchildBlock. simpl in *.
  destruct (beqAddr blockToFree (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HPDchildBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree+scoffset)) (CPaddr (block+sh1offset))) eqn:HbeqSceSh1Bis;
    try(exfalso; congruence). rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPDchildBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s.
  { rewrite <-DTL.beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HPDchildBlock. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockSh1Bis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs1 in HPDchildBlock. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartSh1Bis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  assert(HkernIsKSs0: isKS kernel s0).
  {
    unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs6 in HkernIsKS. simpl in *.
    destruct (beqAddr pd kernel) eqn:HbeqPartKern; try(exfalso; congruence). rewrite beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HkernIsKS. simpl in *.
    destruct (beqAddr blockToFree kernel) eqn:HbeqBlockKern.
    - rewrite HnewB2 in HkernIsKS. simpl in *. rewrite HnewB in HkernIsKS. simpl in *. subst blockToFreeIdx.
      rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. unfold bentryBlockIndex in *.
      rewrite HlookupBlockEqs1s0 in *. rewrite HlookupBlockToF in *. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) kernel) eqn:HbeqSceKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) kernel) eqn:HbeqSh1Kern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HkernIsKS. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockKern in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HkernIsKS. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartKern in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  specialize(Hcons0 block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock HkernIsKSs0).
  assumption.
  (* END nextKernAddrIsInSameBlock *)
}

split.
{ (* BEGIN blockBelongsToAPart s *)
  assert(Hcons0: blockBelongsToAPart s0) by (unfold cons1Free in *; intuition). intros block HPflagBlock.
  rewrite HgetPartsEqs. unfold bentryPFlag in *. rewrite Hs in HPflagBlock. rewrite Hs6 in HPflagBlock. simpl in *.
  destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPflagBlock. simpl in *.
  destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in HPflagBlock. simpl in *. rewrite HnewB in HPflagBlock. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HPflagBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HPflagBlock. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HPflagBlock. simpl in *.
  rewrite beqAddrFalse in *. rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs1 in HPflagBlock. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 block HPflagBlock).
  destruct Hcons0 as [part (HpartIsPart & HblockMapped)]. exists part. split; trivial.
  destruct (beqAddr pd part) eqn:HbeqParts.
  - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. specialize(HgetMappedBPdss0 block).
    destruct HgetMappedBPdss0 as (Hres & _). specialize(Hres HblockMapped).
    destruct Hres as [Hcontra | Hres]; try(exfalso; congruence). assumption.
  - rewrite <-beqAddrFalse in *. rewrite HgetMappedBEqss0; trivial. rewrite <-HgetPartsEqs2 in *.
    apply partitionsArePDT; trivial.
  (* END blockBelongsToAPart *)
}

split.
{ (* BEGIN PDflagMeansNoChild s *)
  assert(Hcons0: PDflagMeansNoChild s0) by (unfold cons1Free in *; intuition).
  intros block HblockIsBE HPDflagBlock. assert(HblockBisIsBEs0: isBE block s0).
  {
    unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs6 in HblockIsBE. simpl in *.
    destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite IL.beqAddrTrue in HblockIsBE.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HblockIsBE. simpl in *.
    destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HblockIsBE. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in HblockIsBE.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HblockIsBE. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartBlockBis in HblockIsBE.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  unfold sh1entryPDchild. unfold sh1entryPDflag in *. rewrite Hs in HPDflagBlock. rewrite Hs6 in HPDflagBlock.
  rewrite Hs. rewrite Hs6. simpl in *.
  destruct (beqAddr pd (CPaddr (block + sh1offset))) eqn:HbeqPartSh1Bis; try(congruence).
  rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDflagBlock. rewrite Hs5.
  simpl in *.
  destruct (beqAddr blockToFree (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HPDflagBlock. rewrite Hs4. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree+scoffset)) (CPaddr (block+sh1offset))) eqn:HbeqSceSh1Bis; try(congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HPDflagBlock. rewrite Hs3. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s; auto.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HPDflagBlock. rewrite Hs2. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockSh1Bis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs1 in HPDflagBlock. rewrite Hs1. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartSh1Bis in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 block HblockBisIsBEs0 HPDflagBlock). assumption.
  (* END PDflagMeansNoChild *)
}

split.
{ (* BEGIN nbPrepareIsNbKern s *)
  assert(Hcons0: nbPrepareIsNbKern s0) by (unfold cons1Free in *; intuition).
  intros partition pdentryPart HlookupPart.
  assert(HlookupPartBiss0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
    /\ structure pdentryParts0 = structure pdentryPart /\ nbprepare pdentryParts0 = nbprepare pdentryPart).
  {
    rewrite Hs in HlookupPart. rewrite Hs6 in HlookupPart. simpl in *. destruct (beqAddr pd partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HpdentriesEq.
      subst pdentryPart. exists pdentry. rewrite Hpdentry3. simpl. rewrite Hpdentry2. simpl. rewrite Hpdentry1. auto.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *. exists pdentryPart. split; auto.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HlookupPart. simpl in *.
      destruct (beqAddr blockToFree partition) eqn:HbeqBlockPartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs4 in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + scoffset)) partition) eqn:HbeqScePartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (blockToFree + sh1offset)) partition) eqn:HbeqSh1PartBis; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupPart. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlockPartBis in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HlookupPart. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqParts in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  destruct HlookupPartBiss0 as [pdentryParts0 (HlookupPartBiss0 & HstructEq & HnbPrepEq)]. rewrite <-HstructEq.
  rewrite <-HnbPrepEq. specialize(Hcons0 partition pdentryParts0 HlookupPartBiss0). rewrite <-Hcons0. f_equal.
  assert(Heqs6: completeListOfKernels (structure pdentryParts0) s
    = completeListOfKernels (structure pdentryParts0) s6).
  { rewrite Hs. apply completeListOfKernelsEqPDT. unfold isPDT. rewrite HlookupParts6. trivial. }
  assert(Heqs5: completeListOfKernels (structure pdentryParts0) s
    = completeListOfKernels (structure pdentryParts0) s5).
  { rewrite Heqs6. rewrite Hs6. apply completeListOfKernelsEqPDT. unfold isPDT. rewrite HlookupParts5. trivial. }
  assert(Heqs4: completeListOfKernels (structure pdentryParts0) s
    = completeListOfKernels (structure pdentryParts0) s4).
  {
    rewrite Heqs5. rewrite Hs5. apply completeListOfKernelsEqBE with emptyBentry; trivial. rewrite HnewB2. auto.
  }
  assert(Heqs3: completeListOfKernels (structure pdentryParts0) s
    = completeListOfKernels (structure pdentryParts0) s3).
  {
    rewrite Heqs4. rewrite Hs4. apply completeListOfKernelsEqSCE. unfold isSCE. rewrite HlookupSceEqs3s0.
    assumption.
  }
  assert(Heqs2: completeListOfKernels (structure pdentryParts0) s
    = completeListOfKernels (structure pdentryParts0) s2).
  {
    rewrite Heqs3. rewrite Hs3. apply completeListOfKernelsEqSHE. unfold isSHE. rewrite HlookupSh1Eqs2s0.
    assumption.
  }
  assert(Heqs1: completeListOfKernels (structure pdentryParts0) s
    = completeListOfKernels (structure pdentryParts0) s1).
  {
    rewrite Heqs2. rewrite Hs2. rewrite <-HlookupBlockEqs1s0 in *. apply completeListOfKernelsEqBE with bentryToF.
    - assumption.
    - rewrite HnewB. simpl. unfold bentryBlockIndex in *. rewrite HlookupBlockToF in *. assumption.
  }
  rewrite Heqs1. rewrite Hs1. apply completeListOfKernelsEqPDT. unfold isPDT. rewrite HlookupParts0. trivial.
 (* END nbPrepareIsNbKern *)
}

split.
{ (* BEGIN pdchildIsPDT s *)
  assert(Hcons0: pdchildIsPDT s0) by (unfold cons1Free in *; intuition).
  intros part block sh1entryaddr idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
  rewrite HgetPartsEqs in *. assert(isPDT part s2).
  { rewrite <-HgetPartsEqs2 in *. apply partitionsArePDT; trivial. }
  assert(HblockMappeds0: In block (getMappedBlocks part s0)).
  {
    destruct (beqAddr pd part) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. specialize(HgetMappedBPdss0 block).
      destruct HgetMappedBPdss0 as (_ & Hres & _). apply Hres; assumption.
    - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBEqss0; assumption.
  }
  assert(isPDT part s1).
  { rewrite <-HgetPartsEqs1 in *. apply partitionsArePDT; trivial. }
  assert(HPflag: bentryPFlag block true s).
  {
    apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag.
    rewrite Hlookup. auto.
  }
  unfold sh1entryAddr in *. unfold bentryPFlag in *. rewrite Hs in HPflag. rewrite Hs in Hsh1. rewrite Hs6 in HPflag.
  rewrite Hs6 in Hsh1. simpl in *.
  destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPflag. rewrite Hs5 in Hsh1.
  simpl in *. destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in HPflag. simpl in *. rewrite HnewB in HPflag. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HPflag.
  rewrite Hs4 in Hsh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPflag.
  rewrite Hs3 in Hsh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HPflag.
  rewrite Hs2 in Hsh1. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPflag.
  rewrite Hs1 in Hsh1. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
  unfold sh1entryInChildLocation in *. rewrite Hs in HPDchild. rewrite Hs6 in HPDchild. simpl in *.
  destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDchild.
  simpl in *. destruct (beqAddr blockToFree sh1entryaddr) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HPDchild. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) sh1entryaddr) eqn:HbeqSceSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HPDchild. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1s. subst sh1entryaddr. exfalso.
    destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    apply CPaddrAddEq in Hsh1; trivial. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HPDchild. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqBlockSh1Bis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPDchild.
  simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartSh1Bis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 part block sh1entryaddr idchild HpartBisIsPart HblockMappeds0 Hsh1 HPDchild HbeqIdChildNull).
  rewrite HgetChildrenEq; trivial.
  (* END pdchildIsPDT *)
}

(*split.*)
{ (* BEGIN childBlockNullIfChildNull s *)
  assert(Hcons0: childBlockNullIfChildNull s0) by (unfold cons1Free in *; intuition).
  intros part block sh1entryaddr HpartBisIsPart HblockMapped Hsh1 HPDchild.
  rewrite HgetPartsEqs in *. assert(isPDT part s2).
  { rewrite <-HgetPartsEqs2 in *. apply partitionsArePDT; trivial. }
  assert(HblockMappeds0: In block (getMappedBlocks part s0)).
  {
    destruct (beqAddr pd part) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. specialize(HgetMappedBPdss0 block).
      destruct HgetMappedBPdss0 as (_ & Hres & _). apply Hres; assumption.
    - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBEqss0; assumption.
  }
  assert(isPDT part s1).
  { rewrite <-HgetPartsEqs1 in *. apply partitionsArePDT; trivial. }
  assert(HPflag: bentryPFlag block true s).
  {
    apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag.
    rewrite Hlookup. auto.
  }
  unfold sh1entryAddr in *. unfold bentryPFlag in *. rewrite Hs in HPflag. rewrite Hs in Hsh1. rewrite Hs6 in HPflag.
  rewrite Hs6 in Hsh1. simpl in *.
  destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPflag. rewrite Hs5 in Hsh1.
  simpl in *. destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in HPflag. simpl in *. rewrite HnewB in HPflag. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in HPflag.
  rewrite Hs4 in Hsh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPflag.
  rewrite Hs3 in Hsh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in HPflag.
  rewrite Hs2 in Hsh1. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPflag.
  rewrite Hs1 in Hsh1. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *. rewrite Hs.
  unfold sh1entryInChildLocation. rewrite Hs6. rewrite Hs in HPDchild. rewrite Hs6 in HPDchild. simpl in *.
  destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDchild. rewrite Hs5.
  simpl in *. destruct (beqAddr blockToFree sh1entryaddr) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HPDchild. rewrite Hs4. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) sh1entryaddr) eqn:HbeqSceSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HPDchild. rewrite Hs3. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1s. subst sh1entryaddr. exfalso.
    destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    apply CPaddrAddEq in Hsh1; trivial. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HPDchild. rewrite Hs2. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqBlockSh1Bis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPDchild. rewrite Hs1.
  simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartSh1Bis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 part block sh1entryaddr HpartBisIsPart HblockMappeds0 Hsh1 HPDchild).
  unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). destruct Hcons0 as (Hcons0 & _). split; trivial. intro. exfalso; congruence.
  (* END pdchildIsPDT *)
}

(*{ (* BEGIN childLocHasSameStart s *)
  assert(Hcons0: childLocHasSameStart s0) by (unfold cons1Free in *; intuition).
  intros part block sh1entryaddr blockChild idchild HpartIsPart HblockMapped Hsh1 HPDchild Hloc HbeqIdChildNull
    HbeqBCNull startaddr Hstart. rewrite HgetPartsEqs in *. assert(isPDT part s2).
  { rewrite <-HgetPartsEqs2 in *. apply partitionsArePDT; trivial. }
  assert(HblockMappeds0: In block (getMappedBlocks part s0)).
  {
    destruct (beqAddr pd part) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. specialize(HgetMappedBPdss0 block).
      destruct HgetMappedBPdss0 as (_ & Hres & _). apply Hres; assumption.
    - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBEqss0; assumption.
  }
  assert(HPflag: bentryPFlag block true s).
  {
    apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag.
    rewrite Hlookup. auto.
  }
  unfold sh1entryAddr in *. unfold bentryStartAddr in *. unfold bentryPFlag in *. rewrite Hs in Hstart.
  rewrite Hs6 in Hstart. rewrite Hs in Hsh1. rewrite Hs6 in Hsh1. rewrite Hs in HPflag. rewrite Hs6 in HPflag.
  simpl in *. destruct (beqAddr pd block) eqn:HbeqPartBlockBis; try(exfalso; congruence). rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in Hstart. rewrite Hs5 in Hsh1.
  rewrite Hs5 in HPflag. simpl in *. destruct (beqAddr blockToFree block) eqn:HbeqBlocks.
  { rewrite HnewB2 in HPflag. simpl in *. rewrite HnewB in HPflag. simpl in *. exfalso; congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs4 in Hstart.
  rewrite Hs4 in Hsh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) block) eqn:HbeqSceBlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hstart.
  rewrite Hs3 in Hsh1. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) block) eqn:HbeqSh1BlockBis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2 in Hstart.
  rewrite Hs2 in Hsh1. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in Hstart.
  rewrite Hs1 in Hsh1. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqPartBlockBis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *. rewrite Hs in HPDchild.
  unfold sh1entryInChildLocationWeak in *. rewrite Hs6 in HPDchild. rewrite Hs in Hloc. rewrite Hs6 in Hloc.
  simpl in *. destruct (beqAddr pd sh1entryaddr) eqn:HbeqPartSh1Bis; try(exfalso; congruence).
  rewrite beqAddrTrue in *.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in HPDchild. rewrite Hs5 in Hloc.
  simpl in *. destruct (beqAddr blockToFree sh1entryaddr) eqn:HbeqBlockSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs4 in HPDchild. rewrite Hs4 in Hloc. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) sh1entryaddr) eqn:HbeqSceSh1Bis; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs3 in HPDchild. rewrite Hs3 in Hloc. simpl in *.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1s. subst sh1entryaddr. exfalso.
    destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    apply CPaddrAddEq in Hsh1; trivial. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  rewrite Hs2 in HPDchild. rewrite Hs2 in Hloc. simpl in *. rewrite beqAddrFalse in *.
  rewrite HbeqBlockSh1Bis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPDchild. rewrite Hs1 in Hloc.
  simpl in *. rewrite beqAddrFalse in *. rewrite HbeqPartSh1Bis in *. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(Hcons0 part block sh1entryaddr blockChild idchild HpartIsPart HblockMappeds0 Hsh1 HPDchild Hloc
    HbeqIdChildNull HbeqBCNull startaddr Hstart). unfold bentryStartAddr in *. rewrite Hs. rewrite Hs6. simpl.
  destruct (beqAddr pd blockChild) eqn:HbeqPartBC.
  { rewrite <-DTL.beqAddrTrue in HbeqPartBC. subst blockChild. rewrite HlookupParts0 in *. congruence. }
  rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl. (*Nope*)
  destruct (beqAddr blockToFree blockChild) eqn:HbeqBlockBC.
  { rewrite <-DTL.beqAddrTrue in HbeqBlockBC. subst blockChild. rewrite HlookupBlockToF in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
  destruct (beqAddr (CPaddr (blockToFree + scoffset)) blockChild) eqn:HbeqSceBC.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSceBC. rewrite HbeqSceBC in *. rewrite Hnone in *. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
  destruct (beqAddr (CPaddr (blockToFree + sh1offset)) blockChild) eqn:HbeqSh1BC.
  {
    rewrite <-DTL.beqAddrTrue in HbeqSh1BC. rewrite HbeqSh1BC in *. rewrite Hnone in *. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
  rewrite beqAddrFalse in *. rewrite HbeqBlockBC. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
  rewrite HbeqPartAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  
  
  
  
  
  
  (* END childLocHasSameStart *)
}*)
Qed.
