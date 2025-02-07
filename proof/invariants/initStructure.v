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

Require Import Model.ADT Model.Monad Model.MAL Model.Lib Core.Internal.
Require Import Proof.Consistency Proof.StateLib.
Require Import Hoare InternalLemmas InternalLemmas2 WeakestPreconditions eraseBlock Invariants Isolation
  lookupInvariant.
Require Import List Coq.Logic.ProofIrrelevance Lia Classical_Prop Compare_dec EqNat Arith
  FunctionalExtensionality List.
Import List.ListNotations.

Lemma writeBlockEntryFromBlockEntryAddrLight entryaddr blockindex startaddr endaddr accessible present read write
exec P:
{{fun  s =>
P tt {|
      currentPartition := currentPartition s;
      memory :=
        add entryaddr
          (BE (CBlockEntry read write exec present accessible blockindex (CBlock startaddr endaddr))) (memory s)
           beqAddr
  |} }}
writeBlockEntryFromBlockEntryAddrLight entryaddr blockindex startaddr endaddr accessible present read write exec
{{P}}.
Proof.
unfold writeBlockEntryFromBlockEntryAddrLight. eapply weaken. apply modify.
simpl. intros s Hprops. apply Hprops.
Qed.

Lemma initBlockEntryRecAux n (kernel: paddr) (indexCurr: index) (P: state -> Prop):
{{
  fun s => indexCurr +1 < kernelStructureEntriesNb
            /\ n > indexCurr /\ kernel + kernelStructureEntriesNb <= maxAddr
            /\ (forall kernIdx: index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb - 1
                  -> exists l, lookup (CPaddr (kernel+kernIdx)) (memory s) beqAddr = Some(BE {|
                        read := false;
                        write := false;
                        exec := false;
                        present := false;
                        accessible := false;
                        blockindex := kernIdx;
                        blockrange := CBlock nullAddr (CPaddr (kernel+kernIdx+1));
                        Hidx := l
                      |}))
            /\ exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb - 1
                                -> addr <> CPaddr (kernel+kernIdx))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr
}}
initBlockEntryRecAux n kernel indexCurr
{{
  fun initSucc s => (forall kernIdx: index, kernIdx < kernelStructureEntriesNb - 1
                    -> exists l, lookup (CPaddr (kernel+kernIdx)) (memory s) beqAddr = Some(BE {|
                          read := false;
                          write := false;
                          exec := false;
                          present := false;
                          accessible := false;
                          blockindex := kernIdx;
                          blockrange := CBlock nullAddr (CPaddr (kernel+kernIdx+1));
                          Hidx := l
                        |}))
            /\ (exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx < kernelStructureEntriesNb - 1
                                -> addr <> CPaddr (kernel+kernIdx))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
            /\ initSucc = true
}}.
Proof.
revert indexCurr. induction n; intros indexCurr; simpl.
- eapply weaken. apply ret. intros s Hprops. simpl. destruct Hprops as (_ & HgtNCurr & _).
  exfalso. lia.
- eapply bindRev.
  { (** indexSuccM **)
    eapply weaken. apply Index.succ. intros s Hprops. simpl. split.
    apply Hprops.
    destruct Hprops as (Hres & _). pose proof maxIdxBiggerThanNbOfKernels. lia.
  }
  intro idxsucc. eapply bindRev.
  { (** MAL.getBlockEntryAddrFromKernelStructureStart **)
    eapply weaken. apply getBlockEntryAddrFromKernelStructureStartLight. intros s Hprops. simpl. apply Hprops.
  }
  intro nextEntryPointer. eapply bindRev.
  { (** MAL.getBlockEntryAddrFromKernelStructureStart **)
    eapply weaken. apply getBlockEntryAddrFromKernelStructureStartLight. intros s Hprops. simpl. apply Hprops.
  }
  intro currEntryPointer. eapply bindRev.
  { (** MAL.writeBlockEntryFromBlockEntryAddrLight **)
    eapply weaken. apply writeBlockEntryFromBlockEntryAddrLight. intros s Hprops. simpl.
    destruct Hprops as ((((HltIdxMax & HgtNCurr & HlebKernMaxKernEntries & HlookupIdxs & HP) & HnextIdx) & HnextP)
      & HcurrP).
      instantiate(1 := fun _ s => indexCurr + 1 < kernelStructureEntriesNb
        /\ StateLib.Index.succ indexCurr = Some idxsucc
        /\ nextEntryPointer = CPaddr (kernel + blkoffset + idxsucc)
        /\ currEntryPointer = CPaddr (kernel + blkoffset + indexCurr)
        /\ S n > indexCurr /\ kernel + kernelStructureEntriesNb <= maxAddr
        /\ exists s1,
          s = {|
              currentPartition := currentPartition s1;
              memory :=
                add currEntryPointer
                  (BE (CBlockEntry false false false false false indexCurr (CBlock nullAddr nextEntryPointer)))
                  (memory s1) beqAddr
            |}
          /\ (forall kernIdx : index,
                kernIdx >= indexCurr /\ kernIdx < kernelStructureEntriesNb-1 ->
                exists l,
                  lookup (CPaddr (kernel + kernIdx)) (memory s) beqAddr =
                  Some
                    (BE
                       {|
                         read := false;
                         write := false;
                         exec := false;
                         present := false;
                         accessible := false;
                         blockindex := kernIdx;
                         blockrange := CBlock nullAddr (CPaddr (kernel + kernIdx + 1));
                         Hidx := l
                       |}))
          /\ exists s0, P s0
            /\ currentPartition s = currentPartition s0
            /\ (forall addr, (forall kernIdx : index, kernIdx >= indexCurr /\ kernIdx < kernelStructureEntriesNb-1
                              -> addr <> CPaddr (kernel + kernIdx))
                  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)).
    set(s':= {|
                currentPartition := currentPartition s;
                memory :=
                  add currEntryPointer
                    (BE (CBlockEntry false false false false false indexCurr (CBlock nullAddr nextEntryPointer)))
                       (memory s) beqAddr
              |}). cbn -[kernelStructureEntriesNb s'].
    destruct HP as [s0 (HP & Hcurr & HlookupsEq)].
    assert(forall addr,
       (forall kernIdx : index, kernIdx >= indexCurr /\ kernIdx < kernelStructureEntriesNb-1
          -> addr <> CPaddr (kernel + kernIdx))
       -> lookup addr (memory s') beqAddr = lookup addr (memory s0) beqAddr).
    {
      intros addr HaddrNotExcept. cbn in HaddrNotExcept.
      assert(HaddrNotExceptExt: forall kernIdx : index, kernIdx > indexCurr /\ kernIdx < 7
        -> addr <> CPaddr (kernel + kernIdx)).
      {
        intros kernIdx (HgebIdxCurr & HltIdxKernEntries).
        assert(Hexcept: kernIdx >= indexCurr /\ kernIdx < 7).
        { split; lia. }
        specialize(HaddrNotExcept kernIdx Hexcept). assumption.
      }
      specialize(HlookupsEq addr HaddrNotExceptExt). rewrite <-HlookupsEq. simpl.
      destruct (beqAddr currEntryPointer addr) eqn:HbeqCurrPAddr.
      {
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqCurrPAddr.
        assert(HcurrIsExcept: indexCurr >= indexCurr /\ indexCurr < 7).
        { unfold kernelStructureEntriesNb in HltIdxMax. simpl in HltIdxMax. split; lia. }
        specialize(HaddrNotExcept indexCurr HcurrIsExcept). subst addr. rewrite HcurrP in HaddrNotExcept.
        unfold blkoffset in HaddrNotExcept. rewrite <-plus_n_O in HaddrNotExcept. congruence.
      }
      rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(forall (kernIdx: index), kernIdx >= indexCurr /\ kernIdx < kernelStructureEntriesNb-1
       -> exists l : kernIdx < kernelStructureEntriesNb,
         lookup (CPaddr (kernel + kernIdx)) (memory s') beqAddr =
         Some
           (BE
              {|
                read := false;
                write := false;
                exec := false;
                present := false;
                accessible := false;
                blockindex := kernIdx;
                blockrange :=
                  CBlock {| p := 0; Hp := ADT.CPaddr_obligation_1 0 (Nat.le_0_l maxAddr) |}
                    (CPaddr (kernel + kernIdx + 1));
                Hidx := l
              |})).
    {
      intros kernIdx (HgebIdxCurr & HltIdxKernEntries).
      destruct (Nat.eqb kernIdx indexCurr) eqn:HbeqIdxCurr.
      - apply Nat.eqb_eq in HbeqIdxCurr. apply DTL.index_eq_i in HbeqIdxCurr. subst kernIdx. simpl.
        assert(HbeqCurrPIdx: beqAddr currEntryPointer (CPaddr (kernel + indexCurr)) = true).
        {
          rewrite HcurrP. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia).
          simpl. rewrite Nat.add_0_r. apply beqAddrTrue.
        }
        rewrite HbeqCurrPIdx. unfold CBlockEntry. destruct (lt_dec indexCurr kernelStructureEntriesNb); try(lia).
        rewrite HnextP. rewrite Nat.add_0_r. unfold StateLib.Index.succ in HnextIdx.
        destruct (lt_dec indexCurr maxIdx); try(exfalso; congruence). injection HnextIdx as HnextIdx.
        rewrite <-HnextIdx. simpl. rewrite Nat.add_assoc. cbn. exists (ADT.CBlockEntry_obligation_1 indexCurr l).
        f_equal.
      - apply Nat.eqb_neq in HbeqIdxCurr. assert(HisNewKern: kernIdx > indexCurr /\ kernIdx < 7).
        { cbn in HltIdxKernEntries. split; lia. }
        specialize(HlookupIdxs kernIdx HisNewKern). destruct HlookupIdxs as [l HlookupIdxs]. exists l. simpl.
        destruct (beqAddr currEntryPointer (CPaddr (kernel + kernIdx))) eqn:HbeqIdxs.
        {
          rewrite <-DTL.beqAddrTrue in HbeqIdxs. unfold blkoffset in HcurrP. unfold CIndex in HcurrP. exfalso.
          destruct (le_dec 0 maxIdx); try(lia). simpl in HcurrP. rewrite Nat.add_0_r in *. rewrite HcurrP in *.
          unfold CPaddr in HbeqIdxs. destruct (le_dec (kernel + indexCurr) maxAddr); try(lia).
          destruct (le_dec (kernel + kernIdx) maxAddr); try(lia). injection HbeqIdxs as HbeqIdxs.
          apply Nat.add_cancel_l in HbeqIdxs. congruence.
        }
        rewrite <-DTL.beqAddrFalse in *. cbn in HlookupIdxs.
        rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    intuition. exists s. intuition. exists s0. split; try(split); assumption.
  }
  intro. eapply bindRev.
  { (** MALInternal.Index.zero **)
    eapply weaken. apply Index.zero. intros s Hprops. simpl. apply Hprops.
  }
  intro zero. destruct (indexEq indexCurr zero) eqn:HbeqIdxZero.
  + eapply weaken. apply ret. simpl. intros s Hprops. destruct Hprops as ((_ & _ & _ & _ & _ &
      [s1 [bentry Hprops]]) & Hzero). destruct Hprops as (Hs & HnewKern & HlookupEqs).
    apply DTL.beqIdxTrue in HbeqIdxZero. rewrite Hzero in HbeqIdxZero. unfold CIndex in HbeqIdxZero.
    destruct (le_dec 0 maxIdx); try(lia). subst indexCurr. split; try(split; try(reflexivity)).
    * intros kernIdx HltIdxKernEntries. simpl in HnewKern. assert(HidxIsNew: kernIdx >= 0 /\ kernIdx < 7).
      { split; lia. }
      specialize(HnewKern kernIdx HidxIsNew). assumption.
    * destruct HlookupEqs as [s0 (HP & Hcurr & HlookupEqs)]. exists s0. split. assumption. split. assumption.
      intros addr HaddrNotExcept.
      simpl in HlookupEqs. assert(HaddrNotExceptBis: (forall kernIdx : index, kernIdx >= 0 /\ kernIdx < 7
            -> addr <> CPaddr (kernel + kernIdx))).
      { intros kernIdx (_ & Hidx). specialize(HaddrNotExcept kernIdx Hidx). assumption. }
      specialize(HlookupEqs addr HaddrNotExceptBis). assumption.
  + eapply bindRev.
    { (** indexPredM **)
      eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops.
      apply DTL.beqIdxFalse in HbeqIdxZero. destruct Hprops as (Hprops & Hzero). subst zero.
      unfold CIndex in HbeqIdxZero. destruct (le_dec 0 maxIdx); try(lia).
      destruct (Nat.eqb (i indexCurr) 0) eqn:HbeqIdxZeroI.
      - apply Nat.eqb_eq in HbeqIdxZeroI. exfalso. contradict HbeqIdxZero. destruct indexCurr. simpl in *.
        subst i. f_equal. apply proof_irrelevance.
      - apply Nat.eqb_neq in HbeqIdxZeroI. lia.
    }
    intro idxpred. eapply weaken. apply IHn. intros s Hprops. simpl.
    destruct Hprops as (((HltIdwKernEntries & Hsucc & Hnext & Hcurr & HgtNCurr & HlebKernMaxKernEntries & [s1
      (Hs & HnewKern & HlookupsEq)]) & Hzero) & Hpred).
    unfold StateLib.Index.pred in Hpred. destruct (gt_dec indexCurr 0); try(exfalso; congruence).
    injection Hpred as Hpred. subst idxpred. simpl. split. lia. split. lia. split. assumption. split.
    * intros kernIdx (HgtIdxPred & HltIdxKernEntries).
      assert(HisNewKern: kernIdx >= indexCurr /\ kernIdx < 7).
      { split; lia. }
      specialize(HnewKern kernIdx HisNewKern). assumption.
    * destruct HlookupsEq as [s0 (HP & HcurrEq & HlookupsEq)]. exists s0. split. assumption. split. assumption.
      intros addr HaddrNotExcept.
      assert(HaddrNotExceptBis: forall (kernIdx : index), kernIdx >= indexCurr /\ kernIdx < 7
          -> addr <> CPaddr (kernel + kernIdx)).
      {
        intros kernIdx (HgebIdxCurr & HltIdxKernEntries).
        assert(Hidx: kernIdx > indexCurr - 1 /\ kernIdx < 7) by (split; lia). specialize(HaddrNotExcept kernIdx Hidx).
        assumption.
      }
      specialize(HlookupsEq addr HaddrNotExceptBis). assumption.
Qed.

Lemma initBlocksStructure (kernStart: paddr) P:
{{
  fun s => P s /\ kernStart + kernelStructureEntriesNb <= maxAddr
}}
initBlocksStructure kernStart
{{
  fun initSucc s => (forall kernIdx: index, kernIdx < kernelStructureEntriesNb - 1
                    -> exists l, lookup (CPaddr (kernStart+kernIdx)) (memory s) beqAddr = Some(BE {|
                          read := false;
                          write := false;
                          exec := false;
                          present := false;
                          accessible := false;
                          blockindex := kernIdx;
                          blockrange := CBlock nullAddr (CPaddr (kernStart+kernIdx+1));
                          Hidx := l
                        |}))
            /\ (exists l, lookup (CPaddr (kernStart+kernelStructureEntriesNb-1)) (memory s) beqAddr = Some(BE {|
                        read := false;
                        write := false;
                        exec := false;
                        present := false;
                        accessible := false;
                        blockindex := CIndex (kernelStructureEntriesNb-1);
                        blockrange := CBlock nullAddr nullAddr;
                        Hidx := l
                      |}))
            /\ (exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx <= kernelStructureEntriesNb - 1
                                -> addr <> CPaddr (kernStart+kernIdx))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
            /\ initSucc = true
}}.
Proof.
unfold initBlocksStructure. eapply bindRev.
{ (** MALInternal.getKernelStructureEntriesNb **)
  eapply weaken. apply getKernelStructureEntriesNb. intros s Hprops. simpl. apply Hprops.
}
intro entriesnb. eapply bindRev.
{ (** indexPredM **)
  eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops. destruct Hprops as (_ & Hres).
  subst entriesnb. unfold CIndex. pose proof KSEntriesNbLessThanMaxIdx.
  destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn. lia.
}
intro lastindex. eapply bindRev.
{ (** indexPredM **)
  eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops. destruct Hprops as ((_ & Hnb) & Hres).
  subst entriesnb. unfold StateLib.Index.pred in Hres.
  destruct (gt_dec (CIndex kernelStructureEntriesNb) 0); try(exfalso; congruence). injection Hres as Hres.
  subst lastindex. simpl. unfold CIndex. pose proof KSEntriesNbLessThanMaxIdx.
  destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn. lia.
}
intro secondlastindex. eapply bindRev.
{ (** Internal.initBlockEntryRecAux **)
  eapply weaken. apply initBlockEntryRecAux. intros s Hprops. simpl.
  destruct Hprops as ((((HP & HlebKernMaxKernEntries) & Hnb) & Hpred) & HsecPred).
  assert(HpredBis: StateLib.Index.pred entriesnb = Some lastindex) by assumption.
  assert(HsecPredBis: StateLib.Index.pred lastindex = Some secondlastindex) by assumption.
  unfold StateLib.Index.pred in HpredBis. destruct (gt_dec entriesnb 0); try(exfalso; congruence).
  unfold StateLib.Index.pred in HsecPredBis. destruct (gt_dec lastindex 0); try(exfalso; congruence).
  injection HpredBis as HpredBis. injection HsecPredBis as HsecPredBis.
  assert(HltSecPredKernEntries: secondlastindex < kernelStructureEntriesNb).
  {
    rewrite <-HsecPredBis. simpl. rewrite <-HpredBis. simpl. subst entriesnb. unfold CIndex.
    pose proof KSEntriesNbLessThanMaxIdx. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn. lia.
  }
  split.
  {
    rewrite <-HsecPredBis. simpl. rewrite <-HpredBis. simpl. subst entriesnb. unfold CIndex.
    pose proof KSEntriesNbLessThanMaxIdx. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn. lia.
  }
  split.
  {
    rewrite <-HsecPredBis. simpl. rewrite <-HpredBis. simpl. subst entriesnb. unfold CIndex. unfold N.
    pose proof KSEntriesNbLessThanMaxIdx. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
    rewrite maxIdxEqualMaxAddr in *. cbn -[kernelStructureEntriesNb]. lia.
  }
  split. assumption. split.
  - intros kernIdx (HgtIdxSecPred & HltIdxKernEntries). exfalso. rewrite <-HsecPredBis in *. simpl in *.
    rewrite <-HpredBis in *. simpl in *. subst entriesnb. unfold CIndex in HgtIdxSecPred.
    pose proof KSEntriesNbLessThanMaxIdx. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
    cbn in HgtIdxSecPred. lia.
  - exists s. split; try(split); try(reflexivity).
    instantiate(1 := fun s => P s /\ entriesnb = CIndex kernelStructureEntriesNb
      /\ StateLib.Index.pred entriesnb = Some lastindex /\ StateLib.Index.pred lastindex = Some secondlastindex
      /\ kernStart + kernelStructureEntriesNb <= maxAddr).
    intuition.
}
intro initEnded. destruct (negb initEnded) eqn:HinitEnded.
- eapply weaken. apply ret. intros s Hprops. simpl. apply Bool.eq_true_not_negb_iff in HinitEnded.
  apply Bool.not_true_is_false in HinitEnded. subst initEnded. exfalso.
  destruct Hprops as (_ & _ & Hcontra). congruence.
- eapply bindRev.
  { (** MAL.getBlockEntryAddrFromKernelStructureStart **)
    eapply weaken. apply getBlockEntryAddrFromKernelStructureStartLight. intros s Hprops. simpl. apply Hprops.
  }
  intro lastEntryPointer. eapply bindRev.
  { (** MAL.writeBlockEntryFromBlockEntryAddrLight **)
    eapply weaken. apply writeBlockEntryFromBlockEntryAddrLight. intros s Hprops. simpl.
    destruct Hprops as ((HnewKern & [s0 ((HP & Hentries & Hpred & HpredSec & HlebKernMaxKernEntries) & Hcurr &
      HlookupsEq)] & _) & Hlast).
    instantiate(1 := fun _ s => (forall kernIdx: index, kernIdx < kernelStructureEntriesNb - 1
                                -> exists l, lookup (CPaddr (kernStart+kernIdx)) (memory s) beqAddr = Some(BE {|
                                      read := false;
                                      write := false;
                                      exec := false;
                                      present := false;
                                      accessible := false;
                                      blockindex := kernIdx;
                                      blockrange := CBlock nullAddr (CPaddr (kernStart+kernIdx+1));
                                      Hidx := l
                                    |}))
      /\ (exists l, lookup lastEntryPointer (memory s) beqAddr = Some(BE {|
                  read := false;
                  write := false;
                  exec := false;
                  present := false;
                  accessible := false;
                  blockindex := lastindex;
                  blockrange := CBlock nullAddr nullAddr;
                  Hidx := l
                |}))
      /\ (exists s0, P s0
          /\ currentPartition s = currentPartition s0
          /\ forall addr, (forall kernIdx: index, kernIdx <= kernelStructureEntriesNb - 1
                          -> addr <> CPaddr (kernStart+kernIdx))
                -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
      /\ StateLib.Index.pred entriesnb = Some lastindex
      /\ entriesnb = CIndex kernelStructureEntriesNb
      /\ lastEntryPointer = CPaddr (kernStart + blkoffset + lastindex)
      /\ kernStart + kernelStructureEntriesNb <= maxAddr).
    set(s' := {|
                currentPartition := currentPartition s;
                memory :=
                  add lastEntryPointer
                    (BE (CBlockEntry false false false false false lastindex (CBlock nullAddr nullAddr)))
                       (memory s) beqAddr
              |}).
    cbn -[s' kernelStructureEntriesNb]. unfold StateLib.Index.pred in *.
    destruct (gt_dec entriesnb 0); try(exfalso; congruence). destruct (gt_dec lastindex 0); try(exfalso; congruence).
    injection Hpred as Hpred. injection HpredSec as HpredSec. unfold CIndex in Hentries.
    pose proof KSEntriesNbLessThanMaxIdx. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). split.
    { (* newKern s' *)
      intros kernIdx HgebIdxKernEntries. simpl. unfold blkoffset in *. unfold CIndex in Hlast.
      destruct (le_dec 0 maxIdx); try(lia). simpl in Hlast. rewrite Nat.add_0_r in Hlast. rewrite Hlast.
      destruct (beqAddr (CPaddr (kernStart + lastindex)) (CPaddr (kernStart + kernIdx))) eqn:HbeqLastIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastIdx. exfalso. unfold CPaddr in HbeqLastIdx. subst lastindex.
        subst entriesnb. cbn -[kernelStructureEntriesNb] in HbeqLastIdx.
        destruct (le_dec (kernStart + (kernelStructureEntriesNb - 1)) maxAddr); try(lia).
        destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia).
        injection HbeqLastIdx as HbeqLastIdx. apply Nat.add_cancel_l in HbeqLastIdx. cbn in HgebIdxKernEntries. lia.
      }
      rewrite <-DTL.beqAddrFalse in *. specialize(HnewKern kernIdx HgebIdxKernEntries).
      rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    split.
    {
      simpl. rewrite beqAddrTrue. unfold CBlockEntry. assert(lastindex < kernelStructureEntriesNb).
      { rewrite <-Hpred. simpl. rewrite Hentries. cbn. lia. }
      destruct (lt_dec lastindex kernelStructureEntriesNb); try(lia). cbn.
      exists (ADT.CBlockEntry_obligation_1 lastindex l0). f_equal.
    }
    split.
    {
      exists s0. split. assumption. split. assumption. intros addr HaddrNotExcept.
      assert(HnotExceptBis: forall (kernIdx: index), kernIdx < kernelStructureEntriesNb - 1
              -> addr <> CPaddr (kernStart + kernIdx)).
      {
        intros kernIdx HltIdxKernEntries. assert(HlebIdxKernEntries: kernIdx <= kernelStructureEntriesNb - 1) by lia.
        specialize(HaddrNotExcept kernIdx HlebIdxKernEntries). assumption.
      }
      specialize(HlookupsEq addr HnotExceptBis). rewrite <-HlookupsEq. simpl.
      destruct (beqAddr lastEntryPointer addr) eqn:HbeqLastAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastAddr. exfalso. unfold blkoffset in *. unfold CIndex in Hlast.
        destruct (le_dec 0 maxIdx); try(lia). simpl in Hlast. rewrite Nat.add_0_r in Hlast.
        rewrite Hlast in HbeqLastAddr. assert(HlebLastKernEntries: lastindex <= kernelStructureEntriesNb - 1).
        { rewrite <-Hpred. simpl. rewrite Hentries. cbn. lia. }
        specialize(HaddrNotExcept lastindex HlebLastKernEntries). congruence.
      }
      rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    split.
    { f_equal. assumption. }
    split. unfold CIndex. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). rewrite Hentries. f_equal.
    apply proof_irrelevance. unfold blkoffset in *. unfold CIndex in Hlast. destruct (le_dec 0 maxIdx); try(lia).
    simpl in Hlast. split; assumption.
  }
  intro. eapply weaken. apply ret. intros s Hprops. simpl.
  destruct Hprops as (HnewKern & HlastKern & HlookupsEq & Hlastidx & Hentries & Hlast & HlebKernMaxKernEntries).
  split. assumption. split.
  {
    assert(HlastEq: lastEntryPointer = CPaddr (kernStart + kernelStructureEntriesNb - 1)).
    {
      unfold StateLib.Index.pred in Hlastidx. unfold CIndex in Hentries. pose proof maxIdxBiggerThanNbOfKernels.
      destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
      destruct (gt_dec entriesnb 0); try(exfalso; congruence). injection Hlastidx as Hlastidx. subst lastindex.
      rewrite Hlast. subst entriesnb. cbn. assert(Hcalc: kernStart + 8 - 1 = kernStart + 0 + 7) by lia. rewrite Hcalc.
      reflexivity.
    }
    rewrite <-HlastEq. assert(lastindex = CIndex 7).
    {
      unfold StateLib.Index.pred in Hlastidx. unfold CIndex in Hentries. pose proof maxIdxBiggerThanNbOfKernels.
      destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
      destruct (gt_dec entriesnb 0); try(exfalso; congruence). injection Hlastidx as Hlastidx. subst lastindex.
      subst entriesnb. simpl. unfold CIndex. cbn in *. destruct (le_dec 7 maxIdx); try(lia). f_equal.
      apply proof_irrelevance.
    }
    subst lastindex. assumption.
  }
  cbn in HlookupsEq. split. assumption. reflexivity.
Qed.

Lemma writeSh1EntryFromBlockEntryAddrLight (block: paddr) pdChild pdFlag inChildLoc P:
{{fun  s => P s /\ exists bentry,
             lookup block (memory s) beqAddr = Some (BE bentry) /\
             isKS (CPaddr (block - blockindex bentry)) s /\ block >= blockindex bentry }}
writeSh1EntryFromBlockEntryAddrLight block pdChild pdFlag inChildLoc
{{ fun _ s => exists s0,
    s = {|
          currentPartition := currentPartition s0;
          memory :=
            add (CPaddr (block + sh1offset))
              (SHE {| PDchild := pdChild; PDflag := pdFlag; inChildLocation := inChildLoc |}) (memory s0) beqAddr
        |}
    /\ P s0
}}.
Proof.
unfold writeSh1EntryFromBlockEntryAddrLight. eapply bindRev.
{ (** MAL.getSh1EntryAddrFromBlockEntryAddr **)
  eapply weaken. apply getSh1EntryAddrFromBlockEntryAddrLight. intros s Hprops. simpl. split; apply Hprops.
}
intro Sh1EAddr. eapply weaken. apply modify. intros s Hprops. simpl. exists s.
destruct Hprops as (Hprops & Hsh1). subst Sh1EAddr. split. reflexivity. apply Hprops.
Qed.

Lemma initSh1EntryRecAux n (kernStart: paddr) (indexCurr: index) P:
{{
  fun s => kernStart + kernelStructureEntriesNb + sh1offset <= maxAddr
            /\ n > indexCurr
            /\ indexCurr < kernelStructureEntriesNb
            /\ isKS kernStart s
            /\ (forall (kernIdx: index), kernIdx < kernelStructureEntriesNb
                  -> bentryBlockIndex (CPaddr (kernStart+kernIdx)) kernIdx s)
            /\ (forall kernIdx: index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb
                  -> lookup (CPaddr (kernStart+kernIdx+sh1offset)) (memory s) beqAddr = Some(SHE {|
                          PDchild := nullAddr;
                          PDflag := false;
                          inChildLocation := nullAddr
                        |}))
            /\ exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb
                                -> addr <> CPaddr (kernStart+kernIdx+sh1offset))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr
}}
initSh1EntryRecAux n kernStart indexCurr
{{
  fun initSucc s => (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                    -> lookup (CPaddr (kernStart+kernIdx+sh1offset)) (memory s) beqAddr = Some(SHE {|
                          PDchild := nullAddr;
                          PDflag := false;
                          inChildLocation := nullAddr
                        |}))
            /\ (exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                                -> addr <> CPaddr (kernStart+kernIdx+sh1offset))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
            /\ initSucc = true
}}.
Proof.
revert indexCurr. induction n; simpl; intro indexCurr.
- eapply weaken. apply ret. intros s Hprops. exfalso. destruct Hprops as (_ & Hcontra & _). lia.
- eapply bindRev.
  { (** MAL.getBlockEntryAddrFromKernelStructureStart **)
    eapply weaken. apply getBlockEntryAddrFromKernelStructureStartLight. intros s Hprops. simpl. apply Hprops.
  }
  intro currEntryPointer. eapply bindRev.
  { (** MAL.writeSh1EntryFromBlockEntryAddrLight **)
    eapply weaken. apply writeSh1EntryFromBlockEntryAddrLight. intros s Hprops. simpl. split. apply Hprops.
    destruct Hprops as ((HlebKernMaxKernEntries & HgtNCurr & HltCurrKernEntries & HkernIsKS & HidxCurr &
      HnewShe) & HcurrP). specialize(HidxCurr indexCurr HltCurrKernEntries).
    unfold blkoffset in HcurrP. unfold CIndex in HcurrP.
    destruct (le_dec 0 maxIdx); try(lia). simpl in HcurrP. rewrite Nat.add_0_r in HcurrP. subst currEntryPointer.
    unfold bentryBlockIndex in HidxCurr.
    destruct (lookup (CPaddr (kernStart + indexCurr)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists b. split. reflexivity.
    assert(HkernEq: CPaddr (kernStart + indexCurr) - blockindex b = kernStart).
    {
      subst indexCurr. apply Nat.add_sub_eq_r. unfold CPaddr.
      destruct (le_dec (kernStart + blockindex b) maxAddr); try(lia). simpl. reflexivity.
    }
    rewrite HkernEq. assert(kernStart <= maxAddr) by (apply Hp). unfold CPaddr.
    destruct (le_dec kernStart maxAddr); try(lia). destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia).
    simpl. subst indexCurr. split; try(lia).
    assert(Heq: {| p := kernStart; Hp := ADT.CPaddr_obligation_1 kernStart l0 |} = kernStart).
    { destruct kernStart. simpl. f_equal. apply proof_irrelevance. }
    rewrite Heq. assumption.
  }
  intro. eapply bindRev.
  { (** MALInternal.Index.zero **)
    eapply weaken. apply Index.zero. intros s Hprops. simpl. apply Hprops.
  }
  intro zero. destruct (indexEq indexCurr zero) eqn:HbeqCurrZero.
  + eapply weaken. apply ret. intros s Hprops. simpl.
    destruct Hprops as ([s1 (Hs & (HlebKernEntriesMax & HgtSNCur & HltCurrKernEntries & HkernIsKS & Hindices &
      HnewShe & Hs0) & HcurrP)] & Hzero). unfold CIndex in Hzero. destruct (le_dec 0 maxIdx); try(lia).
    subst zero. apply DTL.beqIdxTrue in HbeqCurrZero. split.
    * intros kernIdx HltIdxKernEntries. unfold blkoffset in HcurrP. unfold CIndex in HcurrP.
      destruct (le_dec 0 maxIdx); try(lia). simpl in HcurrP. rewrite Nat.add_0_r in HcurrP.
      destruct (Nat.eqb kernIdx indexCurr) eqn:HbeqIdxCurr.
      -- apply Nat.eqb_eq in HbeqIdxCurr. rewrite HbeqIdxCurr in *. subst indexCurr. simpl in *.
         rewrite Nat.add_0_r in *. assert(HcurrIsKern: currEntryPointer = kernStart).
         {
           rewrite HcurrP. assert(kernStart <= maxAddr) by (apply Hp). unfold CPaddr.
           destruct (le_dec kernStart maxAddr); try(lia). destruct kernStart. simpl. f_equal. apply proof_irrelevance.
         }
         clear HcurrP. subst currEntryPointer. rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity.
      -- apply Nat.eqb_neq in HbeqIdxCurr.
         assert(HltBis: kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb).
         { split; try(assumption). subst indexCurr. simpl in *. lia. }
         specialize(HnewShe kernIdx HltBis). rewrite Hs. simpl. subst currEntryPointer.
         assert(Heq: CPaddr (kernStart + indexCurr) + sh1offset = kernStart + indexCurr + sh1offset).
         {
           unfold CPaddr. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia). simpl. reflexivity.
         }
         rewrite Heq. destruct (beqAddr (CPaddr (kernStart + indexCurr + sh1offset))
           (CPaddr (kernStart + kernIdx + sh1offset))) eqn:HbeqCurrSh1IdxSh1.
         ++ reflexivity.
         ++ rewrite <-DTL.beqAddrFalse in HbeqCurrSh1IdxSh1.
            rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    * split; try(reflexivity). destruct Hs0 as [s0 (HP & Hcurr & HlookupsEq)]. exists s0. split. assumption.
      split. rewrite Hs. simpl. assumption. intros addr HaddrNotExcept.
      assert(HaddrNotExceptRestr: forall kernIdx : index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb
        -> addr <> CPaddr (kernStart + kernIdx + sh1offset)).
      { intros kernIdx (_ & Hidx). specialize(HaddrNotExcept kernIdx Hidx). assumption. }
      specialize(HlookupsEq addr HaddrNotExceptRestr). rewrite <-HlookupsEq. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (currEntryPointer + sh1offset)) addr) eqn:HbeqCurrPSh1Addr.
      {
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqCurrPSh1Addr.
        assert(HcurrPEq: currEntryPointer + sh1offset = kernStart + indexCurr + sh1offset).
        {
          rewrite HcurrP. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
          rewrite Nat.add_0_r. unfold CPaddr. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia). simpl.
          reflexivity.
        }
        rewrite HcurrPEq in HbeqCurrPSh1Addr. specialize(HaddrNotExcept indexCurr HltCurrKernEntries). congruence.
      }
      rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
  + apply DTL.beqIdxFalse in HbeqCurrZero. eapply bindRev.
    { (** indexPredM **)
      eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops. destruct Hprops as (_ & Hzero).
      unfold CIndex in Hzero. destruct (le_dec 0 maxIdx); try(lia). subst zero. assert(i indexCurr <> 0).
      { contradict HbeqCurrZero. apply DTL.index_eq_i. simpl. assumption. }
      lia.
    }
    intro idxpred. eapply weaken. apply IHn. intros s Hprops. simpl.
    destruct Hprops as (([s1 (Hs & (HlebKernEntriesSh1Max & HgtSNCurr & HlebCurrKernEntries & HkernIsKS & Hindices &
      HnewShe & [s0 (HP & Hcurr & HlookupsEq)]) & HcurrP)] & Hzero) & Hpred).
    split. assumption. unfold StateLib.Index.pred in Hpred. destruct (gt_dec indexCurr 0); try(exfalso; congruence).
    injection Hpred as Hpred. split. subst idxpred. simpl. lia. split. subst idxpred. simpl. lia. split.
    {
      unfold isKS in *. rewrite Hs. simpl. destruct (beqAddr (CPaddr (currEntryPointer + sh1offset)) kernStart)
        eqn:HbeqCurrSheKern.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSheKern. subst currEntryPointer. unfold blkoffset in HbeqCurrSheKern.
        unfold CIndex in HbeqCurrSheKern. destruct (le_dec 0 maxIdx); try(lia). rewrite Nat.add_0_r in *.
        unfold CPaddr in HbeqCurrSheKern. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia).
        simpl in *. destruct (le_dec (kernStart + indexCurr + sh1offset) maxAddr); try(lia).
        assert(p kernStart = kernStart + indexCurr + sh1offset).
        { rewrite <-HbeqCurrSheKern at 1. simpl. reflexivity. }
        lia.
      }
      rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    split.
    {
      intros kernIdx HlebIdxKernEntries. specialize(Hindices kernIdx HlebIdxKernEntries). unfold bentryBlockIndex.
      rewrite Hs. simpl. destruct (beqAddr (CPaddr (currEntryPointer + sh1offset)) (CPaddr (kernStart + kernIdx)))
        eqn:HbeqCurrSh1Kernidx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1Kernidx. unfold blkoffset in HcurrP. unfold CIndex in HcurrP.
        destruct (le_dec 0 maxIdx); try(lia). rewrite Nat.add_0_r in *. subst currEntryPointer.
        unfold CPaddr in HbeqCurrSh1Kernidx. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia).
        simpl in HbeqCurrSh1Kernidx. destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia).
        destruct (le_dec (kernStart + indexCurr + sh1offset) maxAddr); try(lia).
        injection HbeqCurrSh1Kernidx as HbeqCurrSh1Kernidx. unfold sh1offset in HbeqCurrSh1Kernidx.
        unfold blkoffset in HbeqCurrSh1Kernidx. unfold CIndex in HbeqCurrSh1Kernidx.
        destruct (le_dec 0 maxIdx); try(lia). simpl in HbeqCurrSh1Kernidx.
        pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
        simpl in HbeqCurrSh1Kernidx. lia.
      }
      rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    split.
    {
      intros kernIdx (HgtIdxPred & HlebIdxKernEntries). rewrite Hs. simpl.
      assert(HcurrPEq: currEntryPointer + sh1offset = kernStart + indexCurr + sh1offset).
      {
        rewrite HcurrP. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
        rewrite Nat.add_0_r. unfold CPaddr. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia). simpl.
        reflexivity.
      }
      rewrite HcurrPEq. destruct (Nat.eqb indexCurr kernIdx) eqn:HbeqCurrIdx.
      - apply Nat.eqb_eq in HbeqCurrIdx. rewrite HbeqCurrIdx. rewrite beqAddrTrue. reflexivity.
      - apply Nat.eqb_neq in HbeqCurrIdx.
        destruct (beqAddr (CPaddr (kernStart + indexCurr + sh1offset)) (CPaddr (kernStart + kernIdx + sh1offset)))
          eqn:HbeqSh1s; try(reflexivity).
        assert(HidxNotExceptRestr: kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb).
        { rewrite <-Hpred in *. simpl in *. split; lia. }
        specialize(HnewShe kernIdx HidxNotExceptRestr). rewrite <-DTL.beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    exists s0. split. assumption. split. rewrite Hs. simpl. assumption. intros addr HaddrNotExcept.
    assert(HaddrNotExceptRestr: forall kernIdx : index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb
      -> addr <> CPaddr (kernStart + kernIdx + sh1offset)).
    {
      intros kernIdx (HgtIdxCurr & HlebIdxKernEntries).
      assert(HidxExcept: kernIdx > idxpred /\ kernIdx < kernelStructureEntriesNb).
      { rewrite <-Hpred. simpl. split; lia. }
      specialize(HaddrNotExcept kernIdx HidxExcept). assumption.
    }
    specialize(HlookupsEq addr HaddrNotExceptRestr). rewrite <-HlookupsEq. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (currEntryPointer + sh1offset)) addr) eqn:HbeqCurrSh1Addr.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqCurrSh1Addr.
      assert(HcurrPEq: currEntryPointer + sh1offset = kernStart + indexCurr + sh1offset).
      {
        rewrite HcurrP. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
        rewrite Nat.add_0_r. unfold CPaddr. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia). simpl.
        reflexivity.
      }
      assert(HcurrProp: indexCurr > idxpred /\ indexCurr < kernelStructureEntriesNb).
      { rewrite <-Hpred. simpl. split; lia. }
      rewrite HcurrPEq in HbeqCurrSh1Addr. specialize(HaddrNotExcept indexCurr HcurrProp). congruence.
    }
    rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
Qed.

Lemma initSh1Structure (kernStart: paddr) P:
{{
  fun s => P s /\ kernStart + kernelStructureEntriesNb + sh1offset <= maxAddr
            /\ isKS kernStart s
            /\ (forall (kernIdx: index), kernIdx < kernelStructureEntriesNb
                  -> bentryBlockIndex (CPaddr (kernStart+kernIdx)) kernIdx s)
}}
initSh1Structure kernStart
{{
  fun initSucc s =>
            (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                    -> lookup (CPaddr (kernStart+kernIdx+sh1offset)) (memory s) beqAddr = Some(SHE {|
                          PDchild := nullAddr;
                          PDflag := false;
                          inChildLocation := nullAddr
                        |}))
            /\ (exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                                -> addr <> CPaddr (kernStart+kernIdx+sh1offset))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
            /\ initSucc = true
}}.
Proof.
unfold initSh1Structure. eapply bindRev.
{ (** MALInternal.getKernelStructureEntriesNb **)
  eapply weaken. apply getKernelStructureEntriesNb. intros s Hprops. simpl. apply Hprops.
}
intro entriesnb. eapply bindRev.
{ (** indexPredM **)
  eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops. destruct Hprops as (_ & Hentries).
  subst entriesnb. unfold CIndex. pose proof maxIdxBiggerThanNbOfKernels.
  destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn. lia.
}
intro lastindex. eapply bindRev.
{ (** Internal.initSh1EntryRecAux **)
  eapply weaken. apply initSh1EntryRecAux. intros s Hprops. simpl. destruct Hprops as (((HP & HlebKernEntriesSh1Max &
    HkernIsKS & Hindices) & Hentries) & Hpred). split. assumption. unfold StateLib.Index.pred in Hpred.
  destruct (gt_dec entriesnb 0); try(exfalso; congruence). injection Hpred as Hpred. unfold CIndex in Hentries.
  pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
  subst entriesnb. cbn -[kernelStructureEntriesNb nullAddr] in *. split.
  { rewrite maxIdxEqualMaxAddr in *. rewrite <-Hpred. unfold N. cbn -[kernelStructureEntriesNb]. lia. }
  split. rewrite <-Hpred. cbn -[kernelStructureEntriesNb]. lia. split. assumption. split. assumption.
  assert(Hfalse: forall kernIdx : index, kernIdx > lastindex /\ kernIdx < kernelStructureEntriesNb -> False).
  {
    intros kernIdx (HgtIdxPred & HltIdxKernEntries). rewrite <-Hpred in HgtIdxPred.
    cbn -[kernelStructureEntriesNb] in HgtIdxPred. lia.
  }
  split. intros kernIdx Hcontra. exfalso. apply Hfalse with kernIdx; assumption. exists s. split.
  {
    instantiate(1 := fun s => P s). simpl. assumption.
  }
  split. reflexivity. intros addr _. reflexivity.
}
intro initEnded. destruct (negb initEnded) eqn:HnegInit.
- eapply weaken. apply ret. intros s Hprops. exfalso. destruct Hprops as (_ & _ & Hontra). subst initEnded.
  apply Bool.eq_true_not_negb_iff in HnegInit. congruence.
- eapply weaken. apply ret. intros s Hprops. simpl. destruct Hprops as (HnewShe & HlookupsEq & _). split.
  assumption. split. assumption. reflexivity.
Qed.

Lemma writeSCEntryFromBlockEntryAddrLight (block: paddr) origin next P:
{{fun  s => P s /\ exists bentry,
             lookup block (memory s) beqAddr = Some (BE bentry) /\
             isKS (CPaddr (block - blockindex bentry)) s /\ block >= blockindex bentry }}
writeSCEntryFromBlockEntryAddrLight block origin next
{{ fun _ s => exists s0,
    s = {|
          currentPartition := currentPartition s0;
          memory :=
            add (CPaddr (block + scoffset))
              (SCE {| origin := origin; next := next |}) (memory s0) beqAddr
        |}
    /\ P s0
}}.
Proof.
unfold writeSCEntryFromBlockEntryAddrLight. eapply bindRev.
{ (** MAL.getSCEntryAddrFromBlockEntryAddr **)
  eapply weaken. apply getSCEntryAddrFromBlockEntryAddrLight. intros s Hprops. simpl. split; apply Hprops.
}
intro ScEAddr. eapply weaken. apply modify. intros s Hprops. simpl. exists s.
destruct Hprops as (Hprops & Hsce). unfold scentryAddr in *.
destruct (lookup block (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
subst ScEAddr. split. reflexivity. apply Hprops.
Qed.

Lemma initSCEntryRecAux n (kernStart: paddr) (indexCurr: index) P:
{{
  fun s => kernStart + kernelStructureEntriesNb + scoffset <= maxAddr
            /\ n > indexCurr
            /\ indexCurr < kernelStructureEntriesNb
            /\ isKS kernStart s
            /\ (forall (kernIdx: index), kernIdx < kernelStructureEntriesNb
                  -> bentryBlockIndex (CPaddr (kernStart+kernIdx)) kernIdx s)
            /\ (forall kernIdx: index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb
                  -> lookup (CPaddr (kernStart+kernIdx+scoffset)) (memory s) beqAddr = Some(SCE {|
                          origin := nullAddr;
                          next := nullAddr
                        |}))
            /\ exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb
                                -> addr <> CPaddr (kernStart+kernIdx+scoffset))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr
}}
initSCEntryRecAux n kernStart indexCurr
{{
  fun initSucc s => (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                    -> lookup (CPaddr (kernStart+kernIdx+scoffset)) (memory s) beqAddr = Some(SCE {|
                          origin := nullAddr;
                          next := nullAddr
                        |}))
            /\ (exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                                -> addr <> CPaddr (kernStart+kernIdx+scoffset))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
            /\ initSucc = true
}}.
Proof.
revert indexCurr. induction n; simpl; intro indexCurr.
- eapply weaken. apply ret. intros s Hprops. exfalso. destruct Hprops as (_ & Hcontra & _). lia.
- eapply bindRev.
  { (** MAL.getBlockEntryAddrFromKernelStructureStart **)
    eapply weaken. apply getBlockEntryAddrFromKernelStructureStartLight. intros s Hprops. simpl. apply Hprops.
  }
  intro currEntryPointer. eapply bindRev.
  { (** MAL.writeSh1EntryFromBlockEntryAddrLight **)
    eapply weaken. apply writeSCEntryFromBlockEntryAddrLight. intros s Hprops. simpl. split. apply Hprops.
    destruct Hprops as ((HlebKernMaxKernEntries & HgtNCurr & HltCurrKernEntries & HkernIsKS & HidxCurr &
      HnewShe) & HcurrP). specialize(HidxCurr indexCurr HltCurrKernEntries).
    unfold blkoffset in HcurrP. unfold CIndex in HcurrP.
    destruct (le_dec 0 maxIdx); try(lia). simpl in HcurrP. rewrite Nat.add_0_r in HcurrP. subst currEntryPointer.
    unfold bentryBlockIndex in HidxCurr.
    destruct (lookup (CPaddr (kernStart + indexCurr)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists b. split. reflexivity.
    assert(HkernEq: CPaddr (kernStart + indexCurr) - blockindex b = kernStart).
    {
      subst indexCurr. apply Nat.add_sub_eq_r. unfold CPaddr.
      destruct (le_dec (kernStart + blockindex b) maxAddr); try(lia). simpl. reflexivity.
    }
    rewrite HkernEq. assert(kernStart <= maxAddr) by (apply Hp). unfold CPaddr.
    destruct (le_dec kernStart maxAddr); try(lia). destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia).
    simpl. subst indexCurr. split; try(lia).
    assert(Heq: {| p := kernStart; Hp := ADT.CPaddr_obligation_1 kernStart l0 |} = kernStart).
    { destruct kernStart. simpl. f_equal. apply proof_irrelevance. }
    rewrite Heq. assumption.
  }
  intro. eapply bindRev.
  { (** MALInternal.Index.zero **)
    eapply weaken. apply Index.zero. intros s Hprops. simpl. apply Hprops.
  }
  intro zero. destruct (indexEq indexCurr zero) eqn:HbeqCurrZero.
  + eapply weaken. apply ret. intros s Hprops. simpl.
    destruct Hprops as ([s1 (Hs & (HlebKernEntriesMax & HgtSNCur & HltCurrKernEntries & HkernIsKS & Hindices &
      HnewShe & Hs0) & HcurrP)] & Hzero). unfold CIndex in Hzero. destruct (le_dec 0 maxIdx); try(lia).
    subst zero. apply DTL.beqIdxTrue in HbeqCurrZero. split.
    * intros kernIdx HltIdxKernEntries. unfold blkoffset in HcurrP. unfold CIndex in HcurrP.
      destruct (le_dec 0 maxIdx); try(lia). simpl in HcurrP. rewrite Nat.add_0_r in HcurrP.
      destruct (Nat.eqb kernIdx indexCurr) eqn:HbeqIdxCurr.
      -- apply Nat.eqb_eq in HbeqIdxCurr. rewrite HbeqIdxCurr in *. subst indexCurr. simpl in *.
         rewrite Nat.add_0_r in *. assert(HcurrIsKern: currEntryPointer = kernStart).
         {
           rewrite HcurrP. assert(kernStart <= maxAddr) by (apply Hp). unfold CPaddr.
           destruct (le_dec kernStart maxAddr); try(lia). destruct kernStart. simpl. f_equal. apply proof_irrelevance.
         }
         clear HcurrP. subst currEntryPointer. rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity.
      -- apply Nat.eqb_neq in HbeqIdxCurr.
         assert(HltBis: kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb).
         { split; try(assumption). subst indexCurr. simpl in *. lia. }
         specialize(HnewShe kernIdx HltBis). rewrite Hs. simpl. subst currEntryPointer.
         assert(Heq: CPaddr (kernStart + indexCurr) + scoffset = kernStart + indexCurr + scoffset).
         {
           unfold CPaddr. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia). simpl. reflexivity.
         }
         rewrite Heq. destruct (beqAddr (CPaddr (kernStart + indexCurr + scoffset))
           (CPaddr (kernStart + kernIdx + scoffset))) eqn:HbeqCurrSceIdxSce.
         ++ reflexivity.
         ++ rewrite <-DTL.beqAddrFalse in HbeqCurrSceIdxSce.
            rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    * split; try(reflexivity). destruct Hs0 as [s0 (HP & Hcurr & HlookupsEq)]. exists s0. split. assumption.
      split. rewrite Hs. simpl. assumption. intros addr HaddrNotExcept.
      assert(HaddrNotExceptRestr: forall kernIdx : index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb
        -> addr <> CPaddr (kernStart + kernIdx + scoffset)).
      { intros kernIdx (_ & Hidx). specialize(HaddrNotExcept kernIdx Hidx). assumption. }
      specialize(HlookupsEq addr HaddrNotExceptRestr). rewrite <-HlookupsEq. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (currEntryPointer + scoffset)) addr) eqn:HbeqCurrPSceAddr.
      {
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqCurrPSceAddr.
        assert(HcurrPEq: currEntryPointer + scoffset = kernStart + indexCurr + scoffset).
        {
          rewrite HcurrP. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
          rewrite Nat.add_0_r. unfold CPaddr. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia). simpl.
          reflexivity.
        }
        rewrite HcurrPEq in HbeqCurrPSceAddr. specialize(HaddrNotExcept indexCurr HltCurrKernEntries). congruence.
      }
      rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
  + apply DTL.beqIdxFalse in HbeqCurrZero. eapply bindRev.
    { (** indexPredM **)
      eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops. destruct Hprops as (_ & Hzero).
      unfold CIndex in Hzero. destruct (le_dec 0 maxIdx); try(lia). subst zero. assert(i indexCurr <> 0).
      { contradict HbeqCurrZero. apply DTL.index_eq_i. simpl. assumption. }
      lia.
    }
    intro idxpred. eapply weaken. apply IHn. intros s Hprops. simpl.
    destruct Hprops as (([s1 (Hs & (HlebKernEntriesSceMax & HgtSNCurr & HlebCurrKernEntries & HkernIsKS & Hindices &
      HnewShe & [s0 (HP & Hcurr & HlookupsEq)]) & HcurrP)] & Hzero) & Hpred).
    split. assumption. unfold StateLib.Index.pred in Hpred. destruct (gt_dec indexCurr 0); try(exfalso; congruence).
    injection Hpred as Hpred. split. subst idxpred. simpl. lia. split. subst idxpred. simpl. lia. split.
    {
      unfold isKS in *. rewrite Hs. simpl. destruct (beqAddr (CPaddr (currEntryPointer + scoffset)) kernStart)
        eqn:HbeqCurrSceKern.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSceKern. subst currEntryPointer. unfold blkoffset in HbeqCurrSceKern.
        unfold CIndex in HbeqCurrSceKern. destruct (le_dec 0 maxIdx); try(lia). rewrite Nat.add_0_r in *.
        unfold CPaddr in HbeqCurrSceKern. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia).
        simpl in *. destruct (le_dec (kernStart + indexCurr + scoffset) maxAddr); try(lia).
        assert(p kernStart = kernStart + indexCurr + scoffset).
        { rewrite <-HbeqCurrSceKern at 1. simpl. reflexivity. }
        lia.
      }
      rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    split.
    {
      intros kernIdx HlebIdxKernEntries. specialize(Hindices kernIdx HlebIdxKernEntries). unfold bentryBlockIndex.
      rewrite Hs. simpl. destruct (beqAddr (CPaddr (currEntryPointer + scoffset)) (CPaddr (kernStart + kernIdx)))
        eqn:HbeqCurrSceKernidx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSceKernidx. unfold blkoffset in HcurrP. unfold CIndex in HcurrP.
        destruct (le_dec 0 maxIdx); try(lia). rewrite Nat.add_0_r in *. subst currEntryPointer.
        unfold CPaddr in HbeqCurrSceKernidx. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia).
        simpl in HbeqCurrSceKernidx. destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia).
        destruct (le_dec (kernStart + indexCurr + scoffset) maxAddr); try(lia).
        injection HbeqCurrSceKernidx as HbeqCurrSceKernidx. unfold scoffset in HbeqCurrSceKernidx.
        unfold sh1offset in HbeqCurrSceKernidx. unfold blkoffset in HbeqCurrSceKernidx.
        unfold CIndex in HbeqCurrSceKernidx. destruct (le_dec 0 maxIdx); try(lia). simpl in HbeqCurrSceKernidx.
        pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
        cbn in HbeqCurrSceKernidx. pose proof Constants.maxIdxBiggerThanMinBlock.
        destruct (le_dec 16 maxIdx); try(lia). cbn in *. lia.
      }
      rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    split.
    {
      intros kernIdx (HgtIdxPred & HlebIdxKernEntries). rewrite Hs. simpl.
      assert(HcurrPEq: currEntryPointer + scoffset = kernStart + indexCurr + scoffset).
      {
        rewrite HcurrP. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
        rewrite Nat.add_0_r. unfold CPaddr. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia). simpl.
        reflexivity.
      }
      rewrite HcurrPEq. destruct (Nat.eqb indexCurr kernIdx) eqn:HbeqCurrIdx.
      - apply Nat.eqb_eq in HbeqCurrIdx. rewrite HbeqCurrIdx. rewrite beqAddrTrue. reflexivity.
      - apply Nat.eqb_neq in HbeqCurrIdx.
        destruct (beqAddr (CPaddr (kernStart + indexCurr + scoffset)) (CPaddr (kernStart + kernIdx + scoffset)))
          eqn:HbeqSh1s; try(reflexivity).
        assert(HidxNotExceptRestr: kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb).
        { rewrite <-Hpred in *. simpl in *. split; lia. }
        specialize(HnewShe kernIdx HidxNotExceptRestr). rewrite <-DTL.beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    exists s0. split. assumption. split. rewrite Hs. simpl. assumption. intros addr HaddrNotExcept.
    assert(HaddrNotExceptRestr: forall kernIdx : index, kernIdx > indexCurr /\ kernIdx < kernelStructureEntriesNb
      -> addr <> CPaddr (kernStart + kernIdx + scoffset)).
    {
      intros kernIdx (HgtIdxCurr & HlebIdxKernEntries).
      assert(HidxExcept: kernIdx > idxpred /\ kernIdx < kernelStructureEntriesNb).
      { rewrite <-Hpred. simpl. split; lia. }
      specialize(HaddrNotExcept kernIdx HidxExcept). assumption.
    }
    specialize(HlookupsEq addr HaddrNotExceptRestr). rewrite <-HlookupsEq. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (currEntryPointer + scoffset)) addr) eqn:HbeqCurrSceAddr.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqCurrSceAddr.
      assert(HcurrPEq: currEntryPointer + scoffset = kernStart + indexCurr + scoffset).
      {
        rewrite HcurrP. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
        rewrite Nat.add_0_r. unfold CPaddr. destruct (le_dec (kernStart + indexCurr) maxAddr); try(lia). simpl.
        reflexivity.
      }
      assert(HcurrProp: indexCurr > idxpred /\ indexCurr < kernelStructureEntriesNb).
      { rewrite <-Hpred. simpl. split; lia. }
      rewrite HcurrPEq in HbeqCurrSceAddr. specialize(HaddrNotExcept indexCurr HcurrProp). congruence.
    }
    rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
Qed.

Lemma initSCStructure (kernStart: paddr) P:
{{
  fun s => P s /\ kernStart + kernelStructureEntriesNb + scoffset <= maxAddr
            /\ isKS kernStart s
            /\ (forall (kernIdx: index), kernIdx < kernelStructureEntriesNb
                  -> bentryBlockIndex (CPaddr (kernStart+kernIdx)) kernIdx s)
}}
initSCStructure kernStart
{{
  fun initSucc s =>
            (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                    -> lookup (CPaddr (kernStart+kernIdx+scoffset)) (memory s) beqAddr = Some(SCE {|
                          origin := nullAddr;
                          next := nullAddr
                        |}))
            /\ (exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ forall addr, (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                                -> addr <> CPaddr (kernStart+kernIdx+scoffset))
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
            /\ initSucc = true
}}.
Proof.
unfold initSCStructure. eapply bindRev.
{ (** MALInternal.getKernelStructureEntriesNb **)
  eapply weaken. apply getKernelStructureEntriesNb. intros s Hprops. simpl. apply Hprops.
}
intro entriesnb. eapply bindRev.
{ (** indexPredM **)
  eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops. destruct Hprops as (_ & Hentries).
  subst entriesnb. unfold CIndex. pose proof maxIdxBiggerThanNbOfKernels.
  destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn. lia.
}
intro lastindex. eapply bindRev.
{ (** Internal.initSCEntryRecAux **)
  eapply weaken. apply initSCEntryRecAux. intros s Hprops. simpl. destruct Hprops as (((HP & HlebKernEntriesSceMax &
    HkernIsKS & Hindices) & Hentries) & Hpred). split. assumption. unfold StateLib.Index.pred in Hpred.
  destruct (gt_dec entriesnb 0); try(exfalso; congruence). injection Hpred as Hpred. unfold CIndex in Hentries.
  pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
  subst entriesnb. cbn -[kernelStructureEntriesNb nullAddr] in *. split.
  { rewrite maxIdxEqualMaxAddr in *. rewrite <-Hpred. unfold N. cbn -[kernelStructureEntriesNb]. lia. }
  split. rewrite <-Hpred. cbn -[kernelStructureEntriesNb]. lia. split. assumption. split. assumption.
  assert(Hfalse: forall kernIdx : index, kernIdx > lastindex /\ kernIdx < kernelStructureEntriesNb -> False).
  {
    intros kernIdx (HgtIdxPred & HltIdxKernEntries). rewrite <-Hpred in HgtIdxPred.
    cbn -[kernelStructureEntriesNb] in HgtIdxPred. lia.
  }
  split. intros kernIdx Hcontra. exfalso. apply Hfalse with kernIdx; assumption. exists s. split.
  {
    instantiate(1 := fun s => P s). simpl. assumption.
  }
  split. reflexivity. intros addr _. reflexivity.
}
intro initEnded. destruct (negb initEnded) eqn:HnegInit.
- eapply weaken. apply ret. intros s Hprops. exfalso. destruct Hprops as (_ & _ & Hontra). subst initEnded.
  apply Bool.eq_true_not_negb_iff in HnegInit. congruence.
- eapply weaken. apply ret. intros s Hprops. simpl. destruct Hprops as (HnewShe & HlookupsEq & _). split.
  assumption. split. assumption. reflexivity.
Qed.

Lemma initStructure (kernStart kernEnd: paddr) P:
{{
  fun s => P s /\ Constants.kernelStructureTotalLength <= kernEnd - kernStart /\ kernEnd > kernStart /\ consistency s
            /\ (forall (addr: paddr), kernStart <= addr /\ addr < kernEnd -> lookup addr (memory s) beqAddr = None)
            /\ verticalSharing s /\ partitionsIsolation s /\ kernelDataIsolation s
}}
initStructure kernStart kernEnd
{{
  fun initSucc s => consistency1 s /\ noDupUsedPaddrList s /\ accessibleParentPaddrIsAccessibleIntoChild s
    /\ sharedBlockPointsToChild s /\ adressesRangePreservedIfOriginAndNextOk s /\ childsBlocksPropsInParent s
    /\ noChildImpliesAddressesNotShared s /\ verticalSharing s /\ partitionsIsolation s
    /\ initSucc = true
    /\ exists s0, P s0
        /\ currentPartition s = currentPartition s0
        /\ consistency s0 /\ verticalSharing s0 /\ partitionsIsolation s0 /\ kernelDataIsolation s0
}}.
Proof.
eapply bindRev.
{ (** MAL.eraseBlock **)
  eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.
}
intro isBlockErased. destruct (negb isBlockErased) eqn:HnegErased.
{
  apply Bool.negb_true_iff in HnegErased. eapply weaken. apply ret. intros s Hprops. simpl. exfalso.
  destruct Hprops as [s0 (Hprops & _ & _ & _ & Hcontra)]. destruct Hprops as (_ & _ & Hlen & _).
  specialize(Hcontra HnegErased). destruct Hcontra. lia.
}
apply Bool.negb_false_iff in HnegErased. eapply bindRev.
{ (** Internal.initBlocksStructure **)
  eapply weaken. apply initBlocksStructure. intros s Hprops. simpl.
  destruct Hprops as [s0 ((HP & HblockLargeEnough & HltEndStart & Hconsist & Hnone & HVS & HPI & HKDI) & HcurrPartEq
    & HnewNone & Huntouched & _)]. assert(kernEnd <= maxAddr) by (apply Hp).
  assert(Constants.kernelStructureTotalLength >= kernelStructureEntriesNb).
  {
    unfold Constants.kernelStructureTotalLength. unfold nextoffset. unfold scoffset. unfold sh1offset.
    unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
    pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn.
    pose proof Constants.maxIdxBiggerThanMinBlock. destruct (le_dec 16 maxIdx); try(lia). simpl.
    destruct (le_dec 24 maxIdx); try(lia). simpl. destruct (le_dec 25 maxIdx); try(lia). simpl. lia.
  }
  split; try(lia).
  instantiate(1 := fun s =>
    Constants.kernelStructureTotalLength <= kernEnd - kernStart /\ kernEnd > kernStart
    /\ (forall addr, In addr (getAllPaddrBlock kernStart kernEnd) -> lookup addr (memory s) beqAddr = None)
    /\ consistency s /\ verticalSharing s /\ partitionsIsolation s /\ kernelDataIsolation s
    /\ exists s0,
        consistency s0
        /\ currentPartition s = currentPartition s0
        /\ (forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
        /\ P s0
        /\ verticalSharing s0 /\ partitionsIsolation s0 /\ kernelDataIsolation s0).
  simpl. split. assumption. split. assumption. split. assumption.
  assert(HlookupsEq: forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intro addr. assert(HpropsOr: In addr (getAllPaddrBlock kernStart kernEnd)
      \/ ~ In addr (getAllPaddrBlock kernStart kernEnd)) by (apply classic).
    destruct HpropsOr as [HaddrIn | HaddrNotIn]; try(apply Huntouched; assumption).
    specialize(HnewNone addr HaddrIn). apply getAllPaddrBlockInclRev in HaddrIn. rewrite Hnone; intuition.
  }
  split.
  {
    unfold consistency in *. unfold consistency1 in *. unfold consistency2 in *.
    assert(nullAddrExists s).
    { (* BEGIN nullAddrExists s *)
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupsEq. intuition.
      (* END nullAddrExists *)
    }
    assert(wellFormedFstShadowIfBlockEntry s).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s0) by intuition.
      intros block HblockIsBE. unfold isBE in HblockIsBE. rewrite HlookupsEq in HblockIsBE. unfold isSHE.
      rewrite HlookupsEq. specialize(Hcons0 block HblockIsBE). assumption.
      (* END wellFormedFstShadowIfBlockEntry *)
    }
    assert(PDTIfPDFlag s).
    { (* BEGIN PDTIfPDFlag s *)
      assert(Hcons0: PDTIfPDFlag s0) by intuition.
      intros idPDchild sh1entryaddrBis Hcheck. unfold checkChild in Hcheck. unfold sh1entryAddr in Hcheck.
      rewrite HlookupsEq in Hcheck. rewrite HlookupsEq in Hcheck. unfold bentryAFlag. unfold bentryPFlag.
      unfold bentryStartAddr. unfold entryPDT. rewrite HlookupsEq.
      specialize(Hcons0 idPDchild sh1entryaddrBis Hcheck).
      destruct Hcons0 as (HAFlag & HPFlag & [startaddr (Hstart & HstartIsPDT)]). split. assumption. split.
      assumption. exists startaddr. split. assumption. unfold entryPDT in HstartIsPDT.
      destruct (lookup idPDchild (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite HlookupsEq. assumption.
      (* END PDTIfPDFlag *)
    }
    assert(AccessibleNoPDFlag s).
    { (* BEGIN AccessibleNoPDFlag s *)
      assert(Hcons0: AccessibleNoPDFlag s0) by intuition.
      intros block sh1entryaddrBis HblockIsBE Hsh1Bis HAFlag. unfold isBE in HblockIsBE.
      unfold sh1entryAddr in Hsh1Bis. unfold bentryAFlag in HAFlag. unfold sh1entryPDflag.
      rewrite HlookupsEq in *. specialize(Hcons0 block sh1entryaddrBis HblockIsBE Hsh1Bis HAFlag).
      assumption.
      (* END AccessibleNoPDFlag *)
    }
    assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0) by intuition.
      intros partition pdentry HlookupPart HbeqFirstNull. unfold isBE. unfold isFreeSlot. rewrite HlookupsEq in *.
      specialize(Hcons0 partition pdentry HlookupPart HbeqFirstNull).
      destruct Hcons0 as (HfirstIsBE & HfirstFree). split. assumption. unfold isFreeSlot in HfirstFree.
      destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite HlookupsEq.
      destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). rewrite HlookupsEq. assumption.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }
    assert(multiplexerIsPDT s).
    { (* BEGIN multiplexerIsPDT s *)
      unfold multiplexerIsPDT. unfold isPDT. rewrite HlookupsEq. intuition.
      (* END multiplexerIsPDT *)
    }
    assert(currentPartitionInPartitionsList s).
    { (* BEGIN currentPartitionInPartitionsList s *)
      assert(Hcons0: currentPartitionInPartitionsList s0) by intuition. unfold currentPartitionInPartitionsList.
      rewrite HcurrPartEq. rewrite getPartitionsEqLookup with multiplexer s s0; assumption.
      (* END currentPartitionInPartitionsList *)
    }
    assert(wellFormedShadowCutIfBlockEntry s).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s0) by intuition.
      intros block HblockIsBE. unfold isBE in HblockIsBE. unfold isSCE. rewrite HlookupsEq in *.
      specialize(Hcons0 block HblockIsBE). destruct Hcons0 as [scentryaddr Hsce]. exists scentryaddr.
      rewrite HlookupsEq. assumption.
      (* END wellFormedShadowCutIfBlockEntry *)
    }
    assert(BlocksRangeFromKernelStartIsBE s).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by intuition. intros kernel blockidx HkernIsKS Hblockidx.
      unfold isKS in HkernIsKS. unfold isBE. rewrite HlookupsEq in *.
      specialize(Hcons0 kernel blockidx HkernIsKS Hblockidx). assumption.
      (* END BlocksRangeFromKernelStartIsBE *)
    }
    assert(KernelStructureStartFromBlockEntryAddrIsKS s).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s*)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0) by intuition.
      intros block blockidx HblockIsBE Hblockidx. unfold isBE in HblockIsBE. unfold bentryBlockIndex in Hblockidx.
      unfold isKS. rewrite HlookupsEq in *. specialize(Hcons0 block blockidx HblockIsBE Hblockidx). assumption.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }
    assert(sh1InChildLocationIsBE s).
    { (* BEGIN sh1InChildLocationIsBE s*)
      assert(Hcons0: sh1InChildLocationIsBE s0) by intuition.
      intros sh1entryaddrBis sh1entryBis HlookupSh1Bis HbeqInChildNull. unfold isBE. rewrite HlookupsEq in *.
      specialize(Hcons0 sh1entryaddrBis sh1entryBis HlookupSh1Bis HbeqInChildNull). assumption.
      (* END sh1InChildLocationIsBE *)
    }
    assert(StructurePointerIsKS s).
    { (* BEGIN StructurePointerIsKS s *)
      assert(Hcons0: StructurePointerIsKS s0) by intuition. intros partition pdentry HlookupPart HbeqStructNull.
      unfold isKS. rewrite HlookupsEq in *. specialize(Hcons0 partition pdentry HlookupPart HbeqStructNull).
      assumption.
      (* END StructurePointerIsKS *)
    }
    assert(NextKSIsKS s).
    { (* BEGIN NextKSIsKS s *)
      assert(Hcons0: NextKSIsKS s0) by intuition. intros kernel nextKSaddr nextKS HkernIsKS HnextKSAddr HnextKS.
      unfold isKS in *. unfold nextKSAddr in HnextKSAddr. unfold nextKSentry in HnextKS. rewrite HlookupsEq in *.
      specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextKSAddr HnextKS). assumption.
      (* END NextKSIsKS *)
    }
    assert(NextKSOffsetIsPADDR s).
    { (* BEGIN NextKSOffsetIsPADDR s *)
      assert(Hcons0: NextKSOffsetIsPADDR s0) by intuition. intros kern nextksaddr HkernIsKS HnextIsNext.
      unfold isKS in HkernIsKS. unfold nextKSAddr in HnextIsNext. unfold isPADDR. rewrite HlookupsEq in *.
      specialize(Hcons0 kern nextksaddr HkernIsKS HnextIsNext). assumption.
      (* END NextKSOffsetIsPADDR *)
    }
    assert(NoDupInFreeSlotsList s).
    { (* BEGIN NoDupInFreeSlotsList s *)
      assert(Hcons0: NoDupInFreeSlotsList s0) by intuition. intros partition pdentry HlookupPart.
      rewrite HlookupsEq in *. rewrite getFreeSlotsListEqLookup with partition s s0; try(assumption).
      specialize(Hcons0 partition pdentry HlookupPart). assumption.
      (* END NoDupInFreeSlotsList *)
    }
    assert(freeSlotsListIsFreeSlot s).
    { (* BEGIN freeSlotsListIsFreeSlot s *)
      assert(Hcons0: freeSlotsListIsFreeSlot s0) by intuition.
      intros partition freeslot optionfreeslotslist freeslotslist HpartIsPDT Hoption HslotsList HbeqFreeNull.
      rewrite getFreeSlotsListEqLookup with partition s s0 in Hoption; try(assumption).
      unfold isPDT in HpartIsPDT. unfold isFreeSlot. rewrite HlookupsEq in *.
      specialize(Hcons0 partition freeslot optionfreeslotslist freeslotslist HpartIsPDT Hoption HslotsList
        HbeqFreeNull). unfold isFreeSlot in Hcons0.
      destruct (lookup freeslot (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite HlookupsEq. destruct (lookup (CPaddr (freeslot + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). rewrite HlookupsEq. assumption.
      (* END freeSlotsListIsFreeSlot *)
    }
    assert(DisjointFreeSlotsLists s).
    { (* BEGIN DisjointFreeSlotsLists s *)
      assert(Hcons0: DisjointFreeSlotsLists s0) by intuition.
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2. unfold isPDT in *.
      rewrite getFreeSlotsListEqLookup with part1 s s0; try(assumption).
      rewrite getFreeSlotsListEqLookup with part2 s s0; try(assumption). rewrite HlookupsEq in *.
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2). assumption.
      (* END DisjointFreeSlotsLists *)
    }
    assert(inclFreeSlotsBlockEntries s).
    { (* BEGIN inclFreeSlotsBlockEntries s *)
      assert(Hcons0: inclFreeSlotsBlockEntries s0) by intuition. intros partition HpartIsPDT.
      unfold isPDT in *. rewrite HlookupsEq in *. specialize(Hcons0 partition HpartIsPDT).
      rewrite getFreeSlotsListEqLookup with partition s s0; try(assumption).
      rewrite getKSEntriesEqLookup with partition s s0; assumption.
      (* END inclFreeSlotsBlockEntries *)
    }
    assert(DisjointKSEntries s).
    { (* BEGIN DisjointKSEntries s *)
      assert(Hcons0: DisjointKSEntries s0) by intuition.
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2. unfold isPDT in *. rewrite HlookupsEq in *.
      rewrite getKSEntriesEqLookup with part1 s s0; try(assumption).
      rewrite getKSEntriesEqLookup with part2 s s0; try(assumption).
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2). assumption.
      (* END DisjointKSEntries *)
    }
    assert(noDupPartitionTree s).
    { (* BEGIN noDupPartitionTree s *)
      assert(Hcons0: noDupPartitionTree s0) by intuition. unfold noDupPartitionTree in *.
      rewrite getPartitionsEqLookup with multiplexer s s0; assumption.
      (* END noDupPartitionTree *)
    }
    assert(isParent s).
    { (* BEGIN isParent s *)
      assert(Hcons0: isParent s0) by intuition. intros partition pdparent HparentIsPart HpartIsChild.
      unfold pdentryParent. rewrite HlookupsEq.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0 in HpartIsChild; try(assumption).
      specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). assumption.
      (* END isParent *)
    }
    assert(isChild s).
    { (* BEGIN isChild s *)
      assert(Hcons0: isChild s0) by intuition. intros partition pdparent HpartIsPart HparentIsParent.
      unfold pdentryParent in *. rewrite HlookupsEq in *.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0; try(assumption).
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent). assumption.
      (* END isChild *)
    }
    assert(noDupKSEntriesList s).
    { (* BEGIN noDupKSEntriesList s *)
      assert(Hcons0: noDupKSEntriesList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition HpartIsPDT).
      rewrite getKSEntriesEqLookup with partition s s0; assumption.
      (* END noDupKSEntriesList *)
    }
    assert(noDupMappedBlocksList s).
    { (* BEGIN noDupMappedBlocksList s *)
      assert(Hcons0: noDupMappedBlocksList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition HpartIsPDT).
      rewrite getMappedBlocksEqLookup with partition s s0; assumption.
      (* END noDupMappedBlocksList *)
    }
    assert(wellFormedBlock s).
    { (* BEGIN wellFormedBlock s *)
      assert(Hcons0: wellFormedBlock s0) by intuition. intros block startaddr endaddr HPFlag Hstart Hend.
      unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupsEq in *.
      specialize(Hcons0 block startaddr endaddr HPFlag Hstart Hend). assumption.
      (* END wellFormedBlock *)
    }
    assert(parentOfPartitionIsPartition s).
    { (* BEGIN parentOfPartitionIsPartition s *)
      assert(Hcons0: parentOfPartitionIsPartition s0) by intuition. intros partition pdentry HlookupPart.
      rewrite HlookupsEq in *. specialize(Hcons0 partition pdentry HlookupPart).
      rewrite getPartitionsEqLookup with multiplexer s s0; assumption.
      (* END parentOfPartitionIsPartition *)
    }
    assert(NbFreeSlotsISNbFreeSlotsInList s).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0) by intuition.
      intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. unfold pdentryNbFreeSlots in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree).
      rewrite getFreeSlotsListEqLookup with partition s s0; assumption.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }
    assert(maxNbPrepareIsMaxNbKernels s).
    { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by intuition. intros partition kernList HkernList.
      rewrite isListOfKernelsEqLookup with kernList partition s s0 in HkernList; try(assumption).
      specialize(Hcons0 partition kernList HkernList). assumption.
      (* END maxNbPrepareIsMaxNbKernels *)
    }
    assert(blockInChildHasAtLeastEquivalentBlockInParent s).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0) by intuition.
      intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild Hstart Hend
        HPFlag. rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0 in HchildIsChild; try(assumption).
      rewrite getMappedBlocksEqLookup with child s s0 in HblockMappedChild; try(assumption).
      rewrite getMappedBlocksEqLookup with pdparent s s0; try(assumption). unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite HlookupsEq in *.
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        Hstart Hend HPFlag). destruct Hcons0 as [blockParent [startParent [endParent Hcons0]]].
      exists blockParent. exists startParent. exists endParent. rewrite HlookupsEq. assumption.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }
    assert(partitionTreeIsTree s).
    { (* BEGIN  partitionTreeIsTrees *)
      assert(Hcons0: partitionTreeIsTree s0) by intuition.
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsparent HparentsList.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HchildIsPart; try(assumption).
      unfold pdentryParent in *. rewrite HlookupsEq in *.
      rewrite isParentsListEqLookup with parentsList pdparent s s0 in HparentsList; try(assumption).
      specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsparent HparentsList).
      assumption.
      (* END partitionTreeIsTree *)
    }
    assert(kernelEntriesAreValid s).
    { (* BEGIN kernelEntriesAreValid s *)
      assert(Hcons0: kernelEntriesAreValid s0) by intuition. intros kernel idx HkernisKS Hidx.
      unfold isKS in *. unfold isBE. rewrite HlookupsEq in *. specialize(Hcons0 kernel idx HkernisKS Hidx).
      assumption.
      (* END kernelEntriesAreValid *)
    }
    assert(nextKernelIsValid s).
    { (* BEGIN nextKernelIsValid s *)
      assert(Hcons0: nextKernelIsValid s0) by intuition. intros kernel HkernisKS. unfold isKS in *.
      rewrite HlookupsEq in *. specialize(Hcons0 kernel HkernisKS). split. apply Hcons0.
      destruct Hcons0 as (_ & [nextAddr Hcons0]). exists nextAddr. rewrite HlookupsEq.
      split; try(apply Hcons0). destruct Hcons0 as (Hcons0 & _). intro Hp. rewrite HlookupsEq. apply Hcons0.
      (* END nextKernelIsValid *)
    }
    assert(noDupListOfKerns s).
    { (* BEGIN noDupListOfKerns s *)
      assert(Hcons0: noDupListOfKerns s0) by intuition. intros partition kernList HkernList.
      rewrite isListOfKernelsEqLookup with kernList partition s s0 in HkernList; try(assumption).
      specialize(Hcons0 partition kernList HkernList). assumption.
      (* END noDupListOfKerns *)
    }
    assert(MPUsizeIsBelowMax s).
    { (* BEGIN MPUsizeIsBelowMax s *)
      assert(Hcons0: MPUsizeIsBelowMax s0) by intuition. intros partition MPUlist HMPU.
      unfold pdentryMPU in *. rewrite HlookupsEq in *. specialize(Hcons0 partition MPUlist HMPU). assumption.
      (* END MPUsizeIsBelowMax *)
    }
    assert(originIsParentBlocksStart s).
    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s0) by intuition.
      intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getMappedBlocksEqLookup with partition s s0 in HblockMapped; try(assumption).
      unfold scentryOrigin in *. rewrite HlookupsEq in *.
      specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
        Horigin). destruct Hcons0 as (Hleft & Hright). unfold bentryStartAddr. rewrite HlookupsEq.
      split; try(assumption). intro HbeqPartRoot. specialize(Hleft HbeqPartRoot).
      destruct Hleft as [blockParent Hleft]. exists blockParent. rewrite HlookupsEq.
      rewrite getAllPaddrAuxEqLookup with [block] s s0; try(assumption).
      rewrite getAllPaddrAuxEqLookup with [blockParent] s s0; try(assumption).
      rewrite getMappedBlocksEqLookup with (parent pdentry) s s0; assumption.
      (* END originIsParentBlocksStart *)
    }
    assert(nextImpliesBlockWasCut s).
    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s0) by intuition.
      intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped Hend Hsce
        HbeqNextNull Hnext HbeqPartRoot.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getMappedBlocksEqLookup with partition s s0 in HblockMapped; try(assumption).
      unfold bentryEndAddr in *. unfold scentryNext in *. rewrite HlookupsEq in *.
      specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
        Hend Hsce HbeqNextNull Hnext HbeqPartRoot). destruct Hcons0 as [blockParent [endParent Hcons0]].
      exists blockParent. exists endParent. rewrite HlookupsEq.
      rewrite getAllPaddrAuxEqLookup with [block] s s0; try(assumption).
      rewrite getAllPaddrAuxEqLookup with [blockParent] s s0; try(assumption).
      rewrite getMappedBlocksEqLookup with (parent pdentry) s s0; assumption.
      (* END nextImpliesBlockWasCut *)
    }
    assert(blocksAddressesTypes s).
    { (* BEGIN blocksAddressesTypes s *)
      assert(Hcons0: blocksAddressesTypes s0) by intuition. intros block startaddr endaddr Hstart Hend HPDchild.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold isKS in *. unfold isPDT in *.
      unfold sh1entryPDchild in *. rewrite HlookupsEq in *.
      specialize(Hcons0 block startaddr endaddr Hstart Hend HPDchild). destruct Hcons0 as [HKS | [HPDT | HnoneBis]].
      - left. split. apply HKS. intro addr. unfold isBE. unfold isSHE. unfold isSCE. rewrite HlookupsEq.
        apply HKS.
      - right. left. split. apply HPDT. intro addr. unfold isBE. unfold isSHE. unfold isSCE. rewrite HlookupsEq.
        apply HPDT.
      - right. right. intro addr. unfold isBE. unfold isSHE. unfold isSCE. rewrite HlookupsEq. apply HnoneBis.
      (* END blocksAddressesTypes *)
    }
    assert(notPDTIfNotPDflag s).
    { (* BEGIN notPDTIfNotPDflag s *)
      assert(Hcons0: notPDTIfNotPDflag s0) by intuition.
      intros block startaddr sh1entryaddrBis Hstart Hsh1 HPDFlag HPDchild. unfold bentryStartAddr in *.
      unfold sh1entryAddr in *. unfold sh1entryPDflag in *. unfold sh1entryPDchild in *. unfold isPDT.
      rewrite HlookupsEq in *. specialize(Hcons0 block startaddr sh1entryaddrBis Hstart Hsh1 HPDFlag HPDchild).
      assumption.
      (* END notPDTIfNotPDflag *)
    }
    assert(nextKernAddrIsInSameBlock s).
    { (* BEGIN nextKernAddrIsInSameBlock s *)
      assert(Hcons0: nextKernAddrIsInSameBlock s0) by intuition.
      intros block kernel startaddr endaddr Hstart Hend HkernIsKS HnextInBlock. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. unfold isKS in *. rewrite HlookupsEq in *.
      specialize(Hcons0 block kernel startaddr endaddr Hstart Hend HkernIsKS HnextInBlock). assumption.
      (* END nextKernAddrIsInSameBlock *)
    }
    assert(noDupUsedPaddrList s).
    { (* BEGIN noDupUsedPaddrList s *)
      assert(Hcons0: noDupUsedPaddrList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition HpartIsPDT).
      rewrite getUsedPaddrEqLookup with partition s s0; assumption.
      (* END noDupUsedPaddrList *)
    }
    assert(accessibleParentPaddrIsAccessibleIntoChild s).
    { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
      assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s0) by intuition.
      intros pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0 in HchildIsChild; try(assumption).
      rewrite getAccessibleMappedPaddrEqLookup with pdparent s s0 in HaddrAccParent; try(assumption).
      rewrite getMappedPaddrEqLookup with child s s0 in HaddrMappedChild; try(assumption).
      specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild).
      rewrite getAccessibleMappedPaddrEqLookup with child s s0; assumption.
      (* END accessibleParentPaddrIsAccessibleIntoChild *)
    }
    assert(sharedBlockPointsToChild s).
    { (* BEGIN sharedBlockPointsToChild s *)
      assert(Hcons0: sharedBlockPointsToChild s0) by intuition.
      intros pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParent HblockParentMapped Hsh1Bis.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0 in HchildIsChild; try(assumption).
      rewrite getUsedPaddrEqLookup with child s s0 in HaddrUsedChild; try(assumption).
      rewrite getAllPaddrAuxEqLookup with [blockParent] s s0 in HaddrInBlockParent; try(assumption).
      rewrite getMappedBlocksEqLookup with pdparent s s0 in HblockParentMapped; try(assumption).
      unfold sh1entryAddr in *. unfold sh1entryPDchild. unfold sh1entryPDflag. rewrite HlookupsEq in *.
      specialize(Hcons0 pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParent HblockParentMapped Hsh1Bis). assumption.
      (* END sharedBlockPointsToChild *)
    }
    assert(adressesRangePreservedIfOriginAndNextOk s).
    { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
      assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0) by intuition.
      intros partition pdentry block scentryaddr start endaddr HpartIsPart HblockMapped HblockIsBE Hstart Hend
        HPFlag Hsce Horigin Hnext HlookupPart HbeqPartRoot.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getMappedBlocksEqLookup with partition s s0 in HblockMapped; try(assumption). unfold isBE in *.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. unfold scentryOrigin in *.
      unfold scentryNext in *. rewrite HlookupsEq in *.
      rewrite getMappedBlocksEqLookup with (parent pdentry) s s0; try(assumption).
      specialize(Hcons0 partition pdentry block scentryaddr start endaddr HpartIsPart HblockMapped HblockIsBE
        Hstart Hend HPFlag Hsce Horigin Hnext HlookupPart HbeqPartRoot). destruct Hcons0 as [blockParent Hcons0].
      exists blockParent. rewrite HlookupsEq. assumption.
      (* END adressesRangePreservedIfOriginAndNextOk *)
    }
    assert(childsBlocksPropsInParent s).
    { (* BEGIN childsBlocksPropsInParent s *)
      assert(Hcons0: childsBlocksPropsInParent s0) by intuition.
      intros child parentPart blockChild startChild endChild blockParent startParent endParent HparentIsPart
        HchildIsChild HchildMapped HstartChild HendChild HPFlagChild HparentMapped HparentStart HparentEnd
        HPFlagParent HleStart HgeEnd.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with parentPart s s0 in HchildIsChild; try(assumption).
      rewrite getMappedBlocksEqLookup with child s s0 in HchildMapped; try(assumption).
      rewrite getMappedBlocksEqLookup with parentPart s s0 in HparentMapped; try(assumption).
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. unfold checkChild.
      unfold sh1entryPDchild. unfold sh1entryInChildLocation. unfold bentryAFlag. unfold isBE.
      rewrite HlookupsEq in *. specialize(Hcons0 child parentPart blockChild startChild endChild blockParent
        startParent endParent HparentIsPart HchildIsChild HchildMapped HstartChild HendChild HPFlagChild
        HparentMapped HparentStart HparentEnd HPFlagParent HleStart HgeEnd).
      destruct Hcons0 as (HcheckChild & HPDChild & HinChildLoc & HAFlagParent). unfold checkChild in *.
      unfold sh1entryPDchild in *. unfold sh1entryInChildLocation in *. unfold bentryAFlag in *.
      split; try(split; try(split)).
      - destruct (lookup blockParent (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
        rewrite HlookupsEq. assumption.
      - intro childGlobalID. rewrite HlookupsEq. apply HPDChild.
      - intros blockIDInChild HchildLoc. rewrite HlookupsEq in HchildLoc. apply HinChildLoc.
        destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). rewrite HlookupsEq in HchildLoc. assumption.
      - assumption.
      (* END childsBlocksPropsInParent *)
    }
    assert(noChildImpliesAddressesNotShared s).
    { (* BEGIN noChildImpliesAddressesNotShared s *)
      assert(Hcons0: noChildImpliesAddressesNotShared s0) by intuition.
      intros partition pdentry block sh1entryaddrBis HpartIsPart HlookupPart HblockMapped Hsh1Bis HPDChild child
        addr HchildIsChild HaddrInBlock.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getMappedBlocksEqLookup with partition s s0 in HblockMapped; try(assumption).
      rewrite getChildrenEqLookup with partition s s0 in HchildIsChild; try(assumption).
      rewrite getAllPaddrAuxEqLookup with [block] s s0 in HaddrInBlock; try(assumption).
      rewrite getMappedPaddrEqLookup with child s s0; try(assumption). unfold sh1entryPDchild in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition pdentry block sh1entryaddrBis HpartIsPart HlookupPart
        HblockMapped Hsh1Bis HPDChild child addr HchildIsChild HaddrInBlock). assumption.
      (* END noChildImpliesAddressesNotShared *)
    }
    assert(kernelsAreNotAccessible s).
    { (* BEGIN kernelsAreNotAccessible s *)
      assert(Hcons0: kernelsAreNotAccessible s0) by intuition. intros block startaddr Hstart HstartIsKS.
      unfold bentryStartAddr in *. unfold isKS in *. unfold bentryAFlag. rewrite HlookupsEq in *.
      specialize(Hcons0 block startaddr Hstart HstartIsKS). assumption.
      (* END kernelsAreNotAccessible *)
    }
    assert(blockBelongsToAPart s).
    { (* BEGIN blockBelongsToAPart s *)
      assert(Hcons0: blockBelongsToAPart s0) by intuition. intros block HblockIsBE. unfold isBE in HblockIsBE.
      rewrite HlookupsEq in *. specialize(Hcons0 block HblockIsBE). destruct Hcons0 as [part Hcons0]. exists part.
      rewrite getPartitionsEqLookup with multiplexer s s0; try(assumption).
      rewrite getMappedBlocksEqLookup with part s s0; assumption.
      (* END blockBelongsToAPart *)
    }
    assert(PDflagMeansNoChild s).
    { (* BEGIN PDflagMeansNoChild s *)
      assert(Hcons0: PDflagMeansNoChild s0) by intuition. intros block HblockIsBE. unfold isBE in HblockIsBE.
      rewrite HlookupsEq in *. specialize(Hcons0 block HblockIsBE). unfold sh1entryPDflag. unfold sh1entryPDchild.
      rewrite HlookupsEq. assumption.
      (* END PDflagMeansNoChild *)
    }
    intuition.
  }
  split.
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild.
    rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
    rewrite getChildrenEqLookup with pdparent s s0 in HchildIsChild; try(assumption).
    rewrite getUsedPaddrEqLookup with child s s0; try(assumption).
    rewrite getMappedPaddrEqLookup with pdparent s s0; try(assumption).
    specialize(HVS pdparent child HparentIsPart HchildIsChild). assumption.
    (* END verticalSharing *)
  }
  split.
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
    rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
    rewrite getChildrenEqLookup with pdparent s s0 in Hchild1IsChild; try(assumption).
    rewrite getChildrenEqLookup with pdparent s s0 in Hchild2IsChild; try(assumption).
    rewrite getUsedPaddrEqLookup with child1 s s0; try(assumption).
    rewrite getUsedPaddrEqLookup with child2 s s0; try(assumption).
    specialize(HPI pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
    assumption.
    (* END partitionsIsolation *)
  }
  split.
  { (* BEGIN kernelDataIsolation s *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart.
    rewrite getPartitionsEqLookup with multiplexer s s0 in Hpart1IsPart; try(assumption).
    rewrite getPartitionsEqLookup with multiplexer s s0 in Hpart2IsPart; try(assumption).
    rewrite getAccessibleMappedPaddrEqLookup with part1 s s0; try(assumption).
    rewrite getConfigPaddrEqLookup with part2 s s0; try(assumption).
    specialize(HKDI part1 part2 Hpart1IsPart Hpart2IsPart). assumption.
    (* END kernelDataIsolation *)
  }
  exists s0. intuition.
}
intro. eapply bindRev.
{ (** Internal.initSh1Structure **)
  eapply weaken. apply initSh1Structure. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as (HnewBlocks & HlastBlock & [s1 ((HblockLargeEnough & HltEndStart & _) & _)] & _). split.
  {
    unfold Constants.kernelStructureTotalLength in *. unfold nextoffset in *. unfold scoffset in HblockLargeEnough.
    unfold sh1offset in HblockLargeEnough. unfold blkoffset in *. unfold CIndex in HblockLargeEnough.
    unfold sh1offset. unfold blkoffset. unfold CIndex.
    destruct (le_dec 0 maxIdx); try(lia). simpl in *. pose proof maxIdxBiggerThanNbOfKernels.
    destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn in HblockLargeEnough. cbn.
    pose proof Constants.maxIdxBiggerThanMinBlock. destruct (le_dec 16 maxIdx); try(lia). simpl in *.
    destruct (le_dec 24 maxIdx); try(lia). simpl in *. destruct (le_dec 25 maxIdx); try(lia). simpl in *.
    assert(kernEnd <= maxAddr) by (apply Hp). lia.
  }
  split.
  {
    assert(Hindex: i (CIndex 0) = 0).
    { unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl. reflexivity. }
    assert(HltZeroKernEntries: CIndex 0 < kernelStructureEntriesNb - 1).
    { rewrite Hindex. cbn. lia. }
    specialize(HnewBlocks (CIndex 0) HltZeroKernEntries). destruct HnewBlocks as [l Hlookup]. unfold isKS.
    rewrite Hindex in Hlookup. rewrite Nat.add_0_r in Hlookup.
    assert(Heq: CPaddr kernStart = kernStart).
    {
       unfold CPaddr. assert(kernStart <= maxAddr) by (apply Hp). destruct (le_dec kernStart maxAddr); try(lia).
       destruct kernStart. simpl. f_equal. apply proof_irrelevance.
    }
    rewrite Heq in Hlookup. rewrite Hlookup. simpl. unfold zero. reflexivity.
  }
  intros kernIdx HltIdxKernEntries. destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxs.
  - apply Nat.eqb_eq in HbeqIdxs. rewrite HbeqIdxs.
    replace (kernStart + (kernelStructureEntriesNb - 1)) with (kernStart + kernelStructureEntriesNb - 1); try(lia).
    unfold bentryBlockIndex. destruct HlastBlock as [l HlookupLast]. rewrite HlookupLast.
    cbn -[kernelStructureEntriesNb]. apply DTL.index_eq_i. rewrite HbeqIdxs. unfold CIndex.
    pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). cbn.
    reflexivity.
  - apply Nat.eqb_neq in HbeqIdxs. assert(HltIdxKernEntriesBis: kernIdx < kernelStructureEntriesNb-1) by lia.
    specialize(HnewBlocks kernIdx HltIdxKernEntriesBis). destruct HnewBlocks as [l Hlookup]. unfold bentryBlockIndex.
    rewrite Hlookup. simpl. reflexivity.
}
intro. eapply bindRev.
{ (** Internal.initSCStructure **)
  eapply weaken. apply initSCStructure. intros s Hprops. simpl.
  destruct Hprops as (HnewShe & [s2 ((HnewBE & HlastBlock & [s1 ((HblockLargeEnough & HgtEndStart & HlookupNone &
    Hconsists1 & HVS & HPI & HKDI & HPs0) & Hcurrs2 & Hlookups1Eq)] & _) & Hcurrs & Hlookups2Eq)] & _).
  assert(HlookupsEq: forall addr,
    (forall kernIdx : index, kernIdx <= kernelStructureEntriesNb - 1 -> addr <> CPaddr (kernStart + kernIdx))
    -> (forall kernIdx : index, kernIdx < kernelStructureEntriesNb
        -> addr <> CPaddr (kernStart + kernIdx + sh1offset))
    -> lookup addr (memory s) beqAddr = lookup addr (memory s1) beqAddr).
  {
    intros addr HaddrNotBE HaddrNotSHE. specialize(Hlookups1Eq addr HaddrNotBE).
    specialize(Hlookups2Eq addr HaddrNotSHE). rewrite Hlookups2Eq. assumption.
  }
  assert(KstartIsKSs2: isKS kernStart s2).
  {
    assert(Hindex: i (CIndex 0) = 0).
    { unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl. reflexivity. }
    assert(HltZeroKernEntries: CIndex 0 < kernelStructureEntriesNb - 1).
    { rewrite Hindex. cbn. lia. }
    specialize(HnewBE (CIndex 0) HltZeroKernEntries). destruct HnewBE as [l Hlookup]. unfold isKS.
    rewrite Hindex in Hlookup. rewrite Nat.add_0_r in Hlookup.
    assert(Heq: CPaddr kernStart = kernStart).
    {
       unfold CPaddr. assert(kernStart <= maxAddr) by (apply Hp). destruct (le_dec kernStart maxAddr); try(lia).
       destruct kernStart. simpl. f_equal. apply proof_irrelevance.
    }
    rewrite Heq in Hlookup. rewrite Hlookup. simpl. unfold zero. reflexivity.
  }
  assert(isKS kernStart s).
  {
    unfold isKS.
    assert(HkernNotSce: forall kernIdx : index, kernIdx < kernelStructureEntriesNb
            -> kernStart <> CPaddr (kernStart + kernIdx + sh1offset)).
    {
      intros kernIdx HltIdxKernEntries. unfold CPaddr.
      assert(kernIdx + sh1offset <= Constants.kernelStructureTotalLength).
      {
        unfold Constants.kernelStructureTotalLength. unfold nextoffset. unfold scoffset. unfold sh1offset.
        unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
        pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn in *.
        pose proof Constants.maxIdxBiggerThanMinBlock. destruct (le_dec 16 maxIdx); try(lia). simpl.
        destruct (le_dec 24 maxIdx); try(lia). simpl. destruct (le_dec 25 maxIdx); try(lia). simpl. lia.
      }
      assert(kernEnd <= maxAddr) by (apply Hp). destruct (le_dec (kernStart + kernIdx + sh1offset) maxAddr); try(lia).
      intro Hcontra. assert(Hfalse: p kernStart = kernStart + kernIdx + sh1offset).
      { rewrite Hcontra at 1. simpl. reflexivity. }
      unfold sh1offset in Hfalse. unfold blkoffset in *. unfold CIndex in Hfalse.
      destruct (le_dec 0 maxIdx); try(lia). simpl in Hfalse. pose proof maxIdxBiggerThanNbOfKernels.
      destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl in Hfalse. lia.
    }
    specialize(Hlookups2Eq kernStart HkernNotSce). rewrite Hlookups2Eq. assumption.
  }
  split.
  - instantiate(1 := fun s => Constants.kernelStructureTotalLength <= kernEnd - kernStart /\ kernEnd > kernStart
      /\ isKS kernStart s
      /\ exists s2,
          (forall addr,
            (forall kernIdx : index,
             kernIdx < kernelStructureEntriesNb -> addr <> CPaddr (kernStart + kernIdx + sh1offset))
            -> lookup addr (memory s) beqAddr = lookup addr (memory s2) beqAddr)
          /\ currentPartition s = currentPartition s2
          /\ (forall kernIdx : index,
                kernIdx < kernelStructureEntriesNb
                -> lookup (CPaddr (kernStart + kernIdx + sh1offset)) (memory s) beqAddr =
                      Some (SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |}))
          /\ (forall kernIdx : index,
                kernIdx < kernelStructureEntriesNb - 1
                -> exists l : kernIdx < kernelStructureEntriesNb,
                    lookup (CPaddr (kernStart + kernIdx)) (memory s2) beqAddr =
                    Some
                      (BE
                         {|
                           read := false;
                           write := false;
                           exec := false;
                           present := false;
                           accessible := false;
                           blockindex := kernIdx;
                           blockrange := CBlock nullAddr (CPaddr (kernStart + kernIdx + 1));
                           Hidx := l
                         |}))
          /\ (exists l : CIndex (kernelStructureEntriesNb - 1) < kernelStructureEntriesNb,
                lookup (CPaddr (kernStart + kernelStructureEntriesNb - 1)) (memory s2) beqAddr =
                Some
                  (BE
                     {|
                       read := false;
                       write := false;
                       exec := false;
                       present := false;
                       accessible := false;
                       blockindex := CIndex (kernelStructureEntriesNb - 1);
                       blockrange := CBlock nullAddr nullAddr;
                       Hidx := l
                     |}))
          /\ exists s1,
              (forall addr,
                (forall kernIdx : index, kernIdx <= kernelStructureEntriesNb - 1
                    -> addr <> CPaddr (kernStart + kernIdx))
                -> (forall kernIdx : index, kernIdx < kernelStructureEntriesNb
                    -> addr <> CPaddr (kernStart + kernIdx + sh1offset))
                -> lookup addr (memory s) beqAddr = lookup addr (memory s1) beqAddr)
              /\ (forall addr,
                    (forall kernIdx : index,
                     kernIdx <= kernelStructureEntriesNb - 1 -> addr <> CPaddr (kernStart + kernIdx))
                    -> lookup addr (memory s2) beqAddr = lookup addr (memory s1) beqAddr)
              /\ (forall addr, In addr (getAllPaddrBlock kernStart kernEnd) -> lookup addr (memory s1) beqAddr = None)
              /\ currentPartition s2 = currentPartition s1
              /\ consistency s1
              /\ verticalSharing s1 /\ partitionsIsolation s1 /\ kernelDataIsolation s1
              /\ exists s0,
                  consistency s0 /\ currentPartition s1 = currentPartition s0
                  /\ (forall addr : paddr, lookup addr (memory s1) beqAddr = lookup addr (memory s0) beqAddr)
                  /\ P s0 /\ verticalSharing s0 /\ partitionsIsolation s0 /\ kernelDataIsolation s0
    ).
    simpl. split. assumption. split. assumption. split. assumption. exists s2. intuition. exists s1. intuition.
  - unfold Constants.kernelStructureTotalLength in *. unfold nextoffset in *. unfold scoffset in HblockLargeEnough.
    unfold scoffset. unfold sh1offset in HblockLargeEnough. unfold blkoffset in *.
    unfold CIndex in HblockLargeEnough. unfold sh1offset. unfold blkoffset. unfold CIndex.
    destruct (le_dec 0 maxIdx); try(lia). simpl in *. pose proof maxIdxBiggerThanNbOfKernels.
    destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). cbn in HblockLargeEnough. cbn.
    pose proof Constants.maxIdxBiggerThanMinBlock. destruct (le_dec 16 maxIdx); try(lia). simpl in *.
    destruct (le_dec 24 maxIdx); try(lia). simpl in *. destruct (le_dec 25 maxIdx); try(lia). simpl in *. split.
    {
      assert(kernEnd <= maxAddr) by (apply Hp). lia.
    }
    split. assumption. intros kernIdx HltIdxKernEntries. unfold bentryBlockIndex.
    assert(HlookupIdxEq: lookup (CPaddr (kernStart + kernIdx)) (memory s) beqAddr
        = lookup (CPaddr (kernStart + kernIdx)) (memory s2) beqAddr).
    {
      apply Hlookups2Eq. intros kernIdx2 HltIdx2KernEntries. unfold sh1offset. unfold blkoffset. unfold CIndex.
      destruct (le_dec 0 maxIdx); try(lia). cbn in *. pose proof Constants.maxIdxBiggerThanMinBlock.
      destruct (le_dec 8 maxIdx); try(lia). simpl. unfold CPaddr. assert(kernEnd <= maxAddr) by (apply Hp).
      destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia).
      destruct (le_dec (kernStart + kernIdx2 + 8) maxAddr); try(lia). intro Hcontra. injection Hcontra as Hcontra.
      lia.
    }
    rewrite HlookupIdxEq. destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxLast.
    + apply Nat.eqb_eq in HbeqIdxLast. rewrite HbeqIdxLast in *.
      replace (kernStart + (kernelStructureEntriesNb - 1)) with (kernStart + kernelStructureEntriesNb - 1);
        try(cbn; lia). destruct HlastBlock as [llast HlookupLast]. rewrite HlookupLast. simpl. unfold CIndex.
      destruct (le_dec 7 maxIdx); try(lia). apply DTL.index_eq_i. rewrite HbeqIdxLast. cbn. reflexivity.
    + apply Nat.eqb_neq in HbeqIdxLast. assert(HidxNotLast: kernIdx < 7).
      { cbn in *. lia. }
      specialize(HnewBE kernIdx HidxNotLast). destruct HnewBE as [lidx HlookupIdx]. rewrite HlookupIdx. simpl.
      reflexivity.
}
intro. eapply bindRev.
{ (** MAL.writeNextFromKernelStructureStartLight **)
  eapply weaken. apply writeNextFromKernelStructureStartLight. intros s Hprops. simpl. apply Hprops.
}
intro. eapply weaken. apply ret. intros s Hprops. simpl. destruct Hprops as [s3 ((HnewSce & [s2 ((HblockLargeEnough &
  HgtEndStart & HstartIsKSs2 & [s1 (Hlookups1Eq & Hcurrs2 & HnewShe & HnewBE & HlastBlock & [s0 (Hlookups2s0Eq &
  Hlookups1s0Eq & HlookupNones0 & Hcurrs1 & Hconsists0 & HVSs0 & HPIs0 & HKDIs0 & [sAnc (HconsistAnc & Hcurrs0 &
  Hlookups0AncEq & HPAnc & HVSanc & HPIanc & HKDIanc)])])]) & Hcurrs3 & Hlookups2Eq)] & _) & Hs)].
assert(HmaxKernLen: i Constants.kernelStructureTotalLength = 25).
{
  unfold Constants.kernelStructureTotalLength. unfold nextoffset. unfold scoffset. unfold sh1offset. unfold blkoffset.
  unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). cbn. pose proof Constants.maxIdxBiggerThanMinBlock.
  destruct (le_dec 8 maxIdx); try(lia). simpl. destruct (le_dec 16 maxIdx); try(lia). simpl.
  destruct (le_dec 24 maxIdx); try(lia). simpl. destruct (le_dec 25 maxIdx); try(lia). simpl. reflexivity.
}
rewrite HmaxKernLen in HblockLargeEnough. assert(kernEnd <= maxAddr) by (apply Hp).
assert(Hsh1offset: i sh1offset = kernelStructureEntriesNb).
{
  unfold sh1offset. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
  pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl.
  reflexivity.
}
assert(Hscoffset: i scoffset = kernelStructureEntriesNb + kernelStructureEntriesNb).
{
  unfold scoffset. rewrite Hsh1offset. unfold CIndex. cbn. pose proof Constants.maxIdxBiggerThanMinBlock.
  destruct (le_dec 16 maxIdx); try(lia). simpl. reflexivity.
}
assert(Hnextoffset: i nextoffset = kernelStructureEntriesNb + kernelStructureEntriesNb + kernelStructureEntriesNb).
{
  unfold nextoffset. rewrite Hscoffset. unfold CIndex. cbn. pose proof Constants.maxIdxBiggerThanMinBlock.
  destruct (le_dec 24 maxIdx); try(lia). simpl. reflexivity.
}
(*assert(HlookupPartEq: forall partition, isPDT partition s0
    -> lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr).
{
  intros partition HpartIsPDT. unfold isPDT in HpartIsPDT.
  assert(HlookupEqs2: lookup partition (memory s2) beqAddr = lookup partition (memory s0) beqAddr).
  {
    apply Hlookups2s0Eq; intros kernIdx HltIdxKernEntries Hcontra.
    - assert(HpartInBlock: In partition (getAllPaddrBlock kernStart kernEnd)).
      {
        subst partition. unfold CPaddr. cbn in HltIdxKernEntries.
        destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia). apply getAllPaddrBlockIncl; simpl; lia.
      }
      specialize(HlookupNones0 partition HpartInBlock). rewrite HlookupNones0 in *. congruence.
    - assert(HpartInBlock: In partition (getAllPaddrBlock kernStart kernEnd)).
      {
        subst partition. rewrite Hsh1offset. unfold CPaddr. cbn in HltIdxKernEntries. cbn.
        destruct (le_dec (kernStart + kernIdx + 8) maxAddr); try(lia).
        apply getAllPaddrBlockIncl; simpl; lia.
      }
      specialize(HlookupNones0 partition HpartInBlock). rewrite HlookupNones0 in *. congruence.
  }
  rewrite <-HlookupEqs2. rewrite Hs. simpl.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) partition) eqn:HbeqNextPart.
  {
    assert(HpartInBlock: In partition (getAllPaddrBlock kernStart kernEnd)).
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextPart. subst partition. rewrite Hnextoffset. cbn. unfold CPaddr.
      destruct (le_dec (kernStart + 24) maxAddr); try(lia). apply getAllPaddrBlockIncl; simpl; lia.
    }
    specialize(HlookupNones0 partition HpartInBlock). rewrite HlookupNones0 in *. exfalso; congruence.
  }
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  assert(HpartNotInBlock: forall kernIdx : index, kernIdx < kernelStructureEntriesNb
    -> partition <> CPaddr (kernStart + kernIdx + scoffset)).
  {
    intros kernIdx HltIdxKernEntries. rewrite Hscoffset. cbn in *. unfold CPaddr.
    destruct (le_dec (kernStart + kernIdx + 16) maxAddr); try(lia). intro Hcontra.
    assert(HpartInBlock: In partition (getAllPaddrBlock kernStart kernEnd)).
    {
      subst partition. apply getAllPaddrBlockIncl; simpl; lia.
    }
    specialize(HlookupNones0 partition HpartInBlock). rewrite HlookupNones0 in *. exfalso; congruence.
  }
  specialize(Hlookups2Eq partition HpartNotInBlock). assumption.
}
assert(HlookupNullEq: forall addr, isPADDR addr s0
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
{
  intros addr HaddrIsPADDR. unfold isPADDR in HaddrIsPADDR.
  assert(HlookupEqs2: lookup addr (memory s2) beqAddr = lookup addr (memory s0) beqAddr).
  {
    apply Hlookups2s0Eq; intros kernIdx HltIdxKernEntries Hcontra.
    - assert(HaddrInBlock: In addr (getAllPaddrBlock kernStart kernEnd)).
      {
        subst addr. unfold CPaddr. cbn in HltIdxKernEntries.
        destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia). apply getAllPaddrBlockIncl; simpl; lia.
      }
      specialize(HlookupNones0 addr HaddrInBlock). rewrite HlookupNones0 in *. congruence.
    - assert(HaddrInBlock: In addr (getAllPaddrBlock kernStart kernEnd)).
      {
        subst addr. rewrite Hsh1offset. unfold CPaddr. cbn in HltIdxKernEntries. cbn.
        destruct (le_dec (kernStart + kernIdx + 8) maxAddr); try(lia).
        apply getAllPaddrBlockIncl; simpl; lia.
      }
      specialize(HlookupNones0 addr HaddrInBlock). rewrite HlookupNones0 in *. congruence.
  }
  rewrite <-HlookupEqs2. rewrite Hs. simpl.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) addr) eqn:HbeqNextAddr.
  {
    assert(HaddrInBlock: In addr (getAllPaddrBlock kernStart kernEnd)).
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextAddr. subst addr. rewrite Hnextoffset. cbn. unfold CPaddr.
      destruct (le_dec (kernStart + 24) maxAddr); try(lia). apply getAllPaddrBlockIncl; simpl; lia.
    }
    specialize(HlookupNones0 addr HaddrInBlock). rewrite HlookupNones0 in *. exfalso; congruence.
  }
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  assert(HaddrNotInBlock: forall kernIdx : index, kernIdx < kernelStructureEntriesNb
    -> addr <> CPaddr (kernStart + kernIdx + scoffset)).
  {
    intros kernIdx HltIdxKernEntries. rewrite Hscoffset. cbn in *. unfold CPaddr.
    destruct (le_dec (kernStart + kernIdx + 16) maxAddr); try(lia). intro Hcontra.
    assert(HaddrInBlock: In addr (getAllPaddrBlock kernStart kernEnd)).
    {
      subst addr. apply getAllPaddrBlockIncl; simpl; lia.
    }
    specialize(HlookupNones0 addr HaddrInBlock). rewrite HlookupNones0 in *. exfalso; congruence.
  }
  specialize(Hlookups2Eq addr HaddrNotInBlock). assumption.
}*)
assert(HlookupSomeEq: forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
{
  intros addr HaddrIsSome. destruct HaddrIsSome as [entry HaddrIsSome].
  assert(HlookupEqs2: lookup addr (memory s2) beqAddr = lookup addr (memory s0) beqAddr).
  {
    apply Hlookups2s0Eq; intros kernIdx HltIdxKernEntries Hcontra.
    - assert(HaddrInBlock: In addr (getAllPaddrBlock kernStart kernEnd)).
      {
        subst addr. unfold CPaddr. cbn in HltIdxKernEntries.
        destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia). apply getAllPaddrBlockIncl; simpl; lia.
      }
      specialize(HlookupNones0 addr HaddrInBlock). rewrite HlookupNones0 in *. congruence.
    - assert(HaddrInBlock: In addr (getAllPaddrBlock kernStart kernEnd)).
      {
        subst addr. rewrite Hsh1offset. unfold CPaddr. cbn in HltIdxKernEntries. cbn.
        destruct (le_dec (kernStart + kernIdx + 8) maxAddr); try(lia).
        apply getAllPaddrBlockIncl; simpl; lia.
      }
      specialize(HlookupNones0 addr HaddrInBlock). rewrite HlookupNones0 in *. congruence.
  }
  rewrite <-HlookupEqs2. rewrite Hs. simpl.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) addr) eqn:HbeqNextAddr.
  {
    assert(HaddrInBlock: In addr (getAllPaddrBlock kernStart kernEnd)).
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextAddr. subst addr. rewrite Hnextoffset. cbn. unfold CPaddr.
      destruct (le_dec (kernStart + 24) maxAddr); try(lia). apply getAllPaddrBlockIncl; simpl; lia.
    }
    specialize(HlookupNones0 addr HaddrInBlock). rewrite HlookupNones0 in *. exfalso; congruence.
  }
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  assert(HaddrNotInBlock: forall kernIdx : index, kernIdx < kernelStructureEntriesNb
    -> addr <> CPaddr (kernStart + kernIdx + scoffset)).
  {
    intros kernIdx HltIdxKernEntries. rewrite Hscoffset. cbn in *. unfold CPaddr.
    destruct (le_dec (kernStart + kernIdx + 16) maxAddr); try(lia). intro Hcontra.
    assert(HaddrInBlock: In addr (getAllPaddrBlock kernStart kernEnd)).
    {
      subst addr. apply getAllPaddrBlockIncl; simpl; lia.
    }
    specialize(HlookupNones0 addr HaddrInBlock). rewrite HlookupNones0 in *. exfalso; congruence.
  }
  specialize(Hlookups2Eq addr HaddrNotInBlock). assumption.
}
assert(HgetKSEq: forall partition, isPDT partition s0 -> getKSEntries partition s = getKSEntries partition s0).
{
  intros partition HpartIsPDT. unfold getKSEntries.
  assert(HlookupEq: lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr).
  {
    apply HlookupSomeEq. unfold isPDT in HpartIsPDT.
    destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence). exists v. reflexivity.
  }
  rewrite HlookupEq. destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(reflexivity).
  destruct v; try(reflexivity). destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull; try(reflexivity).
  apply getKSEntriesAuxEqPrepare; try(assumption).
  - unfold consistency in *; unfold consistency1 in *; intuition.
  - unfold consistency in *; unfold consistency1 in *; intuition.
  - unfold consistency in *; unfold consistency1 in *; intuition.
  - unfold consistency in *; unfold consistency1 in *; intuition.
  - assert(Hstruct: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    rewrite <-DTL.beqAddrFalse in HbeqStructNull. specialize(Hstruct partition p HlookupPart HbeqStructNull).
    assumption.
}
assert(HgetMappedEq: forall partition, isPDT partition s0
  -> getMappedBlocks partition s = getMappedBlocks partition s0).
{
  intros partition HpartIsPDT. unfold getMappedBlocks. rewrite HgetKSEq; try(assumption).
  pose proof (KSentriesAreBE partition s0) as HentriesAreBE.
  induction (filterOptionPaddr (getKSEntries partition s0)) as [| el listKS]; simpl; try(reflexivity).
  assert(HelIsBE: isBE el s0).
  { apply HentriesAreBE. simpl. left. reflexivity. }
  unfold isBE in HelIsBE. destruct (lookup el (memory s0) beqAddr) eqn:HlookupEl; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupEl.
  assert(forall addr, In addr listKS -> isBE addr s0).
  { intros addr HaddrInList. apply HentriesAreBE. simpl. right. assumption. }
  rewrite IHlistKS; try(assumption). reflexivity.
}
assert(HgetAccMappedEq: forall partition, isPDT partition s0
  -> getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0).
{
  intros partition HpartIsPDT. unfold getAccessibleMappedBlocks. rewrite HgetMappedEq; try(assumption).
  assert(HentriesAreBE: forall addr, In addr (getMappedBlocks partition s0) -> isBE addr s0).
  {
    intros addr HaddrMapped. apply mappedBlockIsBE in HaddrMapped. destruct HaddrMapped as [bentry (Hlookup & _)].
    unfold isBE. rewrite Hlookup. trivial.
  }
  assert(HlookupEq: lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr).
  {
    apply HlookupSomeEq. unfold isPDT in HpartIsPDT.
    destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence). exists v. reflexivity.
  }
  rewrite HlookupEq. destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(reflexivity).
  destruct v; try(reflexivity). induction (getMappedBlocks partition s0) as [| el listBE]; simpl; try(reflexivity).
  assert(HelIsBE: isBE el s0).
  { apply HentriesAreBE. simpl. left. reflexivity. }
  unfold isBE in HelIsBE. destruct (lookup el (memory s0) beqAddr) eqn:HlookupEl; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupEl.
  assert(forall addr, In addr listBE -> isBE addr s0).
  { intros addr HaddrInList. apply HentriesAreBE. simpl. right. assumption. }
  rewrite IHlistBE; try(assumption). reflexivity.
}
assert(HgetMappedPaddrEq: forall partition, isPDT partition s0
  -> getMappedPaddr partition s = getMappedPaddr partition s0).
{
  intros partition HpartIsPDT. unfold getMappedPaddr. rewrite HgetMappedEq; try(assumption).
  assert(HentriesAreBE: forall addr, In addr (getMappedBlocks partition s0) -> isBE addr s0).
  {
    intros addr HaddrMapped. apply mappedBlockIsBE in HaddrMapped. destruct HaddrMapped as [bentry (Hlookup & _)].
    unfold isBE. rewrite Hlookup. trivial.
  }
  induction (getMappedBlocks partition s0) as [| el listBE]; simpl; try(reflexivity).
  assert(HelIsBE: isBE el s0).
  { apply HentriesAreBE. simpl. left. reflexivity. }
  unfold isBE in HelIsBE. destruct (lookup el (memory s0) beqAddr) eqn:HlookupEl; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupEl.
  assert(forall addr, In addr listBE -> isBE addr s0).
  { intros addr HaddrInList. apply HentriesAreBE. simpl. right. assumption. }
  rewrite IHlistBE; try(assumption). reflexivity.
}
assert(HgetAccMappedPaddrEq: forall partition, isPDT partition s0
  -> getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0).
{
  intros partition HpartIsPDT. unfold getAccessibleMappedPaddr. rewrite HgetAccMappedEq; try(assumption).
  assert(HentriesAreBE: forall addr, In addr (getAccessibleMappedBlocks partition s0) -> isBE addr s0).
  {
    intros addr HaddrMapped. unfold getAccessibleMappedBlocks in HaddrMapped. unfold isPDT in *.
    destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply DTL.InFilterAccessibleInList in HaddrMapped.
    apply mappedBlockIsBE in HaddrMapped. destruct HaddrMapped as [bentry (Hlookup & _)].
    unfold isBE. rewrite Hlookup. trivial.
  }
  induction (getAccessibleMappedBlocks partition s0) as [| el listBE]; simpl; try(reflexivity).
  assert(HelIsBE: isBE el s0).
  { apply HentriesAreBE. simpl. left. reflexivity. }
  unfold isBE in HelIsBE. destruct (lookup el (memory s0) beqAddr) eqn:HlookupEl; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupEl.
  assert(forall addr, In addr listBE -> isBE addr s0).
  { intros addr HaddrInList. apply HentriesAreBE. simpl. right. assumption. }
  rewrite IHlistBE; try(assumption). reflexivity.
}
assert(HgetFreeEq: forall partition, isPDT partition s0
  -> getFreeSlotsList partition s = getFreeSlotsList partition s0).
{
  intros partition HpartIsPDT. unfold getFreeSlotsList.
  assert(HnoDupFree: NoDupInFreeSlotsList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HlookupEq: lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr).
  {
    apply HlookupSomeEq. unfold isPDT in HpartIsPDT.
    destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence). exists v. reflexivity.
  }
  rewrite HlookupEq. destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(reflexivity).
  destruct v; try(reflexivity). specialize(HnoDupFree partition p HlookupPart).
  destruct HnoDupFree as [freeslotslist (Hlist & Hres & _)]. subst freeslotslist. unfold getFreeSlotsList in *.
  rewrite HlookupPart in Hres. destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
  apply getFreeSlotsListAuxEqPrepare; assumption.
}
assert(HgetChildrenEq: forall partition, isPDT partition s0
  -> getChildren partition s = getChildren partition s0).
{
  intros partition HpartIsPDT. unfold getChildren.
  assert(HlookupEq: lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr).
  {
    apply HlookupSomeEq. unfold isPDT in HpartIsPDT.
    destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence). exists v. reflexivity.
  }
  rewrite HlookupEq. destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(reflexivity).
  destruct v; try(reflexivity). rewrite HgetMappedEq; try(assumption). apply getPDsEqPrepare; try(assumption).
  - unfold consistency in *; unfold consistency1 in *; intuition.
  - intros addr HaddrInList. apply mappedBlockIsBE in HaddrInList. destruct HaddrInList as [bentry (Hlookup & _)].
    unfold isBE. rewrite Hlookup. trivial.
}
assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
{
  apply getPartsEqPrepare; try(assumption); unfold consistency in *; unfold consistency1 in *; intuition.
}
assert(HgetConfigBEq: forall partition, isPDT partition s0
  -> getConfigBlocks partition s = getConfigBlocks partition s0).
{
  intros partition HpartIsPDT. apply getConfigBlocksEqPrepare; try(assumption); unfold consistency in *;
    unfold consistency1 in *; intuition.
}
assert(HgetConfigPEq: forall partition, isPDT partition s0
  -> getConfigPaddr partition s = getConfigPaddr partition s0).
{
  intros partition HpartIsPDT. unfold getConfigPaddr. rewrite HgetConfigBEq; try(assumption).
  assert(forall block, In block (getConfigBlocks partition s0) -> isBE block s0).
  { intro block. apply configBlocksAreBE. }
  rewrite getAllPaddrConfigAuxEqPrepare with (getConfigBlocks partition s0) s s0; try(assumption). f_equal.
  simpl. assert(HlookupEq: lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr).
  {
    apply HlookupSomeEq. unfold isPDT in HpartIsPDT.
    destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence). exists v. reflexivity.
  }
  rewrite HlookupEq. reflexivity.
}
assert(HgetUsedPaddrEq: forall partition, isPDT partition s0
  -> getUsedPaddr partition s = getUsedPaddr partition s0).
{
  intros partition HpartIsPDT. unfold getUsedPaddr. rewrite HgetConfigPEq; try(assumption). f_equal.
  apply HgetMappedPaddrEq; assumption.
}
assert(HlistOfKernEq: forall kernList partition, isListOfKernels kernList partition s0
  -> isListOfKernels kernList partition s).
{ intros kernList partition. apply isListOfKernelsEqPrepare; assumption. }
assert(HparentsListEq: forall parentsList pdBase, isParentsList s0 parentsList pdBase
  -> isParentsList s parentsList pdBase).
{ intros parentsList pdBase. apply isParentsListEqPrepare; assumption. }

assert(nullAddrExists s).
{ (* BEGIN nullAddrExists s *)
  assert(Hcons0: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  unfold nullAddrExists in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s0) beqAddr) eqn:HlookupNull; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupNull. assumption.
  (* END nullAddrExists *)
}

assert(HblocksAreBEss1: forall block, isBE block s
  -> lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
{
  intros block HblockIsBE. unfold isBE in *. rewrite Hs in HblockIsBE. simpl in HblockIsBE. rewrite Hs. simpl.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) block) eqn:HbeqNextBlock; try(exfalso; congruence).
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
  rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  assert(HblockNotSce: forall kernIdx : index,
    kernIdx < kernelStructureEntriesNb -> block <> CPaddr (kernStart + kernIdx + scoffset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst block. rewrite HnewSce in HblockIsBE; assumption.
  }
  rewrite Hlookups2Eq in HblockIsBE; try(assumption). rewrite Hlookups2Eq; try(assumption).
  assert(HblockNotSh1: forall kernIdx : index,
    kernIdx < kernelStructureEntriesNb -> block <> CPaddr (kernStart + kernIdx + sh1offset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst block. rewrite HnewShe in HblockIsBE; assumption.
  }
  apply Hlookups1Eq; assumption.
}

assert(HaddrAreSHEs2s: forall addr, isSHE addr s2
  -> lookup addr (memory s) beqAddr = lookup addr (memory s2) beqAddr).
{
  intros addr HaddrIsSHE. unfold isSHE in *. rewrite Hs. simpl.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) addr) eqn:HbeqNextAddr.
  {
    rewrite <-DTL.beqAddrTrue in HbeqNextAddr.
    assert(HaddrInNew: In addr (getAllPaddrBlock kernStart kernEnd)).
    {
      apply DTL.paddrEqNatEqEquiv in HbeqNextAddr. unfold CPaddr in HbeqNextAddr.
      destruct (le_dec (kernStart + nextoffset) maxAddr); try(cbn in *; lia). simpl in HbeqNextAddr.
      apply getAllPaddrBlockIncl; cbn in *; lia.
    }
    specialize(HlookupNones0 addr HaddrInNew).
    assert(forall kernIdx: index, kernIdx <= kernelStructureEntriesNb - 1 -> addr <> CPaddr (kernStart + kernIdx)).
    {
      intros kernIdx HlebIdxKernEntries Hcontra. rewrite Hcontra in HbeqNextAddr.
      apply DTL.paddrEqNatEqEquiv in HbeqNextAddr. unfold CPaddr in HbeqNextAddr.
      destruct (le_dec (kernStart + nextoffset) maxAddr); try(cbn in *; lia). simpl in HbeqNextAddr.
      destruct (le_dec (kernStart + kernIdx) maxAddr); cbn in *; lia.
    }
    assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
      -> addr <> CPaddr (kernStart + kernIdx + sh1offset)).
    {
      intros kernIdx HltIdxKernEntries Hcontra. rewrite Hcontra in HbeqNextAddr.
      apply DTL.paddrEqNatEqEquiv in HbeqNextAddr. unfold CPaddr in HbeqNextAddr.
      destruct (le_dec (kernStart + nextoffset) maxAddr); try(cbn in *; lia). simpl in HbeqNextAddr.
      destruct (le_dec (kernStart + kernIdx + sh1offset) maxAddr); cbn in *; lia.
    }
    rewrite Hlookups2s0Eq in HaddrIsSHE; try(assumption). rewrite HlookupNones0 in HaddrIsSHE. exfalso; congruence.
  }
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
    -> addr <> CPaddr (kernStart + kernIdx + scoffset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. rewrite Hcontra in HaddrIsSHE.
    assert(HaddrInNew: In addr (getAllPaddrBlock kernStart kernEnd)).
    {
      apply DTL.paddrEqNatEqEquiv in Hcontra. unfold CPaddr in Hcontra.
      destruct (le_dec (kernStart + kernIdx + scoffset) maxAddr); try(cbn in *; lia). simpl in Hcontra.
      apply getAllPaddrBlockIncl; cbn in *; lia.
    }
    specialize(HlookupNones0 addr HaddrInNew).
    assert(forall kernIdx: index, kernIdx <= kernelStructureEntriesNb - 1 -> addr <> CPaddr (kernStart + kernIdx)).
    {
      intros kernIdxBis HlebIdxKernEntries HcontraBis. rewrite HcontraBis in Hcontra.
      apply DTL.paddrEqNatEqEquiv in Hcontra. unfold CPaddr in Hcontra.
      destruct (le_dec (kernStart + kernIdx + scoffset) maxAddr); try(cbn in *; lia). simpl in Hcontra.
      destruct (le_dec (kernStart + kernIdxBis) maxAddr); cbn in *; lia.
    }
    assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
      -> addr <> CPaddr (kernStart + kernIdx + sh1offset)).
    {
      intros kernIdxBis HltIdxKernBisEntries HcontraBis. rewrite HcontraBis in Hcontra.
      apply DTL.paddrEqNatEqEquiv in Hcontra. unfold CPaddr in Hcontra.
      destruct (le_dec (kernStart + kernIdx + scoffset) maxAddr); try(cbn in *; lia). simpl in Hcontra.
      destruct (le_dec (kernStart + kernIdxBis + sh1offset) maxAddr); cbn in *; lia.
    }
    subst addr. rewrite Hlookups2s0Eq in HaddrIsSHE; try(assumption). rewrite HlookupNones0 in HaddrIsSHE. congruence.
  }
  apply Hlookups2Eq; assumption.
}

assert(HaddrAreSHEss2: forall addr, isSHE addr s
  -> lookup addr (memory s) beqAddr = lookup addr (memory s2) beqAddr).
{
  intros addr HaddrIsSHE. unfold isSHE in *. rewrite Hs. simpl. rewrite Hs in HaddrIsSHE. simpl in HaddrIsSHE.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) addr) eqn:HbeqNextAddr; try(exfalso; congruence).
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  rewrite removeDupIdentity in HaddrIsSHE; try(apply not_eq_sym; assumption). apply Hlookups2Eq.
  intros kernIdx HltIdxKernEntries Hcontra. subst addr. rewrite HnewSce in HaddrIsSHE; lia.
}

assert(HblockUntouched: forall block,
  ~ In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
  -> isBE block s1
  -> lookup block (memory s1) beqAddr = lookup block (memory s0) beqAddr).
{
  intros block HblockNotNew HblockIsBE. unfold isBE in *. apply Hlookups1s0Eq; try(assumption).
  intros kernIdx HlebIdxKernEntries Hcontra. apply DTL.paddrEqNatEqEquiv in Hcontra. unfold CPaddr in Hcontra.
  destruct (le_dec (kernStart + kernIdx) maxAddr); try(cbn in *; lia). simpl in Hcontra. contradict HblockNotNew.
  unfold CPaddr. destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); try(cbn in *; lia).
  apply getAllPaddrBlockIncl; cbn in *; lia.
}

assert(HblockUntouchedMeansSh1Untouched: forall block,
  ~ In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
  -> isSHE (CPaddr (block + sh1offset)) s0
  -> lookup (CPaddr (block + sh1offset)) (memory s2) beqAddr
      = lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr).
{
  intros block HblockNotNew Hsh1IsSHE. unfold isSHE in *. apply Hlookups2s0Eq; try(assumption).
  - intros kernIdx HlebIdxKernEntries. contradict HblockNotNew. unfold CPaddr in HblockNotNew. unfold CPaddr.
    destruct (le_dec (kernStart + kernIdx) maxAddr); try(cbn in *; lia).
    destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); try(cbn in *; lia). unfold CPaddr in Hsh1IsSHE.
    assert(Hnull: isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold isPADDR in Hnull. destruct (le_dec (block + sh1offset) maxAddr).
    + rewrite HblockNotNew in Hsh1IsSHE. rewrite HlookupNones0 in Hsh1IsSHE; try(exfalso; congruence).
      apply getAllPaddrBlockIncl; cbn in *; lia.
    + assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
      { unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance. }
      rewrite HnullEq in *. exfalso. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
  - intros kernIdx HltIdxKernEntries. contradict HblockNotNew. unfold CPaddr in HblockNotNew. unfold CPaddr.
    destruct (le_dec (kernStart + kernIdx + sh1offset) maxAddr); try(cbn in *; lia).
    destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); try(cbn in *; lia). unfold CPaddr in Hsh1IsSHE.
    assert(Hnull: isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold isPADDR in Hnull. destruct (le_dec (block + sh1offset) maxAddr).
    + rewrite HblockNotNew in Hsh1IsSHE. rewrite HlookupNones0 in Hsh1IsSHE; try(exfalso; congruence).
      apply getAllPaddrBlockIncl; cbn in *; lia.
    + assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
      { unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance. }
      rewrite HnullEq in *. exfalso. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
}

assert(HblockUntouchedMeansSh1Untoucheds2: forall block,
  ~ In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
  -> isSHE (CPaddr (block + sh1offset)) s2
  -> lookup (CPaddr (block + sh1offset)) (memory s2) beqAddr
      = lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr).
{
  intros block HblockNotNew Hsh1IsSHE. unfold isSHE in *.
  pose proof (HaddrAreSHEs2s (CPaddr (block + sh1offset)) Hsh1IsSHE) as HlookupEqss2.
  apply Hlookups2s0Eq; try(assumption).
  - intros kernIdx HlebIdxKernEntries. contradict HblockNotNew. exfalso. rewrite HblockNotNew in Hsh1IsSHE.
    assert(HaddrIsBE: isBE (CPaddr (kernStart + kernIdx)) s1).
    {
      unfold isBE. destruct (Nat.eqb kernIdx (kernelStructureEntriesNb - 1)) eqn:HbeqIdxKernEntries.
      - rewrite Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries.
        destruct HlastBlock as [l HlastBlock]. rewrite Nat.add_sub_assoc; try(cbn; lia). rewrite HlastBlock. trivial.
      - rewrite Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE]. rewrite HnewBE. trivial.
    }
    assert(forall kernIdxBis : index, kernIdxBis < kernelStructureEntriesNb
      -> (CPaddr (kernStart + kernIdx)) <> CPaddr (kernStart + kernIdxBis + sh1offset)).
    {
      intros kernIdxBis HltIdxKernEntries Hcontra. apply DTL.paddrEqNatEqEquiv in Hcontra. unfold CPaddr in Hcontra.
      destruct (le_dec (kernStart + kernIdx) maxAddr); try(cbn in *; lia).
      destruct (le_dec (kernStart + kernIdxBis + sh1offset) maxAddr); cbn in *; lia.
    }
    unfold isBE in HaddrIsBE. rewrite <-Hlookups1Eq in HaddrIsBE; try(assumption).
    destruct (lookup (CPaddr (kernStart + kernIdx)) (memory s2) beqAddr); try(congruence). destruct v; congruence.
  - intros kernIdx HltIdxKernEntries. contradict HblockNotNew. rewrite <-HlookupEqss2 in Hsh1IsSHE.
    unfold CPaddr in HblockNotNew. unfold CPaddr.
    destruct (le_dec (kernStart + kernIdx + sh1offset) maxAddr); try(cbn in *; lia).
    destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); try(cbn in *; lia). unfold CPaddr in Hsh1IsSHE.
    assert(Hnull: isPADDR nullAddr s) by assumption. unfold isPADDR in Hnull.
    destruct (le_dec (block + sh1offset) maxAddr).
    + rewrite HblockNotNew in Hsh1IsSHE. apply DTL.paddrEqNatEqEquiv in HblockNotNew. simpl in HblockNotNew.
      apply Nat.add_cancel_r in HblockNotNew. apply getAllPaddrBlockIncl; cbn in *; lia.
    + assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
      { unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance. }
      rewrite HnullEq in *. exfalso. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
      destruct v; congruence.
}

assert(wellFormedFstShadowIfBlockEntry s).
{ (* BEGIN wellFormedFstShadowIfBlockEntry s *)
  assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
    by (unfold consistency in *; unfold consistency1 in *; intuition). intros block HblockIsBE.
  assert(HblockIsBEs1: isBE block s1).
  { unfold isBE. rewrite <-HblocksAreBEss1; assumption. }
  assert(isSHE (CPaddr (block + sh1offset)) s2).
  {
    assert(HpropsOr: In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
      \/ ~In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
    destruct HpropsOr as [HblockIsNew | HblockUnchanged].
    - apply getAllPaddrBlockInclRev in HblockIsNew.
      destruct HblockIsNew as (HlebKernBlock & HltBlockKernPEntries & _).
      assert(Hidx: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ p block = kernStart + kernIdx).
      {
        exists (CIndex (block-kernStart)). assert(block <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
        unfold CIndex. destruct (le_dec (block - kernStart) maxIdx); try(lia). simpl. split; try(lia).
        unfold CPaddr in HltBlockKernPEntries.
        destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
      }
      destruct Hidx as [kernIdx (HltIdxKernEntries & HblockEq)]. rewrite HblockEq. unfold isSHE.
      rewrite HnewShe; try(assumption). trivial.
    - assert(HblockIsBEs0: isBE block s0) by (unfold isBE; rewrite <-HblockUntouched; assumption).
      specialize(Hcons0 block HblockIsBEs0). unfold isSHE. rewrite HblockUntouchedMeansSh1Untouched; assumption.
  }
  unfold isSHE. rewrite HaddrAreSHEs2s; assumption.
  (* END wellFormedFstShadowIfBlockEntry *)
}

assert(PDTIfPDFlag s).
{ (* BEGIN PDTIfPDFlag s *)
  assert(Hcons0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros block sh1entryaddr (HcheckChild & Hsh1).
  assert(HlookupBlockEqss1: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. unfold sh1entryAddr in Hsh1.
    destruct (lookup block (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
  }
  unfold checkChild in HcheckChild. unfold sh1entryAddr in Hsh1. unfold bentryAFlag. unfold bentryPFlag.
  unfold bentryStartAddr. unfold entryPDT. rewrite HlookupBlockEqss1 in *.
  assert(HlookupBlockEqs1s0: lookup block (memory s1) beqAddr = lookup block (memory s0) beqAddr).
  {
    apply Hlookups1s0Eq. intros kernIdx HlebIdxKernEntries Hcontra.
    destruct (Nat.eqb kernIdx (kernelStructureEntriesNb - 1)) eqn:HbeqIdxKernEntries.
    - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. destruct HlastBlock as [l HlastBlock].
      rewrite Nat.add_sub_assoc in Hcontra; try(cbn; lia). subst block. rewrite HlastBlock in *.
      assert(Hsh1Eq: CPaddr (kernStart + kernelStructureEntriesNb - 1) + sh1offset
        = kernStart + (CIndex(kernelStructureEntriesNb - 1)) + sh1offset).
      {
        unfold CPaddr. unfold CIndex.
        destruct (le_dec (kernStart+kernelStructureEntriesNb-1) maxAddr); try(cbn in *; lia).
        destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(rewrite maxIdxEqualMaxAddr in *; cbn in *; lia).
        cbn. lia.
      }
      rewrite Hsh1Eq in *.
      assert(HlookupSh1Eq: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s2) beqAddr).
      {
        apply HaddrAreSHEss2. unfold isSHE. destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      rewrite HlookupSh1Eq in HcheckChild. subst sh1entryaddr. rewrite HnewShe in HcheckChild; try(lia).
      simpl in HcheckChild. congruence.
    - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(HltIdxKernEntriesM: kernIdx < kernelStructureEntriesNb - 1).
      { lia. }
      specialize(HnewBE kernIdx HltIdxKernEntriesM). destruct HnewBE as [l HnewBE]. subst block. rewrite HnewBE in *.
      assert(Hsh1Eq: CPaddr (kernStart + kernIdx) + sh1offset = kernStart + kernIdx + sh1offset).
      {
        unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); cbn in *; lia.
      }
      rewrite Hsh1Eq in *.
      assert(HlookupSh1Eq: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s2) beqAddr).
      {
        apply HaddrAreSHEss2. unfold isSHE. destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      rewrite HlookupSh1Eq in HcheckChild. subst sh1entryaddr. rewrite HnewShe in HcheckChild; try(lia).
      simpl in HcheckChild. congruence.
  }
  rewrite HlookupBlockEqs1s0 in *.
  assert(HlookupSh1Eq: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
  {
    destruct (lookup block (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). assert(Hsh1IsSHE: isSHE sh1entryaddr s).
    {
      unfold isSHE. destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
      trivial.
    }
    pose proof (HaddrAreSHEss2 sh1entryaddr Hsh1IsSHE) as HlookupEq. rewrite HlookupEq in *. subst sh1entryaddr.
    apply HblockUntouchedMeansSh1Untoucheds2.
    - intro Hcontra. apply getAllPaddrBlockInclRev in Hcontra.
      destruct Hcontra as (HlebStartBlock & HltBlockStartEntriesNb & _).
      assert(Hblock: exists blockIdx, blockIdx < kernelStructureEntriesNb /\ block = CPaddr (kernStart + blockIdx)).
      {
        exists (CIndex (block-kernStart)). assert(block <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
        unfold CIndex. destruct (le_dec (block - kernStart) maxIdx); try(lia). simpl. unfold CPaddr.
        destruct (le_dec (kernStart + (block - kernStart)) maxAddr); try(rewrite maxIdxEqualMaxAddr in *; lia). split.
        - unfold CPaddr in HltBlockStartEntriesNb.
          destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
        - apply DTL.paddrEqNatEqEquiv. simpl. lia.
      }
      destruct Hblock as [blockIdx (HltIdxKernEntries & Hblock)].
      assert(HblockInRange: In block (getAllPaddrBlock kernStart kernEnd)).
      {
        subst block. unfold CPaddr. destruct (le_dec (kernStart + blockIdx) maxAddr); try(cbn in *; lia).
        apply getAllPaddrBlockIncl; cbn in *; lia.
      }
      specialize(HlookupNones0 block HblockInRange). congruence.
    - unfold isSHE. destruct (lookup (CPaddr (block + sh1offset)) (memory s2) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
  }
  rewrite HlookupSh1Eq in HcheckChild.
  assert(HcheckChilds0: true = checkChild block s0 sh1entryaddr /\ sh1entryAddr block sh1entryaddr s0) by intuition.
  specialize(Hcons0 block sh1entryaddr HcheckChilds0).
  destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split. assumption. split. assumption.
  exists startaddr. split. assumption. unfold entryPDT in HstartIsPDT.
  destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
  rewrite HlookupSomeEq; try(assumption).
  destruct (lookup (startAddr (blockrange b)) (memory s0) beqAddr); try(exfalso; congruence).
  exists v. reflexivity.
  (* END PDTIfPDFlag *)
}

assert(AccessibleNoPDFlag s).
{ (* BEGIN AccessibleNoPDFlag s *)
  assert(Hcons0: AccessibleNoPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros block sh1entryaddr HblockIsBE Hsh1 HAflag.
  assert(HlookupBlockEqss1: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. unfold sh1entryAddr in Hsh1.
    destruct (lookup block (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
  }
  unfold isBE in HblockIsBE. unfold sh1entryAddr in Hsh1. unfold bentryAFlag in HAflag.
  rewrite HlookupBlockEqss1 in *.
  assert(HlookupBlockEqs1s0: lookup block (memory s1) beqAddr = lookup block (memory s0) beqAddr).
  {
    apply Hlookups1s0Eq. intros kernIdx HlebIdxKernEntries Hcontra.
    destruct (Nat.eqb kernIdx (kernelStructureEntriesNb - 1)) eqn:HbeqIdxKernEntries.
    - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. destruct HlastBlock as [l HlastBlock].
      rewrite Nat.add_sub_assoc in Hcontra; try(cbn; lia). subst block. rewrite HlastBlock in *.
      simpl in HAflag. congruence.
    - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(HltIdxKernEntriesM: kernIdx < kernelStructureEntriesNb - 1).
      { lia. }
      specialize(HnewBE kernIdx HltIdxKernEntriesM). destruct HnewBE as [l HnewBE]. subst block. rewrite HnewBE in *.
      simpl in HAflag. congruence.
  }
  rewrite HlookupBlockEqs1s0 in *. specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAflag).
  unfold sh1entryPDflag in *.
  assert(HlookupSh1Eq: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
  {
    apply HlookupSomeEq. destruct (lookup sh1entryaddr (memory s0) beqAddr); try(exfalso; congruence).
    exists v. reflexivity.
  }
  rewrite HlookupSh1Eq. assumption.
  (* END AccessibleNoPDFlag *)
}

assert(HpdsArePDT: forall partition, isPDT partition s
  -> lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr).
{
  intros partition HpartIsPDT. unfold isPDT in HpartIsPDT. rewrite Hs. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
  simpl. destruct (beqAddr (CPaddr (kernStart + nextoffset)) partition) eqn:HbeqNextPart; try(exfalso; congruence).
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
  assert(forall kernIdx : index, kernIdx < kernelStructureEntriesNb
    -> partition <> CPaddr (kernStart + kernIdx + scoffset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst partition. rewrite HnewSce in HpartIsPDT; assumption.
  }
  rewrite Hlookups2Eq; try(assumption). apply Hlookups2s0Eq.
  - intros kernIdx HltIdxKernEntries Hcontra. subst partition.
    assert(HisBE: isBE (CPaddr (kernStart + kernIdx)) s1).
    {
      unfold isBE. destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *.
        rewrite Nat.add_sub_assoc in *; try(cbn; lia). destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock.
        trivial.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE]. rewrite HnewBE. trivial.
    }
    assert(forall kernIdxBis: index, kernIdxBis < kernelStructureEntriesNb
      -> CPaddr (kernStart + kernIdx) <> CPaddr (kernStart + kernIdxBis + scoffset)).
    {
      intros kernIdxBis HltIdxBisKernEntries Hcontra. rewrite Hcontra in HpartIsPDT.
      rewrite HnewSce in HpartIsPDT; assumption.
    }
    rewrite Hlookups2Eq in HpartIsPDT; try(assumption).
    assert(forall kernIdxBis: index, kernIdxBis < kernelStructureEntriesNb
      -> CPaddr (kernStart + kernIdx) <> CPaddr (kernStart + kernIdxBis + sh1offset)).
    {
      intros kernIdxBis HltIdxBisKernEntries Hcontra. rewrite Hcontra in HpartIsPDT.
      rewrite HnewShe in HpartIsPDT; assumption.
    }
    rewrite Hlookups1Eq in HpartIsPDT; try(assumption). unfold isBE in HisBE.
    destruct (lookup (CPaddr (kernStart + kernIdx)) (memory s1) beqAddr); try(congruence). destruct v; congruence.
  - intros kernIdx HltIdxKernEntries Hcontra. subst partition.
    assert(HisSHE: isSHE (CPaddr (kernStart + kernIdx + sh1offset)) s2).
    {
      unfold isSHE. rewrite HnewShe; try(assumption). trivial.
    }
    assert(forall kernIdxBis: index, kernIdxBis < kernelStructureEntriesNb
      -> CPaddr (kernStart + kernIdx + sh1offset) <> CPaddr (kernStart + kernIdxBis + scoffset)).
    {
      intros kernIdxBis HltIdxBisKernEntries Hcontra. rewrite Hcontra in HpartIsPDT.
      rewrite HnewSce in HpartIsPDT; assumption.
    }
    rewrite Hlookups2Eq in HpartIsPDT; try(assumption). unfold isSHE in HisSHE.
    destruct (lookup (CPaddr (kernStart + kernIdx + sh1offset)) (memory s2) beqAddr); try(congruence).
    destruct v; congruence.
}

assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
{ (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
  assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0)
    by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition pdentry HlookupPart HbeqFirstNull.
  rewrite HpdsArePDT in HlookupPart; try(unfold isPDT; rewrite HlookupPart; trivial).
  specialize(Hcons0 partition pdentry HlookupPart HbeqFirstNull). destruct Hcons0 as (HfirstIsBE & HfirstIsFree).
  unfold isBE. unfold isFreeSlot in *.
  destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr) eqn:HlookupFirst; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupFirst.
  split. trivial. destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1;
    try(exfalso; congruence). destruct v; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists (SHE s4); assumption). rewrite HlookupSh1.
  destruct (lookup (CPaddr (firstfreeslot pdentry + scoffset)) (memory s0) beqAddr) eqn:HlookupSce;
    try(exfalso; congruence). destruct v; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists (SCE s5); assumption). rewrite HlookupSce. assumption.
  (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
}

assert(multiplexerIsPDT s).
{ (* BEGIN multiplexerIsPDT s *)
  assert(Hcons0: multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  unfold multiplexerIsPDT in *. unfold isPDT in *.
  destruct (lookup multiplexer (memory s0) beqAddr) eqn:HlookupMult; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupMult. assumption.
  (* END multiplexerIsPDT *)
}

assert(currentPartitionInPartitionsList s).
{ (* BEGIN currentPartitionInPartitionsList s *)
  assert(Hcons0: currentPartitionInPartitionsList s0)
    by (unfold consistency in *; unfold consistency1 in *; intuition). unfold currentPartitionInPartitionsList in *.
  rewrite HgetPartsEq. rewrite Hs. simpl. rewrite Hcurrs3. rewrite Hcurrs2. rewrite Hcurrs1. assumption.
  (* END currentPartitionInPartitionsList *)
}

assert(wellFormedShadowCutIfBlockEntry s).
{ (* BEGIN wellFormedShadowCutIfBlockEntry s *)
  assert(Hcons0: wellFormedShadowCutIfBlockEntry s0)
    by (unfold consistency in *; unfold consistency1 in *; intuition). intros block HblockIsBE.
  unfold isBE in HblockIsBE. rewrite HblocksAreBEss1 in HblockIsBE; try(assumption).
  assert(HpropsOr: In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
    \/ ~In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
  destruct HpropsOr as [HblockIsNew | HblockNotNew].
  - apply getAllPaddrBlockInclRev in HblockIsNew.
    destruct HblockIsNew as (HlebKernBlock & HltBlockKernPEntries & _).
    assert(Hidx: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ p block = kernStart + kernIdx).
    {
      exists (CIndex (block-kernStart)). assert(block <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      unfold CIndex. destruct (le_dec (block - kernStart) maxIdx); try(lia). simpl. split; try(lia).
      unfold CPaddr in HltBlockKernPEntries.
      destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
    }
    destruct Hidx as [kernIdx (HltIdxKernEntries & HblockEq)]. exists (CPaddr (kernStart + kernIdx + scoffset)).
    rewrite HblockEq. split; try(reflexivity).
    assert(HaddrIsSCE: isSCE (CPaddr (kernStart + kernIdx + scoffset)) s3).
    { unfold isSCE. rewrite HnewSce; lia. }
    unfold isSCE in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (kernStart + nextoffset)) (CPaddr (kernStart + kernIdx + scoffset))) eqn:HbeqNextSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextSce. unfold CPaddr in HbeqNextSce.
      destruct (le_dec (kernStart + nextoffset) maxAddr); try(cbn in *; lia).
      destruct (le_dec (kernStart + kernIdx + scoffset) maxAddr); try(cbn in *; lia).
      apply DTL.paddrEqNatEqEquiv in HbeqNextSce. cbn in *. lia.
    }
    rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
  - assert(HblockIsBEs0: isBE block s0) by (unfold isBE; rewrite <-HblockUntouched; assumption).
    specialize(Hcons0 block HblockIsBEs0). destruct Hcons0 as [scentryaddr (HisSCE & Hsce)]. exists scentryaddr.
    split; try(assumption). unfold isSCE in *.
    destruct (lookup scentryaddr (memory s0) beqAddr) eqn:HlookupSce; try(exfalso; congruence).
    rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupSce. assumption.
  (* END wellFormedShadowCutIfBlockEntry *)
}

assert(HblocksAreBEs1s: forall block, isBE block s1
  -> lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
{
  intros block HblockIsBE. unfold isBE in *. rewrite Hs. simpl.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) block) eqn:HbeqNextBlock.
  {
    rewrite <-DTL.beqAddrTrue in HbeqNextBlock. subst block. exfalso.
    assert(HnextIsNew: In (CPaddr (kernStart + nextoffset)) (getAllPaddrBlock kernStart kernEnd)).
    {
      unfold CPaddr. destruct (le_dec (kernStart + nextoffset) maxAddr); try(cbn in *; lia).
      apply getAllPaddrBlockIncl; cbn in *; lia.
    }
    specialize(HlookupNones0 (CPaddr (kernStart + nextoffset)) HnextIsNew).
    assert(forall kernIdx : index, kernIdx <= kernelStructureEntriesNb - 1
      -> (CPaddr (kernStart + nextoffset)) <> CPaddr (kernStart + kernIdx)).
    {
      intros kernIdx HltIdxKernEntries Hcontra. unfold CPaddr in Hcontra.
      destruct (le_dec (kernStart + nextoffset) maxAddr); try(cbn in *; lia).
      destruct (le_dec (kernStart + kernIdx) maxAddr); try(cbn in *; lia). apply DTL.paddrEqNatEqEquiv in Hcontra.
      cbn in *. lia.
    }
    rewrite Hlookups1s0Eq in HblockIsBE; try(assumption). rewrite HlookupNones0 in HblockIsBE. congruence.
  }
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  assert(HblockNotSh1: forall kernIdx : index,
    kernIdx < kernelStructureEntriesNb -> block <> CPaddr (kernStart + kernIdx + sh1offset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst block.
    assert(Hsh1IsNew: In (CPaddr (kernStart + kernIdx + sh1offset)) (getAllPaddrBlock kernStart kernEnd)).
    {
      unfold CPaddr. destruct (le_dec (kernStart + kernIdx + sh1offset) maxAddr); try(cbn in *; lia).
      apply getAllPaddrBlockIncl; cbn in *; lia.
    }
    specialize(HlookupNones0 (CPaddr (kernStart + kernIdx + sh1offset)) Hsh1IsNew).
    assert(forall kernIdxBis : index, kernIdxBis <= kernelStructureEntriesNb - 1
      -> CPaddr (kernStart + kernIdx + sh1offset) <> CPaddr (kernStart + kernIdxBis)).
    {
      intros kernIdxBis HltIdxBisKernEntries Hcontra. unfold CPaddr in Hcontra.
      destruct (le_dec (kernStart + kernIdx + sh1offset) maxAddr); try(cbn in *; lia).
      destruct (le_dec (kernStart + kernIdxBis) maxAddr); try(cbn in *; lia). apply DTL.paddrEqNatEqEquiv in Hcontra.
      cbn in *. lia.
    }
    rewrite Hlookups1s0Eq in HblockIsBE; try(assumption). rewrite HlookupNones0 in HblockIsBE. congruence.
  }
  rewrite <-Hlookups1Eq; try(assumption).
  assert(HblockNotSce: forall kernIdx : index,
    kernIdx < kernelStructureEntriesNb -> block <> CPaddr (kernStart + kernIdx + scoffset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst block.
    assert(HsceIsNew: In (CPaddr (kernStart + kernIdx + scoffset)) (getAllPaddrBlock kernStart kernEnd)).
    {
      unfold CPaddr. destruct (le_dec (kernStart + kernIdx + scoffset) maxAddr); try(cbn in *; lia).
      apply getAllPaddrBlockIncl; cbn in *; lia.
    }
    specialize(HlookupNones0 (CPaddr (kernStart + kernIdx + scoffset)) HsceIsNew).
    assert(forall kernIdxBis : index, kernIdxBis <= kernelStructureEntriesNb - 1
      -> CPaddr (kernStart + kernIdx + scoffset) <> CPaddr (kernStart + kernIdxBis)).
    {
      intros kernIdxBis HltIdxBisKernEntries Hcontra. unfold CPaddr in Hcontra.
      destruct (le_dec (kernStart + kernIdx + scoffset) maxAddr); try(cbn in *; lia).
      destruct (le_dec (kernStart + kernIdxBis) maxAddr); try(cbn in *; lia). apply DTL.paddrEqNatEqEquiv in Hcontra.
      cbn in *. lia.
    }
    rewrite Hlookups1s0Eq in HblockIsBE; try(assumption). rewrite HlookupNones0 in HblockIsBE. congruence.
  }
  apply Hlookups2Eq; assumption.
}

assert(BlocksRangeFromKernelStartIsBE s).
{ (* BEGIN BlocksRangeFromKernelStartIsBE s *)
  assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros kernel idx HkernIsKS HltIdxKernEntries. unfold isKS in HkernIsKS.
  assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  }
  rewrite HlookupKernEq in HkernIsKS.
  assert(HpropsOr: In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
    \/ ~In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
  destruct HpropsOr as [HkernIsNew | HkernNotNew].
  - apply getAllPaddrBlockInclRev in HkernIsNew.
    destruct HkernIsNew as (HlebKerns & HltKernKernPEntries & _).
    assert(Hidx: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ p kernel = kernStart + kernIdx).
    {
      exists (CIndex (kernel-kernStart)). assert(kernel <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      unfold CIndex. destruct (le_dec (kernel - kernStart) maxIdx); try(lia). simpl. split; try(lia).
      unfold CPaddr in HltKernKernPEntries.
      destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
    }
    destruct Hidx as [kernIdx (HltKIdxKernEntries & HKernEq)].
    assert(HkernEqBis: p kernel = kernStart).
    {
      destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. exfalso.
        assert(Hkern: kernel = CPaddr(kernStart + kernelStructureEntriesNb - 1)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr.
          destruct (le_dec (kernStart + kernelStructureEntriesNb - 1) maxAddr); cbn in *; lia.
        }
        subst kernel. destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock in HkernIsKS. simpl in HkernIsKS.
        unfold zero in HkernIsKS. unfold CIndex in HkernIsKS. destruct (le_dec 0 maxIdx); try(lia).
        destruct (le_dec 7 maxIdx); try(rewrite maxIdxEqualMaxAddr in *; cbn in *; lia).
        injection HkernIsKS as Hcontra. lia.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE].
        assert(Hkern: kernel = CPaddr(kernStart + kernIdx)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); cbn in *; lia.
        }
        rewrite Hkern in HkernIsKS. rewrite HnewBE in HkernIsKS. simpl in HkernIsKS. unfold zero in HkernIsKS.
        subst kernIdx. rewrite HKernEq. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl. lia.
    }
    rewrite HkernEqBis in *. assert(HisBE: isBE (CPaddr (kernStart + idx)) s1).
    {
      unfold isBE. destruct (Nat.eqb idx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. rewrite Nat.add_sub_assoc; try(lia).
        destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock. trivial.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: idx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE idx Hlt). destruct HnewBE as [l HnewBE]. rewrite HnewBE. trivial.
    }
    unfold isBE. rewrite HblocksAreBEs1s; assumption.
  - assert(HlookupKernEqs0: lookup kernel (memory s1) beqAddr = lookup kernel (memory s0) beqAddr).
    {
      apply HblockUntouched; try(assumption). unfold isBE.
      destruct (lookup kernel (memory s1) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    rewrite HlookupKernEqs0 in HkernIsKS. specialize(Hcons0 kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *.
    destruct (lookup (CPaddr (kernel + idx)) (memory s0) beqAddr) eqn:Hlookup; try(exfalso; congruence).
    rewrite HlookupSomeEq; try(exists v; assumption). rewrite Hlookup. assumption.
  (* END BlocksRangeFromKernelStartIsBE *)
}

assert(HstartIsKSs: isKS kernStart s).
{
  assert(forall kernIdx : index, kernIdx < kernelStructureEntriesNb
    -> kernStart <> CPaddr (kernStart + kernIdx + sh1offset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. unfold CPaddr in Hcontra.
    destruct (le_dec (kernStart + kernIdx + sh1offset) maxAddr); try(cbn in *; lia). destruct kernStart.
    simpl in Hcontra. injection Hcontra as Heq. lia.
  }
  unfold isKS in *. rewrite Hlookups1Eq in HstartIsKSs2; try(assumption). rewrite HblocksAreBEs1s; try(assumption).
  unfold isBE. destruct (lookup kernStart (memory s1) beqAddr); try(congruence). destruct v; try(congruence). trivial.
}

assert(KernelStructureStartFromBlockEntryAddrIsKS s).
{ (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
  assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0)
    by (unfold consistency in *; unfold consistency1 in *; intuition). intros block idx HblockIsBE Hidx.
  assert(HlookupBlockEqss1: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
  { apply HblocksAreBEss1; assumption. }
  unfold isBE in HblockIsBE. unfold bentryBlockIndex in Hidx. rewrite HlookupBlockEqss1 in *.
  assert(HpropsOr: In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
    \/ ~In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
  destruct HpropsOr as [HblockIsNew | HblockNotNew].
  - apply getAllPaddrBlockInclRev in HblockIsNew.
    destruct HblockIsNew as (HlebBlockKern & HltBlockKernPEntries & _).
    assert(HidxBis: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ p block = kernStart + kernIdx).
    {
      exists (CIndex (block-kernStart)). assert(block <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      unfold CIndex. destruct (le_dec (block - kernStart) maxIdx); try(lia). simpl. split; try(lia).
      unfold CPaddr in HltBlockKernPEntries.
      destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
    }
    destruct HidxBis as [kernIdx (HltKIdxKernEntries & HKernEq)].
    assert(HidxEq: idx = kernIdx).
    {
      destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *.
        assert(Hblock: block = CPaddr (kernStart + kernelStructureEntriesNb - 1)).
        {
          unfold CPaddr. destruct (le_dec (kernStart + kernelStructureEntriesNb - 1) maxAddr); try(cbn in *; lia).
          apply DTL.paddrEqNatEqEquiv. simpl. lia.
        }
        subst block. destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock in Hidx. simpl in Hidx. subst idx.
        apply DTL.index_eq_i. rewrite HbeqIdxKernEntries. unfold CIndex.
        destruct (le_dec 7 maxIdx); try(rewrite maxIdxEqualMaxAddr in *); cbn in *; lia.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE].
        assert(Hblock: block = CPaddr (kernStart + kernIdx)).
        {
          unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); try(cbn in *; lia).
          apply DTL.paddrEqNatEqEquiv. simpl. lia.
        }
        subst block. rewrite HnewBE in Hidx. simpl in Hidx. assumption.
    }
    subst idx. rewrite HKernEq. rewrite Nat.add_sub. assert(HstartEq: CPaddr kernStart = kernStart).
    {
      unfold CPaddr. destruct (le_dec kernStart maxAddr); try(lia). apply DTL.paddrEqNatEqEquiv. simpl. reflexivity.
    }
    rewrite HstartEq. assumption.
  - rewrite HblockUntouched in Hidx; try(assumption). rewrite HblockUntouched in HblockIsBE; try(assumption).
    specialize(Hcons0 block idx HblockIsBE Hidx). unfold isKS in *.
    destruct (lookup (CPaddr (block - idx)) (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
    rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupKern. assumption.
  (* END KernelStructureStartFromBlockEntryAddrIsKS *)
}

assert(sh1InChildLocationIsBE s).
{ (* BEGIN sh1InChildLocationIsBE s *)
  assert(Hcons0: sh1InChildLocationIsBE s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull.
  rewrite HaddrAreSHEss2 in HlookupSh1; try(unfold isSHE; rewrite HlookupSh1; trivial).
  assert(forall kernIdx : index, kernIdx < kernelStructureEntriesNb
    -> sh1entryaddr <> CPaddr (kernStart + kernIdx + sh1offset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. rewrite Hcontra in HlookupSh1.
    rewrite HnewShe in HlookupSh1; try(assumption). injection HlookupSh1 as Hentry. rewrite <-Hentry in HbeqLocNull.
    simpl in HbeqLocNull. congruence.
  }
  rewrite Hlookups1Eq in HlookupSh1; try(assumption).
  assert(forall kernIdx : index, kernIdx <= kernelStructureEntriesNb - 1
    -> sh1entryaddr <> CPaddr (kernStart + kernIdx)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. rewrite Hcontra in HlookupSh1.
    destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
    - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *.
      rewrite Nat.add_sub_assoc in HlookupSh1; try(cbn; lia). destruct HlastBlock as [l HlastBlock].
      rewrite HlastBlock in HlookupSh1. congruence.
    - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb-1) by lia.
      specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE]. rewrite HnewBE in HlookupSh1. congruence.
  }
  rewrite Hlookups1s0Eq in HlookupSh1; try(assumption).
  specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). unfold isBE in *.
  destruct (lookup (inChildLocation sh1entry) (memory s0) beqAddr) eqn:HlookupLoc; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupLoc. assumption.
  (* END sh1InChildLocationIsBE *)
}

assert(StructurePointerIsKS s).
{ (* BEGIN StructurePointerIsKS s *)
  assert(Hcons0: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition pdentry HlookupPart HbeqStructNull.
  rewrite HpdsArePDT in HlookupPart; try(unfold isPDT; rewrite HlookupPart; trivial).
  specialize(Hcons0 partition pdentry HlookupPart HbeqStructNull). unfold isKS in *.
  destruct (lookup (structure pdentry) (memory s0) beqAddr) eqn:HlookupStruct; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupStruct. assumption.
  (* END StructurePointerIsKS *)
}

assert(HpaddrLookupEq: forall addr, beqAddr (CPaddr (kernStart+nextoffset)) addr = false
  -> isPADDR addr s
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
{
  intros addr HbeqNextAddr HaddrIsPADDR. unfold isPADDR in HaddrIsPADDR. rewrite Hs. rewrite Hs in HaddrIsPADDR.
  simpl. simpl in HaddrIsPADDR. rewrite HbeqNextAddr in *. rewrite <-DTL.beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
  assert(forall kernIdx : index, kernIdx < kernelStructureEntriesNb
    -> addr <> CPaddr (kernStart + kernIdx + scoffset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst addr. rewrite HnewSce in HaddrIsPADDR; assumption.
  }
  rewrite Hlookups2Eq; try(assumption). rewrite Hlookups2Eq in HaddrIsPADDR; try(assumption).
  assert(forall kernIdx : index, kernIdx < kernelStructureEntriesNb
    -> addr <> CPaddr (kernStart + kernIdx + sh1offset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst addr. rewrite HnewShe in HaddrIsPADDR; assumption.
  }
  rewrite Hlookups1Eq in HaddrIsPADDR; try(assumption).
  assert(forall kernIdx : index, kernIdx <= kernelStructureEntriesNb - 1 -> addr <> CPaddr (kernStart + kernIdx)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst addr.
    destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
    - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *.
      rewrite Nat.add_sub_assoc in HaddrIsPADDR; try(cbn; lia). destruct HlastBlock as [l HlastBlock].
      rewrite HlastBlock in *. congruence.
    - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb-1) by lia.
      specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE]. rewrite HnewBE in *. congruence.
  }
  apply Hlookups2s0Eq; assumption.
}

assert(NextKSIsKS s).
{ (* BEGIN NextKSIsKS s *)
  assert(Hcons0: NextKSIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull. unfold isKS in *.
  unfold nextKSAddr in *. unfold nextKSentry in *.
  assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  }
  rewrite HlookupKernEq in *.
  assert(HpropsOr: In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
    \/ ~In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
  destruct HpropsOr as [HkernIsNew | HkernNotNew].
  - apply getAllPaddrBlockInclRev in HkernIsNew.
    destruct HkernIsNew as (HlebKerns & HltKernKernPEntries & _).
    assert(Hidx: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ p kernel = kernStart + kernIdx).
    {
      exists (CIndex (kernel-kernStart)). assert(kernel <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      unfold CIndex. destruct (le_dec (kernel - kernStart) maxIdx); try(lia). simpl. split; try(lia).
      unfold CPaddr in HltKernKernPEntries.
      destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
    }
    destruct Hidx as [kernIdx (HltKIdxKernEntries & HKernEq)].
    assert(HkernEqBis: kernel = kernStart).
    {
      destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. exfalso.
        assert(Hkern: kernel = CPaddr(kernStart + kernelStructureEntriesNb - 1)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr.
          destruct (le_dec (kernStart + kernelStructureEntriesNb - 1) maxAddr); cbn in *; lia.
        }
        subst kernel. destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock in HkernIsKS. simpl in HkernIsKS.
        unfold zero in HkernIsKS. unfold CIndex in HkernIsKS. destruct (le_dec 0 maxIdx); try(lia).
        destruct (le_dec 7 maxIdx); try(rewrite maxIdxEqualMaxAddr in *; cbn in *; lia).
        injection HkernIsKS as Hcontra. lia.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE].
        assert(Hkern: kernel = CPaddr(kernStart + kernIdx)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); cbn in *; lia.
        }
        rewrite Hkern in HkernIsKS. rewrite HnewBE in HkernIsKS. simpl in HkernIsKS. unfold zero in HkernIsKS.
        subst kernIdx. apply DTL.paddrEqNatEqEquiv. rewrite HKernEq. unfold CIndex.
        destruct (le_dec 0 maxIdx); try(lia). simpl. lia.
    }
    rewrite HkernEqBis in *. destruct (lookup kernStart (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst nextKSaddr. exfalso. rewrite Hs in HnextKSAddr. simpl in HnextKSAddr.
    rewrite beqAddrTrue in HnextKSAddr. congruence.
  - assert(HlookupKernEqs1: lookup kernel (memory s1) beqAddr = lookup kernel (memory s0) beqAddr).
    {
      apply HblockUntouched; try(assumption). unfold isBE.
      destruct(lookup kernel (memory s1) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    rewrite HlookupKernEqs1 in *. destruct (beqAddr (CPaddr (kernStart + nextoffset)) nextKSaddr) eqn:HbeqNexts.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNexts. exfalso. destruct (lookup kernel (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). subst nextKSaddr. unfold CPaddr in HbeqNexts. unfold CPaddr in HnextKSAddr.
      assert(Hnull: isPADDR nullAddr s) by assumption. unfold isPADDR in Hnull.
      destruct (le_dec (kernStart + nextoffset) maxAddr); try(cbn in *; lia).
      destruct (le_dec (kernel + nextoffset) maxAddr).
      - injection HbeqNexts as HbeqNexts. apply Nat.add_cancel_r in HbeqNexts. contradict HkernNotNew.
        unfold CPaddr. destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); try(cbn in *; lia).
        apply getAllPaddrBlockIncl; cbn in *; lia.
      - injection HbeqNexts as HbeqNexts. cbn in *; lia.
    }
    rewrite HpaddrLookupEq in HnextKSAddr; try(assumption).
    + specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull). unfold isKS in Hcons0.
      destruct (lookup nextKS (memory s0) beqAddr) eqn:HlookupKS; try(exfalso; congruence).
      rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupKS. assumption.
    + unfold isPADDR. destruct (lookup nextKSaddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
      trivial.
  (* END NextKSIsKS *)
}

assert(NextKSOffsetIsPADDR s).
{ (* BEGIN NextKSOffsetIsPADDR s *)
  assert(Hcons0: NextKSOffsetIsPADDR s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros kernel nextKSaddr HkernIsKS HnextAddr. unfold isKS in *. unfold nextKSAddr in *.
  assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  }
  rewrite HlookupKernEq in *.
  assert(HpropsOr: In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
    \/ ~In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
  destruct HpropsOr as [HkernIsNew | HkernNotNew].
  - apply getAllPaddrBlockInclRev in HkernIsNew.
    destruct HkernIsNew as (HlebKerns & HltKernKernPEntries & _).
    assert(Hidx: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ p kernel = kernStart + kernIdx).
    {
      exists (CIndex (kernel-kernStart)). assert(kernel <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      unfold CIndex. destruct (le_dec (kernel - kernStart) maxIdx); try(lia). simpl. split; try(lia).
      unfold CPaddr in HltKernKernPEntries.
      destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
    }
    destruct Hidx as [kernIdx (HltKIdxKernEntries & HKernEq)].
    assert(HkernEqBis: kernel = kernStart).
    {
      destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. exfalso.
        assert(Hkern: kernel = CPaddr(kernStart + kernelStructureEntriesNb - 1)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr.
          destruct (le_dec (kernStart + kernelStructureEntriesNb - 1) maxAddr); cbn in *; lia.
        }
        subst kernel. destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock in HkernIsKS. simpl in HkernIsKS.
        unfold zero in HkernIsKS. unfold CIndex in HkernIsKS. destruct (le_dec 0 maxIdx); try(lia).
        destruct (le_dec 7 maxIdx); try(rewrite maxIdxEqualMaxAddr in *; cbn in *; lia).
        injection HkernIsKS as Hcontra. lia.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE].
        assert(Hkern: kernel = CPaddr(kernStart + kernIdx)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); cbn in *; lia.
        }
        rewrite Hkern in HkernIsKS. rewrite HnewBE in HkernIsKS. simpl in HkernIsKS. unfold zero in HkernIsKS.
        subst kernIdx. apply DTL.paddrEqNatEqEquiv. rewrite HKernEq. unfold CIndex.
        destruct (le_dec 0 maxIdx); try(lia). simpl. lia.
    }
    rewrite HkernEqBis in *. destruct (lookup kernStart (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst nextKSaddr. unfold isPADDR. rewrite Hs. simpl. rewrite beqAddrTrue.
    split. trivial. apply DTL.paddrNeqNatNeqEquiv. unfold nullAddr. unfold CPaddr.
    destruct (le_dec 0 maxAddr); try(lia). destruct (le_dec (kernStart + nextoffset) maxAddr); cbn in *; lia.
  - assert(HlookupKernEqs1: lookup kernel (memory s1) beqAddr = lookup kernel (memory s0) beqAddr).
    {
      apply HblockUntouched; try(assumption). unfold isBE.
      destruct(lookup kernel (memory s1) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    rewrite HlookupKernEqs1 in *. specialize(Hcons0 kernel nextKSaddr HkernIsKS HnextAddr).
    destruct Hcons0 as (HnextIsPADDR & HbeqNextNull). split; try(assumption). unfold isPADDR in *.
    destruct (lookup nextKSaddr (memory s0) beqAddr) eqn:HlookupNextA; try(exfalso; congruence).
    rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupNextA. assumption.
  (* END NextKSOffsetIsPADDR *)
}

assert(NoDupInFreeSlotsList s).
{ (* BEGIN NoDupInFreeSlotsList s *)
  assert(Hcons0: NoDupInFreeSlotsList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition pdentry HlookupPart. assert(isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial).
  rewrite HpdsArePDT in HlookupPart; try(assumption). specialize(Hcons0 partition pdentry HlookupPart).
  destruct Hcons0 as [optFreeList (Hlist & HwellFormed & HnoDup)]. exists optFreeList. intuition.
  rewrite HgetFreeEq; try(assumption). unfold isPDT. rewrite HlookupPart. trivial.
  (* END NoDupInFreeSlotsList *)
}

assert(freeSlotsListIsFreeSlot s).
{ (* BEGIN freeSlotsListIsFreeSlot s *)
  assert(Hcons0: freeSlotsListIsFreeSlot s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
  unfold isPDT in HpartIsPDT. rewrite HpdsArePDT in HpartIsPDT; try(assumption).
  rewrite HgetFreeEq in HwellFormed; try(assumption). specialize(Hcons0 partition addr optionfreeslotslist
    freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull). unfold isFreeSlot in *.
  destruct (lookup addr (memory s0) beqAddr) eqn:HlookupAddr; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupAddr. destruct v; try(congruence).
  destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupSh1. destruct v; try(congruence).
  destruct (lookup (CPaddr (addr + scoffset)) (memory s0) beqAddr) eqn:HlookupSce; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupSce. assumption.
  (* END freeSlotsListIsFreeSlot *)
}

assert(DisjointFreeSlotsLists s).
{ (* BEGIN DisjointFreeSlotsLists s *)
  assert(Hcons0: DisjointFreeSlotsLists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *.
  rewrite HpdsArePDT in Hpart1IsPDT; try(assumption). rewrite HpdsArePDT in Hpart2IsPDT; try(assumption).
  specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts).
  destruct Hcons0 as [optFreeList1 [optFreeList2 Hcons0]]. exists optFreeList1. exists optFreeList2.
  rewrite HgetFreeEq; try(assumption). rewrite HgetFreeEq; assumption.
  (* END DisjointFreeSlotsLists *)
}

assert(inclFreeSlotsBlockEntries s).
{ (* BEGIN inclFreeSlotsBlockEntries s *)
  assert(Hcons0: inclFreeSlotsBlockEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition HpartIsPDT. unfold isPDT in *. rewrite HpdsArePDT in HpartIsPDT; try(assumption).
  specialize(Hcons0 partition HpartIsPDT). rewrite HgetFreeEq; try(assumption). rewrite HgetKSEq; assumption.
  (* END inclFreeSlotsBlockEntries *)
}

assert(DisjointKSEntries s).
{ (* BEGIN DisjointKSEntries s *)
  assert(Hcons0: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *.
  rewrite HpdsArePDT in Hpart1IsPDT; try(assumption). rewrite HpdsArePDT in Hpart2IsPDT; try(assumption).
  specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). rewrite HgetKSEq; try(assumption).
  rewrite HgetKSEq; assumption.
  (* END DisjointKSEntries *)
}

assert(noDupPartitionTree s).
{ (* BEGIN noDupPartitionTree s *)
  assert(Hcons0: noDupPartitionTree s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  unfold noDupPartitionTree in *. rewrite HgetPartsEq. assumption.
  (* END noDupPartitionTree *)
}

assert(isParent s).
{ (* BEGIN isParent s *)
  assert(Hcons0: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEq in HparentIsPart.
  assert(isPDT pdparent s0).
  { apply partitionsArePDT; try(assumption); unfold consistency in *; unfold consistency1 in *; intuition. }
  rewrite HgetChildrenEq in HpartIsChild; try(assumption).
  specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent in *.
  destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupPart. assumption.
  (* END isParent *)
}

assert(isChild s).
{ (* BEGIN isChild s *)
  assert(Hcons0: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. unfold pdentryParent in HparentIsParent.
  assert(isPDT partition s) by (apply partitionsArePDT; assumption).
  rewrite HgetPartsEq in HpartIsPart. rewrite HpdsArePDT in HparentIsParent; try(assumption).
  specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
  rewrite HgetChildrenEq; try(assumption). unfold isPDT. unfold getChildren in Hcons0.
  destruct (lookup pdparent (memory s0) beqAddr); try(simpl in *; congruence).
  destruct v; try(simpl in *; congruence). trivial.
  (* END isChild *)
}

assert(noDupKSEntriesList s).
{ (* BEGIN noDupKSEntriesList s *)
  assert(Hcons0: noDupKSEntriesList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition HpartIsPDT. unfold isPDT in *. rewrite HpdsArePDT in HpartIsPDT; try(assumption).
  specialize(Hcons0 partition HpartIsPDT). rewrite HgetKSEq; assumption.
  (* END noDupKSEntriesList *)
}

assert(noDupMappedBlocksList s).
{ (* BEGIN noDupMappedBlocksList s *)
  assert(Hcons0: noDupMappedBlocksList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition HpartIsPDT. unfold isPDT in *. rewrite HpdsArePDT in HpartIsPDT; try(assumption).
  specialize(Hcons0 partition HpartIsPDT). rewrite HgetMappedEq; assumption.
  (* END noDupMappedBlocksList *)
}

assert(wellFormedBlock s).
{ (* BEGIN wellFormedBlock s *)
  assert(Hcons0: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros block startaddr endaddr HPflag HstartBlock HendBlock.
  assert(HlookupBlockEqss1: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. unfold bentryPFlag in HPflag.
    destruct (lookup block (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
  }
  unfold bentryPFlag in HPflag. unfold bentryStartAddr in HstartBlock. unfold bentryEndAddr in HendBlock.
  rewrite HlookupBlockEqss1 in *.
  assert(HlookupBlockEqs1s0: lookup block (memory s1) beqAddr = lookup block (memory s0) beqAddr).
  {
    apply Hlookups1s0Eq. intros kernIdx HlebIdxKernEntries Hcontra.
    destruct (Nat.eqb kernIdx (kernelStructureEntriesNb - 1)) eqn:HbeqIdxKernEntries.
    - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. destruct HlastBlock as [l HlastBlock].
      rewrite Nat.add_sub_assoc in Hcontra; try(cbn; lia). subst block. rewrite HlastBlock in *.
      simpl in HPflag. congruence.
    - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(HltIdxKernEntriesM: kernIdx < kernelStructureEntriesNb - 1).
      { lia. }
      specialize(HnewBE kernIdx HltIdxKernEntriesM). destruct HnewBE as [l HnewBE]. subst block. rewrite HnewBE in *.
      simpl in HPflag. congruence.
  }
  rewrite HlookupBlockEqs1s0 in *. specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock).
  assumption.
  (* END wellFormedBlock *)
}

assert(parentOfPartitionIsPartition s).
{ (* BEGIN parentOfPartitionIsPartition s *)
  assert(Hcons0: parentOfPartitionIsPartition s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition pdentry HlookupPart. rewrite HpdsArePDT in HlookupPart; try(unfold isPDT;
    destruct (lookup partition (memory s) beqAddr); try(congruence); destruct v; try(congruence); trivial).
  specialize(Hcons0 partition pdentry HlookupPart). destruct Hcons0 as (HparentIsPart & Hcons0).
  split; try(assumption). intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot). rewrite HgetPartsEq.
  destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; try(assumption).
  exists parentEntry. rewrite HlookupSomeEq; try(exists (PDT parentEntry)); assumption.
  (* END parentOfPartitionIsPartition *)
}

assert(NbFreeSlotsISNbFreeSlotsInList s).
{ (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
  assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0)
    by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in HpartIsPDT. unfold pdentryNbFreeSlots in HnbFree.
  rewrite HpdsArePDT in *; try(assumption). specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree).
  rewrite HgetFreeEq; assumption.
  (* END NbFreeSlotsISNbFreeSlotsInList *)
}

assert(HlookupNextEq: forall addr kern, lookup (CPaddr (addr + nextoffset)) (memory s) beqAddr = Some(PADDR kern)
  -> kern <> nullAddr
  -> lookup (CPaddr (addr + nextoffset)) (memory s) beqAddr
      = lookup (CPaddr (addr + nextoffset)) (memory s0) beqAddr).
{
  intros addr kern HlookupAddr HbeqKernNull.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) (CPaddr (addr + nextoffset))) eqn:HbeqNexts.
  {
    rewrite <-DTL.beqAddrTrue in HbeqNexts. rewrite <-HbeqNexts in *. rewrite Hs in HlookupAddr. simpl in HlookupAddr.
    rewrite beqAddrTrue in HlookupAddr. injection HlookupAddr as Hcontra. exfalso. congruence.
  }
  apply HpaddrLookupEq; try(assumption). unfold isPADDR. rewrite HlookupAddr. trivial.
}

assert(HlistOfKernEqss0: forall kernList partition, isListOfKernels kernList partition s
  -> isListOfKernels kernList partition s0).
{
  intros kernList partition HkernList. apply isListOfKernelsEqPreparess0 with s; assumption.
}

assert(maxNbPrepareIsMaxNbKernels s).
{ (* BEGIN maxNbPrepareIsMaxNbKernels s *)
  assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition kernList HlistOfKerns. apply HlistOfKernEqss0 in HlistOfKerns.
  specialize(Hcons0 partition kernList HlistOfKerns). assumption.
  (* END maxNbPrepareIsMaxNbKernels *)
}

assert(blockInChildHasAtLeastEquivalentBlockInParent s).
{ (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
  assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0)
    by (unfold consistency in *; unfold consistency1 in *; intuition). intros pdparent child block startChild endChild
  HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild.
  rewrite HgetPartsEq in HparentIsPart. rewrite HgetChildrenEq in HchildIsChild; try(apply partitionsArePDT;
    try(assumption); unfold consistency in *; unfold consistency1 in *; intuition).
  rewrite HgetMappedEq in HblockMappedChild; try(apply childrenArePDT with pdparent; try(assumption);
    unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HlookupBlockEqss1: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. unfold bentryPFlag in HPflagChild.
    destruct (lookup block (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
  }
  unfold bentryPFlag in HPflagChild. unfold bentryStartAddr in HstartChild. unfold bentryEndAddr in HendChild.
  rewrite HlookupBlockEqss1 in *.
  assert(HlookupBlockEqs1s0: lookup block (memory s1) beqAddr = lookup block (memory s0) beqAddr).
  {
    apply Hlookups1s0Eq. intros kernIdx HlebIdxKernEntries Hcontra.
    destruct (Nat.eqb kernIdx (kernelStructureEntriesNb - 1)) eqn:HbeqIdxKernEntries.
    - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. destruct HlastBlock as [l HlastBlock].
      rewrite Nat.add_sub_assoc in Hcontra; try(cbn; lia). subst block. rewrite HlastBlock in *.
      simpl in HPflagChild. congruence.
    - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(HltIdxKernEntriesM: kernIdx < kernelStructureEntriesNb - 1).
      { lia. }
      specialize(HnewBE kernIdx HltIdxKernEntriesM). destruct HnewBE as [l HnewBE]. subst block. rewrite HnewBE in *.
      simpl in HPflagChild. congruence.
  }
  rewrite HlookupBlockEqs1s0 in *. specialize(Hcons0 pdparent child block startChild endChild HparentIsPart
    HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild).
  destruct Hcons0 as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & Hcons0)]]].
  exists blockParent. exists startParent. exists endParent. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
  rewrite HgetMappedEq; try(apply partitionsArePDT; try(assumption); unfold consistency in *;
    unfold consistency1 in *; intuition). split. assumption.
  destruct (lookup blockParent (memory s0) beqAddr) eqn:HlookupBlockP; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupBlockP. split; assumption.
  
  (* END blockInChildHasAtLeastEquivalentBlockInParent *)
}

assert(partitionTreeIsTree s).
{ (* BEGIN partitionTreeIsTree s *)
  assert(Hcons0: partitionTreeIsTree s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
  apply isParentsListEqPreparess0 with parentsList pdparent s s0 in HparentsList; try(assumption).
  unfold pdentryParent in HparentIsParent. rewrite HpdsArePDT in HparentIsParent;
    try(apply partitionsArePDT; assumption). rewrite HgetPartsEq in HchildIsPart.
  specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList). assumption.
  (* END partitionTreeIsTree *)
}

assert(kernelEntriesAreValid s).
{ (* BEGIN kernelEntriesAreValid s *)
  assert(Hcons0: kernelEntriesAreValid s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros kernel idx HkernIsKS Hidx. unfold isKS in *.
  assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  }
  rewrite HlookupKernEq in *.
  assert(HpropsOr: In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
    \/ ~In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
  destruct HpropsOr as [HkernIsNew | HkernNotNew].
  - apply getAllPaddrBlockInclRev in HkernIsNew.
    destruct HkernIsNew as (HlebKerns & HltKernKernPEntries & _).
    assert(HkernIdx: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ p kernel = kernStart + kernIdx).
    {
      exists (CIndex (kernel-kernStart)). assert(kernel <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      unfold CIndex. destruct (le_dec (kernel - kernStart) maxIdx); try(lia). simpl. split; try(lia).
      unfold CPaddr in HltKernKernPEntries.
      destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
    }
    destruct HkernIdx as [kernIdx (HltKIdxKernEntries & HKernEq)].
    assert(HkernEqBis: kernel = kernStart).
    {
      destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. exfalso.
        assert(Hkern: kernel = CPaddr(kernStart + kernelStructureEntriesNb - 1)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr.
          destruct (le_dec (kernStart + kernelStructureEntriesNb - 1) maxAddr); cbn in *; lia.
        }
        subst kernel. destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock in HkernIsKS. simpl in HkernIsKS.
        unfold zero in HkernIsKS. unfold CIndex in HkernIsKS. destruct (le_dec 0 maxIdx); try(lia).
        destruct (le_dec 7 maxIdx); try(rewrite maxIdxEqualMaxAddr in *; cbn in *; lia).
        injection HkernIsKS as Hcontra. lia.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE].
        assert(Hkern: kernel = CPaddr(kernStart + kernIdx)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); cbn in *; lia.
        }
        rewrite Hkern in HkernIsKS. rewrite HnewBE in HkernIsKS. simpl in HkernIsKS. unfold zero in HkernIsKS.
        subst kernIdx. apply DTL.paddrEqNatEqEquiv. rewrite HKernEq. unfold CIndex.
        destruct (le_dec 0 maxIdx); try(lia). simpl. lia.
    }
    rewrite HkernEqBis in *. assert(isBE (CPaddr (kernStart + idx)) s1).
    {
      unfold isBE. destruct (Nat.eqb idx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *.
        rewrite Nat.add_sub_assoc; try(cbn; lia). destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock. trivial.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. unfold CIndex in Hidx.
        destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(rewrite maxIdxEqualMaxAddr in *; cbn in *; lia).
        simpl in Hidx. assert(HidxEq: idx = CIndex idx).
        {
          unfold CIndex. destruct (le_dec idx maxIdx); try(rewrite maxIdxEqualMaxAddr in *; lia). simpl. reflexivity.
        }
        assert(Hlt: CIndex idx < kernelStructureEntriesNb-1) by (cbn in *; lia). specialize(HnewBE (CIndex idx) Hlt).
        destruct HnewBE as [h HnewBE]. rewrite <-HidxEq in HnewBE. rewrite HnewBE. trivial.
    }
    unfold isBE in *. rewrite HblocksAreBEs1s; assumption.
  - assert(HlookupKernEqs1: lookup kernel (memory s1) beqAddr = lookup kernel (memory s0) beqAddr).
    {
      apply HblockUntouched; try(assumption). unfold isBE.
      destruct(lookup kernel (memory s1) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    rewrite HlookupKernEqs1 in *. specialize(Hcons0 kernel idx HkernIsKS Hidx). unfold isBE in *.
    destruct (lookup (CPaddr (kernel + idx)) (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
    rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupBlock. assumption.
  (* END kernelEntriesAreValid *)
}

assert(nextKernelIsValid s).
{ (* BEGIN nextKernelIsValid s *)
  assert(Hcons0: nextKernelIsValid s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros kernel HkernIsKS. unfold isKS in *.
  assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). trivial.
  }
  rewrite HlookupKernEq in *.
  assert(HpropsOr: In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
    \/ ~In kernel (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
  destruct HpropsOr as [HkernIsNew | HkernNotNew].
  - apply getAllPaddrBlockInclRev in HkernIsNew.
    destruct HkernIsNew as (HlebKerns & HltKernKernPEntries & _).
    assert(HkernIdx: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ p kernel = kernStart + kernIdx).
    {
      exists (CIndex (kernel-kernStart)). assert(kernel <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      unfold CIndex. destruct (le_dec (kernel - kernStart) maxIdx); try(lia). simpl. split; try(lia).
      unfold CPaddr in HltKernKernPEntries.
      destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
    }
    destruct HkernIdx as [kernIdx (HltKIdxKernEntries & HKernEq)].
    assert(HkernEqBis: kernel = kernStart).
    {
      destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. exfalso.
        assert(Hkern: kernel = CPaddr(kernStart + kernelStructureEntriesNb - 1)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr.
          destruct (le_dec (kernStart + kernelStructureEntriesNb - 1) maxAddr); cbn in *; lia.
        }
        subst kernel. destruct HlastBlock as [l HlastBlock]. rewrite HlastBlock in HkernIsKS. simpl in HkernIsKS.
        unfold zero in HkernIsKS. unfold CIndex in HkernIsKS. destruct (le_dec 0 maxIdx); try(lia).
        destruct (le_dec 7 maxIdx); try(rewrite maxIdxEqualMaxAddr in *; cbn in *; lia).
        injection HkernIsKS as Hcontra. lia.
      - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb - 1) by lia.
        specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE].
        assert(Hkern: kernel = CPaddr(kernStart + kernIdx)).
        {
          apply DTL.paddrEqNatEqEquiv. unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); cbn in *; lia.
        }
        rewrite Hkern in HkernIsKS. rewrite HnewBE in HkernIsKS. simpl in HkernIsKS. unfold zero in HkernIsKS.
        subst kernIdx. apply DTL.paddrEqNatEqEquiv. rewrite HKernEq. unfold CIndex.
        destruct (le_dec 0 maxIdx); try(lia). simpl. lia.
    }
    rewrite HkernEqBis in *. split. cbn in *; lia. exists nullAddr. split.
    + intro. rewrite Hs. simpl.
      assert(Heq: beqAddr (CPaddr (kernStart + nextoffset)) {| p := kernStart + nextoffset; Hp := Hp |} = true).
      {
        rewrite <-DTL.beqAddrTrue. unfold CPaddr. destruct (le_dec (kernStart + nextoffset) maxAddr); try(lia).
        f_equal. apply proof_irrelevance.
      }
      rewrite Heq. reflexivity.
    + right. reflexivity.
  - assert(HlookupKernEqs1: lookup kernel (memory s1) beqAddr = lookup kernel (memory s0) beqAddr).
    {
      apply HblockUntouched; try(assumption). unfold isBE.
      destruct(lookup kernel (memory s1) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    rewrite HlookupKernEqs1 in *. specialize(Hcons0 kernel HkernIsKS).
    destruct Hcons0 as (Hleb & [nextAddr (Hlookup & Hnext)]). split. assumption. exists nextAddr. split.
    + intro Hp. specialize(Hlookup Hp). destruct (lookup {| p := kernel + nextoffset; Hp := Hp |} (memory s0) beqAddr)
        eqn:HlookupNext; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists v; assumption).
      rewrite HlookupNext. assumption.
    + destruct Hnext as [HKS | Hnull]; try(right; assumption). left. unfold isKS in *.
      destruct (lookup nextAddr (memory s0) beqAddr) eqn:HlookupNext; try(exfalso; congruence).
      rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupNext. assumption.
  (* END nextKernelIsValid *)
}

assert(noDupListOfKerns s).
{ (* BEGIN noDupListOfKerns s *)
  assert(Hcons0: noDupListOfKerns s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition kernList HlistOfKerns. apply HlistOfKernEqss0 in HlistOfKerns.
  specialize(Hcons0 partition kernList HlistOfKerns). assumption.
  (* END noDupListOfKerns *)
}

assert(MPUsizeIsBelowMax s).
{ (* BEGIN MPUsizeIsBelowMax s *)
  assert(Hcons0: MPUsizeIsBelowMax s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition MPUlist HMPU. unfold pdentryMPU in *. rewrite HpdsArePDT in HMPU; try(unfold isPDT;
    destruct (lookup partition (memory s) beqAddr); try(congruence); destruct v; try(congruence); trivial).
  specialize(Hcons0 partition MPUlist HMPU). assumption.
  (* END MPUsizeIsBelowMax *)
}

assert(HaddrAreSCEs2s0: forall addr, isSCE addr s2
  -> lookup addr (memory s2) beqAddr = lookup addr (memory s0) beqAddr).
{
  intros addr HaddrIsSCE. unfold isSCE in HaddrIsSCE.
  assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb -> addr <> CPaddr (kernStart+kernIdx+sh1offset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst addr. specialize(HnewShe kernIdx HltIdxKernEntries).
    rewrite HnewShe in HaddrIsSCE. congruence.
  }
  rewrite Hlookups1Eq in HaddrIsSCE; try(assumption).
  assert(forall kernIdx: index, kernIdx <= kernelStructureEntriesNb - 1 -> addr <> CPaddr (kernStart + kernIdx)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst addr.
    destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
    - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *.
      rewrite Nat.add_sub_assoc in HaddrIsSCE; try(cbn; lia). destruct HlastBlock as [l HlastBlock].
      rewrite HlastBlock in *. congruence.
    - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(Hlt: kernIdx < kernelStructureEntriesNb-1) by lia.
      specialize(HnewBE kernIdx Hlt). destruct HnewBE as [l HnewBE]. rewrite HnewBE in *. congruence.
  }
  apply Hlookups2s0Eq; assumption.
}

assert(originIsParentBlocksStart s).
{ (* BEGIN originIsParentBlocksStart s *)
  assert(Hcons0: originIsParentBlocksStart s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
  rewrite HgetPartsEq in HpartIsPart. rewrite HpdsArePDT in HlookupPart; try(unfold isPDT; rewrite HlookupPart;
    trivial). rewrite HgetMappedEq in HblockMapped; try(unfold isPDT; rewrite HlookupPart; trivial).
  assert(HoriginCopy: scentryOrigin scentryaddr scorigin s) by assumption.
  unfold scentryOrigin in *. rewrite Hs in Horigin. simpl in Horigin.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) scentryaddr) eqn:HbeqNextSce; try(exfalso; congruence).
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity in Horigin; try(apply not_eq_sym; assumption).
  assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
    -> scentryaddr <> CPaddr (kernStart+kernIdx+scoffset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst scentryaddr. exfalso.
    assert(HblockEq: block = CPaddr (kernStart + kernIdx)).
    {
      unfold CPaddr in Hcontra. destruct (le_dec (kernStart + kernIdx + scoffset) maxAddr); try(cbn in *; lia).
      unfold nullAddrExists in *. unfold isPADDR in *. unfold CPaddr in HoriginCopy.
      destruct (le_dec (block + scoffset) maxAddr).
      - injection Hcontra as Hcontra. rewrite Nat.add_cancel_r in Hcontra. apply DTL.paddrEqNatEqEquiv.
        unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia). simpl. assumption.
      - exfalso. assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + scoffset) n |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HnullEq in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBlock & _)].
    assert(HblockInRange: In block (getAllPaddrBlock kernStart kernEnd)).
    {
      subst block. unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); try(cbn in *; lia).
      apply getAllPaddrBlockIncl; cbn in *; lia.
    }
    specialize(HlookupNones0 block HblockInRange). congruence.
  }
  rewrite Hlookups2Eq in Horigin; try(assumption). rewrite HaddrAreSCEs2s0 in Horigin; try(unfold isSCE;
    destruct (lookup scentryaddr (memory s2) beqAddr); try(congruence); destruct v; try(congruence); trivial).
  specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin).
  destruct Hcons0 as (HparentBlock & HlebStart). split.
  - intro HbeqPartRoot. specialize(HparentBlock HbeqPartRoot).
    destruct HparentBlock as [blockParent (HblockParentMapped & HstartParent & Hincl)]. exists blockParent.
    rewrite HgetMappedEq; try(unfold isPDT; unfold getMappedBlocks in *; unfold getKSEntries in *;
      destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in HblockParentMapped; congruence);
      destruct v; try(simpl in HblockParentMapped; congruence); trivial). split. assumption. simpl. simpl in Hincl.
    unfold bentryStartAddr in *. destruct (lookup blockParent (memory s0) beqAddr) eqn:HlookupBlockP;
      try(exfalso; congruence). rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupBlockP. split.
    assumption. intros addr HaddrInBlock. apply Hincl. apply mappedBlockIsBE in HblockMapped.
    destruct HblockMapped as [bentry (HlookupBlock & _)].
    rewrite HlookupSomeEq in HaddrInBlock; try(exists (BE bentry); assumption). assumption.
  - intros startaddr Hstart. apply HlebStart. unfold bentryStartAddr in *. apply mappedBlockIsBE in HblockMapped.
    destruct HblockMapped as [bentry (HlookupBlock & _)].
    rewrite HlookupSomeEq in Hstart; try(exists (BE bentry); assumption). assumption.
  (* END originIsParentBlocksStart *)
}

assert(nextImpliesBlockWasCut s).
{ (* BEGIN nextImpliesBlockWasCut s *)
  assert(Hcons0: nextImpliesBlockWasCut s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock Hsce
    HbeqNextNull Hnext HbeqPartRoot. rewrite HpdsArePDT in HlookupPart; try(unfold isPDT; rewrite HlookupPart;
    trivial). rewrite HgetMappedEq in HblockMapped; try(unfold isPDT; rewrite HlookupPart; trivial).
  assert(HnextCopy: scentryNext scentryaddr scnext s) by assumption. rewrite HgetPartsEq in HpartIsPart.
  unfold scentryNext in *. rewrite Hs in Hnext. simpl in Hnext.
  destruct (beqAddr (CPaddr (kernStart + nextoffset)) scentryaddr) eqn:HbeqNextSce; try(exfalso; congruence).
  rewrite <-DTL.beqAddrFalse in *. rewrite removeDupIdentity in Hnext; try(apply not_eq_sym; assumption).
  assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
    -> scentryaddr <> CPaddr (kernStart+kernIdx+scoffset)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst scentryaddr. exfalso.
    assert(HblockEq: block = CPaddr (kernStart + kernIdx)).
    {
      unfold CPaddr in Hcontra. destruct (le_dec (kernStart + kernIdx + scoffset) maxAddr); try(cbn in *; lia).
      unfold nullAddrExists in *. unfold isPADDR in *. unfold CPaddr in HnextCopy.
      destruct (le_dec (block + scoffset) maxAddr).
      - injection Hcontra as Hcontra. rewrite Nat.add_cancel_r in Hcontra. apply DTL.paddrEqNatEqEquiv.
        unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); try(lia). simpl. assumption.
      - exfalso. assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + scoffset) n |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HnullEq in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBlock & _)].
    assert(HblockInRange: In block (getAllPaddrBlock kernStart kernEnd)).
    {
      subst block. unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); try(cbn in *; lia).
      apply getAllPaddrBlockIncl; cbn in *; lia.
    }
    specialize(HlookupNones0 block HblockInRange). congruence.
  }
  rewrite Hlookups2Eq in Hnext; try(assumption). rewrite HaddrAreSCEs2s0 in Hnext; try(unfold isSCE;
    destruct (lookup scentryaddr (memory s2) beqAddr); try(congruence); destruct v; try(congruence); trivial).
  assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
  {
    apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
    apply HlookupSomeEq; exists (BE bentry); assumption.
  }
  unfold bentryEndAddr in *. rewrite HlookupBlockEq in *.
  specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
    Hsce HbeqNextNull Hnext HbeqPartRoot). destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent
    & HltEnd & Hincl)]]. exists blockParent. exists endParent. rewrite HgetMappedEq; try(unfold isPDT;
    unfold getMappedBlocks in *; unfold getKSEntries in *; destruct (lookup (parent pdentry) (memory s0) beqAddr);
    try(simpl in HblockParentMapped; congruence); destruct v; try(simpl in HblockParentMapped; congruence); trivial).
  split. assumption. simpl. rewrite HlookupBlockEq. simpl in Hincl. unfold bentryEndAddr in *.
  destruct (lookup blockParent (memory s0) beqAddr) eqn:HlookupBlockP; try(exfalso; congruence).
  rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupBlockP. split. assumption. split; assumption.
  (* END nextImpliesBlockWasCut *)
}

assert(blocksAddressesTypes s).
{ (* BEGIN blocksAddressesTypes s *)
  assert(Hcons0: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros block startaddr endaddr HstartBlock HendBlock HPDchild.
  assert(HlookupBlockEqss1: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. unfold bentryStartAddr in HstartBlock.
    destruct (lookup block (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
  }
  unfold bentryStartAddr in HstartBlock. unfold bentryEndAddr in HendBlock. rewrite HlookupBlockEqss1 in *.
  (*assert(HlookupBlockEqs1s0: lookup block (memory s1) beqAddr = lookup block (memory s0) beqAddr).
  {
    apply Hlookups1s0Eq. intros kernIdx HlebIdxKernEntries Hcontra.
    destruct (Nat.eqb kernIdx (kernelStructureEntriesNb - 1)) eqn:HbeqIdxKernEntries.
    - apply Nat.eqb_eq in HbeqIdxKernEntries. rewrite HbeqIdxKernEntries in *. destruct HlastBlock as [l HlastBlock].
      rewrite Nat.add_sub_assoc in Hcontra; try(cbn; lia). subst block. rewrite HlastBlock in *.
      simpl in HPflagChild. congruence.
    - apply Nat.eqb_neq in HbeqIdxKernEntries. assert(HltIdxKernEntriesM: kernIdx < kernelStructureEntriesNb - 1).
      { lia. }
      specialize(HnewBE kernIdx HltIdxKernEntriesM). destruct HnewBE as [l HnewBE]. subst block. rewrite HnewBE in *.
      simpl in HPflagChild. congruence.
  }
  rewrite HlookupBlockEqs1s0 in *.*)
  admit.
  
  
  
  
  
  
  
  (* END blocksAddressesTypes *)
}

assert(notPDTIfNotPDflag s).
{ (* BEGIN notPDTIfNotPDflag s *)
  assert(Hcons0: notPDTIfNotPDflag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros block startaddr sh1entryaddr HstartBlock Hsh1 HPDflag HPDchild.
  assert(HlookupBlockEqss1: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
  {
    apply HblocksAreBEss1. unfold isBE. unfold bentryStartAddr in HstartBlock.
    destruct (lookup block (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
  }
  unfold bentryStartAddr in HstartBlock. unfold sh1entryAddr in Hsh1. rewrite HlookupBlockEqss1 in *.
  unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
  assert(HlookupSh1Eqss2: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s2) beqAddr).
  {
    apply HaddrAreSHEss2. unfold isSHE.
    destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence). destruct v; trivial; congruence.
  }
  rewrite HlookupSh1Eqss2 in *.
  assert(HpropsOr: In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))
    \/ ~In block (getAllPaddrBlock kernStart (CPaddr (kernStart + kernelStructureEntriesNb)))) by (apply classic).
  destruct HpropsOr as [HblockIsNew | HblockNotNew].
  - apply getAllPaddrBlockInclRev in HblockIsNew.
    destruct HblockIsNew as (HlebBlockKern & HltBlockKernPEntries & _).
    assert(HkernIdx: exists kernIdx: index, kernIdx < kernelStructureEntriesNb /\ block = CPaddr(kernStart+kernIdx)).
    {
      exists (CIndex (block-kernStart)). assert(block <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
      unfold CIndex. destruct (le_dec (block - kernStart) maxIdx); try(lia). simpl. Search(?a + (?b-?c)). split; try(lia).
      unfold CPaddr in HltBlockKernPEntries.
      destruct (le_dec (kernStart + kernelStructureEntriesNb) maxAddr); cbn in *; lia.
    }
    destruct HkernIdx as [kernIdx (HltKIdxKernEntries & HKernEq)].
  - 
  assert(forall kernIdx: index, kernIdx <= kernelStructureEntriesNb - 1 -> block <> CPaddr (kernStart + kernIdx)).
  {
    intros kernIdx HltIdxKernEntries Hcontra. subst block.
    destruct (lookup (CPaddr (kernStart + kernIdx)) (memory s1) beqAddr); try(congruence).
    destruct v; try(congruence). assert(Hsh1Eq: CPaddr (kernStart+kernIdx)+sh1offset = kernStart+kernIdx+sh1offset).
    {
      unfold CPaddr. destruct (le_dec (kernStart + kernIdx) maxAddr); cbn in *; lia.
    }
    rewrite Hsh1Eq in Hsh1. subst sh1entryaddr. assert(Hlt: kernIdx < kernelStructureEntriesNb) by (cbn in *; lia).
    specialize(HnewShe kernIdx Hlt). rewrite HnewShe in *.
  }
  
  
  
  (* END notPDTIfNotPDflag *)
}

assert(nextKernAddrIsInSameBlock s).
{ (* BEGIN nextKernAddrIsInSameBlock s *)
  assert(Hcons0: nextKernAddrIsInSameBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros block kernel startaddr endaddr HstartBlock HendBlock HkernIsKS.
  
  
  
  
  (* END nextKernAddrIsInSameBlock *)
}

assert(blockBelongsToAPart s).
{ (* BEGIN blockBelongsToAPart s *)
  assert(Hcons0: blockBelongsToAPart s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros block HblockIsBE.
  
  
  
  
  (* END blockBelongsToAPart *)
}

assert(PDflagMeansNoChild s).
{ (* BEGIN PDflagMeansNoChild s *)
  assert(Hcons0: PDflagMeansNoChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  intros block HblockIsBE.
  
  
  
  
  (* END PDflagMeansNoChild *)
}


Qed.
