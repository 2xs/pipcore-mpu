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
Require Import (*Model.ADT*) Model.Monad Model.Lib
               Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants
               Proof.InternalLemmas2.
Require Import Proof.invariants.findBlockInKSWithAddr Proof.invariants.checkBlockCut freeSlot
               writeAccessibleToAncestorsIfNotCutRec.
From Stdlib Require Import Logic.ProofIrrelevance Lia Setoid Compare_dec (*EqNat*) List Bool FunctionalExtensionality.
Import List.ListNotations FunctionalExtensionality.

Fixpoint checkRemoveOkRec block partition blocksList s := match blocksList with
  | [] => True
  | blockChild::blocksListRec => bentryAFlag block true s /\ bentryPFlag block true s
      /\ In block (getMappedBlocks partition s)
      /\ sh1entryPDchild (CPaddr (block+sh1offset)) nullAddr s
      /\ scentryNext (CPaddr (block+scoffset)) blockChild s
      /\ (blockChild <> nullAddr -> In blockChild (getMappedBlocks partition s)
            /\ (forall endaddr, bentryEndAddr block endaddr s -> bentryStartAddr blockChild endaddr s))
      /\ checkRemoveOkRec blockChild partition blocksListRec s
  end.

Lemma checkRemoveSubblocksRecAux n (blockToRemove firstBlockToRemove partition : paddr) (P : state -> Prop) :
{{ fun s : state => P s /\ isBE blockToRemove s
      /\ In blockToRemove (getMappedBlocks partition s)
      /\ In partition (getPartitions multiplexer s)
      /\ consistency s
      /\ exists blocksList, checkRemoveOkRec firstBlockToRemove partition blocksList s
          /\ blockToRemove = last blocksList firstBlockToRemove
}}
checkRemoveSubblocksRecAux n blockToRemove
{{ fun isRemovePossible s => P s
    /\ (isRemovePossible = true
        -> exists blocksList, checkRemoveOkRec firstBlockToRemove partition blocksList s
            /\ nullAddr = last blocksList firstBlockToRemove)
}}.
Proof.
revert blockToRemove. induction n; simpl; intro blockToRemove.
- eapply weaken. apply ret. simpl. intros s (HP & _). split; trivial. intro Hcontra. exfalso; congruence.
- eapply bindRev.
  { (** MAL.readBlockAccessibleFromBlockEntryAddr*)
    eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
    intros s Hprops. simpl. split. apply Hprops. intuition.
  }
  intro isAccessible. eapply bindRev.
  { (** MAL.readBlockPresentFromBlockEntryAddr*)
    eapply weaken. apply readBlockPresentFromBlockEntryAddr.
    intros s Hprops. simpl. split. apply Hprops. intuition.
  }
  intro isPresent. eapply bindRev.
  { (** MAL.readSh1PDChildFromBlockEntryAddr*)
    eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
    intros s Hprops. simpl. destruct Hprops as (((HP & HblockIsBE & HblockMapped & HpartIsPart & Hconsist &
      HblocksList) & HAflag) & HPflag).
    instantiate(1 := fun s => P s /\ isBE blockToRemove s
      /\ In blockToRemove (getMappedBlocks partition s)
      /\ In partition (getPartitions multiplexer s)
      /\ consistency s
      /\ (exists blocksList, checkRemoveOkRec firstBlockToRemove partition blocksList s
          /\ blockToRemove = last blocksList firstBlockToRemove)
      /\ bentryAFlag blockToRemove isAccessible s
      /\ bentryPFlag blockToRemove isPresent s).
    unfold consistency in *; unfold consistency1 in *; intuition. apply isBELookupEq; assumption.
  }
  intro PDChildAddr. eapply bindRev.
  { (** Internal.compareAddrToNull*)
    eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
  }
  intro PDChildAddrIsNull. destruct (isAccessible && isPresent && PDChildAddrIsNull) eqn:HcheckBlock.
  * (* case isAccessible && isPresent && PDChildAddrIsNull = true *)
    eapply bindRev.
    { (** MAL.readSCNextFromBlockEntryAddr*)
      eapply weaken. apply readSCNextFromBlockEntryAddr. intros s Hprops. simpl.
      destruct Hprops as (((HP & HblockIsBE & HblockMapped & HpartIsPart & Hconsist & HblocksList & HAflag & HPflag) &
        Hsh1) & HbeqNullPDchild).
      apply andb_prop in HcheckBlock. destruct HcheckBlock as (HcheckBlock & HPDchild). subst PDChildAddrIsNull.
      apply andb_prop in HcheckBlock. destruct HcheckBlock as (Hacc & Hpres). subst isAccessible. subst isPresent.
      rewrite <-beqAddrTrue in HbeqNullPDchild. subst PDChildAddr.
      instantiate(1 := fun s => P s /\ isBE blockToRemove s
        /\ In blockToRemove (getMappedBlocks partition s)
        /\ In partition (getPartitions multiplexer s)
        /\ consistency s
        /\ (exists blocksList, checkRemoveOkRec firstBlockToRemove partition blocksList s
            /\ blockToRemove = last blocksList firstBlockToRemove)
        /\ bentryAFlag blockToRemove true s
        /\ bentryPFlag blockToRemove true s
        /\ (exists sh1entry sh1entryaddr,
            lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry)
            /\ sh1entryPDchild sh1entryaddr nullAddr s /\ sh1entryAddr blockToRemove sh1entryaddr s)).
      unfold consistency in *; unfold consistency1 in *; intuition.
      apply isBELookupEq; assumption.
    }
    intro nextsubblock. eapply bindRev.
    { (** Internal.compareAddrToNull*)
      eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
    }
    intro isNull. destruct isNull.
    + (* case isNull = true *)
      (** ret *)
      eapply weaken. apply ret. intros s Hprops. simpl.
      destruct Hprops as (((HP & HblockIsBE & HblockMapped & HpartIsPart & Hconsist & [blocksList (HblocksList &
        Hlast)] & HAflag & HPflag & [sh1entry [sh1entryaddr (HlookupSh1 & HPDchild & Hsh1)]]) & Hnext) &
        HbeqNullNext).
      unfold sh1entryAddr in *. destruct (lookup blockToRemove (memory s) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). subst sh1entryaddr. rewrite <-beqAddrTrue in HbeqNullNext.
      subst nextsubblock. split; trivial. intro. exists (blocksList++[nullAddr]). clear IHn.
      revert firstBlockToRemove Hlast HblocksList.
      induction blocksList; intros firstBlockToRemove Hlast HblocksList; cbn -[nullAddr last] in *.
      --- simpl in *. subst blockToRemove. intuition.
      --- destruct HblocksList as (HAflagFirst & HPflagFirst & HfirstMapped & HPDchildFirst & HnextFirst &
            HnextBlockSidePartial & HblocksListRec).
          apply IL.lastRec in Hlast. specialize(IHblocksList a Hlast HblocksListRec).
          destruct IHblocksList as (IHblocksList & HlastFinal). split. intuition. apply IL.lastRecInc. assumption.
    + (* case isNull = false *)
      eapply weaken. apply IHn. intros s Hprops. simpl.
      destruct Hprops as (((HP & HblockIsBE & HblockMapped & HpartIsPart & Hconsist & [blocksList (HblocksList &
        Hlast)] & HAflag & HPflag & [sh1entry [sh1entryaddr (HlookupSh1 & HPDchild & Hsh1)]]) & Hnext) &
        HbeqNullNext).
      assert(HnextBlockSide: blockAndNextAreSideBySide s)
        by (unfold consistency in *; unfold consistency2 in *; intuition). rewrite <-beqAddrFalse in *.
      apply not_eq_sym in HbeqNullNext.
      assert(Hend: exists endaddr, bentryEndAddr blockToRemove endaddr s).
      {
        unfold isBE in *. unfold bentryEndAddr.
        destruct (lookup blockToRemove (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
      }
      destruct Hend as [endaddr Hend].
      assert(HeqTriv: CPaddr (blockToRemove + scoffset) =  CPaddr (blockToRemove + scoffset)) by reflexivity.
      specialize(HnextBlockSide partition blockToRemove (CPaddr (blockToRemove + scoffset)) nextsubblock endaddr
        HpartIsPart HblockMapped Hend HeqTriv HbeqNullNext Hnext).
      destruct HnextBlockSide as (HstartNext & HnextMapped). assert(isBE nextsubblock s).
      {
        unfold isBE. unfold bentryStartAddr in *.
        destruct (lookup nextsubblock (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
      }
      split; trivial. split; trivial. split; trivial. split; trivial. split; trivial.
      exists (blocksList ++ [nextsubblock]). clear IHn. revert firstBlockToRemove HblocksList Hlast.
      induction blocksList; cbn -[last nullAddr] in *; intros firstBlockToRemove HblocksList Hlast.
      --- simpl in *. subst blockToRemove. unfold sh1entryAddr in *.
          destruct (lookup firstBlockToRemove (memory s) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). subst sh1entryaddr.
          assert(forall endaddrBis, bentryEndAddr firstBlockToRemove endaddrBis s
            -> bentryStartAddr nextsubblock endaddrBis s).
          {
            intros endBis HendBis. unfold bentryEndAddr in *.
            destruct (lookup firstBlockToRemove (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). subst endBis. rewrite <-Hend. assumption.
          }
          intuition.
      --- destruct HblocksList as (HAflagFirst & HPflagFirst & HfirstMapped & HPDchildFirst & HnextFirst &
            HnextBlockSidePartial & HblocksList).
          apply IL.lastRec in Hlast. specialize(IHblocksList a HblocksList Hlast).
          destruct IHblocksList as (HblocksListRec & HlastRec). split. intuition. apply eq_sym.
          replace (a :: blocksList ++ [nextsubblock]) with ((a::blocksList) ++ [nextsubblock]); try(apply last_last).
          auto.
  * (*case_eq isAccessible && isPresent && PDChildAddrIsNull = false *)
    (*apply andb_false_iff in HcheckBlock.*)
    unfold negb. eapply weaken. apply ret. intros s Hprops. simpl.
    destruct Hprops as (((HP & HblockIsBE & HblockMapped & HpartIsPart & Hconsist & HblocksList & HAflag & HPflag) &
      Hsh1) & HbeqNullPDchild). split; trivial. intro Hcontra. exfalso; congruence.
Qed.

Lemma checkRemoveSubblocksRec (blockToRemove firstBlockToRemove removePart: paddr) (P : state -> Prop) :
{{ fun s : state => P s /\ isBE blockToRemove s
      /\ In blockToRemove (getMappedBlocks removePart s)
      /\ In removePart (getPartitions multiplexer s)
      /\ consistency s
      /\ exists blocksList, checkRemoveOkRec firstBlockToRemove removePart blocksList s
          /\ blockToRemove = last blocksList firstBlockToRemove
}}
checkRemoveSubblocksRec blockToRemove
{{ fun isRemovePossible s => P s
    /\ (isRemovePossible = true
        -> exists blocksList, checkRemoveOkRec firstBlockToRemove removePart blocksList s
            /\ nullAddr = last blocksList firstBlockToRemove)
}}.
Proof.
unfold checkRemoveSubblocksRec. apply checkRemoveSubblocksRecAux.
Qed.

Fixpoint removedBlockRec s s0 removePart block statesList blocksList := match statesList with
  | [] => blocksList = [] /\ s = s0
  | s1::statesListRec => exists blockChild blocksListRec,
      blocksList = blockChild::blocksListRec
      /\ block <> nullAddr
      /\ scentryNext (CPaddr (block+scoffset)) blockChild s0
      /\ (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
            /\ lookup removePart (memory s1) beqAddr = Some(PDT pdentry1)
            /\ pdentry1 = {|
                            structure := structure pdentry0;
                            firstfreeslot := block;
                            nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                            nbprepare := nbprepare pdentry0;
                            parent := parent pdentry0;
                            MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                            vidtAddr := vidtAddr pdentry0
                          |})
      /\ In block (getMappedBlocks removePart s0)
      /\ bentryAFlag block true s0
      /\ (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
            /\ pdentryFirstFreeSlot removePart newEnd s0
            /\ lookup block (memory s1) beqAddr = Some(BE
                {|
                  read := false;
                  write := false;
                  exec := false;
                  present := false;
                  accessible := false;
                  blockindex := blockindex bentry0;
                  blockrange := CBlock nullAddr newEnd;
                  Hidx := l
                |}))
      /\ sh1entryPDflag (CPaddr (block + sh1offset)) false s0
      /\ sh1entryPDchild (CPaddr (block+sh1offset)) nullAddr s0
      /\ lookup (CPaddr (block+sh1offset)) (memory s1) beqAddr
          = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
      /\ lookup (CPaddr (block+scoffset)) (memory s1) beqAddr
          = Some(SCE {| origin := nullAddr; next := nullAddr |})
      /\ (forall addr, removePart <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
          -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s1) beqAddr = lookup addr (memory s0) beqAddr)
      /\ removedBlockRec s s1 removePart blockChild statesListRec blocksListRec
  end.

Fixpoint isNextList block blocksList s := match blocksList with
| [] => True
| blockChild::blocksListRec => block <> nullAddr /\ scentryNext (CPaddr (block+scoffset)) blockChild s
    /\ isNextList blockChild blocksListRec s
end.

Lemma wellFormedFstShadowIfBlockEntryPreservedRemove s s0 partition block :
wellFormedFstShadowIfBlockEntry s0
-> (exists pdentry0 pdentry1, lookup partition (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup partition (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot partition newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, partition <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> wellFormedFstShadowIfBlockEntry s.
Proof.
intros HwellSh1 HPDT HBE HSHE HsceIsSCE HSCE HlookupsEq blockBis HblockBisIsBE.
destruct (beqAddr (CPaddr (block + sh1offset)) (CPaddr (blockBis + sh1offset))) eqn:HbeqSh1s.
- rewrite <-beqAddrTrue in HbeqSh1s. rewrite <-HbeqSh1s in *. unfold isSHE. rewrite HSHE. trivial.
- rewrite <-beqAddrFalse in *. unfold isBE in *. assert(HneqBlocks: block <> blockBis).
  { contradict HbeqSh1s. apply CPaddrInjectionNat. f_equal. apply paddrEqNatEqEquiv. assumption. }
  assert(HbeqSh1BlockBis: CPaddr (block + sh1offset) <> blockBis).
  { intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. congruence. }
  assert(HbeqSceBlockBis: CPaddr (block + scoffset) <> blockBis).
  { intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence. }
  assert(HbeqPartBlockBis: partition <> blockBis).
  {
    intro Hcontra. rewrite Hcontra in *. destruct HPDT as [pdentry0 [pdentry1 (_ & Hlookup & _)]].
    rewrite Hlookup in *. congruence.
  }
  assert(HlookupBlockBisEq: lookup blockBis (memory s) beqAddr = lookup blockBis (memory s0) beqAddr).
  { apply HlookupsEq; assumption. }
  rewrite HlookupBlockBisEq in *. specialize(HwellSh1 blockBis HblockBisIsBE). unfold isSHE in *.
  assert(HbeqBlockSh1Bis: block <> CPaddr (blockBis + sh1offset)).
  {
    intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [l [_ (Hlookup & _)]]]. rewrite Hlookup in *.
    congruence.
  }
  assert(HbeqSceSh1Bis: CPaddr (block+scoffset) <> CPaddr (blockBis + sh1offset)).
  {
    intro Hcontra. rewrite Hcontra in *. unfold isSCE in *.
    destruct (lookup (CPaddr (blockBis + sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  assert(HbeqPartSh1Bis: partition <> CPaddr (blockBis + sh1offset)).
  {
    intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [pdentry0 [_ (Hlookup & _)]]. rewrite Hlookup in *.
    congruence.
  }
  rewrite HlookupsEq; trivial.
Qed.

Lemma wellFormedBlockPreservedRemove s s0 partition blockToRemove :
wellFormedBlock s0
-> (exists pdentry0 pdentry1, lookup partition (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup partition (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot partition newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, partition <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> wellFormedBlock s.
Proof.
intros Hwell HPDT HBE HSHE HsceIsSCE HSCE HlookupsEq block startaddr endaddr HPflag Hstart Hend.
unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
assert(HlookupEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{
  apply HlookupsEq; intro Hcontra; subst block.
  - destruct HPDT as [pdentry0 [pdentry1 (_ & Hlookup & _)]]. rewrite Hlookup in *. congruence.
  - destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. rewrite Hlookups in *. simpl in *. congruence.
  - rewrite HSHE in *. congruence.
  - rewrite HSCE in *. congruence.
}
rewrite HlookupEq in *. specialize(Hwell block startaddr endaddr HPflag Hstart Hend). assumption.
Qed.

Lemma AccessibleNoPDFlagPreservedRemove s s0 removePart blockToRemove:
AccessibleNoPDFlag s0
-> nullAddrExists s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove + sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> AccessibleNoPDFlag s.
Proof.
intros HaccNoPD Hnull HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq block sh1entryaddr HblockIsBE Hsh1 HAflag.
unfold bentryAFlag in *. unfold isBE in *. unfold sh1entryAddr in *.
assert(HbeqBlocks: blockToRemove <> block).
{
  intro Hcontra. subst block. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. rewrite Hlookups in *.
  simpl in *. congruence.
}
assert(HlookupBlockTREq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{
  apply HlookupsEq; trivial.
  - intro Hcontra. subst block. destruct HPDT as [pdentry0 [pdentry1 (_ & Hlookups & _)]]. rewrite Hlookups in *.
    congruence.
  - intro Hcontra. subst block. rewrite HSHE in *. congruence.
  - intro Hcontra. subst block. rewrite HSCE in *. congruence.
}
rewrite HlookupBlockTREq in *. specialize(HaccNoPD block sh1entryaddr HblockIsBE Hsh1 HAflag).
unfold sh1entryPDflag in *. rewrite HlookupsEq; trivial.
- intro Hcontra. subst sh1entryaddr. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
  congruence.
- intro Hcontra. subst sh1entryaddr. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. rewrite Hlookups0 in *.
  congruence.
- destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  subst sh1entryaddr. intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
  rewrite HcontraBis in *. unfold isSHE in *. unfold nullAddrExists in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
- intro Hcontra. subst sh1entryaddr. unfold isSCE in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
Qed.

Lemma isBEEqRemoveRec block s s0 partition blockToRemove statesList blocksList:
wellFormedFstShadowIfBlockEntry s0
-> isBE block s0
-> removedBlockRec s s0 partition blockToRemove statesList blocksList
-> isBE block s.
Proof.
revert blocksList blockToRemove s0.
induction statesList; simpl; intros blocksList blockToRemove s0 HwellSh1 HblockIsBE HblocksList.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [blockChild [blocksListRec (HlistsEq & HbeqBlockNull & Hnext & HPDT & HBTRMapped & HAflagBTR
    & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]]. assert(HblockIsBEA: isBE block a).
  {
    destruct (beqAddr blockToRemove block) eqn:HbeqBlocks.
    - rewrite <-beqAddrTrue in HbeqBlocks. subst block. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookup)]]].
      unfold isBE. rewrite Hlookup. trivial.
    - rewrite <-beqAddrFalse in *. unfold isBE in *. rewrite HlookupsEq; trivial.
      + intro Hcontra. subst block. destruct HPDT as [pdentry0 [_ (Hlookup & _)]]. rewrite Hlookup in *. congruence.
      + assert(HblockTRIsBE: isBE blockToRemove s0).
        { destruct HBE as [bentry0 [_ [newEnd (Hlookup & _)]]]. unfold isBE. rewrite Hlookup. trivial. }
        specialize(HwellSh1 blockToRemove HblockTRIsBE). intro Hcontra. subst block. unfold isSHE in *.
        destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      + intro Hcontra. subst block. unfold scentryNext in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 partition blockToRemove; trivial. unfold isSCE.
    unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  specialize(IHstatesList blocksListRec blockChild a HwellSh1A HblockIsBEA HblocksListRec). assumption.
Qed.

Lemma isBEEqRemoveRecRev block s s0 partition blockToRemove statesList blocksList:
isBE block s
-> removedBlockRec s s0 partition blockToRemove statesList blocksList
-> isBE block s0.
Proof.
intro HblockIsBE. revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList
  HblocksList; try(destruct HblocksList; subst s; assumption).
destruct HblocksList as [blockChild [blocksListRec (HlistsEq & HbeqBlockNull & Hnext & HPDT & HBTRMapped & HAflagBTR
  & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
apply IHstatesList in HblocksListRec. unfold isBE in *. destruct (beqAddr blockToRemove block) eqn:HbeqBlocks.
- rewrite <-beqAddrTrue in HbeqBlocks. subst block. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]].
  rewrite Hlookups0. trivial.
- rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
  + intro Hcontra. subst block. destruct HPDT as [_ [pdentry1 (_ & Hlookups1 & _)]]. rewrite Hlookups1 in *.
    congruence.
  + intro Hcontra. subst block. rewrite HSHE in *. congruence.
  + intro Hcontra. subst block. rewrite HSCE in *. congruence.
Qed.

Lemma nullAddrExistsPreservedRemove s s0 removePart blockToRemove :
nullAddrExists s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> nullAddrExists s.
Proof.
intros Hnull HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. unfold nullAddrExists in *. unfold isPADDR in *.
rewrite HlookupsEq; trivial.
- intro Hcontra. rewrite Hcontra in *. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
  congruence.
- intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. rewrite Hlookups0 in *.
  congruence.
- intro Hcontra. rewrite Hcontra in *. unfold isSHE in *.
  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
- intro Hcontra. rewrite Hcontra in *. unfold isSCE in *.
  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
Qed.

Lemma getKSEntriesInStructAuxEqRemove block s s0 removePart kernel n idx:
(exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (block+sh1offset)) s0
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getKSEntriesInStructAux n kernel s idx = getKSEntriesInStructAux n kernel s0 idx.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. revert idx. induction n; intro idx; simpl; trivial.
destruct (Paddr.addPaddrIdx kernel idx) eqn:Hadd; trivial.
destruct (beqAddr removePart p) eqn:HbeqPartNextAddr.
{
  rewrite <-beqAddrTrue in HbeqPartNextAddr. subst p.
  destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]]. rewrite Hlookups0. rewrite Hlookups. reflexivity.
}
destruct (beqAddr (CPaddr (block + sh1offset)) p) eqn:HbeqSh1NextAddr.
{
  rewrite <-beqAddrTrue in HbeqSh1NextAddr. subst p. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (block + scoffset)) p) eqn:HbeqSceNextAddr.
{
  rewrite <-beqAddrTrue in HbeqSceNextAddr. subst p. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr block p) eqn:HbeqBlockNextAddr.
- rewrite <-beqAddrTrue in HbeqBlockNextAddr. subst p.
  destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups0. rewrite Hlookups. destruct (indexEq idx zero) eqn:HbeqIdxZero; trivial.
  destruct (StateLib.Index.pred idx) eqn:Hpred; trivial. rewrite IHn. reflexivity.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
  destruct (lookup p (memory s0) beqAddr) eqn:HlookupP; trivial. destruct v; trivial.
  destruct (indexEq idx zero) eqn:HbeqIdxZero; trivial. destruct (StateLib.Index.pred idx) eqn:Hpred; trivial.
  rewrite IHn. reflexivity.
Qed.

Lemma getKSEntriesAuxEqRemove block s s0 removePart kernel n:
(exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (block+sh1offset)) s0
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getKSEntriesAux n kernel s = getKSEntriesAux n kernel s0.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. revert kernel. induction n; intro kernel; simpl; trivial.
destruct (Paddr.addPaddrIdx kernel nextoffset) eqn:Hadd; trivial.
destruct (beqAddr removePart p) eqn:HbeqPartNextAddr.
{
  rewrite <-beqAddrTrue in HbeqPartNextAddr. subst p.
  destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]]. rewrite Hlookups0. rewrite Hlookups. reflexivity.
}
destruct (beqAddr block p) eqn:HbeqBlockNextAddr.
{
  rewrite <-beqAddrTrue in HbeqBlockNextAddr. subst p.
  destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups0. rewrite Hlookups. reflexivity.
}
destruct (beqAddr (CPaddr (block + sh1offset)) p) eqn:HbeqSh1NextAddr.
{
  rewrite <-beqAddrTrue in HbeqSh1NextAddr. subst p. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (block + scoffset)) p) eqn:HbeqSceNextAddr.
{
  rewrite <-beqAddrTrue in HbeqSceNextAddr. subst p. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
destruct (lookup p (memory s0) beqAddr) eqn:HlookupP; trivial. destruct v; trivial.
destruct (beqAddr removePart p0) eqn:HbeqPartNextK.
{
  rewrite <-beqAddrTrue in HbeqPartNextK. subst p0.
  destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]]. rewrite Hlookups0. rewrite Hlookups. reflexivity.
}
destruct (beqAddr (CPaddr (block + sh1offset)) p0) eqn:HbeqSh1NextK.
{
  rewrite <-beqAddrTrue in HbeqSh1NextK. subst p0. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (block + scoffset)) p0) eqn:HbeqSceNextK.
{
  rewrite <-beqAddrTrue in HbeqSceNextK. subst p0. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
rewrite IHn.
assert(HgetStructEq: getKSEntriesInStructAux (maxIdx + 1) kernel s (CIndex 7)
  = getKSEntriesInStructAux (maxIdx + 1) kernel s0 (CIndex 7)).
{ apply getKSEntriesInStructAuxEqRemove with block removePart; trivial. }
rewrite HgetStructEq. destruct (beqAddr block p0) eqn:HbeqBlockNextK.
- rewrite <-beqAddrTrue in HbeqBlockNextK. subst p0.
  destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups0. rewrite Hlookups. reflexivity.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
Qed.

Lemma getKSEntriesEqRemove block s s0 removePart partition:
(exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (block+sh1offset)) s0
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getKSEntries partition s = getKSEntries partition s0.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. unfold getKSEntries.
destruct (beqAddr block partition) eqn:HbeqBlockPart.
{
  rewrite <-beqAddrTrue in HbeqBlockPart. subst partition.
  destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups0. rewrite Hlookups. reflexivity.
}
destruct (beqAddr (CPaddr (block + sh1offset)) partition) eqn:HbeqSh1Part.
{
  rewrite <-beqAddrTrue in HbeqSh1Part. subst partition. unfold isSHE in *. rewrite HSHE.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (block + scoffset)) partition) eqn:HbeqScePart.
{
  rewrite <-beqAddrTrue in HbeqScePart. subst partition. unfold isSCE in *. rewrite HSCE.
  destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr removePart partition) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. subst partition.
  destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & Hpdentry1)]]. rewrite Hlookups0. rewrite Hlookups.
  rewrite Hpdentry1. simpl structure. destruct (beqAddr (structure pdentry0) nullAddr) eqn:HbeqStructNull; trivial.
  apply getKSEntriesAuxEqRemove with block removePart; trivial. exists pdentry0. exists pdentry1. auto.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  destruct (lookup partition (memory s0) beqAddr) eqn:HlookupParts0; trivial. destruct v; trivial.
  destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull; trivial.
  apply getKSEntriesAuxEqRemove with block removePart; trivial.
Qed.

Lemma DisjointKSEntriesPreservedRemove s s0 partition block :
DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> (exists pdentry0 pdentry1, lookup partition (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup partition (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot partition newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, partition <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> DisjointKSEntries s.
Proof.
intros Hdisjoint Hsh1IsSHE HPDT HBE HSHE HsceIsSCE HSCE HlookupsEq part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
assert(Hpart1IsPDTs0: isPDT part1 s0).
{
  unfold isPDT in *. destruct (beqAddr block part1) eqn:HbeqBlockPart.
  {
    rewrite <-beqAddrTrue in HbeqBlockPart. subst part1. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
    rewrite Hlookups in *. exfalso; congruence.
  }
  destruct (beqAddr (CPaddr (block + sh1offset)) part1) eqn:HbeqSh1Part.
  {
    rewrite <-beqAddrTrue in HbeqSh1Part. subst part1. unfold isSHE in *. rewrite HSHE in *. exfalso; congruence.
  }
  destruct (beqAddr (CPaddr (block + scoffset)) part1) eqn:HbeqScePart.
  {
    rewrite <-beqAddrTrue in HbeqScePart. subst part1. unfold isSCE in *. rewrite HSCE in *. exfalso; congruence.
  }
  destruct (beqAddr partition part1) eqn:HbeqParts1.
  - rewrite <-beqAddrTrue in HbeqParts1. subst part1. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
    rewrite Hlookups0. trivial.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
}
assert(Hpart2IsPDTs0: isPDT part2 s0).
{
  unfold isPDT in *. destruct (beqAddr block part2) eqn:HbeqBlockPart.
  {
    rewrite <-beqAddrTrue in HbeqBlockPart. subst part2. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
    rewrite Hlookups in *. exfalso; congruence.
  }
  destruct (beqAddr (CPaddr (block + sh1offset)) part2) eqn:HbeqSh1Part.
  {
    rewrite <-beqAddrTrue in HbeqSh1Part. subst part2. unfold isSHE in *. rewrite HSHE in *. exfalso; congruence.
  }
  destruct (beqAddr (CPaddr (block + scoffset)) part2) eqn:HbeqScePart.
  {
    rewrite <-beqAddrTrue in HbeqScePart. subst part2. unfold isSCE in *. rewrite HSCE in *. exfalso; congruence.
  }
  destruct (beqAddr partition part2) eqn:HbeqParts2.
  - rewrite <-beqAddrTrue in HbeqParts2. subst part2. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
    rewrite Hlookups0. trivial.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
}
specialize(Hdisjoint part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts). assert(HblockIsBE: isBE block s0).
{
  unfold isBE. destruct HBE as [bentry [_ [_ (Hlookups0 & _)]]]. rewrite Hlookups0. trivial.
}
specialize(Hsh1IsSHE block HblockIsBE).
assert(HgetKSEq1: getKSEntries part1 s = getKSEntries part1 s0).
{ apply getKSEntriesEqRemove with block partition; trivial. }
assert(HgetKSEq2: getKSEntries part2 s = getKSEntries part2 s0).
{ apply getKSEntriesEqRemove with block partition; trivial. }
rewrite HgetKSEq1. rewrite HgetKSEq2. assumption.
Qed.

Lemma noDupKSEntriesListPreservedRemove s s0 partition block :
noDupKSEntriesList s0
-> (exists pdentry0 pdentry1, lookup partition (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup partition (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot partition newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (block + sh1offset)) s0
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, partition <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> noDupKSEntriesList s.
Proof.
intros Hdisjoint HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq part HpartIsPDT.
assert(HpartIsPDTs0: isPDT part s0).
{
  unfold isPDT in *. destruct (beqAddr block part) eqn:HbeqBlockPart.
  {
    rewrite <-beqAddrTrue in HbeqBlockPart. subst part. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
    rewrite Hlookups in *. exfalso; congruence.
  }
  destruct (beqAddr (CPaddr (block + sh1offset)) part) eqn:HbeqSh1Part.
  {
    rewrite <-beqAddrTrue in HbeqSh1Part. subst part. unfold isSHE in *. rewrite HSHE in *. exfalso; congruence.
  }
  destruct (beqAddr (CPaddr (block + scoffset)) part) eqn:HbeqScePart.
  {
    rewrite <-beqAddrTrue in HbeqScePart. subst part. unfold isSCE in *. rewrite HSCE in *. exfalso; congruence.
  }
  destruct (beqAddr partition part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
    rewrite Hlookups0. trivial.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
}
specialize(Hdisjoint part HpartIsPDTs0).
assert(HgetKSEq: getKSEntries part s = getKSEntries part s0).
{ apply getKSEntriesEqRemove with block partition; trivial. }
rewrite HgetKSEq. assumption.
Qed.

Lemma getMappedBlocksEqRemove block s s0 removePart partition:
DisjointKSEntries s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In block (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (block+sh1offset)) s0
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> removePart <> partition -> getMappedBlocks partition s = getMappedBlocks partition s0.
Proof.
intros Hdisjoint HPDT HblockMappeds0 HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq HbeqParts. unfold getMappedBlocks.
assert(HgetKSEq: getKSEntries partition s = getKSEntries partition s0).
{ apply getKSEntriesEqRemove with block removePart; trivial. }
rewrite HgetKSEq. assert(HpropsOr: isPDT partition s0 \/ ~isPDT partition s0) by (apply Classical_Prop.classic).
unfold isPDT in *. destruct HpropsOr as [HpartIsPDT | HpartIsNotPDT].
- assert(HblockNotInPart: ~In block (filterOptionPaddr (getKSEntries partition s0))).
  {
    unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMappeds0.
    assert(HremoveIsPDT: isPDT removePart s0).
    { unfold isPDT. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0. trivial. }
    specialize(Hdisjoint removePart partition HremoveIsPDT HpartIsPDT HbeqParts).
    destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
    specialize(Hdisjoint block HblockMappeds0). assumption.
  }
  revert HblockNotInPart. induction (filterOptionPaddr (getKSEntries partition s0)); simpl; intro; trivial.
  apply Decidable.not_or in HblockNotInPart. destruct HblockNotInPart as (HbeqABlock & HblockNotInPartRec).
  rewrite IHl; trivial.
  destruct (beqAddr removePart a) eqn:HbeqPartA.
  {
    rewrite <-beqAddrTrue in HbeqPartA. subst a. destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]].
    rewrite Hlookups0. rewrite Hlookups. reflexivity.
  }
  destruct (beqAddr (CPaddr (block + sh1offset)) a) eqn:HbeqSh1A.
  {
    rewrite <-beqAddrTrue in HbeqSh1A. subst a. rewrite HSHE. unfold isSHE in *.
    destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
  }
  destruct (beqAddr (CPaddr (block + scoffset)) a) eqn:HbeqSceA.
  {
    rewrite <-beqAddrTrue in HbeqSceA. subst a. rewrite HSCE. unfold isSCE in *.
    destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
  }
  apply not_eq_sym in HbeqABlock. rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
- unfold getKSEntries. destruct (lookup partition (memory s0) beqAddr); trivial. destruct v; trivial. exfalso.
  contradict HpartIsNotPDT. trivial.
Qed.

Lemma getMappedBlocksEquivRemove block s s0 removePart:
noDupKSEntriesList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In block (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (block+sh1offset)) s0
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> (forall blockBis, In blockBis (block::getMappedBlocks removePart s)
      <-> In blockBis (getMappedBlocks removePart s0)) /\ NoDup (getMappedBlocks removePart s).
Proof.
intros HnoDup HPDT HblockMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. unfold getMappedBlocks in *.
assert(HgetKSRemoveEq: getKSEntries removePart s = getKSEntries removePart s0).
{ apply getKSEntriesEqRemove with block removePart; trivial. }
rewrite HgetKSRemoveEq. assert(HremoveIsPDT: isPDT removePart s0).
{ unfold isPDT. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0. trivial. }
specialize(HnoDup removePart HremoveIsPDT). revert HblockMapped HnoDup.
induction (filterOptionPaddr (getKSEntries removePart s0)); simpl; intros; try(exfalso; congruence).
apply NoDup_cons_iff in HnoDup. destruct HnoDup as (HaNotInL & HnoDupRec).
destruct (beqAddr removePart a) eqn:HbeqPartA.
{
  rewrite <-beqAddrTrue in HbeqPartA. subst a. destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]].
  rewrite Hlookups0 in *. rewrite Hlookups. auto.
}
destruct (beqAddr (CPaddr (block + sh1offset)) a) eqn:HbeqSh1A.
{
  rewrite <-beqAddrTrue in HbeqSh1A. subst a. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). auto.
}
destruct (beqAddr (CPaddr (block + scoffset)) a) eqn:HbeqSceA.
{
  rewrite <-beqAddrTrue in HbeqSceA. subst a. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). auto.
}
destruct (beqAddr block a) eqn:HbeqBlockA.
- rewrite <-beqAddrTrue in HbeqBlockA. subst a. destruct HBE as [bentry0 [l0 [newEnd (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups0 in *. rewrite Hlookups. simpl. destruct (present bentry0); simpl in *.
  + apply NotInListNotInFilterPresent with (s:=s0) in HaNotInL. clear IHl. clear HblockMapped.
    assert(HfiltEq: filterPresent l s = filterPresent l s0).
    {
      revert HaNotInL. clear HnoDupRec. induction l; simpl; intro; trivial.
      destruct (beqAddr removePart a) eqn:HbeqPartABis.
      {
        rewrite <-beqAddrTrue in HbeqPartABis. subst a.
        destruct HPDT as [pdentry0 [pdentry1 (HlookupPs0 & HlookupPs & _)]].
        rewrite HlookupPs0 in *. rewrite HlookupPs. auto.
      }
      destruct (beqAddr (CPaddr (block + sh1offset)) a) eqn:HbeqSh1ABis.
      {
        rewrite <-beqAddrTrue in HbeqSh1ABis. subst a. rewrite HSHE. unfold isSHE in *.
        destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). auto.
      }
      destruct (beqAddr (CPaddr (block + scoffset)) a) eqn:HbeqSceABis.
      {
        rewrite <-beqAddrTrue in HbeqSceABis. subst a. rewrite HSCE. unfold isSCE in *.
        destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). auto.
      }
      destruct (beqAddr block a) eqn:HbeqBlockA.
      {
        rewrite <-beqAddrTrue in HbeqBlockA. subst a. rewrite Hlookups0 in *. rewrite Hlookups. simpl.
        destruct (present bentry0); auto. simpl in *. apply Decidable.not_or in HaNotInL. destruct HaNotInL.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
      destruct (lookup a (memory s0) beqAddr); auto. destruct v; auto. destruct (present b); auto. f_equal.
      apply IHl. simpl in *. apply Decidable.not_or in HaNotInL. destruct HaNotInL. assumption.
    }
    rewrite HfiltEq. split. intuition. apply NoDupListNoDupFilterPresent; assumption.
  + apply IHl; trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  destruct (lookup a (memory s0) beqAddr); try(simpl in *; apply IHl; assumption).
  destruct v; try(simpl in *; apply IHl; assumption). destruct (present b); try(simpl in *; apply IHl; assumption).
  simpl in *. destruct HblockMapped as [Hcontra | HblockMappedRec]; try(exfalso; congruence).
  specialize(IHl HblockMappedRec HnoDupRec). destruct IHl as (IHl & HnoDups). split.
  + intro blockBis. specialize(IHl blockBis). destruct IHl as (Hleft & Hright). split; intro HblockBIn.
    * destruct HblockBIn as [HblocksEq | [HbeqABlockB | HblockBInRec]]; try(right; apply Hleft; auto; congruence).
      left. assumption.
    * destruct HblockBIn as [HbeqABlockB | HblockBInRec]; try(right; left; assumption).
      specialize(Hright HblockBInRec). destruct Hright as [HblocksEq | HblockBInRecs]; auto.
  + apply NoDup_cons; trivial. apply NotInListNotInFilterPresent; assumption.
Qed.

Lemma getMappedBlocksEqRemPartRemove block s s0 removePart:
noDupKSEntriesList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In block (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (block+sh1offset)) s0
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> exists leftList rightList, getMappedBlocks removePart s = leftList ++ rightList
    /\ getMappedBlocks removePart s0 = leftList ++ [block] ++ rightList.
Proof.
intros HnoDup HPDT HblockMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. unfold getMappedBlocks in *.
assert(HgetKSRemoveEq: getKSEntries removePart s = getKSEntries removePart s0).
{ apply getKSEntriesEqRemove with block removePart; trivial. }
rewrite HgetKSRemoveEq. assert(HremoveIsPDT: isPDT removePart s0).
{ unfold isPDT. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0. trivial. }
specialize(HnoDup removePart HremoveIsPDT). revert HblockMapped HnoDup.
induction (filterOptionPaddr (getKSEntries removePart s0)); simpl; intros; try(exfalso; congruence).
apply NoDup_cons_iff in HnoDup. destruct HnoDup as (HaNotInL & HnoDupRec).
destruct (beqAddr removePart a) eqn:HbeqPartA.
{
  rewrite <-beqAddrTrue in HbeqPartA. subst a. destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]].
  rewrite Hlookups0 in *. rewrite Hlookups. auto.
}
destruct (beqAddr (CPaddr (block + sh1offset)) a) eqn:HbeqSh1A.
{
  rewrite <-beqAddrTrue in HbeqSh1A. subst a. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). auto.
}
destruct (beqAddr (CPaddr (block + scoffset)) a) eqn:HbeqSceA.
{
  rewrite <-beqAddrTrue in HbeqSceA. subst a. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). auto.
}
destruct (beqAddr block a) eqn:HbeqBlockA.
- rewrite <-beqAddrTrue in HbeqBlockA. subst a. destruct HBE as [bentry0 [l0 [newEnd (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups0 in *. rewrite Hlookups. simpl. destruct (present bentry0); simpl in *; try(apply IHl; trivial).
  apply NotInListNotInFilterPresent with (s:=s0) in HaNotInL. clear IHl. clear HblockMapped.
  assert(HfiltEq: filterPresent l s = filterPresent l s0).
  {
    revert HaNotInL. clear HnoDupRec. induction l; simpl; intro; trivial.
    destruct (beqAddr removePart a) eqn:HbeqPartABis.
    {
      rewrite <-beqAddrTrue in HbeqPartABis. subst a.
      destruct HPDT as [pdentry0 [pdentry1 (HlookupPs0 & HlookupPs & _)]].
      rewrite HlookupPs0 in *. rewrite HlookupPs. auto.
    }
    destruct (beqAddr (CPaddr (block + sh1offset)) a) eqn:HbeqSh1ABis.
    {
      rewrite <-beqAddrTrue in HbeqSh1ABis. subst a. rewrite HSHE. unfold isSHE in *.
      destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). auto.
    }
    destruct (beqAddr (CPaddr (block + scoffset)) a) eqn:HbeqSceABis.
    {
      rewrite <-beqAddrTrue in HbeqSceABis. subst a. rewrite HSCE. unfold isSCE in *.
      destruct (lookup (CPaddr (block + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). auto.
    }
    destruct (beqAddr block a) eqn:HbeqBlockA.
    {
      rewrite <-beqAddrTrue in HbeqBlockA. subst a. rewrite Hlookups0 in *. rewrite Hlookups. simpl.
      destruct (present bentry0); auto. simpl in *. apply Decidable.not_or in HaNotInL. destruct HaNotInL.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
    destruct (lookup a (memory s0) beqAddr); auto. destruct v; auto. destruct (present b); auto. f_equal.
    apply IHl. simpl in *. apply Decidable.not_or in HaNotInL. destruct HaNotInL. assumption.
  }
  rewrite HfiltEq. exists []. exists (filterPresent l s0). intuition.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  destruct (lookup a (memory s0) beqAddr); try(simpl in *; apply IHl; assumption).
  destruct v; try(simpl in *; apply IHl; assumption). destruct (present b); try(simpl in *; apply IHl; assumption).
  simpl in *. destruct HblockMapped as [Hcontra | HblockMappedRec]; try(exfalso; congruence).
  specialize(IHl HblockMappedRec HnoDupRec). destruct IHl as [leftList [rightList (Heqs & Heqs0)]].
  exists (a::leftList). exists rightList. rewrite <-app_comm_cons. rewrite <-app_comm_cons. split; f_equal; trivial.
Qed.

Lemma getChildrenEqRemove s s0 removePart blockToRemove partition:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> In blockToRemove (getMappedBlocks removePart s0)
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getChildren partition s = getChildren partition s0.
Proof.
intros HnoDup Hnull HnoDupMapped Hdisjoint HPDT HBE HblockTRMapped HPDflag HSHE HsceIsSCE HSCE HlookupsEq.
unfold getChildren. unfold nullAddrExists in *.
destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) partition) eqn:HbeqSh1Part.
{
  rewrite <-beqAddrTrue in HbeqSh1Part. subst partition. rewrite HSHE. unfold sh1entryPDflag in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove + scoffset)) partition) eqn:HbeqScePart.
{
  rewrite <-beqAddrTrue in HbeqScePart. subst partition. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr blockToRemove partition) eqn:HbeqBlockPart.
{
  rewrite <-beqAddrTrue in HbeqBlockPart. subst partition.
  destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups0 in *. rewrite Hlookups. reflexivity.
}
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDflag in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
destruct (beqAddr removePart partition) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. subst partition.
  assert(HPDTBis: exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some (PDT pdentry0)
   /\ lookup removePart (memory s) beqAddr = Some (PDT pdentry1)
   /\ pdentry1 =
       {|
         structure := structure pdentry0;
         firstfreeslot := blockToRemove;
         nbfreeslots := CIndex (nbfreeslots pdentry0 + 1);
         nbprepare := nbprepare pdentry0;
         parent := parent pdentry0;
         MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
         vidtAddr := vidtAddr pdentry0
       |}) by assumption.
  destruct HPDTBis as [pdentry0 [pdentry1 (HlookupPs0 & HlookupPs & _)]]. rewrite HlookupPs0. rewrite HlookupPs.
  assert(HchildFiltRemove: childFilter s0 blockToRemove = false).
  {
    unfold childFilter in *. destruct HBE as [bentry0 [l0 [newEnd (Hlookups0 & _ & Hlookups)]]].
    rewrite Hlookups0 in *. unfold Paddr.addPaddrIdx in *. unfold CPaddr in HPDflag.
    destruct (le_dec (blockToRemove + sh1offset) maxAddr); try(lia).
    replace (StateLib.Paddr.addPaddrIdx_obligation_1 blockToRemove sh1offset l) with
      (ADT.CPaddr_obligation_1 (blockToRemove + sh1offset) l) in *; try(apply proof_irrelevance).
    unfold sh1entryPDflag in *.
    destruct (lookup
         {|
           p := blockToRemove + sh1offset;
           Hp := ADT.CPaddr_obligation_1 (blockToRemove + sh1offset) l
         |} (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  assert(HblockTRNotPD: ~In blockToRemove (filter (childFilter s0) (getMappedBlocks removePart s0))).
  {
    clear HblockTRMapped. induction (getMappedBlocks removePart s0); simpl; auto.
    destruct (childFilter s0 a) eqn:HchildFilt.
    - simpl. apply Classical_Prop.and_not_or. split; trivial. intro Hcontra. subst a. congruence.
    - assumption.
  }
  assert(HblockTRNotMappeds: ~In blockToRemove (getMappedBlocks removePart s)).
  {
    intro Hcontra. apply IL.mappedBlockIsBE in Hcontra. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
    destruct Hcontra as [bentryBis (HlookupsBis & Hpres)]. rewrite Hlookups in HlookupsBis.
    injection HlookupsBis as HbentriesEq. subst bentryBis. simpl in *. congruence.
  }
  pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0 removePart HnoDup HPDT HblockTRMapped HBE Hsh1IsSHE
    HSHE HsceIsSCE HSCE HlookupsEq) as Hequiv. unfold getPDs. clear HblockTRMapped.
  destruct Hequiv as [leftList [rightList (Heqs & Heqs0)]]. rewrite Heqs in *. clear Heqs. rewrite Heqs0 in *.
  clear Heqs0. induction leftList as [ | blocks0 lists0]; simpl in *.
  + rewrite HchildFiltRemove in *. induction rightList; simpl in *; trivial.
    apply Decidable.not_or in HblockTRNotMappeds. destruct HblockTRNotMappeds as (HbeqABlockTR & HblockTRNotMappeds).
    assert(HchildFiltEq: childFilter s a = childFilter s0 a).
    {
      unfold childFilter. apply not_eq_sym in HbeqABlockTR.
      destruct (beqAddr removePart a) eqn:HbeqPartABis.
      {
        rewrite <-beqAddrTrue in HbeqPartABis. subst a. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
      }
      destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) a) eqn:HbeqSh1ABis.
      {
        rewrite <-beqAddrTrue in HbeqSh1ABis. subst a. rewrite HSHE. unfold isSHE in *.
        destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). reflexivity.
      }
      destruct (beqAddr (CPaddr (blockToRemove + scoffset)) a) eqn:HbeqSceABis.
      {
        rewrite <-beqAddrTrue in HbeqSceABis. subst a. rewrite HSCE. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). reflexivity.
      }
      rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
      destruct (lookup a (memory s0) beqAddr); trivial. destruct v; trivial.
      destruct (Paddr.addPaddrIdx a sh1offset) eqn:Hadd; trivial.
      destruct (beqAddr removePart p) eqn:HbeqPartP.
      {
        rewrite <-beqAddrTrue in HbeqPartP. subst p. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
      }
      destruct (beqAddr (CPaddr (blockToRemove + scoffset)) p) eqn:HbeqSceP.
      {
        rewrite <-beqAddrTrue in HbeqSceP. subst p. rewrite HSCE. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). reflexivity.
      }
      destruct (beqAddr blockToRemove p) eqn:HbeqBlockP.
      {
        rewrite <-beqAddrTrue in HbeqBlockP. subst p.
        destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & Hlookups)]]].
        rewrite Hlookups0. rewrite Hlookups. reflexivity.
      }
      destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) p) eqn:HbeqSh1P.
      {
        exfalso. assert(Heq: p = CPaddr (a+sh1offset)).
        {
          unfold Paddr.addPaddrIdx in *. unfold CPaddr.
          destruct (le_dec (a + sh1offset) maxAddr); try(exfalso; congruence). injection Hadd as Hres. subst p.
          reflexivity.
        }
        rewrite Heq in *. rewrite <-beqAddrTrue in HbeqSh1P. apply CPaddrAddEq in HbeqSh1P; try(congruence).
        intro Hcontra. rewrite Hcontra in *. unfold isPADDR in *. unfold isSHE in *.
        destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
    }
    rewrite HchildFiltEq. destruct (childFilter s0 a) eqn:HchildFiltA; try(apply IHrightList; assumption).
    simpl in *. apply Decidable.not_or in HblockTRNotPD. destruct HblockTRNotPD as (_ & HblockTRNotPD).
    rewrite IHrightList; trivial. destruct (beqAddr removePart a) eqn:HbeqPartABis.
    {
      rewrite <-beqAddrTrue in HbeqPartABis. subst a. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) a) eqn:HbeqSh1ABis.
    {
      rewrite <-beqAddrTrue in HbeqSh1ABis. subst a. rewrite HSHE. unfold isSHE in *.
      destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove + scoffset)) a) eqn:HbeqSceABis.
    {
      rewrite <-beqAddrTrue in HbeqSceABis. subst a. rewrite HSCE. unfold isSCE in *.
      destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    apply not_eq_sym in HbeqABlockTR. rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
  + apply Decidable.not_or in HblockTRNotMappeds. destruct HblockTRNotMappeds as (HbeqBlocks & HblockTRNotMappeds).
    assert(HchildFiltEq: childFilter s blocks0 = childFilter s0 blocks0).
    {
      unfold childFilter. apply not_eq_sym in HbeqBlocks.
      destruct (beqAddr removePart blocks0) eqn:HbeqPartABis.
      {
        rewrite <-beqAddrTrue in HbeqPartABis. subst blocks0. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
      }
      destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) blocks0) eqn:HbeqSh1ABis.
      {
        rewrite <-beqAddrTrue in HbeqSh1ABis. subst blocks0. rewrite HSHE. unfold isSHE in *.
        destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). reflexivity.
      }
      destruct (beqAddr (CPaddr (blockToRemove + scoffset)) blocks0) eqn:HbeqSceABis.
      {
        rewrite <-beqAddrTrue in HbeqSceABis. subst blocks0. rewrite HSCE. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). reflexivity.
      }
      rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
      destruct (lookup blocks0 (memory s0) beqAddr); trivial. destruct v; trivial.
      destruct (Paddr.addPaddrIdx blocks0 sh1offset) eqn:Hadd; trivial.
      destruct (beqAddr removePart p) eqn:HbeqPartP.
      {
        rewrite <-beqAddrTrue in HbeqPartP. subst p. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
      }
      destruct (beqAddr (CPaddr (blockToRemove + scoffset)) p) eqn:HbeqSceP.
      {
        rewrite <-beqAddrTrue in HbeqSceP. subst p. rewrite HSCE. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). reflexivity.
      }
      destruct (beqAddr blockToRemove p) eqn:HbeqBlockP.
      {
        rewrite <-beqAddrTrue in HbeqBlockP. subst p.
        destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & Hlookups)]]].
        rewrite Hlookups0. rewrite Hlookups. reflexivity.
      }
      destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) p) eqn:HbeqSh1P.
      {
        exfalso. assert(Heq: p = CPaddr (blocks0+sh1offset)).
        {
          unfold Paddr.addPaddrIdx in *. unfold CPaddr.
          destruct (le_dec (blocks0 + sh1offset) maxAddr); try(exfalso; congruence). injection Hadd as Hres. subst p.
          reflexivity.
        }
        rewrite Heq in *. rewrite <-beqAddrTrue in HbeqSh1P. apply CPaddrAddEq in HbeqSh1P; try(congruence).
        intro Hcontra. rewrite Hcontra in *. unfold isPADDR in *. unfold isSHE in *.
        destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
    }
    rewrite HchildFiltEq. destruct (childFilter s0 blocks0) eqn:HchildFiltBlock; try(apply IHlists0; assumption).
    simpl in *. apply Decidable.not_or in HblockTRNotPD. destruct HblockTRNotPD as (_ & HblockTRNotPD).
    rewrite IHlists0; trivial. destruct (beqAddr removePart blocks0) eqn:HbeqPartABis.
    {
      rewrite <-beqAddrTrue in HbeqPartABis. subst blocks0. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) blocks0) eqn:HbeqSh1ABis.
    {
      rewrite <-beqAddrTrue in HbeqSh1ABis. subst blocks0. rewrite HSHE. unfold isSHE in *.
      destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove + scoffset)) blocks0) eqn:HbeqSceABis.
    {
      rewrite <-beqAddrTrue in HbeqSceABis. subst blocks0. rewrite HSCE. unfold isSCE in *.
      destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    apply not_eq_sym in HbeqBlocks. rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
  rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
  unfold getPDs. assert(HblockTRNotMapped: ~In blockToRemove (getMappedBlocks partition s0)).
  {
    assert(HremoveIsPDT: isPDT removePart s0).
    { unfold isPDT. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0. trivial. }
    assert(HpartIsPDT: isPDT partition s0).
    { unfold isPDT. rewrite HlookupPart. trivial. }
    specialize(Hdisjoint removePart partition HremoveIsPDT HpartIsPDT HbeqParts).
    destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
    unfold getMappedBlocks in *. apply InFilterPresentInList in HblockTRMapped. apply NotInListNotInFilterPresent.
    apply Hdisjoint; assumption.
  }
  induction (getMappedBlocks partition s0); simpl in *; trivial. apply Decidable.not_or in HblockTRNotMapped.
  destruct HblockTRNotMapped as (HbeqABlockTR & HblockTRNotMapped).
  destruct HPDT as [pdentry0 [pdentry1 (HlookupPs0 & HlookupPs & _)]].
  assert(HchildFiltEq: childFilter s a = childFilter s0 a).
  {
    unfold childFilter. apply not_eq_sym in HbeqABlockTR.
    destruct (beqAddr removePart a) eqn:HbeqPartABis.
    {
      rewrite <-beqAddrTrue in HbeqPartABis. subst a. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) a) eqn:HbeqSh1ABis.
    {
      rewrite <-beqAddrTrue in HbeqSh1ABis. subst a. rewrite HSHE. unfold isSHE in *.
      destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove + scoffset)) a) eqn:HbeqSceABis.
    {
      rewrite <-beqAddrTrue in HbeqSceABis. subst a. rewrite HSCE. unfold isSCE in *.
      destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
    destruct (lookup a (memory s0) beqAddr); trivial. destruct v; trivial.
    destruct (Paddr.addPaddrIdx a sh1offset) eqn:Hadd; trivial.
    destruct (beqAddr removePart p0) eqn:HbeqPartP.
    {
      rewrite <-beqAddrTrue in HbeqPartP. subst p0. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove + scoffset)) p0) eqn:HbeqSceP.
    {
      rewrite <-beqAddrTrue in HbeqSceP. subst p0. rewrite HSCE. unfold isSCE in *.
      destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    destruct (beqAddr blockToRemove p0) eqn:HbeqBlockP.
    {
      rewrite <-beqAddrTrue in HbeqBlockP. subst p0.
      destruct HBE as [bentry0 [l0 [newEnd (Hlookups0 & _ & Hlookups)]]].
      rewrite Hlookups0. rewrite Hlookups. reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) p0) eqn:HbeqSh1P.
    {
      exfalso. assert(Heq: p0 = CPaddr (a+sh1offset)).
      {
        unfold Paddr.addPaddrIdx in *. unfold CPaddr.
        destruct (le_dec (a + sh1offset) maxAddr); try(exfalso; congruence). injection Hadd as Hres. subst p0.
        reflexivity.
      }
      rewrite Heq in *. rewrite <-beqAddrTrue in HbeqSh1P. apply CPaddrAddEq in HbeqSh1P; try(congruence).
      intro Hcontra. rewrite Hcontra in *. unfold isPADDR in *. unfold isSHE in *.
      destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  }
  rewrite HchildFiltEq. destruct (childFilter s0 a) eqn:HchildFiltA; try(apply IHl; assumption). simpl.
  rewrite IHl; trivial. destruct (beqAddr removePart a) eqn:HbeqPartABis.
  {
    rewrite <-beqAddrTrue in HbeqPartABis. subst a. rewrite HlookupPs0. rewrite HlookupPs. reflexivity.
  }
  destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) a) eqn:HbeqSh1ABis.
  {
    rewrite <-beqAddrTrue in HbeqSh1ABis. subst a. rewrite HSHE. unfold isSHE in *.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
  }
  destruct (beqAddr (CPaddr (blockToRemove + scoffset)) a) eqn:HbeqSceABis.
  {
    rewrite <-beqAddrTrue in HbeqSceABis. subst a. rewrite HSCE. unfold isSCE in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
  }
  apply not_eq_sym in HbeqABlockTR. rewrite <-beqAddrFalse in *. rewrite HlookupsEq at 1; trivial.
Qed.

Lemma getPartitionsEqRemove s s0 removePart blockToRemove :
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getPartitions multiplexer s = getPartitions multiplexer s0.
Proof.
intros HnoDup Hnull HnoDupMapped Hdisjoint HPDT HblockTRMapped HBE HPDflag HSHE HsceIsSCE HSCE HlookupsEq.
unfold getPartitions. generalize multiplexer. induction (maxAddr + 2); simpl; intro part; f_equal.
rewrite getChildrenEqRemove with (s0:=s0) (removePart:=removePart) (blockToRemove:=blockToRemove); trivial.
f_equal. extensionality p. apply IHn.
Qed.

Lemma nextListPaddrAreBigger blockToRemove removePart blocksList s endaddr:
nullAddrExists s
-> wellFormedBlock s
(*-> blockAndNextAreSideBySide s*)
-> In removePart (getPartitions multiplexer s)
-> bentryEndAddr blockToRemove endaddr s
-> checkRemoveOkRec blockToRemove removePart blocksList s
-> forall addr, In addr (getAllPaddrAux blocksList s)
    -> addr >= endaddr.
Proof.
intros Hnull Hwell (*HnextBlockSide*) HpartIsPart. revert blockToRemove endaddr.
induction blocksList; cbn -[nullAddr last]; intros blockToRemove endaddr Hend HblocksList addr HaddrMapped;
  try(exfalso; congruence).
destruct HblocksList as (HAflag & HPflag & HblockMapped & HPDchild & Hnext & HnextBlockSidePartial & HblocksList).
assert(HaIsBE: isBE a s).
{
  unfold isBE. destruct blocksList; simpl in *.
  - destruct (lookup a (memory s) beqAddr); try(simpl in *; congruence). destruct v; simpl in *; congruence.
  - destruct HblocksList as (HAflagA & _). unfold bentryAFlag in *.
    destruct (lookup a (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
}
unfold isBE in *. destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(exfalso; congruence).
destruct v; try(exfalso; congruence). assert(HendNext: bentryEndAddr a (endAddr (blockrange b)) s).
{ unfold bentryEndAddr. rewrite HlookupA. reflexivity. }
assert(HeqTriv: CPaddr (blockToRemove + scoffset) = CPaddr (blockToRemove + scoffset)) by reflexivity.
assert(HbeqANull: a <> nullAddr).
{
  intro Hcontra. subst a. unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupA in *. congruence.
}
specialize(HnextBlockSidePartial HbeqANull). destruct HnextBlockSidePartial as (HnextMapped & HstartNext).
specialize(HstartNext endaddr Hend).
assert(HPflagNext: bentryPFlag a true s).
{
  apply IL.mappedBlockIsBE in HnextMapped. destruct HnextMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag.
  rewrite Hlookup. auto.
}
apply in_app_or in HaddrMapped.
specialize(Hwell a endaddr (endAddr (blockrange b)) HPflagNext HstartNext HendNext).
destruct Hwell as (Hwell & _). specialize(IHblocksList a (endAddr (blockrange b)) HendNext HblocksList addr).
unfold bentryStartAddr in *. rewrite HlookupA in *. rewrite <-HstartNext in *.
destruct HaddrMapped as [HaddrInNext | HaddrMappedRec].
- apply IL.getAllPaddrBlockInclRev in HaddrInNext. destruct HaddrInNext as (Hres & _). lia.
- specialize(IHblocksList HaddrMappedRec). lia.
Qed.

Lemma noDupNextBlocksList blockToRemove removePart blocksList s:
nullAddrExists s
-> wellFormedBlock s
(*-> blockAndNextAreSideBySide s*)
-> noDupMappedPaddrList s
-> In removePart (getPartitions multiplexer s)
-> checkRemoveOkRec blockToRemove removePart blocksList s
-> NoDup (blockToRemove::blocksList).
Proof.
intros Hnull Hwell (*HnextBlockSide*) HnoDupPaddr HpartIsPart. revert blockToRemove.
induction blocksList; intros blockToRemove HblocksList.
- pose proof NoDup_nil. apply NoDup_cons; auto.
- assert(Hend: exists endaddr, bentryEndAddr blockToRemove endaddr s).
  {
    simpl in HblocksList. destruct HblocksList as (HAflag & _). unfold bentryEndAddr. unfold bentryAFlag in *.
    destruct (lookup blockToRemove (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
  }
  destruct Hend as [endaddr Hend].
  pose proof (nextListPaddrAreBigger blockToRemove removePart (a::blocksList) s endaddr Hnull Hwell
    HpartIsPart Hend HblocksList) as HaddrsDisjoint.
  destruct HblocksList as (HAflag & HPflag & HblockMapped & HPDchild & Hnext & HnextBlockSidePartial & HblocksList).
  specialize(IHblocksList a HblocksList). apply NoDup_cons; trivial.
  intro Hcontra. assert(Hstart: exists startaddr, bentryStartAddr blockToRemove startaddr s).
  {
    unfold bentryStartAddr. unfold bentryAFlag in *.
    destruct (lookup blockToRemove (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
  }
  destruct Hstart as [startaddr Hstart]. specialize(Hwell blockToRemove startaddr endaddr HPflag Hstart Hend).
  destruct Hwell as (Hwell & _). assert(HstartInList: In startaddr (getAllPaddrAux (a::blocksList) s)).
  {
    apply blockIsMappedAddrInPaddrList with blockToRemove; trivial. simpl. unfold bentryStartAddr in *.
    unfold bentryEndAddr in *. destruct (lookup blockToRemove (memory s) beqAddr); try(simpl; congruence).
    destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r.
    apply IL.getAllPaddrBlockIncl; lia.
  }
  specialize(HaddrsDisjoint startaddr HstartInList). lia.
Qed.

Lemma checkRemoveOkPreservedRemove s s0 removePart blockToRemove block nextBlocksList:
nullAddrExists s0
-> wellFormedBlock s0
-> noDupKSEntriesList s0
(*-> blockAndNextAreSideBySide s0*)
-> noDupMappedPaddrList s0
-> In removePart (getPartitions multiplexer s0)
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove + sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> ~In blockToRemove (block::nextBlocksList)
-> checkRemoveOkRec block removePart nextBlocksList s0
-> checkRemoveOkRec block removePart nextBlocksList s.
Proof.
intros Hnull Hwell HnoDup (*HnextBlockSide*) HnoDupMapped HpartIsPart HPDT HblockTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE
  HSCE HlookupsEq. unfold nullAddrExists in *.
revert block. induction nextBlocksList; simpl; intros block HblockTRNotIn HnextBlocksList; trivial.
destruct HnextBlocksList as (HAflag & HPflag & HblockMapped & HPDchild & Hnext & HnextBlockSidePartial &
  HnextBlocksList).
apply Decidable.not_or in HblockTRNotIn. destruct HblockTRNotIn as (HbeqBlockBlockTR & HblockTRNotIn).
specialize(IHnextBlocksList a HblockTRNotIn HnextBlocksList).
pose proof (getMappedBlocksEquivRemove blockToRemove s s0 removePart HnoDup HPDT HblockTRMapped HBE Hsh1IsSHE HSHE
  HsceIsSCE HSCE HlookupsEq) as (HgetMappedEquiv & _). apply HgetMappedEquiv in HblockMapped. simpl in *.
destruct HblockMapped as [Hcontra | HblockMapped]; try(exfalso; congruence). apply not_eq_sym in HbeqBlockBlockTR.
assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{
  unfold bentryAFlag in *. apply HlookupsEq; trivial.
  - intro Hcontra. subst block. unfold getMappedBlocks in *. unfold getKSEntries in *.
    destruct (lookup removePart (memory s0) beqAddr); try(simpl in *; congruence).
    destruct v; simpl in *; congruence.
  - intro Hcontra. subst block. unfold isSHE in *.
    destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  - intro Hcontra. subst block. unfold isSCE in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
unfold bentryAFlag. unfold bentryPFlag. unfold bentryEndAddr. rewrite HlookupBlockEq. unfold sh1entryPDchild in *.
assert(HlookupSh1Eq: lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
  = lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr).
{
  apply HlookupsEq.
  - intro Hcontra. rewrite Hcontra in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
    destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(simpl in *; congruence).
    destruct v; simpl in *; congruence.
  - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. rewrite Hlookups0 in *.
    congruence.
  - intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
    unfold isSHE in *. unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
  - intro Hcontra. rewrite Hcontra in *. unfold isSCE in *.
    destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
unfold scentryNext in *.
assert(HlookupSceEq: lookup (CPaddr (block+scoffset)) (memory s) beqAddr
  = lookup (CPaddr (block+scoffset)) (memory s0) beqAddr).
{
  apply HlookupsEq.
  - intro Hcontra. rewrite Hcontra in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
    destruct (lookup (CPaddr (block+scoffset)) (memory s0) beqAddr); try(simpl in *; congruence).
    destruct v; simpl in *; congruence.
  - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. rewrite Hlookups0 in *.
    congruence.
  - intro Hcontra. rewrite Hcontra in *. unfold isSHE in *.
    destruct (lookup (CPaddr (block+scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
  - intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
    unfold isSCE in *. unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
}
rewrite HlookupSh1Eq. rewrite HlookupSceEq.
assert(a <> nullAddr -> In a (getMappedBlocks removePart s)
  /\ (forall endaddr, bentryEndAddr block endaddr s0 -> bentryStartAddr a endaddr s)).
{
  intros HbeqANull. specialize(HnextBlockSidePartial HbeqANull).
  destruct HnextBlockSidePartial as (HAMapped & HstartNext). apply HgetMappedEquiv in HAMapped.
  apply Decidable.not_or in HblockTRNotIn. destruct HblockTRNotIn as (HbeqABlockTR & HblockTRNotIn).
  destruct HAMapped as [Hcontra | HAMapped]; try(exfalso; congruence). split; trivial. intros endaddr Hend.
  specialize(HstartNext endaddr Hend). unfold bentryStartAddr in *. apply not_eq_sym in HbeqABlockTR.
  rewrite HlookupsEq; trivial.
  - intro Hcontra. subst a. unfold getMappedBlocks in *. unfold getKSEntries in *.
    destruct (lookup removePart (memory s0) beqAddr); try(simpl in *; congruence).
    destruct v; simpl in *; congruence.
  - intro Hcontra. subst a. unfold isSHE in *.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(simpl in *; congruence).
    destruct v; simpl in *; congruence.
  - intro Hcontra. subst a. unfold isSCE in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(simpl in *; congruence).
    destruct v; simpl in *; congruence.
}
intuition.
Qed.

Lemma noDupMappedBlocksListPreservedRemove s s0 removePart blockToRemove:
noDupMappedBlocksList s0
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove + sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> noDupMappedBlocksList s.
Proof.
intros HnoDupMapped HnoDup Hdisjoint HPDT HblockTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq part HpartIsPDT.
assert(HpartIsPDTs0: isPDT part s0).
{
  unfold isPDT in *. destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
    rewrite Hlookups0. trivial.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
    + intro Hcontra. subst part. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. rewrite Hlookups in *.
      congruence.
    + intro Hcontra. subst part. rewrite HSHE in *. congruence.
    + intro Hcontra. subst part. rewrite HSCE in *. congruence.
}
specialize(HnoDupMapped part HpartIsPDTs0). destruct (beqAddr removePart part) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getMappedBlocksEquivRemove blockToRemove s s0 removePart
    HnoDup HPDT HblockTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as (_ & Hres). assumption.
- rewrite <-beqAddrFalse in *.
  rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
Qed.

Lemma getAllPaddrAuxEqRemove blockToRemove s s0 removePart l:
(exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> ~In blockToRemove l
-> getAllPaddrAux l s = getAllPaddrAux l s0.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. induction l; simpl; intro HblockNotIn; trivial.
apply Decidable.not_or in HblockNotIn. destruct HblockNotIn as (HbeqABlock & HblockNotIn).
apply not_eq_sym in HbeqABlock. specialize(IHl HblockNotIn). rewrite IHl.
destruct (beqAddr removePart a) eqn:HbeqPartA.
{
  rewrite <-beqAddrTrue in HbeqPartA. subst a. destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]].
  rewrite Hlookups0. rewrite Hlookups. reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) a) eqn:HbeqSh1A.
{
  rewrite <-beqAddrTrue in HbeqSh1A. subst a. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove + scoffset)) a) eqn:HbeqSceA.
{
  rewrite <-beqAddrTrue in HbeqSceA. subst a. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getMappedPaddrEqRemove blockToRemove s s0 removePart partition:
DisjointKSEntries s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> removePart <> partition -> getMappedPaddr partition s = getMappedPaddr partition s0.
Proof.
intros Hdisjoint HPDT HblockMappeds0 HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq HbeqParts. unfold getMappedPaddr.
rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
apply getAllPaddrAuxEqRemove with blockToRemove removePart; trivial. unfold getMappedBlocks in *.
assert(HremoveIsPDT: isPDT removePart s0).
{ destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. unfold isPDT. rewrite Hlookups0. trivial. }
assert(HpropsOr: isPDT partition s0
  \/ ~ In blockToRemove (filterPresent (filterOptionPaddr (getKSEntries partition s0)) s0)).
{
  unfold isPDT. unfold getKSEntries. destruct (lookup partition (memory s0) beqAddr); cbn -[getKSEntriesAux]; auto.
  destruct v; cbn -[getKSEntriesAux]; auto.
}
destruct HpropsOr as [HpartIsPDT | Hres]; trivial. apply InFilterPresentInList in HblockMappeds0.
specialize(Hdisjoint removePart partition HremoveIsPDT HpartIsPDT HbeqParts).
destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
specialize(Hdisjoint blockToRemove HblockMappeds0). apply NotInListNotInFilterPresent; assumption.
Qed.

Lemma filterAccessibleEqRemove blockToRemove s s0 removePart l:
(exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> ~In blockToRemove l
-> filterAccessible l s = filterAccessible l s0.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq HblockNotIn. induction l; simpl in *; trivial.
apply Decidable.not_or in HblockNotIn. destruct HblockNotIn as (HbeqABTR & HblockNotIn). rewrite IHl; trivial.
apply not_eq_sym in HbeqABTR. destruct (beqAddr removePart a) eqn:HbeqRemA.
{
  rewrite <-beqAddrTrue in HbeqRemA. subst a.
  destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]]. rewrite Hlookups. rewrite Hlookups0. reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) a) eqn:HbeqSh1A.
{
  rewrite <-beqAddrTrue in HbeqSh1A. subst a. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) a) eqn:HbeqSceA.
{
  rewrite <-beqAddrTrue in HbeqSceA. subst a. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getAccessibleMappedBlocksEqRemove blockToRemove s s0 removePart partition:
DisjointKSEntries s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> removePart <> partition -> getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0.
Proof.
intros Hdisjoint HPDT HblockMappeds0 HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq HbeqParts.
unfold getAccessibleMappedBlocks.
destruct (beqAddr blockToRemove partition) eqn:HbeqBTRPart.
{
  rewrite <-beqAddrTrue in HbeqBTRPart. subst partition.
  destruct HBE as [bentry0 [newEnd [l (Hlookups0 & _ & Hlookups)]]]. rewrite Hlookups. rewrite Hlookups0. reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) partition) eqn:HbeqSh1Part.
{
  rewrite <-beqAddrTrue in HbeqSh1Part. subst partition. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) partition) eqn:HbeqScePart.
{
  rewrite <-beqAddrTrue in HbeqScePart. subst partition. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
assert(HBTRNotMapped: ~In blockToRemove (getMappedBlocks partition s0)).
{
  unfold getMappedBlocks in *.
  assert(HremoveIsPDT: isPDT removePart s0).
  { destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. unfold isPDT. rewrite Hlookups0. trivial. }
  assert(HpropsOr: isPDT partition s0
    \/ ~ In blockToRemove (filterPresent (filterOptionPaddr (getKSEntries partition s0)) s0)).
  {
    unfold isPDT. unfold getKSEntries. destruct (lookup partition (memory s0) beqAddr); cbn -[getKSEntriesAux]; auto.
    destruct v; cbn -[getKSEntriesAux]; auto.
  }
  destruct HpropsOr as [HpartIsPDT | Hres]; trivial. apply InFilterPresentInList in HblockMappeds0.
  specialize(Hdisjoint removePart partition HremoveIsPDT HpartIsPDT HbeqParts).
  destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
  specialize(Hdisjoint blockToRemove HblockMappeds0). apply NotInListNotInFilterPresent; assumption.
}
rewrite filterAccessibleEqRemove with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
Qed.

Lemma getAccessibleMappedPaddrEqRemove blockToRemove s s0 removePart partition:
DisjointKSEntries s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> removePart <> partition -> getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0.
Proof.
intros Hdisjoint HPDT HblockMappeds0 HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq HbeqParts.
unfold getAccessibleMappedPaddr. rewrite getAccessibleMappedBlocksEqRemove with (blockToRemove:=blockToRemove)
  (s0:=s0) (removePart:=removePart); trivial.
assert(HBTRNotMapped: ~In blockToRemove (getMappedBlocks partition s0)).
{
  unfold getMappedBlocks in *.
  assert(HremoveIsPDT: isPDT removePart s0).
  { destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. unfold isPDT. rewrite Hlookups0. trivial. }
  assert(HpropsOr: isPDT partition s0
    \/ ~ In blockToRemove (filterPresent (filterOptionPaddr (getKSEntries partition s0)) s0)).
  {
    unfold isPDT. unfold getKSEntries. destruct (lookup partition (memory s0) beqAddr); cbn -[getKSEntriesAux]; auto.
    destruct v; cbn -[getKSEntriesAux]; auto.
  }
  destruct HpropsOr as [HpartIsPDT | Hres]; trivial. apply InFilterPresentInList in HblockMappeds0.
  specialize(Hdisjoint removePart partition HremoveIsPDT HpartIsPDT HbeqParts).
  destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
  specialize(Hdisjoint blockToRemove HblockMappeds0). apply NotInListNotInFilterPresent; assumption.
}
apply getAllPaddrAuxEqRemove with blockToRemove removePart; trivial. apply IL.BlockNotMappedNotAccessible; trivial.
Qed.

Lemma getMappedPaddrEqRemPartRemove blockToRemove s s0 removePart:
noDupKSEntriesList s0
-> noDupMappedBlocksList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> exists leftList rightList, getMappedPaddr removePart s = leftList++rightList
    /\ getMappedPaddr removePart s0 = leftList++(getAllPaddrAux [blockToRemove] s0)++rightList.
Proof.
intros HnoDup HnoDupMapped HPDT HblockMappeds0 HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. unfold getMappedPaddr.
pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0 removePart HnoDup HPDT HblockMappeds0 HBE Hsh1IsSHE HSHE
  HsceIsSCE HSCE HlookupsEq) as HgetMappedBEq. assert(HremIsPDT: isPDT removePart s0).
{
  destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. unfold isPDT. rewrite Hlookups0. trivial.
}
specialize(HnoDupMapped removePart HremIsPDT).
destruct HgetMappedBEq as [leftList [rightList (HgetMappedBEqs & HgetMappedBEqs0)]]. rewrite HgetMappedBEqs.
rewrite HgetMappedBEqs0 in *. rewrite IL.getAllPaddrAuxSplit. rewrite IL.getAllPaddrAuxSplit.
rewrite IL.getAllPaddrAuxSplit. apply Lib.NoDupSplitInclIff in HnoDupMapped.
destruct HnoDupMapped as ((_ & HnoDupMapped) & HdisjointLeftRest). apply Lib.NoDupSplitInclIff in HnoDupMapped.
destruct HnoDupMapped as (_ & HdisjointBlockTRRight). assert(~In blockToRemove leftList).
{
  intro Hcontra. specialize(HdisjointLeftRest blockToRemove Hcontra). contradict HdisjointLeftRest. apply in_or_app.
  left. simpl. auto.
}
assert(~In blockToRemove rightList).
{
  assert(HblockInBlock: In blockToRemove [blockToRemove]) by (left; simpl; auto).
  specialize(HdisjointBlockTRRight blockToRemove HblockInBlock). assumption.
}
rewrite getAllPaddrAuxEqRemove with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
assert(Heq: getAllPaddrAux rightList s = getAllPaddrAux rightList s0).
{ apply getAllPaddrAuxEqRemove with blockToRemove removePart; trivial. }
rewrite Heq. exists (getAllPaddrAux leftList s0). exists (getAllPaddrAux rightList s0). auto.
Qed.

Lemma getAccessibleMappedBlocksEqRemPartRemove blockToRemove s s0 removePart:
noDupKSEntriesList s0
-> noDupMappedBlocksList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getAccessibleMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> exists leftList rightList, getAccessibleMappedBlocks removePart s = leftList ++ rightList
    /\ getAccessibleMappedBlocks removePart s0 = leftList ++ filterAccessible [blockToRemove] s0 ++ rightList.
Proof.
intros HnoDup HnoDupMapped HPDT HblockAccMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq.
unfold getAccessibleMappedBlocks in *. assert(HblockMapped: In blockToRemove (getMappedBlocks removePart s0)).
{
  destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
  apply InFilterAccessibleInList with s0; trivial.
}
pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0 removePart HnoDup HPDT HblockMapped HBE Hsh1IsSHE HSHE
  HsceIsSCE HSCE HlookupsEq) as HgetMappedBEq. destruct HgetMappedBEq as [leftList [rightList (Heqs & Heqs0)]].
assert(HPDTCopy: exists pdentry0 pdentry1,
    lookup removePart (memory s0) beqAddr = Some (PDT pdentry0)
    /\ lookup removePart (memory s) beqAddr = Some (PDT pdentry1)
    /\ pdentry1 =
        {|
          structure := structure pdentry0;
          firstfreeslot := blockToRemove;
          nbfreeslots := CIndex (nbfreeslots pdentry0 + 1);
          nbprepare := nbprepare pdentry0;
          parent := parent pdentry0;
          MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
          vidtAddr := vidtAddr pdentry0
        |}) by assumption.
destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & Hpdentry1)]]. rewrite Hlookups. rewrite Hlookups0.
rewrite Heqs. assert(HremIsPDT: isPDT removePart s0).
{ unfold isPDT. rewrite Hlookups0. trivial. }
specialize(HnoDupMapped removePart HremIsPDT). rewrite Heqs0 in *.
apply Lib.NoDupSplitInclIff in HnoDupMapped. destruct HnoDupMapped as ((_ & HnoDupMapped) & HdisjointLeftRest).
apply Lib.NoDupSplitInclIff in HnoDupMapped. destruct HnoDupMapped as (_ & HdisjointBlockTRRight).
assert(~In blockToRemove leftList).
{
  intro Hcontra. specialize(HdisjointLeftRest blockToRemove Hcontra). contradict HdisjointLeftRest. apply in_or_app.
  left. simpl. auto.
}
assert(~In blockToRemove rightList).
{
  assert(HblockInBlock: In blockToRemove [blockToRemove]) by (left; simpl; auto).
  specialize(HdisjointBlockTRRight blockToRemove HblockInBlock). assumption.
}
assert(~In blockToRemove (leftList++rightList)).
{ apply Lib.in_or_app_neg; auto. }
rewrite filterAccessibleEqRemove with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
rewrite filterAccessibleSplit. rewrite filterAccessibleSplit. rewrite filterAccessibleSplit.
exists (filterAccessible leftList s0). exists (filterAccessible rightList s0). auto.
Qed.

Lemma getAccessibleMappedPaddrEqRemPartRemove blockToRemove s s0 removePart:
noDupKSEntriesList s0
-> noDupMappedBlocksList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getAccessibleMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> exists leftList rightList, getAccessibleMappedPaddr removePart s = leftList ++ rightList
    /\ getAccessibleMappedPaddr removePart s0
        = leftList ++ getAllPaddrAux (filterAccessible [blockToRemove] s0) s0 ++ rightList.
Proof.
intros HnoDup HnoDupMapped HPDT HblockAccMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq.
unfold getAccessibleMappedPaddr. pose proof (getAccessibleMappedBlocksEqRemPartRemove blockToRemove s s0 removePart
  HnoDup HnoDupMapped HPDT HblockAccMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
assert(HremIsPDT: isPDT removePart s0).
{ destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. unfold isPDT. rewrite Hlookups0. trivial. }
specialize(HnoDupMapped removePart HremIsPDT). destruct Heqs as [leftList [rightList (Heqs & Heqs0)]]. rewrite Heqs.
assert(HnoDupAccMapped: NoDup (getAccessibleMappedBlocks removePart s0)).
{
  unfold getAccessibleMappedBlocks. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0.
  apply NoDupFilterAccessible; trivial.
}
assert(HAflag: bentryAFlag blockToRemove true s0).
{ apply accessibleMappedBlockIsAccessible with removePart; trivial. }
rewrite Heqs0 in *. apply Lib.NoDupSplitInclIff in HnoDupAccMapped.
destruct HnoDupAccMapped as ((_ & HnoDupAccMapped) & HdisjointLeftRest).
apply Lib.NoDupSplitInclIff in HnoDupAccMapped. destruct HnoDupAccMapped as (_ & HdisjointBlockTRRight).
assert(HblockInBlock: In blockToRemove (filterAccessible [blockToRemove] s0)).
{
  simpl. unfold bentryAFlag in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. rewrite Hlookups0 in *.
  rewrite <-HAflag. simpl. auto.
}
assert(~In blockToRemove leftList).
{
  intro Hcontra. specialize(HdisjointLeftRest blockToRemove Hcontra). contradict HdisjointLeftRest. apply in_or_app.
  auto.
}
assert(~In blockToRemove rightList).
{
  specialize(HdisjointBlockTRRight blockToRemove HblockInBlock). assumption.
}
rewrite IL.getAllPaddrAuxSplit. rewrite IL.getAllPaddrAuxSplit. rewrite IL.getAllPaddrAuxSplit.
rewrite getAllPaddrAuxEqRemove with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
exists (getAllPaddrAux leftList s0). exists (getAllPaddrAux rightList s0).
rewrite getAllPaddrAuxEqRemove with (blockToRemove:=blockToRemove) (s:=s) (s0:=s0) (removePart:=removePart); trivial.
auto.
Qed.

Lemma getConfigBlocksAuxEqRemove blockToRemove s s0 removePart n kernel idx:
(exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getConfigBlocksAux n kernel s idx = getConfigBlocksAux n kernel s0 idx.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. revert kernel idx.
induction n; intros kernel idx; simpl; trivial. destruct (beqAddr removePart kernel) eqn:HbeqPartKern.
{
  rewrite <-beqAddrTrue in HbeqPartKern. subst kernel.
  destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]]. rewrite Hlookups. rewrite Hlookups0. reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) kernel) eqn:HbeqSh1Kern.
{
  rewrite <-beqAddrTrue in HbeqSh1Kern. subst kernel. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) kernel) eqn:HbeqSceKern.
{
  rewrite <-beqAddrTrue in HbeqSceKern. subst kernel. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
assert(Heq: match Paddr.addPaddrIdx kernel nextoffset with
            | Some p =>
                match lookup p (memory s) beqAddr with
                | Some (PADDR addr) =>
                    match StateLib.Index.pred idx with
                    | Some p0 => SomePaddr kernel :: getConfigBlocksAux n addr s p0
                    | None => [NonePaddr]
                    end
                | _ => [NonePaddr]
                end
            | None => [NonePaddr]
            end = match Paddr.addPaddrIdx kernel nextoffset with
                  | Some p =>
                      match lookup p (memory s0) beqAddr with
                      | Some (PADDR addr) =>
                          match StateLib.Index.pred idx with
                          | Some p0 => SomePaddr kernel :: getConfigBlocksAux n addr s0 p0
                          | None => [NonePaddr]
                          end
                      | _ => [NonePaddr]
                      end
                  | None => [NonePaddr]
                  end).
{
  destruct (Paddr.addPaddrIdx kernel nextoffset); trivial. destruct (beqAddr removePart p) eqn:HbeqPartP.
  {
    rewrite <-beqAddrTrue in HbeqPartP. subst p.
    destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]]. rewrite Hlookups. rewrite Hlookups0.
    reflexivity.
  }
  destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) p) eqn:HbeqSh1P.
  {
    rewrite <-beqAddrTrue in HbeqSh1P. subst p. rewrite HSHE. unfold isSHE in *.
    destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
  }
  destruct (beqAddr (CPaddr (blockToRemove+scoffset)) p) eqn:HbeqSceP.
  {
    rewrite <-beqAddrTrue in HbeqSceP. subst p. rewrite HSCE. unfold isSCE in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
  }
  destruct (beqAddr blockToRemove p) eqn:HbeqBTRP.
  {
    rewrite <-beqAddrTrue in HbeqBTRP. subst p.
    destruct HBE as [bentry0 [newEnd [l (Hlookups0 & _ & Hlookups)]]]. rewrite Hlookups. rewrite Hlookups0.
    reflexivity.
  }
  rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. destruct (lookup p (memory s0) beqAddr); trivial.
  destruct v; trivial. destruct (StateLib.Index.pred idx); trivial. rewrite IHn; trivial.
}
rewrite Heq. destruct (beqAddr blockToRemove kernel) eqn:HbeqBlocks.
- rewrite <-beqAddrTrue in HbeqBlocks. subst kernel.
  destruct HBE as [bentry0 [newEnd [l (Hlookups0 & _ & Hlookups)]]]. rewrite Hlookups. rewrite Hlookups0. reflexivity.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getConfigBlocksEqRemove blockToRemove s s0 removePart partition:
(exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getConfigBlocks partition s = getConfigBlocks partition s0.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. unfold getConfigBlocks.
destruct (beqAddr blockToRemove partition) eqn:HbeqBTRPart.
{
  rewrite <-beqAddrTrue in HbeqBTRPart. subst partition.
  destruct HBE as [bentry0 [newEnd [l (Hlookups0 & _ & Hlookups)]]]. rewrite Hlookups. rewrite Hlookups0. reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) partition) eqn:HbeqSh1Part.
{
  rewrite <-beqAddrTrue in HbeqSh1Part. subst partition. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) partition) eqn:HbeqScePart.
{
  rewrite <-beqAddrTrue in HbeqScePart. subst partition. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr removePart partition) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. subst partition.
  assert(exists pdentry0 pdentry1 : PDTable,
    lookup removePart (memory s0) beqAddr = Some (PDT pdentry0)
    /\ lookup removePart (memory s) beqAddr = Some (PDT pdentry1)
    /\ pdentry1 =
        {|
          structure := structure pdentry0;
          firstfreeslot := blockToRemove;
          nbfreeslots := CIndex (nbfreeslots pdentry0 + 1);
          nbprepare := nbprepare pdentry0;
          parent := parent pdentry0;
          MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
          vidtAddr := vidtAddr pdentry0
        |}) by assumption.
  destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & Hpdentry1)]]. rewrite Hlookups. rewrite Hlookups0.
  rewrite Hpdentry1. simpl. rewrite getConfigBlocksAuxEqRemove with (blockToRemove:=blockToRemove) (s0:=s0)
    (removePart:=removePart); trivial.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  destruct (lookup partition (memory s0) beqAddr); trivial. destruct v; trivial. rewrite getConfigBlocksAuxEqRemove
    with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
Qed.

Lemma getConfigPaddrEqRemove blockToRemove s s0 removePart partition:
(exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove+sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getConfigPaddr partition s = getConfigPaddr partition s0.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. unfold getConfigPaddr.
rewrite getConfigBlocksEqRemove with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
assert(Heq: getAllPaddrPDTAux [partition] s = getAllPaddrPDTAux [partition] s0).
{
  simpl. destruct (beqAddr blockToRemove partition) eqn:HbeqBTRPart.
  {
    rewrite <-beqAddrTrue in HbeqBTRPart. subst partition.
    destruct HBE as [bentry0 [newEnd [l (Hlookups0 & _ & Hlookups)]]]. rewrite Hlookups. rewrite Hlookups0.
    reflexivity.
  }
  destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) partition) eqn:HbeqSh1Part.
  {
    rewrite <-beqAddrTrue in HbeqSh1Part. subst partition. rewrite HSHE. unfold isSHE in *.
    destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
  }
  destruct (beqAddr (CPaddr (blockToRemove+scoffset)) partition) eqn:HbeqScePart.
  {
    rewrite <-beqAddrTrue in HbeqScePart. subst partition. rewrite HSCE. unfold isSCE in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
  }
  destruct (beqAddr removePart partition) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst partition.
    destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]]. rewrite Hlookups. rewrite Hlookups0.
    reflexivity.
  - rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
}
rewrite Heq. f_equal. induction (getConfigBlocks partition s0); simpl; trivial. rewrite IHl.
destruct (beqAddr removePart a) eqn:HbeqPartA.
{
  rewrite <-beqAddrTrue in HbeqPartA. subst a.
  destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & _)]]. rewrite Hlookups. rewrite Hlookups0.
  reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) a) eqn:HbeqSh1A.
{
  rewrite <-beqAddrTrue in HbeqSh1A. subst a. rewrite HSHE. unfold isSHE in *.
  destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) a) eqn:HbeqSceA.
{
  rewrite <-beqAddrTrue in HbeqSceA. subst a. rewrite HSCE. unfold isSCE in *.
  destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
destruct (beqAddr blockToRemove a) eqn:HbeqBTRA.
- rewrite <-beqAddrTrue in HbeqBTRA. subst a. destruct HBE as [bentry0 [newEnd [l0 (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups. rewrite Hlookups0. reflexivity.
- rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma getConfigPaddrEqRemoveRec part s s0 removePart blockToRemove statesList blocksList:
removedBlockRec s s0 removePart blockToRemove statesList blocksList
-> getConfigPaddr part s = getConfigPaddr part s0.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HblocksList;
  try(destruct HblocksList; subst s; reflexivity).
destruct HblocksList as [blockChild [blocksListRec (HlistsEq & HbeqBlockNull & Hnext & HPDT & HBTRMapped & HAflagBTR
  & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
assert(Heq: getConfigPaddr part a = getConfigPaddr part s0).
{
  revert HlookupsEq. apply getConfigPaddrEqRemove; trivial.
  - unfold isSHE. unfold sh1entryPDchild in *.
    destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  - unfold isSCE. unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
}
rewrite <-Heq. revert HblocksListRec. apply IHstatesList; trivial.
Qed.

Lemma noDupMappedPaddrListPreservedRemove s s0 removePart blockToRemove:
noDupMappedPaddrList s0
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove + sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> noDupMappedPaddrList s.
Proof.
intros HnoDupPaddr HnoDup Hdisjoint Hwell HPDT HblockTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq part
  HpartIsPDT. assert(HpartIsPDTs0: isPDT part s0).
{
  unfold isPDT in *. destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
    rewrite Hlookups0. trivial.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
    + intro Hcontra. subst part. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. rewrite Hlookups in *.
      congruence.
    + intro Hcontra. subst part. rewrite HSHE in *. congruence.
    + intro Hcontra. subst part. rewrite HSCE in *. congruence.
}
specialize(HnoDupPaddr part HpartIsPDTs0). destruct (beqAddr removePart part) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0
    removePart HnoDup HPDT HblockTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
  destruct Heqs as [leftList [rightList (Heqs & Heqs0)]]. unfold getMappedPaddr in *. rewrite Heqs.
  rewrite Heqs0 in HnoDupPaddr. rewrite IL.getAllPaddrAuxSplit in *. rewrite IL.getAllPaddrAuxSplit in *.
  apply Lib.NoDupSplitInclIff in HnoDupPaddr. destruct HnoDupPaddr as ((HnoDupLeft & HnoDupRest) & HdisjointLeftRest).
  apply Lib.NoDupSplitInclIff in HnoDupRest. destruct HnoDupRest as ((_ & HnoDupRight) & HdisjointBlockRight).
  assert(HleftEq: getAllPaddrAux leftList s = getAllPaddrAux leftList s0).
  {
    apply getAllPaddrAuxEqRemove with blockToRemove removePart; trivial.
    assert(HdisjointLeftBlock: Lib.disjoint (getAllPaddrAux leftList s0) (getAllPaddrAux [blockToRemove] s0)).
    {
      apply Lib.inclDisjoint with (getAllPaddrAux leftList s0)
        (getAllPaddrAux [blockToRemove] s0 ++ getAllPaddrAux rightList s0); trivial. unfold incl. auto.
      apply incl_appl. unfold incl. auto.
    }
    destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. apply Lib.disjointPermut in HdisjointLeftBlock.
    assert(HstartIn: In (startAddr (blockrange bentry0)) (getAllPaddrAux [blockToRemove] s0)).
    {
      assert(Hstart: bentryStartAddr blockToRemove (startAddr (blockrange bentry0)) s0).
      { unfold bentryStartAddr. rewrite Hlookups0. reflexivity. }
      assert(Hend: bentryEndAddr blockToRemove (endAddr (blockrange bentry0)) s0).
      { unfold bentryEndAddr. rewrite Hlookups0. reflexivity. }
      assert(HPflag: bentryPFlag blockToRemove true s0).
      {
        apply IL.mappedBlockIsBE in HblockTRMapped. destruct HblockTRMapped as [bentry (Hlookup & Hpres)].
        unfold bentryPFlag. rewrite Hlookup. auto.
      }
      specialize(Hwell blockToRemove (startAddr (blockrange bentry0)) (endAddr (blockrange bentry0)) HPflag Hstart
        Hend). destruct Hwell as (Hwell & _). simpl. rewrite Hlookups0. rewrite app_nil_r.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    specialize(HdisjointLeftBlock (startAddr (blockrange bentry0)) HstartIn). contradict HdisjointLeftBlock.
    apply blockIsMappedAddrInPaddrList with blockToRemove; trivial.
  }
  assert(HrightEq: getAllPaddrAux rightList s = getAllPaddrAux rightList s0).
  {
    apply getAllPaddrAuxEqRemove with blockToRemove removePart; trivial.
    destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]].
    assert(HstartIn: In (startAddr (blockrange bentry0)) (getAllPaddrAux [blockToRemove] s0)).
    {
      assert(Hstart: bentryStartAddr blockToRemove (startAddr (blockrange bentry0)) s0).
      { unfold bentryStartAddr. rewrite Hlookups0. reflexivity. }
      assert(Hend: bentryEndAddr blockToRemove (endAddr (blockrange bentry0)) s0).
      { unfold bentryEndAddr. rewrite Hlookups0. reflexivity. }
      assert(HPflag: bentryPFlag blockToRemove true s0).
      {
        apply IL.mappedBlockIsBE in HblockTRMapped. destruct HblockTRMapped as [bentry (Hlookup & Hpres)].
        unfold bentryPFlag. rewrite Hlookup. auto.
      }
      specialize(Hwell blockToRemove (startAddr (blockrange bentry0)) (endAddr (blockrange bentry0)) HPflag Hstart
        Hend). destruct Hwell as (Hwell & _). simpl. rewrite Hlookups0. rewrite app_nil_r.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    specialize(HdisjointBlockRight (startAddr (blockrange bentry0)) HstartIn). contradict HdisjointBlockRight.
    apply blockIsMappedAddrInPaddrList with blockToRemove; trivial.
  }
  rewrite HleftEq. rewrite HrightEq. apply Lib.NoDupSplitInclIff. split; auto.
  apply Lib.inclDisjoint with (getAllPaddrAux leftList s0)
    (getAllPaddrAux [blockToRemove] s0 ++ getAllPaddrAux rightList s0); trivial. unfold incl. auto.
  apply incl_appr. unfold incl. auto.
- rewrite <-beqAddrFalse in *.
  rewrite getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
Qed.

Lemma parentOfPartitionIsPartitionPreservedRemove s s0 removePart blockToRemove:
parentOfPartitionIsPartition s0
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> parentOfPartitionIsPartition s.
Proof.
intros HparentOfPart HnoDup Hdisjoint Hnull HnoDupMapped HPDT HblockTRMapped HBE HPDflag HSHE HsceIsSCE HSCE
  HlookupsEq part pdentry HlookupPart.
assert(HlookupParts0: exists pdentrys0, lookup part (memory s0) beqAddr = Some (PDT pdentrys0)
  /\ parent pdentry = parent pdentrys0).
{
  destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part.
    destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & Hpdentry1)]]. exists pdentry0.
    rewrite Hlookups in HlookupPart. injection HlookupPart as HpdentriesEq. subst pdentry. rewrite Hpdentry1.
    split; auto.
  - rewrite <-beqAddrFalse in *. exists pdentry. split; trivial. rewrite <-HlookupsEq; trivial.
    + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]]. congruence.
    + intro Hcontra. subst part. congruence.
    + intro Hcontra. subst part. congruence.
}
destruct HlookupParts0 as [pdentrys0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq.
specialize(HparentOfPart part pdentrys0 HlookupParts0). destruct HparentOfPart as (HparentIsPart & HpropsParent).
split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
rewrite HgetPartsEq. split; trivial. destruct (beqAddr removePart (parent pdentrys0)) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. rewrite <-HbeqParts. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
  exists pdentry1. assumption.
- rewrite <-beqAddrFalse in *. exists parentEntry. rewrite HlookupsEq; trivial.
  + intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. congruence.
  + intro Hcontra. rewrite <-Hcontra in *. unfold sh1entryPDflag in *. rewrite HlookupParent in *. congruence.
  + intro Hcontra. rewrite <-Hcontra in *. unfold isSCE in *. rewrite HlookupParent in *. congruence.
Qed.

Lemma isChildPreservedRemove s s0 removePart blockToRemove:
isChild s0
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isChild s.
Proof.
intros HisChild HnoDup Hdisjoint Hnull HnoDupMapped HPDT HblockTRMapped HBE HPDflag HSHE HsceIsSCE HSCE
  HlookupsEq part pdparent HpartIsPart Hparent HbeqPartRoot.
assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s0).
{ apply getChildrenEqRemove with removePart blockToRemove; trivial. }
rewrite HgetPartsEq in *. rewrite HgetChildrenEq.
assert(Hparents0: pdentryParent part pdparent s0).
{
  unfold pdentryParent in *. destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part.
    destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & Hlookups & Hpdentry1)]]. rewrite Hlookups in *.
    rewrite Hlookups0. rewrite Hpdentry1 in Hparent. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
    + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]]. rewrite Hlookups in *.
      congruence.
    + intro Hcontra. subst part. rewrite HSHE in *. congruence.
    + intro Hcontra. subst part. rewrite HSCE in *. congruence.
}
specialize(HisChild part pdparent HpartIsPart Hparents0 HbeqPartRoot). assumption.
Qed.

Lemma noChildImpliesAddressesNotSharedPreservedRemove s s0 removePart blockToRemove:
noChildImpliesAddressesNotShared s0
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> noChildImpliesAddressesNotShared s.
Proof.
intros HnoChild HnoDup Hdisjoint Hnull HnoDupMapped HPDT HBTRMapped HBE HPDflag HSHE HsceIsSCE HSCE
  HlookupsEq part pdentry block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild child addr
  HchildIsChild HaddrMapped.
assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
assert(HgetChildrenEq: getChildren part s = getChildren part s0).
{ apply getChildrenEqRemove with removePart blockToRemove; trivial. }
rewrite HgetPartsEq in *. rewrite HgetChildrenEq in *.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove+sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDflag in *.
  destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HblockMappeds0: In block (getMappedBlocks part s0)).
{
  destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0
      removePart HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
    destruct Heqs as [leftList [rightList (Heqs & Heqs0)]]. rewrite Heqs0. rewrite Heqs in *. apply in_or_app.
    apply in_app_or in HblockMapped. destruct HblockMapped; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=s)
      (removePart:=removePart); trivial.
}
assert(blockToRemove <> block).
{
  intro Hcontra. subst block. apply IL.mappedBlockIsBE in HblockMapped.
  destruct HblockMapped as [bentry (Hlookup & Hpres)]. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
  rewrite Hlookups in Hlookup. injection Hlookup as HbentriesEq. subst bentry. simpl in *. congruence.
}
unfold sh1entryPDchild in *.
assert(HlookupSh1Eq: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
{
  apply HlookupsEq.
  - intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]]. rewrite Hlookups in *.
    congruence.
  - intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
    rewrite Hlookups in *. congruence.
  - subst sh1entryaddr. intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
    rewrite HcontraBis in *. unfold nullAddrExists in *. unfold isPADDR in *. unfold isSHE in *.
    destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  - intro Hcontra. rewrite <-Hcontra in *. rewrite HSCE in *. congruence.
}
rewrite HlookupSh1Eq in *. assert(HaddrMappeds0: In addr (getAllPaddrAux [block] s0)).
{
  simpl in *. rewrite <-HlookupsEq; trivial.
  - intro Hcontra. subst block. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]]. rewrite Hlookups in *.
    simpl in *. congruence.
  - intro Hcontra. subst block. rewrite HSHE in *. simpl in *. congruence.
  - intro Hcontra. subst block. rewrite HSCE in *. simpl in *. congruence.
}
assert(HlookupParts0: exists pdentrys0, lookup part (memory s0) beqAddr = Some (PDT pdentrys0)).
{
  destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. exists pdentry0.
    assumption.
  - rewrite <-beqAddrFalse in *. exists pdentry. rewrite <-HlookupsEq; trivial.
    + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]]. congruence.
    + intro Hcontra. subst part. congruence.
    + intro Hcontra. subst part. congruence.
}
destruct HlookupParts0 as [pdentrys0 HlookupParts0].
specialize(HnoChild part pdentrys0 block sh1entryaddr HpartIsPart HlookupParts0 HblockMappeds0 Hsh1 HPDchild child
  addr HchildIsChild HaddrMappeds0). contradict HnoChild. destruct (beqAddr removePart child) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. subst child. pose proof (getMappedPaddrEqRemPartRemove blockToRemove s s0
    removePart HnoDup HnoDupMapped HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
  destruct Heqs as [leftList [rightList (Heqs & Heqs0)]]. rewrite Heqs0. rewrite Heqs in *. apply in_or_app.
  apply in_app_or in HnoChild. destruct HnoChild; auto. right. apply in_or_app. auto.
- rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=s)
    (removePart:=removePart); trivial.
Qed.

Lemma noDupPartitionTreePreservedRemove s s0 removePart blockToRemove:
noDupPartitionTree s0
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> noDupPartitionTree s.
Proof.
intros HnoDupTree HnoDup Hdisjoint Hnull HnoDupMapped HPDT HBTRMapped HBE HPDflag HSHE HsceIsSCE HSCE HlookupsEq.
assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
unfold noDupPartitionTree. rewrite HgetPartsEq. assumption.
Qed.

Lemma kernelDataIsolationPreservedRemove s s0 removePart blockToRemove:
kernelDataIsolation s0
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> bentryAFlag blockToRemove true s0
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> kernelDataIsolation s.
Proof.
intros HKDI HnoDup Hdisjoint Hnull HnoDupMapped HPDT HBTRMapped HAflagBTR HBE HPDflag HSHE HsceIsSCE HSCE
  HlookupsEq part1 part2 Hpart1IsPart Hpart2IsPart addr HaddrAccMapped1.
assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove+sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDflag in *.
  destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
rewrite HgetPartsEq in *. assert(HaddrAccMapped1s0: In addr (getAccessibleMappedPaddr part1 s0)).
{
  destruct (beqAddr removePart part1) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part1.
    assert(HBTRAccMapped: In blockToRemove (getAccessibleMappedBlocks removePart s0)).
    { apply IL.accessibleBlockIsAccessibleMapped; trivial. }
    pose proof (getAccessibleMappedPaddrEqRemPartRemove blockToRemove s s0 removePart HnoDup HnoDupMapped HPDT
      HBTRAccMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
    destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite HeqA in *. rewrite Heqs0.
    apply in_app_or in HaddrAccMapped1. apply in_or_app. destruct HaddrAccMapped1; auto. right. apply in_or_app.
    auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getAccessibleMappedPaddrEqRemove with (blockToRemove:=blockToRemove)
      (s:=s) (removePart:=removePart); trivial.
}
specialize(HKDI part1 part2 Hpart1IsPart Hpart2IsPart addr HaddrAccMapped1s0).
rewrite getConfigPaddrEqRemove with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=removePart); trivial.
Qed.

Lemma getMappedBlocksEqRemoveRec blockToRemove s s0 removePart statesList blocksList partition:
removePart <> partition
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> wellFormedFstShadowIfBlockEntry s0
-> noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> noDupMappedPaddrList s0
-> (exists nextBlocksList, checkRemoveOkRec blockToRemove removePart nextBlocksList s0
      /\ nullAddr = last nextBlocksList blockToRemove)
-> In removePart (getPartitions multiplexer s0)
-> In blockToRemove (getMappedBlocks removePart s0)
-> removedBlockRec s s0 removePart blockToRemove statesList blocksList
-> getMappedBlocks partition s = getMappedBlocks partition s0.
Proof.
intros HbeqParts. revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList
  Hdisjoint Hwell Hsh1IsSHE HnoDup Hnull HnoDupMapped HnoDupPaddr HnextBlocksList HremovePartIsPart
  HblockTRMapped HblocksList.
- destruct HblocksList as (_ & Hs). subst s. reflexivity.
- destruct HblocksList as [blockChild [blocksListRec (HlistsEq & HbeqBlockNull & Hnext & HPDT & HBTRMapped & HAflagBTR
    & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
  assert(HblockTRIsBE: isBE blockToRemove s0).
  {
    destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. unfold isBE. rewrite Hlookups0. trivial.
  }
  assert(HgetMappedEqA: getMappedBlocks partition a = getMappedBlocks partition s0).
  {
    apply getMappedBlocksEqRemove with blockToRemove removePart; trivial.
    - specialize(Hsh1IsSHE blockToRemove HblockTRIsBE). assumption.
    - unfold scentryNext in *. unfold isSCE.
      destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
  }
  rewrite <-HgetMappedEqA. assert(HpropsOr: s = a \/ blockChild <> nullAddr).
  {
    clear IHstatesList. induction statesList; simpl in *.
    - destruct HblocksListRec as (_ & Hres). auto.
    - destruct HblocksListRec as [_ [_ (_ & Hres & _)]]. auto.
  }
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold isSCE. unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  destruct HpropsOr as [Heq | HbeqBlockCNull]; try(subst s; reflexivity).
  assert(isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  { specialize(Hsh1IsSHE blockToRemove HblockTRIsBE). assumption. }
  destruct HnextBlocksList as [nextBlocksList (HnextBlocksList & Hlast)].
  pose proof (noDupNextBlocksList blockToRemove removePart nextBlocksList s0 Hnull Hwell HnoDupPaddr
    HremovePartIsPart HnextBlocksList) as HnoDupList. apply NoDup_cons_iff in HnoDupList.
  destruct HnoDupList as (HblockTRNotInNextList & HnoDupList).
  destruct nextBlocksList as [ | blockChildBis nextBlocksList].
  { simpl in *. congruence. }
  apply IL.lastRec in Hlast. simpl in *.
  destruct HnextBlocksList as (HAflag & HPflag & HblockTRMappeds & HPDchildBis & HnextBis & HnextBlockSidePartial &
    HnextBlocksList). assert(blockChildBis = blockChild).
  {
    unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite <-Hnext in *. assumption.
  }
  subst blockChildBis. clear HnextBis.
  assert(exists nextBlocksList, checkRemoveOkRec blockChild removePart nextBlocksList a
    /\ nullAddr = last nextBlocksList blockChild).
  {
    exists nextBlocksList. split; trivial. apply checkRemoveOkPreservedRemove with s0 blockToRemove; trivial.
  }
  apply IHstatesList with blockChild blocksListRec; trivial.
  + apply DisjointKSEntriesPreservedRemove with s0 removePart blockToRemove; trivial.
  + apply wellFormedBlockPreservedRemove with s0 removePart blockToRemove; trivial.
  + apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 removePart blockToRemove; trivial.
  + apply noDupKSEntriesListPreservedRemove with s0 removePart blockToRemove; trivial.
  + apply nullAddrExistsPreservedRemove with s0 removePart blockToRemove; trivial.
  + apply noDupMappedBlocksListPreservedRemove with s0 removePart blockToRemove; trivial.
  + apply noDupMappedPaddrListPreservedRemove with s0 removePart blockToRemove; trivial.
  + assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
    {
      apply getPartitionsEqRemove with removePart blockToRemove; trivial.
    }
    rewrite HgetPartsEq. assumption.
  + assert(HeqTriv: CPaddr (blockToRemove+scoffset) = CPaddr (blockToRemove+scoffset)) by reflexivity.
    assert(Hend: exists endaddr, bentryEndAddr blockToRemove endaddr s0).
    {
      unfold bentryEndAddr. unfold isBE in *.
      destruct (lookup blockToRemove (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
    }
    destruct Hend as [endaddr Hend]. specialize(Hsh1IsSHE blockToRemove HblockTRIsBE).
    pose proof (getMappedBlocksEquivRemove blockToRemove a s0 removePart HnoDup HPDT HblockTRMapped HBE Hsh1IsSHE
      HSHE HsceIsSCE HSCE HlookupsEq) as HgetMappedEquivA. destruct HgetMappedEquivA as (HgetMappedEquivA & _).
    specialize(HnextBlockSidePartial HbeqBlockCNull). destruct HnextBlockSidePartial as (HblockCMappeds0 & _).
    apply HgetMappedEquivA in HblockCMappeds0. simpl in *. destruct HblockCMappeds0 as [Hcontra | Hres]; trivial.
    apply Decidable.not_or in HblockTRNotInNextList. destruct HblockTRNotInNextList as (HbeqBlocks & _).
    exfalso; congruence.
Qed.
(*TODO probably needs the lemma for removePart, but that will be nasty*)

(*TODO that lemma will probably be updated a lot*)
Lemma removeSubblocksRecAux n (idPDchild blockToRemove firstBlockToRemove: paddr) (P: state -> Prop) :
{{ fun s : state =>
    (forall blocksList, checkRemoveOkRec blockToRemove idPDchild blocksList s -> length blocksList < n)
    /\ In idPDchild (getPartitions multiplexer s)
    /\ cons1Free s
    /\ noDupMappedPaddrList s
    /\ (exists nextBlocksList, checkRemoveOkRec blockToRemove idPDchild nextBlocksList s
          /\ nullAddr = last nextBlocksList blockToRemove)
    /\ exists statesList blocksList s0,
        removedBlockRec s s0 idPDchild firstBlockToRemove statesList blocksList
        /\ blockToRemove = last blocksList firstBlockToRemove
        /\ P s0
        /\ consistency s0
        /\ In firstBlockToRemove (getMappedBlocks idPDchild s0)
}}
Internal.removeSubblocksRecAux n idPDchild blockToRemove
{{ fun (recRemoveSubblocksEnded : bool) (s : state) => cons1Free s /\ noDupMappedPaddrList s
    /\ (exists statesList blocksList s0,
        removedBlockRec s s0 idPDchild firstBlockToRemove statesList blocksList
        /\ nullAddr = last blocksList firstBlockToRemove
        /\ P s0)
    /\ recRemoveSubblocksEnded = true
}}.
Proof.
revert blockToRemove. induction n; intro blockToRemove; simpl.
- (* n = 0 *)
  eapply weaken. apply ret. intros s Hprops. simpl. exfalso. destruct Hprops as (HlenNext & _).
  assert(HnextList: isNextList blockToRemove [] s) by (simpl; trivial). specialize(HlenNext [] HnextList). simpl in *.
  lia.
- (* n = S n*)
  eapply bindRev.
  { (** Internal.compareAddrToNull*)
    eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
  }
  intro isNull. destruct isNull.
  + (* case isNull = true *)
    eapply weaken. apply ret. intros s Hprops. simpl. destruct Hprops as ((_ & HchildIsPart & Hconsist & HnoDupPaddr
      & HnextBlocksList & [statesList [blocksList [s0 (HblocksList & Hlast & HP & Hconsits0 & HfirstMappeds0)]]])
      & HbeqNullBlock).
    split; trivial. split; trivial. rewrite <-beqAddrTrue in *. subst blockToRemove. split; trivial.
    exists statesList. exists blocksList. exists s0. auto.
  + (* case isNull = false *)
    eapply bindRev.
    { (** MAL.readSCNextFromBlockEntryAddr *)
      eapply weaken. apply readSCNextFromBlockEntryAddr. intros s Hprops. simpl.
      assert(HblockIsBE: isBE blockToRemove s).
      {
        destruct Hprops as ((_ & HchildIsPart & Hconsist & HnoDupPaddr & HnextBlocksList & [statesList [blocksList
          [s0 (HblocksList & Hlast & _ & Hconsists0 & HfirstMappeds0)]]]) & HbeqNullBlock). clear IHn.
        destruct HnextBlocksList as [nextBlocksList (HnextBlocksList & HlastNext)]. destruct nextBlocksList.
        { simpl in *. rewrite <-beqAddrFalse in *. exfalso; congruence. }
        simpl in HnextBlocksList. destruct HnextBlocksList as (HAflag & _). unfold bentryAFlag in *. unfold isBE.
        destruct (lookup blockToRemove (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
      }
      apply isBELookupEq in HblockIsBE. split. apply Hprops. unfold cons1Free in *. intuition.
    }
    intro nextBlock. eapply bindRev.
    { (** Internal.freeSlot *)
      eapply weaken. apply freeSlot. intros s Hprops. simpl.
      destruct Hprops as (((HnextLen & HchildIsPart & Hconsist & HnoDupPaddr & HnextBlocksList & HblocksList) &
        HbeqNullBlockTR) & Hnext).
      assert(Hblock: In blockToRemove (getMappedBlocks idPDchild s) /\ bentryAFlag blockToRemove true s).
      {
        destruct HnextBlocksList as [nextBlocksList (HnextBlocksList & Hlast)]. destruct nextBlocksList.
        { simpl in *. rewrite <-beqAddrFalse in *. exfalso; congruence. }
        simpl in HnextBlocksList. intuition.
      }
      destruct Hblock as (HblockTRMapped & HAflag).
      instantiate(1 := fun s =>
        (forall blocksList : list paddr, checkRemoveOkRec blockToRemove idPDchild blocksList s
          -> length blocksList < S n)
        /\ In idPDchild (getPartitions multiplexer s)
        /\ In blockToRemove (getMappedBlocks idPDchild s)
        /\ cons1Free s
        /\ noDupMappedPaddrList s
        /\ (exists nextBlocksList, checkRemoveOkRec blockToRemove idPDchild nextBlocksList s
            /\ nullAddr = last nextBlocksList blockToRemove)
        /\ (exists statesList blocksList s0, removedBlockRec s s0 idPDchild firstBlockToRemove statesList blocksList
            /\ blockToRemove = last blocksList firstBlockToRemove /\ P s0 /\ consistency s0
            /\ In firstBlockToRemove (getMappedBlocks idPDchild s0))
        /\ beqAddr nullAddr blockToRemove = false
        /\ scentryNext (CPaddr (blockToRemove + scoffset)) nextBlock s
        /\ bentryAFlag blockToRemove true s).
      split. intuition. split. apply IL.partitionsArePDT; trivial; unfold cons1Free in *; intuition.
      assert(HblockIsBE: isBE blockToRemove s).
      {
        unfold isBE. unfold bentryAFlag in *.
        destruct (lookup blockToRemove (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
      }
      split; trivial. split; trivial. assert(HaccNoPD: AccessibleNoPDFlag s) by (unfold cons1Free in *; intuition).
      assert(Hsh1: sh1entryAddr blockToRemove (CPaddr (blockToRemove + sh1offset)) s).
      {
        unfold sh1entryAddr. unfold isBE in *.
        destruct (lookup blockToRemove (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      specialize(HaccNoPD blockToRemove (CPaddr (blockToRemove + sh1offset)) HblockIsBE Hsh1 HAflag). split; trivial.
      split; trivial. apply IL.mappedBlockIsBE in HblockTRMapped.
      destruct HblockTRMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag. rewrite Hlookup. auto.
    }
    intro. eapply weaken. apply IHn. intros s Hprops. simpl.
    destruct Hprops as [s0 [s1 [s2 [s3 [s4 [s5 [s6 [pdentry [pdentry1 [pdentry2 [pdentry3 [realMPU [emptyBentry
      [freeBentry [currFirstFreeSlot [blockToFreeIdx (Hs & Hs6 & Hs5 & Hs4 & Hs3 & Hs2 & Hs1 & Hconsist & Hstructs6 &
      Hstructs5 &
      HlookupChilds5 & HlookupBlocks4 & HfirstChilds4 & Hidxs1 & HlookupChilds0 & HblockIsBEs0 & HMPUs0 & Hconsists0 &
      HgetPartsEq & HgetChildrenEq & HgetMappedEq & HgetMappedChild & HnewB & Hpdentry1 & Hpdentry2 & Hpdentry3 &
      HlebNbFreePlusMax & HnewB2 & (HlenBlocksList & HchildIsPart & HblockTRMappeds0 & _ & HnoDupPaddr &
      HnextBlocksList & HblocksList & HbeqNullBlockTR & HnextBTRs0 & HAflagBTRs0) & HgetPartsEqs1s0 & HPDTIfPDFlags1 &
      HmultIsPDTs1 & HgetMappedEqss2 & HgetKSEq)]]]]]]]]]]]]]]]].
(*Hconsist: (Hnull & Hsh1IsSHE &
      HPDTIfPDFlag & HaccNoPD & HfirstFree & HmultIsPDT & HcurrPartIsPart & HsceIsSCE & HrangeIsBE & HkernStructIsKS &
      HchildLocIsBE & Hstruct & HnextIsKS & HnextAddrIsPADDR & HnoDupFree & HfreeSlotsAreFree & HdisjointFree &
      HinclFreeKSE & Hdisjoint & HnoDupTree & HisParent & HisChild & HnoDup & HnoDupMapped & Hwell & HparentOfPart &
      HnbFreeIsLen & HmaxNbPrep & Htree & HentriesAreBE & HnextKernValid & HnoDupKerns & HMPUsize & Htypes &
      HnoPDFlag & HnextAddrInSameBlock & HblocksPart & HnoChild & HnbPrepIsLen & HchildIsPDT)*)
    destruct HnextBlocksList as [nextBlocksList (HnextBlocksList & HlastNext)]. destruct HblocksList as [statesList
      [blocksList [sInit (HblocksList & Hlast & HP & HconsistsInit & HfirstMappedsInit)]]].
    assert(HPDT: exists pdentry0 pdentry1, lookup idPDchild (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup idPDchild (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |}).
    {
      exists pdentry. exists pdentry3. rewrite Hs. simpl. rewrite IL.beqAddrTrue. split; trivial. split; trivial.
      rewrite Hpdentry2 in Hpdentry3. simpl in *. rewrite Hpdentry1 in Hpdentry3. simpl in *. unfold pdentryMPU in *.
      rewrite HlookupChilds0 in *. subst realMPU. assumption.
    }
    destruct HnewB as [l0 [l1 HnewB]]. destruct HnewB2 as [l2 [l3 HnewB2]].
    assert(HBE: exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot idPDchild newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |})).
    {
      unfold bentryBlockIndex in *. rewrite Hs1 in Hidxs1. simpl in *.
      destruct (beqAddr idPDchild blockToRemove) eqn:HbeqChildBlockTR; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      destruct (lookup blockToRemove (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). subst blockToFreeIdx. exists b. exists l0. exists currFirstFreeSlot.
      split; trivial. unfold pdentryFirstFreeSlot in *. rewrite Hs4 in HfirstChilds4. simpl in *.
      destruct (beqAddr (CPaddr (blockToRemove + scoffset)) idPDchild) eqn:HbeqSceChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs3 in HfirstChilds4. simpl in *.
      destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) idPDchild) eqn:HbeqSh1Child; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HfirstChilds4. simpl in *.
      destruct (beqAddr blockToRemove idPDchild) eqn:HbeqBlockTRChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HfirstChilds4. simpl in *. rewrite IL.beqAddrTrue in *. rewrite HlookupChilds0.
      rewrite Hpdentry1 in *. simpl in *. split; trivial. rewrite Hs.
      rewrite Hs6. simpl. rewrite beqAddrFalse in *. rewrite HbeqChildBlockTR. rewrite IL.beqAddrTrue.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl. rewrite IL.beqAddrTrue.
      f_equal. f_equal. subst emptyBentry. simpl in *. rewrite HnewB2. f_equal; try(apply proof_irrelevance).
      unfold CBlock. destruct (le_dec (currFirstFreeSlot - nullAddr) maxIdx); try(lia). f_equal.
      apply proof_irrelevance.
    }
    assert(Hsh1s0: sh1entryAddr blockToRemove (CPaddr (blockToRemove + sh1offset)) s0).
    {
      unfold sh1entryAddr. unfold isBE in *.
      destruct (lookup blockToRemove (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    assert(HPDflags0: sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0).
    {
      assert(HaccNoPDs0: AccessibleNoPDFlag s0) by (unfold cons1Free in *; intuition).
      specialize(HaccNoPDs0 blockToRemove (CPaddr (blockToRemove + sh1offset)) HblockIsBEs0 Hsh1s0 HAflagBTRs0).
      assumption.
    }
    assert(HPDchilds0: sh1entryPDchild (CPaddr (blockToRemove + sh1offset)) nullAddr s0).
    {
      destruct nextBlocksList.
      { simpl in *. rewrite <-beqAddrFalse in *. exfalso; congruence. }
      simpl in *. intuition.
    }
    assert(HSHE: lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
      = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})).
    {
      unfold sh1entryPDflag in *. rewrite Hs. rewrite Hs6. simpl. rewrite IL.beqAddrTrue.
      destruct (beqAddr idPDchild (CPaddr (blockToRemove + sh1offset))) eqn:HbeqChildSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqChildSh1. rewrite <-HbeqChildSh1 in *. rewrite HlookupChilds0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
      destruct (beqAddr blockToRemove (CPaddr (blockToRemove + sh1offset))) eqn:HbeqBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. exfalso. unfold isBE in *.
        destruct (lookup blockToRemove (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      destruct (beqAddr (CPaddr (blockToRemove + scoffset)) (CPaddr (blockToRemove + sh1offset))) eqn:HbeqSceSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. exfalso. unfold scentryNext in *.
        destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      rewrite IL.beqAddrTrue. reflexivity.
    }
    assert(HsceTRIsSCE: isSCE (CPaddr (blockToRemove+scoffset)) s0).
    {
      unfold isSCE. unfold scentryNext in *.
      destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
    }
    assert(HSCE: lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
      = Some(SCE {| origin := nullAddr; next := nullAddr |})).
    {
      unfold scentryNext in *. rewrite Hs. rewrite Hs6. simpl. rewrite IL.beqAddrTrue.
      destruct (beqAddr idPDchild (CPaddr (blockToRemove + scoffset))) eqn:HbeqChildSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqChildSce. rewrite <-HbeqChildSce in *. rewrite HlookupChilds0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
      destruct (beqAddr blockToRemove (CPaddr (blockToRemove + scoffset))) eqn:HbeqBlockSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *. exfalso. unfold isBE in *.
        destruct (lookup blockToRemove (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
      rewrite IL.beqAddrTrue. reflexivity.
    }
    assert(HlookupsEq: forall addr, idPDchild <> addr -> blockToRemove <> addr
      -> CPaddr (blockToRemove+sh1offset) <> addr
      -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
    {
      intros addr HbeqChildAddr HbeqBlockTRAddr HbeqSh1Addr HbeqSceAddr. rewrite beqAddrFalse in *. rewrite Hs.
      rewrite Hs6. simpl. rewrite HbeqChildAddr. rewrite IL.beqAddrTrue.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqBlockTRAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite Hs4. simpl. rewrite beqAddrFalse in *. rewrite HbeqSceAddr. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqSh1Addr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite Hs2. simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockTRAddr. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqChildAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(HPflagTRs0: bentryPFlag blockToRemove true s0).
    {
      apply IL.mappedBlockIsBE in HblockTRMappeds0. destruct HblockTRMappeds0 as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(forall blocksList, checkRemoveOkRec nextBlock idPDchild blocksList s -> length blocksList < n).
    {
      intros blocksListBis HisNextList.
      assert(HisNexts0: checkRemoveOkRec nextBlock idPDchild blocksListBis s0).
      {
        clear HnextBTRs0. revert HisNextList. generalize nextBlock. (*noDupNextBlocksList?*)
        induction blocksListBis as [ | nextB blocksListBis]; simpl; intros block HisNextList; trivial.
        destruct HisNextList as (HAflag & HPflag & HblockMapped & HPDchild & Hnext & HnextBlockSidePartial &
          HisNextList). unfold bentryAFlag in *. unfold bentryPFlag in *.
        destruct (beqAddr blockToRemove block) eqn:HbeqBlocks.
        {
          rewrite <-beqAddrTrue in HbeqBlocks. subst block.
          destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. rewrite Hlookups in HAflag. simpl in *.
          exfalso; congruence.
        }
        destruct (beqAddr idPDchild block) eqn:HbeqChildBlock.
        {
          rewrite <-beqAddrTrue in HbeqChildBlock. subst block.
          destruct HPDT as [pdentry0 [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. exfalso; congruence.
        }
        destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) block) eqn:HbeqSh1Block.
        {
          rewrite <-beqAddrTrue in HbeqSh1Block. subst block. rewrite HSHE in *. exfalso; congruence.
        }
        destruct (beqAddr (CPaddr (blockToRemove + scoffset)) block) eqn:HbeqSceBlock.
        {
          rewrite <-beqAddrTrue in HbeqSceBlock. subst block. rewrite HSCE in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite HlookupsEq in HAflag; trivial. rewrite HlookupsEq in HPflag; trivial.
        assert(HblockMappeds0: In block (getMappedBlocks idPDchild s0)).
        {
          specialize(HgetMappedChild block). destruct HgetMappedChild as (_ & Hres & _). apply Hres; assumption.
        }
        unfold sh1entryPDchild in *. destruct (beqAddr blockToRemove (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1.
        {
          rewrite <-beqAddrTrue in HbeqBlockSh1. rewrite HbeqBlockSh1 in *.
          destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. rewrite Hlookups in HPDchild.
          exfalso; congruence.
        }
        destruct (beqAddr idPDchild (CPaddr (block + sh1offset))) eqn:HbeqChildSh1.
        {
          rewrite <-beqAddrTrue in HbeqChildSh1. rewrite HbeqChildSh1 in *.
          destruct HPDT as [pdentry0 [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. exfalso; congruence.
        }
        assert(Hnull: nullAddrExists s) by (unfold cons1Free in *; intuition).
        destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s.
        {
          rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; try(exfalso; congruence). intro Hcontra.
          rewrite Hcontra in *. unfold sh1entryPDflag in *. unfold nullAddrExists in *. unfold isPADDR in *.
          destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
        }
        destruct (beqAddr (CPaddr (blockToRemove + scoffset)) (CPaddr (block + sh1offset))) eqn:HbeqSceSh1.
        {
          rewrite <-beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. rewrite HSCE in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite HlookupsEq in HPDchild; trivial.
        unfold scentryNext in *. destruct (beqAddr blockToRemove (CPaddr (block + scoffset))) eqn:HbeqBlockSce.
        {
          rewrite <-beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *.
          destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. rewrite Hlookups in Hnext.
          exfalso; congruence.
        }
        destruct (beqAddr idPDchild (CPaddr (block + scoffset))) eqn:HbeqChildSce.
        {
          rewrite <-beqAddrTrue in HbeqChildSce. rewrite HbeqChildSce in *.
          destruct HPDT as [pdentry0 [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. exfalso; congruence.
        }
        destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) (CPaddr (block + scoffset))) eqn:HbeqSh1Sce.
        {
          rewrite <-beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. rewrite HSHE in *. exfalso; congruence.
        }
        destruct (beqAddr (CPaddr (blockToRemove + scoffset)) (CPaddr (block + scoffset))) eqn:HbeqSces.
        {
          rewrite <-beqAddrTrue in HbeqSces. apply CPaddrAddEq in HbeqSces; try(exfalso; congruence). intro Hcontra.
          rewrite Hcontra in *. unfold isSCE in *. unfold nullAddrExists in *. unfold isPADDR in *.
          destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite HlookupsEq in Hnext; trivial. split; trivial. split; trivial.
        split; trivial. split; trivial. split; trivial. split; try(apply IHblocksListBis; assumption).
        intro HbeqNextNull. specialize(HnextBlockSidePartial HbeqNextNull).
        destruct HnextBlockSidePartial as (HnextMapped & HnextIsSide). specialize(HgetMappedChild nextB).
        destruct HgetMappedChild as (_ & HnextMappedIncl & _). split; try(apply HnextMappedIncl; assumption).
        intros endaddr Hend. unfold bentryEndAddr in *. rewrite <-HlookupsEq in Hend; trivial.
        specialize(HnextIsSide endaddr Hend). unfold bentryStartAddr in *. rewrite <-HlookupsEq; trivial.
        - intro Hcontra. subst nextB. destruct HPDT as [pdentry0 [pdentrys (_ & Hlookups & _)]].
          rewrite Hlookups in *. congruence.
        - intro Hcontra. subst nextB. assert(Hcontra: bentryPFlag blockToRemove true s).
          {
            apply IL.mappedBlockIsBE in HnextMapped. destruct HnextMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          unfold bentryPFlag in *. rewrite Hs in Hcontra. rewrite Hs6 in Hcontra. simpl  in *.
          destruct (beqAddr idPDchild blockToRemove) eqn:HbeqChildBlockTR; try(congruence).
          rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs5 in Hcontra. simpl in *.
          rewrite IL.beqAddrTrue in *. rewrite HnewB2 in Hcontra. simpl in *. rewrite HnewB in Hcontra. simpl in *.
          congruence.
        - intro Hcontra. subst nextB. rewrite HSHE in *. congruence.
        - intro Hcontra. subst nextB. rewrite HSCE in *. congruence.
      }
      assert(HisNextRec: checkRemoveOkRec blockToRemove idPDchild (nextBlock::blocksListBis) s0).
      {
        simpl. split; trivial. split; trivial. split; trivial. destruct nextBlocksList; simpl in *.
        { rewrite <-beqAddrFalse in *. exfalso; congruence. }
        split. intuition. split; trivial. assert(p = nextBlock).
        {
          assert(HnextBis: scentryNext (CPaddr (blockToRemove + scoffset)) p s0) by intuition.
          unfold scentryNext in *.
          destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-HnextBis in *. auto.
        }
        subst p. split; trivial. intuition.
      }
      specialize(HlenBlocksList (nextBlock::blocksListBis) HisNextRec). simpl in HlenBlocksList. lia.
    }
    rewrite HgetPartsEq. split; trivial. split; trivial. split; trivial.
    assert(HnoDup: NoDup (blockToRemove::nextBlocksList)).
    {
      apply noDupNextBlocksList with idPDchild s0; trivial; unfold cons1Free in *; intuition.
    }
    apply NoDup_cons_iff in HnoDup. destruct HnoDup as (HblockTRNotIn & _). destruct nextBlocksList.
    { simpl in *. rewrite <-beqAddrFalse in *. exfalso; congruence. }
    apply IL.lastRec in HlastNext. simpl in *.
    destruct HnextBlocksList as (_ & _ & _ & _ & HnextBis & _ & HnextBlocksList). assert(p = nextBlock).
    {
      unfold scentryNext in *.
      destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-HnextBis in *. auto.
    }
    subst p. (*apply Decidable.not_or in HblockTRNotIn. destruct HblockTRNotIn as (HbeqNextBlockTR & HblockTRNotIn).*)
    assert(noDupMappedPaddrList s).
    {
      intros part HpartIsPDT. assert(HpartIsPDTs0: isPDT part s0).
      {
        unfold isPDT in *. destruct (beqAddr idPDchild part) eqn:HbeqParts.
        - rewrite <-beqAddrTrue in HbeqParts. subst part. rewrite HlookupChilds0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
          + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
            rewrite Hlookups in *. congruence.
          + intro Hcontra. subst part. rewrite HSHE in *. congruence.
          + intro Hcontra. subst part. rewrite HSCE in *. congruence.
      }
      specialize(HnoDupPaddr part HpartIsPDTs0).
      assert(HgetMappedPEqNotChild: idPDchild <> part -> getMappedPaddr part s = getMappedPaddr part s0).
      {
        apply getMappedPaddrEqRemove with blockToRemove; trivial.
        - unfold cons1Free in *. intuition.
        - unfold sh1entryPDflag in *. unfold isSHE.
          destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
      }
      assert(HgetMappedPEqChild: exists leftList rightList,
         getMappedPaddr idPDchild s = leftList ++ rightList
         /\ getMappedPaddr idPDchild s0 = leftList ++ getAllPaddrAux [blockToRemove] s0 ++ rightList).
      {
        apply getMappedPaddrEqRemPartRemove; trivial. 1,2: unfold cons1Free in *; intuition. unfold isSHE.
        unfold sh1entryPDflag in *.
        destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part.
        destruct HgetMappedPEqChild as [leftList [rightList (HgetMappeds & HgetMappeds0)]]. rewrite HgetMappeds0 in *.
        rewrite HgetMappeds. apply Lib.NoDupSplitInclIff in HnoDupPaddr. apply Lib.NoDupSplitInclIff.
        destruct HnoDupPaddr as ((HnoDupLeft & HnoDupRest) & Hdisjoint). apply Lib.NoDupSplitInclIff in HnoDupRest.
        destruct HnoDupRest as ((_ & HnoDupRight) & _). split; auto. intros addr HaddrInLeft.
        specialize(Hdisjoint addr HaddrInLeft). contradict Hdisjoint. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite HgetMappedPEqNotChild; trivial.
    }
    split; trivial. assert(exists nextBlocksListBis, checkRemoveOkRec nextBlock idPDchild nextBlocksListBis s
      /\ nullAddr = last nextBlocksListBis nextBlock).
    {
      exists nextBlocksList. split; trivial. apply checkRemoveOkPreservedRemove with s0 blockToRemove; trivial.
      1,2,3: unfold cons1Free in *; intuition. unfold sh1entryPDflag in *. unfold isSHE.
      destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
    }
    split; trivial. exists (statesList++[s]). exists (blocksList++[nextBlock]). exists sInit.
    split; try(split; auto). 2: apply eq_sym; apply last_last. clear IHn. clear HP. clear HconsistsInit.
    clear HfirstMappedsInit. revert sInit firstBlockToRemove blocksList HblocksList Hlast.
    induction statesList; simpl; intros sInit firstBlockToRemove blocksList HblocksList Hlast.
    * destruct HblocksList. subst blocksList. subst sInit. exists nextBlock. exists []. split. auto. simpl in Hlast.
      subst blockToRemove. rewrite <-beqAddrFalse in *. split. auto. split; trivial. split; trivial. split; trivial.
      split; trivial. split; trivial. split; trivial. split; trivial. split; trivial. auto.
    * destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqFirstNull & Hnext & HPDTinit &
        HAflagBTR & HBTRMapped & HBEinit & HPDflag & HPDchild & HSHEinit & HSCEinit & HlookupsEqInit &
        HblocksList)]].
      exists blockChild. exists (blocksListRec++[nextBlock]).
      rewrite HblocksListEq. split; auto. split; trivial. split; trivial. split; trivial. split; trivial.
      split; trivial. split; trivial. split; trivial. split; trivial. split; trivial. split; trivial.
      split; trivial. apply IHstatesList; trivial. rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
      assumption.
Qed.

Lemma removeSubblocksRec (idPDchild blockToRemove: paddr) P :
{{ fun s => P s /\ consistency s
    /\ In blockToRemove (getMappedBlocks idPDchild s)
    /\ In idPDchild (getPartitions multiplexer s)
    /\ (exists nextBlocksList, checkRemoveOkRec blockToRemove idPDchild nextBlocksList s
        /\ nullAddr = last nextBlocksList blockToRemove)
}}
Internal.removeSubblocksRec idPDchild blockToRemove
{{ fun recRemoveSubblocksEnded s => cons1Free s /\ noDupMappedPaddrList s
    /\ (exists statesList blocksList s0,
        removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
        /\ nullAddr = last blocksList blockToRemove
        /\ P s0)
    /\ recRemoveSubblocksEnded = true
}}.
Proof.
unfold removeSubblocksRec. eapply weaken. apply removeSubblocksRecAux. intros s Hprops. simpl.
assert(exists statesList blocksList s0, removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
   /\ blockToRemove = last blocksList blockToRemove
   /\ P s0 /\ consistency s0 /\ In blockToRemove (getMappedBlocks idPDchild s0)).
{ exists []. exists []. exists s. simpl. intuition. }
assert(forall blocksList, checkRemoveOkRec blockToRemove idPDchild blocksList s -> length blocksList < N).
{
  intros blocksList HblocksList. assert(HnoDup: NoDup (blockToRemove::blocksList)).
  {
    destruct Hprops as (_ & Hconsist & _ & HremIsPart & _). apply noDupNextBlocksList with idPDchild s; trivial;
      unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *; intuition.
  }
  apply IL.lengthNoDupPartitions in HnoDup. simpl in *. unfold N. lia.
}
unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *; unfold cons1Free; intuition.
Qed.

Lemma blockInChildHasAtLeastEquivalentBlockInParentPreservedRemoveRec s s0 idPDchild blockToRemove statesList
blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> wellFormedFstShadowIfBlockEntry s0
-> noChildImpliesAddressesNotShared s0
-> blockInChildHasAtLeastEquivalentBlockInParent s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> blockInChildHasAtLeastEquivalentBlockInParent s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint Hwell HwellSh1 HnoChild HequivBlockP HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HequivBlockPA: blockInChildHasAtLeastEquivalentBlockInParent a).
  { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
    intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild
      HendChild HPflagChild. rewrite HgetPartsEqsA in *. assert(HbeqBlocks: blockToRemove <> block).
    {
      intro Hcontra. subst block. unfold bentryPFlag in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      rewrite Hlookups in HPflagChild. simpl in *. congruence.
    }
    assert(HgetChildrenEq: getChildren pdparent a = getChildren pdparent s0).
    { apply getChildrenEqRemove with idPDchild blockToRemove; trivial. }
    rewrite HgetChildrenEq in *. assert(HblockMappedChilds0: In block (getMappedBlocks child s0)).
    {
      destruct (beqAddr idPDchild child) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst child. pose proof (getMappedBlocksEqRemPartRemove blockToRemove
          a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
        destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite Heqs0. rewrite HeqA in *. apply in_or_app.
        apply in_app_or in HblockMappedChild. destruct HblockMappedChild; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *.
        rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a) (removePart:=idPDchild); trivial.
    }
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
    assert(HlookupBlockEq: lookup block (memory a) beqAddr = lookup block (memory s0) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro Hcontra. subst block. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]]. rewrite Hlookups in *.
        congruence.
      - intro Hcontra. subst block. rewrite HSHE in *. congruence.
      - intro Hcontra. subst block. rewrite HSCE in *. congruence.
    }
    rewrite HlookupBlockEq in *. specialize(HequivBlockP pdparent child block startChild endChild HparentIsPart
      HchildIsChild HblockMappedChilds0 HstartChild HendChild HPflagChild).
    destruct HequivBlockP as [blockParent [startParent [endParent (HblockParentMapped & HstartBlockP & HendBlockP &
      HlebStart & HgebEnd)]]]. assert(HbeqBlocksP: blockToRemove <> blockParent).
    {
      intro Hcontra. subst blockParent.
      assert(HlookupParents0: exists pdentry, lookup pdparent (memory s0) beqAddr = Some(PDT pdentry)).
      {
        unfold getMappedBlocks in *. unfold getKSEntries in *.
        destruct (lookup pdparent (memory s0) beqAddr); try(simpl in *; exfalso; congruence).
        destruct v; try(simpl in *; exfalso; congruence). exists p. reflexivity.
      }
      destruct HlookupParents0 as [pdentry HlookupParents0].
      assert(HeqTriv: CPaddr (blockToRemove+sh1offset) = CPaddr (blockToRemove+sh1offset)) by reflexivity.
      specialize(Hwell block startChild endChild HPflagChild HstartChild HendChild). destruct Hwell as (Hwell & _).
      assert(HstartCInP: In startChild (getAllPaddrAux [blockToRemove] s0)).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
        destruct HBE as [bentry0 [_ [_ (HlookupBlocks0 & _)]]]. rewrite HlookupBlocks0 in *. rewrite app_nil_r.
        rewrite <-HstartBlockP. rewrite <-HendBlockP. apply IL.getAllPaddrBlockIncl; lia.
      }
      specialize(HnoChild pdparent pdentry blockToRemove (CPaddr (blockToRemove+sh1offset)) HparentIsPart
        HlookupParents0 HblockParentMapped HeqTriv HPDchild child startChild HchildIsChild HstartCInP).
      apply HnoChild. apply IL.addrInBlockIsMapped with block; trivial. simpl.
      destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      rewrite <-HstartChild. rewrite <-HendChild. rewrite app_nil_r. apply IL.getAllPaddrBlockIncl; lia.
    }
    exists blockParent. exists startParent. exists endParent.
    assert(HlookupBlockPEq: lookup blockParent (memory a) beqAddr = lookup blockParent (memory s0) beqAddr).
    {
      unfold bentryStartAddr in *. apply HlookupsEq; trivial.
      - intro Hcontra. subst blockParent. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
        congruence.
      - intro Hcontra. subst blockParent. unfold isSHE in *.
        destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      - intro Hcontra. subst blockParent. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    }
    rewrite HlookupBlockPEq. split; auto. destruct (beqAddr idPDchild pdparent) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. subst pdparent.
      pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA. rewrite Heqs0 in *. apply in_or_app. apply in_app_or in HblockParentMapped.
      destruct HblockParentMapped as [HmappedLeft | HmappedRest]; auto. right. apply in_app_or in HmappedRest.
      destruct HmappedRest as [Hcontra | Hres]; trivial. simpl in *. destruct Hcontra; exfalso; congruence.
    - rewrite <-beqAddrFalse in *. rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0)
        (removePart:=idPDchild); trivial.
    (* END blockInChildHasAtLeastEquivalentBlockInParent *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoChildA: noChildImpliesAddressesNotShared a).
  {
    apply noChildImpliesAddressesNotSharedPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma originIsParentBlocksStartPreservedRemoveRec s s0 idPDchild blockToRemove statesList
blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> wellFormedFstShadowIfBlockEntry s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
-> originIsParentBlocksStart s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> originIsParentBlocksStart s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint Hwell HwellSh1 HparentOfPart HisChild HnoChild Horigin HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HoriginA: originIsParentBlocksStart a).
  { (* BEGIN originIsParentBlocksStart s *)
    intros part pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce HoriginSce.
    rewrite HgetPartsEqsA in *. assert(HbeqBlocks: blockToRemove <> block).
    {
      intro Hcontra. subst block. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
      rewrite Hlookups in Hlookup. injection Hlookup as HbentriesEq. subst bentry. simpl in *. congruence.
    }
    assert(HlookupParts0: exists pdentrys0, lookup part (memory s0) beqAddr = Some (PDT pdentrys0)
      /\ parent pdentry = parent pdentrys0).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part.
        destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & HlookupA & Hpdentry1)]]. exists pdentry0.
        rewrite HlookupA in HlookupPart. injection HlookupPart as HpdentriesEq. subst pdentry. rewrite Hpdentry1.
        split; auto.
      - rewrite <-beqAddrFalse in *. exists pdentry. split; trivial. rewrite <-HlookupsEq; trivial.
        + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]]. congruence.
        + intro Hcontra. subst part. congruence.
        + intro Hcontra. subst part. congruence.
    }
    destruct HlookupParts0 as [pdentrys0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq.
    assert(HblockMappeds0: In block (getMappedBlocks part s0)).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getMappedBlocksEqRemPartRemove blockToRemove
          a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
        destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite Heqs0. rewrite HeqA in *. apply in_or_app.
        apply in_app_or in HblockMapped. destruct HblockMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *.
        rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a) (removePart:=idPDchild); trivial.
    }
    unfold scentryOrigin in *.
    assert(HlookupSceEq: lookup scentryaddr (memory a) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      apply HlookupsEq.
      - intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _& Hlookups)]]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. rewrite HSHE in *. congruence.
      - subst scentryaddr. intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
        rewrite HcontraBis in *. unfold nullAddrExists in *. unfold isPADDR in *. unfold isSCE in *.
        destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupSceEq in *. specialize(Horigin part pdentrys0 block scentryaddr scorigin HpartIsPart HlookupParts0
      HblockMappeds0 Hsce HoriginSce). destruct Horigin as (HblockPIncl & HlebStarts).
    assert(HlookupBlockEq: lookup block (memory a) beqAddr = lookup block (memory s0) beqAddr).
    {
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
      apply HlookupsEq; trivial.
      - intro Hcontra. subst block. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]]. congruence.
      - intro Hcontra. subst block. congruence.
      - intro Hcontra. subst block. congruence.
    }
    unfold bentryStartAddr. rewrite HlookupBlockEq. split; trivial. intro HbeqPartRoot.
    specialize(HblockPIncl HbeqPartRoot). destruct HblockPIncl as [blockParent (HblockPMapped & HstartP & Hincl)].
    exists blockParent. assert(HbeqBlocksP: blockToRemove <> blockParent).
    {
      intro Hcontra. subst blockParent.
      assert(HlookupParents0: exists pdentry, lookup ((parent pdentrys0)) (memory s0) beqAddr = Some(PDT pdentry)).
      {
        unfold getMappedBlocks in *. unfold getKSEntries in *.
        destruct (lookup (parent pdentrys0) (memory s0) beqAddr); try(simpl in *; exfalso; congruence).
        destruct v; try(simpl in *; exfalso; congruence). exists p. reflexivity.
      }
      destruct HlookupParents0 as [parentEntry HlookupParents0].
      assert(HeqTriv: CPaddr (blockToRemove+sh1offset) = CPaddr (blockToRemove+sh1offset)) by reflexivity.
      assert(Hbounds: exists startaddr endaddr, bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0
        /\ bentryPFlag block true s0).
      {
        apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
        unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryPFlag. rewrite Hlookup.
        exists (startAddr (blockrange bentry)). exists (endAddr (blockrange bentry)). auto.
      }
      destruct Hbounds as [startaddr [endaddr (Hstart & Hend & HPflag)]].
      specialize(Hwell block startaddr endaddr HPflag Hstart Hend). destruct Hwell as (Hwell & _).
      assert(HstartCInP: In startaddr (getAllPaddrAux [blockToRemove] s0)).
      {
        apply Hincl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
        destruct (lookup block (memory s0) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
        rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend. apply IL.getAllPaddrBlockIncl; lia.
      }
      specialize(HparentOfPart part pdentrys0 HlookupParts0). destruct HparentOfPart as (HparentIsPart & _).
      specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as (_ & HparentIsPart).
      assert(Hparent: pdentryParent part (parent pdentrys0) s0).
      { unfold pdentryParent. rewrite HlookupParts0. reflexivity. }
      specialize(HisChild part (parent pdentrys0) HpartIsPart Hparent HbeqPartRoot).
      specialize(HnoChild (parent pdentrys0) parentEntry blockToRemove (CPaddr (blockToRemove+sh1offset))
        HparentIsPart HlookupParents0 HblockPMapped HeqTriv HPDchild part startaddr HisChild HstartCInP).
      apply HnoChild. apply IL.addrInBlockIsMapped with block; trivial. simpl. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    assert(HlookupBlockPEq: lookup blockParent (memory a) beqAddr = lookup blockParent (memory s0) beqAddr).
    {
      unfold bentryStartAddr in *. apply HlookupsEq; trivial.
      - intro Hcontra. subst blockParent. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
        congruence.
      - intro Hcontra. subst blockParent. unfold isSHE in *.
        destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      - intro Hcontra. subst blockParent. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    }
    simpl in *. rewrite HlookupBlockPEq. rewrite HlookupBlockEq. split; auto.
    destruct (beqAddr idPDchild (parent pdentrys0)) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. rewrite <-HbeqParts in *.
      pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA. rewrite Heqs0 in *. apply in_or_app. apply in_app_or in HblockPMapped.
      destruct HblockPMapped as [HmappedLeft | HmappedRest]; auto. right. apply in_app_or in HmappedRest.
      destruct HmappedRest as [Hcontra | Hres]; trivial. simpl in *. destruct Hcontra; exfalso; congruence.
    - rewrite <-beqAddrFalse in *. rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0)
        (removePart:=idPDchild); trivial.
    (* END originIsParentBlocksStart *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoChildA: noChildImpliesAddressesNotShared a).
  {
    apply noChildImpliesAddressesNotSharedPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma nextImpliesBlockWasCutPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> wellFormedFstShadowIfBlockEntry s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
-> nextImpliesBlockWasCut s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> nextImpliesBlockWasCut s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint Hwell HwellSh1 HparentOfPart HisChild HnoChild HnextCut HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HoriginA: nextImpliesBlockWasCut a).
  { (* BEGIN nextImpliesBlockWasCut s *)
    intros part pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped Hend Hsce HbeqSceNull
      HnextSce HbeqPartRoot. rewrite HgetPartsEqsA in *. assert(HbeqBlocks: blockToRemove <> block).
    {
      intro Hcontra. subst block. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
      rewrite Hlookups in Hlookup. injection Hlookup as HbentriesEq. subst bentry. simpl in *. congruence.
    }
    assert(HlookupParts0: exists pdentrys0, lookup part (memory s0) beqAddr = Some (PDT pdentrys0)
      /\ parent pdentry = parent pdentrys0).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part.
        destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & HlookupA & Hpdentry1)]]. exists pdentry0.
        rewrite HlookupA in HlookupPart. injection HlookupPart as HpdentriesEq. subst pdentry. rewrite Hpdentry1.
        split; auto.
      - rewrite <-beqAddrFalse in *. exists pdentry. split; trivial. rewrite <-HlookupsEq; trivial.
        + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]]. congruence.
        + intro Hcontra. subst part. congruence.
        + intro Hcontra. subst part. congruence.
    }
    destruct HlookupParts0 as [pdentrys0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq.
    assert(HblockMappeds0: In block (getMappedBlocks part s0)).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getMappedBlocksEqRemPartRemove blockToRemove
          a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
        destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite Heqs0. rewrite HeqA in *. apply in_or_app.
        apply in_app_or in HblockMapped. destruct HblockMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *.
        rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a) (removePart:=idPDchild); trivial.
    }
    unfold scentryNext in *.
    assert(HlookupSceEq: lookup scentryaddr (memory a) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      apply HlookupsEq.
      - intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _& Hlookups)]]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. rewrite HSHE in *. congruence.
      - subst scentryaddr. intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
        rewrite HcontraBis in *. unfold nullAddrExists in *. unfold isPADDR in *. unfold isSCE in *.
        destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupSceEq in *. unfold bentryEndAddr in *.
    assert(HlookupBlockEq: lookup block (memory a) beqAddr = lookup block (memory s0) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro Hcontra. subst block. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]]. rewrite Hlookups in *.
        congruence.
      - intro Hcontra. subst block. rewrite HSHE in *. congruence.
      - intro Hcontra. subst block. rewrite HSCE in *. congruence.
    }
    rewrite HlookupBlockEq in *.
    specialize(HnextCut part pdentrys0 block scentryaddr scnext endaddr HpartIsPart HlookupParts0 HblockMappeds0 Hend
      Hsce HbeqSceNull HnextSce HbeqPartRoot).
    destruct HnextCut as [blockParent [endP (HblockPMapped & HendP & HltEnds & Hincl)]]. exists blockParent.
    exists endP. assert(HbeqBlocksP: blockToRemove <> blockParent).
    {
      intro Hcontra. subst blockParent.
      assert(HlookupParents0: exists pdentry, lookup ((parent pdentrys0)) (memory s0) beqAddr = Some(PDT pdentry)).
      {
        unfold getMappedBlocks in *. unfold getKSEntries in *.
        destruct (lookup (parent pdentrys0) (memory s0) beqAddr); try(simpl in *; exfalso; congruence).
        destruct v; try(simpl in *; exfalso; congruence). exists p. reflexivity.
      }
      destruct HlookupParents0 as [parentEntry HlookupParents0].
      assert(HeqTriv: CPaddr (blockToRemove+sh1offset) = CPaddr (blockToRemove+sh1offset)) by reflexivity.
      assert(Hbounds: exists startaddr, bentryStartAddr block startaddr s0 /\ bentryPFlag block true s0).
      {
        apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
        unfold bentryStartAddr. unfold bentryPFlag. rewrite Hlookup. exists (startAddr (blockrange bentry)). auto.
      }
      destruct Hbounds as [startaddr (Hstart & HPflag)].
      specialize(Hwell block startaddr endaddr HPflag Hstart Hend). destruct Hwell as (Hwell & _).
      assert(HstartCInP: In startaddr (getAllPaddrAux [blockToRemove] s0)).
      {
        apply Hincl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
        destruct (lookup block (memory s0) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
        rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend. apply IL.getAllPaddrBlockIncl; lia.
      }
      specialize(HparentOfPart part pdentrys0 HlookupParts0). destruct HparentOfPart as (HparentIsPart & _).
      specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as (_ & HparentIsPart).
      assert(Hparent: pdentryParent part (parent pdentrys0) s0).
      { unfold pdentryParent. rewrite HlookupParts0. reflexivity. }
      specialize(HisChild part (parent pdentrys0) HpartIsPart Hparent HbeqPartRoot).
      specialize(HnoChild (parent pdentrys0) parentEntry blockToRemove (CPaddr (blockToRemove+sh1offset))
        HparentIsPart HlookupParents0 HblockPMapped HeqTriv HPDchild part startaddr HisChild HstartCInP).
      apply HnoChild. apply IL.addrInBlockIsMapped with block; trivial. simpl. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    assert(HlookupBlockPEq: lookup blockParent (memory a) beqAddr = lookup blockParent (memory s0) beqAddr).
    {
      unfold bentryEndAddr in *. apply HlookupsEq; trivial.
      - intro Hcontra. subst blockParent. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
        congruence.
      - intro Hcontra. subst blockParent. unfold sh1entryPDflag in *.
        destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      - intro Hcontra. subst blockParent. unfold scentryNext in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    }
    simpl in *. rewrite HlookupBlockPEq. rewrite HlookupBlockEq. split; auto.
    destruct (beqAddr idPDchild (parent pdentrys0)) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. rewrite <-HbeqParts in *.
      pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA. rewrite Heqs0 in *. apply in_or_app. apply in_app_or in HblockPMapped.
      destruct HblockPMapped as [HmappedLeft | HmappedRest]; auto. right. apply in_app_or in HmappedRest.
      destruct HmappedRest as [Hcontra | Hres]; trivial. simpl in *. destruct Hcontra; exfalso; congruence.
    - rewrite <-beqAddrFalse in *. rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0)
        (removePart:=idPDchild); trivial.
    (* END nextImpliesBlockWasCut *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoChildA: noChildImpliesAddressesNotShared a).
  {
    apply noChildImpliesAddressesNotSharedPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma noDupMappedPaddrListPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> noDupMappedPaddrList s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> noDupMappedPaddrList s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup
  HnoDupMapped Hdisjoint HwellSh1 HnoDupPaddr HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HnoDupPaddrA: noDupMappedPaddrList a).
  { (* BEGIN noDupMappedPaddrList s *)
    intros part HpartIsPDT. assert(HpartIsPDTs0: isPDT part s0).
    {
      unfold isPDT in *. destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
        rewrite Hlookups0. trivial.
      - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
        + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
          rewrite Hlookups in *. congruence.
        + intro Hcontra. subst part. rewrite HSHE in *. congruence.
        + intro Hcontra. subst part. rewrite HSCE in *. congruence.
    }
    specialize(HnoDupPaddr part HpartIsPDTs0).
    destruct (beqAddr idPDchild part) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. subst part.
      pose proof (getMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRMapped HBE
        Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA. rewrite Heqs0 in *. apply Lib.NoDupSplitInclIff. apply Lib.NoDupSplitInclIff in HnoDupPaddr.
      destruct HnoDupPaddr as ((HnoDupLeft & HnoDupRest) & HdisjointLeft). apply Lib.NoDupSplitInclIff in HnoDupRest.
      destruct HnoDupRest as ((_ & HnoDupRight) & _). split; auto. intros addr HaddrIn.
      specialize(HdisjointLeft addr HaddrIn). contradict HdisjointLeft. apply in_or_app. auto.
    - rewrite <-beqAddrFalse in *. rewrite getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s0:=s0)
        (removePart:=idPDchild); trivial.
    (* END noDupMappedPaddrList *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma accessibleParentPaddrIsAccessibleIntoChildPreservedRemove s s0 removePart blockToRemove:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> noDupMappedPaddrList s0
-> accessibleParentPaddrIsAccessibleIntoChild s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> bentryAFlag blockToRemove true s0
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> accessibleParentPaddrIsAccessibleIntoChild s.
Proof.
intros HnoDup Hnull HnoDupMapped Hdisjoint HnoDupMappedP Haccess HPDT HBTRMapped HAflagBTR HBE HPDflagBTR HSHE
  HsceIsSCE HSCE HlookupsEq.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold sh1entryPDflag in *. unfold isSHE.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HgetPartsEqs: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
intros part child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
rewrite HgetPartsEqs in *. assert(HgetChildrenEq: getChildren part s = getChildren part s0).
{ apply getChildrenEqRemove with removePart blockToRemove; trivial. }
rewrite HgetChildrenEq in *.
assert(HaddrMappedChilds0: In addr (getMappedPaddr child s0)).
{
  destruct (beqAddr removePart child) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst child.
    pose proof (getMappedPaddrEqRemPartRemove blockToRemove s s0 removePart HnoDup HnoDupMapped HPDT HBTRMapped HBE
      Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
    rewrite HeqA in *. rewrite Heqs0. apply in_app_or in HaddrMappedChild. apply in_or_app.
    destruct HaddrMappedChild; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=s)
      (removePart:=removePart); trivial.
}
assert(HBTRAccMapped: In blockToRemove (getAccessibleMappedBlocks removePart s0)).
{ apply IL.accessibleBlockIsAccessibleMapped; trivial. }
assert(HaddrAccMappedParents0: In addr (getAccessibleMappedPaddr part s0)).
{
  destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getAccessibleMappedPaddrEqRemPartRemove
      blockToRemove s s0 removePart HnoDup HnoDupMapped HPDT HBTRAccMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE
      HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (Heqs & Heqs0)]]. rewrite Heqs in *.
    rewrite Heqs0. apply in_app_or in HaddrAccMappedParent. apply in_or_app. destruct HaddrAccMappedParent; auto.
    right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getAccessibleMappedPaddrEqRemove with (blockToRemove:=blockToRemove)
      (s:=s) (removePart:=removePart); trivial.
}
specialize(Haccess part child addr HparentIsPart HchildIsChild HaddrAccMappedParents0 HaddrMappedChilds0).
destruct (beqAddr removePart child) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. subst child.
  pose proof (getAccessibleMappedPaddrEqRemPartRemove blockToRemove s s0 removePart HnoDup HnoDupMapped HPDT
    HBTRAccMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
  destruct Heqs as [leftList [rightList (Heqs & Heqs0)]].
  rewrite Heqs. rewrite Heqs0 in *. apply in_or_app. apply in_app_or in Haccess.
  destruct Haccess as [HmappedLeft | HmappedRest]; auto. right. apply in_app_or in HmappedRest.
  destruct HmappedRest as [Hcontra | Hres]; trivial. simpl in *. unfold bentryAFlag in *.
  assert(HBEBis: exists bentry0 l newEnd,
    lookup blockToRemove (memory s0) beqAddr = Some (BE bentry0)
    /\ pdentryFirstFreeSlot removePart newEnd s0
    /\ lookup blockToRemove (memory s) beqAddr =
          Some
            (BE
               {|
                 read := false;
                 write := false;
                 exec := false;
                 present := false;
                 accessible := false;
                 blockindex := blockindex bentry0;
                 blockrange := CBlock nullAddr newEnd;
                 Hidx := l
               |})) by assumption.
  destruct HBEBis as [bentry0 [newEnd [l (Hlookups0 & _ & Hlookups)]]]. rewrite Hlookups0 in HAflagBTR. exfalso.
  rewrite Hlookups0 in Hcontra. rewrite <-HAflagBTR in *. assert(HchildIsPDT: isPDT removePart s0).
  { destruct HPDT as [pdentry0 [_ (Hlookup0 & _)]]. unfold isPDT. rewrite Hlookup0. trivial. }
  specialize(HnoDupMappedP removePart HchildIsPDT).
  pose proof (getMappedPaddrEqRemPartRemove blockToRemove s s0 removePart HnoDup HnoDupMapped HPDT HBTRMapped HBE
    Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heq.
  destruct Heq as [leftMapped [rightMapped (HeqMappeds & HeqMappeds0)]]. rewrite HeqMappeds0 in HnoDupMappedP.
  rewrite HeqMappeds in *. apply Lib.NoDupSplitInclIff in HnoDupMappedP.
  destruct HnoDupMappedP as ((_ & HnoDupMappedP) & HdisjointLeft). apply Lib.NoDupSplitInclIff in HnoDupMappedP.
  destruct HnoDupMappedP as (_ & HdisjointRight). contradict HaddrMappedChild. apply Lib.in_or_app_neg.
  apply Lib.disjointPermut in HdisjointLeft. specialize(HdisjointRight addr Hcontra).
  assert(HcontraBis: In addr (getAllPaddrAux [blockToRemove] s0 ++ rightMapped)).
  { apply in_or_app. auto. }
  specialize(HdisjointLeft addr HcontraBis). auto.
- rewrite <-beqAddrFalse in *. rewrite getAccessibleMappedPaddrEqRemove with (blockToRemove:=blockToRemove)
    (s0:=s0) (removePart:=removePart); trivial.
Qed.

Lemma accessibleParentPaddrIsAccessibleIntoChildPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> wellFormedBlock s0
(*-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0*)
-> noDupMappedPaddrList s0
-> accessibleParentPaddrIsAccessibleIntoChild s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> accessibleParentPaddrIsAccessibleIntoChild s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 Hwell (*HparentOfPart HisChild HnoChild*) HnoDupMappedP Haccess HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HoriginA: accessibleParentPaddrIsAccessibleIntoChild a).
  { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
    revert HlookupsEq. apply accessibleParentPaddrIsAccessibleIntoChildPreservedRemove; trivial.
    (* END accessibleParentPaddrIsAccessibleIntoChild *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedPA: noDupMappedPaddrList a).
  {
    apply noDupMappedPaddrListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma sharedBlockPointsToChildPreservedRemove s s0 removePart blockToRemove:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> sharedBlockPointsToChild s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> sharedBlockPointsToChild s.
Proof.
intros HnoDup Hnull HnoDupMapped Hdisjoint Hshared HPDT HBTRMapped HBE HPDflagBTR HSHE HsceIsSCE HSCE HlookupsEq.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold sh1entryPDflag in *. unfold isSHE.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HgetPartsEqs: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild HaddrInBP
  HblockPMapped Hsh1. assert(HbeqBlocksP: blockToRemove <> blockParent).
{
  intro Hcontra. subst blockParent. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
  apply IL.mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
  rewrite Hlookups in Hlookup. injection Hlookup as HbentriesEq. subst bentry. simpl in *. congruence.
}
rewrite HgetPartsEqs in *. assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s0).
{ apply getChildrenEqRemove with removePart blockToRemove; trivial. }
rewrite HgetChildrenEq in *. unfold sh1entryAddr in *. destruct (beqAddr removePart blockParent) eqn:HbeqChildBP.
{
  rewrite <-beqAddrTrue in HbeqChildBP. subst blockParent. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
  rewrite Hlookups in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) blockParent) eqn:HbeqSh1BP.
{
  rewrite <-beqAddrTrue in HbeqSh1BP. subst blockParent. rewrite HSHE in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) blockParent) eqn:HbeqSceBP.
{
  rewrite <-beqAddrTrue in HbeqSceBP. subst blockParent. rewrite HSCE in *. exfalso; congruence.
}
rewrite <-beqAddrFalse in *. rewrite HlookupsEq in Hsh1; trivial.
assert(HaddrUsedChilds0: In addr (getUsedPaddr child  s0)).
{
  unfold getUsedPaddr in *. rewrite getConfigPaddrEqRemove with (blockToRemove:=blockToRemove) (s0:=s0)
    (removePart:=removePart) in HaddrUsedChild; trivial. apply in_app_or in HaddrUsedChild. apply in_or_app.
  destruct HaddrUsedChild as [Hconfig | Hmapped]; auto. right.
  destruct (beqAddr removePart child) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst child.
    pose proof (getMappedPaddrEqRemPartRemove blockToRemove s s0 removePart HnoDup HnoDupMapped HPDT HBTRMapped HBE
      Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (Heqs & Heqs0)]].
    rewrite Heqs in *. rewrite Heqs0. apply in_app_or in Hmapped. apply in_or_app.
    destruct Hmapped; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=s)
      (removePart:=removePart); trivial.
}
assert(HaddrInBPs0: In addr (getAllPaddrAux [blockParent] s0)).
{ simpl in *. rewrite <-HlookupsEq; trivial. }
assert(HblockPMappeds0: In blockParent (getMappedBlocks pdparent s0)).
{
  destruct (beqAddr removePart pdparent) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst pdparent. pose proof (getMappedBlocksEqRemPartRemove blockToRemove
      s s0 removePart HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
    destruct Heqs as [leftList [rightList (Heqs & Heqs0)]]. rewrite Heqs0. rewrite Heqs in *. apply in_or_app.
    apply in_app_or in HblockPMapped. destruct HblockPMapped; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *.
    rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=s) (removePart:=removePart); trivial.
}
specialize(Hshared pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChilds0
  HaddrInBPs0 HblockPMappeds0 Hsh1). unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
assert(Hsh1PIsSHE: isSHE (CPaddr (blockParent+sh1offset)) s0).
{
  unfold isSHE.
  destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr); try(destruct Hshared; congruence).
  destruct v; try(destruct Hshared; congruence). trivial.
}
unfold isSHE in *. destruct (beqAddr removePart (CPaddr (blockParent+sh1offset))) eqn:HbeqPartSh1.
{
  rewrite <-beqAddrTrue in HbeqPartSh1. rewrite <-HbeqPartSh1 in *.
  destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *. exfalso; congruence.
}
destruct (beqAddr blockToRemove (CPaddr (blockParent+sh1offset))) eqn:HbeqBTRSh1.
{
  rewrite <-beqAddrTrue in HbeqBTRSh1. rewrite <-HbeqBTRSh1 in *.
  destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. rewrite Hlookups0 in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) (CPaddr (blockParent+sh1offset))) eqn:HbeqSceSh1.
{
  rewrite <-beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. unfold isSCE in *. exfalso.
  destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) (CPaddr (blockParent+sh1offset))) eqn:HbeqSh1s.
{
  rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; try(exfalso; congruence). intro Hcontra.
  rewrite Hcontra in *. unfold nullAddrExists in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
Qed.

Lemma sharedBlockPointsToChildPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
(*-> wellFormedBlock s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
-> noDupMappedPaddrList s0*)
-> sharedBlockPointsToChild s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> sharedBlockPointsToChild s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 (*Hwell HparentOfPart HisChild HnoChild HnoDupMappedP*) Hshared HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HsharedA: sharedBlockPointsToChild a).
  { (* BEGIN sharedBlockPointsToChild s *)
    revert HlookupsEq. apply sharedBlockPointsToChildPreservedRemove; trivial.
    (* END sharedBlockPointsToChild *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma adressesRangePreservedIfOriginAndNextOkPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> wellFormedBlock s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
(*-> noDupMappedPaddrList s0*)
-> adressesRangePreservedIfOriginAndNextOk s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> adressesRangePreservedIfOriginAndNextOk s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 Hwell HparentOfPart HisChild HnoChild (*HnoDupMappedP*) Hrange HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HsharedA: adressesRangePreservedIfOriginAndNextOk a).
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
    intros part pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped HblockIsBE Hstart Hend HPflag
      Hsce Horigin Hnext HlookupPart HbeqPartRoot. assert(HbeqBlocks: blockToRemove <> block).
    {
      intro Hcontra. subst block. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      unfold bentryPFlag in *. rewrite Hlookups in *. simpl in *. congruence.
    }
    rewrite HgetPartsEqsA in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
    unfold isBE in *. destruct (beqAddr idPDchild block) eqn:HbeqChildBlock.
    {
      rewrite <-beqAddrTrue in HbeqChildBlock. subst block. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
      rewrite HlookupA in *. exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) block) eqn:HbeqSh1Block.
    {
      rewrite <-beqAddrTrue in HbeqSh1Block. subst block. rewrite HSHE in *. exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (blockToRemove+scoffset)) block) eqn:HbeqSceBlock.
    {
      rewrite <-beqAddrTrue in HbeqSceBlock. subst block. rewrite HSCE in *. exfalso; congruence.
    }
    assert(HlookupBlockEq: lookup block (memory a) beqAddr = lookup block (memory s0) beqAddr).
    { rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
    rewrite HlookupBlockEq in *.
    assert(HblockMappeds0: In block (getMappedBlocks part s0)).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part.
        pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in HblockMapped. apply in_or_app.
        destruct HblockMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    unfold scentryNext in *. unfold scentryOrigin in *.
    assert(HlookupSh1Eq: lookup scentryaddr (memory a) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      apply HlookupsEq.
      - intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. congruence.
      - subst scentryaddr. intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
        rewrite HcontraBis in *. unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupSh1Eq in *.
    assert(HlookupParts0: exists pdentrys0, lookup part (memory s0) beqAddr = Some (PDT pdentrys0)
      /\ parent pdentry = parent pdentrys0).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part.
        destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & HlookupA & Hpdentry1)]]. exists pdentry0.
        rewrite HlookupA in HlookupPart. injection HlookupPart as HpdentriesEq. subst pdentry. rewrite Hpdentry1.
        split; auto.
      - rewrite <-beqAddrFalse in *. exists pdentry. split; trivial. rewrite <-HlookupsEq; trivial.
        + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]]. congruence.
        + intro Hcontra. subst part. congruence.
        + intro Hcontra. subst part. congruence.
    }
    destruct HlookupParts0 as [pdentrys0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq.
    specialize(Hrange part pdentrys0 block scentryaddr startaddr endaddr HpartIsPart HblockMappeds0 HblockIsBE Hstart
      Hend HPflag Hsce Horigin Hnext HlookupParts0 HbeqPartRoot).
    destruct Hrange as [blockParent (HblockPMapped & HblockPIsBE & HstartP & HendP)]. exists blockParent.
    assert(HbeqBlocksP: blockToRemove <> blockParent).
    {
      intro Hcontra. subst blockParent.
      assert(HlookupParents0: exists pdentry, lookup ((parent pdentrys0)) (memory s0) beqAddr = Some(PDT pdentry)).
      {
        unfold getMappedBlocks in *. unfold getKSEntries in *.
        destruct (lookup (parent pdentrys0) (memory s0) beqAddr); try(simpl in *; exfalso; congruence).
        destruct v; try(simpl in *; exfalso; congruence). exists p. reflexivity.
      }
      destruct HlookupParents0 as [parentEntry HlookupParents0].
      assert(HeqTriv: CPaddr (blockToRemove+sh1offset) = CPaddr (blockToRemove+sh1offset)) by reflexivity.
      specialize(Hwell block startaddr endaddr HPflag Hstart Hend). destruct Hwell as (Hwell & _).
      assert(HstartCInP: In startaddr (getAllPaddrAux [blockToRemove] s0)).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
        destruct (lookup blockToRemove (memory s0) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence).
        rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendP. apply IL.getAllPaddrBlockIncl; lia.
      }
      specialize(HparentOfPart part pdentrys0 HlookupParts0). destruct HparentOfPart as (HparentIsPart & _).
      specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as (_ & HparentIsPart).
      assert(Hparent: pdentryParent part (parent pdentrys0) s0).
      { unfold pdentryParent. rewrite HlookupParts0. reflexivity. }
      specialize(HisChild part (parent pdentrys0) HpartIsPart Hparent HbeqPartRoot).
      specialize(HnoChild (parent pdentrys0) parentEntry blockToRemove (CPaddr (blockToRemove+sh1offset))
        HparentIsPart HlookupParents0 HblockPMapped HeqTriv HPDchild part startaddr HisChild HstartCInP).
      apply HnoChild. apply IL.addrInBlockIsMapped with block; trivial. simpl. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    assert(HlookupBlockPEq: lookup blockParent (memory a) beqAddr = lookup blockParent (memory s0) beqAddr).
    {
      unfold bentryEndAddr in *. apply HlookupsEq; trivial.
      - intro Hcontra. subst blockParent. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
        congruence.
      - intro Hcontra. subst blockParent. unfold sh1entryPDflag in *.
        destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      - intro Hcontra. subst blockParent. unfold scentryNext in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    }
    simpl in *. rewrite HlookupBlockPEq. split; auto.
    destruct (beqAddr idPDchild (parent pdentrys0)) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. rewrite <-HbeqParts in *.
      pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA. rewrite Heqs0 in *. apply in_or_app. apply in_app_or in HblockPMapped.
      destruct HblockPMapped as [HmappedLeft | HmappedRest]; auto. right. apply in_app_or in HmappedRest.
      destruct HmappedRest as [Hcontra | Hres]; trivial. simpl in *. destruct Hcontra; exfalso; congruence.
    - rewrite <-beqAddrFalse in *. rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0)
        (removePart:=idPDchild); trivial.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoChildA: noChildImpliesAddressesNotShared a).
  {
    apply noChildImpliesAddressesNotSharedPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma childsBlocksPropsInParentPreservedRemove s s0 removePart blockToRemove:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> childsBlocksPropsInParent s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> childsBlocksPropsInParent s.
Proof.
intros HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 HchildBlockProps HPDT HBTRMapped HBE HPDflagBTR HSHE HsceIsSCE
  HSCE HlookupsEq.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold sh1entryPDflag in *. unfold isSHE.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HgetPartsEqs: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart HchildIsChild
  HblockCMapped HstartC HendC HPflagC HblockPMapped HstartP HendP HPflagP HlebStarts HgebEnds.
assert(HbeqBlocksC: blockToRemove <> blockChild).
{
  intro Hcontra. subst blockChild. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
  unfold bentryPFlag in *. rewrite Hlookups in *. simpl in *. congruence.
}
assert(HbeqBlocksP: blockToRemove <> blockParent).
{
  intro Hcontra. subst blockParent. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
  unfold bentryPFlag in *. rewrite Hlookups in *. simpl in *. congruence.
}
rewrite HgetPartsEqs in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
destruct (beqAddr removePart blockChild) eqn:HbeqChildBlockC.
{
  rewrite <-beqAddrTrue in HbeqChildBlockC. subst blockChild. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
  rewrite HlookupA in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) blockChild) eqn:HbeqSh1BlockC.
{
  rewrite <-beqAddrTrue in HbeqSh1BlockC. subst blockChild. rewrite HSHE in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) blockChild) eqn:HbeqSceBlockC.
{
  rewrite <-beqAddrTrue in HbeqSceBlockC. subst blockChild. rewrite HSCE in *. exfalso; congruence.
}
destruct (beqAddr removePart blockParent) eqn:HbeqChildBlockP.
{
  rewrite <-beqAddrTrue in HbeqChildBlockP. subst blockParent. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
  rewrite HlookupA in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) blockParent) eqn:HbeqSh1BlockP.
{
  rewrite <-beqAddrTrue in HbeqSh1BlockP. subst blockParent. rewrite HSHE in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) blockParent) eqn:HbeqSceBlockP.
{
  rewrite <-beqAddrTrue in HbeqSceBlockP. subst blockParent. rewrite HSCE in *. exfalso; congruence.
}
assert(HlookupBlockCEq: lookup blockChild (memory s) beqAddr = lookup blockChild (memory s0) beqAddr).
{ rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
{ rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
rewrite HlookupBlockCEq in *. rewrite HlookupBlockPEq in *.
assert(HblockCMappeds0: In blockChild (getMappedBlocks child s0)).
{
  destruct (beqAddr removePart child) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst child.
    pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0 removePart HnoDup HPDT HBTRMapped HBE
      Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (Heqs & Heqs0)]].
    rewrite Heqs in *. rewrite Heqs0. apply in_app_or in HblockCMapped. apply in_or_app.
    destruct HblockCMapped; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=s)
      (removePart:=removePart); trivial.
}
assert(HblockPMappeds0: In blockParent (getMappedBlocks pdparent s0)).
{
  destruct (beqAddr removePart pdparent) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst pdparent.
    pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0 removePart HnoDup HPDT HBTRMapped HBE
      Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (Heqs & Heqs0)]].
    rewrite Heqs in *. rewrite Heqs0. apply in_app_or in HblockPMapped. apply in_or_app.
    destruct HblockPMapped; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=s)
      (removePart:=removePart); trivial.
}
assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s0).
{ apply getChildrenEqRemove with removePart blockToRemove; trivial. }
rewrite HgetChildrenEq in *.
specialize(HchildBlockProps child pdparent blockChild startChild endChild blockParent startParent endParent
  HparentIsPart HchildIsChild HblockCMappeds0 HstartC HendC HPflagC HblockPMappeds0 HstartP HendP HPflagP
  HlebStarts HgebEnds).
destruct HchildBlockProps as (HcheckChild & HPDchildNotNull & HchildLocNotNull & HaccIfBounds).
assert(HlookupSh1Eq: lookup (CPaddr (blockParent+sh1offset)) (memory s) beqAddr
  = lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr).
{
  assert(HblockPIsBE: isBE blockParent s0).
  {
    unfold isBE. destruct (lookup blockParent (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  specialize(HwellSh1 blockParent HblockPIsBE). unfold isSHE in *. apply HlookupsEq.
  - intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
    rewrite Hlookups0 in *. congruence.
  - intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]].
    rewrite Hlookups0 in *. congruence.
  - intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
    unfold nullAddrExists in *. unfold isPADDR in *.
    destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  - intro Hcontra. rewrite <-Hcontra in *. unfold isSCE in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
}
unfold checkChild. unfold sh1entryPDchild. unfold sh1entryInChildLocation in *. unfold bentryAFlag.
rewrite HlookupSh1Eq. rewrite HlookupBlockPEq. split; trivial. split; trivial. split; trivial.
intros blockIDInChild HchildLocP. apply HchildLocNotNull.
destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr); try(congruence).
destruct v; try(congruence). destruct HchildLocP as (HchildLocP & HchildLocPNotNull). split; trivial.
intro HbeqLocNull. specialize(HchildLocPNotNull HbeqLocNull). unfold isBE in *.
destruct (beqAddr blockToRemove blockIDInChild) eqn:HbeqBTRLoc.
- rewrite <-beqAddrTrue in HbeqBTRLoc. rewrite HbeqBTRLoc in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]].
  rewrite Hlookups0. trivial.
- rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
  + intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
    rewrite HlookupA in *. congruence.
  + intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. congruence.
  + intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
Qed.

Lemma childsBlocksPropsInParentPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
(*-> wellFormedBlock s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
-> noDupMappedPaddrList s0*)
-> childsBlocksPropsInParent s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> childsBlocksPropsInParent s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 (*Hwell HparentOfPart HisChild HnoChild HnoDupMappedP*) HchildBlockProps HblocksList
  Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HchildBlockPropsA: childsBlocksPropsInParent a).
  { (* BEGIN childsBlocksPropsInParent s *)
    revert HlookupsEq. apply childsBlocksPropsInParentPreservedRemove; trivial.
    (* END childsBlocksPropsInParent *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma noChildImpliesAddressesNotSharedPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
(*-> wellFormedBlock s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
-> noDupMappedPaddrList s0*)
-> noChildImpliesAddressesNotShared s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> noChildImpliesAddressesNotShared s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 (*Hwell HparentOfPart HisChild HnoChild HnoDupMappedP*) HnoChild HblocksList
  Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HnoChildA: noChildImpliesAddressesNotShared a).
  { (* BEGIN noChildImpliesAddressesNotShared s *)
    apply noChildImpliesAddressesNotSharedPreservedRemove with s0 idPDchild blockToRemove; trivial.
    (* END noChildImpliesAddressesNotShared *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma kernelsAreNotAccessiblePreservedRemove s s0 removePart blockToRemove:
kernelsAreNotAccessible s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove + sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> kernelsAreNotAccessible s.
Proof.
intros HkernNotAcc HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq.
intros block startaddr Hstart HPflag HstartIsKS. unfold bentryPFlag in *.
assert(HbeqBlocks: blockToRemove <> block).
{
  intro Hcontra. subst block. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
  unfold bentryPFlag in *. rewrite Hlookups in *. simpl in *. congruence.
}
unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryAFlag.
destruct (beqAddr removePart block) eqn:HbeqChildBlock.
{
  rewrite <-beqAddrTrue in HbeqChildBlock. subst block. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
  rewrite HlookupA in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) block) eqn:HbeqSh1Block.
{
  rewrite <-beqAddrTrue in HbeqSh1Block. subst block. rewrite HSHE in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) block) eqn:HbeqSceBlock.
{
  rewrite <-beqAddrTrue in HbeqSceBlock. subst block. rewrite HSCE in *. exfalso; congruence.
}
assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{ rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
rewrite HlookupBlockEq in *. assert(HstartIsKSs0: isKS startaddr s0).
{
  unfold isKS in *. destruct (beqAddr blockToRemove startaddr) eqn:HbeqBTRStart.
  - rewrite <-beqAddrTrue in HbeqBTRStart. subst startaddr.
    destruct HBE as [bentry0 [newEnd [l (Hlookups0 & _ & Hlookups)]]]. rewrite Hlookups in *. rewrite Hlookups0.
    auto.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
    + intro Hcontra. subst startaddr. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]]. rewrite HlookupA in *.
      congruence.
    + intro Hcontra. subst startaddr. rewrite HSHE in *. congruence.
    + intro Hcontra. subst startaddr. rewrite HSCE in *. congruence.
}
specialize(HkernNotAcc block startaddr Hstart HPflag HstartIsKSs0). assumption.
Qed.

Lemma kernelsAreNotAccessiblePreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
kernelsAreNotAccessible s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> kernelsAreNotAccessible s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList
  HkernNotAcc HblocksList.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HkernNotAccA: kernelsAreNotAccessible a).
  { (* BEGIN kernelsAreNotAccessible s *)
    revert HlookupsEq. apply kernelsAreNotAccessiblePreservedRemove; trivial.
    (* END kernelsAreNotAccessible *)
  }
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma blockAndNextAreSideBySidePreservedRemove s s0 removePart blockToRemove:
blockAndNextAreSideBySide s0
-> noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> (forall part block scnext, In part (getPartitions multiplexer s0)
      -> In block (getMappedBlocks part s0)
      -> scentryNext (CPaddr (block+scoffset)) scnext s0
       -> scnext <> nullAddr
      -> blockToRemove <> scnext)
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> blockAndNextAreSideBySide s.
Proof.
intros HnextBlockSide HnoDup Hnull HnoDupMapped Hdisjoint HBTRNotNext HPDT HBTRMapped HBE HPDflagBTR HSHE HsceIsSCE
  HSCE HlookupsEq part block scentryaddr scnext endaddr HpartIsPart HblockMapped Hend Hsce HbeqNextNull Hnext.
assert(HbeqBlocksC: blockToRemove <> block).
{
  intro Hcontra. subst block. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
  apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBis & Hpres)].
  rewrite Hlookups in *. injection HlookupBis as HbentriesEq. subst bentry. simpl in *. congruence.
}
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold sh1entryPDflag in *. unfold isSHE.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
rewrite HgetPartsEq in *. unfold bentryEndAddr in *.
destruct (beqAddr removePart block) eqn:HbeqChildBlock.
{
  rewrite <-beqAddrTrue in HbeqChildBlock. subst block. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
  rewrite HlookupA in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) block) eqn:HbeqSh1Block.
{
  rewrite <-beqAddrTrue in HbeqSh1Block. subst block. rewrite HSHE in *. exfalso; congruence.
}
destruct (beqAddr (CPaddr (blockToRemove+scoffset)) block) eqn:HbeqSceBlock.
{
  rewrite <-beqAddrTrue in HbeqSceBlock. subst block. rewrite HSCE in *. exfalso; congruence.
}
assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{ rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
rewrite HlookupBlockEq in *.
assert(HblockMappeds0: In block (getMappedBlocks part s0)).
{
  destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part.
    pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0 removePart HnoDup HPDT HBTRMapped HBE
      Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
    rewrite HeqA in *. rewrite Heqs0. apply in_app_or in HblockMapped. apply in_or_app.
    destruct HblockMapped; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=s)
      (removePart:=removePart); trivial.
}
unfold scentryNext in *.
assert(HlookupSceEq: lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s0) beqAddr).
{
  apply HlookupsEq.
  - intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
    rewrite Hlookups in *. congruence.
  - intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
    rewrite Hlookups in *. congruence.
  - intro Hcontra. rewrite <-Hcontra in *. rewrite HSHE in *. congruence.
  - intro Hcontra. rewrite <-Hcontra in *. rewrite HSCE in *. simpl in *. congruence.
}
rewrite HlookupSceEq in *.
specialize(HnextBlockSide part block scentryaddr scnext endaddr HpartIsPart HblockMappeds0 Hend Hsce HbeqNextNull
  Hnext). destruct HnextBlockSide as (Hstart & HnextMapped). rewrite Hsce in Hnext.
specialize(HBTRNotNext part block scnext HpartIsPart HblockMappeds0 Hnext HbeqNextNull). split.
- unfold bentryStartAddr in *. rewrite HlookupsEq; trivial.
  + intro Hcontra. subst scnext. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
    congruence.
  + intro Hcontra. subst scnext. unfold isSHE in *.
    destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
  + intro Hcontra. subst scnext. unfold isSCE in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
- destruct (beqAddr removePart part) eqn:HbeqParts.
  + rewrite <-beqAddrTrue in HbeqParts. subst part.
    pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0 removePart HnoDup HPDT HBTRMapped HBE
      Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
    rewrite HeqA. rewrite Heqs0 in *. apply in_app_or in HnextMapped. apply in_or_app.
    destruct HnextMapped as [Hleft | Hright]; auto. right. apply in_app_or in Hright. simpl in *.
    destruct Hright as [Hcontra | Hright]; trivial. exfalso. destruct Hcontra; congruence.
  + rewrite <-beqAddrFalse in *. rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0)
      (removePart:=removePart); trivial.
Qed.

Lemma blockAndNextAreSideBySidePreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> wellFormedBlock s0
(*-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0*)
-> noDupMappedPaddrList s0
-> blockAndNextAreSideBySide s0
-> (forall part block scnext, In part (getPartitions multiplexer s0)
      -> In block (getMappedBlocks part s0)
      -> scentryNext (CPaddr (block+scoffset)) scnext s0
       -> scnext <> nullAddr
      -> blockToRemove <> scnext) (*TODO that will probably be a pain to prove*)
-> In idPDchild (getPartitions multiplexer s0)
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
(*-> nullAddr = last blocksList blockToRemove*)
-> blockAndNextAreSideBySide s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 Hwell (*HparentOfPart HisChild HnoChild*) HnoDupMappedP HnextBlockSide HBTRNotNext
  HchildIsPart HblocksList (*Hlast*).
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HnextNotNext: forall part block scnext, In part (getPartitions multiplexer a)
    -> In block (getMappedBlocks part a) -> scentryNext (CPaddr (block + scoffset)) scnext a
    -> scnext <> nullAddr -> nextBlock <> scnext).
  {
    intros part block scnext HpartIsPart HblockMapped Hnext HbeqNextNull HbeqNextBTRNext. subst scnext.
    assert(HblockMappeds0: In block (getMappedBlocks part s0)).
    {
      pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as HeqChilds.
      destruct HeqChilds as [leftChild [rightChild (HchildA & Hchilds0)]].
      pose proof (getMappedBlocksEqRemove blockToRemove a s0 idPDchild part Hdisjoint HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. rewrite Hchilds0. rewrite HchildA in *.
        apply in_app_or in HblockMapped. apply in_or_app. destruct HblockMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. specialize(Heqs HbeqParts). rewrite <-Heqs. assumption.
    }
    unfold scentryNext in *. rewrite HgetPartsEqsA in *. assert(HbeqChildSce: idPDchild <> (CPaddr (block+scoffset))).
    {
      intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
      rewrite Hlookups in *. congruence.
    }
    assert(HbeqBTRSce: blockToRemove <> (CPaddr (block+scoffset))).
    {
      intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      rewrite Hlookups in *. congruence.
    }
    assert(HbeqSh1Sce: CPaddr (blockToRemove+sh1offset) <> CPaddr (block+scoffset)).
    { intro Hcontra. rewrite <-Hcontra in *. rewrite HSHE in *. congruence. }
    assert(HbeqSces: CPaddr (blockToRemove+scoffset) <> CPaddr (block+scoffset)).
    { intro Hcontra. rewrite <-Hcontra in *. rewrite HSCE in *. simpl in *. congruence. }
    rewrite HlookupsEq in Hnext; trivial.
    assert(Hsce: CPaddr (block+scoffset) = CPaddr (block+scoffset)) by reflexivity.
    assert(Hbounds: (exists startaddr endaddr, bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0)
      /\ bentryPFlag block true s0).
    {
      apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. unfold bentryEndAddr. unfold bentryStartAddr. rewrite Hlookup. split; auto.
      exists (startAddr (blockrange bentry)). exists (endAddr (blockrange bentry)). split; trivial.
    }
    destruct Hbounds as ([startaddr [endaddr (Hstart & Hend)]] & HPflag).
    assert(HnextBlockSideCopy: blockAndNextAreSideBySide s0) by assumption.
    specialize(HnextBlockSide part block (CPaddr (block+scoffset)) nextBlock endaddr HpartIsPart HblockMappeds0
      Hend Hsce HbeqNextNull Hnext). destruct HnextBlockSide as (HstartNext & HnextMappedPart).
    assert(HboundsBTR: exists startBTR endBTR, bentryStartAddr blockToRemove startBTR s0
      /\ bentryEndAddr blockToRemove endBTR s0).
    {
      destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. unfold bentryEndAddr. unfold bentryStartAddr.
      rewrite Hlookups0. exists (startAddr (blockrange bentry0)). exists (endAddr (blockrange bentry0)).
      split; trivial.
    }
    destruct HboundsBTR as [startBTR [endBTR (HstartBTR & HendBTR)]].
    assert(HsceBTR: CPaddr (blockToRemove+scoffset) = CPaddr (blockToRemove+scoffset)) by reflexivity.
    specialize(HnextBlockSideCopy idPDchild blockToRemove (CPaddr (blockToRemove+scoffset)) nextBlock endBTR
      HchildIsPart HBTRMapped HendBTR HsceBTR HbeqNextNull HnextBTR).
    destruct HnextBlockSideCopy as (HstartNextBis & HnextMappedChild). unfold bentryStartAddr in *.
    destruct (lookup nextBlock (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    rewrite <-HstartNext in *. subst endBTR. assert(HPflagBTR: bentryPFlag blockToRemove true s0).
    {
      apply IL.mappedBlockIsBE in HBTRMapped. destruct HBTRMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(HwellCopy: wellFormedBlock s0) by assumption. specialize(Hwell block startaddr endaddr HPflag Hstart Hend).
    specialize(HwellCopy blockToRemove startBTR endaddr HPflagBTR HstartBTR HendBTR). destruct Hwell as (Hwell & _).
    destruct HwellCopy as (HwellBTR & _). assert(HchildIsPDT: isPDT idPDchild s0).
    { destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. unfold isPDT. rewrite Hlookups0. trivial. }
    assert(part = idPDchild).
    {
      destruct (beqAddr part idPDchild) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
      rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HnextMappedPart.
      apply InFilterPresentInList in HnextMappedChild. assert(HpartIsPDT: isPDT part s0).
      {
        unfold isPDT. unfold getKSEntries in *.
        destruct (lookup part (memory s0) beqAddr); try(simpl in *; congruence).
        destruct v; try(simpl in *; congruence). trivial.
      }
      specialize(Hdisjoint part idPDchild HpartIsPDT HchildIsPDT HbeqParts).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      specialize(Hdisjoint nextBlock HnextMappedPart). congruence.
    }
    subst part.
    assert(HbeqBlocks: blockToRemove = block).
    {
      destruct (beqAddr blockToRemove block) eqn:HbeqBlocks; try(rewrite beqAddrTrue; trivial). exfalso.
      rewrite <-beqAddrFalse in *. assert(HendIsValid: p (CPaddr (endaddr-1)) = endaddr-1).
      {
        unfold CPaddr. assert(endaddr <= maxAddr) by (apply Hp).
        destruct (le_dec (endaddr - 1) maxAddr); try(lia). reflexivity.
      }
      assert(HendInBTR: In (CPaddr (endaddr-1)) (getAllPaddrAux [blockToRemove] s0)).
      {
        simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        destruct (lookup blockToRemove (memory s0) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence). rewrite <-HstartBTR. rewrite <-HendBTR. rewrite app_nil_r.
        apply IL.getAllPaddrBlockIncl; lia.
      }
      pose proof (DisjointPaddrInPart idPDchild blockToRemove block (CPaddr (endaddr-1)) s0 HnoDupMappedP
        HchildIsPDT HBTRMapped HblockMappeds0 HbeqBlocks HendInBTR) as HendNotInBlock. apply HendNotInBlock. simpl.
      unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
      destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    subst block. congruence.
  }
  assert(HnextBlockSideA: blockAndNextAreSideBySide a).
  { (* BEGIN blockAndNextAreSideBySide s *)
    intros part block scentryaddr scnext endaddr HpartIsPart HblockMapped Hend Hsce HbeqNextNull Hnext.
    assert(HbeqBlocksC: blockToRemove <> block).
    {
      intro Hcontra. subst block. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBis & Hpres)].
      rewrite Hlookups in *. injection HlookupBis as HbentriesEq. subst bentry. simpl in *. congruence.
    }
    rewrite HgetPartsEqsA in *. unfold bentryEndAddr in *.
    destruct (beqAddr idPDchild block) eqn:HbeqChildBlock.
    {
      rewrite <-beqAddrTrue in HbeqChildBlock. subst block. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
      rewrite HlookupA in *. exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) block) eqn:HbeqSh1Block.
    {
      rewrite <-beqAddrTrue in HbeqSh1Block. subst block. rewrite HSHE in *. exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (blockToRemove+scoffset)) block) eqn:HbeqSceBlock.
    {
      rewrite <-beqAddrTrue in HbeqSceBlock. subst block. rewrite HSCE in *. exfalso; congruence.
    }
    assert(HlookupBlockEq: lookup block (memory a) beqAddr = lookup block (memory s0) beqAddr).
    { rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
    rewrite HlookupBlockEq in *.
    assert(HblockMappeds0: In block (getMappedBlocks part s0)).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part.
        pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in HblockMapped. apply in_or_app.
        destruct HblockMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    unfold scentryNext in *.
    assert(HlookupSceEq: lookup scentryaddr (memory a) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      apply HlookupsEq.
      - intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. rewrite HSHE in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. rewrite HSCE in *. simpl in *. congruence.
    }
    rewrite HlookupSceEq in *.
    specialize(HnextBlockSide part block scentryaddr scnext endaddr HpartIsPart HblockMappeds0 Hend Hsce HbeqNextNull
      Hnext). destruct HnextBlockSide as (Hstart & HnextMapped). rewrite Hsce in Hnext.
    specialize(HBTRNotNext part block scnext HpartIsPart HblockMappeds0 Hnext HbeqNextNull). split.
    - unfold bentryStartAddr in *. rewrite HlookupsEq; trivial.
      + intro Hcontra. subst scnext. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
        congruence.
      + intro Hcontra. subst scnext. unfold isSHE in *.
        destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      + intro Hcontra. subst scnext. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    - destruct (beqAddr idPDchild part) eqn:HbeqParts.
      + rewrite <-beqAddrTrue in HbeqParts. subst part.
        pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA. rewrite Heqs0 in *. apply in_app_or in HnextMapped. apply in_or_app.
        destruct HnextMapped as [Hleft | Hright]; auto. right. apply in_app_or in Hright. simpl in *.
        destruct Hright as [Hcontra | Hright]; trivial. exfalso. destruct Hcontra; congruence.
      + rewrite <-beqAddrFalse in *. rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0)
          (removePart:=idPDchild); trivial.
    (* END blockAndNextAreSideBySide *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedPA: noDupMappedPaddrList a).
  {
    apply noDupMappedPaddrListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  (*rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.*) rewrite <-HgetPartsEqsA in *.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma parentBlocksBoundsIfNoNextPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> wellFormedBlock s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
(*-> noDupMappedPaddrList s0*)
-> parentBlocksBoundsIfNoNext s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> parentBlocksBoundsIfNoNext s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 Hwell HparentOfPart HisChild HnoChild (*HnoDupMappedP*) HparentBounds HblocksList
  Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HparentBoundsA: parentBlocksBoundsIfNoNext a).
  { (* BEGIN parentBlocksBoundsIfNoNext s *)
    intros part pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped Hstart Hend Hsce Hnext
      HbeqPartRoot HlookupPart.
    assert(HbeqBlocks: blockToRemove <> block).
    {
      intro Hcontra. subst block. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBis & Hpres)].
      rewrite Hlookups in *. injection HlookupBis as HbentriesEq. subst bentry. simpl in *. congruence.
    }
    rewrite HgetPartsEqsA in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    destruct (beqAddr idPDchild block) eqn:HbeqChildBlock.
    {
      rewrite <-beqAddrTrue in HbeqChildBlock. subst block. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
      rewrite HlookupA in *. exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) block) eqn:HbeqSh1Block.
    {
      rewrite <-beqAddrTrue in HbeqSh1Block. subst block. rewrite HSHE in *. exfalso; congruence.
    }
    destruct (beqAddr (CPaddr (blockToRemove+scoffset)) block) eqn:HbeqSceBlock.
    {
      rewrite <-beqAddrTrue in HbeqSceBlock. subst block. rewrite HSCE in *. exfalso; congruence.
    }
    assert(HlookupBlockEq: lookup block (memory a) beqAddr = lookup block (memory s0) beqAddr).
    { rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
    rewrite HlookupBlockEq in *.
    assert(HblockMappeds0: In block (getMappedBlocks part s0)).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part.
        pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in HblockMapped. apply in_or_app.
        destruct HblockMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    unfold scentryNext in *.
    assert(HlookupSceEq: lookup scentryaddr (memory a) beqAddr = lookup scentryaddr (memory s0) beqAddr).
    {
      apply HlookupsEq.
      - intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
        rewrite HlookupA in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & HlookupA)]]].
        rewrite HlookupA in *. congruence.
      - intro Hcontra. rewrite <-Hcontra in *. rewrite HSHE in *. congruence.
      - subst scentryaddr. intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
        rewrite HcontraBis in *. unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupSceEq in *.
    assert(HlookupParts0: exists pdentrys0, lookup part (memory s0) beqAddr = Some (PDT pdentrys0)
      /\ parent pdentry = parent pdentrys0).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part.
        destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & HlookupA & Hpdentry1)]]. exists pdentry0.
        rewrite HlookupA in HlookupPart. injection HlookupPart as HpdentriesEq. subst pdentry. rewrite Hpdentry1.
        split; auto.
      - rewrite <-beqAddrFalse in *. exists pdentry. split; trivial. rewrite <-HlookupsEq; trivial.
        + intro Hcontra. subst part. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]]. congruence.
        + intro Hcontra. subst part. congruence.
        + intro Hcontra. subst part. congruence.
    }
    destruct HlookupParts0 as [pdentrys0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq.
    specialize(HparentBounds part pdentrys0 block scentryaddr startaddr endaddr HpartIsPart HblockMappeds0 Hstart Hend
      Hsce Hnext HbeqPartRoot HlookupParts0).
    destruct HparentBounds as [blockParent [startP (HblockPMapped & HstartP & HendP & HlebStarts)]].
    exists blockParent. exists startP. assert(HPflag: bentryPFlag block true s0).
    {
      apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(HbeqBlocksP: blockToRemove <> blockParent).
    {
      intro Hcontra. subst blockParent.
      assert(HlookupParents0: exists pdentry, lookup ((parent pdentrys0)) (memory s0) beqAddr = Some(PDT pdentry)).
      {
        unfold getMappedBlocks in *. unfold getKSEntries in *.
        destruct (lookup (parent pdentrys0) (memory s0) beqAddr); try(simpl in *; exfalso; congruence).
        destruct v; try(simpl in *; exfalso; congruence). exists p. reflexivity.
      }
      destruct HlookupParents0 as [parentEntry HlookupParents0].
      assert(HeqTriv: CPaddr (blockToRemove+sh1offset) = CPaddr (blockToRemove+sh1offset)) by reflexivity.
      specialize(Hwell block startaddr endaddr HPflag Hstart Hend). destruct Hwell as (Hwell & _).
      assert(HstartCInP: In startaddr (getAllPaddrAux [blockToRemove] s0)).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
        destruct (lookup blockToRemove (memory s0) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence).
        rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendP. apply IL.getAllPaddrBlockIncl; lia.
      }
      specialize(HparentOfPart part pdentrys0 HlookupParts0). destruct HparentOfPart as (HparentIsPart & _).
      specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as (_ & HparentIsPart).
      assert(Hparent: pdentryParent part (parent pdentrys0) s0).
      { unfold pdentryParent. rewrite HlookupParts0. reflexivity. }
      specialize(HisChild part (parent pdentrys0) HpartIsPart Hparent HbeqPartRoot).
      specialize(HnoChild (parent pdentrys0) parentEntry blockToRemove (CPaddr (blockToRemove+sh1offset))
        HparentIsPart HlookupParents0 HblockPMapped HeqTriv HPDchild part startaddr HisChild HstartCInP).
      apply HnoChild. apply IL.addrInBlockIsMapped with block; trivial. simpl. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    assert(HlookupBlockPEq: lookup blockParent (memory a) beqAddr = lookup blockParent (memory s0) beqAddr).
    {
      unfold bentryEndAddr in *. apply HlookupsEq; trivial.
      - intro Hcontra. subst blockParent. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
        congruence.
      - intro Hcontra. subst blockParent. unfold sh1entryPDflag in *.
        destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      - intro Hcontra. subst blockParent. unfold scentryNext in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    }
    rewrite HlookupBlockPEq. split; auto.
    destruct (beqAddr idPDchild (parent pdentrys0)) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. rewrite <-HbeqParts in *.
      pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA. rewrite Heqs0 in *. apply in_or_app. apply in_app_or in HblockPMapped.
      destruct HblockPMapped as [HmappedLeft | HmappedRest]; auto. right. apply in_app_or in HmappedRest.
      destruct HmappedRest as [Hcontra | Hres]; trivial. simpl in *. destruct Hcontra; exfalso; congruence.
    - rewrite <-beqAddrFalse in *. rewrite getMappedBlocksEqRemove with (block:=blockToRemove) (s0:=s0)
        (removePart:=idPDchild); trivial.
    (* END parentBlocksBoundsIfNoNext *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellA: wellFormedBlock a).
  {
    apply wellFormedBlockPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HparentOfPartA: parentOfPartitionIsPartition a).
  {
    apply parentOfPartitionIsPartitionPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HisChildA: isChild a).
  {
    apply isChildPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoChildA: noChildImpliesAddressesNotShared a).
  {
    apply noChildImpliesAddressesNotSharedPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma partitionsIsolationPreservedRemove s s0 removePart blockToRemove:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> partitionsIsolation s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> partitionsIsolation s.
Proof.
intros HnoDup Hnull HnoDupMapped Hdisjoint HPI HPDT HBTRMapped HBE HPDflagBTR HSHE HsceIsSCE HSCE HlookupsEq.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold sh1entryPDflag in *. unfold isSHE.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HgetPartsEqsA: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren addr HaddrUsed1.
rewrite HgetPartsEqsA in *. assert(HgetChildrenEq: getChildren pdparent s = getChildren pdparent s0).
{ apply getChildrenEqRemove with removePart blockToRemove; trivial. }
rewrite HgetChildrenEq in *. assert(HaddrUsed1s0: In addr (getUsedPaddr child1 s0)).
{
  unfold getUsedPaddr in *. apply in_or_app. apply in_app_or in HaddrUsed1.
  rewrite <-getConfigPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=s) (removePart:=removePart); trivial.
  destruct HaddrUsed1 as [Hconfig | Hmapped]; auto. right. destruct (beqAddr removePart child1) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst child1.
    pose proof (getMappedPaddrEqRemPartRemove blockToRemove s s0 removePart HnoDup HnoDupMapped HPDT HBTRMapped HBE
      Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
    rewrite HeqA in *. rewrite Heqs0. apply in_app_or in Hmapped. apply in_or_app.
    destruct Hmapped; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=s)
      (removePart:=removePart); trivial.
}
specialize(HPI pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren addr HaddrUsed1s0).
contradict HPI. unfold getUsedPaddr in *. apply in_or_app. apply in_app_or in HPI.
rewrite <-getConfigPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=s) (removePart:=removePart); trivial.
destruct HPI as [Hconfig | Hmapped]; auto. right. destruct (beqAddr removePart child2) eqn:HbeqParts.
- rewrite <-beqAddrTrue in HbeqParts. subst child2.
  pose proof (getMappedPaddrEqRemPartRemove blockToRemove s s0 removePart HnoDup HnoDupMapped HPDT HBTRMapped HBE
    Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
  rewrite HeqA in *. rewrite Heqs0. apply in_app_or in Hmapped. apply in_or_app.
  destruct Hmapped; auto. right. apply in_or_app. auto.
- rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=s)
    (removePart:=removePart); trivial.
Qed.

Lemma partitionsIsolationPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> partitionsIsolation s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> partitionsIsolation s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 HPI HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HPIA: partitionsIsolation a).
  { (* BEGIN partitionsIsolation s *)
    revert HlookupsEq. apply partitionsIsolationPreservedRemove; trivial.
    (* END partitionsIsolation *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma kernelDataIsolationPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> kernelDataIsolation s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> kernelDataIsolation s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 HKDI HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HKDIA: kernelDataIsolation a).
  { (* BEGIN kernelDataIsolation s *)
    apply kernelDataIsolationPreservedRemove with (blockToRemove:=blockToRemove) (s0:=s0) (removePart:=idPDchild);
      trivial.
    (* END kernelDataIsolation *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma verticalSharingPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> noDupPartitionTree s0
-> noChildImpliesAddressesNotShared s0
-> kernelDataIsolation s0
-> verticalSharing s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> verticalSharing s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 HnoDupTree HnoChild HKDI HVS HblocksList Hlast.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [nextBlock [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBTR & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { apply getPartitionsEqRemove with idPDchild blockToRemove; trivial. }
  assert(HVSA: verticalSharing a).
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild addr HaddrUsedChild.
    rewrite HgetPartsEqsA in *. assert(HgetChildrenEq: getChildren pdparent a = getChildren pdparent s0).
    { apply getChildrenEqRemove with idPDchild blockToRemove; trivial. }
    rewrite HgetChildrenEq in *. assert(HaddrUsedChilds0: In addr (getUsedPaddr child s0)).
    {
      unfold getUsedPaddr in *. apply in_or_app. apply in_app_or in HaddrUsedChild.
      rewrite <-getConfigPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=a) (removePart:=idPDchild); trivial.
      destruct HaddrUsedChild as [Hconfig | Hmapped]; auto. right. destruct (beqAddr idPDchild child) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst child.
        pose proof (getMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in Hmapped. apply in_or_app.
        destruct Hmapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    specialize(HVS pdparent child HparentIsPart HchildIsChild addr HaddrUsedChilds0).
    destruct (beqAddr idPDchild pdparent) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. subst pdparent.
      assert(HaddrNotInBTR: ~In addr (getAllPaddrAux [blockToRemove] s0)).
      {
        intro HaddrInBTR. assert(HaddrAccMappedChild: In addr (getAccessibleMappedPaddr idPDchild s0)).
        {
          apply IL.addrInAccessibleBlockIsAccessibleMapped with blockToRemove; trivial.
        }
        assert(HaddrNotConfig: ~ In addr (getConfigPaddr child s0)).
        {
          assert(HchildIsPart: In child (getPartitions multiplexer s0)).
          { apply IL.childrenPartitionInPartitionList with idPDchild; trivial. }
          specialize(HKDI idPDchild child HparentIsPart HchildIsPart addr HaddrAccMappedChild). assumption.
        }
        unfold getUsedPaddr in *. apply in_app_or in HaddrUsedChilds0.
        destruct HaddrUsedChilds0 as [Hcontra | HaddrMapped]; try(congruence).
        assert(HeqTriv: CPaddr (blockToRemove+sh1offset) = CPaddr (blockToRemove+sh1offset)) by reflexivity.
        destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
        specialize(HnoChild idPDchild pdentry0 blockToRemove (CPaddr (blockToRemove+sh1offset)) HparentIsPart
          Hlookups0 HBTRMapped HeqTriv HPDchild child addr HchildIsChild HaddrInBTR). congruence.
      }
      pose proof (getMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRMapped HBE
        Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA. rewrite Heqs0 in *. apply in_app_or in HVS. apply in_or_app.
      destruct HVS as [Hleft | HVS]; auto. right. apply in_app_or in HVS. destruct HVS as [Hcontra | Hright]; trivial.
      exfalso; congruence.
    - rewrite <-beqAddrFalse in *. rewrite getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s0:=s0)
        (removePart:=idPDchild); trivial.
    (* END verticalSharing *)
  }
  assert(HnoDupA: noDupKSEntriesList a).
  {
    apply noDupKSEntriesListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnullA: nullAddrExists a).
  {
    apply nullAddrExistsPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  {
    apply noDupMappedBlocksListPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HdisjointA: DisjointKSEntries a).
  {
    apply DisjointKSEntriesPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  {
    apply wellFormedFstShadowIfBlockEntryPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoDupTreeA: noDupPartitionTree a).
  {
    apply noDupPartitionTreePreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HKDIA: kernelDataIsolation a).
  {
    apply kernelDataIsolationPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  assert(HnoChildA: noChildImpliesAddressesNotShared a).
  {
    apply noChildImpliesAddressesNotSharedPreservedRemove with s0 idPDchild blockToRemove; trivial.
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
  apply IHstatesList with a nextBlock blocksListRec; trivial.
Qed.

Lemma lookupBEEqRemoveRec block s s0 idPDchild blockToRemove statesList blocksList:
isBE block s0
-> ~In block (blockToRemove::blocksList)
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr.
Proof.
revert s0 blockToRemove blocksList.
induction statesList; simpl; intros s0 blockToRemove blocksList HblockIsBE HblockNotIn HblocksList.
- destruct HblocksList. subst s. reflexivity.
- destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBlockNull & Hnext & HPDT & HBTRMapped &
    HAflagBTR & HBE & HPflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
  apply Decidable.not_or in HblockNotIn. destruct HblockNotIn as (HbeqBlocks & HblockNotInRec). unfold isBE in *.
  rewrite HblocksListEq in *. assert(HeqA: lookup block (memory a) beqAddr = lookup block (memory s0) beqAddr).
  {
    apply HlookupsEq; trivial.
    - intro Hcontra. subst block. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
      congruence.
    - intro Hcontra. subst block. unfold sh1entryPDchild in *.
      destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    - intro Hcontra. subst block. unfold scentryNext in *.
      destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
  }
  rewrite <-HeqA in *. revert HblocksList. apply IHstatesList; trivial.
Qed.

Lemma removeRecBlocksWereMapped block s s0 idPDchild blockToRemove statesList blocksList:
block <> nullAddr
-> noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> In block blocksList
-> nullAddr = last blocksList blockToRemove
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> In block (getMappedBlocks idPDchild s0).
Proof.
intro HbeqBlockNull. revert s0 blockToRemove statesList. induction blocksList; cbn -[last nullAddr]; intros s0
  blockToRemove statesList HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 HblockIn Hlast HblocksList;
  try(exfalso; congruence). apply IL.lastRec in Hlast.
destruct statesList; try(destruct HblocksList; exfalso; congruence). simpl in *.
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBlockCNull & Hnext & HPDT & HblockCMapped &
  HAflag & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
injection HblocksListEq. intros HlistsEq HblocksEq. subst blocksListRec. subst a.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDflag in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
{
  unfold isSCE. unfold scentryNext in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HnoDups1: noDupKSEntriesList s1).
{ revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial. }
assert(HnoDupMappeds1: noDupMappedBlocksList s1).
{ revert HlookupsEq. apply noDupMappedBlocksListPreservedRemove; trivial. }
assert(Hnulls1: nullAddrExists s1).
{ revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial. }
assert(Hdisjoints1: DisjointKSEntries s1).
{ revert HlookupsEq. apply DisjointKSEntriesPreservedRemove; trivial. }
assert(HwellSh1s1: wellFormedFstShadowIfBlockEntry s1).
{ revert HlookupsEq. apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial. }
assert(HgetMappedEqs1: In block (getMappedBlocks idPDchild s1)
  -> In block (getMappedBlocks idPDchild s0)).
{
  pose proof (getMappedBlocksEqRemPartRemove blockToRemove s1 s0 idPDchild HnoDup HPDT
    HblockCMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
  destruct Heqs as [leftList [rightList (Heqs1 & Heqs0)]]. rewrite Heqs0. rewrite Heqs1. intro HblockIns1.
  apply in_or_app. apply in_app_or in HblockIns1. destruct HblockIns1; auto. right. apply in_or_app. auto.
}
destruct HblockIn as [HbeqBlocks | HblockIn];
  try(apply HgetMappedEqs1; revert HblocksList; apply IHblocksList; assumption). subst block.
destruct statesList; try(destruct HblocksList; subst blocksList; simpl in *; exfalso; congruence). simpl in *.
destruct HblocksList as [blockNext [blocksListRec HblocksList]]. apply HgetMappedEqs1. intuition.
Qed.

Lemma getPartitionsEqRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> getPartitions multiplexer s = getPartitions multiplexer s0.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint Hwell HblocksList; try(destruct HblocksList; subst s; reflexivity).
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBlockNull & Hnext & HPDT & HBTRMapped &
  HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
assert(isSCE (CPaddr (blockToRemove + scoffset)) s0).
{
  unfold isSCE. unfold scentryNext in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDflag in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HeqA: getPartitions multiplexer a = getPartitions multiplexer s0).
{ revert HlookupsEq. apply getPartitionsEqRemove; trivial. }
rewrite <-HeqA. revert HblocksList. apply IHstatesList; trivial.
- revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial.
- revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial.
- revert HlookupsEq. apply noDupMappedBlocksListPreservedRemove; trivial.
- revert HlookupsEq. apply DisjointKSEntriesPreservedRemove; trivial.
- revert HlookupsEq. apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial.
Qed.

Lemma getKSEntriesEqRemoveRec part s s0 idPDchild blockToRemove statesList blocksList:
removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> getKSEntries part s = getKSEntries part s0.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HblocksList;
  try(destruct HblocksList; subst s; reflexivity).
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBlockNull & Hnext & HPDT & HBTRMapped &
  HAflagBTR & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksList)]].
assert(isSCE (CPaddr (blockToRemove + scoffset)) s0).
{
  unfold isSCE. unfold scentryNext in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDflag in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HeqA: getKSEntries part a = getKSEntries part s0).
{ revert HlookupsEq. apply getKSEntriesEqRemove; trivial. }
rewrite <-HeqA. revert HblocksList. apply IHstatesList; trivial.
Qed.

Lemma blockRemovedWereNotShared block s s0 idPDchild blockToRemove statesList blocksList:
block <> nullAddr
-> In block (blockToRemove::blocksList)
-> nullAddr = last blocksList blockToRemove
-> blockToRemove <> nullAddr
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> sh1entryPDchild (CPaddr (block+sh1offset)) nullAddr s0.
Proof.
intro HbeqBlockNull. revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0
  blockToRemove blocksList HblockIn Hlast HbeqBTRNull HblocksList.
{
  destruct HblocksList. subst blocksList. simpl in *. exfalso; congruence.
}
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & _ & Hnext & HPDT & HBTRMapped & HAflag & HBE &
  HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
destruct HblockIn as [HbeqBTRBlock | HblockIn]; try(subst block; assumption). rewrite HblocksListEq in *.
apply IL.lastRec in Hlast. assert(HbeqNextNull: blockChild <> nullAddr).
{
  intro Hcontra. subst blockChild. destruct statesList; simpl in HblocksListRec.
  - destruct HblocksListRec. subst blocksListRec. simpl in *. destruct HblockIn; congruence.
  - destruct HblocksListRec as [_ [_ (_ & Hcontra & _)]]. congruence.
}
specialize(IHstatesList a blockChild blocksListRec HblockIn Hlast HbeqNextNull HblocksListRec).
unfold sh1entryPDchild in *.
destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) (CPaddr (block+sh1offset))) eqn:HbeqSh1s.
- rewrite <-beqAddrTrue in HbeqSh1s. rewrite HbeqSh1s in *. assumption.
- rewrite <-beqAddrFalse in *. assert(idPDchild <> CPaddr (block+sh1offset)).
  {
    intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups1 & _)]]. rewrite Hlookups1 in *.
    congruence.
  }
  assert(blockToRemove <> CPaddr (block+sh1offset)).
  {
    intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups1)]]].
    rewrite Hlookups1 in *. congruence.
  }
  assert(CPaddr (blockToRemove+scoffset) <> CPaddr (block+sh1offset)).
  {
    intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
  }
  rewrite <-HlookupsEq; trivial.
Qed.

Lemma noPDchildPreservedRemoveRec sh1entryaddr s s0 idPDchild blockToRemove statesList blocksList:
sh1entryPDchild sh1entryaddr nullAddr s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> sh1entryPDchild sh1entryaddr nullAddr s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HPDchildSh1
  HblocksList; try(destruct HblocksList; subst s; assumption).
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped & HAflag &
  HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
assert(HPDchildSh1A: sh1entryPDchild sh1entryaddr nullAddr a).
{
  unfold sh1entryPDchild in *. destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
  - rewrite <-beqAddrTrue in HbeqSh1s. subst sh1entryaddr. rewrite HSHE. reflexivity.
  - rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
    + intro Hcontra. subst sh1entryaddr. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *.
      congruence.
    + intro Hcontra. subst sh1entryaddr. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. rewrite Hlookups0 in *.
      congruence.
    + intro Hcontra. subst sh1entryaddr. unfold scentryNext in *.
      destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
}
revert HblocksListRec. apply IHstatesList; assumption.
Qed.

Lemma lookupSh1EqRemoveRec (block:paddr) s s0 idPDchild blockToRemove statesList blocksList:
isSHE (CPaddr (block+sh1offset)) s
-> nullAddrExists s0
-> ~In block (blockToRemove::blocksList)
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr = lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr.
Proof.
intro Hsh1IsSHE. revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList
  Hnull HblockNotIn HblocksList; try(destruct HblocksList; subst s; reflexivity).
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped & HAflag &
  HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]]. apply Decidable.not_or in HblockNotIn.
destruct HblockNotIn as (HbeqBlocks & HblockNotInRec). rewrite HblocksListEq in *.
assert(HnullA: nullAddrExists a).
{
  revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial.
  - unfold isSHE. unfold sh1entryPDchild in *.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  - unfold isSCE. unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
}
apply IHstatesList in HblocksListRec; trivial. unfold isSHE in *. rewrite HblocksListRec in *. apply HlookupsEq.
- intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]]. rewrite Hlookups in *.
  congruence.
- intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
  rewrite Hlookups in *. congruence.
- intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
  unfold nullAddrExists in *. unfold isPADDR in *. rewrite HSHE in *. congruence.
- intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
Qed.

Lemma getMappedInclRemoveRec block s s0 idPDchild blockToRemove statesList blocksList:
In block (getMappedBlocks idPDchild s)
-> noDupKSEntriesList s0
(*-> ~In block (blockToRemove::blocksList)*)
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> In block (getMappedBlocks idPDchild s0).
Proof.
intro HblockMapped. revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove
  blocksList HnoDup (*HblockNotIn*) HblocksList; try(destruct HblocksList; subst s; assumption).
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped & HAflag &
  HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]]. (*apply Decidable.not_or in HblockNotIn.
destruct HblockNotIn as (HbeqBlocks & HblockNotInRec). rewrite HblocksListEq in *.*)
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDchild in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
{
  unfold isSCE. unfold scentryNext in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HnoDupA: noDupKSEntriesList a).
{ revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial. }
apply IHstatesList in HblocksListRec; trivial.
pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
  HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
destruct Heqs as [leftList [rightList (Heqa & Heqs0)]]. rewrite Heqa in *. rewrite Heqs0. apply in_or_app.
apply in_app_or in HblocksListRec. destruct HblocksListRec; auto. right. apply in_or_app. auto.
Qed.

Lemma getMappedInclRemoveRecNotInListRev block s s0 idPDchild blockToRemove statesList blocksList:
In block (getMappedBlocks idPDchild s0)
-> noDupKSEntriesList s0
-> ~In block (blockToRemove::blocksList)
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> In block (getMappedBlocks idPDchild s).
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove
  blocksList HblockMapped HnoDup HblockNotIn HblocksList; try(destruct HblocksList; subst s; assumption).
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped & HAflag &
  HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]]. apply Decidable.not_or in HblockNotIn.
destruct HblockNotIn as (HbeqBlocks & HblockNotInRec). rewrite HblocksListEq in *.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDchild in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
{
  unfold isSCE. unfold scentryNext in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HnoDupA: noDupKSEntriesList a).
{ revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial. }
assert(HblockMappedA: In block (getMappedBlocks idPDchild a)).
{
  pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
    HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
  destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite HeqA. rewrite Heqs0 in *. apply in_or_app.
  apply in_app_or in HblockMapped. destruct HblockMapped as [Hleft | Hright]; auto. right. apply in_app_or in Hright.
  simpl in *. destruct Hright as [Hcontra | Hright]; trivial. destruct Hcontra; exfalso; congruence.
}
revert HblocksListRec. apply IHstatesList; trivial.
Qed.

Lemma removedBlocksAreNexts block s s0 idPDchild blockToRemove statesList blocksList:
block <> nullAddr
-> noDupKSEntriesList s0
-> In block blocksList
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> exists prevBlock, In prevBlock (getMappedBlocks idPDchild s0)
    /\ scentryNext (CPaddr (prevBlock+scoffset)) block s0.
Proof.
intro HbeqBlockNull. revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove
  blocksList HnoDup HblockIn HblocksList; try(destruct HblocksList; subst blocksList; simpl in *; exfalso;
  congruence).
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped & HAflag &
  HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]]. rewrite HblocksListEq in *. simpl in *.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold isSHE. unfold sh1entryPDchild in *.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
{
  unfold isSCE. unfold scentryNext in *.
  destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HnoDupA: noDupKSEntriesList a).
{ revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial. }
destruct HblockIn as [HblocksEq | HblockInRec].
- subst block. exists blockToRemove. auto.
- apply IHstatesList in HblocksListRec; trivial. destruct HblocksListRec as [prevBlock (HprevMapped & HnextPrev)].
  exists prevBlock. split.
  + pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE
      HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite Heqs0.
    rewrite HeqA in *. apply in_or_app. apply in_app_or in HprevMapped. destruct HprevMapped; auto. right.
    apply in_or_app. auto.
  + unfold scentryNext in *. rewrite <-HlookupsEq; trivial.
    * intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]]. rewrite HlookupA in *.
      congruence.
    * intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & HlookupA)]]].
      rewrite HlookupA in *. congruence.
    * intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. congruence.
    * intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. simpl in *. congruence.
Qed.

Lemma removedAddrsAreARange s s0 idPDchild blockToRemove statesList blocksList:
blockAndNextAreSideBySide s0
-> noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> wellFormedBlock s0
-> noDupMappedPaddrList s0
-> (forall part block scnext, In part (getPartitions multiplexer s0)
      -> In block (getMappedBlocks part s0)
      -> scentryNext (CPaddr (block+scoffset)) scnext s0
       -> scnext <> nullAddr
      -> blockToRemove <> scnext)
-> In idPDchild (getPartitions multiplexer s0)
-> NoDup (blockToRemove::blocksList)
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> exists startaddr endaddr, getAllPaddrAux (blockToRemove::blocksList) s0 = getAllPaddrBlock startaddr endaddr.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnextBlockSide
  HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 Hwell HnoDupMappedP HBTRNotNext HchildIsPart HnoDupList HblocksList.
- destruct HblocksList. subst blocksList. simpl.
  destruct (lookup blockToRemove (memory s0) beqAddr); try(exists nullAddr; exists nullAddr; cbn; reflexivity).
  destruct v; try(exists nullAddr; exists nullAddr; cbn; reflexivity). exists (startAddr (blockrange b)).
  rewrite app_nil_r. exists (endAddr (blockrange b)). reflexivity.
- destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & Hnext & HPDT & HBTRMapped & HAflag
    & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold isSHE. unfold sh1entryPDchild in *.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold isSCE. unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HnoDupA: noDupKSEntriesList a).
  { revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial. }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  { revert HlookupsEq. apply noDupMappedBlocksListPreservedRemove; trivial. }
  assert(HnullA: nullAddrExists a).
  { revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial. }
  assert(HdisjointA: DisjointKSEntries a).
  { revert HlookupsEq. apply DisjointKSEntriesPreservedRemove; trivial. }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  { revert HlookupsEq. apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial. }
  assert(HnextBlockSideA: blockAndNextAreSideBySide a).
  { revert HlookupsEq. apply blockAndNextAreSideBySidePreservedRemove; trivial. }
  assert(HwellA: wellFormedBlock a).
  { revert HlookupsEq. apply wellFormedBlockPreservedRemove; trivial. }
  assert(HnoDupMappedPA: noDupMappedPaddrList a).
  { revert HlookupsEq. apply noDupMappedPaddrListPreservedRemove; trivial. }
  assert(HgetPartsEqsA: getPartitions multiplexer a = getPartitions multiplexer s0).
  { revert HlookupsEq. apply getPartitionsEqRemove; trivial. }
  apply NoDup_cons_iff in HnoDupList. destruct HnoDupList as (HBTRNotInList & HnoDupListRec).
  assert(HnextNotNext: forall part block scnext, In part (getPartitions multiplexer a)
    -> In block (getMappedBlocks part a) -> scentryNext (CPaddr (block + scoffset)) scnext a
    -> scnext <> nullAddr -> blockChild <> scnext).
  {
    intros part block scnext HpartIsPart HblockMapped HnextBis HbeqNextNull HbeqNextBTRNext. subst scnext.
    assert(HblockMappeds0: In block (getMappedBlocks part s0)).
    {
      pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as HeqChilds.
      destruct HeqChilds as [leftChild [rightChild (HchildA & Hchilds0)]].
      pose proof (getMappedBlocksEqRemove blockToRemove a s0 idPDchild part Hdisjoint HPDT HBTRMapped HBE Hsh1IsSHE
        HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. rewrite Hchilds0. rewrite HchildA in *.
        apply in_app_or in HblockMapped. apply in_or_app. destruct HblockMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. specialize(Heqs HbeqParts). rewrite <-Heqs. assumption.
    }
    unfold scentryNext in *. rewrite HgetPartsEqsA in *. assert(HbeqChildSce: idPDchild <> (CPaddr (block+scoffset))).
    {
      intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]].
      rewrite Hlookups in *. congruence.
    }
    assert(HbeqBTRSce: blockToRemove <> (CPaddr (block+scoffset))).
    {
      intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      rewrite Hlookups in *. congruence.
    }
    assert(HbeqSh1Sce: CPaddr (blockToRemove+sh1offset) <> CPaddr (block+scoffset)).
    { intro Hcontra. rewrite <-Hcontra in *. rewrite HSHE in *. congruence. }
    assert(HbeqSces: CPaddr (blockToRemove+scoffset) <> CPaddr (block+scoffset)).
    { intro Hcontra. rewrite <-Hcontra in *. rewrite HSCE in *. simpl in *. congruence. }
    rewrite HlookupsEq in HnextBis; trivial.
    assert(Hsce: CPaddr (block+scoffset) = CPaddr (block+scoffset)) by reflexivity.
    assert(Hbounds: (exists startaddr endaddr, bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0)
      /\ bentryPFlag block true s0).
    {
      apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. unfold bentryEndAddr. unfold bentryStartAddr. rewrite Hlookup. split; auto.
      exists (startAddr (blockrange bentry)). exists (endAddr (blockrange bentry)). split; trivial.
    }
    destruct Hbounds as ([startaddr [endaddr (Hstart & Hend)]] & HPflag).
    assert(HnextBlockSideCopy: blockAndNextAreSideBySide s0) by assumption.
    specialize(HnextBlockSide part block (CPaddr (block+scoffset)) blockChild endaddr HpartIsPart HblockMappeds0
      Hend Hsce HbeqNextNull HnextBis). destruct HnextBlockSide as (HstartNext & HnextMappedPart).
    assert(HboundsBTR: exists startBTR endBTR, bentryStartAddr blockToRemove startBTR s0
      /\ bentryEndAddr blockToRemove endBTR s0).
    {
      destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. unfold bentryEndAddr. unfold bentryStartAddr.
      rewrite Hlookups0. exists (startAddr (blockrange bentry0)). exists (endAddr (blockrange bentry0)).
      split; trivial.
    }
    destruct HboundsBTR as [startBTR [endBTR (HstartBTR & HendBTR)]].
    assert(HsceBTR: CPaddr (blockToRemove+scoffset) = CPaddr (blockToRemove+scoffset)) by reflexivity.
    specialize(HnextBlockSideCopy idPDchild blockToRemove (CPaddr (blockToRemove+scoffset)) blockChild endBTR
      HchildIsPart HBTRMapped HendBTR HsceBTR HbeqNextNull Hnext).
    destruct HnextBlockSideCopy as (HstartNextBis & HnextMappedChild). unfold bentryStartAddr in *.
    destruct (lookup blockChild (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    rewrite <-HstartNext in *. subst endBTR. assert(HPflagBTR: bentryPFlag blockToRemove true s0).
    {
      apply IL.mappedBlockIsBE in HBTRMapped. destruct HBTRMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(HwellCopy: wellFormedBlock s0) by assumption. specialize(Hwell block startaddr endaddr HPflag Hstart Hend).
    specialize(HwellCopy blockToRemove startBTR endaddr HPflagBTR HstartBTR HendBTR). destruct Hwell as (Hwell & _).
    destruct HwellCopy as (HwellBTR & _). assert(HchildIsPDT: isPDT idPDchild s0).
    { destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. unfold isPDT. rewrite Hlookups0. trivial. }
    assert(part = idPDchild).
    {
      destruct (beqAddr part idPDchild) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
      rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HnextMappedPart.
      apply InFilterPresentInList in HnextMappedChild. assert(HpartIsPDT: isPDT part s0).
      {
        unfold isPDT. unfold getKSEntries in *.
        destruct (lookup part (memory s0) beqAddr); try(simpl in *; congruence).
        destruct v; try(simpl in *; congruence). trivial.
      }
      specialize(Hdisjoint part idPDchild HpartIsPDT HchildIsPDT HbeqParts).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      specialize(Hdisjoint blockChild HnextMappedPart). congruence.
    }
    subst part.
    assert(HbeqBlocks: blockToRemove = block).
    {
      destruct (beqAddr blockToRemove block) eqn:HbeqBlocks; try(rewrite beqAddrTrue; trivial). exfalso.
      rewrite <-beqAddrFalse in *. assert(HendIsValid: p (CPaddr (endaddr-1)) = endaddr-1).
      {
        unfold CPaddr. assert(endaddr <= maxAddr) by (apply Hp).
        destruct (le_dec (endaddr - 1) maxAddr); try(lia). reflexivity.
      }
      assert(HendInBTR: In (CPaddr (endaddr-1)) (getAllPaddrAux [blockToRemove] s0)).
      {
        simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        destruct (lookup blockToRemove (memory s0) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence). rewrite <-HstartBTR. rewrite <-HendBTR. rewrite app_nil_r.
        apply IL.getAllPaddrBlockIncl; lia.
      }
      pose proof (DisjointPaddrInPart idPDchild blockToRemove block (CPaddr (endaddr-1)) s0 HnoDupMappedP
        HchildIsPDT HBTRMapped HblockMappeds0 HbeqBlocks HendInBTR) as HendNotInBlock. apply HendNotInBlock. simpl.
      unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
      destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    subst block. congruence.
  }
  rewrite <-HgetPartsEqsA in HchildIsPart. rewrite HblocksListEq in HnoDupListRec.
  specialize(IHstatesList a blockChild blocksListRec HnextBlockSideA HnoDupA HnullA HnoDupMappedA HdisjointA
    HwellSh1A HwellA HnoDupMappedPA HnextNotNext HchildIsPart HnoDupListRec HblocksListRec).
  destruct IHstatesList as [startNext [endRange HrangeEq]].
  assert(Hbounds: exists startBTR endBTR, bentryStartAddr blockToRemove startBTR s0
    /\ bentryEndAddr blockToRemove endBTR s0).
  {
    unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryAFlag in *.
    destruct (lookup blockToRemove (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). exists (endAddr (blockrange b)).
    auto.
  }
  destruct Hbounds as [startBTR [endBTR (HstartBTR & HendBTR)]]. exists startBTR.
  assert(HrangeEqAs0: getAllPaddrAux (blockChild::blocksListRec) a = getAllPaddrAux (blockChild::blocksListRec) s0).
  {
    rewrite HblocksListEq in HBTRNotInList. clear HnoDupListRec. clear HblocksListEq. clear HrangeEq.
    induction (blockChild::blocksListRec); simpl in *; trivial. apply Decidable.not_or in HBTRNotInList.
    destruct HBTRNotInList as (HbeqBlocks & HBTRNotInListRec). rewrite IHl; trivial. apply not_eq_sym in HbeqBlocks.
    destruct (beqAddr idPDchild a0) eqn:HbeqChildA.
    {
      rewrite <-beqAddrTrue in HbeqChildA. subst a0.
      destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & HlookupA & _)]]. rewrite Hlookups0. rewrite HlookupA. trivial.
    }
    destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) a0) eqn:HbeqSh1A.
    {
      rewrite <-beqAddrTrue in HbeqSh1A. subst a0. rewrite HSHE. unfold isSHE in *.
      destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). trivial.
    }
    destruct (beqAddr (CPaddr (blockToRemove+scoffset)) a0) eqn:HbeqSceA.
    {
      rewrite <-beqAddrTrue in HbeqSceA. subst a0. rewrite HSCE. unfold isSCE in *.
      destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). trivial.
    }
    rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  }
  rewrite HrangeEqAs0 in *. rewrite HblocksListEq. rewrite HrangeEq.
  destruct (beqAddr blockChild nullAddr) eqn:HbeqNextNull.
  + rewrite <-beqAddrTrue in HbeqNextNull. subst blockChild. assert(blocksListRec = []).
    {
      destruct statesList; simpl in *.
      - destruct HblocksListRec. assumption.
      - destruct HblocksListRec as [_ [_ (_ & Hcontra & _)]]. exfalso; congruence.
    }
    subst blocksListRec. simpl in *. exists endBTR. unfold nullAddrExists in *. unfold isPADDR in *.
    destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite <-HrangeEq. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    destruct (lookup blockToRemove (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite <-HstartBTR. rewrite <-HendBTR. apply app_nil_r.
  + exists endRange. rewrite <-beqAddrFalse in *.
    assert(HeqTriv: CPaddr (blockToRemove+scoffset) = CPaddr (blockToRemove+scoffset)) by reflexivity.
    rewrite HgetPartsEqsA in *.
    specialize(HnextBlockSide idPDchild blockToRemove (CPaddr (blockToRemove+scoffset)) blockChild endBTR HchildIsPart
      HBTRMapped HendBTR HeqTriv HbeqNextNull Hnext). destruct HnextBlockSide as (HstartNext & HnextMapped).
    assert(HPflagNext: bentryPFlag blockChild true s0).
    {
      apply IL.mappedBlockIsBE in HnextMapped. destruct HnextMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(HendNext: exists endNext, bentryEndAddr blockChild endNext s0).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr.
      destruct (lookup blockChild (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
    }
    destruct HendNext as [endNext HendNext].
    assert(HwellCopy: wellFormedBlock s0) by assumption.
    specialize(Hwell blockChild endBTR endNext HPflagNext HstartNext HendNext). destruct Hwell as (Hwell & _).
    assert(endBTR = startNext).
    {
      simpl in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      destruct (lookup blockChild (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-HstartNext in *. rewrite <-HendNext in *. apply eq_sym.
      apply eq_sym in HrangeEq. revert HrangeEq. apply getAllPaddrBlockSplit. assumption.
    }
    assert(HPflag: bentryPFlag blockToRemove true s0).
    {
      apply IL.mappedBlockIsBE in HBTRMapped. destruct HBTRMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    specialize(HwellCopy blockToRemove startBTR endBTR HPflag HstartBTR HendBTR).
    destruct HwellCopy as (HwellBTR & _). subst endBTR. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    destruct (lookup blockToRemove (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite <-HstartBTR. rewrite <-HendBTR. unfold getAllPaddrBlock.
    assert(endRange <= maxAddr) by (apply Hp). apply IL.getAllPaddrBlockAuxCut; try(lia).
    assert(HstartIn: In startNext (getAllPaddrBlock startNext endRange)).
    {
      rewrite <-HrangeEq. simpl.
      destruct (lookup blockChild (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-HstartNext. rewrite <-HendNext. apply in_or_app. left.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    apply IL.getAllPaddrBlockInclRev in HstartIn. destruct HstartIn as (_ & Hres & _). lia.
Qed.

Lemma checkRemovedEq s s0 idPDchild blockToRemove statesList blocksList nextBlocksList:
nullAddrExists s0
-> wellFormedBlock s0
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> noDupMappedBlocksList s0
-> noDupMappedPaddrList s0
-> In idPDchild (getPartitions multiplexer s0)
-> nullAddr = last blocksList blockToRemove
-> nullAddr = last nextBlocksList blockToRemove
-> checkRemoveOkRec blockToRemove idPDchild nextBlocksList s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> blocksList = nextBlocksList.
Proof.
revert s0 blockToRemove statesList blocksList. induction nextBlocksList; cbn -[last nullAddr]; intros s0 blockToRemove
  statesList blocksList Hnull Hwell HnoDup Hdisjoint HwellSh1 HnoDupMapped HnoDupPaddr HchildIsPart Hlast HlastNext
  HnextBlocksList HblocksList.
- simpl in *. subst blockToRemove. destruct statesList; simpl in *.
  + destruct HblocksList. assumption.
  + destruct HblocksList as [_ [_ (_ & Hcontra & _)]]. congruence.
- apply IL.lastRec in HlastNext.
  pose proof (noDupNextBlocksList blockToRemove idPDchild (a::nextBlocksList) s0 Hnull Hwell HnoDupPaddr
    HchildIsPart HnextBlocksList) as HnoDupList. apply NoDup_cons_iff in HnoDupList.
  destruct HnoDupList as (HBTRNotInist & _).
  destruct HnextBlocksList as (HAflag & HPflag & HBTRMapped & HPDchild & Hnext & HnextSide & HnextBlocksListRec).
  destruct statesList.
  {
    simpl in *. destruct HblocksList. subst blocksList. simpl in *. subst blockToRemove. unfold bentryAFlag in *.
    unfold nullAddrExists in *. unfold isPADDR in *. exfalso.
    destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  simpl in *. destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBis & HPDT &
    _ & _ & HBE & HPDflag & _ & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold isSHE. unfold sh1entryPDchild in *.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold isSCE. unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hnulls1: nullAddrExists s1).
  { revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial. }
  assert(Hwells1: wellFormedBlock s1).
  { revert HlookupsEq. apply wellFormedBlockPreservedRemove; trivial. }
  assert(HnoDupMappedPs1: noDupMappedPaddrList s1).
  { revert HlookupsEq. apply noDupMappedPaddrListPreservedRemove; trivial. }
  assert(HnoDups1: noDupKSEntriesList s1).
  { revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial. }
  assert(Hdisjoints1: DisjointKSEntries s1).
  { revert HlookupsEq. apply DisjointKSEntriesPreservedRemove; trivial. }
  assert(HwellSh1s1: wellFormedFstShadowIfBlockEntry s1).
  { revert HlookupsEq. apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial. }
  assert(HnoDupMappeds1: noDupMappedBlocksList s1).
  { revert HlookupsEq. apply noDupMappedBlocksListPreservedRemove; trivial. }
  assert(a = blockChild).
  {
    unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite <-HnextBis in *. assumption.
  }
  subst a. rewrite HblocksListEq in *. apply IL.lastRec in Hlast. f_equal.
  assert(HgetPartsEqss1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
  { revert HlookupsEq. apply getPartitionsEqRemove; trivial. }
  assert(HnextBlocksListRecs1: checkRemoveOkRec blockChild idPDchild nextBlocksList s1).
  {
    revert HnextBlocksListRec. apply checkRemoveOkPreservedRemove with blockToRemove; trivial.
  }
  rewrite <-HgetPartsEqss1 in *. revert HblocksListRec. apply IHnextBlocksList; trivial.
Qed.

Lemma secToLastElHasNextNullAndLastAddr blocksListHead lastNext s s0 idPDchild blockToRemove statesList blocksList
  startRange endRange:
nullAddrExists s0
-> wellFormedBlock s0
-> NoDup (blockToRemove::blocksList)
-> blockToRemove::blocksList = blocksListHead++[lastNext]++[nullAddr]
-> getAllPaddrAux (blockToRemove::blocksList) s0 = getAllPaddrBlock startRange endRange
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> scentryNext (CPaddr (lastNext+scoffset)) nullAddr s0 /\ bentryEndAddr lastNext endRange s0.
Proof.
revert s0 blockToRemove blocksList blocksListHead startRange.
induction statesList; simpl; intros s0 blockToRemove blocksList blocksListHead startRange Hnull Hwell
  HnoDupList HlistEq Hrange HblocksList.
{
  destruct HblocksList. subst blocksList. exfalso.
  assert(length (blocksListHead ++ [lastNext; nullAddr]) >= 2).
  { rewrite length_app. simpl. lia. }
  rewrite <-HlistEq in *. simpl in *. lia.
}
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBis & HPDT & HBTRMapped &
  HAflag & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
apply NoDup_cons_iff in HnoDupList. destruct HnoDupList as (HBTRNotInList & HnoDupListRec).
destruct blocksListHead as [ | firstEl blocksListHead].
- rewrite app_nil_l in HlistEq. injection HlistEq. intros HlistSingl HblocksEq. rewrite HlistSingl in *.
  subst lastNext. injection HblocksListEq as Heq. subst blockChild. split; trivial. simpl in *.
  unfold nullAddrExists in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). unfold bentryAFlag in *. unfold bentryEndAddr.
  destruct (lookup blockToRemove (memory s0) beqAddr) eqn:Hlookup; try(congruence). destruct v; try(congruence).
  rewrite app_nil_r in *. assert(Hstart: bentryStartAddr blockToRemove (startAddr (blockrange b)) s0).
  { unfold bentryStartAddr. rewrite Hlookup. reflexivity. }
  assert(Hend: bentryEndAddr blockToRemove (endAddr (blockrange b)) s0).
  { unfold bentryEndAddr. rewrite Hlookup. reflexivity. }
  assert(HPflag: bentryPFlag blockToRemove true s0).
  {
    apply IL.mappedBlockIsBE in HBTRMapped. destruct HBTRMapped as [bentry (HlookupBis & Hres)]. unfold bentryPFlag.
    rewrite HlookupBis. auto.
  }
  specialize(Hwell blockToRemove (startAddr (blockrange b)) (endAddr (blockrange b)) HPflag Hstart Hend).
  destruct Hwell as (Hwell & _). apply getAllPaddrBlockEq in Hrange; trivial. destruct Hrange. auto.
- injection HlistEq. clear HlistEq. intros HlistEq HblocksEq. subst firstEl. rewrite HblocksListEq in HlistEq.
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold isSHE. unfold sh1entryPDchild in *.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold isSCE. unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HnullA: nullAddrExists a).
  { revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial. }
  assert(HwellA: wellFormedBlock a).
  { revert HlookupsEq. apply wellFormedBlockPreservedRemove; trivial. }
  unfold bentryAFlag in *.
  destruct (lookup blockToRemove (memory s0) beqAddr) eqn:HlookupBTR; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). assert(Hstart: bentryStartAddr blockToRemove (startAddr (blockrange b)) s0).
  { unfold bentryStartAddr. rewrite HlookupBTR. reflexivity. }
  assert(Hend: bentryEndAddr blockToRemove (endAddr (blockrange b)) s0).
  { unfold bentryEndAddr. rewrite HlookupBTR. reflexivity. }
  assert(HPflag: bentryPFlag blockToRemove true s0).
  {
    apply IL.mappedBlockIsBE in HBTRMapped. destruct HBTRMapped as [bentry (HlookupBis & Hres)]. unfold bentryPFlag.
    rewrite HlookupBis. auto.
  }
  specialize(Hwell blockToRemove (startAddr (blockrange b)) (endAddr (blockrange b)) HPflag Hstart Hend).
  destruct Hwell as (Hwell & _).
  assert(HstartsEq: startAddr (blockrange b) = startRange).
  {
    apply eq_sym in Hrange. apply eq_sym. revert Hrange. apply getAllPaddrBlockSplit. assumption.
  }
  rewrite HstartsEq in *. apply eq_sym in Hrange. apply getAllPaddrBlockSplitLEq in Hrange; trivial.
  rewrite HblocksListEq in *.
  assert(HrangeA: getAllPaddrAux (blockChild::blocksListRec) a = getAllPaddrBlock (endAddr (blockrange b)) endRange).
  {
    rewrite <-Hrange. clear HnoDupListRec. clear HblocksListEq. clear Hrange. clear HlistEq.
    induction (blockChild::blocksListRec); simpl in *; trivial. apply Decidable.not_or in HBTRNotInList.
    destruct HBTRNotInList as (HbeqA0BTR & HBTRNotInListRec). rewrite IHl; trivial. apply not_eq_sym in HbeqA0BTR.
    destruct (beqAddr idPDchild a0) eqn:HbeqChildA0.
    {
      rewrite <-beqAddrTrue in HbeqChildA0. subst a0.
      destruct HPDT as [pdentry0 [pdentry1 (Hlookups0 & HlookupA & _)]]. rewrite Hlookups0. rewrite HlookupA.
      reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove+sh1offset)) a0) eqn:HbeqSh1A0.
    {
      rewrite <-beqAddrTrue in HbeqSh1A0. subst a0. rewrite HSHE. unfold isSHE in *.
      destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    destruct (beqAddr (CPaddr (blockToRemove+scoffset)) a0) eqn:HbeqSceA0.
    {
      rewrite <-beqAddrTrue in HbeqSceA0. subst a0. rewrite HSCE. unfold isSCE in *.
      destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    }
    rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  }
  specialize(IHstatesList a blockChild blocksListRec blocksListHead (endAddr (blockrange b)) HnullA HwellA
    HnoDupListRec HlistEq HrangeA HblocksListRec). destruct IHstatesList as (HnextLast & HendLast).
  unfold scentryNext in *. unfold bentryEndAddr in *. rewrite HlistEq in HBTRNotInList.
  apply Lib.in_app_or_neg in HBTRNotInList. destruct HBTRNotInList as (_ & HBTRNotInListEnd). simpl in *.
  apply Decidable.not_or in HBTRNotInListEnd. destruct HBTRNotInListEnd as (HbeqLastBTR & HBTRNotNull).
  apply not_eq_sym in HbeqLastBTR. assert(idPDchild <> lastNext).
  {
    intro Hcontra. subst lastNext. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]]. rewrite HlookupA in *.
    exfalso; congruence.
  }
  assert(CPaddr (blockToRemove+sh1offset) <> lastNext).
  { intro Hcontra. subst lastNext. rewrite HSHE in *. exfalso; congruence. }
  assert(CPaddr (blockToRemove+scoffset) <> lastNext).
  { intro Hcontra. subst lastNext. rewrite HSCE in *. exfalso; congruence. }
  rewrite HlookupsEq in HendLast; trivial. split; trivial. assert(idPDchild <> CPaddr (lastNext+scoffset)).
  {
    intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]]. rewrite HlookupA in *.
    exfalso; congruence.
  }
  assert(blockToRemove <> CPaddr (lastNext+scoffset)).
  {
    intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & HlookupA)]]].
    rewrite HlookupA in *. exfalso; congruence.
  }
  assert(CPaddr (blockToRemove+sh1offset) <> CPaddr (lastNext+scoffset)).
  { intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. exfalso; congruence. }
  assert(CPaddr (blockToRemove+scoffset) <> CPaddr (lastNext+scoffset)).
  {
    intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
    unfold nullAddrExists in *. unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr) ; try(congruence).
    destruct v; congruence.
  }
  rewrite <-HlookupsEq; trivial.
Qed.

Lemma removedAddrsInSameParent blockToRemove idPDchild blocksList s pdentry pdparent blockParent block addr startaddr:
nullAddrExists s
-> wellFormedBlock s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> nextImpliesBlockWasCut s
-> noDupMappedPaddrList s
-> In pdparent (getPartitions multiplexer s)
-> In idPDchild (getPartitions multiplexer s)
-> In idPDchild (getChildren pdparent s)
-> lookup idPDchild (memory s) beqAddr = Some(PDT pdentry)
-> pdparent = parent pdentry
-> idPDchild <> constantRootPartM
-> In blockParent (getMappedBlocks pdparent s)
-> In addr (getAllPaddrAux [block] s)
-> bentryStartAddr blockToRemove startaddr s
-> In startaddr (getAllPaddrAux [blockParent] s)
-> In block (blockToRemove::blocksList)
-> nullAddr = last blocksList blockToRemove
-> checkRemoveOkRec blockToRemove idPDchild blocksList s
-> In addr (getAllPaddrAux [blockParent] s).
Proof.
intros Hnull Hwell HequivParent HnextCut HnoDupPaddr HparentIsPart HchildIsPart HchildIsChild HlookupChild Hparent
  HbeqChildRoot HblockPMapped HaddrInBlock. unfold nullAddrExists in *. unfold isPADDR in *.
revert blockToRemove startaddr.
induction blocksList; cbn -[last nullAddr]; intros blockToRemove startaddr HstartBTR HstartInBP HblockInList Hlast
  HnextBlocksList.
{
  destruct HblockInList as [HbeqBlocks | Hcontra]; try(exfalso; congruence). subst block. simpl in *.
  subst blockToRemove. unfold bentryStartAddr in *. exfalso.
  destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
}
destruct HnextBlocksList as (HAflag & HPflag & HBTRMapped & HPDchild & Hnext & HpartialChildLoc & HnextBlocksListRec).
assert(HendBTR: exists endaddr, bentryEndAddr blockToRemove endaddr s).
{
  unfold bentryStartAddr in *. unfold bentryEndAddr.
  destruct (lookup blockToRemove (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
}
destruct HendBTR as [endaddr HendBTR]. apply IL.lastRec in Hlast.
specialize(HequivParent pdparent idPDchild blockToRemove startaddr endaddr HparentIsPart HchildIsChild HBTRMapped
  HstartBTR HendBTR HPflag).
destruct HequivParent as [blockPBis [startPBis [endPBis (HblockPBisMapped & HstartPBis & HendPBis & HlebStarts &
  HgebEnds)]]]. assert(HparentIsPDT: isPDT pdparent s).
{
  unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
  destruct (lookup pdparent (memory s) beqAddr); try(simpl in *; congruence).
  destruct v; try(simpl in *; congruence). trivial.
}
specialize(Hwell blockToRemove startaddr endaddr HPflag HstartBTR HendBTR). destruct Hwell as (Hwell & _).
assert(blockParent = blockPBis).
{
  destruct (beqAddr blockParent blockPBis) eqn:HbeqBPS; try(rewrite beqAddrTrue; assumption). exfalso.
  rewrite <-beqAddrFalse in *.
  pose proof (DisjointPaddrInPart pdparent blockParent blockPBis startaddr s HnoDupPaddr HparentIsPDT HblockPMapped
    HblockPBisMapped HbeqBPS HstartInBP) as Hcontra. contradict Hcontra. simpl.
  unfold bentryStartAddr in *. unfold bentryEndAddr in *.
  destruct (lookup blockPBis (memory s) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
  rewrite app_nil_r. rewrite <-HstartPBis. rewrite <-HendPBis. apply IL.getAllPaddrBlockIncl; lia.
}
subst blockPBis. destruct (lookup blockParent (memory s) beqAddr) eqn:HlookupBP; try(simpl in *; congruence).
destruct v; try(simpl in *; congruence). rewrite app_nil_r in *.
destruct HblockInList as [HbeqBlocks | HblockInListRec].
- subst block. simpl in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBP in *.
  destruct (lookup blockToRemove (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite <-HstartPBis. rewrite <-HendPBis. rewrite app_nil_r in *.
  rewrite <-HstartBTR in *. rewrite <-HendBTR in *. apply IL.getAllPaddrBlockInclRev in HaddrInBlock.
  destruct HaddrInBlock as (HlebStartAddr & HltAddrEnd & _). apply IL.getAllPaddrBlockIncl; lia.
- assert(HbeqANull: a <> nullAddr).
  {
    destruct blocksList; simpl in *.
    - subst a. exfalso. destruct HblockInListRec as [Hcontra | Hfalse]; try(congruence). subst block.
      destruct (lookup nullAddr (memory s) beqAddr); try(simpl in *; congruence).
      destruct v; simpl in *; congruence.
    - destruct HnextBlocksListRec as (HAflagA & _). intro Hcontra. subst a. unfold bentryAFlag in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  specialize(HpartialChildLoc HbeqANull). destruct HpartialChildLoc as (HAMapped & HpartialChildLoc).
  specialize(HpartialChildLoc endaddr HendBTR).
  assert(HeqTriv: CPaddr (blockToRemove+scoffset) = CPaddr (blockToRemove+scoffset)) by reflexivity.
  specialize(HnextCut idPDchild pdentry blockToRemove (CPaddr (blockToRemove+scoffset)) a endaddr HchildIsPart
    HlookupChild HBTRMapped HendBTR HeqTriv HbeqANull Hnext HbeqChildRoot).
  destruct HnextCut as [blockPTri [endPTri (HblockPTriMapped & HendPTri & HltEnds & Hincl)]].
  assert(blockParent = blockPTri).
  {
    destruct (beqAddr blockParent blockPTri) eqn:HbeqBPs; try(rewrite beqAddrTrue; assumption). exfalso.
    rewrite <-beqAddrFalse in *. rewrite <-Hparent in *.
    assert(HstartInBPCopy: In startaddr (getAllPaddrAux [blockParent] s)).
    { simpl. rewrite HlookupBP. rewrite app_nil_r. assumption. }
    pose proof (DisjointPaddrInPart pdparent blockParent blockPTri startaddr s HnoDupPaddr HparentIsPDT HblockPMapped
      HblockPTriMapped HbeqBPs HstartInBPCopy) as Hcontra. contradict Hcontra. apply Hincl. simpl.
    unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    destruct (lookup blockToRemove (memory s) beqAddr); try(simpl; congruence).
    destruct v; try(simpl; congruence). rewrite <-HstartBTR. rewrite <-HendBTR. rewrite app_nil_r.
    apply IL.getAllPaddrBlockIncl; lia.
  }
  subst blockPTri. assert(HendInBP: In endaddr (getAllPaddrAux [blockParent] s)).
  {
    simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBP in *. rewrite app_nil_r.
    rewrite <-HstartPBis. rewrite <-HendPTri. apply IL.getAllPaddrBlockIncl; lia.
  }
  specialize(IHblocksList a endaddr HpartialChildLoc HendInBP HblockInListRec Hlast HnextBlocksListRec).
  simpl in *. rewrite HlookupBP in *. rewrite app_nil_r in *. assumption.
Qed.

Lemma addrInRemovesRangeIsInAccBlock s idPDchild blockToRemove blocksList addr:
nullAddrExists s
-> In addr (getAllPaddrAux (blockToRemove::blocksList) s)
-> nullAddr = last blocksList blockToRemove
-> checkRemoveOkRec blockToRemove idPDchild blocksList s
-> exists blockC, In blockC (blockToRemove::blocksList) /\ bentryAFlag blockC true s
    /\ In addr (getAllPaddrAux [blockC] s).
Proof.
intro Hnull. unfold nullAddrExists in *. unfold isPADDR in *. revert blockToRemove. induction blocksList;
  cbn -[last nullAddr]; intros blockToRemove HaddrMapped Hlast HnextBlocksList.
{
  simpl in *. subst blockToRemove. exfalso. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
  destruct v; simpl in *; congruence.
}
destruct HnextBlocksList as (HAflag & HPflag & HBTRMapped & HPDchild & Hnext & HpartialChildLoc & HnextBlocksListRec).
unfold bentryPFlag in *. destruct (lookup blockToRemove (memory s) beqAddr) eqn:HlookupBTR; try(exfalso; congruence).
destruct v; try(exfalso; congruence). apply in_app_or in HaddrMapped.
destruct HaddrMapped as [HaddrInBTR | HaddrMappedRec].
- exists blockToRemove. split; auto. split; trivial. rewrite HlookupBTR. rewrite app_nil_r. assumption.
- apply IL.lastRec in Hlast. specialize(IHblocksList a HaddrMappedRec Hlast HnextBlocksListRec).
  destruct IHblocksList as [blockC (HblockCIn & HAflagC & HaddrInC)]. exists blockC. auto.
Qed.

Lemma isKSPreservedRemoveRecRev s s0 idPDchild blockToRemove statesList blocksList block:
isKS block s
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> isKS block s0. (*in fact, we even have lookup equality*)
Proof.
intro HblockIsKS. revert s0 blockToRemove blocksList.
induction statesList; simpl; intros s0 blockToRemove blocksList HblocksList.
- destruct HblocksList. subst s. assumption.
- destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBis & HPDT & HBTRMapped &
    HAflag & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
  apply IHstatesList in HblocksListRec. unfold isKS in *.
  destruct (beqAddr blockToRemove block) eqn:HbeqBlocks.
  + rewrite <-beqAddrTrue in HbeqBlocks. subst block.
    destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & HlookupA)]]]. rewrite Hlookups0. rewrite HlookupA in *.
    auto.
  + rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
    * intro Hcontra. subst block. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]]. rewrite HlookupA in *.
      congruence.
    * intro Hcontra. subst block. rewrite HSHE in *. congruence.
    * intro Hcontra. subst block. rewrite HSCE in *. congruence.
Qed.

Lemma getChildrenEqRemoveRec s s0 idPDchild blockToRemove statesList blocksList part:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> getChildren part s = getChildren part s0.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 HblocksList.
- destruct HblocksList. subst s0. reflexivity.
- destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBis & HPDT & HBTRMapped &
    HAflag & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
  assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold isSHE. unfold sh1entryPDchild in *.
    destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HsceIsSCE: isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold isSCE. unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HnoDupA: noDupKSEntriesList a).
  { revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial. }
  assert(HnullA: nullAddrExists a).
  { revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial. }
  assert(HnoDupMappedA: noDupMappedBlocksList a).
  { revert HlookupsEq. apply noDupMappedBlocksListPreservedRemove; trivial. }
  assert(HdisjointA: DisjointKSEntries a).
  { revert HlookupsEq. apply DisjointKSEntriesPreservedRemove; trivial. }
  assert(HwellSh1A: wellFormedFstShadowIfBlockEntry a).
  { revert HlookupsEq. apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial. }
  apply IHstatesList in HblocksListRec; trivial. rewrite HblocksListRec. revert HlookupsEq.
  apply getChildrenEqRemove; trivial.
Qed.

Lemma listsBlocksAreNotPresent s s0 idPDchild blockToRemove statesList blocksList block:
block <> nullAddr
-> In block (blockToRemove::blocksList)
-> NoDup (blockToRemove::blocksList)
-> nullAddr = last blocksList blockToRemove
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> bentryPFlag block false s.
Proof.
intro HbeqBlockNull. revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove
  blocksList HblockInList HnoDupList Hlast HblocksList.
- destruct HblocksList. subst blocksList. simpl in *. subst blockToRemove. exfalso. destruct HblockInList; congruence.
- destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBis & HPDT & HBTRMapped &
    HAflag & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
  apply NoDup_cons_iff in HnoDupList. destruct HnoDupList as (HBTRNotInList & HnoDupListRec).
  subst blocksList. apply IL.lastRec in Hlast. destruct (beqAddr blockToRemove block) eqn:HbeqBlocks.
  + rewrite <-beqAddrTrue in HbeqBlocks. subst block. destruct HBE as [bentry0 [l [newEnd (_ & _ & HlookupA)]]].
    assert(HlookupEq: lookup blockToRemove (memory s) beqAddr = lookup blockToRemove (memory a) beqAddr).
    {
      revert HblocksListRec. apply lookupBEEqRemoveRec; trivial. unfold isBE. rewrite HlookupA. trivial.
    }
    unfold bentryPFlag. rewrite HlookupEq. rewrite HlookupA. reflexivity.
  + rewrite <-beqAddrFalse in *. destruct HblockInList as [Hcontra | HblockInListRec]; try(exfalso; congruence).
    revert HblocksListRec. apply IHstatesList; trivial.
Qed.

Lemma blockInListNotShared blockToRemove idPDchild blocksList s block:
nullAddrExists s
-> block <> nullAddr
-> In block (blockToRemove::blocksList)
-> nullAddr = last blocksList blockToRemove
-> checkRemoveOkRec blockToRemove idPDchild blocksList s
-> sh1entryPDchild (CPaddr (block+sh1offset)) nullAddr s.
Proof.
intros Hnull HbeqBlockNull. revert blockToRemove. induction blocksList; cbn -[last nullAddr]; intros blockToRemove
  HblockInList Hlast HblocksList; try(simpl in *; exfalso; destruct HblockInList; congruence).
destruct HblocksList as (_ & _ & _ & HPDchild & _ & _ & HblocksList). apply IL.lastRec in Hlast.
destruct HblockInList.
- subst block. assumption.
- apply IHblocksList with a; trivial.
Qed.

Lemma lookupNoneEqRemoveRec s s0 idPDchild blockToRemove statesList blocksList addr:
lookup addr (memory s0) beqAddr = None
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> lookup addr (memory s) beqAddr = None.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList Hnone
  HblocksList; try(destruct HblocksList; subst s; assumption).
destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqBTRNull & HnextBis & HPDT & HBTRMapped &
  HAflag & HBE & HPDflag & HPDchild & HSHE & HSCE & HlookupsEq & HblocksListRec)]].
revert HblocksListRec. apply IHstatesList; trivial. rewrite HlookupsEq; trivial.
- intro Hcontra. subst addr. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. congruence.
- intro Hcontra. subst addr. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. congruence.
- intro Hcontra. subst addr. unfold sh1entryPDchild in *. rewrite Hnone in *. congruence.
- intro Hcontra. subst addr. unfold scentryNext in *. rewrite Hnone in *. congruence.
Qed.

Fixpoint removedBlockInDescRec s s0 idPart blockToRemove statesList blocksList parentsList :=
match statesList with
| [] => blocksList = [] /\ parentsList = [] /\ s = s0
| s1::statesListRec => exists blockChild childPart blocksListRec parentsListRec,
    blocksList = blockChild::blocksListRec
    /\ parentsList = childPart::parentsListRec
    /\ blockToRemove <> nullAddr
    /\ bentryAFlag blockToRemove true s0
    /\ In blockToRemove (getMappedBlocks idPart s0)
    /\ In idPart (getPartitions multiplexer s0)
    /\ (exists pdentry0 pdentry1, lookup idPart (memory s0) beqAddr = Some(PDT pdentry0)
        /\ lookup idPart (memory s1) beqAddr = Some(PDT pdentry1)
        /\ pdentry1 = {|
                        structure := structure pdentry0;
                        firstfreeslot := blockToRemove;
                        nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                        nbprepare := nbprepare pdentry0;
                        parent := parent pdentry0;
                        MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                        vidtAddr := vidtAddr pdentry0
                      |})
    /\ (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
          /\ pdentryFirstFreeSlot idPart newEnd s0
          /\ lookup blockToRemove (memory s1) beqAddr = Some(BE
              {|
                read := false;
                write := false;
                exec := false;
                present := false;
                accessible := false;
                blockindex := blockindex bentry0;
                blockrange := CBlock nullAddr newEnd;
                Hidx := l
              |}))
    /\ sh1entryPDflag (CPaddr (blockToRemove+sh1offset)) false s0
    /\ sh1entryPDchild (CPaddr (blockToRemove+sh1offset)) childPart s0
    /\ sh1entryInChildLocation (CPaddr (blockToRemove+sh1offset)) blockChild s0
    /\ scentryNext (CPaddr (blockToRemove+scoffset)) nullAddr s0
    /\ lookup (CPaddr (blockToRemove+sh1offset)) (memory s1) beqAddr
        = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
    /\ lookup (CPaddr (blockToRemove+scoffset)) (memory s1) beqAddr
        = Some(SCE {| origin := nullAddr; next := nullAddr |})
    /\ (forall addr, idPart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
        -> CPaddr (blockToRemove+scoffset) <> addr
        -> lookup addr (memory s1) beqAddr = lookup addr (memory s0) beqAddr)
    /\ removedBlockInDescRec s s1 childPart blockChild statesListRec blocksListRec parentsListRec
end.

Lemma isParentsListPreservedRemove s s0 partition block part parentsList:
(exists pdentry0 pdentry1, lookup partition (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup partition (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := block;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux block (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup block (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot partition newEnd s0
      /\ lookup block (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (block+sh1offset)) s0
-> lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (block+scoffset)) s0
-> lookup (CPaddr (block+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, partition <> addr -> block <> addr -> CPaddr (block+sh1offset) <> addr
    -> CPaddr (block+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isParentsList s parentsList part
-> isParentsList s0 parentsList part.
Proof.
intros HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. revert part.
induction parentsList; simpl; intros part HparentsList; trivial.
destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(exfalso; congruence). destruct v; try(exfalso; congruence).
assert(HaIsPDTs0: isPDT a s0).
{
  unfold isPDT. destruct (beqAddr partition a) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst a. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]].
    rewrite Hlookups0. trivial.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
    + rewrite HlookupA. trivial.
    + intro Hcontra. subst a. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. congruence.
    + intro Hcontra. subst a. congruence.
    + intro Hcontra. subst a. congruence.
}
unfold isPDT in *. destruct (lookup a (memory s0) beqAddr) eqn:HlookupAs; try(congruence).
destruct v; try(congruence).
destruct HparentsList as (HbeqPartRoot & [pdentry (HlookupPart & Hparent)] & HparentsList). split; trivial. split.
- destruct (beqAddr partition part) eqn:HbeqParts.
  + rewrite <-beqAddrTrue in HbeqParts. subst part.
    destruct HPDT as [pdentry0 [pdentrys (Hlookups0 & Hlookups & Hpdentrys)]]. exists pdentry0.
    rewrite HlookupPart in *. injection Hlookups as HpdentriesEq. subst pdentrys. rewrite Hpdentrys in Hparent.
    split; auto.
  + rewrite <-beqAddrFalse in *. exists pdentry. rewrite <-HlookupsEq; auto.
    * intro. subst part. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. congruence.
    * intro. subst part. congruence.
    * intro. subst part. congruence.
- apply IHparentsList; assumption.
Qed.

(*Lemma childLocMappedInChildPreservedRemove s s0 removePart blockToRemove:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> childLocMappedInChild s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> In blockToRemove (getMappedBlocks removePart s0)
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> childLocMappedInChild s.
Proof.
intros HnoDup Hnull HnoDupMapped Hdisjoint HlocProps HPDT HBTRMapped HBE HPDflagBTR HSHE HsceIsSCE
  HSCE HlookupsEq.
assert(Hsh1IsSHE: isSHE (CPaddr (blockToRemove + sh1offset)) s0).
{
  unfold sh1entryPDflag in *. unfold isSHE.
  destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(HgetPartsEqs: getPartitions multiplexer s = getPartitions multiplexer s0).
{ apply getPartitionsEqRemove with removePart blockToRemove; trivial. }
intros part block sh1entryaddr blockChild idchild HpartIsPart HblockMapped Hsh1 HPDchild HchildLoc HbeqChildNull.
rewrite HgetPartsEqs in *.
(*assert(HgetChildrenEq: getChildren part s = getChildren part s0).
{ apply getChildrenEqRemove with removePart blockToRemove; trivial. }
rewrite HgetChildrenEq in *.*)
assert(HblockMappeds0: In block (getMappedBlocks part s0)).
{
  destruct (beqAddr removePart part) eqn:HbeqParts.
  - rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getMappedBlocksEqRemPartRemove blockToRemove s s0
      removePart HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
    destruct Heqs as [leftList [rightList (Heqs & Heqs0)]]. rewrite Heqs0. rewrite Heqs in *. apply in_or_app.
    apply in_app_or in HblockMapped. destruct HblockMapped; auto. right. apply in_or_app. auto.
  - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=s)
      (removePart:=removePart); trivial.
}
assert(blockToRemove <> block).
{
  intro Hcontra. subst block. apply IL.mappedBlockIsBE in HblockMapped.
  destruct HblockMapped as [bentry (Hlookup & Hpres)]. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
  rewrite Hlookups in Hlookup. injection Hlookup as HbentriesEq. subst bentry. simpl in *. congruence.
}
unfold sh1entryAddr in *. unfold bentryStartAddr.
assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{
  apply HlookupsEq; trivial.
  - intro. subst block. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]]. rewrite Hlookups in *.
    congruence.
  - intro. subst block. rewrite HSHE in *. congruence.
  - intro. subst block. rewrite HSCE in *. congruence.
}
rewrite HlookupBlockEq in *. unfold sh1entryPDchild in *. unfold sh1entryInChildLocation in *.
assert(HlookupSh1Eq: lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
{
  apply HlookupsEq.
  - intro Hcontra. rewrite <-Hcontra in *. destruct HPDT as [_ [pdentry1 (_ & Hlookups & _)]]. rewrite Hlookups in *.
    congruence.
  - intro Hcontra. rewrite <-Hcontra in *. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
    rewrite Hlookups in *. congruence.
  - destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    subst sh1entryaddr. intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
    rewrite HcontraBis in *. unfold nullAddrExists in *. unfold isPADDR in *. unfold isSHE in *.
    destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  - intro Hcontra. rewrite <-Hcontra in *. rewrite HSCE in *. congruence.
}
rewrite HlookupSh1Eq in *.
assert(HchildLocs0: sh1entryInChildLocation sh1entryaddr blockChild s0).
{
  unfold sh1entryInChildLocation. destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). destruct HchildLoc as (HchildLocVal & HblockCIsBE). split; trivial.
  intro HbeqBlockCNull. specialize(HblockCIsBE HbeqBlockCNull). unfold isBE in *.
  destruct (beqAddr blockToRemove blockChild) eqn:HbeqBlocks.
  - rewrite <-beqAddrTrue in HbeqBlocks. subst blockToRemove. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]].
    rewrite Hlookups0. trivial.
  - rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
    + intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *.
      congruence.
    + intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. congruence.
    + intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
}
specialize(HlocProps part block sh1entryaddr blockChild idchild HpartIsPart HblockMappeds0 Hsh1 HPDchild HchildLocs0
  HbeqChildNull). destruct HlocProps as (HbeqBlockCNull & HblockCMappped & HstartsEq). split; trivial.
(*TODO false*)
Qed.*)

Definition cons2FreeRemove s :=
noDupMappedPaddrList s
/\ accessibleParentPaddrIsAccessibleIntoChild s
/\ sharedBlockPointsToChild s
/\ childsBlocksPropsInParent s
/\ noChildImpliesAddressesNotShared s
/\ kernelsAreNotAccessible s
/\ blockAndNextAreSideBySide s.
(*adressesRangePreservedIfOriginAndNextOk, parentBlocksBoundsIfNoNext and childLocMappedInChild false*)

Lemma isChildBlocksListEqRemove s0 s blocksList block removePart blockToRemove:
isPADDR nullAddr s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove + sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> ~In nullAddr blocksList
-> isChildBlocksList s blocksList block
-> isChildBlocksList s0 blocksList block.
Proof.
intros Hnull HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. revert block.
induction blocksList; simpl; intros block HnullNotIn HblocksList; trivial. apply Decidable.not_or in HnullNotIn.
destruct HnullNotIn as (HbeqANull & HnullNotIn).
destruct (beqAddr blockToRemove block) eqn:HbeqBlocks.
{
  rewrite <-beqAddrTrue in HbeqBlocks. subst block. destruct HBE as [bentry0 [l [newEnd (Hlookups0 & _ & Hlookups)]]].
  rewrite Hlookups in *. rewrite HSHE in *. exfalso. destruct HblocksList as (HchildLoc & _). simpl in *. congruence.
}
rewrite <-beqAddrFalse in *.
assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{
  apply HlookupsEq; trivial.
  - intro. subst block. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. congruence.
  - intro. subst block. rewrite HSHE in *. congruence.
  - intro. subst block. rewrite HSCE in *. congruence.
}
rewrite HlookupBlockEq in *. destruct (lookup block (memory s0) beqAddr); try(congruence).
destruct v; try(congruence).
assert(HlookupSh1Eq: lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
  = lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr).
{
  apply HlookupsEq.
  - intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *.
    congruence.
  - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
    rewrite Hlookups in *. congruence.
  - intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
    unfold isPADDR in *. unfold isSHE in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
  - intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
}
rewrite HlookupSh1Eq in *. destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence).
destruct v; try(congruence). destruct HblocksList as (HchildLoc & HlocIsBE & HblocksList). split; trivial. split.
- intro. specialize(HlocIsBE HbeqANull). unfold isBE in *. destruct (beqAddr blockToRemove a) eqn:HbeqBTRA.
  + rewrite <-beqAddrTrue in HbeqBTRA. rewrite HbeqBTRA in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _ )]]].
    rewrite Hlookups0. trivial.
  + rewrite <-beqAddrFalse in *. clear HchildLoc. rewrite <-HlookupsEq; trivial.
    * intro. subst a. destruct HPDT as [_ [Hpdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. congruence.
    * intro. subst a. rewrite HSHE in *. congruence.
    * intro. subst a. rewrite HSCE in *. congruence.
- apply IHblocksList; assumption.
Qed.

Lemma removeDescIsChildBlockList s s0 firstPart blockToRemove statesList blocksList parentsList:
isPADDR nullAddr s0
-> ~ In nullAddr blocksList
-> removedBlockInDescRec s s0 firstPart blockToRemove statesList blocksList parentsList
-> isChildBlocksList s0 blocksList blockToRemove.
Proof.
revert s0 firstPart blockToRemove blocksList parentsList.
induction statesList; simpl; intros s0 firstPart blockToRemove blocksList parentsList Hnull HnullNotIn HblocksList.
- destruct HblocksList. subst blocksList. simpl. trivial.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]]. rewrite HblocksList. rewrite HblocksList in HnullNotIn. simpl in *.
  assert(HBECopy: exists bentry0 l newEnd,
    lookup blockToRemove (memory s0) beqAddr = Some (BE bentry0)
    /\ pdentryFirstFreeSlot firstPart newEnd s0
    /\ lookup blockToRemove (memory a) beqAddr
         = Some (BE
                   {|
                     read := false;
                     write := false;
                     exec := false;
                     present := false;
                     accessible := false;
                     blockindex := blockindex bentry0;
                     blockrange := CBlock nullAddr newEnd;
                     Hidx := l
                   |})) by assumption.
  destruct HBE as [bentry0 [l [newEnd (Hlookups0 & HBE)]]]. rewrite Hlookups0. unfold sh1entryInChildLocation in *.
  destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). destruct HchildLoc. split; auto. split; trivial. apply Decidable.not_or in HnullNotIn.
  assert(isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold isSHE. unfold sh1entryPDflag in *.
    destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold isSCE. unfold scentryNext in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(isPADDR nullAddr a).
  { revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial. }
  destruct HnullNotIn as (HbeqBlockCNull & HnullNotIn). apply IHstatesList in HblocksListRec; trivial.
  revert HlookupsEq HnullNotIn HblocksListRec. apply isChildBlocksListEqRemove; trivial.
Qed.

Lemma isChildBlocksListEqRemoveNoBTR s0 s blocksList block removePart blockToRemove:
isPADDR nullAddr s0
-> (exists pdentry0 pdentry1, lookup removePart (memory s0) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s0) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s0
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> isSHE (CPaddr (blockToRemove + sh1offset)) s0
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> isSCE (CPaddr (blockToRemove+scoffset)) s0
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> ~In blockToRemove (block::blocksList)
-> isChildBlocksList s blocksList block
-> isChildBlocksList s0 blocksList block.
Proof.
intros Hnull HPDT HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq. revert block.
induction blocksList; simpl; intros block HBTRNotIn HblocksList; trivial. apply Decidable.not_or in HBTRNotIn.
destruct HBTRNotIn as (HbeqBlockBTR & HBTRNotIn). apply not_eq_sym in HbeqBlockBTR.
assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{
  apply HlookupsEq; trivial.
  - intro. subst block. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. congruence.
  - intro. subst block. rewrite HSHE in *. congruence.
  - intro. subst block. rewrite HSCE in *. congruence.
}
rewrite HlookupBlockEq in *. destruct (lookup block (memory s0) beqAddr); try(congruence).
destruct v; try(congruence).
assert(HlookupSh1Eq: lookup (CPaddr (block+sh1offset)) (memory s) beqAddr
  = lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr).
{
  apply HlookupsEq.
  - intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *.
    congruence.
  - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
    rewrite Hlookups in *. congruence.
  - intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
    unfold isPADDR in *. unfold isSHE in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
  - intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
}
rewrite HlookupSh1Eq in *. destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence).
destruct v; try(congruence). destruct HblocksList as (HchildLoc & HlocIsBE & HblocksList). split; trivial. split.
- intro HbeqANull. specialize(HlocIsBE HbeqANull). unfold isBE in *. destruct (beqAddr blockToRemove a) eqn:HbeqBTRA.
  + rewrite <-beqAddrTrue in HbeqBTRA. rewrite HbeqBTRA in *. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _ )]]].
    rewrite Hlookups0. trivial.
  + rewrite <-beqAddrFalse in *. clear HchildLoc. rewrite <-HlookupsEq; trivial.
    * intro. subst a. destruct HPDT as [_ [Hpdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. congruence.
    * intro. subst a. rewrite HSHE in *. congruence.
    * intro. subst a. rewrite HSCE in *. congruence.
- apply IHblocksList; assumption.
Qed.

Lemma nullNotInRemoveDesc lastBlock s s0 firstPart blockToRemove statesList blocksList parentsList:
lastBlock <> nullAddr
-> lastBlock = last blocksList blockToRemove
-> removedBlockInDescRec s s0 firstPart blockToRemove statesList blocksList parentsList
-> ~In nullAddr blocksList.
Proof.
intro HbeqLastNull. revert s0 firstPart blockToRemove blocksList parentsList.
induction statesList; simpl; intros s0 firstPart blockToRemove blocksList parentsList Hlast HblocksList.
- destruct HblocksList. subst blocksList. simpl. auto.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]]. rewrite HblocksList. rewrite HblocksList in Hlast. simpl.
  apply IL.lastRec in Hlast. apply Classical_Prop.and_not_or. split.
  + destruct statesList; simpl in *.
    * destruct HblocksListRec. subst blocksListRec. simpl in *. subst lastBlock. assumption.
    * destruct HblocksListRec as [_ [_ [_ [_ (_ & _ & Hres & _)]]]]. assumption.
  + revert HblocksListRec. apply IHstatesList; assumption.
Qed.

Lemma getPartitionsEqRemoveDesc s s0 firstPart blockToRemove statesList blocksList parentsList:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> removedBlockInDescRec s s0 firstPart blockToRemove statesList blocksList parentsList
-> getPartitions multiplexer s = getPartitions multiplexer s0.
Proof.
revert s0 firstPart blockToRemove blocksList parentsList.
induction statesList; simpl; intros s0 firstPart blockToRemove blocksList parentsList HnoDup Hnull HnoDupMapped
  Hdisjoint HwellSh1 HblocksList.
- destruct HblocksList as (_ & _ & Hs). subst s. reflexivity.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]]. assert(isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Heq: getPartitions multiplexer s0 = getPartitions multiplexer a).
  { apply eq_sym. revert HlookupsEq. apply getPartitionsEqRemove; trivial. }
  rewrite Heq. revert HblocksListRec. apply IHstatesList; trivial.
  + revert HlookupsEq. apply noDupKSEntriesListPreservedRemove; trivial.
  + revert HlookupsEq. apply nullAddrExistsPreservedRemove; trivial.
  + revert HlookupsEq. apply noDupMappedBlocksListPreservedRemove; trivial.
  + revert HlookupsEq. apply DisjointKSEntriesPreservedRemove; trivial.
  + revert HlookupsEq. apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial.
Qed.

Lemma getMappedBlocksEqRemoveDesc part s s0 firstPart blockToRemove statesList blocksList parentsList:
DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> ~In part (firstPart::parentsList)
-> removedBlockInDescRec s s0 firstPart blockToRemove statesList blocksList parentsList
-> getMappedBlocks part s = getMappedBlocks part s0.
Proof.
revert s0 firstPart blockToRemove blocksList parentsList.
induction statesList; simpl; intros s0 firstPart blockToRemove blocksList parentsList Hdisjoint HwellSh1
  HpartNotInList HblocksList.
- destruct HblocksList as (_ & _ & Hs). subst s. reflexivity.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]]. assert(isSCE (CPaddr (blockToRemove + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(isSHE (CPaddr (blockToRemove + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  apply Decidable.not_or in HpartNotInList. destruct HpartNotInList as (HbeqFirstPart & HpartNotInList).
  rewrite HparentsList in HpartNotInList.
  assert(Heq: getMappedBlocks part s0 = getMappedBlocks part a).
  { apply eq_sym. revert HlookupsEq HbeqFirstPart. apply getMappedBlocksEqRemove; trivial. }
  rewrite Heq. revert HblocksListRec. apply IHstatesList; trivial.
  + revert HlookupsEq. apply DisjointKSEntriesPreservedRemove; trivial.
  + revert HlookupsEq. apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial.
Qed.

Lemma isChildBlocksListRecR s blocksList block firstBlock blockDesc:
isBE block s
-> sh1entryInChildLocation (CPaddr (block+sh1offset)) blockDesc s
-> isChildBlocksList s blocksList firstBlock
-> block = last blocksList firstBlock
-> isChildBlocksList s (blocksList++[blockDesc]) firstBlock.
Proof.
intros HblockIsBE HchildLoc. unfold isBE in *. unfold sh1entryInChildLocation in *. revert firstBlock.
induction blocksList; cbn -[last nullAddr]; intros firstBlock HblocksList Hlast.
- simpl in *. subst block. destruct (lookup firstBlock (memory s) beqAddr); try(congruence).
  destruct v; try(congruence).
  destruct (lookup (CPaddr (firstBlock+sh1offset)) (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  destruct HchildLoc. auto.
- destruct (lookup firstBlock (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  destruct (lookup (CPaddr (firstBlock+sh1offset)) (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  destruct HblocksList as (HchildLocFirst & HlocFirstIsBE & HblocksList). split; trivial. split; trivial.
  apply IL.lastRec in Hlast. apply IHblocksList; trivial.
Qed.

Lemma lookupEqLastRemoveDesc s s0 lastBlock firstPart firstBlock statesList blocksList parentsList:
isBE lastBlock s
-> isSHE (CPaddr (lastBlock+sh1offset)) s
-> nullAddrExists s0
-> lastBlock = last blocksList firstBlock
-> NoDup (firstBlock::blocksList)
-> removedBlockInDescRec s s0 firstPart firstBlock statesList blocksList parentsList
-> lookup lastBlock (memory s) beqAddr = lookup lastBlock (memory s0) beqAddr
    /\ lookup (CPaddr (lastBlock+sh1offset)) (memory s) beqAddr
        = lookup (CPaddr (lastBlock+sh1offset)) (memory s0) beqAddr.
Proof.
intros HlastIsBE HlastSh1IsSHE. unfold isBE in *. unfold isSHE in *.
revert s0 firstPart firstBlock blocksList parentsList.
induction statesList; simpl; intros s0 firstPart firstBlock blocksList parentsList Hnull Hlast HnoDup HblocksList.
- destruct HblocksList as (_ & _ & Hs). subst s. auto.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]]. rewrite HblocksList in *. apply NoDup_cons_iff in HnoDup.
  destruct HnoDup as (HfirstNotIn & HnoDup). assert(HlastInList: In lastBlock (blockChild::blocksListRec)).
  { apply IL.lastOfNotEmptyIsIn with firstBlock; assumption. }
  assert(isSCE (CPaddr (firstBlock + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (firstBlock+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(isSHE (CPaddr (firstBlock + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (firstBlock+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(nullAddrExists a) by (revert HlookupsEq; apply nullAddrExistsPreservedRemove; trivial).
  apply IL.lastRec in Hlast. apply IHstatesList in HblocksListRec; trivial. unfold nullAddrExists in *.
  destruct HblocksListRec as (HlookupLastEq & HlookupLastSh1Eq).
  rewrite HlookupLastEq in *. rewrite HlookupLastSh1Eq in *. assert(firstBlock <> lastBlock).
  { intro. subst firstBlock. congruence. }
  assert(CPaddr (firstBlock + sh1offset) <> CPaddr (lastBlock + sh1offset)).
  {
    intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
    unfold isPADDR in *. rewrite HSHE in *. congruence.
  }
  split; apply HlookupsEq; trivial.
  + intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentryA (_ & HlookupA & _)]]. rewrite HlookupA in *.
    congruence.
  + intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. congruence.
  + intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
  + intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentryA (_ & HlookupA & _)]]. rewrite HlookupA in *.
    congruence.
  + intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & HlookupA)]]].
    rewrite HlookupA in *. congruence.
  + intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
Qed.

Lemma isBEPreservedRemoveDescRev s s0 block firstPart firstBlock statesList blocksList parentsList:
isBE block s
-> removedBlockInDescRec s s0 firstPart firstBlock statesList blocksList parentsList
-> isBE block s0.
Proof.
intro HblockIsBE. revert s0 firstPart firstBlock blocksList parentsList.
induction statesList; simpl; intros s0 firstPart firstBlock blocksList parentsList HblocksList.
- destruct HblocksList as (_ & _ & Hs). subst s. assumption.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]]. apply IHstatesList in HblocksListRec. unfold isBE in *.
  destruct (beqAddr firstBlock block) eqn:HbeqBlocks.
  + rewrite <-beqAddrTrue in HbeqBlocks. subst block. destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]].
    rewrite Hlookups0. trivial.
  + rewrite <-beqAddrFalse in *. rewrite <-HlookupsEq; trivial.
    * intro. subst block. destruct HPDT as [_ [pdentryA (_ & HlookupA & _)]]. rewrite HlookupA in *. congruence.
    * intro. subst block. rewrite HSHE in *. congruence.
    * intro. subst block. rewrite HSCE in *. congruence.
Qed.

Lemma absentBlocksEqRemoveDescRev s s0 block firstPart firstBlock statesList blocksList parentsList:
bentryPFlag block false s0
-> removedBlockInDescRec s s0 firstPart firstBlock statesList blocksList parentsList
-> bentryPFlag block false s.
Proof.
revert s0 firstPart firstBlock blocksList parentsList.
induction statesList; simpl; intros s0 firstPart firstBlock blocksList parentsList HPflag HblocksList.
- destruct HblocksList as (_ & _ & Hs). subst s. assumption.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]]. revert HblocksListRec. apply IHstatesList. unfold bentryPFlag in *.
  destruct (beqAddr firstBlock block) eqn:HbeqBlocks.
  + rewrite <-beqAddrTrue in HbeqBlocks. subst block. destruct HBE as [bentry0 [l [newEnd (_ & _ & HlookupA)]]].
    rewrite HlookupA. reflexivity.
  + rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
    * intro. subst block. destruct HPDT as [pdentry0 [_ (Hlookups0 & _)]]. rewrite Hlookups0 in *. congruence.
    * intro. subst block. unfold sh1entryPDchild in *.
      destruct (lookup (CPaddr (firstBlock+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    * intro. subst block. unfold scentryNext in *.
      destruct (lookup (CPaddr (firstBlock+scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
Qed.

Lemma blocksNotPresentAfterRemoveDesc s s0 block firstPart firstBlock statesList blocksList parentsList:
In block (firstBlock::blocksList)
-> blocksList <> []
-> block <> last blocksList firstBlock
-> removedBlockInDescRec s s0 firstPart firstBlock statesList blocksList parentsList
-> bentryPFlag block false s.
Proof.
revert s0 firstPart firstBlock blocksList parentsList.
induction statesList; simpl; intros s0 firstPart firstBlock blocksList parentsList HblockIn HlistNotEmpty
  HblockNotLast HblocksList.
{ destruct HblocksList. exfalso; congruence. }
destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
  HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
  HSCE & HlookupsEq & HblocksListRec)]]]]. simpl in *. subst blocksList.
assert(HeqLast: last (blockChild :: blocksListRec) firstBlock = last blocksListRec blockChild).
{ apply IL.lastRec with firstBlock. reflexivity. }
rewrite HeqLast in *.
destruct (beqAddr firstBlock block) eqn:HbeqBlocks.
- rewrite <-beqAddrTrue in HbeqBlocks. subst block. revert HblocksListRec. apply absentBlocksEqRemoveDescRev.
  unfold bentryPFlag. destruct HBE as [bentry0 [l [newEnd (_ & _ & HlookupA)]]]. rewrite HlookupA. reflexivity.
- rewrite <-beqAddrFalse in *. destruct HblockIn as [Hcontra | HblockIn]; try(exfalso; congruence).
  destruct blocksListRec eqn:HeqBlocksList.
  { simpl in *. exfalso. destruct HblockIn; congruence. }
  rewrite <-HeqBlocksList in *. assert(HlistNotEmptyRec: blocksListRec <> []).
  { intro Hcontra. rewrite Hcontra in *. congruence. }
  revert HblocksListRec. apply IHstatesList; trivial.
Qed.

Lemma penWasMappedRemoveDesc s s0 firstPart firstBlock statesList blocksList parentsList block:
noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> In block (firstBlock::blocksList)
-> block <> last blocksList firstBlock
-> removedBlockInDescRec s s0 firstPart firstBlock statesList blocksList parentsList
-> exists part, In part (firstPart::parentsList) /\ In part (getPartitions multiplexer s0)
    /\ In block (getMappedBlocks part s0).
Proof.
revert s0 firstPart firstBlock blocksList parentsList.
induction statesList; simpl in *; intros s0 firstPart firstBlock blocksList parentsList HnoDup Hnull HnoDupMapped
  Hdisjoint HwellSh1 HblockIn HblockNotLast HblocksList.
{ exfalso. destruct HblocksList. subst blocksList. simpl in *. destruct HblockIn; congruence. }
destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
  HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
  HSCE & HlookupsEq & HblocksListRec)]]]].
assert(Heq: last blocksList firstBlock = last blocksListRec blockChild).
{ rewrite HblocksList. apply IL.lastRec with firstBlock; trivial. }
assert(HsceIsSCE: isSCE (CPaddr (firstBlock + scoffset)) s0).
{
  unfold scentryNext in *. unfold isSCE.
  destruct (lookup (CPaddr (firstBlock+scoffset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(Hsh1IsSHE: isSHE (CPaddr (firstBlock + sh1offset)) s0).
{
  unfold sh1entryPDflag in *. unfold isSHE.
  destruct (lookup (CPaddr (firstBlock+sh1offset)) (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
assert(nullAddrExists a) by (revert HlookupsEq; apply nullAddrExistsPreservedRemove; trivial).
assert(noDupKSEntriesList a) by (revert HlookupsEq; apply noDupKSEntriesListPreservedRemove; trivial).
assert(noDupMappedBlocksList a) by (revert HlookupsEq; apply noDupMappedBlocksListPreservedRemove; trivial).
assert(DisjointKSEntries a) by (revert HlookupsEq; apply DisjointKSEntriesPreservedRemove; trivial).
assert(wellFormedFstShadowIfBlockEntry a)
  by (revert HlookupsEq; apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial).
rewrite Heq in *. destruct (beqAddr firstBlock block) eqn:HbeqBlocks.
- rewrite <-beqAddrTrue in HbeqBlocks. subst block. exists firstPart. auto.
- rewrite <-beqAddrFalse in *. destruct HblockIn as [Hcontra | HblockIn]; try(exfalso; congruence).
  subst blocksList. apply IHstatesList in HblocksListRec; trivial.
  destruct HblocksListRec as [part (HpartIn & HpartBIsPart & HblockMapped)]. exists part. subst parentsList.
  split; auto. assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
  { revert HlookupsEq. apply getPartitionsEqRemove; trivial. }
  rewrite HgetPartsEq in *. split; trivial. destruct (beqAddr firstPart part) eqn:HbeqParts.
  + rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getMappedBlocksEqRemPartRemove firstBlock a s0
      firstPart HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
    destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite HeqA in *. rewrite Heqs0. apply in_or_app.
    apply in_app_or in HblockMapped. destruct HblockMapped; auto. right. apply in_or_app. auto.
  + rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=firstBlock) (s:=a)
      (removePart:=firstPart); trivial.
Qed.

Lemma penBlocksListIsParentOfLast s blocksList lastBlock firstBlock:
isChildBlocksList s (blocksList ++ [lastBlock]) firstBlock
-> sh1entryInChildLocation (CPaddr ((last blocksList firstBlock)+sh1offset)) lastBlock s.
Proof.
revert firstBlock. induction blocksList; cbn -[last nullAddr]; intros firstBlock HblocksList.
- simpl. destruct (lookup firstBlock (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). unfold sh1entryInChildLocation.
  destruct (lookup (CPaddr (firstBlock+sh1offset)) (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  intuition.
- assert(Heq: last (a :: blocksList) firstBlock = last blocksList a).
  { apply IL.lastRec with firstBlock; reflexivity. }
  rewrite Heq. destruct (lookup firstBlock (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  destruct (lookup (CPaddr (firstBlock+sh1offset)) (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). destruct HblocksList as (_ & _ & HblocksList). apply IHblocksList; assumption.
Qed.

Lemma getMappedBlocksImplRemoveDesc s s0 firstPart firstBlock statesList blocksList parentsList block part:
In block (getMappedBlocks part s)
-> noDupKSEntriesList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> removedBlockInDescRec s s0 firstPart firstBlock statesList blocksList parentsList
-> In block (getMappedBlocks part s0).
Proof.
intro HblockMapped. revert s0 firstPart firstBlock blocksList parentsList.
induction statesList; simpl in *; intros s0 firstPart firstBlock blocksList parentsList HnoDup Hdisjoint HwellSh1
  HblocksList.
- destruct HblocksList as (_ & _ & Hs). subst s. assumption.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]].
  assert(HsceIsSCE: isSCE (CPaddr (firstBlock + scoffset)) s0).
  {
    unfold scentryNext in *. unfold isSCE.
    destruct (lookup (CPaddr (firstBlock+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(Hsh1IsSHE: isSHE (CPaddr (firstBlock + sh1offset)) s0).
  {
    unfold sh1entryPDflag in *. unfold isSHE.
    destruct (lookup (CPaddr (firstBlock+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(noDupKSEntriesList a) by (revert HlookupsEq; apply noDupKSEntriesListPreservedRemove; trivial).
  assert(DisjointKSEntries a) by (revert HlookupsEq; apply DisjointKSEntriesPreservedRemove; trivial).
  assert(wellFormedFstShadowIfBlockEntry a)
    by (revert HlookupsEq; apply wellFormedFstShadowIfBlockEntryPreservedRemove; trivial).
  apply IHstatesList in HblocksListRec; trivial.
  destruct (beqAddr firstPart part) eqn:HbeqParts.
  + rewrite <-beqAddrTrue in HbeqParts. subst part.
    pose proof (getMappedBlocksEquivRemove firstBlock a s0 firstPart HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE
      HsceIsSCE HSCE HlookupsEq) as Hres. destruct Hres as (Hres & _). specialize(Hres block). apply Hres. simpl.
    auto.
  + rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=firstBlock) (s:=a)
      (removePart:=firstPart); trivial.
Qed.

Lemma lookupSh1EqRemoveDesc s s0 firstPart firstBlock statesList blocksList parentsList sh1entryaddr child:
sh1entryPDchild sh1entryaddr child s
-> child <> nullAddr
-> removedBlockInDescRec s s0 firstPart firstBlock statesList blocksList parentsList
-> lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr.
Proof.
intros HPDchilds HbeqChildNull. revert s0 firstPart firstBlock blocksList parentsList.
induction statesList; simpl in *; intros s0 firstPart firstBlock blocksList parentsList HblocksList.
- destruct HblocksList as (_ & _ & Hs). subst s. reflexivity.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqBTRNull & HAflag & HBTRMapped & HpartIsPart & HPDT & HBE & HPDflag & HPDchild & HchildLoc & Hnext & HSHE &
    HSCE & HlookupsEq & HblocksListRec)]]]]. apply IHstatesList in HblocksListRec. unfold sh1entryPDchild in *.
  rewrite HblocksListRec in *. apply HlookupsEq.
  + intro. subst sh1entryaddr. destruct HPDT as [_ [pdentryA (_ & HlookupA & _)]]. rewrite HlookupA in *. congruence.
  + intro. subst sh1entryaddr. destruct HBE as [bentry0 [l [newEnd (_ & _ & HlookupA)]]]. rewrite HlookupA in *.
    congruence.
  + intro. subst sh1entryaddr. rewrite HSHE in *. simpl in *. congruence.
  + intro. subst sh1entryaddr. rewrite HSCE in *. congruence.
Qed.

Lemma removedBlockInDescRecRec s s1 s0 firstPart firstBlockToRemove statesList blocksList parentsList removePart
  blockToRemove child blockToRemoveInDescendant:
(exists pdentry0 pdentry1, lookup removePart (memory s1) beqAddr = Some(PDT pdentry0)
      /\ lookup removePart (memory s) beqAddr = Some(PDT pdentry1)
      /\ pdentry1 = {|
                      structure := structure pdentry0;
                      firstfreeslot := blockToRemove;
                      nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                      nbprepare := nbprepare pdentry0;
                      parent := parent pdentry0;
                      MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                      vidtAddr := vidtAddr pdentry0
                    |})
-> (exists bentry0 l newEnd, lookup blockToRemove (memory s1) beqAddr = Some(BE bentry0)
      /\ pdentryFirstFreeSlot removePart newEnd s1
      /\ lookup blockToRemove (memory s) beqAddr = Some(BE
          {|
            read := false;
            write := false;
            exec := false;
            present := false;
            accessible := false;
            blockindex := blockindex bentry0;
            blockrange := CBlock nullAddr newEnd;
            Hidx := l
          |}))
-> lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
-> lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})
-> (forall addr, removePart <> addr -> blockToRemove <> addr -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s1) beqAddr)
-> blockToRemove <> nullAddr
-> In blockToRemove (getMappedBlocks removePart s1)
-> In removePart (getPartitions multiplexer s1)
-> bentryAFlag blockToRemove true s1
-> sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s1
-> sh1entryPDchild (CPaddr (blockToRemove + sh1offset)) child s1
-> sh1entryInChildLocation (CPaddr (blockToRemove + sh1offset)) blockToRemoveInDescendant s1
-> scentryNext (CPaddr (blockToRemove + scoffset)) nullAddr s1
-> removePart = last parentsList firstPart
-> blockToRemove = last blocksList firstBlockToRemove
-> removedBlockInDescRec s1 s0 firstPart firstBlockToRemove statesList blocksList parentsList
-> removedBlockInDescRec s s0 firstPart firstBlockToRemove (statesList++[s]) (blocksList++[blockToRemoveInDescendant])
     (parentsList++[child]).
Proof.
intros HPDT HBE HSHE HSCE HlookupsEq HbeqBTRNull HBTRMapped HremPartIsPart HAflagBTR HPDflagBTR HPDchildBTR
  HlocBTR HnextBTR. revert s0 firstPart firstBlockToRemove blocksList parentsList.
induction statesList; simpl; intros s0 firstPart firstBlockToRemove blocksList parentsList HlastPart HlastBlock
  HblocksList.
- destruct HblocksList as (HblockEq & HparentEq & Hs). subst blocksList. subst parentsList. subst s1. simpl in *.
  subst blockToRemove. subst removePart. exists blockToRemoveInDescendant. exists child. exists []. exists [].
  intuition.
- destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList &
    HbeqFBTRNull & HAflag & HFBTRMapped & HpartIsPart & HPDTF & HBEF & HPDflag & HPDchild & HchildLoc & Hnext & HSHEF
    & HSCEF & HlookupsEqF & HblocksListRec)]]]]. subst blocksList. subst parentsList. apply IL.lastRec in HlastPart.
  apply IL.lastRec in HlastBlock. apply IHstatesList in HblocksListRec; trivial.
  exists blockChild. exists childPart. exists (blocksListRec++[blockToRemoveInDescendant]).
  exists (parentsListRec++[child]). intuition.
Qed.

Lemma removeBlockInDescendantsRecAux n idPart blockToRemove firstPart firstBlockToRemove (P: state -> Prop):
{{
  fun s => (forall childrenList, isChildBlocksList s childrenList blockToRemove
      -> length childrenList < n)
    /\ cons1Free s
    /\ cons2FreeRemove s
    /\ partitionsIsolation s
    /\ kernelDataIsolation s
    /\ ((blockToRemove = nullAddr /\ idPart = nullAddr)
          \/ (In idPart (getPartitions multiplexer s) /\ In blockToRemove (getMappedBlocks idPart s)
              /\ bentryAFlag blockToRemove true s))
    /\ (exists statesList blocksList parentsList s0,
          removedBlockInDescRec s s0 firstPart firstBlockToRemove statesList blocksList parentsList
          /\ blockToRemove = last blocksList firstBlockToRemove
          /\ idPart = last parentsList firstPart
          (*/\ isParentsList s (tl parentsList++[firstPart]) idPart*)
          /\ P s0
          /\ consistency s0
          /\ partitionsIsolation s0
          /\ kernelDataIsolation s0
          /\ verticalSharing s0
          /\ In firstPart (getPartitions multiplexer s0)
          /\ In firstBlockToRemove (getMappedBlocks firstPart s0))
    /\ (forall part block scnext,
          In part (getPartitions multiplexer s)
          -> In block (getMappedBlocks part s)
          -> scentryNext (CPaddr (block + scoffset)) scnext s
          -> scnext <> nullAddr -> blockToRemove <> scnext)
    /\ (forall partition block sh1entryaddr blockChild idchild,
          firstBlockToRemove <> blockChild
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> sh1entryAddr block sh1entryaddr s
          -> sh1entryPDchild sh1entryaddr idchild s
          -> sh1entryInChildLocation sh1entryaddr blockChild s
          -> idchild <> nullAddr
          -> blockChild <> nullAddr /\ In blockChild (getMappedBlocks idchild s)
              /\ (forall startaddr : paddr, bentryStartAddr block startaddr s
                  -> bentryStartAddr blockChild startaddr s))
    /\ (forall partition pdentry block scentryaddr start endaddr,
          blockToRemove <> block
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> isBE block s
          -> bentryStartAddr block start s
          -> bentryEndAddr block endaddr s
          -> bentryPFlag block true s
          -> scentryaddr = CPaddr (block + scoffset)
          -> scentryOrigin scentryaddr start s
          -> scentryNext scentryaddr nullAddr s
          -> lookup partition (memory s) beqAddr = Some (PDT pdentry)
          -> partition <> constantRootPartM
          -> exists blockParent,
              In blockParent (getMappedBlocks (parent pdentry) s) /\ isBE blockParent s
              /\ bentryStartAddr blockParent start s /\ bentryEndAddr blockParent endaddr s)
    /\ (forall partition pdentry block scentryaddr startaddr endaddr,
          blockToRemove <> block
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> bentryStartAddr block startaddr s
          -> bentryEndAddr block endaddr s
          -> scentryaddr = CPaddr (block + scoffset)
          -> scentryNext scentryaddr nullAddr s
          -> partition <> constantRootPartM
          -> lookup partition (memory s) beqAddr = Some (PDT pdentry)
          -> exists blockParent startParent,
              In blockParent (getMappedBlocks (parent pdentry) s) /\ bentryStartAddr blockParent startParent s
              /\ bentryEndAddr blockParent endaddr s /\ startParent <= startaddr)
    /\ (forall parent child, In parent (getPartitions multiplexer s)
          -> In child (getChildren parent s)
          -> forall addr,
              (idPart <> child \/ ~In addr (getAllPaddrAux [blockToRemove] s))
              -> In addr (getUsedPaddr child s)
              -> In addr (getMappedPaddr parent s))
    /\ (forall parent child block startChild endChild,
          blockToRemove <> block
          -> In parent (getPartitions multiplexer s)
          -> In child (getChildren parent s)
          -> In block (getMappedBlocks child s)
          -> bentryStartAddr block startChild s
          -> bentryEndAddr block endChild s
          -> bentryPFlag block true s
          -> exists blockParent startParent endParent,
              In blockParent (getMappedBlocks parent s)
              /\ bentryStartAddr blockParent startParent s
              /\ bentryEndAddr blockParent endParent s /\ startParent <= startChild /\ endParent >= endChild)
}}
removeBlockInDescendantsRecAux n idPart blockToRemove
{{
  fun removeBlockDescEnded s => cons1Free s /\ cons2FreeRemove s
    /\ partitionsIsolation s
    /\ kernelDataIsolation s
    /\ verticalSharing s
    /\ (exists statesList blocksList parentsList s0,
          removedBlockInDescRec s s0 firstPart firstBlockToRemove statesList blocksList parentsList
          /\ nullAddr = last blocksList firstBlockToRemove
          (*/\ (exists lastPart, isParentsList s (tl parentsList++[firstPart]) lastPart)*)
          /\ P s0
          /\ consistency s0
          /\ partitionsIsolation s0
          /\ kernelDataIsolation s0
          /\ verticalSharing s0
          /\ In firstPart (getPartitions multiplexer s0)
          /\ In firstBlockToRemove (getMappedBlocks firstPart s0))
    /\ removeBlockDescEnded = true
    /\ (forall partition block sh1entryaddr blockChild idchild,
          firstBlockToRemove <> blockChild
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> sh1entryAddr block sh1entryaddr s
          -> sh1entryPDchild sh1entryaddr idchild s
          -> sh1entryInChildLocation sh1entryaddr blockChild s
          -> idchild <> nullAddr
          -> blockChild <> nullAddr /\ In blockChild (getMappedBlocks idchild s)
              /\ (forall startaddr, bentryStartAddr block startaddr s
                  -> bentryStartAddr blockChild startaddr s))
    /\ adressesRangePreservedIfOriginAndNextOk s
    /\ parentBlocksBoundsIfNoNext s
    /\ blockInChildHasAtLeastEquivalentBlockInParent s
}}.
Proof.
revert idPart blockToRemove. induction n; simpl; intros.
{
  eapply weaken. apply WP.ret. intros s Hprops. simpl. exfalso.
  destruct Hprops as (HlenProp & _).
  assert(HchildrenTriv: isChildBlocksList s [] blockToRemove) by (simpl; trivial).
  specialize(HlenProp [] HchildrenTriv). simpl in *. lia.
}
eapply bindRev.
{ (** Internal.compareAddrToNull **)
  eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
}
intro isNull. destruct isNull.
+ (* case isNull = true *)
  eapply weaken. apply WP.ret. intros s Hprops. simpl.
  destruct Hprops as ((_ & Hcons1 & Hcons2 & HPI & HKDI & _ & [statesList [blocksList [parentsList [s0 (HblocksList
    & HlastBlock & HlastParent & HP & Hconsists0 & HPIs0 & HKDIs0 & HVSs0 & HfirstBMapped)]]]] & _ & HlocPropsPartial
    & HrangePartial & HboundsNoNextPartial & HVSPartial & HparentEquivPartial) & HbeqNullBTR).
  rewrite <-beqAddrTrue in HbeqNullBTR. rewrite <-HbeqNullBTR in *. split; trivial. split; trivial. split; trivial.
  split; trivial. split; try(split).
  * intros pdparent child HparentIsPart HchildIsChild addr HaddrUsedChild.
    assert(HnotSpecialCase: idPart <> child \/ ~In addr (getAllPaddrAux [nullAddr] s)).
    {
      simpl. right. assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition). unfold isPADDR in *. intro.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; simpl in *; congruence.
    }
    specialize(HVSPartial pdparent child HparentIsPart HchildIsChild addr HnotSpecialCase HaddrUsedChild).
    assumption.
  * exists statesList. exists blocksList. exists parentsList. exists s0. intuition.
  * split; trivial. split; trivial. split; try(split).
    --- intros part pdentry block scentryaddr start endaddr HpartIsPart HblockMapped. assert(nullAddr <> block).
        {
          assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition). unfold isPADDR in *. intro. subst block.
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
          rewrite Hlookup in *. congruence.
        }
        apply HrangePartial; trivial.
    --- intros part pdentry block scentryaddr start endaddr HpartIsPart HblockMapped. assert(nullAddr <> block).
        {
          assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition). unfold isPADDR in *. intro. subst block.
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
          rewrite Hlookup in *. congruence.
        }
        apply HboundsNoNextPartial; trivial.
    --- intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMapped.
        assert(HbeqNullBlock: nullAddr <> block).
        {
          assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition). unfold isPADDR in *. intro. subst block.
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
          rewrite Hlookup in *. congruence.
        }
        apply HparentEquivPartial with child; assumption.
+ (* case isNull = false *)
  eapply bindRev.
  { (** MAL.readSh1PDChildFromBlockEntryAddr **)
    eapply weaken. apply readSh1PDChildFromBlockEntryAddr. intros s Hprops. simpl.
    destruct Hprops as ((HlenProp & Hcons1 & Hcons2 & HPI & HKDI & Hprops1 & Hprops2 & Hpartials) & HbeqNullBTR).
    rewrite <-beqAddrFalse in HbeqNullBTR.
    destruct Hprops1 as [(Hcontra & _) | (HidIsPart & HBTRMapped & HAflagBTR)]; try(exfalso; congruence).
    instantiate(1 := fun s =>
      (forall childrenList, isChildBlocksList s childrenList blockToRemove
        -> length childrenList < S n)
      /\ cons1Free s
      /\ cons2FreeRemove s
      /\ partitionsIsolation s
      /\ kernelDataIsolation s
      /\ In idPart (getPartitions multiplexer s)
      /\ In blockToRemove (getMappedBlocks idPart s)
      /\ bentryAFlag blockToRemove true s
      /\ sh1entryPDflag (CPaddr (blockToRemove+sh1offset)) false s
      /\ (exists statesList blocksList parentsList s0,
           removedBlockInDescRec s s0 firstPart firstBlockToRemove statesList blocksList parentsList
           /\ blockToRemove = last blocksList firstBlockToRemove
           /\ idPart = last parentsList firstPart
           (*/\ isParentsList s (tl parentsList ++ [firstPart]) idPart*)
           /\ P s0 /\ consistency s0
           /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
           /\ In firstPart (getPartitions multiplexer s0)
           /\ In firstBlockToRemove (getMappedBlocks firstPart s0))
      /\ blockToRemove <> nullAddr
      /\ (forall part block scnext,
            In part (getPartitions multiplexer s)
            -> In block (getMappedBlocks part s)
            -> scentryNext (CPaddr (block + scoffset)) scnext s
            -> scnext <> nullAddr -> blockToRemove <> scnext)
      /\ (forall partition block sh1entryaddr blockChild idchild,
            firstBlockToRemove <> blockChild
            -> In partition (getPartitions multiplexer s)
            -> In block (getMappedBlocks partition s)
            -> sh1entryAddr block sh1entryaddr s
            -> sh1entryPDchild sh1entryaddr idchild s
            -> sh1entryInChildLocation sh1entryaddr blockChild s
            -> idchild <> nullAddr
            -> blockChild <> nullAddr /\ In blockChild (getMappedBlocks idchild s)
                /\ (forall startaddr : paddr, bentryStartAddr block startaddr s
                    -> bentryStartAddr blockChild startaddr s))
      /\ (forall partition pdentry block scentryaddr start endaddr,
            blockToRemove <> block
            -> In partition (getPartitions multiplexer s)
            -> In block (getMappedBlocks partition s)
            -> isBE block s
            -> bentryStartAddr block start s
            -> bentryEndAddr block endaddr s
            -> bentryPFlag block true s
            -> scentryaddr = CPaddr (block + scoffset)
            -> scentryOrigin scentryaddr start s
            -> scentryNext scentryaddr nullAddr s
            -> lookup partition (memory s) beqAddr = Some (PDT pdentry)
            -> partition <> constantRootPartM
            -> exists blockParent,
                In blockParent (getMappedBlocks (parent pdentry) s) /\ isBE blockParent s
                /\ bentryStartAddr blockParent start s /\ bentryEndAddr blockParent endaddr s)
      /\ (forall partition pdentry block scentryaddr startaddr endaddr,
            blockToRemove <> block
            -> In partition (getPartitions multiplexer s)
            -> In block (getMappedBlocks partition s)
            -> bentryStartAddr block startaddr s
            -> bentryEndAddr block endaddr s
            -> scentryaddr = CPaddr (block + scoffset)
            -> scentryNext scentryaddr nullAddr s
            -> partition <> constantRootPartM
            -> lookup partition (memory s) beqAddr = Some (PDT pdentry)
            -> exists blockParent startParent,
                In blockParent (getMappedBlocks (parent pdentry) s) /\ bentryStartAddr blockParent startParent s
                /\ bentryEndAddr blockParent endaddr s /\ startParent <= startaddr)
      /\ (forall parent child, In parent (getPartitions multiplexer s)
            -> In child (getChildren parent s)
            -> forall addr,
                (idPart <> child \/ ~In addr (getAllPaddrAux [blockToRemove] s))
                -> In addr (getUsedPaddr child s)
                -> In addr (getMappedPaddr parent s))
      /\ (forall parent child block startChild endChild,
            blockToRemove <> block
            -> In parent (getPartitions multiplexer s)
            -> In child (getChildren parent s)
            -> In block (getMappedBlocks child s)
            -> bentryStartAddr block startChild s
            -> bentryEndAddr block endChild s
            -> bentryPFlag block true s
            -> exists blockParent startParent endParent,
                In blockParent (getMappedBlocks parent s)
                /\ bentryStartAddr blockParent startParent s
                /\ bentryEndAddr blockParent endParent s /\ startParent <= startChild /\ endParent >= endChild)).
    assert(HaccNoPDf: AccessibleNoPDFlag s) by (unfold cons1Free in *; intuition).
    assert(HBTR: isBE blockToRemove s /\ sh1entryAddr blockToRemove (CPaddr (blockToRemove+sh1offset)) s).
    {
      unfold bentryAFlag in *. unfold isBE. unfold sh1entryAddr.
      destruct (lookup blockToRemove (memory s) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). auto.
    }
    destruct HBTR as (HBTRIsBE & Hsh1).
    specialize(HaccNoPDf blockToRemove (CPaddr (blockToRemove+sh1offset)) HBTRIsBE Hsh1 HAflagBTR).
    split. intuition. unfold cons1Free in *; intuition.
    apply IL.mappedBlockIsBE in HBTRMapped. destruct HBTRMapped as [bentry (Hlookup & _)]. exists bentry. trivial.
  }
  intro child. eapply bindRev.
  { (** MAL.readSh1InChildLocationFromBlockEntryAddr **)
    eapply weaken. apply readSh1InChildLocationFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
    destruct Hprops as ((_ & Hcons1 & Hcons2 & _ & _ & _ & HBTRMapped & _) & _).
    unfold cons1Free in *; intuition.
    apply IL.mappedBlockIsBE in HBTRMapped. destruct HBTRMapped as [bentry (Hlookup & _)]. exists bentry. trivial.
  }
  intro blockToRemoveInDescendant. eapply bindRev.
  { (** Internal.freeSlot **)
    eapply weaken. apply freeSlot. intros s Hprops. simpl. split. apply Hprops.
    destruct Hprops as (((_ & Hcons1 & Hcons2 & HPI & HKDI & HidIsPart & HBTRMapped & HAflagBTR & HPDflagBTR & Hprops
      & HbeqBTRNull & _) & HPDchild) & HchildLoc). intuition.
    - apply IL.partitionsArePDT; trivial; unfold cons1Free in *; intuition.
    - unfold bentryAFlag in *. unfold isBE. destruct (lookup blockToRemove (memory s) beqAddr); try(congruence).
      destruct v; try(congruence). trivial.
    - apply IL.mappedBlockIsBE in HBTRMapped. destruct HBTRMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
  }
  intro. eapply weaken. apply IHn. intros s Hprops. simpl.
  destruct Hprops as [s1 [s2 [s3 [s4 [s5 [s6 [s7 [pdentry [pdentry1 [pdentry2 [pdentry3 [realMPU [emptyBentry
    [freeBentry [currFirstFreeSlot [blockToFreeIdx (Hs & Hs7 & Hs6 & Hs5 & Hs4 & Hs3 & Hs2 & Hcons1 & Hstructs7 &
    Hstructs6 & HlookupIds6 & HlookupBTRs5 & HfirstFrees5 & Hidxs2 & HlookupIds1 & HBTRIsBEs1 & HMPUIds1 & Hcons1s1
    & HgetPartsEq & HgetChildrenEq & HgetMappedBEq & HgetMappedBEqId & HemptyB & Hpdentry1 & Hpdentry2 &
    Hpdentry3 & HlebSuccNbFreeMax & HnewB & (((HlenProp & _ & Hcons2s1 & HPIs1 & HDKIs1 & HidIsParts1 & HBTRMappeds1 &
    HAflagBTR & HPDflagBTR & [statesList [blocksList [parentsList [s0 (HblocksList & HlastBlock & HlastParent & HP &
    Hconsists0 & HPIs0 & HKDIs0 & HVSs0 & HfirstPIsParts0 & HfirstBMappeds0)]]]] & HbeqNullBTR & HBTRNotNext &
    HlocPropsPartial & HrangePartial & HboundsNoNextPartial & HVSPartial & HparentEquivPartial) & [sh1entry
    [sh1entryaddr (HlookupSh1 & HPDchilds1 & Hsh1s1)]]) & [sh1entryBis [sh1entryaddrB (HlookupSh1Bis & Hsh1Bs1 &
    HchildLocs1)]]) & HgetPartsEqs2 & HPDTIfPDFlags2 & HmultPDTs2 & HgetMappedBEqss3 & HgetKSEq)]]]]]]]]]]]]]]]].
  assert(sh1entryaddrB = sh1entryaddr).
  {
    unfold sh1entryAddr in *. destruct (lookup blockToRemove (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite <-Hsh1s1 in *. assumption.
  }
  subst sh1entryaddrB. clear HlookupSh1Bis. clear Hsh1Bs1.
  (*specialize(HlocPropsPartial idPart blockToRemove sh1entryaddr blockToRemoveInDescendant child HidIsParts1
    HBTRMappeds1 Hsh1s1 HPDchilds1 HchildLocs1).*)
  assert(HPDchildIsPDT: pdchildIsPDT s1) by (unfold cons1Free in *; intuition).
  specialize(HPDchildIsPDT idPart blockToRemove sh1entryaddr child HidIsParts1 HBTRMappeds1 Hsh1s1 HPDchilds1).
  assert(HPDT: exists pdentry0 pdentry1, lookup idPart (memory s1) beqAddr = Some(PDT pdentry0)
    /\ lookup idPart (memory s) beqAddr = Some(PDT pdentry1)
    /\ pdentry1 = {|
                    structure := structure pdentry0;
                    firstfreeslot := blockToRemove;
                    nbfreeslots := CIndex (nbfreeslots pdentry0 +1);
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := removeBlockFromPhysicalMPUAux blockToRemove (MPU pdentry0);
                    vidtAddr := vidtAddr pdentry0
                  |}).
  {
    exists pdentry. exists pdentry3. rewrite Hs. simpl. rewrite IL.beqAddrTrue. split; trivial. split; trivial.
    rewrite Hpdentry2 in Hpdentry3. simpl in *. rewrite Hpdentry1 in Hpdentry3. simpl in *. unfold pdentryMPU in *.
    rewrite HlookupIds1 in *. subst realMPU. assumption.
  }
  destruct HnewB as [l2 [l3 HnewB2]]. destruct HemptyB as [l0 [l1 HnewB]].
  assert(HBE: exists bentry0 l newEnd, lookup blockToRemove (memory s1) beqAddr = Some(BE bentry0)
    /\ pdentryFirstFreeSlot idPart newEnd s1
    /\ lookup blockToRemove (memory s) beqAddr = Some(BE
        {|
          read := false;
          write := false;
          exec := false;
          present := false;
          accessible := false;
          blockindex := blockindex bentry0;
          blockrange := CBlock nullAddr newEnd;
          Hidx := l
        |})).
  {
    unfold bentryBlockIndex in *. rewrite Hs2 in Hidxs2. simpl in *.
    destruct (beqAddr idPart blockToRemove) eqn:HbeqChildBlockTR; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    destruct (lookup blockToRemove (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst blockToFreeIdx. exists b. exists l0. exists currFirstFreeSlot.
    split; trivial. unfold pdentryFirstFreeSlot in *. rewrite Hs5 in HfirstFrees5. simpl in *.
    destruct (beqAddr (CPaddr (blockToRemove + scoffset)) idPart) eqn:HbeqSceChild; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs4 in HfirstFrees5. simpl in *.
    destruct (beqAddr (CPaddr (blockToRemove + sh1offset)) idPart) eqn:HbeqSh1Child; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs3 in HfirstFrees5. simpl in *.
    destruct (beqAddr blockToRemove idPart) eqn:HbeqBlockTRChild; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs2 in HfirstFrees5. simpl in *. rewrite IL.beqAddrTrue in *. rewrite HlookupIds1.
    rewrite Hpdentry1 in *. simpl in *. split; trivial. rewrite Hs.
    rewrite Hs7. simpl. rewrite beqAddrFalse in *. rewrite HbeqChildBlockTR. rewrite IL.beqAddrTrue.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl. rewrite IL.beqAddrTrue.
    f_equal. f_equal. subst emptyBentry. simpl in *. rewrite HnewB2. f_equal; try(apply proof_irrelevance).
    unfold CBlock. destruct (le_dec (currFirstFreeSlot - nullAddr) maxIdx); try(lia). f_equal.
    apply proof_irrelevance.
  }
  assert(Hsh1Eq: sh1entryaddr = CPaddr (blockToRemove + sh1offset)).
  {
    unfold sh1entryAddr in *. destruct (lookup blockToRemove (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). assumption.
  }
  rewrite Hsh1Eq in *.
  (*assert(HPDflags0: sh1entryPDflag (CPaddr (blockToRemove + sh1offset)) false s0).
  {
    assert(HaccNoPDs0: AccessibleNoPDFlag s0) by (unfold cons1Free in *; intuition).
    specialize(HaccNoPDs0 blockToRemove (CPaddr (blockToRemove + sh1offset)) HblockIsBEs0 Hsh1s0 HAflagBTRs0).
    assumption.
  }*)
  assert(HwellSce: wellFormedShadowCutIfBlockEntry s1) by (unfold cons1Free in *; intuition).
  specialize(HwellSce blockToRemove HBTRIsBEs1). destruct HwellSce as [scentryaddr (HsceIsSCEs1 & Hsce)].
  subst scentryaddr. assert(HSHE: lookup (CPaddr (blockToRemove+sh1offset)) (memory s) beqAddr
    = Some(SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})).
  {
    unfold sh1entryPDflag in *. rewrite Hs. rewrite Hs7. simpl. rewrite IL.beqAddrTrue.
    destruct (beqAddr idPart (CPaddr (blockToRemove + sh1offset))) eqn:HbeqChildSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqChildSh1. rewrite <-HbeqChildSh1 in *. rewrite HlookupIds1 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
    destruct (beqAddr blockToRemove (CPaddr (blockToRemove + sh1offset))) eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. exfalso. unfold isBE in *.
      destruct (lookup blockToRemove (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
    destruct (beqAddr (CPaddr (blockToRemove + scoffset)) (CPaddr (blockToRemove + sh1offset))) eqn:HbeqSceSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSceSh1. rewrite HbeqSceSh1 in *. exfalso. unfold isSCE in *.
      destruct (lookup (CPaddr (blockToRemove + sh1offset)) (memory s1) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl.
    rewrite IL.beqAddrTrue. reflexivity.
  }
  assert(HSCE: lookup (CPaddr (blockToRemove+scoffset)) (memory s) beqAddr
    = Some(SCE {| origin := nullAddr; next := nullAddr |})).
  {
    unfold isSCE in *. rewrite Hs. rewrite Hs7. simpl. rewrite IL.beqAddrTrue.
    destruct (beqAddr idPart (CPaddr (blockToRemove + scoffset))) eqn:HbeqChildSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqChildSce. rewrite <-HbeqChildSce in *. rewrite HlookupIds1 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl.
    destruct (beqAddr blockToRemove (CPaddr (blockToRemove + scoffset))) eqn:HbeqBlockSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *. exfalso. unfold isBE in *.
      destruct (lookup blockToRemove (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs5. simpl.
    rewrite IL.beqAddrTrue. reflexivity.
  }
  assert(HlookupsEq: forall addr, idPart <> addr -> blockToRemove <> addr
    -> CPaddr (blockToRemove+sh1offset) <> addr
    -> CPaddr (blockToRemove+scoffset) <> addr -> lookup addr (memory s) beqAddr = lookup addr (memory s1) beqAddr).
  {
    intros addr HbeqChildAddr HbeqBlockTRAddr HbeqSh1Addr HbeqSceAddr. rewrite beqAddrFalse in *. rewrite Hs.
    rewrite Hs7. simpl. rewrite HbeqChildAddr. rewrite IL.beqAddrTrue.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs6. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqBlockTRAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite Hs5. simpl. rewrite beqAddrFalse in *. rewrite HbeqSceAddr. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs4. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqSh1Addr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite Hs3. simpl. rewrite beqAddrFalse in *. rewrite HbeqBlockTRAddr. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl. rewrite beqAddrFalse in *.
    rewrite HbeqChildAddr. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HPflagBTRs1: bentryPFlag blockToRemove true s1).
  {
    apply IL.mappedBlockIsBE in HBTRMappeds1. destruct HBTRMappeds1 as [bentry (Hlookup & Hpres)].
    unfold bentryPFlag. rewrite Hlookup. auto.
  }
  assert(Hsh1IsSHEs1: isSHE (CPaddr (blockToRemove + sh1offset)) s1) by (unfold isSHE; rewrite HlookupSh1; trivial).
  assert(HlenPropsRec: forall childrenList, isChildBlocksList s1 childrenList blockToRemoveInDescendant
    -> length childrenList < n).
  {
    intros childrenList HchildrenList.
    assert(HchildrenListRec: isChildBlocksList s1 (blockToRemoveInDescendant::childrenList) blockToRemove).
    { apply isChildBlocksListRec; trivial. }
    specialize(HlenProp (blockToRemoveInDescendant::childrenList) HchildrenListRec). simpl in *. lia.
  }

  assert(noDupMappedPaddrList s).
  { (* BEGIN noDupMappedPaddrList s *)
    assert(Hcons0: noDupMappedPaddrList s1) by (unfold cons2FreeRemove in *; intuition).
    revert HlookupsEq. apply noDupMappedPaddrListPreservedRemove; trivial; unfold cons1Free in *; intuition.
    (* END noDupMappedPaddrList *)
  }

  assert(accessibleParentPaddrIsAccessibleIntoChild s).
  { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
    assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s1) by (unfold cons2FreeRemove in *; intuition).
    revert HlookupsEq. apply accessibleParentPaddrIsAccessibleIntoChildPreservedRemove; trivial.
    1,2,3,4: unfold cons1Free in *; intuition.
    unfold cons2FreeRemove in *; intuition.
    (* END accessibleParentPaddrIsAccessibleIntoChild *)
  }

  assert(sharedBlockPointsToChild s).
  { (* BEGIN sharedBlockPointsToChild s *)
    assert(Hcons0: sharedBlockPointsToChild s1) by (unfold cons2FreeRemove in *; intuition).
    revert HlookupsEq. apply sharedBlockPointsToChildPreservedRemove; trivial; unfold cons1Free in *; intuition.
    (* END sharedBlockPointsToChild *)
  }

  assert(childsBlocksPropsInParent s).
  { (* BEGIN childsBlocksPropsInParent s *)
    assert(Hcons0: childsBlocksPropsInParent s1) by (unfold cons2FreeRemove in *; intuition).
    revert HlookupsEq. apply childsBlocksPropsInParentPreservedRemove; trivial; unfold cons1Free in *; intuition.
    (* END childsBlocksPropsInParent *)
  }

  assert(noChildImpliesAddressesNotShared s).
  { (* BEGIN noChildImpliesAddressesNotShared s *)
    assert(Hcons0: noChildImpliesAddressesNotShared s1) by (unfold cons2FreeRemove in *; intuition).
    revert HlookupsEq. apply noChildImpliesAddressesNotSharedPreservedRemove; trivial; unfold cons1Free in *;
      intuition.
    (* END noChildImpliesAddressesNotShared *)
  }

  assert(kernelsAreNotAccessible s).
  { (* BEGIN kernelsAreNotAccessible s *)
    assert(Hcons0: kernelsAreNotAccessible s1) by (unfold cons2FreeRemove in *; intuition).
    revert HlookupsEq. apply kernelsAreNotAccessiblePreservedRemove; trivial.
    (* END kernelsAreNotAccessible *)
  }

  assert(blockAndNextAreSideBySide s).
  { (* BEGIN blockAndNextAreSideBySide s *)
    assert(Hcons0: blockAndNextAreSideBySide s1) by (unfold cons2FreeRemove in *; intuition).
    revert HlookupsEq. apply blockAndNextAreSideBySidePreservedRemove; trivial; unfold cons1Free in *; intuition.
    (* END blockAndNextAreSideBySide *)
  }

  assert(forall partition pdentry block scentryaddr start endaddr,
          blockToRemoveInDescendant <> block
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> isBE block s
          -> bentryStartAddr block start s
          -> bentryEndAddr block endaddr s
          -> bentryPFlag block true s
          -> scentryaddr = CPaddr (block + scoffset)
          -> scentryOrigin scentryaddr start s
          -> scentryNext scentryaddr nullAddr s
          -> lookup partition (memory s) beqAddr = Some (PDT pdentry)
          -> partition <> constantRootPartM
          -> exists blockParent,
              In blockParent (getMappedBlocks (parent pdentry) s) /\ isBE blockParent s
              /\ bentryStartAddr blockParent start s /\ bentryEndAddr blockParent endaddr s).
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
    intros part pdentryPart block scentryaddr start endaddr HbeqBlockCBlock HpartIsPart HblockMapped HblockIsBE
      Hstart Hend HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. rewrite HgetPartsEq in *.
    unfold bentryPFlag in *. assert(HbeqBlocks: blockToRemove <> block).
    {
      intro. subst block. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
      rewrite Hlookups in *. simpl in *. congruence.
    }
    unfold isBE in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro. subst block. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. congruence.
      - intro. subst block. rewrite HSHE in *. congruence.
      - intro. subst block. rewrite HSCE in *. congruence.
    }
    rewrite HlookupBlockEq in *. unfold scentryNext in *. unfold scentryOrigin in *.
    assert(HlookupSceEq: lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s1) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. congruence.
      - intro Hcontra. subst scentryaddr. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
        assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
        rewrite HcontraBis in *. rewrite HSCE in *. congruence.
    }
    assert(Hpart: exists pdentryParts3 pdentryParts1, lookup part (memory s3) beqAddr = Some (PDT pdentryParts3)
      /\ lookup part (memory s1) beqAddr = Some (PDT pdentryParts1)
      /\ parent pdentryParts1 = parent pdentryPart).
    {
      rewrite Hs3. simpl. destruct (beqAddr blockToRemove part) eqn:HbeqBTRPart.
      {
        rewrite <-beqAddrTrue in HbeqBTRPart. subst part. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      destruct (beqAddr idPart part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. exists pdentry1. rewrite Hs in HlookupPart. simpl in *.
        rewrite IL.beqAddrTrue in *. injection HlookupPart as HpdentriesEq. subst pdentryPart. rewrite Hpdentry3.
        simpl. rewrite Hpdentry2. simpl. rewrite Hpdentry1. exists pdentry. auto.
      - exists pdentryPart. exists pdentryPart. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite <-HlookupsEq; auto.
        + intro. subst part. congruence.
        + intro. subst part. congruence.
    }
    destruct Hpart as [pdentryParts3 [pdentryParts1 (HlookupParts3 & HlookupParts1 & HparentsEq)]].
    rewrite HlookupSceEq in *. rewrite <-HparentsEq. assert(HblockMappeds1: In block (getMappedBlocks part s1)).
    {
      destruct (beqAddr idPart part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. specialize(HgetMappedBEqId block).
        destruct HgetMappedBEqId as (_ & Hres & _). apply Hres; assumption.
      - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBEq; trivial. unfold isPDT. rewrite HlookupParts3. trivial.
    }
    specialize(HrangePartial part pdentryParts1 block scentryaddr start endaddr HbeqBlocks HpartIsPart HblockMappeds1
      HblockIsBE Hstart Hend HPflag Hsce Horigin Hnext HlookupParts1 HbeqPartRoot).
    destruct HrangePartial as [blockParent (HblockPMapped & HblockPIsBE & HstartP & HendP)]. exists blockParent.
    assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold cons1Free in *; intuition).
    specialize(HparentOfPart part pdentryParts1 HlookupParts1). destruct HparentOfPart as (HparentIsPart & _).
    specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
    assert(HisChild: isChild s1) by (unfold cons1Free in *; intuition).
    assert(Hparent: pdentryParent part (parent pdentryParts1) s1).
    { unfold pdentryParent. rewrite HlookupParts1. reflexivity. }
    specialize(HisChild part (parent pdentryParts1) HpartIsPart Hparent HbeqPartRoot).
    assert(HchildBlockProps: childsBlocksPropsInParent s1) by (unfold cons2FreeRemove in *; intuition).
    assert(HPflagP: bentryPFlag blockParent true s1).
    {
      apply IL.mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(HlebStartsTriv: start <= start) by lia.
    assert(HgebEndsTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps part (parent pdentryParts1) block start endaddr blockParent start endaddr
      HparentIsPart HisChild HblockMappeds1 Hstart Hend HPflag HblockPMapped HstartP HendP HPflagP HlebStartsTriv
      HgebEndsTriv). destruct HchildBlockProps as (_ & HchildNotNull & HchildLocNotNull & _).
    assert(blockToRemove <> blockParent).
    {
      intro. subst blockParent. specialize(HchildLocNotNull blockToRemoveInDescendant HchildLocs1).
      destruct HchildLocNotNull as (HbeqBlockCNull & HblocksEq). assert(HeqTriv: start = start) by reflexivity.
      specialize(HblocksEq HeqTriv). congruence.
    }
    assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro. subst blockParent. rewrite HlookupIds1 in *. congruence.
      - intro. subst blockParent. rewrite HlookupSh1 in *. congruence.
      - intro. subst blockParent. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s1) beqAddr); try(congruence).
        destruct v; congruence.
    }
    rewrite HlookupBlockPEq. split; auto. destruct (beqAddr idPart (parent pdentryParts1)) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. rewrite <-HbeqParts in *. specialize(HgetMappedBEqId blockParent).
      destruct HgetMappedBEqId as (Hres & _). apply Hres in HblockPMapped.
      destruct HblockPMapped as [Hcontra | HblockPMapped]; try(exfalso; congruence). assumption.
    - rewrite <-beqAddrFalse in *. rewrite HgetMappedBEq; trivial. unfold isPDT. rewrite Hs3. simpl.
      destruct (beqAddr blockToRemove (parent pdentryParts1)) eqn:HbeqBTRParent.
      { rewrite <-beqAddrTrue in HbeqBTRParent. rewrite HbeqBTRParent in *. rewrite HlookupParent in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqParts. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent. trivial.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }

  assert(HgetPartsEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
  {
    revert HblocksList. apply getPartitionsEqRemoveDesc; trivial; unfold consistency in *; unfold consistency1 in *;
      intuition.
  }
  assert(HnullNotInBlocksList: ~In nullAddr blocksList).
  {
    revert HblocksList. apply nullNotInRemoveDesc with blockToRemove; trivial.
  }
  assert(HblocksListIsChildBList: isChildBlocksList s0 blocksList firstBlockToRemove).
  {
    revert HblocksList. apply removeDescIsChildBlockList; trivial.
    unfold consistency in *; unfold consistency1 in *; intuition.
  }
  assert(HnoDupBlocksList: NoDup (firstBlockToRemove::blocksList)).
  {
    apply noDupChildrenList with s0; trivial.
    1,2,3,4,5,6,7,8: unfold consistency in *; unfold consistency1 in *; intuition.
    - unfold consistency in *; unfold consistency2 in *; intuition.
    - exists firstPart. auto.
  }
  assert(HidIsPDTs1: isPDT idPart s1) by (unfold isPDT; rewrite HlookupIds1; trivial).
  assert(Hnulls0: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  pose proof (lookupEqLastRemoveDesc s1 s0 blockToRemove firstPart firstBlockToRemove statesList blocksList
    parentsList HBTRIsBEs1 Hsh1IsSHEs1 Hnulls0 HlastBlock HnoDupBlocksList HblocksList) as HlookupBTREq.
  destruct HlookupBTREq as (HlookupBTREqs1s0 & HlookupBTRSh1Eqs1s0).
  assert(HlistIsChildBListRec: isChildBlocksList s0 (blocksList++[blockToRemoveInDescendant]) firstBlockToRemove).
  {
    apply isChildBlocksListRecR with blockToRemove; trivial.
    - unfold isBE. rewrite <-HlookupBTREqs1s0. assumption.
    - unfold sh1entryInChildLocation in *. rewrite <-HlookupBTRSh1Eqs1s0.
      destruct (lookup (CPaddr (blockToRemove+sh1offset)) (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HchildLocs1 as (HchildLocs1 & HlocIsBE). split; trivial.
      intro HbeqDescNull. specialize(HlocIsBE HbeqDescNull). revert HblocksList.
      apply isBEPreservedRemoveDescRev; trivial.
  }
  assert(HnoDupComplete: NoDup (firstBlockToRemove::blocksList ++ [blockToRemoveInDescendant])).
  {
    revert HlistIsChildBListRec. apply noDupChildrenList; trivial.
    1,2,3,4,5,6,7: unfold consistency in *; unfold consistency1 in *; intuition.
    - unfold consistency in *; unfold consistency2 in *; intuition.
    - exists firstPart. auto.
  }
  assert(HbeqFirstDesc: firstBlockToRemove <> blockToRemoveInDescendant).
  {
    intro. subst blockToRemoveInDescendant. apply NoDup_cons_iff in HnoDupComplete.
    destruct HnoDupComplete as (Hcontra & _). apply Lib.in_app_or_neg in Hcontra. destruct Hcontra as (_ & Hcontra).
    simpl in *. contradict Hcontra. auto.
  }
  assert(HdescProps: blockToRemoveInDescendant <> nullAddr
    -> child <> nullAddr
        /\ In blockToRemoveInDescendant (getMappedBlocks child s1)
        /\ forall startaddrB, bentryStartAddr blockToRemove startaddrB s1
            -> bentryStartAddr blockToRemoveInDescendant startaddrB s1).
  {
    intro HbeqBlockCNull. assert(HbeqChildNull: child <> nullAddr).
    {
      assert(HnullEquiv: childBlockNullIfChildNull s1) by (unfold cons1Free in *; intuition). intro. subst child.
      specialize(HnullEquiv idPart blockToRemove (CPaddr (blockToRemove+sh1offset)) HidIsParts1 HBTRMappeds1 Hsh1s1
        HPDchilds1). unfold sh1entryInChildLocation in *. rewrite HlookupSh1 in *.
      destruct HnullEquiv as (HnullEquiv & _). destruct HchildLocs1 as (HchildLocs1 & _). rewrite <-HnullEquiv in *.
      congruence.
    }
    split; trivial. specialize(HPDchildIsPDT HbeqChildNull). destruct statesList; simpl in *.
    - destruct HblocksList as (HbList & HpList & Hs1). subst blocksList. subst s1. subst parentsList.
      simpl in *. subst blockToRemove. subst idPart. assert(HlocProps: childLocMappedInChild s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      specialize(HlocProps firstPart firstBlockToRemove (CPaddr (firstBlockToRemove+sh1offset))
        blockToRemoveInDescendant child HfirstPIsParts0 HfirstBMappeds0 Hsh1s1 HPDchilds1 HchildLocs1
        HbeqChildNull). destruct HlocProps. assumption.
    - destruct HblocksList as [blockChild [childPart [blocksListRec [parentsListRec (HblocksList & HparentsList
        & HbeqBTRNull & HAflag & HBTRMapped & HpartBIsPart & _ & _ & HPDflag & HPDchild & HchildLoc & _
        & _ & _ & _ & HblocksListRec)]]]]. rewrite HblocksList in *. apply IL.lastOfNotEmptyIsIn in HlastBlock.
      apply NoDup_cons_iff in HnoDupBlocksList. destruct HnoDupBlocksList as (HfirstNotIn & HnoDupBlocksList).
      specialize(HlocPropsPartial idPart blockToRemove (CPaddr (blockToRemove+sh1offset))
        blockToRemoveInDescendant child HbeqFirstDesc HidIsParts1 HBTRMappeds1 Hsh1s1 HPDchilds1 HchildLocs1
        HbeqChildNull). destruct HlocPropsPartial. assumption.
  }
  assert(HbeqBTRBlockC: blockToRemove <> blockToRemoveInDescendant).
  {
    intro. subst blockToRemoveInDescendant. specialize(HdescProps HbeqNullBTR).
    destruct HdescProps as (HbeqChildNull & HBTRMappedBis & _). specialize(HPDchildIsPDT HbeqChildNull).
    assert(HisParent: isParent s1) by (unfold cons1Free in *; intuition).
    specialize(HisParent child idPart HidIsParts1 HPDchildIsPDT). unfold pdentryParent in *.
    destruct (lookup child (memory s1) beqAddr) eqn:HlookupChild; try(congruence). destruct v; try(congruence).
    assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold cons1Free in *; intuition).
    specialize(HparentOfPart child p HlookupChild). destruct HparentOfPart as (_ & _ & HbeqParts).
    rewrite <-HisParent in *. assert(Hdisjoint: DisjointKSEntries s1) by (unfold cons1Free in *; intuition).
    assert(HchildIsPDT: isPDT child s1) by (unfold isPDT; rewrite HlookupChild; trivial).
    specialize(Hdisjoint idPart child HidIsPDTs1 HchildIsPDT HbeqParts).
    destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
    unfold getMappedBlocks in *. apply InFilterPresentInList in HBTRMappedBis.
    apply InFilterPresentInList in HBTRMappeds1. specialize(Hdisjoint blockToRemove HBTRMappeds1). congruence.
  }
  assert(HdescIsFullRange: blockToRemoveInDescendant <> nullAddr
    -> forall startaddr endaddr, bentryStartAddr blockToRemove startaddr s1
    -> bentryEndAddr blockToRemove endaddr s1
    -> bentryStartAddr blockToRemoveInDescendant startaddr s1 /\ bentryEndAddr blockToRemoveInDescendant endaddr s1).
  {
    assert(HchildBlockProps: childsBlocksPropsInParent s1) by (unfold cons2FreeRemove in *; intuition).
    intros HbeqBlockCNull startaddr endaddr HstartBTR HendBTR.
    specialize(HdescProps HbeqBlockCNull). destruct HdescProps as (HbeqChildNull & HblockCMapped & HstartsEq).
    specialize(HPDchildIsPDT HbeqChildNull). assert(HstartC: bentryStartAddr blockToRemoveInDescendant startaddr s1).
    { apply HstartsEq; assumption. }
    split; trivial. assert(HPflagC: bentryPFlag blockToRemoveInDescendant true s1).
    {
      apply IL.mappedBlockIsBE in HblockCMapped. destruct HblockCMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(HlebStarts: startaddr <= startaddr) by lia.
    assert(HendC: exists endC, bentryEndAddr blockToRemoveInDescendant endC s1).
    {
      unfold bentryPFlag in *. unfold bentryEndAddr.
      destruct (lookup blockToRemoveInDescendant (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
    }
    destruct HendC as [endC HendC].
    specialize(HparentEquivPartial idPart child blockToRemoveInDescendant startaddr endC HbeqBTRBlockC
      HidIsParts1 HPDchildIsPDT HblockCMapped HstartC HendC HPflagC).
    assert(Hwell: wellFormedBlock s1) by (unfold cons1Free in *; intuition).
    specialize(Hwell blockToRemoveInDescendant startaddr endC HPflagC HstartC HendC). destruct Hwell as (HwellC & _).
    destruct HparentEquivPartial as [blockParent [startP [endP (HblockPMapped & HstartP & HendP & HlebStartsBis &
      HgebEnds)]]]. assert(blockParent = blockToRemove).
    {
      destruct (beqAddr blockParent blockToRemove) eqn:HbeqBlocks; try(rewrite beqAddrTrue; assumption). exfalso.
      rewrite <-beqAddrFalse in *. assert(HstartInBP: In startaddr (getAllPaddrAux [blockParent] s1)).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
        destruct (lookup blockParent (memory s1) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
        rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendP. apply IL.getAllPaddrBlockIncl; lia.
      }
      assert(HnoDupMappedPaddr: noDupMappedPaddrList s1) by (unfold cons2FreeRemove in *; intuition).
      pose proof (DisjointPaddrInPart idPart blockParent blockToRemove startaddr s1 HnoDupMappedPaddr HidIsPDTs1
        HblockPMapped HBTRMappeds1 HbeqBlocks HstartInBP) as Hcontra. contradict Hcontra.
      assert(Hwell: wellFormedBlock s1) by (unfold cons1Free in *; intuition).
      specialize(Hwell blockToRemove startaddr endaddr HPflagBTRs1 HstartBTR HendBTR). destruct Hwell as (Hwell & _).
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
      destruct (lookup blockToRemove (memory s1) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
      rewrite app_nil_r. rewrite <-HstartBTR. rewrite <-HendBTR. apply IL.getAllPaddrBlockIncl; lia.
    }
    subst blockParent. assert(endP = endaddr).
    {
      unfold bentryEndAddr in *. destruct (lookup blockToRemove (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-HendBTR in *. assumption.
    }
    subst endP. specialize(HchildBlockProps child idPart blockToRemoveInDescendant startaddr endC blockToRemove
      startaddr endaddr HidIsParts1 HPDchildIsPDT HblockCMapped HstartC HendC HPflagC HBTRMappeds1 HstartBTR HendBTR
      HPflagBTRs1 HlebStarts HgebEnds). destruct HchildBlockProps as (_ & _ & _ & HAflagBTRBis).
    assert(endaddr = endC).
    {
      destruct (beqAddr endaddr endC) eqn:HbeqEnds; try(rewrite beqAddrTrue; assumption). rewrite <-beqAddrFalse in *.
      exfalso. assert(HboundsDiff: startaddr <> startaddr \/ endaddr <> endC) by auto.
      specialize(HAflagBTRBis HboundsDiff). unfold bentryAFlag in *.
      destruct (lookup blockToRemove (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    subst endC. assumption.
  }
  assert(HdescIsAcc: blockToRemoveInDescendant <> nullAddr -> bentryAFlag blockToRemoveInDescendant true s1).
  {
    intro HbeqBlockCNull. specialize(HdescProps HbeqBlockCNull). specialize(HdescIsFullRange HbeqBlockCNull).
    destruct HdescProps as (HbeqChildNull & HblockCMapped & _). specialize(HPDchildIsPDT HbeqChildNull).
    assert(Hbounds: exists startaddr endaddr, bentryStartAddr blockToRemove startaddr s1
      /\ bentryEndAddr blockToRemove endaddr s1).
    {
      unfold bentryAFlag in *. unfold bentryStartAddr. unfold bentryEndAddr.
      destruct (lookup blockToRemove (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). exists (endAddr (blockrange b)). auto.
    }
    destruct Hbounds as [startaddr [endaddr (HstartBTR & HendBTR)]].
    specialize(HdescIsFullRange startaddr endaddr HstartBTR HendBTR).
    destruct HdescIsFullRange as (HstartC & HendC).
    assert(Hwell: wellFormedBlock s1) by (unfold cons1Free in *; intuition).
    specialize(Hwell blockToRemove startaddr endaddr HPflagBTRs1 HstartBTR HendBTR). destruct Hwell as (Hwell & _).
    assert(HstartAccId: In startaddr (getAccessibleMappedPaddr idPart s1)).
    {
      apply IL.addrInAccessibleBlockIsAccessibleMapped with blockToRemove; trivial. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. simpl.
      destruct (lookup blockToRemove (memory s1) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
      rewrite app_nil_r. rewrite <-HstartBTR. rewrite <-HendBTR. apply IL.getAllPaddrBlockIncl; lia.
    }
    assert(In startaddr (getAllPaddrAux [blockToRemoveInDescendant] s1)).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
      destruct (lookup blockToRemoveInDescendant (memory s1) beqAddr); try(simpl; congruence).
      destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartC. rewrite <-HendC.
      apply IL.getAllPaddrBlockIncl; lia.
    }
    assert(HstartMappedChild: In startaddr (getMappedPaddr child s1)).
    {
      apply IL.addrInBlockIsMapped with blockToRemoveInDescendant; trivial.
    }
    assert(HaccessImpl: accessibleParentPaddrIsAccessibleIntoChild s1) by (unfold cons2FreeRemove in *; intuition).
    specialize(HaccessImpl idPart child startaddr HidIsParts1 HPDchildIsPDT HstartAccId HstartMappedChild).
    revert HaccessImpl. apply IL.addrInAccessibleMappedIsAccessible; trivial. unfold cons2FreeRemove in *; intuition.
  }

  assert(forall partition pdentry block scentryaddr startaddr endaddr,
          blockToRemoveInDescendant <> block
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> bentryStartAddr block startaddr s
          -> bentryEndAddr block endaddr s
          -> scentryaddr = CPaddr (block + scoffset)
          -> scentryNext scentryaddr nullAddr s
          -> partition <> constantRootPartM
          -> lookup partition (memory s) beqAddr = Some (PDT pdentry)
          -> exists blockParent startParent,
              In blockParent (getMappedBlocks (parent pdentry) s) /\ bentryStartAddr blockParent startParent s
              /\ bentryEndAddr blockParent endaddr s /\ startParent <= startaddr).
  { (* BEGIN parentBlocksBoundsIfNoNext s *)
    intros part pdentryPart block scentryaddr startaddr endaddr HbeqBlockCBlock HpartIsPart HblockMapped Hstart
      Hend Hsce Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEq in *. unfold bentryStartAddr in *.
    unfold bentryEndAddr in *. assert(HbeqBlocks: blockToRemove <> block).
    {
      intro. subst block. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
      rewrite Hlookups in *. injection Hlookup as HbentriesEq. subst bentry. simpl in *. congruence.
    }
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro. subst block. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. congruence.
      - intro. subst block. rewrite HSHE in *. congruence.
      - intro. subst block. rewrite HSCE in *. congruence.
    }
    rewrite HlookupBlockEq in *. unfold scentryNext in *.
    assert(HlookupSceEq: lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s1) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite Hcontra in *. rewrite HSHE in *. congruence.
      - intro Hcontra. subst scentryaddr. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
        assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
        rewrite HcontraBis in *. rewrite HSCE in *. congruence.
    }
    assert(Hpart: exists pdentryParts3 pdentryParts1, lookup part (memory s3) beqAddr = Some (PDT pdentryParts3)
      /\ lookup part (memory s1) beqAddr = Some (PDT pdentryParts1)
      /\ parent pdentryParts1 = parent pdentryPart).
    {
      rewrite Hs3. simpl. destruct (beqAddr blockToRemove part) eqn:HbeqBTRPart.
      {
        rewrite <-beqAddrTrue in HbeqBTRPart. subst part. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      destruct (beqAddr idPart part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. exists pdentry1. rewrite Hs in HlookupPart. simpl in *.
        rewrite IL.beqAddrTrue in *. injection HlookupPart as HpdentriesEq. subst pdentryPart. rewrite Hpdentry3.
        simpl. rewrite Hpdentry2. simpl. rewrite Hpdentry1. exists pdentry. auto.
      - exists pdentryPart. exists pdentryPart. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite <-HlookupsEq; auto.
        + intro. subst part. congruence.
        + intro. subst part. congruence.
    }
    destruct Hpart as [pdentryParts3 [pdentryParts1 (HlookupParts3 & HlookupParts1 & HparentsEq)]].
    rewrite HlookupSceEq in *. rewrite <-HparentsEq. assert(HblockMappeds1: In block (getMappedBlocks part s1)).
    {
      destruct (beqAddr idPart part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. specialize(HgetMappedBEqId block).
        destruct HgetMappedBEqId as (_ & Hres & _). apply Hres; assumption.
      - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBEq; trivial. unfold isPDT. rewrite HlookupParts3. trivial.
    }
    specialize(HboundsNoNextPartial part pdentryParts1 block scentryaddr startaddr endaddr HbeqBlocks HpartIsPart
      HblockMappeds1 Hstart Hend Hsce Hnext HbeqPartRoot HlookupParts1).
    destruct HboundsNoNextPartial as [blockParent [startP (HblockPMapped & HstartP & HendP & HlebStarts)]].
    exists blockParent. exists startP.
    assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold cons1Free in *; intuition).
    specialize(HparentOfPart part pdentryParts1 HlookupParts1). destruct HparentOfPart as (HparentIsPart & _).
    specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
    assert(HisChild: isChild s1) by (unfold cons1Free in *; intuition).
    assert(Hparent: pdentryParent part (parent pdentryParts1) s1).
    { unfold pdentryParent. rewrite HlookupParts1. reflexivity. }
    specialize(HisChild part (parent pdentryParts1) HpartIsPart Hparent HbeqPartRoot).
    assert(HchildBlockProps: childsBlocksPropsInParent s1) by (unfold cons2FreeRemove in *; intuition).
    assert(HPflagP: bentryPFlag blockParent true s1).
    {
      apply IL.mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(HPflag: bentryPFlag block true s1).
    {
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite <-HlookupBlockEq. rewrite Hlookup. auto.
    }
    assert(HgebEndsTriv: endaddr >= endaddr) by lia.
    specialize(HchildBlockProps part (parent pdentryParts1) block startaddr endaddr blockParent startP endaddr
      HparentIsPart HisChild HblockMappeds1 Hstart Hend HPflag HblockPMapped HstartP HendP HPflagP HlebStarts
      HgebEndsTriv). destruct HchildBlockProps as (_ & HchildNotNull & HchildLocNotNull & _).
    assert(blockToRemove <> blockParent).
    {
      intro. subst blockParent. specialize(HchildLocNotNull blockToRemoveInDescendant HchildLocs1).
      destruct HchildLocNotNull as (HbeqBlockCNull & HblocksEq). destruct (beqAddr startP startaddr) eqn:HbeqStarts.
      - rewrite <-beqAddrTrue in HbeqStarts. specialize(HblocksEq HbeqStarts). congruence.
      - rewrite <-beqAddrFalse in *. assert(HltStarts: startP < startaddr).
        { apply paddrNeqNatNeqEquiv in HbeqStarts. lia. }
        assert(HbeqChildNull: child <> nullAddr).
        {
          assert(HnullEq: childBlockNullIfChildNull s1) by (unfold cons1Free in *; intuition). intro. subst child.
          specialize(HnullEq idPart blockToRemove (CPaddr (blockToRemove+sh1offset)) HidIsParts1 HBTRMappeds1
            Hsh1s1 HPDchilds1). unfold sh1entryInChildLocation in *. rewrite HlookupSh1 in *.
          destruct HchildLocs1 as (HchildLocs1 & _). destruct HnullEq as (Hcontra & _). rewrite <-Hcontra in *.
          congruence.
        }
        assert(HbeqIdParent: idPart = parent pdentryParts1).
        {
          destruct (beqAddr idPart (parent pdentryParts1)) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. exfalso. unfold getMappedBlocks in *.
          apply InFilterPresentInList in HblockPMapped. apply InFilterPresentInList in HBTRMappeds1.
          assert(Hdisjoint: DisjointKSEntries s1) by (unfold cons1Free in *; intuition).
          assert(HparentIsPDTs1: isPDT (parent pdentryParts1) s1) by (unfold isPDT; rewrite HlookupParent; trivial).
          specialize(Hdisjoint idPart (parent pdentryParts1) HidIsPDTs1 HparentIsPDTs1 HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint blockToRemove HBTRMappeds1). congruence.
        }
        rewrite <-HbeqIdParent in *. specialize(HPDchildIsPDT HbeqChildNull). specialize(HdescProps HbeqBlockCNull).
        destruct HdescProps as (_ & HdescMappeds1 & HstartsEqDesc). specialize(HstartsEqDesc startP HstartP).
        assert(Hwell: wellFormedBlock s1) by (unfold cons1Free in *; intuition).
        specialize(Hwell block startaddr endaddr HPflag Hstart Hend). destruct Hwell as (Hwell & _).
        assert(HstartInRange: In startaddr (getAllPaddrBlock startP endaddr)).
        { apply IL.getAllPaddrBlockIncl; lia. }
        specialize(HdescIsFullRange HbeqBlockCNull startP endaddr HstartP HendP).
        destruct HdescIsFullRange as (_ & HendC).
        assert(HstartInBTRDesc: In startaddr (getAllPaddrAux [blockToRemoveInDescendant] s1)).
        {
          simpl. destruct (lookup blockToRemoveInDescendant (memory s1) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartsEqDesc. rewrite <-HendC. assumption.
        }
        assert(HstartInBlock: In startaddr (getAllPaddrAux [block] s1)).
        {
          simpl. destruct (lookup block (memory s1) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r.
          apply IL.getAllPaddrBlockIncl; lia.
        }
        assert(child = part).
        {
          destruct (beqAddr child part) eqn:HbeqChildren; try(rewrite beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. exfalso.
          specialize(HPIs1 idPart child part HidIsParts1 HPDchildIsPDT HisChild HbeqChildren).
          assert(HstartUsedChild: In startaddr (getUsedPaddr child s1)).
          {
            unfold getUsedPaddr. apply in_or_app. right.
            apply IL.addrInBlockIsMapped with blockToRemoveInDescendant; trivial.
          }
          specialize(HPIs1 startaddr HstartUsedChild). contradict HPIs1. unfold getUsedPaddr. apply in_or_app. right.
          apply IL.addrInBlockIsMapped with block; trivial.
        }
        subst part. assert(HnoDupMappedP: noDupMappedPaddrList s1) by (unfold cons2FreeRemove in *; intuition).
        assert(HchildIsPDT: isPDT child s1) by (unfold isPDT; rewrite HlookupParts1; trivial).
        pose proof (DisjointPaddrInPart child blockToRemoveInDescendant block startaddr s1 HnoDupMappedP HchildIsPDT
          HdescMappeds1 HblockMappeds1 HbeqBlockCBlock HstartInBTRDesc). congruence.
    }
    assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
    {
      unfold bentryPFlag in *. apply HlookupsEq; trivial.
      - intro. subst blockParent. rewrite HlookupIds1 in *. congruence.
      - intro. subst blockParent. rewrite HlookupSh1 in *. congruence.
      - intro. subst blockParent. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s1) beqAddr); try(congruence).
        destruct v; congruence.
    }
    rewrite HlookupBlockPEq. split; auto. destruct (beqAddr idPart (parent pdentryParts1)) eqn:HbeqParts.
    - specialize(HgetMappedBEqId blockParent). destruct HgetMappedBEqId as (HgetMappedBEqId & _).
      rewrite <-beqAddrTrue in HbeqParts. rewrite HbeqParts in *. apply HgetMappedBEqId in HblockPMapped.
      destruct HblockPMapped as [Hcontra | Hres]; try(exfalso; congruence). assumption.
    - rewrite <-beqAddrFalse in *. rewrite HgetMappedBEq; trivial. unfold isPDT. rewrite Hs3. simpl.
      destruct (beqAddr blockToRemove (parent pdentryParts1)) eqn:HbeqBTRParent.
      {
        rewrite <-beqAddrTrue in HbeqBTRParent. rewrite HbeqBTRParent in *. unfold isBE in *.
        rewrite HlookupParent in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqParts. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent. trivial.
    (* END parentBlocksBoundsIfNoNext *)
  }
  assert(HPflagBTRs: bentryPFlag blockToRemove false s).
  {
    unfold bentryPFlag. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]]. rewrite Hlookups. reflexivity.
  }

  assert(HchildLocMappedInChildPartials: forall part block sh1entryaddr blockChild idchild,
    firstBlockToRemove <> blockChild
    -> In part (getPartitions multiplexer s)
    -> In block (getMappedBlocks part s)
    -> sh1entryAddr block sh1entryaddr s
    -> sh1entryPDchild sh1entryaddr idchild s
    -> sh1entryInChildLocation sh1entryaddr blockChild s
    -> idchild <> nullAddr
    -> blockChild <> nullAddr /\ In blockChild (getMappedBlocks idchild s)
        /\ (forall startaddr, bentryStartAddr block startaddr s -> bentryStartAddr blockChild startaddr s)).
  {
    intros part block sh1entryaddrBis blockChild idchild HbeqFirstBlock HpartIsPart HblockMapped Hsh1 HPDchild
      HchildLoc HbeqChildNull. rewrite HgetPartsEq in *. assert(HbeqBlocks: blockToRemove <> block).
    {
      intro. subst block. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
      rewrite Hlookups in *. injection Hlookup as HbentriesEq. subst bentry. simpl in *. congruence.
    }
    assert(HblockMappeds1: In block (getMappedBlocks part s1)).
    {
      destruct (beqAddr idPart part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. specialize(HgetMappedBEqId block).
        destruct HgetMappedBEqId as (_ & Hres & _). apply Hres; assumption.
      - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBEq; trivial.
        assert(HpartIsPDT: isPDT part s1).
        { apply IL.partitionsArePDT; trivial; unfold cons1Free in *; intuition. }
        unfold isPDT in *. rewrite Hs3. simpl.
        destruct (beqAddr blockToRemove part) eqn:HbeqBTRPart.
        {
          rewrite <-beqAddrTrue in HbeqBTRPart. subst part. unfold isBE in *.
          destruct (lookup blockToRemove (memory s1) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqParts. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    unfold sh1entryAddr in *. unfold bentryStartAddr.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro. subst block. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. congruence.
      - intro. subst block. rewrite HSHE in *. congruence.
      - intro. subst block. rewrite HSCE in *. congruence.
    }
    rewrite HlookupBlockEq in *. unfold sh1entryPDchild in *. unfold sh1entryInChildLocation in *.
    assert(HlookupSh1Eq: lookup sh1entryaddrBis (memory s) beqAddr = lookup sh1entryaddrBis (memory s1) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]].
        rewrite Hlookups in *. congruence.
      - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
        rewrite Hlookups in *. congruence.
      - destruct (lookup block (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        intro Hcontra. subst sh1entryaddrBis. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis.
        assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
        rewrite HcontraBis in *. rewrite HSHE in *. congruence.
      - intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
    }
    rewrite HlookupSh1Eq in *. assert(HchildLocBiss1: sh1entryInChildLocation sh1entryaddrBis blockChild s1).
    {
      unfold sh1entryInChildLocation. destruct (lookup sh1entryaddrBis (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial.
      intro HbeqLocNull. specialize(HlocIsBE HbeqLocNull). unfold isBE in *.
      destruct (beqAddr blockToRemove blockChild) eqn:HbeqBTRBlockCBis.
      - rewrite <-beqAddrTrue in HbeqBTRBlockCBis. rewrite HbeqBTRBlockCBis in *. assumption.
      - rewrite <-beqAddrFalse in *. clear HchildLoc. rewrite <-HlookupsEq; trivial.
        + intro. subst blockChild. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *.
          congruence.
        + intro. subst blockChild. rewrite HSHE in *. congruence.
        + intro. subst blockChild. rewrite HSCE in *. congruence.
    }
    specialize(HlocPropsPartial part block sh1entryaddrBis blockChild idchild HbeqFirstBlock
      HpartIsPart HblockMappeds1 Hsh1 HPDchild HchildLocBiss1 HbeqChildNull).
    destruct HlocPropsPartial as (HbeqBlockCNull & HBCMapped & HstartsEq). split; trivial.
    assert(blockToRemove <> blockChild).
    {
      destruct statesList.
      - simpl in *. destruct HblocksList as (HblockEq & HparentEq & Hs1). subst blocksList. subst s1. simpl in *.
        subst blockToRemove. assumption.
      - intro. subst blockChild. assert(blocksList <> []).
        {
          simpl in *. destruct HblocksList as [blockChild [_ [blocksListRec [_ (HblocksList & _ )]]]]. intro Hcontra.
          rewrite Hcontra in *. congruence.
        }
        assert(block <> last blocksList firstBlockToRemove).
        { rewrite <-HlastBlock. auto. }
        assert(idchild = idPart).
        {
          destruct (beqAddr idchild idPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
          rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HBTRMappeds1.
          apply InFilterPresentInList in HBCMapped.
          assert(Hdisjoint: DisjointKSEntries s1) by (unfold cons1Free in *; intuition).
          assert(HchildIsPDT: isPDT idchild s1).
          {
            unfold getKSEntries in *. unfold isPDT.
            destruct (lookup idchild (memory s1) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          specialize(Hdisjoint idchild idPart HchildIsPDT HidIsPDTs1 HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint blockToRemove HBCMapped). congruence.
        }
        subst idchild. clear HBCMapped.
        assert(HblocksListLast: exists blocksListHd, blocksList = blocksListHd++[blockToRemove]).
        {
          exists (removelast blocksList). rewrite HlastBlock. apply app_removelast_last; trivial.
        }
        destruct HblocksListLast as [blocksListHd HblocksListLast].
        assert(HchildLocLast: sh1entryInChildLocation (CPaddr (last blocksListHd firstBlockToRemove + sh1offset))
          blockToRemove s0).
        {
          rewrite HblocksListLast in *. apply penBlocksListIsParentOfLast; assumption.
        }
        assert(HpenInList: In (last blocksListHd firstBlockToRemove) (firstBlockToRemove::blocksListHd)).
        {
          destruct blocksListHd.
          - simpl. auto.
          - assert(HeqTriv: last (p::blocksListHd) firstBlockToRemove = last (p::blocksListHd) firstBlockToRemove).
            { reflexivity. }
            pose proof (IL.lastOfNotEmptyIsIn paddr (last (p::blocksListHd) firstBlockToRemove) p blocksListHd
              firstBlockToRemove HeqTriv) as Hres. simpl in *. auto.
        }
        assert(In (last blocksListHd firstBlockToRemove) (firstBlockToRemove :: blocksList)).
        {
          simpl in *. destruct HpenInList as [HpenIsFirst | HpenInList]; auto. rewrite HblocksListLast. right.
          apply in_or_app. auto.
        }
        assert(HpenMapped: exists part, In part (firstPart::parentsList) /\ In part (getPartitions multiplexer s0)
          /\ In (last blocksListHd firstBlockToRemove) (getMappedBlocks part s0)).
        {
          revert HblocksList. apply penWasMappedRemoveDesc; trivial.
          1,2,3,4: unfold consistency in *; unfold consistency1 in *; intuition.
          rewrite <-HlastBlock. rewrite HblocksListLast in *. intro Hcontra. rewrite Hcontra in *. simpl in *.
          apply NoDup_cons_iff in HnoDupBlocksList. destruct HnoDupBlocksList as (HfirstNotInRest & HnoDupBlocksList).
          apply Lib.in_app_or_neg in HfirstNotInRest. destruct HfirstNotInRest as (_ & HbeqFirstBTR). simpl in *.
          apply Decidable.not_or in HbeqFirstBTR. destruct HbeqFirstBTR as (HbeqFirstBTR & _).
          destruct HpenInList as [HcontraFirst | HcontraTail]; try(congruence).
          apply NoDup_remove_2 in HnoDupBlocksList. rewrite app_nil_r in *. congruence.
        }
        destruct HpenMapped as [partPen (_ & HpartPenIsPart & HpenMapped)].
        assert(HlookupSh1Eqs1: lookup sh1entryaddrBis (memory s1) beqAddr
          = lookup sh1entryaddrBis (memory s0) beqAddr).
        { revert HblocksList. apply lookupSh1EqRemoveDesc with idPart; trivial. }
        unfold sh1entryInChildLocation in *. rewrite HlookupSh1Eqs1 in *.
        assert(HchildLocBiss0: sh1entryInChildLocation sh1entryaddrBis blockToRemove s0).
        {
          unfold sh1entryInChildLocation. destruct (lookup sh1entryaddrBis (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). destruct HchildLocBiss1 as (HchildLocBiss1 & HBTRIsBE). split; trivial.
          intro. specialize(HBTRIsBE HbeqNullBTR). unfold isBE. rewrite <-HlookupBTREqs1s0. assumption.
        }
        assert(Hsh1Block: sh1entryAddr block sh1entryaddrBis s0).
        {
          unfold sh1entryAddr in *.
          destruct (lookup block (memory s1) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). assert(HblockIsBEs0: isBE block s0).
          {
            revert HblocksList. apply isBEPreservedRemoveDescRev. unfold isBE. rewrite HlookupBlock. trivial.
          }
          unfold isBE in *. destruct (lookup block (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        rewrite HgetPartsEqs1 in *. assert(HblockMappeds0: In block (getMappedBlocks part s0)).
        {
          revert HblocksList. apply getMappedBlocksImplRemoveDesc; trivial; unfold consistency in *;
            unfold consistency1 in *; intuition.
        }
        assert(Hsh1Pen: sh1entryAddr (last blocksListHd firstBlockToRemove)
          (CPaddr (last blocksListHd firstBlockToRemove+sh1offset)) s0).
        {
          apply IL.mappedBlockIsBE in HpenMapped. destruct HpenMapped as [bentry (Hlookup & _)].
          unfold sh1entryAddr. rewrite Hlookup. reflexivity.
        }
        assert(HPDchildPen: exists childPen,
          sh1entryPDchild (CPaddr (last blocksListHd firstBlockToRemove+sh1offset)) childPen s0).
        {
          unfold sh1entryPDchild. unfold sh1entryInChildLocation in *.
          destruct (lookup (CPaddr (last blocksListHd firstBlockToRemove+sh1offset)) (memory s0) beqAddr);
            try(exfalso; congruence). destruct v; try(exfalso; congruence). exists (PDchild s9). reflexivity.
        }
        destruct HPDchildPen as [childPen HPDchildPen]. assert(HbeqChildPenNull: childPen <> nullAddr).
        {
          intro. subst childPen. assert(HnullEquiv: childBlockNullIfChildNull s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HnullEquiv partPen (last blocksListHd firstBlockToRemove)
            (CPaddr (last blocksListHd firstBlockToRemove+sh1offset)) HpartPenIsPart HpenMapped Hsh1Pen
            HPDchildPen). unfold sh1entryInChildLocation in *.
          destruct (lookup (CPaddr (last blocksListHd firstBlockToRemove+sh1offset)) (memory s0) beqAddr);
            try(congruence). destruct v; try(congruence). destruct HchildLocLast as (HchildLocLast & _).
          destruct HnullEquiv as (HnullEquiv & _). rewrite <-HnullEquiv in *. congruence.
        }
        assert(HPDchildIsPDTBis: pdchildIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HPDchildIsPDTBis partPen (last blocksListHd firstBlockToRemove)
          (CPaddr (last blocksListHd firstBlockToRemove+sh1offset)) childPen HpartPenIsPart HpenMapped
          Hsh1Pen HPDchildPen HbeqChildPenNull).
        assert(HlocPen: childLocMappedInChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
        specialize(HlocPen  partPen (last blocksListHd firstBlockToRemove)
          (CPaddr (last blocksListHd firstBlockToRemove+sh1offset)) blockToRemove childPen HpartPenIsPart
          HpenMapped Hsh1Pen HPDchildPen HchildLocLast HbeqChildPenNull).
        destruct HlocPen as (_ & HBTRMappedPen & _). assert(childPen = idPart).
        {
          destruct (beqAddr childPen idPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HBTRMappeds0: In blockToRemove (getMappedBlocks idPart s0)).
          {
            revert HblocksList. apply getMappedBlocksImplRemoveDesc; trivial; unfold consistency in *;
              unfold consistency1 in *; intuition.
          }
          rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HBTRMappedPen.
          apply InFilterPresentInList in HBTRMappeds0. assert(HchildPenIsPDT: isPDT childPen s0).
          {
            unfold getKSEntries in *. unfold isPDT.
            destruct (lookup childPen (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          assert(HidIsPDTs0: isPDT idPart s0).
          {
            apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
          }
          specialize(Hdisjoint childPen idPart HchildPenIsPDT HidIsPDTs0 HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint blockToRemove HBTRMappedPen). congruence.
        }
        subst childPen. assert(partPen = part).
        {
          assert(HchildPart: pdchildIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HchildPart part block sh1entryaddrBis idPart HpartIsPart HblockMappeds0 Hsh1Block
            HPDchild HbeqChildNull).
          assert(HisParentPen: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HisParentPart: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HisParentPen idPart partPen HpartPenIsPart HPDchildIsPDTBis).
          specialize(HisParentPart idPart part HpartIsPart HchildPart). unfold pdentryParent in *.
          destruct (lookup idPart (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-HisParentPart in *. assumption.
        }
        subst part. assert(HblockIsLastHd: block = last blocksListHd firstBlockToRemove).
        {
          assert(HlocPen: childLocMappedInChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HlocBlk: childLocMappedInChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
          specialize(HlocPen partPen (last blocksListHd firstBlockToRemove)
            (CPaddr (last blocksListHd firstBlockToRemove+sh1offset)) blockToRemove idPart HpartPenIsPart HpenMapped
            Hsh1Pen HPDchildPen HchildLocLast HbeqChildPenNull). destruct HlocPen as (_ & _ & HstartsPenEq).
          specialize(HlocBlk partPen block sh1entryaddrBis blockToRemove idPart HpartIsPart HblockMappeds0
            Hsh1Block HPDchild HchildLocBiss0 HbeqChildNull). destruct HlocBlk as (_ & _ & HstartsBlockEq).
          assert(HstartPen: exists startPen, bentryStartAddr (last blocksListHd firstBlockToRemove) startPen s0).
          {
            apply IL.mappedBlockIsBE in HpenMapped. destruct HpenMapped as [bentry (Hlookup & _)].
            exists (startAddr (blockrange bentry)). unfold bentryStartAddr. rewrite Hlookup. reflexivity.
          }
          assert(HstartBlock: exists startBlock, bentryStartAddr block startBlock s0).
          {
            apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & _)].
            exists (startAddr (blockrange bentry)). unfold bentryStartAddr. rewrite Hlookup. reflexivity.
          }
          destruct HstartPen as [startPen HstartPen]. destruct HstartBlock as [startBlock HstartBlock].
          specialize(HstartsPenEq startPen HstartPen). specialize(HstartsBlockEq startBlock HstartBlock).
          unfold bentryStartAddr in *. destruct (lookup blockToRemove (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-HstartsPenEq in *. subst startBlock.
          apply uniqueBlockMapped with startPen partPen s0; trivial.
          - unfold consistency in *; unfold consistency2 in *; intuition.
          - unfold consistency in *; unfold consistency1 in *; intuition.
          - apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
          - apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          - apply IL.mappedBlockIsBE in HpenMapped. destruct HpenMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
        }
        rewrite <-HblockIsLastHd in *. assert(bentryPFlag block false s1).
        {
          revert HblocksList. apply blocksNotPresentAfterRemoveDesc; trivial.
        }
        apply IL.mappedBlockIsBE in HblockMappeds1. destruct HblockMappeds1 as [bentry (Hlookup & Hpres)].
        unfold bentryPFlag in *. rewrite Hlookup in *. congruence.
    }
    split.
    - destruct (beqAddr idPart idchild) eqn:HbeqParts.
      + specialize(HgetMappedBEqId blockChild). destruct HgetMappedBEqId as (HgetMappedBEqId & _).
        rewrite <-beqAddrTrue in HbeqParts. rewrite HbeqParts in *. apply HgetMappedBEqId in HBCMapped.
        destruct HBCMapped as [Hcontra | Hres]; try(exfalso; congruence). assumption.
      + rewrite <-beqAddrFalse in *. rewrite HgetMappedBEq; trivial. unfold isPDT. rewrite Hs3. simpl.
        destruct (beqAddr blockToRemove idchild) eqn:HbeqBTRChild.
        {
          rewrite <-beqAddrTrue in HbeqBTRChild. rewrite HbeqBTRChild in *. unfold isBE in *.
          unfold getMappedBlocks in *. unfold getKSEntries in *.
          destruct (lookup idchild (memory s1) beqAddr); try(congruence). destruct v; simpl in *; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqParts. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. unfold getMappedBlocks in *.
        unfold getKSEntries in *. destruct (lookup idchild (memory s1) beqAddr); try(simpl in *; congruence).
        destruct v; try(simpl in *; congruence). trivial.
    - intros startaddr Hstart. specialize(HstartsEq startaddr Hstart). unfold bentryStartAddr in *.
      rewrite HlookupsEq; trivial.
      + intro. subst blockChild. rewrite HlookupIds1 in *. congruence.
      + intro. subst blockChild. rewrite HlookupSh1 in *. congruence.
      + intro. subst blockChild. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s1) beqAddr); try(congruence).
        destruct v; congruence.
  }

  assert(forall parent childPart block startChild endChild,
     blockToRemoveInDescendant <> block
     -> In parent (getPartitions multiplexer s)
     -> In childPart (getChildren parent s)
     -> In block (getMappedBlocks childPart s)
     -> bentryStartAddr block startChild s
     -> bentryEndAddr block endChild s
     -> bentryPFlag block true s
     -> exists blockParent startParent endParent,
         In blockParent (getMappedBlocks parent s)
         /\ bentryStartAddr blockParent startParent s
         /\ bentryEndAddr blockParent endParent s /\ startParent <= startChild /\ endParent >= endChild).
  { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
    intros pdparent childPart block startChild endChild HbeqDescBlock HparentIsPart HchildIsChild HblockMapped
      HstartBlock HendBlock HPflagBlock. rewrite HgetPartsEq in *. assert(isPDT pdparent s2).
    {
      rewrite <-HgetPartsEqs2 in *. apply IL.partitionsArePDT; trivial; unfold cons1Free in *; intuition.
    }
    rewrite HgetChildrenEq in *; trivial. assert(HbeqBTRBlock: blockToRemove <> block).
    {
      unfold bentryPFlag in *. intro. subst block. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
      rewrite Hlookups in *. simpl in *. congruence.
    }
    assert(HblockMappeds1: In block (getMappedBlocks childPart s1)).
    {
      destruct (beqAddr idPart childPart) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst childPart. specialize(HgetMappedBEqId block).
        destruct HgetMappedBEqId as (_ & HgetMappedBEqId & _). apply HgetMappedBEqId; assumption.
      - rewrite <-beqAddrFalse in *. rewrite <-HgetMappedBEq; trivial. assert(isPDT childPart s1).
        {
          apply IL.childrenArePDT with pdparent; trivial; unfold cons1Free in *; intuition.
        }
        unfold isPDT in *. rewrite Hs3. simpl. destruct (beqAddr blockToRemove childPart) eqn:HbeqBTRChild.
        {
          rewrite <-beqAddrTrue in HbeqBTRChild. subst childPart. unfold isBE in *.
          destruct (lookup blockToRemove (memory s1) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqParts. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
    {
      apply HlookupsEq; trivial.
      - intro. subst block. destruct HPDT as [_ [pdentrys (_ & Hlookups & _)]]. rewrite Hlookups in *. congruence.
      - intro. subst block. rewrite HSHE in *. congruence.
      - intro. subst block. rewrite HSCE in *. congruence.
    }
    rewrite HlookupBlockEq in *. specialize(HparentEquivPartial pdparent childPart block startChild endChild
      HbeqBTRBlock HparentIsPart HchildIsChild HblockMappeds1 HstartBlock HendBlock HPflagBlock).
    destruct HparentEquivPartial as [blockParent [startP [endP (HblockPMapped & HstartP & HendP & HlebStarts &
      HgebEnds)]]]. exists blockParent. exists startP. exists endP.
    assert(HisParent: isParent s1) by (unfold cons1Free in *; intuition).
    specialize(HisParent childPart pdparent HparentIsPart HchildIsChild). unfold pdentryParent in *.
    destruct (lookup childPart (memory s1) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold cons1Free in *; intuition).
    specialize(HparentOfPart childPart p HlookupChild).
    destruct HparentOfPart as (HparentIsPartB & HparentOfRoot & HbeqParentChild).
    assert(HbeqChildRoot: childPart <> constantRootPartM).
    {
      intro Hcontra. specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *. subst pdparent.
      assert(isPDT nullAddr s1) by (apply IL.partitionsArePDT; trivial; unfold cons1Free in *; intuition).
      assert(isPADDR nullAddr s1) by (unfold cons1Free in *; intuition). unfold isPDT in *. unfold isPADDR in *.
      destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    specialize(HparentIsPartB HbeqChildRoot). destruct HparentIsPartB as ([parentEntry HlookupParent] & _).
    assert(HchildBlockProps: childsBlocksPropsInParent s1) by (unfold cons2FreeRemove in *; intuition).
    assert(HPflagP: bentryPFlag blockParent true s1).
    {
      apply IL.mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite Hlookup. auto.
    }
    assert(HPflag: bentryPFlag block true s1).
    {
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
      unfold bentryPFlag. rewrite <-HlookupBlockEq. rewrite Hlookup. auto.
    }
    specialize(HchildBlockProps childPart pdparent block startChild endChild blockParent startP endP
      HparentIsPart HchildIsChild HblockMappeds1 HstartBlock HendBlock HPflagBlock HblockPMapped HstartP HendP
      HPflagP HlebStarts HgebEnds). destruct HchildBlockProps as (_ & HchildNotNull & HchildLocNotNull & _).
    assert(blockToRemove <> blockParent).
    {
      intro. subst blockParent. specialize(HchildLocNotNull blockToRemoveInDescendant HchildLocs1).
      destruct HchildLocNotNull as (HbeqBlockCNull & HblocksEq). destruct (beqAddr startP startChild) eqn:HbeqStarts.
      - rewrite <-beqAddrTrue in HbeqStarts. specialize(HblocksEq HbeqStarts). congruence.
      - rewrite <-beqAddrFalse in *. assert(HltStarts: startP < startChild).
        { apply paddrNeqNatNeqEquiv in HbeqStarts. lia. }
        assert(HbeqChildNull: child <> nullAddr).
        {
          assert(HnullEq: childBlockNullIfChildNull s1) by (unfold cons1Free in *; intuition). intro. subst child.
          specialize(HnullEq idPart blockToRemove (CPaddr (blockToRemove+sh1offset)) HidIsParts1 HBTRMappeds1
            Hsh1s1 HPDchilds1). unfold sh1entryInChildLocation in *. rewrite HlookupSh1 in *.
          destruct HchildLocs1 as (HchildLocs1 & _). destruct HnullEq as (Hcontra & _). rewrite <-Hcontra in *.
          congruence.
        }
        assert(HbeqIdParent: idPart = parent p).
        {
          destruct (beqAddr idPart (parent p)) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. exfalso. unfold getMappedBlocks in *.
          apply InFilterPresentInList in HblockPMapped. apply InFilterPresentInList in HBTRMappeds1.
          assert(Hdisjoint: DisjointKSEntries s1) by (unfold cons1Free in *; intuition).
          assert(HparentIsPDTs1: isPDT (parent p) s1) by (unfold isPDT; rewrite HlookupParent; trivial).
          specialize(Hdisjoint idPart (parent p) HidIsPDTs1 HparentIsPDTs1 HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint blockToRemove HBTRMappeds1). congruence.
        }
        rewrite <-HbeqIdParent in *. specialize(HPDchildIsPDT HbeqChildNull). specialize(HdescProps HbeqBlockCNull).
        destruct HdescProps as (_ & HdescMappeds1 & HstartsEqDesc). specialize(HstartsEqDesc startP HstartP).
        assert(Hwell: wellFormedBlock s1) by (unfold cons1Free in *; intuition).
        specialize(Hwell block startChild endChild HPflagBlock HstartBlock HendBlock). destruct Hwell as (Hwell & _).
        assert(HstartInRange: In startChild (getAllPaddrBlock startP endP)).
        { apply IL.getAllPaddrBlockIncl; lia. }
        specialize(HdescIsFullRange HbeqBlockCNull startP endP HstartP HendP).
        destruct HdescIsFullRange as (_ & HendC).
        assert(HstartInBTRDesc: In startChild (getAllPaddrAux [blockToRemoveInDescendant] s1)).
        {
          simpl. destruct (lookup blockToRemoveInDescendant (memory s1) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartsEqDesc. rewrite <-HendC. assumption.
        }
        assert(HstartInBlock: In startChild (getAllPaddrAux [block] s1)).
        {
          simpl. destruct (lookup block (memory s1) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite <-HstartBlock. rewrite <-HendBlock. rewrite app_nil_r.
          apply IL.getAllPaddrBlockIncl; lia.
        }
        subst pdparent. assert(child = childPart).
        {
          destruct (beqAddr child childPart) eqn:HbeqChildren; try(rewrite beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. exfalso.
          specialize(HPIs1 idPart child childPart HidIsParts1 HPDchildIsPDT HchildIsChild HbeqChildren).
          assert(HstartUsedChild: In startChild (getUsedPaddr child s1)).
          {
            unfold getUsedPaddr. apply in_or_app. right.
            apply IL.addrInBlockIsMapped with blockToRemoveInDescendant; trivial.
          }
          specialize(HPIs1 startChild HstartUsedChild). contradict HPIs1. unfold getUsedPaddr. apply in_or_app. right.
          apply IL.addrInBlockIsMapped with block; trivial.
        }
        subst childPart. assert(HnoDupMappedP: noDupMappedPaddrList s1) by (unfold cons2FreeRemove in *; intuition).
        assert(HchildIsPDT: isPDT child s1) by (unfold isPDT; rewrite HlookupChild; trivial).
        pose proof (DisjointPaddrInPart child blockToRemoveInDescendant block startChild s1 HnoDupMappedP HchildIsPDT
          HdescMappeds1 HblockMappeds1 HbeqDescBlock HstartInBTRDesc). congruence.
    }
    assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
    {
      unfold bentryPFlag in *. apply HlookupsEq; trivial.
      - intro. subst blockParent. rewrite HlookupIds1 in *. congruence.
      - intro. subst blockParent. rewrite HlookupSh1 in *. congruence.
      - intro. subst blockParent. unfold isSCE in *.
        destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s1) beqAddr); try(congruence).
        destruct v; congruence.
    }
    rewrite HlookupBlockPEq. split; auto. rewrite <-HisParent in *. destruct (beqAddr idPart pdparent) eqn:HbeqParts.
    - specialize(HgetMappedBEqId blockParent). destruct HgetMappedBEqId as (HgetMappedBEqId & _).
      rewrite <-beqAddrTrue in HbeqParts. rewrite HbeqParts in *. apply HgetMappedBEqId in HblockPMapped.
      destruct HblockPMapped as [Hcontra | Hres]; try(exfalso; congruence). assumption.
    - rewrite <-beqAddrFalse in *. rewrite HgetMappedBEq; trivial. unfold isPDT. rewrite Hs3. simpl.
      destruct (beqAddr blockToRemove pdparent) eqn:HbeqBTRParent.
      {
        rewrite <-beqAddrTrue in HbeqBTRParent. rewrite HbeqBTRParent in *. unfold isBE in *.
        rewrite HlookupParent in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END blockInChildHasAtLeastEquivalentBlockInParent *)
  }

  assert(HdescPropsOr: blockToRemoveInDescendant = nullAddr /\ child = nullAddr
    \/ In child (getPartitions multiplexer s) /\ In blockToRemoveInDescendant (getMappedBlocks child s)
      /\ bentryAFlag blockToRemoveInDescendant true s).
  {
    destruct (beqAddr child nullAddr) eqn:HbeqChildNull.
    - rewrite <-beqAddrTrue in HbeqChildNull. subst child.
      assert(HbeqDescNull: blockToRemoveInDescendant = nullAddr).
      {
        destruct (beqAddr blockToRemoveInDescendant nullAddr) eqn:HbeqDescNull; try(rewrite beqAddrTrue; assumption).
        rewrite <-beqAddrFalse in *. exfalso. specialize(HdescProps HbeqDescNull). destruct HdescProps. congruence.
      }
      auto.
    - rewrite <-beqAddrFalse in *.
      specialize(HlocPropsPartial idPart blockToRemove (CPaddr (blockToRemove+sh1offset)) blockToRemoveInDescendant
        child HbeqFirstDesc HidIsParts1 HBTRMappeds1 Hsh1s1 HPDchilds1 HchildLocs1 HbeqChildNull).
      destruct HlocPropsPartial as (HbeqDescNull & HdescMapped & HstartsEq). specialize(HdescIsAcc HbeqDescNull).
      right. rewrite HgetPartsEq. split; try(split).
      + specialize(HPDchildIsPDT HbeqChildNull). apply IL.childrenPartitionInPartitionList with idPart; trivial.
        unfold cons1Free in *; intuition.
      + destruct (beqAddr idPart child) eqn:HbeqIdChild.
        * rewrite <-beqAddrTrue in HbeqIdChild. (*actually false, but faster*) subst child.
          specialize(HgetMappedBEqId blockToRemoveInDescendant). destruct HgetMappedBEqId as (HgetMappedBEqId & _).
          apply HgetMappedBEqId in HdescMapped. destruct HdescMapped as [Hcontra | Hres]; try(exfalso; congruence).
          assumption.
        * rewrite <-beqAddrFalse in *. rewrite HgetMappedBEq; trivial. unfold getMappedBlocks in *.
          unfold getKSEntries in *. unfold isPDT. rewrite Hs3. simpl.
          destruct (beqAddr blockToRemove child) eqn:HbeqBTRChild.
          {
            rewrite <-beqAddrTrue in HbeqBTRChild. subst child. destruct HBE as [bentry0 [_ [_ (Hlookups1 & _)]]].
            rewrite Hlookups1 in *. simpl in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqIdChild. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup child (memory s1) beqAddr); try(simpl in *; congruence).
          destruct v; try(simpl in *; congruence). trivial.
      + unfold bentryAFlag in *. rewrite HlookupsEq; trivial.
        * intro. subst blockToRemoveInDescendant. rewrite HlookupIds1 in *. congruence.
        * intro. subst blockToRemoveInDescendant. rewrite HlookupSh1 in *. congruence.
        * intro. subst blockToRemoveInDescendant. unfold isSCE in *.
          destruct (lookup (CPaddr (blockToRemove + scoffset)) (memory s1) beqAddr); try(simpl in *; congruence).
          destruct v; simpl in *; congruence.
  }

  assert(HPIs: partitionsIsolation s).
  { revert HlookupsEq. apply partitionsIsolationPreservedRemove; trivial; unfold cons1Free in *; intuition. }

  assert(HKDIs: kernelDataIsolation s).
  { revert HlookupsEq. apply kernelDataIsolationPreservedRemove; trivial; unfold cons1Free in *; intuition. }

  assert(HnextBTR: exists nextBlockBTR, scentryNext (CPaddr (blockToRemove + scoffset)) nextBlockBTR s1).
  {
    unfold scentryNext. unfold isSCE in *.
    destruct (lookup (CPaddr (blockToRemove+scoffset)) (memory s1) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists (next s8). reflexivity.
  }
  destruct HnextBTR as [nextBlockBTR HnextBTR]. assert(nextBlockBTR = nullAddr).
  {
    destruct (beqAddr nextBlockBTR nullAddr) eqn:HbeqNextNull; try(rewrite beqAddrTrue; assumption). exfalso.
    rewrite <-beqAddrFalse in *.
nextImpliesBlockWasCut / blockAndNextAreSideBySide + childsBlocksPropsInParent?
  }
  subst nextBlockBTR.

  assert(exists statesListRec blocksListRec parentsListRec sInit,
    removedBlockInDescRec s sInit firstPart firstBlockToRemove statesListRec blocksListRec parentsListRec
    /\ blockToRemoveInDescendant = last blocksListRec firstBlockToRemove
    /\ child = last parentsListRec firstPart
    /\ P sInit
    /\ consistency sInit
    /\ partitionsIsolation sInit
    /\ kernelDataIsolation sInit
    /\ verticalSharing sInit
    /\ In firstPart (getPartitions multiplexer sInit)
    /\ In firstBlockToRemove (getMappedBlocks firstPart sInit)).
  {
    exists (statesList++[s]). exists (blocksList++[blockToRemoveInDescendant]). exists (parentsList++[child]).
    exists s0. rewrite last_last. rewrite last_last. split.
    - revert HblocksList. apply removedBlockInDescRecRec with idPart blockToRemove; trivial.
    - intuition.
  }

  split. admit. split; trivial. split. unfold cons2FreeRemove. intuition. split; trivial. split; trivial.
  split; trivial. split. admit. split. admit. split; trivial. split; trivial. split; trivial. split; trivial.
  intuition.
(*TODO HERE use HchildLocMappedInChildPartials for a lemma*)

  assert(forall childrenList, isChildBlocksList s childrenList blockToRemoveInDescendant -> length childrenList < n).
  {
    intros childrenList HchildrenList. apply HlenPropsRec. (*TODO HERE*)
    assert(~ In blockToRemove (blockToRemoveInDescendant::childrenList)).
    {
      simpl. apply Classical_Prop.and_not_or. split; auto. destruct childrenList; auto.
      assert(HbeqDescNull: blockToRemoveInDescendant <> nullAddr).
      {
        intro. subst blockToRemoveInDescendant. simpl in *.
        assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
        destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      specialize(HdescProps HbeqDescNull). destruct HdescProps as (HbeqChildNull & HDescMapped & _).
      specialize(HPDchildIsPDT HbeqChildNull). destruct childrenList.
      - simpl in *. apply Classical_Prop.and_not_or. split; auto. admit.
        (*assert(HlocalChildList: isChildBlocksList s1 [blockToRemoveInDescendant;p] blockToRemove).
        {
          simpl. unfold isBE in *.
          destruct (lookup blockToRemove (memory s1) beqAddr) eqn:HlookupBTR; try(congruence).
          destruct v; try(congruence). unfold sh1entryInChildLocation in *. rewrite HlookupSh1 in *.
          destruct HchildLocs1 as (HchildLocs1 & HlocIsBE). split; auto. split; trivial.
          assert(HlookupEqDesc: lookup blockToRemoveInDescendant (memory s) beqAddr
            = lookup blockToRemoveInDescendant (memory s1) beqAddr).
          {
            clear HchildLocs1. apply HlookupsEq; trivial.
            - intro. subst blockToRemoveInDescendant. destruct HPDT as [_ [pdentys (_ & Hlookups & _)]].
              rewrite Hlookups in *. congruence.
            - intro. subst blockToRemoveInDescendant. rewrite HSHE in *. congruence.
            - intro. subst blockToRemoveInDescendant. rewrite HSCE in *. congruence.
          }
          rewrite <-HlookupEqDesc. destruct (lookup blockToRemoveInDescendant (memory s) beqAddr); try(congruence).
          destruct v; try(congruence).
          assert(HlookupEqDescSh1: lookup (CPaddr (blockToRemoveInDescendant+sh1offset)) (memory s) beqAddr
            = lookup (CPaddr (blockToRemoveInDescendant+sh1offset)) (memory s1) beqAddr).
          {
            apply HlookupsEq.
            - intro Hcontra. rewrite Hcontra in *. destruct HPDT as [_ [pdentys (_ & Hlookups & _)]].
              rewrite Hlookups in *. congruence.
            - intro Hcontra. rewrite Hcontra in *. destruct HBE as [bentry0 [l [newEnd (_ & _ & Hlookups)]]].
              rewrite Hlookups in *. congruence.
            - intro Hcontra. apply CPaddrAddEq in Hcontra; try(congruence). intro HcontraBis. rewrite HcontraBis in *.
              assert(isPADDR nullAddr s1) by (unfold cons1Free in *; intuition). unfold isPADDR in *.
              rewrite HlookupSh1 in *. congruence.
            - intro Hcontra. rewrite Hcontra in *. rewrite HSCE in *. congruence.
          }
          rewrite <-HlookupEqDescSh1.
          destruct (lookup (CPaddr (blockToRemoveInDescendant + sh1offset)) (memory s) beqAddr) eqn:HlookupSh1Desc;
            try(congruence). destruct v; try(congruence). destruct HchildrenList as (HlocDesc & HlocDescIsBE & _).
          split; trivial. split; trivial. intro HbeqPNull. specialize(HlocDescIsBE HbeqPNull).
          destruct (beqAddr blockToRemove p) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. rewrite <-HbeqBlocks in *. rewrite HlookupBTR. trivial.
          - rewrite <-beqAddrFalse in *. clear HlocDesc. rewrite <-HlookupsEq; trivial.
            + intro. subst p. destruct HPDT as [_ [pdentys (_ & Hlookups & _)]].
              rewrite Hlookups in *. congruence.
            + intro. subst p. rewrite HSHE in *. congruence.
            + intro. subst p. rewrite HSCE in *. congruence.
        }
        assert(HnoDupLocal: NoDup [blockToRemove; blockToRemoveInDescendant; p]).
        {
          revert HlocalChildList. apply noDupChildrenList.
          1,2,3,4,5,6,7,8: 
          9? NOPE
        }*)
(*HchildLocMappedInChildPartials*)
      - assert(HparentsListNotEmpty: partitionsFromChildList s (p::p0::childrenList) blockToRemoveInDescendant <> []).
        {
          simpl in *. destruct (lookup blockToRemoveInDescendant (memory s) beqAddr); try(congruence).
          destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToRemoveInDescendant + sh1offset)) (memory s) beqAddr) eqn:HlookupSh1Desc;
            try(congruence). destruct v; try(congruence).
          destruct HchildrenList as (HchildLoc & HlocIsBE & HchildrenList). assert(HbeqLocNull: p <> nullAddr).
          {
            intro Hcontra. rewrite Hcontra in *. assert(isPADDR nullAddr s) by (unfold cons1Free in *; intuition).
            unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
            destruct v; congruence.
          }
          assert(HbeqPDchildNull: beqAddr (PDchild s8) nullAddr = false).
          {
            rewrite <-beqAddrFalse. intro Hcontra.
            assert(HPDchild: sh1entryPDchild (CPaddr (blockToRemoveInDescendant+sh1offset)) nullAddr s).
            { unfold sh1entryPDchild. rewrite HlookupSh1Desc. auto. }
            assert(Hres: childBlockNullIfChildNull s) by (unfold cons1Free in *; intuition). admit.
            (*specialize(Hres child blockToRemoveInDescendant (CPaddr (blockToRemoveInDescendant+sh1offset))
              HchildIsPart HdescMapped Hsh1Desc HPDchild).*)
          }
          rewrite HbeqPDchildNull. intro Hcontra. apply app_eq_nil in Hcontra. destruct Hcontra. congruence.
        }
        assert(HparentsList:
          isParentsList s (tl (partitionsFromChildList s (p::p0::childrenList) blockToRemoveInDescendant) ++ [child])
            (hd nullAddr (partitionsFromChildList s (p::p0::childrenList) blockToRemoveInDescendant ++ [child]))).
        {
          revert HchildrenList. apply partitionsFromChildListAreParentsList; trivial.
getMappedBlocks s -> HgetMappedBEq
HgetPartsEq
        noDupChildrenList partNotInParentsListMeansBlockNotInChildrenList
    }
    revert HchildrenList. apply isChildBlocksListEqRemoveNoBTR with idPart blockToRemove; trivial.
    unfold cons1Free in *; intuition.
  }

(*TODO HERE*)
(*TODO prove the new HBTRNotNext and HVSPartial*)
Qed.

Lemma removeBlockInDescendantsRec idPart blockToRemove firstPart firstBlockToRemove (P: state -> Prop):
{{
  fun s => (forall parentsList lastPart, isParentsList s parentsList lastPart
      -> idPart = last parentsList lastPart
      -> length parentsList < n)
    /\ consistency s
    /\ exists statesList blocksList parentsList s0,
        removedBlockRec s s0 firstPart firstBlockToRemove statesList blocksList parentsList
        /\ blockToRemove = last blocksList firstBlockToRemove
        /\ idPart = last parentsList firstPart
        /\ P s0
        /\ consistency s0
        /\ In firstBlockToRemove (getMappedBlocks firstBlockToRemove s0)
}}
removeBlockInDescendantsRecAux n idPart blockToRemove
{{
  fun removeBlockDescEnded s => consistency s
    /\ (exists statesList blocksList parentsList s0,
          removedBlockRec s s0 firstPart firstBlockToRemove statesList blocksList parentsList
          /\ nullAddr = last blocksList firstBlockToRemove
          /\ P s0
          /\ consistency s0)
    /\ removeBlockDescEnded = true
}}.
Proof.

Qed.

Lemma removeBlockInChildAndDescendants (currentPart blockToRemoveInCurrPartAddr idPDchild
  blockToRemoveInChildAddr : paddr) P :
{{ fun s => P s /\ consistency s /\ partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ isBE blockToRemoveInCurrPartAddr s
    /\ isBE blockToRemoveInChildAddr s
    /\ In blockToRemoveInCurrPartAddr (getMappedBlocks currentPart s)
    /\ In currentPart (getPartitions multiplexer s)
    /\ (exists sh1entryaddr,
        sh1entryPDchild sh1entryaddr idPDchild s
        /\ sh1entryAddr blockToRemoveInCurrPartAddr sh1entryaddr s
        /\ sh1entryInChildLocation sh1entryaddr blockToRemoveInChildAddr s)
    /\ beqAddr nullAddr blockToRemoveInChildAddr = false
    /\ beqAddr nullAddr idPDchild = false }}
Internal.removeBlockInChildAndDescendants currentPart blockToRemoveInCurrPartAddr idPDchild blockToRemoveInChildAddr
{{fun _ s => consistency s /\ partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
}}.
Proof.
unfold Internal.removeBlockInChildAndDescendants. eapply bindRev.
{ (** readBlockStartFromBlockEntryAddr *)
  eapply weaken. apply readBlockStartFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops. intuition.
}
intro globalIdBlockToRemove. eapply bindRev.
{ (** checkBlockCut *)
  eapply weaken. apply checkBlockCut. intros s Hprops. simpl. split. apply Hprops.
  unfold consistency in *; unfold consistency1 in *; intuition.
}
intro isBlockCut. destruct isBlockCut.
- (* case_eq isBlockCut = true *)
  eapply bindRev.
  { (** Internal.checkRemoveSubblocksRec *)
    eapply weaken. apply checkRemoveSubblocksRec. intros s Hprops. simpl. split. apply Hprops. unfold negb in *.
    destruct Hprops as (((HP & Hconsist & _ & _ & _ & HblockIsBE & HblockChildIsBE & HBTRMapped & HcurrIsPart & Hsh1 &
      HbeqNullBlock & HbeqNullChild)
      & Hstart) & [blockStart [blockOrigin [blockNext (Horigin & Hnext & HstartChild & HisCut)]]]). split; trivial.
    rewrite beqAddrSym in *. rewrite <-beqAddrFalse in *.
    destruct Hsh1 as [sh1entryaddr (HPDchild & Hsh1 & HchildLoc)].
    assert(HchildIsChild: pdchildIsPDT s) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HchildIsChild currentPart blockToRemoveInCurrPartAddr sh1entryaddr idPDchild HcurrIsPart HBTRMapped
      Hsh1 HPDchild HbeqNullChild).
    assert(HlocMapped: childLocMappedInChild s) by (unfold consistency in *; unfold consistency2 in *; intuition).
    specialize(HlocMapped currentPart blockToRemoveInCurrPartAddr sh1entryaddr blockToRemoveInChildAddr idPDchild
      HcurrIsPart HBTRMapped Hsh1 HPDchild HchildLoc HbeqNullChild HbeqNullBlock).
    assert(HchildIsPart: In idPDchild (getPartitions multiplexer s)).
    {
      apply IL.childrenPartitionInPartitionList with currentPart; trivial.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    instantiate(1:= blockToRemoveInChildAddr). instantiate(1:= idPDchild). intuition. exists []. simpl.
    split; trivial.
	}
	intro isRemovePossible. destruct (negb isRemovePossible) eqn:HremovePossible.
  + (* case_eq isRemovePossible = false *)
    eapply weaken. apply ret. intros s Hprops. simpl. intuition.
  + (* case_eq isRemovePossible = true *)
    apply negb_false_iff in HremovePossible. subst isRemovePossible. eapply bindRev.
    { (** removeSubblocksRec *)
      eapply weaken. apply removeSubblocksRec. intros s Hprops. simpl.
      destruct Hprops as ((((HP & Hconsist & HPI & HKDI & HVS & HBTRIsBE & HCTRIsBE & HBTRIsMapped & HcurrIsPart &
        Hprops) & HstartBTR) & HblocksList) & HnextBlocksList).
      assert(exists blocksList, checkRemoveOkRec blockToRemoveInChildAddr idPDchild blocksList s
        /\ nullAddr = last blocksList blockToRemoveInChildAddr).
      { apply HnextBlocksList; trivial. }
      assert(HnewProps: In blockToRemoveInChildAddr (getMappedBlocks idPDchild s)
        /\ In idPDchild (getPartitions multiplexer s)
        /\ bentryStartAddr blockToRemoveInChildAddr globalIdBlockToRemove s
        /\ exists blockNext, scentryNext (CPaddr (blockToRemoveInChildAddr + scoffset)) blockNext s
            /\ blockNext <> nullAddr).
      {
        destruct HblocksList as [blockStart [blockOrigin [blockNext (Horigin & Hnext & Hstart & Hcut)]]].
        unfold negb in Hcut. apply andb_false_iff in Hcut. rewrite <-beqAddrFalse in *. rewrite <-beqAddrFalse in *.
        assert(HlocMapped: childLocMappedInChild s) by (unfold consistency in *; unfold consistency2 in *; intuition).
        destruct Hprops as ([sh1entryaddr (HPDchild & Hsh1 & HchildLoc)] & HbeqNullBlockC & HbeqNullChild).
        apply not_eq_sym in HbeqNullChild. apply not_eq_sym in HbeqNullBlockC.
        specialize(HlocMapped currentPart blockToRemoveInCurrPartAddr sh1entryaddr blockToRemoveInChildAddr idPDchild
          HcurrIsPart HBTRIsMapped Hsh1 HPDchild HchildLoc HbeqNullChild HbeqNullBlockC).
        assert(HchildPDT: pdchildIsPDT s) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HchildPDT currentPart blockToRemoveInCurrPartAddr sh1entryaddr idPDchild HcurrIsPart HBTRIsMapped
          Hsh1 HPDchild HbeqNullChild).
        destruct HlocMapped as (HchildMapped & HstartsEq). split; trivial. split.
        - apply IL.childrenPartitionInPartitionList with currentPart; trivial.
          unfold consistency in *; unfold consistency1 in *; intuition.
        - specialize(HstartsEq globalIdBlockToRemove HstartBTR).
          assert(HequivBP: blockInChildHasAtLeastEquivalentBlockInParent s)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HPflag: bentryPFlag blockToRemoveInChildAddr true s).
          {
            apply IL.mappedBlockIsBE in HchildMapped. destruct HchildMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(HendC: exists endC, bentryEndAddr blockToRemoveInChildAddr endC s).
          {
            unfold bentryEndAddr. unfold bentryStartAddr in *.
            destruct (lookup blockToRemoveInChildAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
          }
          destruct HendC as [endC HendC].
          specialize(HequivBP currentPart idPDchild blockToRemoveInChildAddr globalIdBlockToRemove endC
            HcurrIsPart HchildPDT HchildMapped HstartsEq HendC HPflag).
          destruct HequivBP as [blockParent [startP [endP (HblockPMapped & HstartP & HendP & HlebStarts &
            HgebEnds)]]].
          assert(HPflagP: bentryPFlag blockToRemoveInCurrPartAddr true s).
          {
            apply IL.mappedBlockIsBE in HBTRIsMapped. destruct HBTRIsMapped as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(Hwell: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HendBP: exists endBP, bentryEndAddr blockToRemoveInCurrPartAddr endBP s).
          {
            unfold bentryEndAddr. unfold isBE in *.
            destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
          }
          destruct HendBP as [endBP HendBP].
          specialize(Hwell blockToRemoveInCurrPartAddr globalIdBlockToRemove endBP HPflagP HstartBTR HendBP).
          destruct Hwell as (Hwell & _).
          assert(HglobInBP: In globalIdBlockToRemove (getAllPaddrAux [blockToRemoveInCurrPartAddr] s)).
          {
            simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartBTR. rewrite <-HendBP.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          assert(HwellC: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HwellC blockToRemoveInChildAddr globalIdBlockToRemove endC HPflag HstartsEq HendC).
          destruct HwellC as (HwellC & _).
          assert(HcurrIsPDT: isPDT currentPart s).
          { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
          assert(blockToRemoveInCurrPartAddr = blockParent).
          {
            destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks;
              try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
            assert(HnoDupPaddr: noDupMappedPaddrList s)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            pose proof (DisjointPaddrInPart currentPart blockToRemoveInCurrPartAddr blockParent globalIdBlockToRemove
              s HnoDupPaddr HcurrIsPDT HBTRIsMapped HblockPMapped HbeqBlocks HglobInBP) as Hcontra.
            contradict Hcontra. unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
            assert(HPflagBP: bentryPFlag blockParent true s).
            {
              apply IL.mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
              unfold bentryPFlag. rewrite Hlookup. auto.
            }
            assert(HwellP: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HwellP blockParent startP endP HPflagBP HstartP HendP). destruct HwellP as (HwellP & _).
            destruct (lookup blockParent (memory s) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendP.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          subst blockParent. clear HblockPMapped. assert(HboundsEq: startP = globalIdBlockToRemove /\ endP = endBP).
          {
            unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). subst startP. subst endP. split; auto.
          }
          destruct HboundsEq. subst startP. subst endP. clear HstartP. clear HendP. clear HlebStarts.
          assert(HoriginIsStart: originIsParentBlocksStart s)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HeqTriv: CPaddr (blockToRemoveInChildAddr+scoffset) = CPaddr (blockToRemoveInChildAddr+scoffset))
            by reflexivity. assert(HchildIsPart: In idPDchild (getPartitions multiplexer s)).
          {
            apply IL.childrenPartitionInPartitionList with currentPart; trivial.
            unfold consistency in *; unfold consistency1 in *; intuition.
          }
          assert(HchildIsPDT: isPDT idPDchild s).
          { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
          apply isPDTLookupEq in HchildIsPDT. destruct HchildIsPDT as [pdentryChild HlookupChild].
          specialize(HoriginIsStart idPDchild pdentryChild blockToRemoveInChildAddr
            (CPaddr (blockToRemoveInChildAddr+scoffset)) blockOrigin HchildIsPart HlookupChild HchildMapped HeqTriv
            Horigin). destruct HoriginIsStart as (HoriginIsStart & _).
          assert(HisParent: isParent s) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HisParent idPDchild currentPart HcurrIsPart HchildPDT). unfold pdentryParent in *.
          rewrite HlookupChild in *.
          assert(HbeqChildRoot: idPDchild <> constantRootPartM).
          {
            assert(HparentOfPart: parentOfPartitionIsPartition s)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HparentOfPart idPDchild pdentryChild HlookupChild).
            destruct HparentOfPart as (_ & HparentOfRoot & _). intro Hcontra. specialize(HparentOfRoot Hcontra).
            rewrite <-HisParent in *. assert(isPDT currentPart s).
            { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
            assert(isPADDR nullAddr s) by (unfold consistency in *; unfold consistency1 in *; intuition).
            rewrite HparentOfRoot in *. unfold isPDT in *. unfold isPADDR in *.
            destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
          }
          specialize(HoriginIsStart HbeqChildRoot). destruct HoriginIsStart as [blockParent (HblockPMapped & HstartP &
            Hincl)].
          assert(blockToRemoveInCurrPartAddr = blockParent).
          {
            destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks;
              try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
            assert(HnoDupPaddr: noDupMappedPaddrList s)
              by (unfold consistency in *; unfold consistency2 in *; intuition). rewrite <-HisParent in *.
            pose proof (DisjointPaddrInPart currentPart blockToRemoveInCurrPartAddr blockParent globalIdBlockToRemove
              s HnoDupPaddr HcurrIsPDT HBTRIsMapped HblockPMapped HbeqBlocks HglobInBP) as Hcontra.
            contradict Hcontra. apply Hincl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
            destruct (lookup blockToRemoveInChildAddr (memory s) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartsEq. rewrite <-HendC.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          subst blockParent. unfold bentryStartAddr in *. split; trivial.
          exists blockNext. split; trivial. destruct Hcut as [HbeqStartOrigin | Hres]; trivial. exfalso.
          destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(congruence).
          destruct v; try(congruence). rewrite <-HstartP in *.
          destruct (lookup blockToRemoveInChildAddr (memory s) beqAddr); try(congruence).
          destruct v; congruence.
      }
      instantiate(1 := fun s => P s /\ consistency s /\ partitionsIsolation s /\ kernelDataIsolation s
        /\ verticalSharing s /\ isBE blockToRemoveInCurrPartAddr s
        /\ isBE blockToRemoveInChildAddr s
        /\ bentryStartAddr blockToRemoveInCurrPartAddr globalIdBlockToRemove s
        /\ bentryStartAddr blockToRemoveInChildAddr globalIdBlockToRemove s
        /\ In blockToRemoveInCurrPartAddr (getMappedBlocks currentPart s)
        /\ In currentPart (getPartitions multiplexer s)
        /\ (exists sh1entryaddr, sh1entryPDchild sh1entryaddr idPDchild s
           /\ sh1entryAddr blockToRemoveInCurrPartAddr sh1entryaddr s
           /\ sh1entryInChildLocation sh1entryaddr blockToRemoveInChildAddr s)
        /\  beqAddr nullAddr blockToRemoveInChildAddr = false /\ beqAddr nullAddr idPDchild = false
        /\ In blockToRemoveInChildAddr (getMappedBlocks idPDchild s)
        /\ In idPDchild (getPartitions multiplexer s)
        /\ (exists blocksList, checkRemoveOkRec blockToRemoveInChildAddr idPDchild blocksList s
            /\ nullAddr = last blocksList blockToRemoveInChildAddr)
        /\ exists blockNext, scentryNext (CPaddr (blockToRemoveInChildAddr + scoffset)) blockNext s
            /\ blockNext <> nullAddr).
      intuition.
    }
    intro recRemoveSubblocksEnded. destruct recRemoveSubblocksEnded.
    * (* case recRemoveSubblocksEnded = true *)
      eapply bindRev.
      { (** MAL.writeBlockAccessibleFromBlockEntryAddr *)
        eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr. intros s Hprops. simpl.
        destruct Hprops as (Hconsist & HnoDupPaddr & Hprops & _).
        assert(HBTRIsBE: isBE blockToRemoveInCurrPartAddr s).
        {
          destruct Hprops as [statesList [blocksList [s0 (HblocksList & Hlast & HP & Hconsists0 & HPI & HKDI & HVS &
            HBTRIsBEs0 & Hprops)]]]. revert HblocksList.
          apply isBEEqRemoveRec; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
        }
        unfold isBE in HBTRIsBE.
        destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr) eqn:HlookupBTR; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. split; trivial.
        instantiate(1 := fun _ s => exists s1 bentry1,
          s = {|
                currentPartition := currentPartition s1;
                memory :=
                  add blockToRemoveInCurrPartAddr
                    (BE (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) (present bentry1) true
                      (blockindex bentry1) (blockrange bentry1)))
                    (memory s1) beqAddr
              |}
          /\ lookup blockToRemoveInCurrPartAddr (memory s1) beqAddr = Some(BE bentry1)
          /\ cons1Free s1 /\ noDupMappedPaddrList s1
          /\ exists statesList blocksList s0,
              removedBlockRec s1 s0 idPDchild blockToRemoveInChildAddr statesList blocksList
              /\ nullAddr = last blocksList blockToRemoveInChildAddr
              /\ P s0
              /\ consistency s0 /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
              /\ isBE blockToRemoveInCurrPartAddr s0
              /\ isBE blockToRemoveInChildAddr s0
              /\ bentryStartAddr blockToRemoveInCurrPartAddr globalIdBlockToRemove s0
              /\ bentryStartAddr blockToRemoveInChildAddr globalIdBlockToRemove s0
              /\ In blockToRemoveInCurrPartAddr (getMappedBlocks currentPart s0)
              /\ In currentPart (getPartitions multiplexer s0)
              /\ (exists sh1entryaddr,
                   sh1entryPDchild sh1entryaddr idPDchild s0
                   /\ sh1entryAddr blockToRemoveInCurrPartAddr sh1entryaddr s0
                   /\ sh1entryInChildLocation sh1entryaddr blockToRemoveInChildAddr s0)
              /\ beqAddr nullAddr blockToRemoveInChildAddr = false
              /\ beqAddr nullAddr idPDchild = false
              /\ In blockToRemoveInChildAddr (getMappedBlocks idPDchild s0)
              /\ In idPDchild (getPartitions multiplexer s0)
              /\ (exists nextBlocksList,
                   checkRemoveOkRec blockToRemoveInChildAddr idPDchild nextBlocksList s0
                   /\ nullAddr = last nextBlocksList blockToRemoveInChildAddr)
              /\ exists blockNext,
                  scentryNext (CPaddr (blockToRemoveInChildAddr + scoffset)) blockNext s0
                  /\ blockNext <> nullAddr). simpl. exists s. exists b.
        intuition.
      }
      intros. eapply bindRev.
      { (** MAL.readBlockEndFromBlockEntryAddr **)
        eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
        destruct Hprops as [s1 [bentry1 (Hs & _)]]. unfold isBE. rewrite Hs. simpl. rewrite IL.beqAddrTrue. trivial.
      }
      intro endBlockToRemove. eapply bindRev.
      { (** MAL.writeSh1EntryFromBlockEntryAddr **)
        eapply weaken. apply writeSh1EntryFromBlockEntryAddr. intros s Hprops. simpl.
        destruct Hprops as ([s1 [bentry1 (Hs & HlookupBlockPs1 & Hconss1 & HnoDupPaddrs1 & [statesList [blocksList
          [s0 (HblocksList & Hlast & HP & Hconsists0 & HPIs0 & HKDIs0 & HVSs0 & HblockPIsBEs0 & HblockCIsBEs0 &
          HstartP & HstartC & HblockPMappeds0 & HcurrIsParts0 & [sh1entryaddr (HPDchildPs0 & Hsh1Ps0 & HchildLocPs0)]
          & HbeqNullBlockC & HbeqNullChild & HblockCMappeds0 & HchildIsParts0 & HnextBlocksList & HnextNotNull)]]])]]
          & HendP).
        assert(HnewB: exists l, CBlockEntry (read bentry1) (write bentry1) (exec bentry1) (present bentry1) true
              (blockindex bentry1) (blockrange bentry1)
            = {|
                read := read bentry1;
                write := write bentry1;
                exec := exec bentry1;
                present := present bentry1;
                accessible := true;
                blockindex := blockindex bentry1;
                blockrange := blockrange bentry1;
                Hidx := l
              |}).
        {
          unfold CBlockEntry. assert(blockindex bentry1 < kernelStructureEntriesNb) by (apply Hidx).
          destruct (lt_dec (blockindex bentry1) kernelStructureEntriesNb); try(lia).
          exists (ADT.CBlockEntry_obligation_1 (blockindex bentry1) l). reflexivity.
        }

        assert(Hconsistss1: consistency1 s1).
        {
          assert(blockInChildHasAtLeastEquivalentBlockInParent s1).
          { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s1 *)
            assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition). revert HblocksList Hlast.
            apply blockInChildHasAtLeastEquivalentBlockInParentPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
            (* END blockInChildHasAtLeastEquivalentBlockInParent *)
          }

          assert(originIsParentBlocksStart s1).
          { (* BEGIN originIsParentBlocksStart s1 *)
            assert(Hcons0: originIsParentBlocksStart s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition). revert HblocksList Hlast.
            apply originIsParentBlocksStartPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
            (* END originIsParentBlocksStart *)
          }

          assert(nextImpliesBlockWasCut s1).
          { (* BEGIN nextImpliesBlockWasCut s1 *)
            assert(Hcons0: nextImpliesBlockWasCut s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition). revert HblocksList Hlast.
            apply nextImpliesBlockWasCutPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
            (* END nextImpliesBlockWasCut *)
          }
          unfold consistency1. unfold cons1Free in *. intuition.
        }

        assert(HchildIsChild: In idPDchild (getChildren currentPart s0)).
        {
          assert(Hres: pdchildIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hres currentPart blockToRemoveInCurrPartAddr sh1entryaddr idPDchild HcurrIsParts0).
          rewrite <-beqAddrFalse in *. apply Hres; auto.
        }
        assert(HchildIsPDT: isPDT idPDchild s0).
        { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
        assert(HlookupChild: exists pdentry, lookup idPDchild (memory s0) beqAddr = Some(PDT pdentry)).
        { apply isPDTLookupEq. assumption. }
        destruct HlookupChild as [pdentry HlookupChild].
        assert(HisParent: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HisParent idPDchild currentPart HcurrIsParts0 HchildIsChild). unfold pdentryParent in *.
        rewrite HlookupChild in *.
        assert(HbeqPartRoot: idPDchild <> constantRootPartM).
        {
          assert(HparentOfPart: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HparentOfPart idPDchild pdentry HlookupChild).
          destruct HparentOfPart as (_ & HparentOfRoot & _). intro Hcontra. specialize(HparentOfRoot Hcontra).
          rewrite <-HisParent in *. assert(isPDT currentPart s0).
          { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
          assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          rewrite HparentOfRoot in *. unfold isPDT in *. unfold isPADDR in *.
          destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        assert(HparentOfPart: parentOfPartitionIsPartition s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HparentOfPart idPDchild pdentry HlookupChild).
        destruct HparentOfPart as (_ & _ & HbeqCurrChild). rewrite <-HisParent in *.
        assert(HcurrIsPDT: isPDT currentPart s0).
        {
          apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
        }
        assert(HblockPNotIn: ~In blockToRemoveInCurrPartAddr (blockToRemoveInChildAddr::blocksList)).
        {
          assert(HblocksAreInChild: forall block, block <> nullAddr
            -> In block (blockToRemoveInChildAddr::blocksList)
            -> In block (getMappedBlocks idPDchild s0)).
          {
            simpl. intros block HbeqBlockNull HblockIn.
            destruct HblockIn as [HbeqBlocks | HblockIn]; try(subst block; assumption). revert HblocksList.
            apply removeRecBlocksWereMapped; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
          }
          assert(HbeqBlockPNull: blockToRemoveInCurrPartAddr <> nullAddr).
          {
            intro Hcontra. subst blockToRemoveInCurrPartAddr. assert(isPADDR nullAddr s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition). unfold isPADDR in *.
            unfold isBE in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          intro Hcontra. specialize(HblocksAreInChild blockToRemoveInCurrPartAddr HbeqBlockPNull Hcontra).
          unfold getMappedBlocks in *. apply InFilterPresentInList in HblocksAreInChild.
          apply InFilterPresentInList in HblockPMappeds0. assert(Hdisjoint: DisjointKSEntries s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hdisjoint currentPart idPDchild HcurrIsPDT HchildIsPDT HbeqCurrChild).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint blockToRemoveInCurrPartAddr HblockPMappeds0). congruence.
        }

        assert(HblockCIsNoNext: forall part block scnext,
          In part (getPartitions multiplexer s0)
          -> In block (getMappedBlocks part s0)
          -> scentryNext (CPaddr (block + scoffset)) scnext s0
          -> scnext <> nullAddr -> blockToRemoveInChildAddr <> scnext).
        {
          destruct HnewB as [l HnewB].
          intros part block scnext HpartIsPart HblockMapped Hnext HbeqNextNull HbeqBlockCNext. subst scnext.
          assert(HnextBlockSide: blockAndNextAreSideBySide s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(Hbounds: (exists startaddr endaddr, bentryStartAddr block startaddr s0
            /\ bentryEndAddr block endaddr s0) /\ bentryPFlag block true s0).
          {
            apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
            unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryPFlag. rewrite Hlookup. split; auto.
            exists (startAddr (blockrange bentry)). exists (endAddr (blockrange bentry)). auto.
          }
          destruct Hbounds as ([startaddr [endaddr (Hstart & Hend)]] & HPflag).
          assert(HeqTriv: CPaddr (block+scoffset) = CPaddr (block+scoffset)) by reflexivity.
          specialize(HnextBlockSide part block (CPaddr (block+scoffset)) blockToRemoveInChildAddr endaddr
            HpartIsPart HblockMapped Hend HeqTriv HbeqNextNull Hnext).
          destruct HnextBlockSide as (HstartCBis & HblockCMappedBis). assert(part = idPDchild).
          {
            destruct (beqAddr part idPDchild) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
            rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HblockCMappeds0.
            assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            apply InFilterPresentInList in HblockCMappedBis. assert(HpartIsPDT: isPDT part s0).
            { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
            specialize(Hdisjoint part idPDchild HpartIsPDT HchildIsPDT HbeqParts).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint blockToRemoveInChildAddr HblockCMappedBis). congruence.
          }
          subst part. assert(HlocProps: childLocMappedInChild s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition). rewrite beqAddrSym in *.
          rewrite <-beqAddrFalse in *.
          specialize(HlocProps currentPart blockToRemoveInCurrPartAddr sh1entryaddr blockToRemoveInChildAddr
            idPDchild HcurrIsParts0 HblockPMappeds0 Hsh1Ps0 HPDchildPs0 HchildLocPs0 HbeqNullChild HbeqNullBlockC).
          destruct HlocProps as (_ & HstartIsOrigin). specialize(HstartIsOrigin globalIdBlockToRemove HstartP).
          assert(globalIdBlockToRemove = endaddr).
          {
            unfold bentryStartAddr in *.
            destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartCBis in *. assumption.
          }
          subst globalIdBlockToRemove.
          assert(HblockCut: nextImpliesBlockWasCut s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HblockCut idPDchild pdentry block (CPaddr (block+scoffset)) blockToRemoveInChildAddr endaddr
            HpartIsPart HlookupChild HblockMapped Hend HeqTriv HbeqNextNull Hnext HbeqPartRoot).
          destruct HblockCut as [blockParent [endParent (HblockPBisMapped & HendPBis & HltEnds & Hincl)]].
          assert(HPflagP: bentryPFlag blockToRemoveInCurrPartAddr true s0).
          {
            apply IL.mappedBlockIsBE in HblockPMappeds0. destruct HblockPMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HendPs0: bentryEndAddr blockToRemoveInCurrPartAddr endBlockToRemove s0).
          {
            assert(HendPs0: bentryEndAddr blockToRemoveInCurrPartAddr endBlockToRemove s1).
            {
              unfold bentryEndAddr in *. rewrite Hs in HendP. simpl in *. rewrite IL.beqAddrTrue in *.
              rewrite HlookupBlockPs1. rewrite HnewB in HendP. auto.
            }
            pose proof (lookupBEEqRemoveRec blockToRemoveInCurrPartAddr s1 s0 idPDchild blockToRemoveInChildAddr
              statesList blocksList HblockPIsBEs0 HblockPNotIn HblocksList) as HlookupsEq.
            unfold bentryEndAddr. rewrite <-HlookupsEq. assumption.
          }
          specialize(Hwell blockToRemoveInCurrPartAddr endaddr endBlockToRemove HPflagP HstartP HendPs0).
          destruct Hwell as (HwellP & _).
          rewrite <-HisParent in *. assert(HendInBP: In endaddr (getAllPaddrAux [blockToRemoveInCurrPartAddr] s0)).
          {
            simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendPs0.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hwell block startaddr endaddr HPflag Hstart Hend). destruct Hwell as (Hwell & _).
          assert(HstartInBlock: In startaddr (getAllPaddrAux [block] s0)).
          {
            unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            simpl. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          specialize(Hincl startaddr HstartInBlock). assert(blockParent = blockToRemoveInCurrPartAddr).
          {
            assert(HnoDupPaddr: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            destruct (beqAddr blockParent blockToRemoveInCurrPartAddr) eqn:HbeqBlocks;
              try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
            assert(HendInBPBis: In endaddr (getAllPaddrAux [blockParent] s0)).
            {
              assert(HPflagPBis: bentryPFlag blockParent true s0).
              {
                apply IL.mappedBlockIsBE in HblockPBisMapped. destruct HblockPBisMapped as [bentry (Hlookup & Hpres)].
                unfold bentryPFlag. rewrite Hlookup. auto.
              }
              assert(HwellPBis: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HstartPBis: exists startPBis, bentryStartAddr blockParent startPBis s0).
              {
                unfold bentryStartAddr. unfold bentryPFlag in *.
                destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
              }
              destruct HstartPBis as [startPBis HstartPBis].
              specialize(HwellPBis blockParent startPBis endParent HPflagPBis HstartPBis HendPBis).
              destruct HwellPBis as (HwellPBis & _). unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
              simpl in *. destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r in *. rewrite <-HstartPBis in *.
              rewrite <-HendPBis in *. apply IL.getAllPaddrBlockInclRev in Hincl. destruct Hincl as (HlebStarts & _).
              apply IL.getAllPaddrBlockIncl; lia.
            }
            pose proof (DisjointPaddrInPart currentPart blockParent blockToRemoveInCurrPartAddr endaddr s0
              HnoDupPaddr HcurrIsPDT HblockPBisMapped HblockPMappeds0 HbeqBlocks HendInBPBis). congruence.
          }
          subst blockParent. simpl in Hincl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). rewrite app_nil_r in Hincl. rewrite <-HstartP in *. rewrite <-HendPBis in *.
          apply IL.getAllPaddrBlockInclRev in Hincl. destruct Hincl as (Hcontra & _). lia.
        }

        assert(HpartConsist2s1: accessibleParentPaddrIsAccessibleIntoChild s1 /\ sharedBlockPointsToChild s1
          /\ adressesRangePreservedIfOriginAndNextOk s1 /\ childsBlocksPropsInParent s1
          /\ noChildImpliesAddressesNotShared s1 /\ kernelsAreNotAccessible s1 /\ blockAndNextAreSideBySide s1
          /\ parentBlocksBoundsIfNoNext s1).
        {
          split.
          { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s1 *)
            assert(accessibleParentPaddrIsAccessibleIntoChild s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). revert HblocksList Hlast.
            apply accessibleParentPaddrIsAccessibleIntoChildPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
            (* END accessibleParentPaddrIsAccessibleIntoChild *)
          }
          split.
          { (* BEGIN sharedBlockPointsToChild s1 *)
            assert(sharedBlockPointsToChild s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). revert HblocksList Hlast.
            apply sharedBlockPointsToChildPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; intuition.
            (* END sharedBlockPointsToChild *)
          }
          split.
          { (* BEGIN adressesRangePreservedIfOriginAndNextOk s1 *)
            assert(adressesRangePreservedIfOriginAndNextOk s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). revert HblocksList Hlast.
            apply adressesRangePreservedIfOriginAndNextOkPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
            (* END adressesRangePreservedIfOriginAndNextOk *)
          }
          split.
          { (* BEGIN childsBlocksPropsInParent s1 *)
            assert(childsBlocksPropsInParent s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). revert HblocksList Hlast.
            apply childsBlocksPropsInParentPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; intuition.
            (* END childsBlocksPropsInParent *)
          }
          split.
          { (* BEGIN noChildImpliesAddressesNotShared s1 *)
            assert(noChildImpliesAddressesNotShared s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). revert HblocksList Hlast.
            apply noChildImpliesAddressesNotSharedPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
            (* END noChildImpliesAddressesNotShared *)
          }
          split.
          { (* BEGIN kernelsAreNotAccessible s1 *)
            assert(kernelsAreNotAccessible s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). revert HblocksList Hlast.
            apply kernelsAreNotAccessiblePreservedRemoveRec; trivial.
            (* END kernelsAreNotAccessible *)
          }
          split.
          { (* BEGIN blockAndNextAreSideBySide s1 *)
            assert(blockAndNextAreSideBySide s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). revert HblocksList.
            apply blockAndNextAreSideBySidePreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
            (* END blockAndNextAreSideBySide *)
          }
          { (* BEGIN parentBlocksBoundsIfNoNext s1 *)
            assert(parentBlocksBoundsIfNoNext s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). revert HblocksList Hlast.
            apply parentBlocksBoundsIfNoNextPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
            (* END parentBlocksBoundsIfNoNext *)
          }
        }

        assert(Hisos1: partitionsIsolation s1 /\ kernelDataIsolation s1 /\ verticalSharing s1).
        {
          split. revert HblocksList Hlast.
            apply partitionsIsolationPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; intuition.
          split. revert HblocksList Hlast.
            apply kernelDataIsolationPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; intuition. revert HblocksList Hlast.
            apply verticalSharingPreservedRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; unfold consistency2 in *; intuition.
        }

        destruct HnewB as [l HnewB].
        pose proof (lookupBEEqRemoveRec blockToRemoveInCurrPartAddr s1 s0 idPDchild blockToRemoveInChildAddr
          statesList blocksList HblockPIsBEs0 HblockPNotIn HblocksList) as HlookupBPEq.
        assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s1).
        {
          rewrite Hs.
          apply IL.getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry1 sh1entryaddr; trivial;
            try(rewrite HnewB; reflexivity). 1,2,5: unfold consistency1 in *; intuition.
          - unfold sh1entryAddr. rewrite HlookupBPEq. assumption.
          - simpl. destruct (beqAddr blockToRemoveInCurrPartAddr sh1entryaddr) eqn:HbeqBlockPSh1.
            {
              rewrite <-beqAddrTrue in HbeqBlockPSh1. subst sh1entryaddr. unfold sh1entryPDchild in *. exfalso.
              unfold isBE in *. destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(congruence).
              destruct v; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        assert(HgetKSEq: forall part, getKSEntries part s = getKSEntries part s1).
        {
          intro part. rewrite Hs. apply IL.getKSEntriesEqBE. unfold isBE. rewrite HlookupBPEq. assumption.
        }
        assert(HgetMappedBEq: forall part, getMappedBlocks part s = getMappedBlocks part s1).
        {
          intro part. rewrite Hs. apply IL.getMappedBlocksEqBENoChange with bentry1; trivial. rewrite HnewB.
          reflexivity.
        }
        assert(HgetMappedPEq: forall part, isPDT part s1 -> getMappedPaddr part s = getMappedPaddr part s1).
        {
          intros part HpartIsPDT. rewrite Hs.
          apply IL.getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry1; trivial;
            rewrite HnewB; reflexivity.
        }
        assert(HgetChildrenEq: forall part, isPDT part s1 -> getChildren part s = getChildren part s1).
        {
          intros part HpartIsPDT. rewrite Hs. apply IL.getChildrenEqBENoStartNoPresentChange with bentry1; trivial;
            rewrite HnewB; reflexivity.
        }
        assert(HgetConfigEq: forall part, isPDT part s1 -> getConfigPaddr part s = getConfigPaddr part s1).
        {
          intros part HpartIsPDT. rewrite Hs. apply IL.getConfigPaddrEqBE; trivial. unfold isBE. rewrite HlookupBPEq.
          assumption.
        }
        assert(HcurrIsPDTs1: isPDT currentPart s1).
        {
          assert(HgetPartsEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
          {
            revert HblocksList. apply getPartitionsEqRemoveRec; unfold consistency in *; unfold consistency1 in *;
              intuition.
          }
          rewrite <-HgetPartsEqs1 in HcurrIsParts0.
          apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition.
        }
        assert(HgetAccMappedBEq: forall part, part <> currentPart -> isPDT part s1
          -> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s1).
        {
          intros part HbeqParts HpartIsPDT. rewrite Hs.
          apply IL.getAccessibleMappedBlocksEqBENotInPart; trivial.
          - unfold isBE. rewrite HlookupBPEq. assumption.
          - assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
            specialize(Hdisjoint part currentPart HpartIsPDT HcurrIsPDTs1 HbeqParts).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            intro Hcontra. specialize(Hdisjoint blockToRemoveInCurrPartAddr Hcontra). unfold getMappedBlocks in *.
            apply InFilterPresentInList in HblockPMappeds0.
            assert(HeqKS: getKSEntries currentPart s1 = getKSEntries currentPart s0).
            { revert HblocksList. apply getKSEntriesEqRemoveRec; trivial. }
            rewrite HeqKS in *. congruence.
        }
        assert(HgetAccMappedPEq: forall part, part <> currentPart -> isPDT part s1
          -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s1).
        {
          intros part HbeqParts HpartIsPDT. rewrite Hs.
          apply IL.getAccessibleMappedPaddrEqBENotInPart; trivial.
          - unfold isBE. rewrite HlookupBPEq. assumption.
          - assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
            specialize(Hdisjoint part currentPart HpartIsPDT HcurrIsPDTs1 HbeqParts).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            intro Hcontra. specialize(Hdisjoint blockToRemoveInCurrPartAddr Hcontra). unfold getMappedBlocks in *.
            apply InFilterPresentInList in HblockPMappeds0.
            assert(HeqKS: getKSEntries currentPart s1 = getKSEntries currentPart s0).
            { revert HblocksList. apply getKSEntriesEqRemoveRec; trivial. }
            rewrite HeqKS in *. congruence.
        }
        assert(HendPs0: bentryEndAddr blockToRemoveInCurrPartAddr endBlockToRemove s0).
        {
          unfold bentryEndAddr in *. rewrite <-HlookupBPEq. rewrite Hs in HendP. simpl in *.
          rewrite IL.beqAddrTrue in *. rewrite HlookupBlockPs1. rewrite HnewB in HendP. auto.
        }
        assert(HAflagPs0: bentryAFlag blockToRemoveInCurrPartAddr false s0).
        {
          assert(HchildBlockProps: childsBlocksPropsInParent s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          rewrite beqAddrSym in *. rewrite <-beqAddrFalse in *.
          assert(HblockWasCut: nextImpliesBlockWasCut s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HeqTriv: CPaddr (blockToRemoveInChildAddr+scoffset) = CPaddr (blockToRemoveInChildAddr+scoffset))
            by reflexivity. assert(HendC: exists endC, bentryEndAddr blockToRemoveInChildAddr endC s0).
          {
            unfold bentryEndAddr. unfold isBE in *.
            destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
          }
          destruct HendC as [endC HendC].
          destruct HnextNotNull as [blockNext (Hnext & HbeqNextNull)].
          specialize(HblockWasCut idPDchild pdentry blockToRemoveInChildAddr
            (CPaddr (blockToRemoveInChildAddr+scoffset)) blockNext endC HchildIsParts0 HlookupChild
            HblockCMappeds0 HendC HeqTriv HbeqNextNull Hnext HbeqPartRoot).
          destruct HblockWasCut as [blockParent [endParent (HblockPBisMapped & HendPBis & HltEnds & Hincl)]].
          assert(HPflagP: bentryPFlag blockToRemoveInCurrPartAddr true s0).
          {
            apply IL.mappedBlockIsBE in HblockPMappeds0. destruct HblockPMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(HglobInBP: In globalIdBlockToRemove (getAllPaddrAux [blockToRemoveInCurrPartAddr] s0)).
          {
            assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(Hwell blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HPflagP HstartP
              HendPs0). destruct Hwell as (Hwell & _). unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            simpl. rewrite HlookupBPEq in *. rewrite HlookupBlockPs1 in *. rewrite app_nil_r. rewrite <-HstartP.
            rewrite <-HendPs0. apply IL.getAllPaddrBlockIncl; lia.
          }
          assert(HglobInBPs1: In globalIdBlockToRemove (getAllPaddrAux [blockToRemoveInCurrPartAddr] s1)).
          { simpl in *. rewrite HlookupBPEq. assumption. }
          assert(HPflagC: bentryPFlag blockToRemoveInChildAddr true s0).
          {
            apply IL.mappedBlockIsBE in HblockCMappeds0. destruct HblockCMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(blockToRemoveInCurrPartAddr = blockParent).
          {
            destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks;
              try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
            assert(HnoDupPaddr: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). rewrite <-HisParent in *.
            pose proof (DisjointPaddrInPart currentPart blockToRemoveInCurrPartAddr blockParent
              globalIdBlockToRemove s0 HnoDupPaddr HcurrIsPDT HblockPMappeds0 HblockPBisMapped HbeqBlocks HglobInBP)
              as Hcontra.
            assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(Hwell blockToRemoveInChildAddr globalIdBlockToRemove endC HPflagC HstartC HendC).
            destruct Hwell as (Hwell & _).
            contradict Hcontra. apply Hincl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
            destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartC. rewrite <-HendC.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          subst blockParent. assert(HlebStarts: globalIdBlockToRemove <= globalIdBlockToRemove) by lia.
          assert(endParent = endBlockToRemove).
          {
            unfold bentryEndAddr in *. rewrite HlookupBPEq in *. rewrite HlookupBlockPs1 in *. subst endParent.
            auto.
          }
          subst endParent. assert(HgebEnds: endBlockToRemove >= endC) by lia.
          specialize(HchildBlockProps idPDchild currentPart blockToRemoveInChildAddr globalIdBlockToRemove endC
            blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HcurrIsParts0 HchildIsChild
            HblockCMappeds0 HstartC HendC HPflagC HblockPMappeds0 HstartP HendPs0 HPflagP HlebStarts HgebEnds).
          destruct HchildBlockProps as (_ & _ & _ & Hres). apply Hres. right. apply paddrNeqNatNeqEquiv. lia.
        }
        assert(HgetAccMappedBCurrEquiv: forall block, In block (getAccessibleMappedBlocks currentPart s)
          <-> In block (blockToRemoveInCurrPartAddr::getAccessibleMappedBlocks currentPart s1)).
        {
          intro block. rewrite Hs.
          apply IL.getAccessibleMappedBlocksEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence with bentry1;
            trivial; try(rewrite HnewB; simpl); trivial.
          - apply IL.mappedBlockIsBE in HblockPMappeds0. destruct HblockPMappeds0 as [bentry (Hlookup & Hpres)].
            rewrite HlookupBPEq in *. rewrite HlookupBlockPs1 in Hlookup. injection Hlookup as HbentriesEq.
            subst bentry. auto.
          - unfold bentryAFlag in *. rewrite HlookupBPEq in *. rewrite HlookupBlockPs1 in *.
            intro. congruence.
          - unfold consistency1 in *; intuition.
          - unfold getMappedBlocks in *. apply InFilterPresentInList in HblockPMappeds0.
            assert(HeqKS: getKSEntries currentPart s1 = getKSEntries currentPart s0).
            { revert HblocksList. apply getKSEntriesEqRemoveRec; trivial. }
            rewrite HeqKS. assumption.
        }
        assert(HgetAccMappedPCurrEquiv: forall addr, In addr (getAccessibleMappedPaddr currentPart s)
          <-> In addr (getAllPaddrBlock (startAddr (blockrange bentry1)) (endAddr (blockrange bentry1))
                ++ getAccessibleMappedPaddr currentPart s1)).
        {
          intro block. rewrite Hs.
          apply IL.getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence; trivial;
            try(rewrite HnewB; simpl); trivial.
          - apply IL.mappedBlockIsBE in HblockPMappeds0. destruct HblockPMappeds0 as [bentry (Hlookup & Hpres)].
            rewrite HlookupBPEq in *. rewrite HlookupBlockPs1 in Hlookup. injection Hlookup as HbentriesEq.
            subst bentry. auto.
          - unfold bentryAFlag in *. rewrite HlookupBPEq in *. rewrite HlookupBlockPs1 in *.
            intro. congruence.
          - unfold consistency1 in *; intuition.
          - unfold getMappedBlocks in *. apply InFilterPresentInList in HblockPMappeds0.
            assert(HeqKS: getKSEntries currentPart s1 = getKSEntries currentPart s0).
            { revert HblocksList. apply getKSEntriesEqRemoveRec; trivial. }
            rewrite HeqKS. assumption.
        }

        assert(HgetPartsEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
        {
          revert HblocksList.
          apply getPartitionsEqRemoveRec; unfold consistency in *; unfold consistency1 in *; intuition.
        }
        assert(HchildLocMappedInChildPartial: forall part block sh1entryaddr blockChild idchild,
          blockToRemoveInCurrPartAddr <> block
          -> In part (getPartitions multiplexer s1)
          -> In block (getMappedBlocks part s1)
          -> sh1entryAddr block sh1entryaddr s1
          -> sh1entryPDchild sh1entryaddr idchild s1
          -> sh1entryInChildLocation sh1entryaddr blockChild s1
          -> idchild <> nullAddr
          -> blockChild <> nullAddr
          -> In blockChild (getMappedBlocks idchild s1)
              /\ (forall startaddr, bentryStartAddr block startaddr s1 -> bentryStartAddr blockChild startaddr s1)).
        {
          intros part block sh1entryaddrB blockChild idchild HbeqBlocks HpartIsPart HblockMapped Hsh1 HPDchild
            HchildLoc HbeqChildNull HbeqBlockCNull.
          rewrite HgetPartsEqs1 in *. assert(HblockNotInList: ~In block (blockToRemoveInChildAddr::blocksList)).
          {
            assert(HbeqBlockNull: block <> nullAddr).
            {
              assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold sh1entryAddr in *.
              unfold isPADDR in *. intro Hcontra. subst block.
              destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
            }
            intro Hcontra. rewrite beqAddrSym in *. rewrite <-beqAddrFalse in *.
            pose proof (blockRemovedWereNotShared block s1 s0 idPDchild blockToRemoveInChildAddr
              statesList blocksList HbeqBlockNull Hcontra Hlast HbeqNullBlockC HblocksList) as HPDchildBis.
            unfold sh1entryAddr in *. destruct (lookup block (memory s1) beqAddr); try(congruence).
            destruct v; try(congruence). subst sh1entryaddrB.
            assert(sh1entryPDchild (CPaddr (block+sh1offset)) nullAddr s1).
            { revert HblocksList. apply noPDchildPreservedRemoveRec; assumption. }
            unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block+sh1offset)) (memory s1) beqAddr); try(congruence). destruct v; congruence.
          }
          assert(isBE block s0).
          {
            revert HblocksList. apply isBEEqRemoveRecRev. unfold isBE. unfold sh1entryAddr in *.
            destruct (lookup block (memory s1) beqAddr); try(congruence). destruct v; try(congruence). trivial.
          }
          assert(HlookupBlockEq: lookup block (memory s1) beqAddr = lookup block (memory s0) beqAddr).
          {
            revert HblocksList. apply lookupBEEqRemoveRec; trivial.
          }
          unfold sh1entryAddr in *. unfold bentryStartAddr. rewrite HlookupBlockEq in *.
          assert(HlookupSh1Eq: lookup sh1entryaddrB (memory s1) beqAddr = lookup sh1entryaddrB (memory s0) beqAddr).
          {
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). subst sh1entryaddrB. revert HblocksList.
            apply lookupSh1EqRemoveRec; trivial.
            - unfold isSHE. unfold sh1entryPDchild in *.
              destruct (lookup (CPaddr (block + sh1offset)) (memory s1) beqAddr); try(congruence).
              destruct v; try(congruence). trivial.
            - unfold consistency in *; unfold consistency1 in *; intuition.
          }
          unfold sh1entryPDchild in *. unfold sh1entryInChildLocation in *. rewrite HlookupSh1Eq in *.
          assert(HchildLocs0: sh1entryInChildLocation sh1entryaddrB blockChild s0).
          {
            unfold sh1entryInChildLocation. destruct (lookup sh1entryaddrB (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial.
            intro HbeqBCNull. specialize(HlocIsBE HbeqBCNull). revert HblocksList. apply isBEEqRemoveRecRev; trivial.
          }
          assert(HblockMappeds0: In block (getMappedBlocks part s0)).
          {
            destruct (beqAddr idPDchild part) eqn:HbeqParts.
            - rewrite <-beqAddrTrue in HbeqParts. subst part. revert HblocksList.
              apply getMappedInclRemoveRec; trivial.
              unfold consistency in *; unfold consistency1 in *; intuition.
            - rewrite <-beqAddrFalse in *. assert(Hdisjoint: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HwellSh1: wellFormedFstShadowIfBlockEntry s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDup: noDupKSEntriesList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupMapped: noDupMappedBlocksList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupPaddr: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              pose proof (getMappedBlocksEqRemoveRec blockToRemoveInChildAddr s1 s0 idPDchild statesList
                blocksList part HbeqParts Hdisjoint Hwell HwellSh1 HnoDup Hnull HnoDupMapped HnoDupPaddr
                HnextBlocksList HchildIsParts0 HblockCMappeds0 HblocksList) as Heq. rewrite <-Heq. assumption.
          }
          assert(Hcons0: childLocMappedInChild s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          specialize(Hcons0 part block sh1entryaddrB blockChild idchild HpartIsPart HblockMappeds0 Hsh1 HPDchild
            HchildLocs0 HbeqChildNull HbeqBlockCNull). destruct Hcons0 as (HblockCBisMapped & HstartsEq).
          assert(HblockCNotInList: ~In blockChild (blockToRemoveInChildAddr::blocksList)).
          {
            assert(Hstart: exists startaddr, bentryStartAddr block startaddr s0).
            {
              unfold bentryStartAddr. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
            }
            assert(HchildBisIsPDT: isPDT idchild s0).
            {
              unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
              destruct(lookup idchild (memory s0) beqAddr); try(simpl in *; congruence).
              destruct v; try(simpl in *; congruence). trivial.
            }
            destruct Hstart as [startaddr Hstart]. specialize(HstartsEq startaddr Hstart).
            simpl. apply Classical_Prop.and_not_or. assert(blockToRemoveInChildAddr <> blockChild).
            {
              intro Hcontra. subst blockChild. assert(startaddr = globalIdBlockToRemove).
              {
                unfold bentryStartAddr in *.
                destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). subst startaddr. auto.
              }
              subst startaddr. assert(idchild = idPDchild).
              {
                destruct (beqAddr idchild idPDchild) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
                rewrite <-beqAddrFalse in *. assert(Hdisjoint: DisjointKSEntries s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition). unfold getMappedBlocks in *.
                apply InFilterPresentInList in HblockCMappeds0. apply InFilterPresentInList in HblockCBisMapped.
                specialize(Hdisjoint idchild idPDchild HchildBisIsPDT HchildIsPDT HbeqParts).
                destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
                specialize(Hdisjoint blockToRemoveInChildAddr HblockCBisMapped). congruence.
              }
              subst idchild. assert(HchildIsChildBis: pdchildIsPDT s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              specialize(HchildIsChildBis part block sh1entryaddrB idPDchild HpartIsPart HblockMappeds0 Hsh1
                HPDchild HbeqChildNull).
              assert(HisParentBis: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              specialize(HisParentBis idPDchild part HpartIsPart HchildIsChildBis). unfold pdentryParent in *.
              rewrite HlookupChild in *. rewrite <-HisParent in *. subst part. contradict HbeqBlocks.
              apply IL.mappedBlocksEqStartEq with currentPart globalIdBlockToRemove s0; trivial.
              - unfold consistency in *; unfold consistency2 in *; intuition.
              - unfold consistency in *; unfold consistency1 in *; intuition.
              - apply IL.mappedBlockIsBE in HblockPMappeds0. destruct HblockPMappeds0 as [bentry (Hlookup & Hpres)].
                unfold bentryPFlag. rewrite Hlookup. auto.
              - apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
                unfold bentryPFlag. rewrite Hlookup. auto.
            }
            split; trivial. intro Hcontra.
            assert(HblockCBisMappedChild: In blockChild (getMappedBlocks idPDchild s0)).
            {
              revert HblocksList. apply removeRecBlocksWereMapped; trivial; unfold consistency in *;
                unfold consistency1 in *; intuition.
            }
            assert(idchild = idPDchild).
            {
              destruct (beqAddr idchild idPDchild) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
              rewrite <-beqAddrFalse in *. assert(Hdisjoint: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition). unfold getMappedBlocks in *.
              apply InFilterPresentInList in HblockCBisMappedChild. apply InFilterPresentInList in HblockCBisMapped.
              specialize(Hdisjoint idchild idPDchild HchildBisIsPDT HchildIsPDT HbeqParts).
              destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
              specialize(Hdisjoint blockChild HblockCBisMapped). congruence.
            }
            subst idchild. assert(HchildIsChildBis: pdchildIsPDT s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HchildIsChildBis part block sh1entryaddrB idPDchild HpartIsPart HblockMappeds0 Hsh1
              HPDchild HbeqChildNull).
            assert(HisParentBis: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HisParentBis idPDchild part HpartIsPart HchildIsChildBis). unfold pdentryParent in *.
            rewrite HlookupChild in *. rewrite <-HisParent in *. subst part.
            assert(HnoDup: noDupKSEntriesList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            pose proof (removedBlocksAreNexts blockChild s1 s0 idPDchild blockToRemoveInChildAddr statesList
              blocksList HbeqBlockCNull HnoDup Hcontra HblocksList) as Hprev.
            destruct Hprev as [prevBlock (HprevMapped & HnextPrev)].
            assert(HisCut: nextImpliesBlockWasCut s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HeqTriv: CPaddr (prevBlock + scoffset) = CPaddr (prevBlock + scoffset)) by reflexivity.
            assert(HnextBlockSide: blockAndNextAreSideBySide s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            assert(HendPrev: exists endaddr, bentryEndAddr prevBlock endaddr s0).
            {
              apply IL.mappedBlockIsBE in HprevMapped. destruct HprevMapped as [bentry (Hlookup & _)].
              unfold bentryEndAddr. rewrite Hlookup. exists (endAddr (blockrange bentry)). reflexivity.
            }
            destruct HendPrev as [endaddr HendPrev].
            specialize(HnextBlockSide idPDchild prevBlock (CPaddr (prevBlock + scoffset)) blockChild endaddr
              HchildIsParts0 HprevMapped HendPrev HeqTriv HbeqBlockCNull HnextPrev).
            destruct HnextBlockSide as (HstartCBis & _). assert(endaddr = startaddr).
            {
              unfold bentryStartAddr in *. destruct (lookup blockChild (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). subst startaddr. assumption.
            }
            subst endaddr.
            specialize(HisCut idPDchild pdentry prevBlock (CPaddr (prevBlock + scoffset)) blockChild startaddr
              HchildIsParts0 HlookupChild HprevMapped HendPrev HeqTriv HbeqBlockCNull HnextPrev HbeqPartRoot).
            destruct HisCut as [blockParent [endP (HblockPBisMapped & HendPBis & HltEnds & Hincl)]].
            assert(HstartPrev: exists startPrev, bentryStartAddr prevBlock startPrev s0).
            {
              unfold bentryStartAddr. unfold bentryEndAddr in *.
              destruct (lookup prevBlock (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
            }
            destruct HstartPrev as [startPrev HstartPrev].
            assert(HPflagPrev: bentryPFlag prevBlock true s0).
            {
              apply IL.mappedBlockIsBE in HprevMapped. destruct HprevMapped as [bentry (Hlookup & Hpres)].
              unfold bentryPFlag. rewrite Hlookup. auto.
            }
            assert(HwellPrev: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            specialize(HwellPrev prevBlock startPrev startaddr HPflagPrev HstartPrev HendPrev).
            destruct HwellPrev as (HwellPrev & _). assert(HPflag: bentryPFlag block true s0).
            {
              apply IL.mappedBlockIsBE in HblockMappeds0. destruct HblockMappeds0 as [bentry (Hlookup & Hpres)].
              unfold bentryPFlag. rewrite Hlookup. auto.
            }
            assert(HstartPInBP: In startPrev (getAllPaddrAux [blockParent] s0)).
            {
              apply Hincl. simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              destruct (lookup prevBlock (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartPrev. rewrite <-HendPrev.
              apply IL.getAllPaddrBlockIncl; lia.
            }
            assert(HstartBP: exists startP, bentryStartAddr blockParent startP s0).
            {
              unfold bentryStartAddr. unfold bentryEndAddr in *.
              destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
            }
            destruct HstartBP as [startP HstartBP]. assert(startP <= startPrev).
            {
              simpl in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite app_nil_r in *. rewrite <-HstartBP in *.
              rewrite <-HendPBis in *. apply IL.getAllPaddrBlockInclRev in HstartPInBP. destruct HstartPInBP.
              assumption.
            }
            assert(blockParent = block).
            {
              destruct (beqAddr blockParent block) eqn:HbeqBlockPBlock; try(rewrite beqAddrTrue; assumption).
              rewrite <-beqAddrFalse in *. assert(HstartInBP: In startaddr (getAllPaddrAux [blockParent] s0)).
              {
                simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite app_nil_r. rewrite <-HstartBP. rewrite <-HendPBis.
                apply IL.getAllPaddrBlockIncl; lia.
              }
              assert(HnoDupPaddr: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition). rewrite <-HisParent in *.
              pose proof (DisjointPaddrInPart currentPart blockParent block startaddr s0 HnoDupPaddr HcurrIsPDT
                HblockPBisMapped HblockMappeds0 HbeqBlockPBlock HstartInBP) as HstartInBlock.
              contradict HstartInBlock.
              assert(Hend: exists endaddr, bentryEndAddr block endaddr s0).
              {
                unfold bentryStartAddr in *. unfold bentryEndAddr.
                destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
              }
              destruct Hend as [endaddr Hend]. simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              specialize(Hwell block startaddr endaddr HPflag Hstart Hend). destruct Hwell as (Hwell & _).
              destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend.
              apply IL.getAllPaddrBlockIncl; lia.
            }
            subst blockParent. unfold bentryStartAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            rewrite <-Hstart in *. subst startP. lia.
          }
          split.
          - destruct (beqAddr idPDchild idchild) eqn:HbeqParts.
            + rewrite <-beqAddrTrue in HbeqParts. subst idchild. revert HblocksList.
              apply getMappedInclRemoveRecNotInListRev; trivial.
              unfold consistency in *; unfold consistency1 in *; intuition.
            + rewrite <-beqAddrFalse in *. assert(Hdisjoint: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hwell: wellFormedBlock s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HwellSh1: wellFormedFstShadowIfBlockEntry s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDup: noDupKSEntriesList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupMapped: noDupMappedBlocksList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupPaddr: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              pose proof (getMappedBlocksEqRemoveRec blockToRemoveInChildAddr s1 s0 idPDchild statesList blocksList
                idchild HbeqParts Hdisjoint Hwell HwellSh1 HnoDup Hnull HnoDupMapped HnoDupPaddr HnextBlocksList
                HchildIsParts0 HblockCMappeds0 HblocksList) as Heq. rewrite Heq. assumption.
          - intros startaddr Hstart. specialize(HstartsEq startaddr Hstart).
            rewrite lookupBEEqRemoveRec with (s0:=s0) (idPDchild:=idPDchild) (blockToRemove:=blockToRemoveInChildAddr)
              (statesList:=statesList) (blocksList:=blocksList); trivial. unfold bentryStartAddr in *. unfold isBE.
            destruct (lookup blockChild (memory s0) beqAddr); try(congruence). destruct v; try(congruence). trivial.
        }

        assert(partitionsIsolation s).
        { (* BEGIN partitionsIsolation s *)
          assert(HPIs1: partitionsIsolation s1) by intuition.
          intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
          rewrite HgetPartsEq in *.
          assert(isPDT pdparent s1) by (apply IL.partitionsArePDT; unfold consistency1 in *; intuition).
          rewrite HgetChildrenEq in *; trivial.
          specialize(HPIs1 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
          unfold getUsedPaddr. assert(isPDT child1 s1).
          { apply IL.childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition. }
          rewrite HgetConfigEq; trivial. assert(isPDT child2 s1).
          { apply IL.childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition. }
          rewrite HgetConfigEq; trivial. rewrite HgetMappedPEq; trivial. rewrite HgetMappedPEq; trivial.
          (* END partitionsIsolation *)
        }

        destruct HnextBlocksList as [nextBlocksList (HnextBlocksList & HlastNext)].
        assert(blocksList = nextBlocksList).
        {
          revert HblocksList. apply checkRemovedEq; trivial; unfold consistency in *; unfold consistency1 in *;
            unfold consistency2 in *; intuition.
        }
        subst nextBlocksList.

        assert(HnoDupList: NoDup (blockToRemoveInChildAddr::blocksList)).
        {
          revert HnextBlocksList. apply noDupNextBlocksList; trivial; unfold consistency in *;
            unfold consistency1 in *; unfold consistency2 in *; intuition.
        }

        assert(HblockC: bentryPFlag blockToRemoveInChildAddr true s0
          /\ exists endC, bentryEndAddr blockToRemoveInChildAddr endC s0).
        {
          apply IL.mappedBlockIsBE in HblockCMappeds0. destruct HblockCMappeds0 as [bentry (Hlookup & Hpres)].
          unfold bentryPFlag. unfold bentryEndAddr. rewrite Hlookup. split; auto.
          exists (endAddr (blockrange bentry)). reflexivity.
        }
        destruct HblockC as (HPflagC & [endC HendC]).
        assert(HPflagPs0: bentryPFlag blockToRemoveInCurrPartAddr true s0).
        {
          apply IL.mappedBlockIsBE in HblockPMappeds0. destruct HblockPMappeds0 as [bentry (Hlookup & Hpres)].
          unfold bentryPFlag. rewrite Hlookup. auto.
        }

        assert(kernelDataIsolation s).
        { (* BEGIN kernelDataIsolation s *)
          assert(HKDIs1: kernelDataIsolation s1) by intuition.
          intros part1 part2 Hpart1IsPart Hpart2IsPart. rewrite HgetPartsEq in *.
          assert(isPDT part2 s1) by (apply IL.partitionsArePDT; unfold consistency1 in *; intuition).
          rewrite HgetConfigEq; trivial. specialize(HKDIs1 part1 part2 Hpart1IsPart Hpart2IsPart).
          destruct (beqAddr part1 currentPart) eqn:HbeqParts.
          - rewrite <-beqAddrTrue in HbeqParts. subst part1. intros addr HaddrAccMapped.
            apply HgetAccMappedPCurrEquiv in HaddrAccMapped. apply in_app_or in HaddrAccMapped.
            destruct HaddrAccMapped as [HaddrInRange | HaddrAccMappeds1]; try(apply HKDIs1; assumption).
            assert(HconfigEq: getConfigPaddr part2 s1 = getConfigPaddr part2 s0).
            { revert HblocksList. apply getConfigPaddrEqRemoveRec; trivial. }
            rewrite HconfigEq. rewrite HgetPartsEqs1 in *.
            specialize(HKDIs0 idPDchild part2 HchildIsParts0 Hpart2IsPart). apply HKDIs0.
            assert(HaddrMappedList: exists blockC, In blockC (blockToRemoveInChildAddr::blocksList)
              /\ bentryAFlag blockC true s0
              /\ In addr (getAllPaddrAux [blockC] s0)).
            {
              assert(HnextBlockSide: blockAndNextAreSideBySide s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              assert(HnoDup: noDupKSEntriesList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupMapped: noDupMappedBlocksList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hdisjoint: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HwellSh1: wellFormedFstShadowIfBlockEntry s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupPaddr: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              pose proof (removedAddrsAreARange s1 s0 idPDchild blockToRemoveInChildAddr statesList blocksList
                HnextBlockSide HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 Hwell HnoDupPaddr HblockCIsNoNext
                HchildIsParts0 HnoDupList HblocksList) as HisRange.
              destruct HisRange as [startRange [endRange HisRange]].
              assert(startRange = globalIdBlockToRemove).
              {
                specialize(Hwell blockToRemoveInChildAddr globalIdBlockToRemove endC HPflagC HstartC HendC).
                destruct Hwell as (Hwell & _).
                unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl in HisRange.
                destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HstartC in *. rewrite <-HendC in *.
                apply eq_sym in HisRange. revert HisRange. apply getAllPaddrBlockSplit. assumption.
              }
              subst startRange. assert(endRange = endBlockToRemove).
              {
                rewrite beqAddrSym in HbeqNullBlockC. rewrite <-beqAddrFalse in *.
                assert(HlastElem: exists blocksListBis, blocksList = blocksListBis++[nullAddr]).
                { apply lastElNotElDef with blockToRemoveInChildAddr; trivial. }
                destruct HlastElem as [blocksListBis HlistEq].
                assert(HlastElem: exists lastNext blocksListHead,
                  blockToRemoveInChildAddr::blocksListBis = blocksListHead++[lastNext]).
                { apply notEmptyListHasLast. }
                destruct HlastElem as [lastNext [blocksListHead HlistEqBis]].
                assert(Heq: blockToRemoveInChildAddr::blocksList = blocksListHead++[lastNext]++[nullAddr]).
                {
                  rewrite HlistEq. rewrite app_comm_cons. rewrite HlistEqBis. rewrite <-app_assoc. reflexivity.
                }
                assert(HlastProps: scentryNext (CPaddr (lastNext+scoffset)) nullAddr s0
                  /\ bentryEndAddr lastNext endRange s0).
                {
                  revert Heq HisRange HblocksList. apply secToLastElHasNextNullAndLastAddr; trivial.
                }
                destruct HlastProps as (HnextLast & HendLast).
                assert(HlastIn: In lastNext (blockToRemoveInChildAddr::blocksList)).
                {
                  rewrite Heq. apply in_or_app. right. apply in_or_app. left. simpl. auto.
                }
                assert(HlastMapped: In lastNext (getMappedBlocks idPDchild s0)).
                {
                  destruct (beqAddr blockToRemoveInChildAddr lastNext) eqn:HbeqBlocks.
                  - rewrite <-beqAddrTrue in HbeqBlocks. subst lastNext. assumption.
                  - rewrite <-beqAddrFalse in *. revert HblocksList. apply removeRecBlocksWereMapped; trivial.
                    + intro Hcontra. subst lastNext. unfold bentryEndAddr in *. unfold nullAddrExists in *.
                      unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
                      destruct v; congruence.
                    + simpl in HlastIn. destruct HlastIn as [Hcontra | Hres]; try(exfalso; congruence). assumption.
                }
                assert(HparentBounds: parentBlocksBoundsIfNoNext s0)
                  by (unfold consistency in *; unfold consistency2 in *; intuition).
                assert(HstartLast: exists startLast, bentryStartAddr lastNext startLast s0).
                {
                  unfold bentryStartAddr. unfold bentryEndAddr in *.
                  destruct (lookup lastNext (memory s0) beqAddr); try(exfalso; congruence).
                  destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
                }
                destruct HstartLast as [startLast HstartLast].
                assert(HeqTriv: CPaddr (lastNext+scoffset) = CPaddr (lastNext+scoffset)) by reflexivity.
                specialize(HparentBounds idPDchild pdentry lastNext (CPaddr (lastNext+scoffset)) startLast endRange
                  HchildIsParts0 HlastMapped HstartLast HendLast HeqTriv HnextLast HbeqPartRoot HlookupChild).
                destruct HparentBounds as [blockParent [startP (HblockPMapped & HstartPBis & HendPBis & HlebStarts)]].
                assert(blockParent = blockToRemoveInCurrPartAddr).
                {
                  rewrite <-HisParent in *. destruct (beqAddr blockParent blockToRemoveInCurrPartAddr) eqn:HbeqBPs;
                    try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
                  assert(HPflagLast: bentryPFlag lastNext true s0).
                  {
                    apply IL.mappedBlockIsBE in HlastMapped. destruct HlastMapped as [bentry (Hlookup & Hpres)].
                    unfold bentryPFlag. rewrite Hlookup. auto.
                  }
                  assert(HwellLast: wellFormedBlock s0) by assumption.
                  specialize(HwellLast lastNext startLast endRange HPflagLast HstartLast HendLast).
                  destruct HwellLast as (HwellLast & _).
                  assert(HstartLInLast: In startLast (getAllPaddrAux [lastNext] s0)).
                  {
                    simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                    destruct (lookup lastNext (memory s0) beqAddr); try(simpl; congruence).
                    destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartLast. rewrite <-HendLast.
                    apply IL.getAllPaddrBlockIncl; lia.
                  }
                  assert(HstartLInBP: In startLast (getAllPaddrAux [blockParent] s0)).
                  {
                    simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                    destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
                    destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartPBis. rewrite <-HendPBis.
                    apply IL.getAllPaddrBlockIncl; lia.
                  }
                  pose proof (DisjointPaddrInPart currentPart blockParent blockToRemoveInCurrPartAddr startLast s0
                    HnoDupPaddr HcurrIsPDT HblockPMapped HblockPMappeds0 HbeqBPs HstartLInBP) as Hcontra.
                  contradict Hcontra. revert HlastIn HlastNext HnextBlocksList.
                  apply removedAddrsInSameParent with pdentry currentPart globalIdBlockToRemove; trivial.
                  1,2: unfold consistency in *; unfold consistency1 in *;  intuition.
                  specialize(Hwell blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HPflagPs0
                    HstartP HendPs0).
                  destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite <-HstartP. rewrite <-HendPs0. rewrite app_nil_r.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                subst blockParent. unfold bentryEndAddr in *.
                destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HendPs0 in *. assumption.
              }
              subst endRange.
              unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBPEq in *.
              rewrite HlookupBlockPs1 in *. rewrite <-HstartP in *. rewrite <-HendPs0 in *. rewrite <-HisRange in *.
              revert HnextBlocksList. apply addrInRemovesRangeIsInAccBlock; trivial.
            }
            destruct HaddrMappedList as [blockC (HblockCInList & HAflagC & HaddrInChild)].
            apply IL.addrInAccessibleBlockIsAccessibleMapped with blockC; trivial. simpl in *.
            destruct HblockCInList as [HblocksEq | HblockCInList].
            + subst blockC. assumption.
            + revert HblocksList. apply removeRecBlocksWereMapped; trivial.
              2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition. unfold bentryAFlag in *.
              assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              intro Hcontra. subst blockC. unfold isPADDR in *.
              destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          - rewrite <-beqAddrFalse in *. rewrite HgetAccMappedPEq; trivial.
            apply IL.partitionsArePDT; unfold consistency1 in *; intuition.
          (* END kernelDataIsolation *)
        }

        assert(verticalSharing s).
        { (* BEGIN verticalSharing s *)
          assert(HVSs1: verticalSharing s1) by intuition.
          intros pdparent child HparentIsPart HchildBisIsChild. rewrite HgetPartsEq in *.
          assert(isPDT pdparent s1) by (apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition).
          rewrite HgetChildrenEq in *; trivial. rewrite HgetMappedPEq; trivial. unfold getUsedPaddr.
          specialize(HVSs1 pdparent child HparentIsPart HchildBisIsChild). assert(isPDT child s1).
          { apply IL.childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition. }
          rewrite HgetConfigEq; trivial. rewrite HgetMappedPEq; trivial.
          (* END verticalSharing *)
        }

        assert(nullAddrExists s).
        { (* BEGIN nullAddrExists s *)
          assert(Hcons0: nullAddrExists s1) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr nullAddr) eqn:HbeqBTRNull.
          {
            rewrite <-beqAddrTrue in HbeqBTRNull. subst blockToRemoveInCurrPartAddr. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END nullAddrExists *)
        }

        assert(wellFormedFstShadowIfBlockEntry s).
        { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
          assert(Hcons0: wellFormedFstShadowIfBlockEntry s1) by (unfold consistency1 in *; intuition).
          intros block HblockIsBE. assert(HblockIsBEs1: isBE block s1).
          {
            unfold isBE in *. rewrite Hs in HblockIsBE. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. trivial.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          specialize(Hcons0 block HblockIsBEs1). unfold isSHE in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBTRSh1.
          {
            rewrite <-beqAddrTrue in HbeqBTRSh1. subst blockToRemoveInCurrPartAddr.
            destruct (lookup (CPaddr (block+sh1offset)) (memory s1) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END wellFormedFstShadowIfBlockEntry *)
        }

        assert(HPDTIfPDFlagPartial: forall block sh1entryaddrBis,
          blockToRemoveInCurrPartAddr <> block
          -> true = checkChild block s sh1entryaddrBis /\ sh1entryAddr block sh1entryaddrBis s
          -> bentryAFlag block false s /\ bentryPFlag block true s
              /\ exists startaddr, bentryStartAddr block startaddr s /\ entryPDT block startaddr s).
        {
          intros block sh1entryaddrBis HbeqBlocks HcheckChild. unfold checkChild in *. unfold sh1entryAddr in *.
          unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr. unfold entryPDT. rewrite Hs in HcheckChild.
          rewrite Hs. simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(HcheckChilds1: true = checkChild block s1 sh1entryaddrBis /\ sh1entryAddr block sh1entryaddrBis s1).
          {
            destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. unfold checkChild.
            destruct (lookup block (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
            destruct (beqAddr blockToRemoveInCurrPartAddr sh1entryaddrBis) eqn:HbeqBTRPSh1; try(congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          assert(Hcons0: PDTIfPDFlag s1) by (unfold consistency1 in *; intuition).
          specialize(Hcons0 block sh1entryaddrBis HcheckChilds1).
          destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
          exists startaddr. split; trivial. unfold entryPDT in *.
          destruct (lookup block (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr (startAddr (blockrange b))) eqn:HbeqBTRPStart.
          {
            rewrite <-beqAddrTrue in HbeqBTRPStart. rewrite HbeqBTRPStart in *. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }

        assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
        { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
          assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
          intros partition pdentryBis HlookupPart HbeqFirstNull. rewrite Hs in HlookupPart. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition pdentryBis HlookupPart HbeqFirstNull).
          destruct Hcons0 as (HfirstIsBE & HfirstIsFree). unfold isBE. unfold isFreeSlot in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (firstfreeslot pdentryBis)) eqn:HbeqBTRFirst.
          {
            exfalso. rewrite <-beqAddrTrue in HbeqBTRFirst. rewrite <-HbeqBTRFirst in *.
            unfold bentryPFlag in *. rewrite <-HlookupBPEq in *. rewrite HlookupBlockPs1 in *.
            destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s1) beqAddr); try(congruence).
            destruct v; try(congruence).
            destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+scoffset)) (memory s1) beqAddr); try(congruence).
            destruct v; try(congruence). destruct HfirstIsFree as (_ & _ & _ & _ & Hpres & _). congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial.
          destruct (lookup (firstfreeslot pdentryBis) (memory s1) beqAddr); try(congruence).
          destruct v; try(congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (firstfreeslot pdentryBis+sh1offset)))
            eqn:HbeqBTRSh1.
          {
            rewrite <-beqAddrTrue in HbeqBTRSh1. rewrite <-HbeqBTRSh1 in *. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup (CPaddr (firstfreeslot pdentryBis+sh1offset)) (memory s1) beqAddr); try(congruence).
          destruct v; try(congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (firstfreeslot pdentryBis+scoffset)))
            eqn:HbeqBTRSce.
          {
            rewrite <-beqAddrTrue in HbeqBTRSce. rewrite <-HbeqBTRSce in *. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
        }

        assert(multiplexerIsPDT s).
        { (* BEGIN multiplexerIsPDT s *)
          assert(Hcons0: multiplexerIsPDT s1) by (unfold consistency1 in *; intuition).
          unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr multiplexer) eqn:HbeqBTRMult.
          {
            rewrite <-beqAddrTrue in HbeqBTRMult. subst blockToRemoveInCurrPartAddr. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END multiplexerIsPDT *)
        }

        assert(currentPartitionInPartitionsList s).
        { (* BEGIN currentPartitionInPartitionsList s *)
          assert(Hcons0: currentPartitionInPartitionsList s1) by (unfold consistency1 in *; intuition).
          unfold currentPartitionInPartitionsList. rewrite HgetPartsEq. rewrite Hs. simpl. assumption.
          (* END currentPartitionInPartitionsList *)
        }

        assert(wellFormedShadowCutIfBlockEntry s).
        { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
          assert(Hcons0: wellFormedShadowCutIfBlockEntry s1) by (unfold consistency1 in *; intuition).
          intros block HblockIsBE. assert(HblockIsBEs1: isBE block s1).
          {
            unfold isBE in *. rewrite Hs in HblockIsBE. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. trivial.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          specialize(Hcons0 block HblockIsBEs1). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)].
          exists scentryaddr. split; trivial. unfold isSCE in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr scentryaddr) eqn:HbeqBTRSce.
          {
            rewrite <-beqAddrTrue in HbeqBTRSce. subst blockToRemoveInCurrPartAddr. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END wellFormedShadowCutIfBlockEntry *)
        }

        assert(BlocksRangeFromKernelStartIsBE s).
        { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
          assert(Hcons0: BlocksRangeFromKernelStartIsBE s1) by (unfold consistency1 in *; intuition).
          intros kernel idx HkernIsKS HltIdxKernEntries. assert(HkernIsKSs1: isKS kernel s1).
          {
            unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr kernel) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlockPs1.
              rewrite HnewB in HkernIsKS. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          specialize(Hcons0 kernel idx HkernIsKSs1 HltIdxKernEntries). unfold isBE. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (kernel + idx))) eqn:HbeqBTRIdx; trivial.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END BlocksRangeFromKernelStartIsBE *)
        }

        assert(KernelStructureStartFromBlockEntryAddrIsKS s).
        { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
          assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s1) by (unfold consistency1 in *; intuition).
          intros block idx HblockIsBE Hidx. assert(Hblocks1: isBE block s1 /\ bentryBlockIndex block idx s1).
          {
            unfold isBE in *. unfold bentryBlockIndex in *. rewrite Hs in HblockIsBE. rewrite Hs in Hidx.
            simpl in *. destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in Hidx.
              auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hblocks1 as (HblockIsBEs1 & Hidxs1). specialize(Hcons0 block idx HblockIsBEs1 Hidxs1).
          unfold isKS in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (block - idx))) eqn:HbeqBTRKern.
          - rewrite <-beqAddrTrue in HbeqBTRKern. subst blockToRemoveInCurrPartAddr. rewrite HlookupBlockPs1 in *.
            rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END KernelStructureStartFromBlockEntryAddrIsKS *)
        }

        assert(sh1InChildLocationIsBE s).
        { (* BEGIN sh1InChildLocationIsBE s *)
          assert(Hcons0: sh1InChildLocationIsBE s1) by (unfold consistency1 in *; intuition).
          intros sh1entryaddrBis sh1entry HlookupSh1 HbeqLocNull. rewrite Hs in HlookupSh1. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr sh1entryaddrBis) eqn:HbeqBTRSh1; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 sh1entryaddrBis sh1entry HlookupSh1 HbeqLocNull). unfold isBE. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (inChildLocation sh1entry)) eqn:HbeqBTRLoc; trivial.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END sh1InChildLocationIsBE *)
        }

        assert(StructurePointerIsKS s).
        { (* BEGIN StructurePointerIsKS s *)
          assert(Hcons0: StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
          intros partition pdentryBis HlookupPart HbeqStructNull. rewrite Hs in HlookupPart. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition pdentryBis HlookupPart HbeqStructNull). unfold isKS in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (structure pdentryBis)) eqn:HbeqBTRStruct.
          - rewrite <-beqAddrTrue in HbeqBTRStruct. subst blockToRemoveInCurrPartAddr. rewrite HlookupBlockPs1 in *.
            rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END StructurePointerIsKS *)
        }

        assert(NextKSIsKS s).
        { (* BEGIN NextKSIsKS s *)
          assert(Hcons0: NextKSIsKS s1) by (unfold consistency1 in *; intuition).
          intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull.
          assert(Hkerns1: isKS kernel s1 /\ nextKSAddr kernel nextKSaddr s1).
          {
            unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr kernel) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlockPs1.
              rewrite HnewB in HkernIsKS. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hkerns1 as (HkernIsKSs1 & HnextAddrs1). unfold nextKSentry in *. rewrite Hs in HnextKSAddr.
          simpl in *. destruct (beqAddr blockToRemoveInCurrPartAddr nextKSaddr) eqn:HbeqBTRNext;
            try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKSs1 HnextAddrs1 HnextKSAddr HbeqNextNull).
          unfold isKS in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr nextKS) eqn:HbeqBTRNextKS.
          - rewrite <-beqAddrTrue in HbeqBTRNextKS. subst nextKS. rewrite HlookupBlockPs1 in *.
            rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END NextKSIsKS *)
        }

        assert(NextKSOffsetIsPADDR s).
        { (* BEGIN NextKSOffsetIsPADDR s *)
          assert(Hcons0: NextKSOffsetIsPADDR s1) by (unfold consistency1 in *; intuition).
          intros kernel nextKSaddr HkernIsKS HnextAddr.
          assert(Hkerns1: isKS kernel s1 /\ nextKSAddr kernel nextKSaddr s1).
          {
            unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr kernel) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlockPs1.
              rewrite HnewB in HkernIsKS. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hkerns1 as (HkernIsKSs1 & HnextAddrs1).
          specialize(Hcons0 kernel nextKSaddr HkernIsKSs1 HnextAddrs1). destruct Hcons0 as (Hcons0 & HbeqNextNull).
          split; trivial. unfold isPADDR in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr nextKSaddr) eqn:HbeqBTRNextAddr.
          {
            rewrite <-beqAddrTrue in HbeqBTRNextAddr. subst nextKSaddr. rewrite HlookupBlockPs1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END NextKSOffsetIsPADDR *)
        }

        assert(HBTRPNotFree: ~isFreeSlot blockToRemoveInCurrPartAddr s1).
        {
          unfold isFreeSlot. unfold bentryPFlag in *. rewrite HlookupBPEq in *. rewrite HlookupBlockPs1 in *.
          intro Hcontra.
          destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s1) beqAddr); try(congruence).
          destruct v; try(congruence).
          destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+scoffset)) (memory s1) beqAddr); try(congruence).
          destruct v; try(congruence). destruct Hcontra as (_ & _ & _ & _ & Hcontra & _). congruence.
        }

        assert(HbeqBTRPNull: blockToRemoveInCurrPartAddr <> nullAddr).
        {
          intro Hcontra. assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition).
          unfold isPADDR in *. subst blockToRemoveInCurrPartAddr. rewrite HlookupBlockPs1 in *. congruence.
        }

        assert(HgetFreeEq: forall part, getFreeSlotsList part s = getFreeSlotsList part s1).
        {
          intro part. unfold getFreeSlotsList. rewrite Hs at 1. simpl lookup.
          destruct (beqAddr blockToRemoveInCurrPartAddr part) eqn:HbeqBTRPart.
          {
            rewrite <-beqAddrTrue in HbeqBTRPart. subst part. rewrite HlookupBlockPs1. reflexivity.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup part (memory s1) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
          destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial. rewrite Hs.
          assert(HnoDupFree: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
          specialize(HnoDupFree part p HlookupPart).
          destruct HnoDupFree as [optFreeList (HoptList & HwellFree & HnoDupFree)]. subst optFreeList.
          unfold getFreeSlotsList in *. rewrite HlookupPart in *. rewrite HbeqFirstNull in *.
          apply IL.getFreeSlotsListRecEqBE; trivial.
          - assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
            rewrite <-beqAddrFalse in *. specialize(HfirstIsFree part p HlookupPart HbeqFirstNull).
            destruct HfirstIsFree as (_ & HfirstIsFree). intro Hcontra. subst blockToRemoveInCurrPartAddr.
            congruence.
          - unfold isBE. rewrite HlookupBlockPs1. trivial.
          - assert(HfreeAreFree: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
            intro Hcontra. assert(HpartIsPDT: isPDT part s1) by (unfold isPDT; rewrite HlookupPart; trivial).
            assert(HoptFree: getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s1 (nbfreeslots p)
                = getFreeSlotsList part s1
              /\ wellFormedFreeSlotsList (getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s1 (nbfreeslots p))
                  <> False).
            {
              split; trivial. unfold getFreeSlotsList. rewrite HlookupPart. rewrite HbeqFirstNull. reflexivity.
            }
            assert(Hfree: filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s1 (nbfreeslots p))
                = filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s1 (nbfreeslots p))
              /\ In blockToRemoveInCurrPartAddr (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) (firstfreeslot p)
                s1 (nbfreeslots p)))) by auto.
            specialize(HfreeAreFree part blockToRemoveInCurrPartAddr
              (getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s1 (nbfreeslots p))
              (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s1 (nbfreeslots p))) HpartIsPDT
              HoptFree Hfree HbeqBTRPNull). congruence.
        }

        assert(NoDupInFreeSlotsList s).
        { (* BEGIN NoDupInFreeSlotsList s *)
          assert(Hcons0: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
          intros partition pdentryBis HlookupPart. rewrite Hs in HlookupPart. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition pdentryBis HlookupPart). rewrite HgetFreeEq. assumption.
          (* END NoDupInFreeSlotsList *)
        }

        assert(freeSlotsListIsFreeSlot s).
        { (* BEGIN freeSlotsListIsFreeSlot s *)
          assert(Hcons0: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
          intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
          rewrite HgetFreeEq in *. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList
            HbeqAddrNull). unfold isFreeSlot in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:HbeqBTRPAddr.
          {
            rewrite <-beqAddrTrue in HbeqBTRPAddr. subst addr. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup addr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (addr+sh1offset))) eqn:HbeqBTRPSh1.
          {
            rewrite <-beqAddrTrue in HbeqBTRPSh1. rewrite HbeqBTRPSh1 in *. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup (CPaddr (addr+sh1offset)) (memory s1) beqAddr); try(congruence).
          destruct v; try(congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (addr+scoffset))) eqn:HbeqBTRPSce.
          {
            rewrite <-beqAddrTrue in HbeqBTRPSce. rewrite HbeqBTRPSce in *. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END freeSlotsListIsFreeSlot *)
        }

        assert(DisjointFreeSlotsLists s).
        { (* BEGIN DisjointFreeSlotsLists s *)
          assert(Hcons0: DisjointFreeSlotsLists s1) by (unfold consistency1 in *; intuition).
          intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. rewrite Hs in Hpart1IsPDT.
          rewrite Hs in Hpart2IsPDT. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr part1) eqn:HbeqBTRPart1; try(exfalso; congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr part2) eqn:HbeqBTRPart2; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). rewrite HgetFreeEq. rewrite HgetFreeEq.
          assumption.
          (* END DisjointFreeSlotsLists *)
        }

        assert(inclFreeSlotsBlockEntries s).
        { (* BEGIN inclFreeSlotsBlockEntries s *)
          assert(Hcons0: inclFreeSlotsBlockEntries s1) by (unfold consistency1 in *; intuition).
          intros partition HpartIsPDT. rewrite HgetFreeEq. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition HpartIsPDT). rewrite HgetKSEq. assumption.
          (* END inclFreeSlotsBlockEntries *)
        }

        assert(DisjointKSEntries s).
        { (* BEGIN DisjointKSEntries s *)
          assert(Hcons0: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
          intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. rewrite Hs in Hpart1IsPDT.
          rewrite Hs in Hpart2IsPDT. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr part1) eqn:HbeqBTRPart1; try(exfalso; congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr part2) eqn:HbeqBTRPart2; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). rewrite HgetKSEq. rewrite HgetKSEq.
          assumption.
          (* END DisjointKSEntries *)
        }

        assert(noDupPartitionTree s).
        { (* BEGIN noDupPartitionTree s *)
          assert(Hcons0: noDupPartitionTree s1) by (unfold consistency1 in *; intuition). unfold noDupPartitionTree.
          rewrite HgetPartsEq. assumption.
          (* END noDupPartitionTree *)
        }

        assert(isParent s).
        { (* BEGIN isParent s *)
          assert(Hcons0: isParent s1) by (unfold consistency1 in *; intuition).
          intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEq in *.
          assert(isPDT pdparent s1) by (apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition).
          rewrite HgetChildrenEq in *; trivial. specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild).
          unfold pdentryParent in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPPart.
          {
            rewrite <-beqAddrTrue in HbeqBTRPPart. subst partition. rewrite HlookupBlockPs1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END isParent *)
        }

        assert(isChild s).
        { (* BEGIN isChild s *)
          assert(Hcons0: isChild s1) by (unfold consistency1 in *; intuition).
          intros partition pdparent HpartIsPart HparentIsParent HbeqPartBisRoot. rewrite HgetPartsEq in *.
          unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartBisRoot).
          assert(HparentIsPDT: isPDT pdparent s1).
          {
            unfold isPDT. unfold getChildren in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
            destruct (lookup pdparent (memory s1) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          rewrite HgetChildrenEq; trivial.
          (* END isChild *)
        }

        assert(noDupKSEntriesList s).
        { (* BEGIN noDupKSEntriesList s *)
          assert(Hcons0: noDupKSEntriesList s1) by (unfold consistency1 in *; intuition).
          intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition HpartIsPDT). rewrite HgetKSEq. assumption.
          (* END noDupKSEntriesList *)
        }

        assert(noDupMappedBlocksList s).
        { (* BEGIN noDupMappedBlocksList s *)
          assert(Hcons0: noDupMappedBlocksList s1) by (unfold consistency1 in *; intuition).
          intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition HpartIsPDT). rewrite HgetMappedBEq. assumption.
          (* END noDupMappedBlocksList *)
        }

        assert(wellFormedBlock s).
        { (* BEGIN wellFormedBlock s *)
          assert(Hcons0: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
          intros block startaddr endaddr HPflag HstartBlock HendBlock.
          assert(Hblocks1: bentryPFlag block true s1 /\ bentryStartAddr block startaddr s1
            /\ bentryEndAddr block endaddr s1).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs in HPflag.
            rewrite Hs in HstartBlock. rewrite Hs in HendBlock. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hblocks1 as (HPflags1 & HstartBlocks1 & HendBlocks1).
          specialize(Hcons0 block startaddr endaddr HPflags1 HstartBlocks1 HendBlocks1). assumption.
          (* END wellFormedBlock *)
        }

        assert(parentOfPartitionIsPartition s).
        { (* BEGIN parentOfPartitionIsPartition s *)
          assert(Hcons0: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
          intros partition pdentryBis HlookupPart. rewrite Hs in HlookupPart. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition pdentryBis HlookupPart). destruct Hcons0 as (HparentIsPart & Hcons0).
          split; trivial. intro HbeqPartBisRoot. specialize(HparentIsPart HbeqPartBisRoot).
          destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEq.
          split; trivial. exists parentEntry. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (parent pdentryBis)) eqn:HbeqBTRPParent.
          {
            rewrite <-beqAddrTrue in HbeqBTRPParent. rewrite HbeqBTRPParent in *. rewrite HlookupBlockPs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END parentOfPartitionIsPartition *)
        }

        assert(NbFreeSlotsISNbFreeSlotsInList s).
        { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
          assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s1) by (unfold consistency1 in *; intuition).
          intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. unfold pdentryNbFreeSlots in *.
          rewrite Hs in HpartIsPDT. rewrite Hs in HnbFree. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree). rewrite HgetFreeEq. assumption.
          (* END NbFreeSlotsISNbFreeSlotsInList *)
        }

        assert(maxNbPrepareIsMaxNbKernels s).
        { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
          assert(Hcons0: maxNbPrepareIsMaxNbKernels s1) by (unfold consistency1 in *; intuition).
          intros partition kernList HlistOfKerns. rewrite Hs in HlistOfKerns.
          apply IL.isListOfKernelsEqBE in HlistOfKerns. specialize(Hcons0 partition kernList HlistOfKerns).
          assumption.
          (* END maxNbPrepareIsMaxNbKernels *)
        }

        assert(blockInChildHasAtLeastEquivalentBlockInParent s).
        { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
          assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s1) by (unfold consistency1 in *; intuition).
          intros pdparent child block startChild endChild HparentIsPart HchildBisIsChild HblockMappedChild
            HstartChild HendChild HPflagChild. rewrite HgetPartsEq in *.
          assert(Hblocks1: bentryPFlag block true s1 /\ bentryStartAddr block startChild s1
            /\ bentryEndAddr block endChild s1).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs in HendChild.
            rewrite Hs in HstartChild. rewrite Hs in HPflagChild. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hblocks1 as (HPflags1 & Hstarts1 & Hends1).
          assert(isPDT pdparent s1) by (apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition).
          rewrite HgetChildrenEq in *; trivial. rewrite HgetMappedBEq in *.
          specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildBisIsChild HblockMappedChild
            Hstarts1 Hends1 HPflags1).
          destruct Hcons0 as [blockParent [startP [endP (HblockPBisMapped & HstartPBis & HendPBis & Hbounds)]]].
          exists blockParent. exists startP. exists endP. split; trivial. unfold bentryStartAddr in *. rewrite Hs.
          unfold bentryEndAddr in *. simpl. destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1 in *. rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
          (* END blockInChildHasAtLeastEquivalentBlockInParent *)
        }

        assert(partitionTreeIsTree s).
        { (* BEGIN partitionTreeIsTree s *)
          assert(Hcons0: partitionTreeIsTree s1) by (unfold consistency1 in *; intuition).
          intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
          rewrite HgetPartsEq in *. unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr child) eqn:HbeqBTRChild; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(HparentsLists1: isParentsList s1 parentsList pdparent).
          {
            revert HparentsList. rewrite Hs. apply IL.isParentsListEqBERev with bentry1; trivial.
            - assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
              destruct (lookup child (memory s1) beqAddr) eqn:HlookupChildBis; try(exfalso; congruence).
              destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChildBis).
              destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqChildRoot). subst pdparent.
              destruct HparentIsPart. assumption.
            - unfold consistency1 in *; intuition.
          }
          specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsLists1).
          assumption.
          (* END partitionTreeIsTree *)
        }

        assert(kernelEntriesAreValid s).
        { (* BEGIN kernelEntriesAreValid s *)
          assert(Hcons0: kernelEntriesAreValid s1) by (unfold consistency1 in *; intuition).
          intros kernel idx HkernIsKS Hidx. assert(HkernIsKSs1: isKS kernel s1).
          {
            unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr kernel) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlockPs1.
              rewrite HnewB in HkernIsKS. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          specialize(Hcons0 kernel idx HkernIsKSs1 Hidx). unfold isBE in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (kernel + idx))) eqn:HbeqBTRPIdx; trivial.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END kernelEntriesAreValid *)
        }

        assert(nextKernelIsValid s).
        { (* BEGIN nextKernelIsValid s *)
          assert(Hcons0: nextKernelIsValid s1) by (unfold consistency1 in *; intuition).
          intros kernel HkernIsKS. assert(HkernIsKSs1: isKS kernel s1).
          {
            unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr kernel) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlockPs1.
              rewrite HnewB in HkernIsKS. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          specialize(Hcons0 kernel HkernIsKSs1).
          destruct Hcons0 as (HlebNextMax & [nextKS (HlookupNextAddr & HnextKS)]). split; trivial. exists nextKS.
          split.
          - intro Hp. specialize(HlookupNextAddr Hp). rewrite Hs. simpl.
            destruct (beqAddr blockToRemoveInCurrPartAddr {| p:= kernel+nextoffset; Hp:= Hp |}) eqn:HbeqBTRPNext.
            { rewrite <-beqAddrTrue in HbeqBTRPNext. rewrite HbeqBTRPNext in *. congruence. }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          - destruct HnextKS as [HnextKSIsKS | HnextIsNull]; auto. unfold isKS in *. rewrite Hs. simpl. left.
            destruct (beqAddr blockToRemoveInCurrPartAddr nextKS) eqn:HbeqBTRPNext.
            + rewrite <-beqAddrTrue in HbeqBTRPNext. subst nextKS. rewrite HlookupBlockPs1 in *. rewrite HnewB. auto.
            + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END nextKernelIsValid *)
        }

        assert(noDupListOfKerns s).
        { (* BEGIN noDupListOfKerns s *)
          assert(Hcons0: noDupListOfKerns s1) by (unfold consistency1 in *; intuition).
          intros partition kernList HlistOfKerns. rewrite Hs in HlistOfKerns.
          apply IL.isListOfKernelsEqBE in HlistOfKerns. specialize(Hcons0 partition kernList HlistOfKerns).
          assumption.
          (* END noDupListOfKerns *)
        }

        assert(MPUsizeIsBelowMax s).
        { (* BEGIN MPUsizeIsBelowMax s *)
          assert(Hcons0: MPUsizeIsBelowMax s1) by (unfold consistency1 in *; intuition).
          intros partition MPUlist HMPU. unfold pdentryMPU in *. rewrite Hs in HMPU. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition MPUlist HMPU). assumption.
          (* END MPUsizeIsBelowMax *)
        }

        assert(originIsParentBlocksStart s).
        { (* BEGIN originIsParentBlocksStart s *)
          assert(Hcons0: originIsParentBlocksStart s1) by (unfold consistency1 in *; intuition).
          intros partition pdentryBis block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
          rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. rewrite Hs in HlookupPart. simpl in HlookupPart.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          unfold scentryOrigin in *. rewrite Hs in Horigin. simpl in Horigin.
          destruct (beqAddr blockToRemoveInCurrPartAddr scentryaddr) eqn:HbeqBTRPSce; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition pdentryBis block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
            Horigin). destruct Hcons0 as (HoriginIsStartP & HlebStarts). split.
          - intro HbeqPartBisRoot. specialize(HoriginIsStartP HbeqPartBisRoot).
            destruct HoriginIsStartP as [blockParent (HblockPBisMapped & HstartPBis & Hincl)]. exists blockParent.
            split; trivial. unfold bentryStartAddr in *. rewrite Hs. simpl. split.
            + destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
              * rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1 in *. rewrite HnewB.
                auto.
              * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            + intros addr HaddrInBlock. assert(HaddrInBlocks1: In addr (getAllPaddrAux [block] s1)).
              {
                simpl. destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
                - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
                - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              }
              specialize(Hincl addr HaddrInBlocks1). simpl in *.
              destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
              * rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1 in *. rewrite HnewB.
                auto.
              * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          - intros startaddr Hstart. apply HlebStarts. unfold bentryStartAddr in *. rewrite Hs in Hstart. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            + rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          (* END originIsParentBlocksStart *)
        }

        assert(nextImpliesBlockWasCut s).
        { (* BEGIN nextImpliesBlockWasCut s *)
          assert(Hcons0: nextImpliesBlockWasCut s1) by (unfold consistency1 in *; intuition).
          intros partition pdentryBis block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
            Hsce HbeqNextNull Hnext HbeqPartBisRoot. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *.
          rewrite Hs in HlookupPart. unfold scentryNext in *. rewrite Hs in Hnext. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr scentryaddr) eqn:HbeqBTRPSce; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(HendBlocks1: bentryEndAddr block endaddr s1).
          {
            unfold bentryEndAddr in *. rewrite Hs in HendBlock. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          specialize(Hcons0 partition pdentryBis block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
            HendBlocks1 Hsce HbeqNextNull Hnext HbeqPartBisRoot).
          destruct Hcons0 as [blockParent [endP (HblockPBisMapped & HendPBis & HltEnds & Hincl)]]. exists blockParent.
          exists endP. split; trivial. unfold bentryEndAddr in *. rewrite Hs. simpl. split.
          - destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
            + rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1 in *. rewrite HnewB.
              auto.
            + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          - split; trivial. intros addr HaddrInBlock. assert(HaddrInBlocks1: In addr (getAllPaddrAux [block] s1)).
            {
              simpl. destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
              - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
              - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            }
            specialize(Hincl addr HaddrInBlocks1). simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
            + rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1 in *. rewrite HnewB.
              auto.
            + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END nextImpliesBlockWasCut *)
        }

        assert(blocksAddressesTypes s).
        { (* BEGIN blocksAddressesTypes s *)
          assert(Hcons0: blocksAddressesTypes s1) by (unfold consistency1 in *; intuition).
          intros block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock.
          assert(Hblocks1: bentryStartAddr block startaddr s1 /\ bentryEndAddr block endaddr s1
            /\ bentryPFlag block true s1).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            rewrite Hs in HPflagBlock. rewrite Hs in HstartBlock. rewrite Hs in HendBlock. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hblocks1 as (HstartBlocks1 & HendBlocks1 & HPflags1).
          unfold sh1entryPDchild in *. rewrite Hs in HPDchildBlock. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (block+sh1offset))) eqn:HbeqBTRPSh1;
            try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 block startaddr endaddr HstartBlocks1 HendBlocks1 HPflags1 HPDchildBlock).
          destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hrange]].
          - left. split.
            + unfold isKS in *. rewrite Hs. simpl.
              destruct (beqAddr blockToRemoveInCurrPartAddr startaddr) eqn:HbeqBlocks.
              * rewrite <-beqAddrTrue in HbeqBlocks. subst startaddr. rewrite HlookupBlockPs1 in *. rewrite HnewB.
                auto.
              * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            + intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
              destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
              * left.  unfold isBE in *. rewrite Hs. simpl.
                destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:HbeqBlocks; trivial.
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              * right. left. unfold isSHE in *. rewrite Hs. simpl.
                destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:HbeqBlockAddr.
                { rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockPs1 in *. congruence. }
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              * right. right. left. unfold isSCE in *. rewrite Hs. simpl.
                destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:HbeqBlockAddr.
                { rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockPs1 in *. congruence. }
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              * right. right. right. left. unfold isPADDR in *. rewrite Hs. simpl.
                destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:HbeqBlockAddr.
                { rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockPs1 in *. congruence. }
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              * right. right. right. right. rewrite Hs. simpl.
                destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:HbeqBlockAddr.
                { rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockPs1 in *. congruence. }
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          - right. left. split.
            + unfold isPDT in *. rewrite Hs. simpl.
              destruct (beqAddr blockToRemoveInCurrPartAddr startaddr) eqn:HbeqBlockStart.
              { rewrite <-beqAddrTrue in HbeqBlockStart. subst startaddr. rewrite HlookupBlockPs1 in *. congruence. }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            + intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). rewrite Hs. simpl.
                destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:HbeqBlockAddr.
                { rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockPs1 in *. congruence. }
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          - right. right. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). rewrite Hs. simpl.
            destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:HbeqBlockAddr.
            { rewrite <-beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlockPs1 in *. congruence. }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END blocksAddressesTypes *)
        }

        assert(notPDTIfNotPDflag s).
        { (* BEGIN notPDTIfNotPDflag s *)
          assert(Hcons0: notPDTIfNotPDflag s1) by (unfold consistency1 in *; intuition).
          intros block startaddr sh1entryaddrBis HstartBlock Hsh1 HPflag HPDflag HPDchild.
          assert(Hblocks1: bentryStartAddr block startaddr s1 /\ sh1entryAddr block sh1entryaddrBis s1
            /\ bentryPFlag block true s1).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold sh1entryAddr in *.
            rewrite Hs in HPflag. rewrite Hs in HstartBlock. rewrite Hs in Hsh1. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hblocks1 as (HstartBlocks1 & Hsh1s1 & HPflags1).
          unfold sh1entryPDchild in *. unfold sh1entryPDflag in *. rewrite Hs in HPDchild. rewrite Hs in HPDflag.
          simpl in *. destruct (beqAddr blockToRemoveInCurrPartAddr sh1entryaddrBis) eqn:HbeqBTRPSh1;
            try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 block startaddr sh1entryaddrBis HstartBlocks1 Hsh1s1 HPflags1 HPDflag HPDchild).
          unfold isPDT. rewrite Hs. contradict Hcons0. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr startaddr) eqn:HbeqBTRPStart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          (* END notPDTIfNotPDflag *)
        }

        assert(nextKernAddrIsInSameBlock s).
        { (* BEGIN nextKernAddrIsInSameBlock s *)
          assert(Hcons0: nextKernAddrIsInSameBlock s1) by (unfold consistency1 in *; intuition).
          intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock HkernIsKS.
          assert(Hblocks1: bentryStartAddr block startaddr s1 /\ bentryEndAddr block endaddr s1
            /\ bentryPFlag block true s1).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            rewrite Hs in HPflagBlock. rewrite Hs in HstartBlock. rewrite Hs in HendBlock. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hblocks1 as (HstartBlocks1 & HendBlocks1 & HPflagBlocks1). assert(HkernIsKSs1: isKS kernel s1).
          {
            unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr kernel) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlockPs1.
              rewrite HnewB in HkernIsKS. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          unfold sh1entryPDchild in *. rewrite Hs in HPDchildBlock. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (block+sh1offset))) eqn:HbeqBTRPSh1;
            try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 block kernel startaddr endaddr HstartBlocks1 HendBlocks1 HPflagBlocks1 HPDchildBlock
            HkernIsKSs1). assumption.
          (* END nextKernAddrIsInSameBlock *)
        }

        assert(blockBelongsToAPart s).
        { (* BEGIN blockBelongsToAPart s *)
          assert(Hcons0: blockBelongsToAPart s1) by (unfold consistency1 in *; intuition).
          intros block HPflagBlock. assert(HPflagBlocks1: bentryPFlag block true s1).
          {
            unfold bentryPFlag in *. rewrite Hs in HPflagBlock. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          specialize(Hcons0 block HPflagBlocks1). destruct Hcons0 as [part Hcons0]. exists part. rewrite HgetPartsEq.
          rewrite HgetMappedBEq. assumption.
          (* END blockBelongsToAPart *)
        }

        assert(HPDfNoChild: PDflagMeansNoChild s).
        { (* BEGIN PDflagMeansNoChild s *)
          assert(Hcons0: PDflagMeansNoChild s1) by (unfold consistency1 in *; intuition).
          intros block HblockIsBE HPDflagBlock. assert(HblockIsBEs1: isBE block s1).
          {
            unfold isBE in *. rewrite Hs in HblockIsBE. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. trivial.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          unfold sh1entryPDchild. unfold sh1entryPDflag in *. rewrite Hs in HPDflagBlock. rewrite Hs. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (block+sh1offset))) eqn:HbeqBTRPSh1;
            try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 block HblockIsBEs1 HPDflagBlock). assumption.
          (* END PDflagMeansNoChild *)
        }

        assert(HPDflagBTRP: sh1entryPDflag (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) false s).
        {
          assert(HBTRPIsBE: isBE blockToRemoveInCurrPartAddr s).
          { unfold isBE. rewrite Hs. simpl. rewrite IL.beqAddrTrue. trivial. }
          specialize(HPDfNoChild blockToRemoveInCurrPartAddr HBTRPIsBE). unfold sh1entryAddr in *.
          rewrite <-HlookupBPEq in *. rewrite HlookupBlockPs1 in *. subst sh1entryaddr.
          unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
          assert(Heqs1: lookup (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) (memory s1) beqAddr
            = lookup (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) (memory s0) beqAddr).
          {
            revert HblocksList. apply lookupSh1EqRemoveRec; trivial.
            - assert(Hres: wellFormedFstShadowIfBlockEntry s1) by (unfold consistency1 in *; intuition).
              assert(HBTRPIsBEs1: isBE blockToRemoveInCurrPartAddr s1)
                by (unfold isBE; rewrite HlookupBlockPs1; trivial).
              specialize(Hres blockToRemoveInCurrPartAddr HBTRPIsBEs1). assumption.
            - unfold consistency in *; unfold consistency1 in *; intuition.
          }
          rewrite <-Heqs1 in *. rewrite Hs. rewrite Hs in HPDfNoChild. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset))) eqn:Hbeq.
          {
            rewrite <-beqAddrTrue in Hbeq. rewrite <-Hbeq in *. rewrite HlookupBlockPs1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) (memory s1) beqAddr); try(congruence).
          destruct v; try(congruence). destruct (PDflag s2); trivial. assert(HeqTriv: true = true) by reflexivity.
          specialize(HPDfNoChild HeqTriv). rewrite <-HPDfNoChild in *. congruence.
        }

        assert(HaccNoPDf: AccessibleNoPDFlag s).
        {
          intros block sh1entryaddrBis HblockIsBE Hsh1 HAflag. unfold sh1entryAddr in *.
          unfold bentryAFlag in *. unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs in Hsh1.
          rewrite Hs in HAflag. simpl in *. destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. subst block. subst sh1entryaddrBis.
            destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). subst sh1entryaddr. assumption.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            assert(Hcons0: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
            specialize(Hcons0 block sh1entryaddrBis HblockIsBE Hsh1 HAflag). unfold sh1entryPDflag in *. rewrite Hs.
            simpl. destruct (beqAddr blockToRemoveInCurrPartAddr sh1entryaddrBis) eqn:HbeqBTRPSh1.
            {
              rewrite <-beqAddrTrue in HbeqBTRPSh1. rewrite HbeqBTRPSh1 in *. rewrite HlookupBlockPs1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }

        assert(nbPrepareIsNbKern s).
        { (* BEGIN nbPrepareIsNbKern s *)
          assert(Hcons0: nbPrepareIsNbKern s1) by (unfold consistency1 in *; intuition).
          intros partition pdentryBis HlookupPart. rewrite Hs in HlookupPart. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition pdentryBis HlookupPart). rewrite Hs.
          rewrite completeListOfKernelsEqBE with (bentry:=bentry1); trivial. rewrite HnewB. auto.
         (* END nbPrepareIsNbKern *)
        }

        assert(pdchildIsPDT s).
        { (* BEGIN pdchildIsPDT s *)
          assert(Hcons0: pdchildIsPDT s1) by (unfold consistency1 in *; intuition).
          intros part block sh1entryaddrBis idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
          rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. assert(Hsh1s1: sh1entryAddr block sh1entryaddrBis s1).
          {
            unfold sh1entryAddr in *. rewrite Hs in Hsh1. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. trivial.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr sh1entryaddrBis) eqn:HbeqBTRPSh1; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 part block sh1entryaddrBis idchild HpartBisIsPart HblockMapped Hsh1s1 HPDchild
            HbeqIdChildNull). rewrite HgetChildrenEq; trivial.
          apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition.
          (* END pdchildIsPDT *)
        }

        assert(noDupMappedPaddrList s).
        { (* BEGIN noDupMappedPaddrList s *)
          assert(Hcons0: noDupMappedPaddrList s1) by intuition.
          intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition HpartIsPDT). rewrite HgetMappedPEq; trivial.
          (* END noDupMappedPaddrList *)
        }

        assert(accessibleParentPaddrIsAccessibleIntoChild s).
        { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
          assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s1) by intuition.
          intros pdparent child addr HparentIsPart HchildBisIsChild HaddrAccMappedParent HaddrMappedChild.
          rewrite HgetPartsEq in *.
          assert(isPDT pdparent s1) by (apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition).
          rewrite HgetChildrenEq in *; trivial.
          assert(isPDT child s1) by (apply IL.childrenArePDT with pdparent; unfold consistency1 in *; intuition).
          rewrite HgetMappedPEq in *; trivial.
          assert(Hincl: In addr (getAccessibleMappedPaddr child s1) -> In addr (getAccessibleMappedPaddr child s)).
          {
            intro HaddrAccMappedChild. destruct (beqAddr child currentPart) eqn:HbeqParentCurr.
            - rewrite <-beqAddrTrue in HbeqParentCurr. subst child. apply HgetAccMappedPCurrEquiv.
              apply in_or_app. auto.
            - rewrite <-beqAddrFalse in *. rewrite HgetAccMappedPEq; trivial.
          }
          destruct (beqAddr pdparent currentPart) eqn:HbeqParentCurr.
          - rewrite <-beqAddrTrue in HbeqParentCurr. subst pdparent.
            apply HgetAccMappedPCurrEquiv in HaddrAccMappedParent. apply in_app_or in HaddrAccMappedParent.
            specialize(Hcons0 currentPart child addr HparentIsPart HchildBisIsChild).
            destruct HaddrAccMappedParent as [HaddrInRange | HaddrAccMappedParents1];
              try(apply Hincl; apply Hcons0; assumption). exfalso.
            apply IL.mappedAddrIsInMappedBlock in HaddrMappedChild.
            destruct HaddrMappedChild as [blockC (HBCMapped & HaddrInBC)].
            assert(HPflagBC: bentryPFlag blockC true s1).
            {
              apply IL.mappedBlockIsBE in HBCMapped. destruct HBCMapped as [bentry (Hlookup & Hpres)].
              unfold bentryPFlag. rewrite Hlookup. auto.
            }
            assert(HaddrMappedList: exists blockC, In blockC (blockToRemoveInChildAddr::blocksList)
              /\ bentryAFlag blockC true s0
              /\ In addr (getAllPaddrAux [blockC] s0)).
            {
              assert(HnextBlockSide: blockAndNextAreSideBySide s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              assert(HnoDup: noDupKSEntriesList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupMapped: noDupMappedBlocksList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hdisjoint: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HwellSh1: wellFormedFstShadowIfBlockEntry s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupPaddr: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              pose proof (removedAddrsAreARange s1 s0 idPDchild blockToRemoveInChildAddr statesList blocksList
                HnextBlockSide HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 Hwell HnoDupPaddr HblockCIsNoNext
                HchildIsParts0 HnoDupList HblocksList) as HisRange.
              destruct HisRange as [startRange [endRange HisRange]].
              assert(startRange = globalIdBlockToRemove).
              {
                specialize(Hwell blockToRemoveInChildAddr globalIdBlockToRemove endC HPflagC HstartC HendC).
                destruct Hwell as (Hwell & _).
                unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl in HisRange.
                destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HstartC in *. rewrite <-HendC in *.
                apply eq_sym in HisRange. revert HisRange. apply getAllPaddrBlockSplit. assumption.
              }
              subst startRange. assert(endRange = endBlockToRemove).
              {
                rewrite beqAddrSym in HbeqNullBlockC. rewrite <-beqAddrFalse in *.
                assert(HlastElem: exists blocksListBis, blocksList = blocksListBis++[nullAddr]).
                { apply lastElNotElDef with blockToRemoveInChildAddr; trivial. }
                destruct HlastElem as [blocksListBis HlistEq].
                assert(HlastElem: exists lastNext blocksListHead,
                  blockToRemoveInChildAddr::blocksListBis = blocksListHead++[lastNext]).
                { apply notEmptyListHasLast. }
                destruct HlastElem as [lastNext [blocksListHead HlistEqBis]].
                assert(Heq: blockToRemoveInChildAddr::blocksList = blocksListHead++[lastNext]++[nullAddr]).
                {
                  rewrite HlistEq. rewrite app_comm_cons. rewrite HlistEqBis. rewrite <-app_assoc. reflexivity.
                }
                assert(HlastProps: scentryNext (CPaddr (lastNext+scoffset)) nullAddr s0
                  /\ bentryEndAddr lastNext endRange s0).
                {
                  revert Heq HisRange HblocksList. apply secToLastElHasNextNullAndLastAddr; trivial.
                }
                destruct HlastProps as (HnextLast & HendLast).
                assert(HlastIn: In lastNext (blockToRemoveInChildAddr::blocksList)).
                {
                  rewrite Heq. apply in_or_app. right. apply in_or_app. left. simpl. auto.
                }
                assert(HlastMapped: In lastNext (getMappedBlocks idPDchild s0)).
                {
                  destruct (beqAddr blockToRemoveInChildAddr lastNext) eqn:HbeqBlocks.
                  - rewrite <-beqAddrTrue in HbeqBlocks. subst lastNext. assumption.
                  - rewrite <-beqAddrFalse in *. revert HblocksList. apply removeRecBlocksWereMapped; trivial.
                    + intro Hcontra. subst lastNext. unfold bentryEndAddr in *. unfold nullAddrExists in *.
                      unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
                      destruct v; congruence.
                    + simpl in HlastIn. destruct HlastIn as [Hcontra | Hres]; try(exfalso; congruence). assumption.
                }
                assert(HparentBounds: parentBlocksBoundsIfNoNext s0)
                  by (unfold consistency in *; unfold consistency2 in *; intuition).
                assert(HstartLast: exists startLast, bentryStartAddr lastNext startLast s0).
                {
                  unfold bentryStartAddr. unfold bentryEndAddr in *.
                  destruct (lookup lastNext (memory s0) beqAddr); try(exfalso; congruence).
                  destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
                }
                destruct HstartLast as [startLast HstartLast].
                assert(HeqTriv: CPaddr (lastNext+scoffset) = CPaddr (lastNext+scoffset)) by reflexivity.
                specialize(HparentBounds idPDchild pdentry lastNext (CPaddr (lastNext+scoffset)) startLast endRange
                  HchildIsParts0 HlastMapped HstartLast HendLast HeqTriv HnextLast HbeqPartRoot HlookupChild).
                destruct HparentBounds as [blockParent [startP (HblockPMapped & HstartPBis & HendPBis & HlebStarts)]].
                assert(blockParent = blockToRemoveInCurrPartAddr).
                {
                  rewrite <-HisParent in *. destruct (beqAddr blockParent blockToRemoveInCurrPartAddr) eqn:HbeqBPs;
                    try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
                  assert(HPflagLast: bentryPFlag lastNext true s0).
                  {
                    apply IL.mappedBlockIsBE in HlastMapped. destruct HlastMapped as [bentry (Hlookup & Hpres)].
                    unfold bentryPFlag. rewrite Hlookup. auto.
                  }
                  assert(HwellLast: wellFormedBlock s0) by assumption.
                  specialize(HwellLast lastNext startLast endRange HPflagLast HstartLast HendLast).
                  destruct HwellLast as (HwellLast & _).
                  assert(HstartLInLast: In startLast (getAllPaddrAux [lastNext] s0)).
                  {
                    simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                    destruct (lookup lastNext (memory s0) beqAddr); try(simpl; congruence).
                    destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartLast. rewrite <-HendLast.
                    apply IL.getAllPaddrBlockIncl; lia.
                  }
                  assert(HstartLInBP: In startLast (getAllPaddrAux [blockParent] s0)).
                  {
                    simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                    destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
                    destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartPBis. rewrite <-HendPBis.
                    apply IL.getAllPaddrBlockIncl; lia.
                  }
                  pose proof (DisjointPaddrInPart currentPart blockParent blockToRemoveInCurrPartAddr startLast s0
                    HnoDupPaddr HcurrIsPDT HblockPMapped HblockPMappeds0 HbeqBPs HstartLInBP) as Hcontra.
                  contradict Hcontra. revert HlastIn HlastNext HnextBlocksList.
                  apply removedAddrsInSameParent with pdentry currentPart globalIdBlockToRemove; trivial.
                  1,2: unfold consistency in *; unfold consistency1 in *;  intuition.
                  specialize(Hwell blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HPflagPs0
                    HstartP HendPs0).
                  destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite <-HstartP. rewrite <-HendPs0. rewrite app_nil_r.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                subst blockParent. unfold bentryEndAddr in *.
                destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HendPs0 in *. assumption.
              }
              subst endRange.
              unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBPEq in *.
              rewrite HlookupBlockPs1 in *. rewrite <-HstartP in *. rewrite <-HendPs0 in *. rewrite <-HisRange in *.
              revert HnextBlocksList. apply addrInRemovesRangeIsInAccBlock; trivial.
            }
            destruct HaddrMappedList as [blockCBis (HblockCInList & HAflagC & HaddrInChild)].
            assert(HPflagBCBis: bentryPFlag blockCBis false s1).
            {
              revert HblocksList. apply listsBlocksAreNotPresent; trivial. unfold bentryAFlag in *. intro.
              assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              subst blockCBis. unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
              destruct v; congruence.
            }
            assert(HbeqBlocks: blockC <> blockCBis).
            {
              intro Hcontra. subst blockCBis. unfold bentryPFlag in *.
              destruct (lookup blockC (memory s1) beqAddr); try(congruence). destruct v; congruence.
            }
            assert(HblockCMapped: In blockCBis (getMappedBlocks idPDchild s0)).
            {
              simpl in *. destruct HblockCInList as [Hbeq | HblockCInList]; try(subst blockCBis; assumption).
              revert HblocksList. apply removeRecBlocksWereMapped; trivial.
              2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
              assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
              unfold bentryPFlag in *. intro. subst blockCBis.
              destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
            }
            assert(HBCMappeds0: In blockC (getMappedBlocks child s0)).
            {
              destruct (beqAddr idPDchild child) eqn:HbeqChildren.
              - rewrite <-beqAddrTrue in HbeqChildren. subst child.
                revert HblocksList. apply getMappedInclRemoveRec; trivial.
                unfold consistency in *; unfold consistency1 in *; intuition.
              - rewrite <-beqAddrFalse in *. assert(Heq: getMappedBlocks child s1 = getMappedBlocks child s0).
                {
                  revert HblocksList. apply getMappedBlocksEqRemoveRec; trivial.
                  1,2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
                  unfold consistency in *; unfold consistency2 in *; intuition.
                  exists blocksList. auto.
                }
                rewrite <-Heq. assumption.
            }
            assert(HaddrInBCs0: In addr (getAllPaddrAux [blockC] s0)).
            {
              assert(~ In blockC (blockToRemoveInChildAddr :: blocksList)).
              {
                intro Hcontra. assert(HPflagBCContra: bentryPFlag blockC false s1).
                {
                  revert HblocksList. apply listsBlocksAreNotPresent; trivial. unfold bentryPFlag in *. intro.
                  subst blockC. assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition).
                  unfold isPADDR in *. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence).
                  destruct v; congruence.
                }
                unfold bentryPFlag in *. destruct (lookup blockC (memory s1) beqAddr); try(congruence).
                destruct v; congruence.
              }
              assert(HlookupEq: lookup blockC (memory s1) beqAddr = lookup blockC (memory s0) beqAddr).
              {
                revert HblocksList. apply lookupBEEqRemoveRec; trivial. unfold isBE.
                apply IL.mappedBlockIsBE in HBCMappeds0. destruct HBCMappeds0 as [bentry (Hlookup & _)].
                rewrite Hlookup. trivial.
              }
              simpl in *. rewrite <-HlookupEq. assumption.
            }
            destruct (beqAddr idPDchild child) eqn:HbeqChildren.
            + rewrite <-beqAddrTrue in HbeqChildren. subst child.
              assert(HnoDupPaddr: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              pose proof (DisjointPaddrInPart idPDchild blockC blockCBis addr s0 HnoDupPaddr HchildIsPDT HBCMappeds0
                HblockCMapped HbeqBlocks HaddrInBCs0) as Hcontra. congruence.
            + rewrite <-beqAddrFalse in *. assert(HchildBisIsChilds0: In child (getChildren currentPart s0)).
              {
                assert(Heq: getChildren currentPart s1 = getChildren currentPart s0).
                {
                  revert HblocksList. apply getChildrenEqRemoveRec; trivial; unfold consistency in *;
                    unfold consistency1 in *; intuition.
                }
                rewrite <-Heq. assumption.
              }
              assert(HaddrUsedChild: In addr (getUsedPaddr idPDchild s0)).
              {
                unfold getUsedPaddr. apply in_or_app. right. apply IL.addrInBlockIsMapped with blockCBis; trivial.
              }
              specialize(HPIs0 currentPart idPDchild child HcurrIsParts0 HchildIsChild HchildBisIsChilds0
                HbeqChildren addr HaddrUsedChild). contradict HPIs0. unfold getUsedPaddr. apply in_or_app. right.
              apply IL.addrInBlockIsMapped with blockC; trivial.
          - rewrite <-beqAddrFalse in *. rewrite HgetAccMappedPEq in HaddrAccMappedParent; trivial.
            specialize(Hcons0 pdparent child addr HparentIsPart HchildBisIsChild HaddrAccMappedParent
              HaddrMappedChild). apply Hincl; assumption.
          (* END accessibleParentPaddrIsAccessibleIntoChild *)
        }

        assert(sharedBlockPointsToChild s).
        { (* BEGIN sharedBlockPointsToChild s *)
          assert(Hcons0: sharedBlockPointsToChild s1) by intuition.
          intros pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildBisIsChild HaddrUsedChild
            HaddrInBlockParent HblockParentMapped Hsh1. rewrite HgetPartsEq in *.
          assert(isPDT pdparent s1) by (apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition).
          rewrite HgetChildrenEq in *; trivial. assert(Hsh1s1: sh1entryAddr blockParent sh1entryaddrBis s1).
          {
            unfold sh1entryAddr in *. rewrite Hs in Hsh1. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1. trivial.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          assert(isPDT child s1) by (apply IL.childrenArePDT with pdparent; unfold consistency1 in *; intuition).
          unfold getUsedPaddr in *. rewrite HgetMappedBEq in *; trivial. rewrite HgetMappedPEq in *; trivial.
          rewrite HgetConfigEq in *; trivial. assert(HaddrInBlockParents1: In addr (getAllPaddrAux [blockParent] s1)).
          {
            rewrite Hs in HaddrInBlockParent. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1. rewrite HnewB in *.
              auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          specialize(Hcons0 pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildBisIsChild
            HaddrUsedChild HaddrInBlockParents1 HblockParentMapped Hsh1s1). unfold sh1entryPDchild in *.
          unfold sh1entryPDflag in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBTRPSh1.
          {
            rewrite <-beqAddrTrue in HbeqBTRPSh1. rewrite HbeqBTRPSh1 in *. rewrite HlookupBlockPs1 in *. assumption.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END sharedBlockPointsToChild *)
        }

        assert(adressesRangePreservedIfOriginAndNextOk s).
        { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
          assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s1) by intuition.
          intros partition pdentryBis block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE
            HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartBisRoot. rewrite HgetPartsEq in *.
          rewrite HgetMappedBEq in *. rewrite Hs in HlookupPart. unfold scentryNext in *. rewrite Hs in Hnext.
          unfold scentryOrigin in *. rewrite Hs in Horigin. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr scentryaddr) eqn:HbeqBTRPSce; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(Hblocks1: bentryStartAddr block startBlock s1 /\ bentryEndAddr block endBlock s1
            /\ bentryPFlag block true s1 /\ isBE block s1).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold isBE in *.
            rewrite Hs in HPflag. rewrite Hs in HstartBlock. rewrite Hs in HendBlock. rewrite Hs in HblockIsBE.
            simpl in *. destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hblocks1 as (HstartBlocks1 & HendBlocks1 & HPflags1 & HblockIsBEs1).
          specialize(Hcons0 partition pdentryBis block scentryaddr startBlock endBlock HpartIsPart HblockMapped
            HblockIsBEs1 HstartBlocks1 HendBlocks1 HPflags1 Hsce Horigin Hnext HlookupPart HbeqPartBisRoot).
          destruct Hcons0 as [blockParent (HblockPBisMapped & HBPIsBE & HstartPBis & HendPBis)]. exists blockParent.
          unfold isBE. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1 in *. rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
          (* END adressesRangePreservedIfOriginAndNextOk *)
        }

        assert(childsBlocksPropsInParent s).
        { (* BEGIN childsBlocksPropsInParent s *)
          assert(Hcons0: childsBlocksPropsInParent s1) by intuition.
          intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
            HchildBisIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent
            HendParent HPflagParent HlebStart HgebEnd. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *.
          assert(HparentIsPDT: isPDT pdparent s1)
            by (apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition).
          rewrite HgetChildrenEq in *; trivial.
          assert(HblockCs1: bentryStartAddr blockChild startChild s1 /\ bentryEndAddr blockChild endChild s1
            /\ bentryPFlag blockChild true s1).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            rewrite Hs in HPflagChild. rewrite Hs in HstartChild. rewrite Hs in HendChild. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr blockChild) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst blockChild. rewrite HlookupBlockPs1. rewrite HnewB in *.
              auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct HblockCs1 as (HstartChilds1 & HendChilds1 & HPflagChilds1).
          assert(HblockPs1: bentryStartAddr blockParent startParent s1 /\ bentryEndAddr blockParent endParent s1
            /\ bentryPFlag blockParent true s1).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            rewrite Hs in HPflagParent. rewrite Hs in HstartParent. rewrite Hs in HendParent. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1. rewrite HnewB in *.
              auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct HblockPs1 as (HstartParents1 & HendParents1 & HPflagParents1).
          specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent endParent
            HparentIsPart HchildBisIsChild HblockChildMapped HstartChilds1 HendChilds1 HPflagChilds1
            HblockParentMapped HstartParents1 HendParents1 HPflagParents1 HlebStart HgebEnd).
          destruct Hcons0 as (HcheckChild & HPDchildNotNull & HInChildLocProp & HAflag). unfold checkChild in *.
          unfold bentryAFlag in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
          {
            rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. exfalso.
            assert(HboundsEq: startParent = globalIdBlockToRemove /\ endParent = endBlockToRemove).
            {
              unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBPEq in *.
              rewrite HlookupBlockPs1 in *. subst globalIdBlockToRemove. subst endBlockToRemove. auto.
            }
            destruct HboundsEq. subst startParent. subst endParent. assert(pdparent = currentPart).
            {
              destruct (beqAddr pdparent currentPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
              rewrite <-beqAddrFalse in *.
              assert(HeqMB: getMappedBlocks currentPart s1 = getMappedBlocks currentPart s0).
              {
                revert HblocksList. apply getMappedBlocksEqRemoveRec; auto.
                1,2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
                - unfold consistency in *; unfold consistency2 in *; intuition.
                - exists blocksList. auto.
              }
              rewrite <-HeqMB in *. assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
              specialize(Hdisjoint pdparent currentPart HparentIsPDT HcurrIsPDTs1 HbeqParts).
              destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
              unfold getMappedBlocks in *. apply InFilterPresentInList in HblockParentMapped.
              apply InFilterPresentInList in HblockPMappeds0.
              specialize(Hdisjoint blockToRemoveInCurrPartAddr HblockParentMapped). congruence.
            }
            subst pdparent.  assert(Hwell: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
            specialize(Hwell blockChild startChild endChild HPflagChilds1 HstartChilds1 HendChilds1).
            destruct Hwell as (HltStartEndC & _).
            assert(HaddrMappedList: exists blockC, In blockC (blockToRemoveInChildAddr::blocksList)
              /\ bentryAFlag blockC true s0
              /\ In startChild (getAllPaddrAux [blockC] s0)).
            {
              assert(HstartCInRange: In startChild (getAllPaddrBlock globalIdBlockToRemove endBlockToRemove)).
              { apply IL.getAllPaddrBlockIncl; lia. }
              assert(HnextBlockSide: blockAndNextAreSideBySide s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              assert(HnoDup: noDupKSEntriesList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupMapped: noDupMappedBlocksList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hdisjoint: DisjointKSEntries s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HwellSh1: wellFormedFstShadowIfBlockEntry s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HnoDupPaddr: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              pose proof (removedAddrsAreARange s1 s0 idPDchild blockToRemoveInChildAddr statesList blocksList
                HnextBlockSide HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 Hwell HnoDupPaddr HblockCIsNoNext
                HchildIsParts0 HnoDupList HblocksList) as HisRange.
              destruct HisRange as [startRange [endRange HisRange]].
              assert(startRange = globalIdBlockToRemove).
              {
                specialize(Hwell blockToRemoveInChildAddr globalIdBlockToRemove endC HPflagC HstartC HendC).
                destruct Hwell as (Hwell & _).
                unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl in HisRange.
                destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HstartC in *. rewrite <-HendC in *.
                apply eq_sym in HisRange. revert HisRange. apply getAllPaddrBlockSplit. assumption.
              }
              subst startRange. assert(endRange = endBlockToRemove).
              {
                rewrite beqAddrSym in HbeqNullBlockC. rewrite <-beqAddrFalse in *.
                assert(HlastElem: exists blocksListBis, blocksList = blocksListBis++[nullAddr]).
                { apply lastElNotElDef with blockToRemoveInChildAddr; trivial. }
                destruct HlastElem as [blocksListBis HlistEq].
                assert(HlastElem: exists lastNext blocksListHead,
                  blockToRemoveInChildAddr::blocksListBis = blocksListHead++[lastNext]).
                { apply notEmptyListHasLast. }
                destruct HlastElem as [lastNext [blocksListHead HlistEqBis]].
                assert(Heq: blockToRemoveInChildAddr::blocksList = blocksListHead++[lastNext]++[nullAddr]).
                {
                  rewrite HlistEq. rewrite app_comm_cons. rewrite HlistEqBis. rewrite <-app_assoc. reflexivity.
                }
                assert(HlastProps: scentryNext (CPaddr (lastNext+scoffset)) nullAddr s0
                  /\ bentryEndAddr lastNext endRange s0).
                {
                  revert Heq HisRange HblocksList. apply secToLastElHasNextNullAndLastAddr; trivial.
                }
                destruct HlastProps as (HnextLast & HendLast).
                assert(HlastIn: In lastNext (blockToRemoveInChildAddr::blocksList)).
                {
                  rewrite Heq. apply in_or_app. right. apply in_or_app. left. simpl. auto.
                }
                assert(HlastMapped: In lastNext (getMappedBlocks idPDchild s0)).
                {
                  destruct (beqAddr blockToRemoveInChildAddr lastNext) eqn:HbeqBlocks.
                  - rewrite <-beqAddrTrue in HbeqBlocks. subst lastNext. assumption.
                  - rewrite <-beqAddrFalse in *. revert HblocksList. apply removeRecBlocksWereMapped; trivial.
                    + intro Hcontra. subst lastNext. unfold bentryEndAddr in *. unfold nullAddrExists in *.
                      unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
                      destruct v; congruence.
                    + simpl in HlastIn. destruct HlastIn as [Hcontra | Hres]; try(exfalso; congruence). assumption.
                }
                assert(HparentBounds: parentBlocksBoundsIfNoNext s0)
                  by (unfold consistency in *; unfold consistency2 in *; intuition).
                assert(HstartLast: exists startLast, bentryStartAddr lastNext startLast s0).
                {
                  unfold bentryStartAddr. unfold bentryEndAddr in *.
                  destruct (lookup lastNext (memory s0) beqAddr); try(exfalso; congruence).
                  destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
                }
                destruct HstartLast as [startLast HstartLast].
                assert(HeqTriv: CPaddr (lastNext+scoffset) = CPaddr (lastNext+scoffset)) by reflexivity.
                specialize(HparentBounds idPDchild pdentry lastNext (CPaddr (lastNext+scoffset)) startLast endRange
                  HchildIsParts0 HlastMapped HstartLast HendLast HeqTriv HnextLast HbeqPartRoot HlookupChild).
                destruct HparentBounds as [blockParent [startP (HblockPMapped & HstartPBis & HendPBis &
                  HlebStarts)]].
                assert(blockParent = blockToRemoveInCurrPartAddr).
                {
                  rewrite <-HisParent in *. destruct (beqAddr blockParent blockToRemoveInCurrPartAddr) eqn:HbeqBPs;
                    try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
                  assert(HPflagLast: bentryPFlag lastNext true s0).
                  {
                    apply IL.mappedBlockIsBE in HlastMapped. destruct HlastMapped as [bentry (Hlookup & Hpres)].
                    unfold bentryPFlag. rewrite Hlookup. auto.
                  }
                  assert(HwellLast: wellFormedBlock s0) by assumption.
                  specialize(HwellLast lastNext startLast endRange HPflagLast HstartLast HendLast).
                  destruct HwellLast as (HwellLast & _).
                  assert(HstartLInLast: In startLast (getAllPaddrAux [lastNext] s0)).
                  {
                    simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                    destruct (lookup lastNext (memory s0) beqAddr); try(simpl; congruence).
                    destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartLast. rewrite <-HendLast.
                    apply IL.getAllPaddrBlockIncl; lia.
                  }
                  assert(HstartLInBP: In startLast (getAllPaddrAux [blockParent] s0)).
                  {
                    simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                    destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
                    destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartPBis. rewrite <-HendPBis.
                    apply IL.getAllPaddrBlockIncl; lia.
                  }
                  pose proof (DisjointPaddrInPart currentPart blockParent blockToRemoveInCurrPartAddr startLast s0
                    HnoDupPaddr HcurrIsPDT HblockPMapped HblockPMappeds0 HbeqBPs HstartLInBP) as Hcontra.
                  contradict Hcontra. revert HlastIn HlastNext HnextBlocksList.
                  apply removedAddrsInSameParent with pdentry currentPart globalIdBlockToRemove; trivial.
                  1,2: unfold consistency in *; unfold consistency1 in *;  intuition.
                  specialize(Hwell blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HPflagPs0
                    HstartP HendPs0).
                  destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite <-HstartP. rewrite <-HendPs0. rewrite app_nil_r.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                subst blockParent. unfold bentryEndAddr in *.
                destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HendPs0 in *. assumption.
              }
              subst endRange. rewrite <-HisRange in *.
              revert HnextBlocksList. apply addrInRemovesRangeIsInAccBlock; trivial.
            }
            destruct HaddrMappedList as [blockC (HblockCInList & _ & HstartCInBlockC)]. assert(child = idPDchild).
            {
              destruct (beqAddr child idPDchild) eqn:HbeqChildren; try(rewrite beqAddrTrue; assumption). exfalso.
              rewrite <-beqAddrFalse in *. assert(isBE blockChild s0).
              {
                revert HblocksList. apply isBEEqRemoveRecRev. unfold isBE. unfold bentryPFlag in *.
                destruct (lookup blockChild (memory s1) beqAddr); try(congruence).
                destruct v; try(congruence). trivial.
              }
              assert(HblockInListIsMapped: In blockChild (blockToRemoveInChildAddr :: blocksList)
                -> In blockChild (getMappedBlocks idPDchild s0)).
              {
                intro HBCInList. simpl in *. destruct HBCInList as [HbeqBlocks | HBCInList].
                - subst blockChild. assumption.
                - revert HblocksList. apply removeRecBlocksWereMapped; trivial.
                  2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
                  assert(Hnull: isPADDR nullAddr s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition). unfold isPADDR in *.
                  unfold isBE in *. intro Hcontra. subst blockChild.
                  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
              }
              assert(HeqMB: getMappedBlocks child s1 = getMappedBlocks child s0).
              {
                revert HblocksList. apply getMappedBlocksEqRemoveRec; auto.
                1,2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
                - unfold consistency in *; unfold consistency2 in *; intuition.
                - exists blocksList. auto.
              }
              assert(HlookupEq: lookup blockChild (memory s1) beqAddr = lookup blockChild (memory s0) beqAddr).
              {
                revert HblocksList. apply lookupBEEqRemoveRec; trivial. intro Hcontra.
                apply HblockInListIsMapped in Hcontra. rewrite HeqMB in *.
                assert(Hdisjoint: DisjointKSEntries s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
                unfold getMappedBlocks in *. apply InFilterPresentInList in HblockChildMapped.
                apply InFilterPresentInList in Hcontra. assert(HchildBisIsPDT: isPDT child s0).
                {
                  unfold getKSEntries in *. unfold isPDT.
                  destruct (lookup child (memory s0) beqAddr); try(simpl in *; congruence).
                  destruct v; try(simpl in *; congruence). trivial.
                }
                specialize(Hdisjoint child idPDchild HchildBisIsPDT HchildIsPDT HbeqChildren).
                destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
                specialize(Hdisjoint blockChild HblockChildMapped). congruence.
              }
              unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              rewrite HlookupEq in *. rewrite HeqMB in *.
              assert(HgetChildrenEqs0: getChildren currentPart s1 = getChildren currentPart s0).
              {
                revert HblocksList. apply getChildrenEqRemoveRec; trivial; unfold consistency in *;
                  unfold consistency1 in *; intuition.
              }
              rewrite HgetChildrenEqs0 in *. assert(HstartCInBC: In startChild (getAllPaddrAux [blockChild] s0)).
              {
                simpl. destruct (lookup blockChild (memory s0) beqAddr); try(simpl; congruence).
                destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartChilds1. rewrite <-HendChilds1.
                apply IL.getAllPaddrBlockIncl; lia.
              }
              assert(HstartCMappedChildBis: In startChild (getUsedPaddr child s0)).
              {
                unfold getUsedPaddr. apply in_or_app. right. apply IL.addrInBlockIsMapped with blockChild; trivial.
              }
              specialize(HPIs0 currentPart child idPDchild HcurrIsParts0 HchildBisIsChild HchildIsChild HbeqChildren
                startChild HstartCMappedChildBis). contradict HPIs0. unfold getUsedPaddr. apply in_or_app. right.
              apply IL.addrInBlockIsMapped with blockC; trivial. simpl in *.
              destruct HblockCInList as [HbeqBlocks | HblockCInListRec]; try(subst blockC; assumption).
              revert HblocksList. apply removeRecBlocksWereMapped; trivial.
              2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition. intro Hcontra. subst blockC.
              assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(simpl in *; congruence).
              destruct v; simpl in *; congruence.
            }
            subst child. assert(HPflagBC: bentryPFlag blockC false s1).
            {
              revert HblocksList. apply listsBlocksAreNotPresent; trivial. intro Hcontra. simpl in *. subst blockC.
              assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(simpl in *; congruence).
              destruct v; simpl in *; congruence.
            }
            destruct (beqAddr blockC blockChild) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst blockC. unfold bentryPFlag in *.
              destruct (lookup blockChild (memory s1) beqAddr); try(congruence). destruct v; congruence.
            - rewrite <-beqAddrFalse in *. assert(HblockCBisMapped: In blockC (getMappedBlocks idPDchild s0)).
              {
                simpl in HblockCInList. destruct HblockCInList as [Hbeq | HblockCInListRec].
                - subst blockC. assumption.
                - revert HblocksList. apply removeRecBlocksWereMapped; trivial.
                  2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition. intro Hcontra.
                  simpl in *. subst blockC.
                  assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
                  unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(simpl in *; congruence).
                  destruct v; simpl in *; congruence.
              }
              assert(HblockChildMappeds0: In blockChild (getMappedBlocks idPDchild s0)).
              {
                revert HblocksList. apply getMappedInclRemoveRec; trivial.
                unfold consistency in *; unfold consistency1 in *; intuition.
              }
              assert(HnoDupPaddr: noDupMappedPaddrList s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              pose proof (DisjointPaddrInPart idPDchild blockC blockChild startChild s0 HnoDupPaddr HchildIsPDT
                HblockCBisMapped HblockChildMappeds0 HbeqBlocks HstartCInBlockC) as Hcontra.
              assert(HblockCInListIsNotPres: In blockChild (blockToRemoveInChildAddr :: blocksList)
                -> bentryPFlag blockChild false s1).
              {
                intro HBCInList. revert HblocksList. apply listsBlocksAreNotPresent; trivial. intro. subst blockChild.
                unfold bentryStartAddr in *. assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition).
                unfold isPADDR in *. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence).
                destruct v; congruence.
              }
              assert(HlookupEq: lookup blockChild (memory s1) beqAddr = lookup blockChild (memory s0) beqAddr).
              {
                revert HblocksList. apply lookupBEEqRemoveRec; trivial.
                - apply IL.mappedBlockIsBE in HblockChildMappeds0. destruct HblockChildMappeds0 as [b (Hlookup & _)].
                  unfold isBE. rewrite Hlookup. trivial.
                - intro HBCInList. assert(bentryPFlag blockChild false s1).
                  { apply HblockCInListIsNotPres; trivial. }
                  unfold bentryPFlag in *. destruct (lookup blockChild (memory s1) beqAddr); try(congruence).
                  destruct v; congruence.
              }
              contradict Hcontra. simpl. rewrite <-HlookupEq. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              destruct (lookup blockChild (memory s1) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartChilds1. rewrite <-HendChilds1.
              apply IL.getAllPaddrBlockIncl; lia.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          unfold bentryPFlag in *. destruct (lookup blockParent (memory s1) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). split; try(split; try(split)); trivial.
          - destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (blockParent+sh1offset))) eqn:HbeqBTRPSh1; trivial.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          - intros childGlobalID HPDchild. unfold sh1entryPDchild in *. simpl in *. apply HPDchildNotNull.
            destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (blockParent+sh1offset))) eqn:HbeqBTRPSh1;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          - intros blockIDInChild HchildLoc. apply HInChildLocProp. unfold sh1entryInChildLocation in *. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (blockParent+sh1offset))) eqn:HbeqBTRPSh1;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s1) beqAddr); try(congruence).
            destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial.
            intro HbeqLocNull. specialize(HlocIsBE HbeqLocNull). unfold isBE in *. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr blockIDInChild) eqn:HbeqBTRPLoc.
            + rewrite <-beqAddrTrue in HbeqBTRPLoc. rewrite HbeqBTRPLoc in *. rewrite HlookupBlockPs1. trivial.
            + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          (* END childsBlocksPropsInParent *)
        }

        assert(noChildImpliesAddressesNotShared s).
        { (* BEGIN noChildImpliesAddressesNotShared s *)
          assert(Hcons0: noChildImpliesAddressesNotShared s1) by intuition.
          intros partition pdentryBis block sh1entryaddrBis HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild child
            addr HchildBisIsChild HaddrInBlock. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *.
          rewrite Hs in HlookupPart. unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr sh1entryaddrBis) eqn:HbeqBTRPSh1; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(isPDT partition s1) by (apply IL.partitionsArePDT; trivial; unfold consistency1 in *; intuition).
          assert(HaddrInBlocks1: In addr (getAllPaddrAux [block] s1)).
          {
            rewrite Hs in HaddrInBlock. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *.
              auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          rewrite HgetChildrenEq in *; trivial.
          assert(isPDT child s1) by (apply IL.childrenArePDT with partition; unfold consistency1 in *; intuition).
          specialize(Hcons0 partition pdentryBis block sh1entryaddrBis HpartIsPart HlookupPart HblockMapped Hsh1
            HPDchild child addr HchildBisIsChild HaddrInBlocks1). rewrite HgetMappedPEq; trivial.
          (* END noChildImpliesAddressesNotShared *)
        }

        assert(kernelsAreNotAccessible s).
        { (* BEGIN kernelsAreNotAccessible s *)
          assert(Hcons0: kernelsAreNotAccessible s1) by intuition. intros block startaddr Hstart HPflag HstartIsKS.
          assert(HstartIsKSs1: isKS startaddr s1).
          {
            unfold isKS in *. rewrite Hs in HstartIsKS. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr startaddr) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst startaddr. rewrite HlookupBlockPs1.
              rewrite HnewB in HstartIsKS. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          unfold bentryPFlag in *. unfold bentryStartAddr in *. rewrite Hs in HPflag. rewrite Hs in Hstart.
          unfold bentryAFlag. rewrite Hs. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
          {
            rewrite <-beqAddrTrue in HbeqBlocks. subst block. exfalso. rewrite HlookupBPEq in *. rewrite HnewB in *.
            simpl in *. rewrite HlookupBlockPs1 in *. rewrite <-HstartP in *. subst startaddr.
            assert(Hprops0: kernelsAreNotAccessible s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            assert(HstartIsKSs0: isKS globalIdBlockToRemove s0).
            {
              revert HblocksList. apply isKSPreservedRemoveRecRev; trivial.
            }
            specialize(Hprops0 blockToRemoveInChildAddr globalIdBlockToRemove HstartC HPflagC HstartIsKSs0).
            destruct blocksList; simpl in *.
            - subst blockToRemoveInChildAddr. rewrite <-beqAddrFalse in *. congruence.
            - destruct HnextBlocksList as (HAflag & _). unfold bentryAFlag in *.
              destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          specialize(Hcons0 block startaddr Hstart HPflag HstartIsKSs1). assumption.
          (* END kernelsAreNotAccessible *)
        }

        assert(blockAndNextAreSideBySide s).
        { (* BEGIN blockAndNextAreSideBySide s *)
          assert(Hcons0: blockAndNextAreSideBySide s1) by intuition.
          intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
            Hnext. assert(HendBlocks1: bentryEndAddr block endaddr s1).
          {
            unfold bentryEndAddr in *. rewrite Hs in HendBlock.
            simpl in *. destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. unfold scentryNext in *. rewrite Hs in Hnext.
          simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr scentryaddr) eqn:HbeqBTRPSce; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlocks1 Hsce
            HbeqNextNull Hnext). destruct Hcons0 as (Hstart & HnextMapped). split; trivial.
          unfold bentryStartAddr in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr scnext) eqn:HbeqBTRPNext.
          - rewrite <-beqAddrTrue in HbeqBTRPNext. subst scnext. rewrite HlookupBlockPs1 in *. rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END blockAndNextAreSideBySide *)
        }

        assert(parentBlocksBoundsIfNoNext s).
        { (* BEGIN parentBlocksBoundsIfNoNext s *)
          assert(Hcons0: parentBlocksBoundsIfNoNext s1) by intuition.
          intros partition pdentryBis block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock
            HendBlock Hsce Hnext HbeqPartBisRoot HlookupPart. rewrite Hs in HlookupPart. unfold scentryNext in *.
          rewrite Hs in Hnext. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *. simpl in *.
          destruct (beqAddr blockToRemoveInCurrPartAddr scentryaddr) eqn:HbeqBTRSce; try(exfalso; congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr partition) eqn:HbeqBTRPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(Hblocks1: bentryStartAddr block startaddr s1 /\ bentryEndAddr block endaddr s1).
          {
            unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            rewrite Hs in HstartBlock. rewrite Hs in HendBlock. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr block) eqn:HbeqBlocks.
            - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlockPs1. rewrite HnewB in *. auto.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct Hblocks1 as (HstartBlocks1 & HendBlocks1).
          specialize(Hcons0 partition pdentryBis block scentryaddr startaddr endaddr HpartIsPart HblockMapped
            HstartBlocks1 HendBlocks1 Hsce Hnext HbeqPartBisRoot HlookupPart).
          destruct Hcons0 as [blockParent [startParent (HblockPBisMapped & HstartPBis & HendPBis & HlebStarts)]].
          exists blockParent. exists startParent. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs.
          simpl. destruct (beqAddr blockToRemoveInCurrPartAddr blockParent) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlockPs1 in *. rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
          (* END parentBlocksBoundsIfNoNext *)
        }

        assert(HchildLocMappedInChildPartials: forall part block sh1entryaddr blockChild idchild,
          blockToRemoveInCurrPartAddr <> block
          -> In part (getPartitions multiplexer s)
          -> In block (getMappedBlocks part s)
          -> sh1entryAddr block sh1entryaddr s
          -> sh1entryPDchild sh1entryaddr idchild s
          -> sh1entryInChildLocation sh1entryaddr blockChild s
          -> idchild <> nullAddr
          -> blockChild <> nullAddr
          -> In blockChild (getMappedBlocks idchild s) /\
              (forall startaddr,
                bentryStartAddr block startaddr s -> bentryStartAddr blockChild startaddr s)).
        {
          intros part block sh1entryaddrBis blockChild idchild HbeqBlocks HpartIsPart HblockMapped Hsh1 HPDchild
            HchildLoc HbeqChildNull HbeqBCNull. rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *.
          unfold sh1entryAddr in *. rewrite Hs in Hsh1. unfold sh1entryPDchild in *. rewrite Hs in HPDchild.
          unfold sh1entryInChildLocation in *. rewrite Hs in HchildLoc. unfold bentryStartAddr at 1. rewrite Hs.
          simpl in *. rewrite beqAddrFalse in *. rewrite HbeqBlocks in *.
           destruct (beqAddr blockToRemoveInCurrPartAddr sh1entryaddrBis) eqn:HbeqBTRPSh1; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(HchildLocs1: sh1entryInChildLocation sh1entryaddrBis blockChild s1).
          {
            unfold sh1entryInChildLocation. destruct (lookup sh1entryaddrBis (memory s1) beqAddr); try(congruence).
            destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial.
            intro HbeqLocNull. specialize(HlocIsBE HbeqLocNull). unfold isBE in *. simpl in *.
            destruct (beqAddr blockToRemoveInCurrPartAddr blockChild) eqn:HbeqBlocksBis.
            - rewrite <-beqAddrTrue in HbeqBlocksBis. rewrite HbeqBlocksBis in *. rewrite HlookupBlockPs1. trivial.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          specialize(HchildLocMappedInChildPartial part block sh1entryaddrBis blockChild idchild HbeqBlocks
            HpartIsPart HblockMapped Hsh1 HPDchild HchildLocs1 HbeqChildNull HbeqBCNull).
          destruct HchildLocMappedInChildPartial as (HBCMapped & HstartsEq). split; trivial.
          intros startaddr Hstart. specialize(HstartsEq startaddr Hstart). unfold bentryStartAddr in *. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr blockChild) eqn:HbeqBlocksBis.
          - rewrite <-beqAddrTrue in HbeqBlocksBis. subst blockChild. rewrite HlookupBlockPs1 in *. rewrite HnewB.
            auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }

        assert(~ isFreeSlot blockToRemoveInCurrPartAddr s
          /\ sh1entryAddr blockToRemoveInCurrPartAddr sh1entryaddr s
          /\ bentryPFlag blockToRemoveInCurrPartAddr true s
          /\ bentryAFlag blockToRemoveInCurrPartAddr true s
          /\ bentryStartAddr blockToRemoveInCurrPartAddr globalIdBlockToRemove s).
        {
          unfold bentryStartAddr in *. unfold sh1entryAddr in *. unfold bentryPFlag in *. unfold bentryAFlag.
          unfold isFreeSlot. rewrite <-HlookupBPEq in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue. rewrite HnewB.
          simpl. rewrite HlookupBlockPs1 in *. split; auto.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset))) eqn:Hbeq1;
            try(intro; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s1) beqAddr);
            try(intro; congruence). destruct v; try(intro; congruence).
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (blockToRemoveInCurrPartAddr + scoffset))) eqn:Hbeq2;
            try(intro; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+scoffset)) (memory s1) beqAddr);
            try(intro; congruence). destruct v; try(intro; congruence). intro Hcontra.
          destruct Hcontra as (_ & _ & _ & _ & _ & Hcontra & _). congruence.
        }
        assert(In blockToRemoveInCurrPartAddr (getMappedBlocks currentPart s)).
        {
          rewrite HgetMappedBEq. assert(Heq: getMappedBlocks currentPart s1 = getMappedBlocks currentPart s0).
          {
            revert HblocksList. apply getMappedBlocksEqRemoveRec; auto.
            1,2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
            unfold consistency in *; unfold consistency2 in *; intuition.
            exists blocksList. auto.
          }
          rewrite Heq. assumption.
        }
        assert(In idPDchild (getChildren currentPart s)).
        {
          rewrite HgetChildrenEq; trivial. assert(Heq: getChildren currentPart s1 = getChildren currentPart s0).
          {
            revert HblocksList. apply getChildrenEqRemoveRec; trivial; unfold consistency in *;
              unfold consistency1 in *; intuition.
          }
          rewrite Heq. assumption.
        }
        assert(In currentPart (getPartitions multiplexer s) /\ In idPDchild (getPartitions multiplexer s)).
        {
          rewrite HgetPartsEq. rewrite HgetPartsEqs1. auto.
        }
        assert(sh1entryPDchild sh1entryaddr idPDchild s).
        {
          assert(isSHE (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) s1).
          {
            assert(HwellSh1: wellFormedFstShadowIfBlockEntry s1) by (unfold consistency1 in *; intuition).
            unfold isBE in *. rewrite <-HlookupBPEq in *.
            specialize(HwellSh1 blockToRemoveInCurrPartAddr HblockPIsBEs0). assumption.
          }
          unfold sh1entryAddr in *.
          destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). subst sh1entryaddr. unfold sh1entryPDchild in *.
          assert(Heq: lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s1) beqAddr
            = lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s0) beqAddr).
          {
            revert HblocksList. apply lookupSh1EqRemoveRec; trivial.
            unfold consistency in *; unfold consistency1 in *; intuition.
          }
          rewrite <-Heq in *. rewrite Hs. simpl.
          destruct (beqAddr blockToRemoveInCurrPartAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset))) eqn:Hbeq.
          {
            rewrite <-beqAddrTrue in Hbeq. rewrite <-Hbeq in *. rewrite HlookupBlockPs1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        assert(HremovedAddrsAreNone: forall addr, In addr (getAllPaddrBlock globalIdBlockToRemove endBlockToRemove)
          -> lookup addr (memory s) beqAddr = None).
        {
          intros addr HaddrInRange.
          assert(HaddrMappedList: exists blockC, In blockC (blockToRemoveInChildAddr::blocksList)
            /\ bentryAFlag blockC true s0
            /\ In addr (getAllPaddrAux [blockC] s0)).
          {
            assert(HnextBlockSide: blockAndNextAreSideBySide s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            assert(HnoDup: noDupKSEntriesList s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HnoDupMapped: noDupMappedBlocksList s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hdisjoint: DisjointKSEntries s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HwellSh1: wellFormedFstShadowIfBlockEntry s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HnoDupPaddr: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            pose proof (removedAddrsAreARange s1 s0 idPDchild blockToRemoveInChildAddr statesList blocksList
              HnextBlockSide HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 Hwell HnoDupPaddr HblockCIsNoNext
              HchildIsParts0 HnoDupList HblocksList) as HisRange.
            destruct HisRange as [startRange [endRange HisRange]].
            assert(startRange = globalIdBlockToRemove).
            {
              specialize(Hwell blockToRemoveInChildAddr globalIdBlockToRemove endC HPflagC HstartC HendC).
              destruct Hwell as (Hwell & _).
              unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl in HisRange.
              destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HstartC in *. rewrite <-HendC in *.
              apply eq_sym in HisRange. revert HisRange. apply getAllPaddrBlockSplit. assumption.
            }
            subst startRange. assert(endRange = endBlockToRemove).
            {
              rewrite beqAddrSym in HbeqNullBlockC. rewrite <-beqAddrFalse in *.
              assert(HlastElem: exists blocksListBis, blocksList = blocksListBis++[nullAddr]).
              { apply lastElNotElDef with blockToRemoveInChildAddr; trivial. }
              destruct HlastElem as [blocksListBis HlistEq].
              assert(HlastElem: exists lastNext blocksListHead,
                blockToRemoveInChildAddr::blocksListBis = blocksListHead++[lastNext]).
              { apply notEmptyListHasLast. }
              destruct HlastElem as [lastNext [blocksListHead HlistEqBis]].
              assert(Heq: blockToRemoveInChildAddr::blocksList = blocksListHead++[lastNext]++[nullAddr]).
              {
                rewrite HlistEq. rewrite app_comm_cons. rewrite HlistEqBis. rewrite <-app_assoc. reflexivity.
              }
              assert(HlastProps: scentryNext (CPaddr (lastNext+scoffset)) nullAddr s0
                /\ bentryEndAddr lastNext endRange s0).
              {
                revert Heq HisRange HblocksList. apply secToLastElHasNextNullAndLastAddr; trivial.
              }
              destruct HlastProps as (HnextLast & HendLast).
              assert(HlastIn: In lastNext (blockToRemoveInChildAddr::blocksList)).
              {
                rewrite Heq. apply in_or_app. right. apply in_or_app. left. simpl. auto.
              }
              assert(HlastMapped: In lastNext (getMappedBlocks idPDchild s0)).
              {
                destruct (beqAddr blockToRemoveInChildAddr lastNext) eqn:HbeqBlocks.
                - rewrite <-beqAddrTrue in HbeqBlocks. subst lastNext. assumption.
                - rewrite <-beqAddrFalse in *. revert HblocksList. apply removeRecBlocksWereMapped; trivial.
                  + intro Hcontra. subst lastNext. unfold bentryEndAddr in *. unfold nullAddrExists in *.
                    unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
                    destruct v; congruence.
                  + simpl in HlastIn. destruct HlastIn as [Hcontra | Hres]; try(exfalso; congruence). assumption.
              }
              assert(HparentBounds: parentBlocksBoundsIfNoNext s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              assert(HstartLast: exists startLast, bentryStartAddr lastNext startLast s0).
              {
                unfold bentryStartAddr. unfold bentryEndAddr in *.
                destruct (lookup lastNext (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
              }
              destruct HstartLast as [startLast HstartLast].
              assert(HeqTriv: CPaddr (lastNext+scoffset) = CPaddr (lastNext+scoffset)) by reflexivity.
              specialize(HparentBounds idPDchild pdentry lastNext (CPaddr (lastNext+scoffset)) startLast endRange
                HchildIsParts0 HlastMapped HstartLast HendLast HeqTriv HnextLast HbeqPartRoot HlookupChild).
              destruct HparentBounds as [blockParent [startP (HblockPMapped & HstartPBis & HendPBis &
                HlebStarts)]].
              assert(blockParent = blockToRemoveInCurrPartAddr).
              {
                rewrite <-HisParent in *. destruct (beqAddr blockParent blockToRemoveInCurrPartAddr) eqn:HbeqBPs;
                  try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
                assert(HPflagLast: bentryPFlag lastNext true s0).
                {
                  apply IL.mappedBlockIsBE in HlastMapped. destruct HlastMapped as [bentry (Hlookup & Hpres)].
                  unfold bentryPFlag. rewrite Hlookup. auto.
                }
                assert(HwellLast: wellFormedBlock s0) by assumption.
                specialize(HwellLast lastNext startLast endRange HPflagLast HstartLast HendLast).
                destruct HwellLast as (HwellLast & _).
                assert(HstartLInLast: In startLast (getAllPaddrAux [lastNext] s0)).
                {
                  simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup lastNext (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartLast. rewrite <-HendLast.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                assert(HstartLInBP: In startLast (getAllPaddrAux [blockParent] s0)).
                {
                  simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartPBis. rewrite <-HendPBis.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                pose proof (DisjointPaddrInPart currentPart blockParent blockToRemoveInCurrPartAddr startLast s0
                  HnoDupPaddr HcurrIsPDT HblockPMapped HblockPMappeds0 HbeqBPs HstartLInBP) as Hcontra.
                contradict Hcontra. revert HlastIn HlastNext HnextBlocksList.
                apply removedAddrsInSameParent with pdentry currentPart globalIdBlockToRemove; trivial.
                1,2: unfold consistency in *; unfold consistency1 in *;  intuition.
                specialize(Hwell blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HPflagPs0
                  HstartP HendPs0).
                destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
                destruct v; try(simpl; congruence). rewrite <-HstartP. rewrite <-HendPs0. rewrite app_nil_r.
                apply IL.getAllPaddrBlockIncl; lia.
              }
              subst blockParent. unfold bentryEndAddr in *.
              destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HendPs0 in *. assumption.
            }
            subst endRange. rewrite <-HisRange in *.
            revert HnextBlocksList. apply addrInRemovesRangeIsInAccBlock; trivial.
          }
          destruct HaddrMappedList as [blockC (HblockCInList & HAflagC & HstartCInBlockC)].
          assert(blockC <> nullAddr).
          {
            assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *;  intuition).
            intro. subst blockC. unfold isPADDR in *.
            unfold bentryAFlag in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          assert(HPDchildC: sh1entryPDchild (CPaddr (blockC+sh1offset)) nullAddr s0).
          {
            revert HnextBlocksList. apply blockInListNotShared; trivial.
            unfold consistency in *; unfold consistency1 in *;  intuition.
          }
          assert(HPDflagC: AccessibleNoPDFlag s0) by (unfold consistency in *; unfold consistency1 in *;  intuition).
          assert(HblockCIsBE: isBE blockC s0).
          {
            unfold isBE. unfold bentryAFlag in *.
            destruct (lookup blockC (memory s0) beqAddr); try(congruence). destruct v; try(congruence). trivial.
          }
          assert(Hsh1C: sh1entryAddr blockC (CPaddr (blockC+sh1offset)) s0).
          {
            unfold sh1entryAddr. unfold bentryAFlag in *.
            destruct (lookup blockC (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          specialize(HPDflagC blockC (CPaddr (blockC+sh1offset)) HblockCIsBE Hsh1C HAflagC).
          assert(Hlookups0: lookup addr (memory s0) beqAddr = None).
          {
            assert(HaddrTypes: blocksAddressesTypes s0)
              by (unfold consistency in *; unfold consistency1 in *;  intuition).
            assert(Hbounds: exists startC endCBis, bentryStartAddr blockC startC s0
              /\ bentryEndAddr blockC endCBis s0 /\ In addr (getAllPaddrBlock startC endCBis)).
            {
              unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryAFlag in *. simpl in *.
              destruct (lookup blockC (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite app_nil_r in *. exists (startAddr (blockrange b)).
              exists (endAddr (blockrange b)). auto.
            }
            destruct Hbounds as [startC [endCBis (HstartCBis & HendCBis & HaddrInRangeC)]].
            assert(HPflagCBis: bentryPFlag blockC true s0).
            {
              assert(HblockCMapped: In blockC (getMappedBlocks idPDchild s0)).
              {
                simpl in HblockCInList. destruct HblockCInList; try(subst blockC; assumption).
                revert HblocksList. apply removeRecBlocksWereMapped; trivial;
                  unfold consistency in *; unfold consistency1 in *;  intuition.
              }
              apply IL.mappedBlockIsBE in HblockCMapped. destruct HblockCMapped as [b (Hlookup & Hpres)].
              unfold bentryPFlag. rewrite Hlookup. auto.
            }
            specialize(HaddrTypes blockC startC endCBis HstartCBis HendCBis HPflagCBis HPDchildC).
            destruct HaddrTypes as [(HKS & _) | [(HPDT & _) | Hres]].
            - exfalso. assert(HkernNotAcc: kernelsAreNotAccessible s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              specialize(HkernNotAcc blockC startC HstartCBis HPflagCBis HKS). unfold bentryAFlag in *.
              destruct (lookup blockC (memory s0) beqAddr); try(congruence). destruct v; congruence.
            - exfalso. assert(HnotPDT: notPDTIfNotPDflag s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
              specialize(HnotPDT blockC startC (CPaddr (blockC+sh1offset)) HstartCBis Hsh1C HPflagCBis HPDflagC
                HPDchildC). congruence.
            - apply Hres; assumption.
          }
          rewrite Hs. simpl. destruct (beqAddr blockToRemoveInCurrPartAddr addr) eqn:Hbeq.
          {
            rewrite <-beqAddrTrue in Hbeq. subst addr. unfold isBE in *. rewrite Hlookups0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          revert HblocksList. apply lookupNoneEqRemoveRec; trivial.
        }
        assert(HBTRPsAddsNotShared: forall child addr, In child (getChildren currentPart s)
          -> In addr (getAllPaddrAux [blockToRemoveInCurrPartAddr] s) -> ~ In addr (getMappedPaddr child s)).
        {
          intros child addr HchildBisIsChild HaddrInBTRP HaddrMappedChild.
          assert(HaddrInRange: In addr (getAllPaddrBlock globalIdBlockToRemove endBlockToRemove)).
          {
            assert(HstartPs: bentryStartAddr blockToRemoveInCurrPartAddr globalIdBlockToRemove s) by intuition.
            simpl in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartPs in *. rewrite app_nil_r in *.
            rewrite <-HendP in *. assumption.
          }
          assert(HaddrMappedList: exists blockC, In blockC (blockToRemoveInChildAddr::blocksList)
            /\ bentryAFlag blockC true s0
            /\ In addr (getAllPaddrAux [blockC] s0)).
          {
            assert(HnextBlockSide: blockAndNextAreSideBySide s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            assert(HnoDup: noDupKSEntriesList s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HnoDupMapped: noDupMappedBlocksList s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hdisjoint: DisjointKSEntries s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HwellSh1: wellFormedFstShadowIfBlockEntry s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HnoDupPaddr: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            pose proof (removedAddrsAreARange s1 s0 idPDchild blockToRemoveInChildAddr statesList blocksList
              HnextBlockSide HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 Hwell HnoDupPaddr HblockCIsNoNext
              HchildIsParts0 HnoDupList HblocksList) as HisRange.
            destruct HisRange as [startRange [endRange HisRange]].
            assert(startRange = globalIdBlockToRemove).
            {
              specialize(Hwell blockToRemoveInChildAddr globalIdBlockToRemove endC HPflagC HstartC HendC).
              destruct Hwell as (Hwell & _).
              unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl in HisRange.
              destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HstartC in *. rewrite <-HendC in *.
              apply eq_sym in HisRange. revert HisRange. apply getAllPaddrBlockSplit. assumption.
            }
            subst startRange. assert(endRange = endBlockToRemove).
            {
              rewrite beqAddrSym in HbeqNullBlockC. rewrite <-beqAddrFalse in *.
              assert(HlastElem: exists blocksListBis, blocksList = blocksListBis++[nullAddr]).
              { apply lastElNotElDef with blockToRemoveInChildAddr; trivial. }
              destruct HlastElem as [blocksListBis HlistEq].
              assert(HlastElem: exists lastNext blocksListHead,
                blockToRemoveInChildAddr::blocksListBis = blocksListHead++[lastNext]).
              { apply notEmptyListHasLast. }
              destruct HlastElem as [lastNext [blocksListHead HlistEqBis]].
              assert(Heq: blockToRemoveInChildAddr::blocksList = blocksListHead++[lastNext]++[nullAddr]).
              {
                rewrite HlistEq. rewrite app_comm_cons. rewrite HlistEqBis. rewrite <-app_assoc. reflexivity.
              }
              assert(HlastProps: scentryNext (CPaddr (lastNext+scoffset)) nullAddr s0
                /\ bentryEndAddr lastNext endRange s0).
              {
                revert Heq HisRange HblocksList. apply secToLastElHasNextNullAndLastAddr; trivial.
              }
              destruct HlastProps as (HnextLast & HendLast).
              assert(HlastIn: In lastNext (blockToRemoveInChildAddr::blocksList)).
              {
                rewrite Heq. apply in_or_app. right. apply in_or_app. left. simpl. auto.
              }
              assert(HlastMapped: In lastNext (getMappedBlocks idPDchild s0)).
              {
                destruct (beqAddr blockToRemoveInChildAddr lastNext) eqn:HbeqBlocks.
                - rewrite <-beqAddrTrue in HbeqBlocks. subst lastNext. assumption.
                - rewrite <-beqAddrFalse in *. revert HblocksList. apply removeRecBlocksWereMapped; trivial.
                  + intro Hcontra. subst lastNext. unfold bentryEndAddr in *. unfold nullAddrExists in *.
                    unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
                    destruct v; congruence.
                  + simpl in HlastIn. destruct HlastIn as [Hcontra | Hres]; try(exfalso; congruence). assumption.
              }
              assert(HparentBounds: parentBlocksBoundsIfNoNext s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              assert(HstartLast: exists startLast, bentryStartAddr lastNext startLast s0).
              {
                unfold bentryStartAddr. unfold bentryEndAddr in *.
                destruct (lookup lastNext (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
              }
              destruct HstartLast as [startLast HstartLast].
              assert(HeqTriv: CPaddr (lastNext+scoffset) = CPaddr (lastNext+scoffset)) by reflexivity.
              specialize(HparentBounds idPDchild pdentry lastNext (CPaddr (lastNext+scoffset)) startLast endRange
                HchildIsParts0 HlastMapped HstartLast HendLast HeqTriv HnextLast HbeqPartRoot HlookupChild).
              destruct HparentBounds as [blockParent [startP (HblockPMapped & HstartPBis & HendPBis &
                HlebStarts)]].
              assert(blockParent = blockToRemoveInCurrPartAddr).
              {
                rewrite <-HisParent in *. destruct (beqAddr blockParent blockToRemoveInCurrPartAddr) eqn:HbeqBPs;
                  try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
                assert(HPflagLast: bentryPFlag lastNext true s0).
                {
                  apply IL.mappedBlockIsBE in HlastMapped. destruct HlastMapped as [bentry (Hlookup & Hpres)].
                  unfold bentryPFlag. rewrite Hlookup. auto.
                }
                assert(HwellLast: wellFormedBlock s0) by assumption.
                specialize(HwellLast lastNext startLast endRange HPflagLast HstartLast HendLast).
                destruct HwellLast as (HwellLast & _).
                assert(HstartLInLast: In startLast (getAllPaddrAux [lastNext] s0)).
                {
                  simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup lastNext (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartLast. rewrite <-HendLast.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                assert(HstartLInBP: In startLast (getAllPaddrAux [blockParent] s0)).
                {
                  simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartPBis. rewrite <-HendPBis.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                pose proof (DisjointPaddrInPart currentPart blockParent blockToRemoveInCurrPartAddr startLast s0
                  HnoDupPaddr HcurrIsPDT HblockPMapped HblockPMappeds0 HbeqBPs HstartLInBP) as Hcontra.
                contradict Hcontra. revert HlastIn HlastNext HnextBlocksList.
                apply removedAddrsInSameParent with pdentry currentPart globalIdBlockToRemove; trivial.
                1,2: unfold consistency in *; unfold consistency1 in *;  intuition.
                specialize(Hwell blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HPflagPs0
                  HstartP HendPs0).
                destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
                destruct v; try(simpl; congruence). rewrite <-HstartP. rewrite <-HendPs0. rewrite app_nil_r.
                apply IL.getAllPaddrBlockIncl; lia.
              }
              subst blockParent. unfold bentryEndAddr in *.
              destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HendPs0 in *. assumption.
            }
            subst endRange. rewrite <-HisRange in *.
            revert HnextBlocksList. apply addrInRemovesRangeIsInAccBlock; trivial.
          }
          destruct HaddrMappedList as [blockC (HblockCInList & HAflagC & HstartCInBlockC)].
          assert(blockC <> nullAddr).
          {
            assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *;  intuition).
            intro. subst blockC. unfold isPADDR in *.
            unfold bentryAFlag in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          assert(HblockCMapped: In blockC (getMappedBlocks idPDchild s0)).
          {
            simpl in HblockCInList. destruct HblockCInList; try(subst blockC; assumption).
            revert HblocksList. apply removeRecBlocksWereMapped; trivial;
              unfold consistency in *; unfold consistency1 in *;  intuition.
          }
          rewrite HgetChildrenEq in *; trivial. assert(isPDT child s1).
          { apply IL.childrenArePDT with currentPart; trivial; unfold consistency1 in *; intuition. }
          rewrite HgetMappedPEq in *; trivial. apply IL.mappedAddrIsInMappedBlock in HaddrMappedChild.
          destruct HaddrMappedChild as [blockCBis (HblockCBisMapped & HaddrInCBis)].
          assert(HPflagCs1: bentryPFlag blockC false s1).
          {
            revert HblocksList. apply listsBlocksAreNotPresent; trivial.
          }
          assert(HbeqBlocks: blockC <> blockCBis).
          {
            intro. subst blockCBis. unfold bentryPFlag in *. apply IL.mappedBlockIsBE in HblockCBisMapped.
            destruct HblockCBisMapped as [b (Hlookup & Hpres)]. rewrite Hlookup in *. congruence.
          }
          assert(HblockCBisMappeds0: In blockCBis (getMappedBlocks child s0)).
          {
            destruct (beqAddr idPDchild child) eqn:HbeqChildren.
            - rewrite <-beqAddrTrue in HbeqChildren. subst child.
              revert HblocksList. apply getMappedInclRemoveRec; trivial.
              unfold consistency in *; unfold consistency1 in *; intuition.
            - rewrite <-beqAddrFalse in *. assert(Heq: getMappedBlocks child s1 = getMappedBlocks child s0).
              {
                revert HblocksList. apply getMappedBlocksEqRemoveRec; trivial.
                1,2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
                unfold consistency in *; unfold consistency2 in *; intuition.
                exists blocksList. auto.
              }
              rewrite <-Heq. assumption.
          }
          assert(HaddrInCBiss0: In addr (getAllPaddrAux [blockCBis] s0)).
          {
            assert(~ In blockCBis (blockToRemoveInChildAddr :: blocksList)).
            {
              intro Hcontra. assert(bentryPFlag blockCBis false s1).
              {
                revert HblocksList. apply listsBlocksAreNotPresent; trivial. simpl in *. intro. subst blockCBis.
                assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
                destruct (lookup nullAddr (memory s1) beqAddr); try(simpl in *; congruence).
                destruct v; simpl in *; congruence.
              }
              unfold bentryPFlag in *. apply IL.mappedBlockIsBE in HblockCBisMapped.
              destruct HblockCBisMapped as [b (Hlookup & Hpres)]. rewrite Hlookup in *. congruence.
            }
            assert(Heq: lookup blockCBis (memory s1) beqAddr = lookup blockCBis (memory s0) beqAddr).
            {
              revert HblocksList. apply lookupBEEqRemoveRec; trivial. apply IL.mappedBlockIsBE in HblockCBisMappeds0.
              destruct HblockCBisMappeds0 as [b (Hlookup & _)]. unfold isBE. rewrite Hlookup. trivial.
            }
            simpl in *. rewrite <-Heq. assumption.
          }
          destruct (beqAddr idPDchild child) eqn:HbeqChildren.
          - rewrite <-beqAddrTrue in HbeqChildren. subst child.
            assert(HnoDupPaddr: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            pose proof (DisjointPaddrInPart idPDchild blockC blockCBis addr s0 HnoDupPaddr HchildIsPDT HblockCMapped
              HblockCBisMappeds0 HbeqBlocks HstartCInBlockC) as Hcontra. congruence.
          - rewrite <-beqAddrFalse in *. assert(HchildBisIsChilds0: In child (getChildren currentPart s0)).
            {
              assert(Heq: getChildren currentPart s1 = getChildren currentPart s0).
              {
                revert HblocksList. apply getChildrenEqRemoveRec; trivial; unfold consistency in *;
                  unfold consistency1 in *; intuition.
              }
              rewrite <-Heq. assumption.
            }
            assert(HaddrUsedChild: In addr (getUsedPaddr idPDchild s0)).
            {
              unfold getUsedPaddr. apply in_or_app. right. apply IL.addrInBlockIsMapped with blockC; trivial.
            }
            specialize(HPIs0 currentPart idPDchild child HcurrIsParts0 HchildIsChild HchildBisIsChilds0
              HbeqChildren addr HaddrUsedChild). contradict HPIs0. unfold getUsedPaddr. apply in_or_app. right.
            apply IL.addrInBlockIsMapped with blockCBis; trivial.
        }
        assert(forall child addr, In child (getChildren currentPart s)
          -> In addr (getAllPaddrAux [blockToRemoveInCurrPartAddr] s)
          -> ~In addr (getUsedPaddr child s)).
        {
          intros child addr HchildBisIsChild HaddrInBTRP HaddrUsedChild. rewrite HgetChildrenEq in *; trivial.
          assert(HaddrInBTRPs1: In addr (getAllPaddrAux [blockToRemoveInCurrPartAddr] s1)).
          {
            rewrite Hs in HaddrInBTRP. simpl in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            rewrite HlookupBlockPs1 in *. rewrite IL.beqAddrTrue in *. rewrite HnewB in *. auto.
          }
          assert(isPDT child s1).
          { apply IL.childrenArePDT with currentPart; trivial; unfold consistency1 in *; intuition. }
          unfold getUsedPaddr in *. rewrite HgetConfigEq in *; trivial. rewrite HgetMappedPEq in *; trivial.
          assert(HblockPMappeds1: In blockToRemoveInCurrPartAddr (getMappedBlocks currentPart s1)).
          {
            assert(Heq: getMappedBlocks currentPart s1 = getMappedBlocks currentPart s0).
            {
              revert HblocksList. apply getMappedBlocksEqRemoveRec; auto.
              1,2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
              unfold consistency in *; unfold consistency2 in *; intuition.
              exists blocksList. auto.
            }
            rewrite Heq. assumption.
          }
          assert(Hshareds1: sharedBlockPointsToChild s1) by intuition. rewrite <-HgetPartsEqs1 in *.
          assert(Hsh1Ps1: sh1entryAddr blockToRemoveInCurrPartAddr sh1entryaddr s1).
          { unfold sh1entryAddr in *. rewrite HlookupBPEq in *. rewrite HlookupBlockPs1 in *. assumption. }
          specialize(Hshareds1 currentPart child addr blockToRemoveInCurrPartAddr sh1entryaddr HcurrIsParts0
            HchildBisIsChild HaddrUsedChild HaddrInBTRPs1 HblockPMappeds1 Hsh1Ps1).
          unfold sh1entryAddr in *. rewrite HlookupBlockPs1 in *. subst sh1entryaddr.
          assert(HlookupSh1Eq: lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s1) beqAddr
            = lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s0) beqAddr).
          {
            revert HblocksList. apply lookupSh1EqRemoveRec; trivial.
            - unfold isSHE. unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
              destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s1) beqAddr);
                try(destruct Hshareds1; congruence).
              destruct v; try(destruct Hshareds1; congruence). trivial.
            - unfold consistency in *; unfold consistency1 in *; intuition.
          }
          assert(HaddrInRange: In addr (getAllPaddrBlock globalIdBlockToRemove endBlockToRemove)).
          {
            assert(HstartPs: bentryStartAddr blockToRemoveInCurrPartAddr globalIdBlockToRemove s) by intuition.
            simpl in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartPs in *. rewrite app_nil_r in *.
            rewrite <-HendP in *. assumption.
          }
          specialize(HBTRPsAddsNotShared child addr HchildBisIsChild HaddrInBTRP). unfold getUsedPaddr in *.
          apply in_app_or in HaddrUsedChild. rewrite HgetMappedPEq in *; trivial.
          destruct HaddrUsedChild as [HaddrConfigChild | Hcontra]; try(congruence).
          assert(HconfigEq: getConfigPaddr child s1 = getConfigPaddr child s0).
          {
            revert HblocksList. apply getConfigPaddrEqRemoveRec; trivial.
          }
          rewrite HconfigEq in *. specialize(HremovedAddrsAreNone addr HaddrInRange).
          assert(HaddrMappedList: exists blockC, In blockC (blockToRemoveInChildAddr::blocksList)
            /\ bentryAFlag blockC true s0
            /\ In addr (getAllPaddrAux [blockC] s0)).
          {
            assert(HnextBlockSide: blockAndNextAreSideBySide s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            assert(HnoDup: noDupKSEntriesList s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HnoDupMapped: noDupMappedBlocksList s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hdisjoint: DisjointKSEntries s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HwellSh1: wellFormedFstShadowIfBlockEntry s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HnoDupPaddr: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition). rewrite HgetPartsEqs1 in *.
            pose proof (removedAddrsAreARange s1 s0 idPDchild blockToRemoveInChildAddr statesList blocksList
              HnextBlockSide HnoDup Hnull HnoDupMapped Hdisjoint HwellSh1 Hwell HnoDupPaddr HblockCIsNoNext
              HchildIsParts0 HnoDupList HblocksList) as HisRange.
            destruct HisRange as [startRange [endRange HisRange]].
            assert(startRange = globalIdBlockToRemove).
            {
              specialize(Hwell blockToRemoveInChildAddr globalIdBlockToRemove endC HPflagC HstartC HendC).
              destruct Hwell as (Hwell & _).
              unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl in HisRange.
              destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HstartC in *. rewrite <-HendC in *.
              apply eq_sym in HisRange. revert HisRange. apply getAllPaddrBlockSplit. assumption.
            }
            subst startRange. assert(endRange = endBlockToRemove).
            {
              rewrite beqAddrSym in HbeqNullBlockC. rewrite <-beqAddrFalse in *.
              assert(HlastElem: exists blocksListBis, blocksList = blocksListBis++[nullAddr]).
              { apply lastElNotElDef with blockToRemoveInChildAddr; trivial. }
              destruct HlastElem as [blocksListBis HlistEq].
              assert(HlastElem: exists lastNext blocksListHead,
                blockToRemoveInChildAddr::blocksListBis = blocksListHead++[lastNext]).
              { apply notEmptyListHasLast. }
              destruct HlastElem as [lastNext [blocksListHead HlistEqBis]].
              assert(Heq: blockToRemoveInChildAddr::blocksList = blocksListHead++[lastNext]++[nullAddr]).
              {
                rewrite HlistEq. rewrite app_comm_cons. rewrite HlistEqBis. rewrite <-app_assoc. reflexivity.
              }
              assert(HlastProps: scentryNext (CPaddr (lastNext+scoffset)) nullAddr s0
                /\ bentryEndAddr lastNext endRange s0).
              {
                revert Heq HisRange HblocksList. apply secToLastElHasNextNullAndLastAddr; trivial.
              }
              destruct HlastProps as (HnextLast & HendLast).
              assert(HlastIn: In lastNext (blockToRemoveInChildAddr::blocksList)).
              {
                rewrite Heq. apply in_or_app. right. apply in_or_app. left. simpl. auto.
              }
              assert(HlastMapped: In lastNext (getMappedBlocks idPDchild s0)).
              {
                destruct (beqAddr blockToRemoveInChildAddr lastNext) eqn:HbeqBlocks.
                - rewrite <-beqAddrTrue in HbeqBlocks. subst lastNext. assumption.
                - rewrite <-beqAddrFalse in *. revert HblocksList. apply removeRecBlocksWereMapped; trivial.
                  + intro Hcontra. subst lastNext. unfold bentryEndAddr in *. unfold nullAddrExists in *.
                    unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
                    destruct v; congruence.
                  + simpl in HlastIn. destruct HlastIn as [Hcontra | Hres]; try(exfalso; congruence). assumption.
              }
              assert(HparentBounds: parentBlocksBoundsIfNoNext s0)
                by (unfold consistency in *; unfold consistency2 in *; intuition).
              assert(HstartLast: exists startLast, bentryStartAddr lastNext startLast s0).
              {
                unfold bentryStartAddr. unfold bentryEndAddr in *.
                destruct (lookup lastNext (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
              }
              destruct HstartLast as [startLast HstartLast].
              assert(HeqTriv: CPaddr (lastNext+scoffset) = CPaddr (lastNext+scoffset)) by reflexivity.
              specialize(HparentBounds idPDchild pdentry lastNext (CPaddr (lastNext+scoffset)) startLast endRange
                HchildIsParts0 HlastMapped HstartLast HendLast HeqTriv HnextLast HbeqPartRoot HlookupChild).
              destruct HparentBounds as [blockParent [startP (HblockPMapped & HstartPBis & HendPBis &
                HlebStarts)]].
              assert(blockParent = blockToRemoveInCurrPartAddr).
              {
                rewrite <-HisParent in *. destruct (beqAddr blockParent blockToRemoveInCurrPartAddr) eqn:HbeqBPs;
                  try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
                assert(HPflagLast: bentryPFlag lastNext true s0).
                {
                  apply IL.mappedBlockIsBE in HlastMapped. destruct HlastMapped as [bentry (Hlookup & Hpres)].
                  unfold bentryPFlag. rewrite Hlookup. auto.
                }
                assert(HwellLast: wellFormedBlock s0) by assumption.
                specialize(HwellLast lastNext startLast endRange HPflagLast HstartLast HendLast).
                destruct HwellLast as (HwellLast & _).
                assert(HstartLInLast: In startLast (getAllPaddrAux [lastNext] s0)).
                {
                  simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup lastNext (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartLast. rewrite <-HendLast.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                assert(HstartLInBP: In startLast (getAllPaddrAux [blockParent] s0)).
                {
                  simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                  destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
                  destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartPBis. rewrite <-HendPBis.
                  apply IL.getAllPaddrBlockIncl; lia.
                }
                pose proof (DisjointPaddrInPart currentPart blockParent blockToRemoveInCurrPartAddr startLast s0
                  HnoDupPaddr HcurrIsPDT HblockPMapped HblockPMappeds0 HbeqBPs HstartLInBP) as Hcontra.
                contradict Hcontra. revert HlastIn HlastNext HnextBlocksList.
                apply removedAddrsInSameParent with pdentry currentPart globalIdBlockToRemove; trivial.
                1,2: unfold consistency in *; unfold consistency1 in *;  intuition.
                specialize(Hwell blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HPflagPs0
                  HstartP HendPs0).
                destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
                destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
                destruct v; try(simpl; congruence). rewrite <-HstartP. rewrite <-HendPs0. rewrite app_nil_r.
                apply IL.getAllPaddrBlockIncl; lia.
              }
              subst blockParent. unfold bentryEndAddr in *.
              destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HendPs0 in *. assumption.
            }
            subst endRange. rewrite <-HisRange in *.
            revert HnextBlocksList. apply addrInRemovesRangeIsInAccBlock; trivial.
          }
          destruct HaddrMappedList as [blockC (HblockCInList & HAflagC & HstartCInBlockC)].
          destruct Hshareds1 as [HcontraChild | HcontraFlag].
          - unfold sh1entryPDchild in *. rewrite HlookupSh1Eq in *.
            destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). rewrite <-HPDchildPs0 in *. subst child. rewrite HgetPartsEqs1 in *.
            specialize(HKDIs0 idPDchild idPDchild HchildIsParts0 HchildIsParts0).
            apply Lib.disjointPermut in HKDIs0. specialize(HKDIs0 addr HaddrConfigChild). contradict HKDIs0.
            apply IL.addrInAccessibleBlockIsAccessibleMapped with blockC; trivial. simpl in *.
            destruct HblockCInList; try(subst blockC; assumption).
            revert HblocksList. apply removeRecBlocksWereMapped; trivial.
            2,3,4,5,6: unfold consistency in *; unfold consistency1 in *; intuition.
            assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intro. subst blockC. unfold bentryAFlag in *. unfold isPADDR in *.
            destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          - assert(HnoPDchild: PDflagMeansNoChild s1) by (unfold consistency1 in *; intuition).
            assert(HblockPIsBEs1: isBE blockToRemoveInCurrPartAddr s1)
              by (unfold isBE; rewrite HlookupBlockPs1; trivial).
            specialize(HnoPDchild blockToRemoveInCurrPartAddr HblockPIsBEs1 HcontraFlag).
            unfold sh1entryPDchild in *. rewrite HlookupSh1Eq in *. rewrite <-beqAddrFalse in *.
            destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
        }

        instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
          /\ nullAddrExists s /\ wellFormedFstShadowIfBlockEntry s
          /\ (forall block sh1entryaddrBis,
                blockToRemoveInCurrPartAddr <> block
                -> true = checkChild block s sh1entryaddrBis /\ sh1entryAddr block sh1entryaddrBis s
                -> bentryAFlag block false s /\ bentryPFlag block true s
                    /\ (exists startaddr, bentryStartAddr block startaddr s /\ entryPDT block startaddr s))
          /\ AccessibleNoPDFlag s
          /\ FirstFreeSlotPointerIsBEAndFreeSlot s
          /\ multiplexerIsPDT s /\ sh1InChildLocationIsBE s /\ StructurePointerIsKS s
          /\ NextKSIsKS s /\ NextKSOffsetIsPADDR s /\ currentPartitionInPartitionsList s
          /\ wellFormedShadowCutIfBlockEntry s /\ BlocksRangeFromKernelStartIsBE s
          /\ KernelStructureStartFromBlockEntryAddrIsKS s /\ inclFreeSlotsBlockEntries s
          /\ DisjointKSEntries s /\ noDupPartitionTree s /\ blockInChildHasAtLeastEquivalentBlockInParent s
          /\ isChild s /\ noDupKSEntriesList s /\ noDupMappedBlocksList s /\ wellFormedBlock s
          /\ parentOfPartitionIsPartition s /\ NbFreeSlotsISNbFreeSlotsInList s
          /\ maxNbPrepareIsMaxNbKernels s /\ sharedBlockPointsToChild s /\ NoDupInFreeSlotsList s
          /\ DisjointFreeSlotsLists s /\ freeSlotsListIsFreeSlot s /\ isParent s
          /\ blockAndNextAreSideBySide s /\ parentBlocksBoundsIfNoNext s /\ nextImpliesBlockWasCut s
          /\ blocksAddressesTypes s /\ notPDTIfNotPDflag s /\ nextKernAddrIsInSameBlock s
          /\ blockBelongsToAPart s /\ PDflagMeansNoChild s /\ nbPrepareIsNbKern s /\ pdchildIsPDT s
          /\ noDupMappedPaddrList s /\ accessibleParentPaddrIsAccessibleIntoChild s /\ noDupListOfKerns s
          /\ partitionTreeIsTree s /\ kernelEntriesAreValid s
          /\ nextKernelIsValid s /\ kernelsAreNotAccessible s /\ MPUsizeIsBelowMax s /\ originIsParentBlocksStart s
          /\ noChildImpliesAddressesNotShared s /\ childsBlocksPropsInParent s
          /\ adressesRangePreservedIfOriginAndNextOk s
          /\ bentryEndAddr blockToRemoveInCurrPartAddr endBlockToRemove s
          /\ (forall part block sh1entryaddr blockChild idchild,
                blockToRemoveInCurrPartAddr <> block
                -> In part (getPartitions multiplexer s)
                -> In block (getMappedBlocks part s)
                -> sh1entryAddr block sh1entryaddr s
                -> sh1entryPDchild sh1entryaddr idchild s
                -> sh1entryInChildLocation sh1entryaddr blockChild s
                -> idchild <> nullAddr
                -> blockChild <> nullAddr
                -> In blockChild (getMappedBlocks idchild s) /\
                    (forall startaddr,
                      bentryStartAddr block startaddr s -> bentryStartAddr blockChild startaddr s))
          /\ (forall addr, In addr (getAllPaddrBlock globalIdBlockToRemove endBlockToRemove)
                -> lookup addr (memory s) beqAddr = None)
          /\ (forall child addr, In child (getChildren currentPart s)
                -> In addr (getAllPaddrAux [blockToRemoveInCurrPartAddr] s) -> ~ In addr (getMappedPaddr child s))
          /\ (forall child addr, In child (getChildren currentPart s)
                -> In addr (getAllPaddrAux [blockToRemoveInCurrPartAddr] s) -> ~ In addr (getUsedPaddr child s))
          /\ bentryStartAddr blockToRemoveInCurrPartAddr globalIdBlockToRemove s
          /\ sh1entryPDflag (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) false s
          /\ (exists sh1entryaddr, sh1entryAddr blockToRemoveInCurrPartAddr sh1entryaddr s
              /\ sh1entryPDchild sh1entryaddr idPDchild s)
          /\ bentryPFlag blockToRemoveInCurrPartAddr true s
          /\ bentryAFlag blockToRemoveInCurrPartAddr true s
          /\ ~ isFreeSlot blockToRemoveInCurrPartAddr s
          /\ In blockToRemoveInCurrPartAddr (getMappedBlocks currentPart s)
          /\ In idPDchild (getChildren currentPart s)
          /\ In currentPart (getPartitions multiplexer s)
          /\ In idPDchild (getPartitions multiplexer s)
          /\ blockToRemoveInCurrPartAddr <> nullAddr
          /\ currentPart <> idPDchild
          /\ idPDchild <> constantRootPartM
          /\ nullAddr <> idPDchild
          /\ nullAddr <> blockToRemoveInChildAddr).
        rewrite <-beqAddrFalse in *. intuition.
        - exists sh1entryaddr. auto.
        - unfold isBE. unfold sh1entryAddr in *.
          destruct (lookup blockToRemoveInCurrPartAddr (memory s) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
      }
      intro. eapply bindRev.
      { (** writeAccessibleRec *)
        eapply weaken. apply writeAccessibleRec. intros s Hprops. simpl.
        destruct Hprops as [s0 [sh1entry1 [sh1entry0 ((HPIs0 & HKDIs0 & HVSs0 & Hnulls0 & HwellSh1s0 &
          HPDTIfPDFlagPartials0 & HaccNoPDfPartials0 & HfirstIsFrees0 & HmultIsPDTs0 & HchildLocIsBEs0 & Hstructs0 &
          HnextKSs0 & HnextPADDRs0 & HcurrPIsParts0 & HwellSces0 & HkernOffIsKSs0 & HkernStartIsKSs0 & HinclFreeKSEs0
          & Hdisjoints0 & HnoDupTrees0 & HblockEquivParents0 & HisChilds0 & HnoDups0 & HnoDupMappeds0 & Hwells0 &
          HparentOfParts0 & HnbFrees0 & HmaxNbPreps0 & Hshareds0 & HnoDupFrees0 & HdisjointFrees0 & HfreeIsFrees0 &
          HisParents0 & HnextBlockSides0 & HblockPBoundss0 & HnextCuts0 & HaddrTypes0 & HnotPDTs0 & HkernIsStart &
          HblockInParts0 & HnoChildIfNoPDs0 & HnbPreps0 & HpdchildIsPDTs0 & HnoDupPaddrs0 & Haccesss0 & HnoDupListKSs0
          & Htrees0 & HkernIdxIsBEs0 & HnextKSIsValids0 & HkernNotAccs0 & HMPUsizes0 & HoriginIsStarts0 & HnoChilds0 &
          HchildBlocksPropss0 & Hranges0 & HendBTRs0 & HchildLocMappedInChildPartialss0 & HremovedAddrsAreNones0 &
          HBTRPsAddsNotShareds0 & HBTRPsAddsNotUseds0 & HstartBTRs0 & HPDflagBTR &
          [sh1entryaddr (Hsh1BTRs0 & HPDchildBTRs0)] & HPflagBTRs0 & HAflagBTRs0 & HBTRNotFrees0 & HBTRMappeds0 &
          HidchildIsChilds0 & HcurrIsParts0 & HidchildIsParts0 & HbeqBTRNull & HbeqCurrChild & HbeqChildRoot &
          HbeqNullChild & HbeqNullBTR) & Hs & HwellSh1 & HkernStartIsKS & HkernIdxIsBE & Hnull)]]].

        (*assert(HchildIsPDT: isPDT idPDchild s0).
        { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }*)
        (*assert(HcurrIsPDT: isPDT currentPart s0).
        { apply IL.partitionsArePDT; trivial. }*)

        (*assert(HblockCIsNoNext: forall part block scnext,
          In part (getPartitions multiplexer s0)
          -> In block (getMappedBlocks part s0)
          -> scentryNext (CPaddr (block + scoffset)) scnext s0
          -> scnext <> nullAddr -> blockToRemoveInChildAddr <> scnext).
        {
          destruct HnewB as [l HnewB].
          intros part block scnext HpartIsPart HblockMapped Hnext HbeqNextNull HbeqBlockCNext. subst scnext.
          assert(HnextBlockSide: blockAndNextAreSideBySide s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(Hbounds: (exists startaddr endaddr, bentryStartAddr block startaddr s0
            /\ bentryEndAddr block endaddr s0) /\ bentryPFlag block true s0).
          {
            apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
            unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryPFlag. rewrite Hlookup. split; auto.
            exists (startAddr (blockrange bentry)). exists (endAddr (blockrange bentry)). auto.
          }
          destruct Hbounds as ([startaddr [endaddr (Hstart & Hend)]] & HPflag).
          assert(HeqTriv: CPaddr (block+scoffset) = CPaddr (block+scoffset)) by reflexivity.
          specialize(HnextBlockSide part block (CPaddr (block+scoffset)) blockToRemoveInChildAddr endaddr
            HpartIsPart HblockMapped Hend HeqTriv HbeqNextNull Hnext).
          destruct HnextBlockSide as (HstartCBis & HblockCMappedBis). assert(part = idPDchild).
          {
            destruct (beqAddr part idPDchild) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
            rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HblockCMappeds0.
            assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            apply InFilterPresentInList in HblockCMappedBis. assert(HpartIsPDT: isPDT part s0).
            { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
            specialize(Hdisjoint part idPDchild HpartIsPDT HchildIsPDT HbeqParts).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint blockToRemoveInChildAddr HblockCMappedBis). congruence.
          }
          subst part. assert(HlocProps: childLocMappedInChild s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition). rewrite beqAddrSym in *.
          rewrite <-beqAddrFalse in *.
          specialize(HlocProps currentPart blockToRemoveInCurrPartAddr sh1entryaddr blockToRemoveInChildAddr
            idPDchild HcurrIsParts0 HblockPMappeds0 Hsh1Ps0 HPDchildPs0 HchildLocPs0 HbeqNullChild HbeqNullBlockC).
          destruct HlocProps as (_ & HstartIsOrigin). specialize(HstartIsOrigin globalIdBlockToRemove HstartP).
          assert(globalIdBlockToRemove = endaddr).
          {
            unfold bentryStartAddr in *.
            destruct (lookup blockToRemoveInChildAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartCBis in *. assumption.
          }
          subst globalIdBlockToRemove.
          assert(HblockCut: nextImpliesBlockWasCut s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(HblockCut idPDchild pdentry block (CPaddr (block+scoffset)) blockToRemoveInChildAddr endaddr
            HpartIsPart HlookupChild HblockMapped Hend HeqTriv HbeqNextNull Hnext HbeqPartRoot).
          destruct HblockCut as [blockParent [endParent (HblockPBisMapped & HendPBis & HltEnds & Hincl)]].
          assert(HPflagP: bentryPFlag blockToRemoveInCurrPartAddr true s0).
          {
            apply IL.mappedBlockIsBE in HblockPMappeds0. destruct HblockPMappeds0 as [bentry (Hlookup & Hpres)].
            unfold bentryPFlag. rewrite Hlookup. auto.
          }
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HendPs0: bentryEndAddr blockToRemoveInCurrPartAddr endBlockToRemove s0).
          {
            assert(HendPs0: bentryEndAddr blockToRemoveInCurrPartAddr endBlockToRemove s1).
            {
              unfold bentryEndAddr in *. rewrite Hs in HendP. simpl in *. rewrite IL.beqAddrTrue in *.
              rewrite HlookupBlockPs1. rewrite HnewB in HendP. auto.
            }
            pose proof (lookupBEEqRemoveRec blockToRemoveInCurrPartAddr s1 s0 idPDchild blockToRemoveInChildAddr
              statesList blocksList HblockPIsBEs0 HblockPNotIn HblocksList) as HlookupsEq.
            unfold bentryEndAddr. rewrite <-HlookupsEq. assumption.
          }
          specialize(Hwell blockToRemoveInCurrPartAddr endaddr endBlockToRemove HPflagP HstartP HendPs0).
          destruct Hwell as (HwellP & _).
          rewrite <-HisParent in *. assert(HendInBP: In endaddr (getAllPaddrAux [blockToRemoveInCurrPartAddr] s0)).
          {
            simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartP. rewrite <-HendPs0.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          specialize(Hwell block startaddr endaddr HPflag Hstart Hend). destruct Hwell as (Hwell & _).
          assert(HstartInBlock: In startaddr (getAllPaddrAux [block] s0)).
          {
            unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            simpl. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          specialize(Hincl startaddr HstartInBlock). assert(blockParent = blockToRemoveInCurrPartAddr).
          {
            assert(HnoDupPaddr: noDupMappedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
            destruct (beqAddr blockParent blockToRemoveInCurrPartAddr) eqn:HbeqBlocks;
              try(rewrite beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
            assert(HendInBPBis: In endaddr (getAllPaddrAux [blockParent] s0)).
            {
              assert(HPflagPBis: bentryPFlag blockParent true s0).
              {
                apply IL.mappedBlockIsBE in HblockPBisMapped. destruct HblockPBisMapped as [bentry (Hlookup & Hpres)].
                unfold bentryPFlag. rewrite Hlookup. auto.
              }
              assert(HwellPBis: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
              assert(HstartPBis: exists startPBis, bentryStartAddr blockParent startPBis s0).
              {
                unfold bentryStartAddr. unfold bentryPFlag in *.
                destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). exists (startAddr (blockrange b)). reflexivity.
              }
              destruct HstartPBis as [startPBis HstartPBis].
              specialize(HwellPBis blockParent startPBis endParent HPflagPBis HstartPBis HendPBis).
              destruct HwellPBis as (HwellPBis & _). unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
              simpl in *. destruct (lookup blockParent (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r in *. rewrite <-HstartPBis in *.
              rewrite <-HendPBis in *. apply IL.getAllPaddrBlockInclRev in Hincl. destruct Hincl as (HlebStarts & _).
              apply IL.getAllPaddrBlockIncl; lia.
            }
            pose proof (DisjointPaddrInPart currentPart blockParent blockToRemoveInCurrPartAddr endaddr s0
              HnoDupPaddr HcurrIsPDT HblockPBisMapped HblockPMappeds0 HbeqBlocks HendInBPBis). congruence.
          }
          subst blockParent. simpl in Hincl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). rewrite app_nil_r in Hincl. rewrite <-HstartP in *. rewrite <-HendPBis in *.
          apply IL.getAllPaddrBlockInclRev in Hincl. destruct Hincl as (Hcontra & _). lia.
        }*)
        assert(HlookupSh1: exists sh1entry,
          lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s0) beqAddr = Some(SHE sh1entry)
          /\ PDflag sh1entry = false).
        {
          unfold sh1entryPDflag in *. destruct (lookup (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (memory s0)
            beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
          exists s1. split; auto.
        }
        destruct HlookupSh1 as [sh1entry (HlookupBTRSh1 & HPDflag)].

        assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
        {
          rewrite Hs. apply getPartitionsEqSHEFalse with (sh1entry:=sh1entry); trivial. auto.
        }
        set(s1 := {|
                    currentPartition := currentPartition s0;
                    memory := add (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (SHE sh1entry0) (memory s0) beqAddr
                  |}).
        set(s2 := {|
                    currentPartition := currentPartition s1;
                    memory := add (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (SHE sh1entry1) (memory s1) beqAddr
                  |}).
        set(s3 := {|
                    currentPartition := currentPartition s2;
                    memory := add (CPaddr (blockToRemoveInCurrPartAddr+sh1offset))
                      (SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
                      (memory s2) beqAddr
                  |}).
        assert(HsEq: s = s3) by (rewrite Hs; reflexivity).
        assert(HgetKSEq: forall part, isPDT part s0 -> getKSEntries part s = getKSEntries part s0).
        {
          intros part HpartIsPDT. rewrite HsEq. unfold isPDT in *.
          destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          assert(Heqs1: getKSEntries part s1 = getKSEntries part s0).
          { apply IL.getKSEntriesEqSHE with p; trivial. unfold isSHE. rewrite HlookupBTRSh1. trivial. }
          assert(lookup part (memory s1) beqAddr = Some (PDT p)).
          {
            simpl. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          assert(Heqs2: getKSEntries part s2 = getKSEntries part s0).
          {
            rewrite <-Heqs1. apply IL.getKSEntriesEqSHE with p; trivial. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
            trivial.
          }
          assert(lookup part (memory s2) beqAddr = Some (PDT p)).
          {
            cbn -[s1]. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          rewrite <-Heqs2. apply IL.getKSEntriesEqSHE with p; trivial. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
          trivial.
        }
        assert(HgetMappedBEq: forall part, isPDT part s0 -> getMappedBlocks part s = getMappedBlocks part s0).
        {
          intros part HpartIsPDT. rewrite HsEq.
          assert(Heqs1: getMappedBlocks part s1 = getMappedBlocks part s0).
          { apply IL.getMappedBlocksEqSHE; trivial. unfold isSHE. rewrite HlookupBTRSh1. trivial. }
          assert(isPDT part s1).
          {
            unfold isPDT in *. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          assert(Heqs2: getMappedBlocks part s2 = getMappedBlocks part s0).
          {
            rewrite <-Heqs1. apply IL.getMappedBlocksEqSHE; trivial. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
            trivial.
          }
          assert(isPDT part s2).
          {
            unfold isPDT in *. cbn -[s1].
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          rewrite <-Heqs2. apply IL.getMappedBlocksEqSHE; trivial. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
          trivial.
        }
        assert(HgetMappedPEq: forall part, isPDT part s0 -> getMappedPaddr part s = getMappedPaddr part s0).
        {
          intros part HpartIsPDT. rewrite HsEq.
          assert(Heqs1: getMappedPaddr part s1 = getMappedPaddr part s0).
          { apply IL.getMappedPaddrEqSHE; trivial. unfold isSHE. rewrite HlookupBTRSh1. trivial. }
          assert(isPDT part s1).
          {
            unfold isPDT in *. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          assert(Heqs2: getMappedPaddr part s2 = getMappedPaddr part s0).
          {
            rewrite <-Heqs1. apply IL.getMappedPaddrEqSHE; trivial. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
            trivial.
          }
          assert(isPDT part s2).
          {
            unfold isPDT in *. cbn -[s1].
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          rewrite <-Heqs2. apply IL.getMappedPaddrEqSHE; trivial. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
          trivial.
        }
        assert(HgetChildrenEq: forall part, isPDT part s0 -> getChildren part s = getChildren part s0).
        {
          intros part HpartIsPDT. rewrite Hs. apply getChildrenEqSHEFalse with sh1entry; trivial. auto.
        }
        assert(HgetConfigEq: forall part, isPDT part s0 -> getConfigPaddr part s = getConfigPaddr part s0).
        {
          intros part HpartIsPDT. rewrite HsEq.
          assert(Heqs1: getConfigPaddr part s1 = getConfigPaddr part s0).
          { apply IL.getConfigPaddrEqSHE; trivial. unfold isSHE. rewrite HlookupBTRSh1. trivial. }
          assert(isPDT part s1).
          {
            unfold isPDT in *. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          assert(Heqs2: getConfigPaddr part s2 = getConfigPaddr part s0).
          {
            rewrite <-Heqs1. apply IL.getConfigPaddrEqSHE; trivial. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
            trivial.
          }
          assert(isPDT part s2).
          {
            unfold isPDT in *. cbn -[s1].
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          rewrite <-Heqs2. apply IL.getConfigPaddrEqSHE; trivial. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
          trivial.
        }
        assert(HgetAccMappedBEq: forall part, isPDT part s0
          -> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s0).
        {
          intros part HpartIsPDT. rewrite HsEq.
          assert(Heqs1: getAccessibleMappedBlocks part s1 = getAccessibleMappedBlocks part s0).
          { apply IL.getAccessibleMappedBlocksEqSHE; trivial. unfold isSHE. rewrite HlookupBTRSh1. trivial. }
          assert(isPDT part s1).
          {
            unfold isPDT in *. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          assert(Heqs2: getAccessibleMappedBlocks part s2 = getAccessibleMappedBlocks part s0).
          {
            rewrite <-Heqs1. apply IL.getAccessibleMappedBlocksEqSHE; trivial. unfold isSHE. simpl.
            rewrite IL.beqAddrTrue. trivial.
          }
          assert(isPDT part s2).
          {
            unfold isPDT in *. cbn -[s1].
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          rewrite <-Heqs2. apply IL.getAccessibleMappedBlocksEqSHE; trivial. unfold isSHE. simpl.
          rewrite IL.beqAddrTrue. trivial.
        }
        assert(HgetAccMappedPEq: forall part, isPDT part s0
          -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s0).
        {
          intros part HpartIsPDT. rewrite HsEq.
          assert(Heqs1: getAccessibleMappedPaddr part s1 = getAccessibleMappedPaddr part s0).
          { apply IL.getAccessibleMappedPaddrEqSHE; trivial. unfold isSHE. rewrite HlookupBTRSh1. trivial. }
          assert(isPDT part s1).
          {
            unfold isPDT in *. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          assert(Heqs2: getAccessibleMappedPaddr part s2 = getAccessibleMappedPaddr part s0).
          {
            rewrite <-Heqs1. apply IL.getAccessibleMappedPaddrEqSHE; trivial. unfold isSHE. simpl.
            rewrite IL.beqAddrTrue. trivial.
          }
          assert(isPDT part s2).
          {
            unfold isPDT in *. cbn -[s1].
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:Hbeq.
            {
              rewrite <-beqAddrTrue in Hbeq. subst part. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          rewrite <-Heqs2. apply IL.getAccessibleMappedPaddrEqSHE; trivial. unfold isSHE. simpl.
          rewrite IL.beqAddrTrue. trivial.
        }

        assert(HchildLocMappedInChild: childLocMappedInChild s).
        {
          intros part block sh1entryaddrB blockChild idchild HpartIsPart HblockMapped Hsh1 HPDchild
            HchildLoc HbeqChildNull HbeqBlockCNull. assert(HpartIsPDT: isPDT part s).
          {
            unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
            destruct (lookup part (memory s) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *. rewrite IL.beqAddrTrue in *.
          destruct ( beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite HgetPartsEq in *. rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryAddr in *.
          rewrite Hs in Hsh1. unfold bentryStartAddr at 1. rewrite Hs. simpl in *. rewrite <-Hs.
          rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryInChildLocation in *.
          unfold sh1entryPDchild in *. rewrite Hs in HPDchild. rewrite Hs in HchildLoc. simpl in *.
          rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) sh1entryaddrB) eqn:HbeqSh1s.
          { simpl in *. exfalso; congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(HchildLocs0: sh1entryInChildLocation sh1entryaddrB blockChild s0).
          {
            unfold sh1entryInChildLocation. destruct (lookup sh1entryaddrB (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial.
            intro HbeqBCNull. specialize(HlocIsBE HbeqBCNull). unfold isBE in *. simpl in *.
            rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) blockChild) eqn:HbeqSh1BC;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          }
          assert(HbeqBlocks: blockToRemoveInCurrPartAddr <> block).
          {
            intro. subst block. destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          specialize(HchildLocMappedInChildPartialss0 part block sh1entryaddrB blockChild idchild HbeqBlocks
            HpartIsPart HblockMapped Hsh1 HPDchild HchildLocs0 HbeqChildNull HbeqBlockCNull).
          destruct HchildLocMappedInChildPartialss0 as (HBCMapped & HstartsEq).
          assert(isPDT idchild s0).
          {
            unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
            destruct (lookup idchild (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          rewrite HgetMappedBEq; trivial. split; trivial. intros startaddr Hstart.
          specialize(HstartsEq startaddr Hstart). unfold bentryStartAddr in *. rewrite Hs. simpl.
          rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) blockChild) eqn:HbeqSh1BC.
          {
            rewrite <-beqAddrTrue in HbeqSh1BC. rewrite HbeqSh1BC in *. rewrite HlookupBTRSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        }

        assert(PDTIfPDFlag s).
        { (* BEGIN PDTIfPDFlag s *)
          intros block sh1entryaddrBis HcheckChild. unfold checkChild in *. unfold sh1entryAddr in *.
          assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
          {
            destruct HcheckChild as (_ & Hsh1). rewrite Hs. rewrite Hs in Hsh1. simpl in *.
            rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          unfold bentryPFlag. unfold bentryAFlag. unfold bentryStartAddr. unfold entryPDT.
          rewrite HlookupBlockEq in *.
          assert(HcheckChilds0: CPaddr (blockToRemoveInCurrPartAddr + sh1offset) <> sh1entryaddrBis
            /\ true = checkChild block s0 sh1entryaddrBis /\ sh1entryAddr block sh1entryaddrBis s0).
          {
            destruct HcheckChild as (HcheckChild & Hsh1). unfold checkChild. unfold sh1entryAddr.
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite Hs in HcheckChild. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) sh1entryaddrBis) eqn:HbeqSh1s.
            { simpl in *; exfalso; congruence. }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
          }
          destruct HcheckChilds0 as (HbeqSh1s & HcheckChilds0).
          assert(HbeqBlocks: blockToRemoveInCurrPartAddr <> block).
          {
            intro. subst block. destruct HcheckChild as (_ & Hsh1).
            destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          specialize(HPDTIfPDFlagPartials0 block sh1entryaddrBis HbeqBlocks HcheckChilds0).
          destruct HPDTIfPDFlagPartials0 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial.
          split; trivial. exists startaddr. split; trivial. unfold entryPDT in *.
          destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          rewrite Hs. simpl. rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (startAddr (blockrange b)))
            eqn:HbeqSh1Start.
          {
            rewrite <-beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *. rewrite HlookupBTRSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END PDTIfPDFlag *)
        }

        assert(HPDTEq: forall part, isPDT part s -> isPDT part s0).
        {
          intros part HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
          rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) part) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        }

        assert(partitionsIsolation s).
        { (* BEGIN partitionsIsolation s *)
          intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
          rewrite HgetPartsEq in *. assert(HparentIsPDT: isPDT pdparent s).
          {
            unfold getChildren in *. unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
            destruct (lookup pdparent (memory s) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          apply HPDTEq in HparentIsPDT.
          assert(Hchild1IsPDT: isPDT child1 s).
          { apply IL.childrenArePDT with pdparent; trivial. }
          assert(Hchild2IsPDT: isPDT child2 s).
          { apply IL.childrenArePDT with pdparent; trivial. }
          apply HPDTEq in Hchild1IsPDT. apply HPDTEq in Hchild2IsPDT. rewrite HgetChildrenEq in *; trivial.
          specialize(HPIs0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
          unfold getUsedPaddr. rewrite HgetConfigEq; trivial. rewrite HgetMappedPEq; trivial.
          rewrite HgetMappedPEq; trivial. rewrite HgetConfigEq; trivial.
          (* END partitionsIsolation *)
        }

        split; trivial.
        assert(multiplexerIsPDT s).
        { (* BEGIN multiplexerIsPDT s *)
          unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) multiplexer) eqn:HbeqSh1Mult.
          {
            rewrite <-beqAddrTrue in HbeqSh1Mult. rewrite HbeqSh1Mult in *. rewrite HlookupBTRSh1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END multiplexerIsPDT *)
        }

        split.
        { (* BEGIN kernelDataIsolation s *)
          intros part1 part2 Hpart1IsPart Hpart2IsPart.
          assert(Hpart1IsPDT: isPDT part1 s) by (apply IL.partitionsArePDT; trivial).
          assert(Hpart2IsPDT: isPDT part2 s) by (apply IL.partitionsArePDT; trivial). rewrite HgetPartsEq in *.
          apply HPDTEq in Hpart1IsPDT. apply HPDTEq in Hpart2IsPDT. rewrite HgetConfigEq; trivial.
          specialize(HKDIs0 part1 part2 Hpart1IsPart Hpart2IsPart). rewrite HgetAccMappedPEq; trivial.
          (* END kernelDataIsolation *)
        }

        split.
        { (* BEGIN verticalSharing s *)
          intros pdparent child HparentIsPart HchildBisIsChild.
          assert(HparentIsPDT: isPDT pdparent s) by (apply IL.partitionsArePDT; trivial). rewrite HgetPartsEq in *.
          assert(HchildIsPDT: isPDT child s) by (apply IL.childrenArePDT with pdparent; trivial).
          apply HPDTEq in HparentIsPDT. apply HPDTEq in HchildIsPDT.
          rewrite HgetChildrenEq in *; trivial. rewrite HgetMappedPEq; trivial. unfold getUsedPaddr.
          specialize(HVSs0 pdparent child HparentIsPart HchildBisIsChild).
          rewrite HgetConfigEq; trivial. rewrite HgetMappedPEq; trivial.
          (* END verticalSharing *)
        }

        assert(HgetFreeEq: forall part, getFreeSlotsList part s = getFreeSlotsList part s0).
        {
          intro part. unfold getFreeSlotsList. rewrite Hs at 1. simpl.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) part) eqn:HbeqSh1Part.
          {
            rewrite <-beqAddrTrue in HbeqSh1Part. subst part. rewrite HlookupBTRSh1. reflexivity.
          }
          rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
          destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
          assert(firstfreeslot p <> CPaddr (blockToRemoveInCurrPartAddr + sh1offset)).
          {
            rewrite <-beqAddrFalse in *. specialize(HfirstIsFrees0 part p HlookupPart HbeqFirstNull).
            destruct HfirstIsFrees0 as (HfirstIsBE & _). unfold isBE in *. intro Hcontra. rewrite Hcontra in *.
            rewrite HlookupBTRSh1 in *. congruence.
          }
          assert(Heqs1: getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s1 (nbfreeslots p)
            = getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s0 (nbfreeslots p)).
          {
            apply IL.getFreeSlotsListRecEqSHE; trivial; unfold isBE; unfold isPADDR; rewrite HlookupBTRSh1; auto.
          }
          assert(Heqs2: getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s2 (nbfreeslots p)
            = getFreeSlotsListRec (maxIdx+1) (firstfreeslot p) s0 (nbfreeslots p)).
          {
            rewrite <-Heqs1. apply IL.getFreeSlotsListRecEqSHE; trivial; unfold isBE; unfold isPADDR; simpl;
              rewrite IL.beqAddrTrue; auto.
          }
          rewrite <-Heqs2. rewrite HsEq. apply IL.getFreeSlotsListRecEqSHE; trivial; unfold isBE; unfold isPADDR;
            simpl; rewrite IL.beqAddrTrue; auto.
        }
        assert(HkernListEq: forall part kernList, isListOfKernels kernList part s
          -> isListOfKernels kernList part s0).
        {
          rewrite HsEq. intros part kernList HkernList. assert(HkernLists2: isListOfKernels kernList part s2).
          { revert HkernList. apply IL.isListOfKernelsEqSHE. }
          assert(HkernLists1: isListOfKernels kernList part s1).
          { revert HkernLists2. apply IL.isListOfKernelsEqSHE. }
          revert HkernLists1. apply IL.isListOfKernelsEqSHE.
        }
        assert(HparentsListEq: forall parentsList part, isPDT part s0
          -> isParentsList s parentsList part
          -> isParentsList s0 parentsList part).
        {
          rewrite Hs. intros parentsList part HpartIsPDT. apply isParentsListEqSHERevCompl; trivial.
          - apply isPDTLookupEq. assumption.
          - unfold isSHE. rewrite HlookupBTRSh1. trivial.
        }
        assert(CPaddr (blockToRemoveInCurrPartAddr + sh1offset) <> nullAddr).
        {
          unfold nullAddrExists in *. unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *.
          rewrite HlookupBTRSh1 in *. congruence.
        }
        assert(HstartBTRInRange: In globalIdBlockToRemove (getAllPaddrBlock globalIdBlockToRemove endBlockToRemove)).
        {
          specialize(Hwells0 blockToRemoveInCurrPartAddr globalIdBlockToRemove endBlockToRemove HPflagBTRs0
            HstartBTRs0 HendBTRs0). apply IL.getAllPaddrBlockIncl; lia.
        }
        assert(HcompleteKernEq: forall kernel, completeListOfKernels kernel s = completeListOfKernels kernel s0).
        {
          intro kernel. rewrite HsEq.
          assert(Heqs1: completeListOfKernels kernel s1 = completeListOfKernels kernel s0).
          {
            apply completeListOfKernelsEqSHE. unfold isSHE. rewrite HlookupBTRSh1. trivial.
          }
          assert(Heqs2: completeListOfKernels kernel s2 = completeListOfKernels kernel s0).
          {
            rewrite <-Heqs1. apply completeListOfKernelsEqSHE. unfold isSHE. simpl. rewrite IL.beqAddrTrue.
            trivial.
          }
          rewrite <-Heqs2. apply completeListOfKernelsEqSHE. unfold isSHE. cbn -[s1]. rewrite IL.beqAddrTrue.
          trivial.
        }

        assert(consistency1 s).
        {
          assert(AccessibleNoPDFlag s).
          { (* BEGIN AccessibleNoPDFlag s *)
            intros block sh1entryaddrBis HblockIsBE Hsh1 HAflag. unfold bentryAFlag in *. unfold sh1entryAddr in *.
            unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs in Hsh1. rewrite Hs in HAflag. simpl in *.
            rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDflag. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) sh1entryaddrBis) eqn:HbeqSh1s.
            - reflexivity.
            - rewrite <-beqAddrFalse in *. rewrite IL.beqAddrTrue.
              specialize(HaccNoPDfPartials0 block sh1entryaddrBis HblockIsBE Hsh1 HAflag).
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            (* END AccessibleNoPDFlag *)
          }

          assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
          { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
            intros partition pdentryBis HlookupPart HbeqFirstNull. rewrite Hs in HlookupPart. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
              try(exfalso; congruence). rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HfirstIsFrees0 partition pdentryBis HlookupPart HbeqFirstNull).
            destruct HfirstIsFrees0 as (HfirstIsBE & HfirstIsFree). unfold isBE. unfold isFreeSlot in *. rewrite Hs.
            simpl. rewrite IL.beqAddrTrue.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (firstfreeslot pdentryBis))
              eqn:HbeqSh1First.
            {
              exfalso. rewrite <-beqAddrTrue in HbeqSh1First. rewrite <-HbeqSh1First in *. rewrite HlookupBTRSh1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial.
            destruct (lookup (firstfreeslot pdentryBis) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset))
              (CPaddr (firstfreeslot pdentryBis+sh1offset))) eqn:HbeqSh1s.
            - rewrite <-beqAddrTrue in HbeqSh1s. rewrite <-HbeqSh1s in *. rewrite HlookupBTRSh1 in *.
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset))
                (CPaddr (firstfreeslot pdentryBis+scoffset))) eqn:HbeqSh1Sce.
              {
                rewrite <-beqAddrTrue in HbeqSh1Sce. rewrite <-HbeqSh1Sce in *. rewrite HlookupBTRSh1 in *.
                congruence.
              }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              destruct (lookup (CPaddr (firstfreeslot pdentryBis+scoffset)) (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence). intuition.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              destruct (lookup (CPaddr (firstfreeslot pdentryBis+sh1offset)) (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence).
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset))
                (CPaddr (firstfreeslot pdentryBis+scoffset))) eqn:HbeqSh1Sce.
              {
                rewrite <-beqAddrTrue in HbeqSh1Sce. rewrite <-HbeqSh1Sce in *. rewrite HlookupBTRSh1 in *.
                congruence.
              }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
          }

          assert(currentPartitionInPartitionsList s).
          { (* BEGIN currentPartitionInPartitionsList s *)
            unfold currentPartitionInPartitionsList. rewrite HgetPartsEq. rewrite Hs. simpl. assumption.
            (* END currentPartitionInPartitionsList *)
          }

          assert(wellFormedShadowCutIfBlockEntry s).
          { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
            intros block HblockIsBE. unfold isBE in *. rewrite Hs in HblockIsBE. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence). rewrite IL.beqAddrTrue in *.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HwellSces0 block HblockIsBE). destruct HwellSces0 as [scentryaddr (HsceIsSCE & Hsce)].
            exists scentryaddr. split; trivial. unfold isSCE in *. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh1Sce.
            {
              rewrite <-beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. rewrite HlookupBTRSh1 in *.
              congruence.
            }
            rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END wellFormedShadowCutIfBlockEntry *)
          }

          assert(sh1InChildLocationIsBE s).
          { (* BEGIN sh1InChildLocationIsBE s *)
            intros sh1entryaddrBis sh1entryBis HlookupSh1 HbeqLocNull. rewrite Hs in HlookupSh1. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) sh1entryaddrBis) eqn:HbeqSh1s.
            {
              injection HlookupSh1 as Hsh1entriesEq. subst sh1entryBis. simpl in *. exfalso; congruence.
            }
            rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HchildLocIsBEs0 sh1entryaddrBis sh1entryBis HlookupSh1 HbeqLocNull). unfold isBE in *.
            rewrite Hs. simpl. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset))
              (inChildLocation sh1entryBis)) eqn:HbeqSh1Loc.
            {
              rewrite <-beqAddrTrue in HbeqSh1Loc. rewrite HbeqSh1Loc in *. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END sh1InChildLocationIsBE *)
          }

          assert(StructurePointerIsKS s).
          { (* BEGIN StructurePointerIsKS s *)
            intros partition pdentryBis HlookupPart HbeqStructNull. rewrite Hs in HlookupPart. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
              try(exfalso; congruence). rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(Hstructs0 partition pdentryBis HlookupPart HbeqStructNull). unfold isKS in *. rewrite Hs.
            simpl. rewrite IL.beqAddrTrue.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (structure pdentryBis))
              eqn:HbeqSh1Struct.
            {
              rewrite <-beqAddrTrue in HbeqSh1Struct. rewrite HbeqSh1Struct in *. rewrite HlookupBTRSh1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END StructurePointerIsKS *)
          }

          assert(NextKSIsKS s).
          { (* BEGIN NextKSIsKS s *)
            intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull.
            unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) kernel) eqn:HbeqSh1Block;
              try(exfalso; congruence). unfold nextKSentry in *. rewrite Hs in HnextKSAddr. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) nextKSaddr) eqn:HbeqSh1Next;
              try(exfalso; congruence).
            rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnextKSs0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull).
            unfold isKS in *. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) nextKS) eqn:HbeqSh1NextKS.
            {
              rewrite <-beqAddrTrue in HbeqSh1NextKS. subst nextKS. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END NextKSIsKS *)
          }

          assert(NextKSOffsetIsPADDR s).
          { (* BEGIN NextKSOffsetIsPADDR s *)
            intros kernel nextKSaddr HkernIsKS HnextAddr.
            unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) kernel) eqn:HbeqSh1Block;
              try(exfalso; congruence). rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnextPADDRs0 kernel nextKSaddr HkernIsKS HnextAddr).
            destruct HnextPADDRs0 as (HnextPADDRs0 & HbeqNextNull).
            split; trivial. unfold isPADDR in *. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) nextKSaddr) eqn:HbeqSh1NextAddr.
            {
              rewrite <-beqAddrTrue in HbeqSh1NextAddr. subst nextKSaddr. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END NextKSOffsetIsPADDR *)
          }

          assert(NoDupInFreeSlotsList s).
          { (* BEGIN NoDupInFreeSlotsList s *)
            intros partition pdentry HlookupPart. rewrite Hs in HlookupPart. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
              try(exfalso; congruence). rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnoDupFrees0 partition pdentry HlookupPart). rewrite HgetFreeEq. assumption.
            (* END NoDupInFreeSlotsList *)
          }

          assert(freeSlotsListIsFreeSlot s).
          { (* BEGIN freeSlotsListIsFreeSlot s *)
            intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
            rewrite HgetFreeEq in *. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition)
              eqn:HbeqSh1Part; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HfreeIsFrees0 partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed
              HaddrInList HbeqAddrNull). unfold isFreeSlot in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
            {
              rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (addr+scoffset)))
              eqn:HbeqSh1Sce.
            {
              rewrite <-beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. exfalso.
              destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence). rewrite HlookupBTRSh1 in *. congruence.
            }
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (addr+sh1offset)))
              eqn:HbeqSh1s.
            - rewrite <-beqAddrTrue in HbeqSh1s. rewrite HbeqSh1s in *. rewrite HlookupBTRSh1 in *.
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              destruct (lookup (CPaddr (addr+scoffset)) (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence). destruct HfreeIsFrees0 as (Hstart & Hr & Hw & He & Hpres & Hacc & _ & _ &
                _ & Horigin & Hnext). intuition.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END freeSlotsListIsFreeSlot *)
          }

          assert(DisjointFreeSlotsLists s).
          { (* BEGIN DisjointFreeSlotsLists s *)
            intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. rewrite Hs in Hpart1IsPDT.
            rewrite Hs in Hpart2IsPDT. simpl in *. rewrite HgetFreeEq. rewrite HgetFreeEq.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part1)
              eqn:HbeqSh1Part1; try(exfalso; congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part2) eqn:HbeqSh1Part2;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HdisjointFrees0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). assumption.
            (* END DisjointFreeSlotsLists *)
          }

          assert(inclFreeSlotsBlockEntries s).
          { (* BEGIN inclFreeSlotsBlockEntries s *)
            intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition)
              eqn:HbeqSh1Part; try(exfalso; congruence). rewrite HgetFreeEq.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HgetKSEq; trivial.
            specialize(HinclFreeKSEs0 partition HpartIsPDT). assumption.
            (* END inclFreeSlotsBlockEntries *)
          }

          assert(DisjointKSEntries s).
          { (* BEGIN DisjointKSEntries s *)
            intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. rewrite Hs in Hpart1IsPDT.
            rewrite Hs in Hpart2IsPDT. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part1)
              eqn:HbeqSh1Part1; try(exfalso; congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) part2) eqn:HbeqSh1Part2;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HgetKSEq; trivial.
            specialize(Hdisjoints0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). rewrite HgetKSEq; trivial.
            (* END DisjointKSEntries *)
          }

          assert(noDupPartitionTree s).
          { (* BEGIN noDupPartitionTree s *)
            unfold noDupPartitionTree in *. rewrite HgetPartsEq. assumption.
            (* END noDupPartitionTree *)
          }

          assert(isParent s).
          { (* BEGIN isParent s *)
            intros partition pdparent HparentIsPart HpartIsChild.
            assert(HparentIsPDT: isPDT pdparent s) by (apply IL.partitionsArePDT; trivial). rewrite HgetPartsEq in *.
            apply HPDTEq in HparentIsPDT. rewrite HgetChildrenEq in *; trivial.
            specialize(HisParents0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent in *.
            rewrite Hs. simpl. rewrite IL.beqAddrTrue.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part.
            {
              rewrite <-beqAddrTrue in HbeqSh1Part. subst partition. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END isParent *)
          }

          assert(isChild s).
          { (* BEGIN isChild s *)
            intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEq in *.
            unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HisChilds0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
            rewrite HgetChildrenEq; trivial. unfold isPDT. unfold getChildren in *. unfold getMappedBlocks in *.
            unfold getKSEntries in *.
            destruct (lookup pdparent (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
            (* END isChild *)
          }

          assert(noDupKSEntriesList s).
          { (* BEGIN noDupKSEntriesList s *)
            intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition)
              eqn:HbeqSh1Part; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnoDups0 partition HpartIsPDT). rewrite HgetKSEq; trivial.
            (* END noDupKSEntriesList *)
          }

          assert(noDupMappedBlocksList s).
          { (* BEGIN noDupMappedBlocksList s *)
            intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition)
              eqn:HbeqSh1Part; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnoDupMappeds0 partition HpartIsPDT). rewrite HgetMappedBEq; trivial.
            (* END noDupMappedBlocksList *)
          }

          assert(wellFormedBlock s).
          { (* BEGIN wellFormedBlock s *)
            intros block startaddr endaddr HPflag HstartBlock HendBlock. unfold bentryPFlag in *.
            unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs in HPflag. rewrite Hs in HstartBlock.
            rewrite Hs in HendBlock. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(Hwells0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
            (* END wellFormedBlock *)
          }

          assert(parentOfPartitionIsPartition s).
          { (* BEGIN parentOfPartitionIsPartition s *)
            intros partition pdentry HlookupPart. rewrite Hs in HlookupPart. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
              try(exfalso; congruence). rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HparentOfParts0 partition pdentry HlookupPart).
            destruct HparentOfParts0 as (HparentIsPart & Hprops). split; trivial. intro HbeqPartRoot.
            specialize(HparentIsPart HbeqPartRoot). rewrite HgetPartsEq.
            destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
            exists parentEntry. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) (parent pdentry)) eqn:HbeqSh1Parent.
            {
              rewrite <-beqAddrTrue in HbeqSh1Parent. rewrite HbeqSh1Parent in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END parentOfPartitionIsPartition *)
          }

          assert(NbFreeSlotsISNbFreeSlotsInList s).
          { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
            intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. rewrite Hs in HpartIsPDT.
            unfold pdentryNbFreeSlots in *. rewrite Hs in HnbFree. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition)
              eqn:HbeqSh1Part; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HgetFreeEq.
            specialize(HnbFrees0 partition nbfreeslots HpartIsPDT HnbFree). assumption.
            (* END NbFreeSlotsISNbFreeSlotsInList *)
          }

          assert(maxNbPrepareIsMaxNbKernels s).
          { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
            intros partition kernList HlistOfKerns. apply HkernListEq in HlistOfKerns.
            specialize(HmaxNbPreps0 partition kernList HlistOfKerns). assumption.
            (* END maxNbPrepareIsMaxNbKernels *)
          }

          assert(blockInChildHasAtLeastEquivalentBlockInParent s).
          { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
            intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
              HstartChild HendChild HPflagChild. assert(HparentIsPDT: isPDT pdparent s).
            { apply IL.partitionsArePDT; trivial. }
            assert(HchildIsPDT: isPDT child s) by (apply IL.childrenArePDT with pdparent; trivial).
            apply HPDTEq in HparentIsPDT. apply HPDTEq in HchildIsPDT. rewrite HgetChildrenEq in *; trivial.
            rewrite HgetPartsEq in *. rewrite HgetMappedBEq in *; trivial. unfold bentryPFlag in *.
            unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs in HPflagChild.
            rewrite Hs in HstartChild. rewrite Hs in HendChild. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HblockEquivParents0 pdparent child block startChild endChild HparentIsPart HchildIsChild
              HblockMappedChild HstartChild HendChild HPflagChild).
            destruct HblockEquivParents0 as [blockParent [startP [endP (HblockPMapped & HstartP & HendP & Hbounds)]]].
            exists blockParent. exists startP. exists endP. unfold bentryStartAddr in *. rewrite Hs. simpl.
            rewrite IL.beqAddrTrue. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) blockParent)
              eqn:HbeqSh1BP.
            {
              rewrite <-beqAddrTrue in HbeqSh1BP. subst blockParent. rewrite HlookupBTRSh1 in *. exfalso; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
            (* END blockInChildHasAtLeastEquivalentBlockInParent *)
          }

          assert(partitionTreeIsTree s).
          { (* BEGIN partitionTreeIsTree s *)
            intros child pdparent parentsList HbeqChildBisRoot HchildIsPart HparentIsParent HparentsList.
            rewrite HgetPartsEq in *.  unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) child)
              eqn:HbeqSh1Child; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(Htrees0 child pdparent parentsList HbeqChildBisRoot HchildIsPart HparentIsParent).
            apply Htrees0. revert HparentsList. apply HparentsListEq.
            destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
            destruct v; try(exfalso; congruence). subst pdparent.
            specialize(HparentOfParts0 child p HlookupChild). destruct HparentOfParts0 as (HparentIsPart & _).
            specialize(HparentIsPart HbeqChildBisRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & _).
            unfold isPDT. rewrite HlookupParent. trivial.
            (* END partitionTreeIsTree *)
          }

          assert(kernelEntriesAreValid s).
          { (* BEGIN kernelEntriesAreValid s *)
            intros kernel idx HkernIsKS Hidx. unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) kernel)
              eqn:HbeqSh1Kern; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HkernIdxIsBEs0 kernel idx HkernIsKS Hidx). unfold isBE in *. rewrite Hs. simpl.
            rewrite IL.beqAddrTrue.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (kernel+idx))) eqn:HbeqSh1Idx.
            {
              rewrite <-beqAddrTrue in HbeqSh1Idx. rewrite HbeqSh1Idx in *. rewrite HlookupBTRSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            (* END kernelEntriesAreValid *)
          }

          assert(nextKernelIsValid s).
          { (* BEGIN nextKernelIsValid s *)
            intros kernel HkernIsKS. unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) kernel)
              eqn:HbeqSh1Kern; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnextKSIsValids0 kernel HkernIsKS).
            destruct HnextKSIsValids0 as (HlebNextMax & [nextaddr (HlookupNextA & Hnext)]). split; trivial.
            exists nextaddr. unfold isKS in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue. split.
            - intro Hp. specialize(HlookupNextA Hp).
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) {| p:=kernel+nextoffset; Hp:=Hp |})
                eqn:HbeqSh1NextA.
              {
                rewrite <-beqAddrTrue in HbeqSh1NextA. rewrite HbeqSh1NextA in *. congruence.
              }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            - destruct Hnext as [HnextIsKS | HnextIsNull]; auto. left.
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) nextaddr) eqn:HbeqSh1Next.
              { rewrite <-beqAddrTrue in HbeqSh1Next. subst nextaddr. rewrite HlookupBTRSh1 in *. congruence. }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            (* END nextKernelIsValid *)
          }

          assert(noDupListOfKerns s).
          { (* BEGIN noDupListOfKerns s *)
            intros partition kernList HlistOfKerns. apply HkernListEq in HlistOfKerns.
            specialize(HnoDupListKSs0 partition kernList HlistOfKerns). assumption.
            (* END noDupListOfKerns *)
          }

          assert(MPUsizeIsBelowMax s).
          { (* BEGIN MPUsizeIsBelowMax s *)
            intros partition MPUlist HMPU. unfold pdentryMPU in *. rewrite Hs in HMPU. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition)
              eqn:HbeqSh1Part; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HMPUsizes0 partition MPUlist HMPU). assumption.
            (* END MPUsizeIsBelowMax *)
          }

          assert(originIsParentBlocksStart s).
          { (* BEGIN originIsParentBlocksStart s *)
            intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
            rewrite HgetPartsEq in *. rewrite Hs in HlookupPart. unfold scentryOrigin in *. rewrite Hs in Horigin.
            simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
              try(exfalso; congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            assert(isPDT partition s0) by (unfold isPDT; rewrite HlookupPart; trivial).
            rewrite HgetMappedBEq in HblockMapped; trivial.
            specialize(HoriginIsStarts0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart
              HblockMapped Hsce Horigin). destruct HoriginIsStarts0 as (HoriginIsStart & HlebStarts). split.
            - intro HbeqPartRoot. specialize(HoriginIsStart HbeqPartRoot).
              destruct HoriginIsStart as [blockParent (HblockPMapped & HstartP & Hincl)]. exists blockParent.
              assert(isPDT (parent pdentry) s0).
              {
                unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
                destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
                destruct v; try(simpl in *; congruence). trivial.
              }
              rewrite HgetMappedBEq; trivial. split; trivial. unfold bentryStartAddr in *.
              assert(HlookupEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
              {
                rewrite Hs. simpl. rewrite IL.beqAddrTrue.
                destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) blockParent) eqn:HbeqSh1BP.
                {
                  rewrite <-beqAddrTrue in HbeqSh1BP. subst blockParent. rewrite HlookupBTRSh1 in *.
                  exfalso; congruence.
                }
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              }
              rewrite HlookupEq. split; trivial. rewrite Hs. simpl. rewrite IL.beqAddrTrue. intros addr Hstart.
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Bblock;
                try(simpl in *; exfalso; congruence). rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. apply Hincl; assumption.
            - unfold bentryStartAddr. rewrite Hs. simpl. rewrite IL.beqAddrTrue. intros addr Hstart.
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Bblock;
                try(simpl in *; exfalso; congruence). rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. apply HlebStarts; assumption.
            (* END originIsParentBlocksStart *)
          }

          assert(nextImpliesBlockWasCut s).
          { (* BEGIN nextImpliesBlockWasCut s *)
            intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
              Hsce HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEq in *. rewrite Hs in HlookupPart.
            unfold scentryNext in *. rewrite Hs in Hnext. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
              try(exfalso; congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            assert(isPDT partition s0) by (unfold isPDT; rewrite HlookupPart; trivial).
            rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryEndAddr in *.
            assert(HlookupEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
            {
              rewrite Hs. rewrite Hs in HendBlock. simpl in *. rewrite IL.beqAddrTrue in *.
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block.
              {
                rewrite <-beqAddrTrue in HbeqSh1Block. subst block. rewrite HlookupBTRSh1 in *.
                exfalso; congruence.
              }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            }
            rewrite HlookupEq in *. specialize(HnextCuts0 partition pdentry block scentryaddr scnext endaddr
              HpartIsPart HlookupPart HblockMapped HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
            destruct HnextCuts0 as [blockParent [endP (HblockPMapped & HendP & HltEnds & Hincl)]]. exists blockParent.
            exists endP. assert(isPDT (parent pdentry) s0).
            {
              unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
              destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
              destruct v; try(simpl in *; congruence). trivial.
            }
            rewrite HgetMappedBEq; trivial. split; trivial. unfold bentryEndAddr in *. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) blockParent) eqn:HbeqSh1BP.
            {
              rewrite <-beqAddrTrue in HbeqSh1BP. subst blockParent. rewrite HlookupBTRSh1 in *. exfalso; congruence.
            }
            rewrite IL.beqAddrTrue. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
            (* END nextImpliesBlockWasCut *)
          }

          assert(blocksAddressesTypes s).
          { (* BEGIN blocksAddressesTypes s *)
            intros block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock. unfold bentryPFlag in *.
            unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs in HPflagBlock.
            rewrite Hs in HstartBlock. rewrite Hs in HendBlock. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
            rewrite Hs in HPDchildBlock. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset)))
              eqn:HbeqSh1s.
            - rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. subst block. right. right.
              destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HstartBTRs0 in *. rewrite <-HendBTRs0 in *.
              subst startaddr. subst endaddr. intros addr HaddrInRange.
              specialize(HremovedAddrsAreNones0 addr HaddrInRange). rewrite Hs. simpl. rewrite IL.beqAddrTrue.
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
              { rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. congruence. }
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              specialize(HaddrTypes0 block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock).
              destruct HaddrTypes0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hrange]].
              + left. split.
                * unfold isKS in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
                  destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh1Start.
                  { rewrite <-beqAddrTrue in HbeqSh1Start. subst startaddr. rewrite HlookupBTRSh1 in *. congruence. }
                  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                * intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
                  destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
                  --- left. unfold isBE in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
                      destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) addr) eqn:HbeqSh1Addr.
                      { rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. rewrite HlookupBTRSh1 in *. congruence. }
                      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  --- right. left. unfold isSHE in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
                      destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) addr) eqn:HbeqSh1Addr.
                      { trivial. }
                      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  --- right. right. left. unfold isSCE in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
                      destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) addr) eqn:HbeqSh1Addr.
                      { rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. rewrite HlookupBTRSh1 in *. congruence. }
                      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  --- right. right. right. left. unfold isPADDR in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
                      destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) addr) eqn:HbeqSh1Addr.
                      { rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. rewrite HlookupBTRSh1 in *. congruence. }
                      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  --- right. right. right. right. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
                      destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) addr) eqn:HbeqSh1Addr.
                      { rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. congruence. }
                      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              + right. left. split.
                * unfold isPDT in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
                  destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh1Start.
                  { rewrite <-beqAddrTrue in HbeqSh1Start. subst startaddr. rewrite HlookupBTRSh1 in *. congruence. }
                  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                * intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). rewrite Hs. simpl.
                  rewrite IL.beqAddrTrue.
                  destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) addr) eqn:HbeqSh1Addr.
                  { rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. congruence. }
                  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
              + right. right. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). rewrite Hs. simpl.
                rewrite IL.beqAddrTrue.
                destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) addr) eqn:HbeqSh1Addr.
                { rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. congruence. }
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
                rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            (* END blocksAddressesTypes *)
          }

          assert(notPDTIfNotPDflag s).
          { (* BEGIN notPDTIfNotPDflag s *)
            intros block startaddr sh1entryaddrB HstartBlock Hsh1 HPflag HPDflagBis HPDchild. unfold bentryPFlag in *.
            unfold bentryStartAddr in *. unfold sh1entryAddr in *. rewrite Hs in HstartBlock. rewrite Hs in Hsh1.
            rewrite Hs in HPflag. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
            unfold sh1entryPDflag in *. rewrite Hs in HPDchild. rewrite Hs in HPDflagBis. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset))
              sh1entryaddrB) eqn:HbeqSh1s.
            - assert(sh1entryaddrB = CPaddr (block + sh1offset)).
              {
                destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). assumption.
              }
              subst sh1entryaddrB. rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial.
              subst block.
              destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HstartBTRs0 in *. subst startaddr.
              specialize(HremovedAddrsAreNones0 globalIdBlockToRemove HstartBTRInRange). unfold isPDT. intro Hcontra.
              rewrite Hs in Hcontra. simpl in *. rewrite IL.beqAddrTrue in *.
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) globalIdBlockToRemove)
                eqn:HbeqSh1Glob; try(exfalso; congruence).
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HremovedAddrsAreNones0 in *.
              congruence.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              specialize(HnotPDTs0 block startaddr sh1entryaddrB HstartBlock Hsh1 HPflag HPDflagBis HPDchild).
              unfold isPDT in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue. contradict HnotPDTs0.
              destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh1Start;
                try(exfalso; congruence). rewrite <-beqAddrFalse in *.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            (* END notPDTIfNotPDflag *)
          }

          assert(nextKernAddrIsInSameBlock s).
          { (* BEGIN nextKernAddrIsInSameBlock s *)
            intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock HkernIsKS.
            unfold isKS in *. rewrite Hs in HkernIsKS. unfold bentryPFlag in *. unfold bentryStartAddr in *.
            unfold bentryEndAddr in *. rewrite Hs in HstartBlock. rewrite Hs in HPflagBlock. rewrite Hs in HendBlock.
            simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) kernel) eqn:HbeqSh1Kern;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
            rewrite Hs in HPDchildBlock. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset)))
              eqn:HbeqSh1s.
            - rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. subst block.
              intro HnextInRange. exfalso.
              destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence). rewrite <-HstartBTRs0 in *. rewrite <-HendBTRs0 in *. subst startaddr.
              subst endaddr. specialize(HnextKSIsValids0 kernel HkernIsKS).
              destruct HnextKSIsValids0 as (HlebNextMax & [nextaddr (HlookupNextA & _)]).
              specialize(HremovedAddrsAreNones0 (CPaddr (kernel+nextoffset)) HnextInRange). unfold CPaddr in *.
              destruct (le_dec (kernel + nextoffset) maxAddr); try(lia).
              rewrite HlookupNextA in HremovedAddrsAreNones0. congruence.
            - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
              specialize(HkernIsStart block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock
                HkernIsKS). assumption.
            (* END nextKernAddrIsInSameBlock *)
          }

          assert(blockBelongsToAPart s).
          { (* BEGIN blockBelongsToAPart s *)
            intros block HPflagBlock. unfold bentryPFlag in *. rewrite Hs in HPflagBlock. simpl in *.
            rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HblockInParts0 block HPflagBlock).
            destruct HblockInParts0 as [part (HpartIsPart & HblockMapped)]. exists part.
            assert(HpartIsPDT: isPDT part s0).
            {
              unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
              destruct (lookup part (memory s0) beqAddr); try(simpl in *; congruence).
              destruct v; try(simpl in *; congruence). trivial.
            }
            rewrite HgetPartsEq. rewrite HgetMappedBEq; auto.
            (* END blockBelongsToAPart *)
          }

          assert(PDflagMeansNoChild s).
          { (* BEGIN PDflagMeansNoChild s *)
            intros block HblockIsBE HPDflagBlock. unfold isBE in *. rewrite Hs in HblockIsBE.
            unfold sh1entryPDflag in *. rewrite Hs in HPDflagBlock. unfold sh1entryPDchild. rewrite Hs. simpl in *.
            rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset)))
              eqn:HbeqSh1s; try(simpl in *; exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnoChildIfNoPDs0 block HblockIsBE HPDflagBlock). assumption.
            (* END PDflagMeansNoChild *)
          }

          assert(nbPrepareIsNbKern s).
          { (* BEGIN nbPrepareIsNbKern s *)
            intros partition pdentry HlookupPart. rewrite Hs in HlookupPart. simpl in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
              try(exfalso; congruence). rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnbPreps0 partition pdentry HlookupPart). rewrite HcompleteKernEq. assumption.
           (* END nbPrepareIsNbKern *)
          }

          assert(pdchildIsPDT s).
          { (* BEGIN pdchildIsPDT s *)
            intros part block sh1entryaddrB idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
            assert(HpartIsPDT: isPDT part s) by (apply IL.partitionsArePDT; trivial). rewrite HgetPartsEq in *.
            apply HPDTEq in HpartIsPDT. rewrite HgetMappedBEq in *; trivial. rewrite HgetChildrenEq; trivial.
            unfold sh1entryAddr in *. unfold sh1entryPDchild in *. rewrite Hs in Hsh1. rewrite Hs in HPDchild.
            simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) sh1entryaddrB) eqn:HbeqSh1s;
              try(simpl in *; exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HpdchildIsPDTs0 part block sh1entryaddrB idchild HpartBisIsPart HblockMapped Hsh1 HPDchild
              HbeqIdChildNull). assumption.
            (* END pdchildIsPDT *)
          }
          unfold consistency1. intuition.
        }

        assert(noDupMappedPaddrList s).
        { (* BEGIN noDupMappedPaddrList s *)
          intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
          rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition)
            eqn:HbeqSh1Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(HnoDupPaddrs0 partition HpartIsPDT). rewrite HgetMappedPEq; trivial.
          (* END noDupMappedPaddrList *)
        }

        assert(accessibleParentPaddrIsAccessibleIntoChild s).
        { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
          intros pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
          assert(HparentIsPDT: isPDT pdparent s) by (apply IL.partitionsArePDT; trivial). rewrite HgetPartsEq in *.
          assert(HchildIsPDT: isPDT child s) by (apply IL.childrenArePDT with pdparent; trivial).
          apply HPDTEq in HparentIsPDT. apply HPDTEq in HchildIsPDT. rewrite HgetMappedPEq in *; trivial.
          rewrite HgetChildrenEq in *; trivial. rewrite HgetAccMappedPEq in *; trivial.
          specialize(Haccesss0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild).
          assumption.
          (* END accessibleParentPaddrIsAccessibleIntoChild *)
        }

        assert(sharedBlockPointsToChild s).
        { (* BEGIN sharedBlockPointsToChild s *)
          intros pdparent child addr blockParent sh1entryaddrB HparentIsPart HchildIsChild HaddrUsedChild
            HaddrInBlockParent HblockParentMapped Hsh1.
          assert(HparentIsPDT: isPDT pdparent s) by (apply IL.partitionsArePDT; trivial). rewrite HgetPartsEq in *.
          assert(HchildIsPDT: isPDT child s) by (apply IL.childrenArePDT with pdparent; trivial).
          apply HPDTEq in HparentIsPDT. apply HPDTEq in HchildIsPDT. rewrite HgetChildrenEq in *; trivial.
          rewrite HgetMappedBEq in *; trivial. unfold sh1entryAddr in *.
          assert(HlookupBPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
          {
            rewrite Hs. rewrite Hs in Hsh1. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh1BP;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          rewrite HlookupBPEq in *. assert(HaddrInBlockParents0: In addr (getAllPaddrAux [blockParent] s0)).
          { simpl in *. rewrite <-HlookupBPEq. assumption. }
          unfold getUsedPaddr in *. rewrite HgetMappedPEq in *; trivial. rewrite HgetConfigEq in *; trivial.
          specialize(Hshareds0 pdparent child addr blockParent sh1entryaddrB HparentIsPart HchildIsChild
            HaddrUsedChild HaddrInBlockParents0 HblockParentMapped Hsh1). unfold sh1entryPDchild in *.
          unfold sh1entryPDflag in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset)))
            eqn:HbeqSh1s.
          {
            rewrite <-beqAddrTrue in HbeqSh1s.  apply CPaddrAddEq in HbeqSh1s; trivial. subst blockParent. exfalso.
            specialize(HBTRPsAddsNotUseds0 idPDchild addr HidchildIsChilds0 HaddrInBlockParents0).
            destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). subst sh1entryaddr. rewrite HlookupBTRSh1 in *.
            destruct Hshareds0 as [Hchild | Hflag]; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END sharedBlockPointsToChild *)
        }

        assert(adressesRangePreservedIfOriginAndNextOk s).
        { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
          intros partition pdentry block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE
            HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. rewrite Hs in HlookupPart.
          unfold isBE in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
          unfold scentryNext in *. unfold scentryOrigin in *. rewrite Hs in HblockIsBE. rewrite Hs in HstartBlock.
          rewrite Hs in HendBlock. rewrite Hs in HPflag. rewrite Hs in Hnext. rewrite Hs in Horigin. simpl in *.
          rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
              try(exfalso; congruence).
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
              try(exfalso; congruence).
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HgetPartsEq in *.
          assert(isPDT partition s0) by (unfold isPDT; rewrite HlookupPart; trivial).
          rewrite HgetMappedBEq in HblockMapped; trivial.
          specialize(Hranges0 partition pdentry block scentryaddr startBlock endBlock HpartIsPart HblockMapped
            HblockIsBE HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot).
          destruct Hranges0 as [blockParent (HblockPMapped & HBPIsBE & HstartP & HendP)]. exists blockParent.
          assert(isPDT (parent pdentry) s0).
          {
            unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
            destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          rewrite HgetMappedBEq; trivial. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh1BP.
          {
            rewrite <-beqAddrTrue in HbeqSh1BP. subst blockParent. exfalso. unfold isBE in *.
            rewrite HlookupBTRSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); auto.
          (* END adressesRangePreservedIfOriginAndNextOk *)
        }

        assert(HcurrIsPDT: isPDT currentPart s0).
        {
          unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
          destruct (lookup currentPart (memory s0) beqAddr); try(simpl in *; congruence).
          destruct v; try(simpl in *; congruence). trivial.
        }

        assert(childsBlocksPropsInParent s).
        { (* BEGIN childsBlocksPropsInParent s *)
          intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
            HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent
            HendParent HPflagParent HlebStart HgebEnd. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          unfold bentryPFlag in *. rewrite Hs in HstartChild. rewrite Hs in HendChild. rewrite Hs in HPflagChild.
          simpl in *. rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) blockChild) eqn:HbeqSh1BC;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(HparentIsPDT: isPDT pdparent s) by (apply IL.partitionsArePDT; trivial). rewrite HgetPartsEq in *.
          assert(HchildIsPDT: isPDT child s) by (apply IL.childrenArePDT with pdparent; trivial).
          apply HPDTEq in HparentIsPDT. apply HPDTEq in HchildIsPDT. rewrite HgetChildrenEq in *; trivial.
          rewrite HgetMappedBEq in *; trivial. unfold checkChild. unfold bentryAFlag.
          assert(HlookupBPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
          {
            rewrite Hs. rewrite Hs in HstartParent. simpl in *. rewrite IL.beqAddrTrue in *.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh1BP;
              try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          }
          rewrite HlookupBPEq in *. specialize(HchildBlocksPropss0 child pdparent blockChild startChild endChild
            blockParent startParent endParent HparentIsPart HchildIsChild HblockChildMapped HstartChild HendChild
            HPflagChild HblockParentMapped HstartParent HendParent HPflagParent HlebStart HgebEnd).
          destruct HchildBlocksPropss0 as (HcheckChild & HchildNotNull & HlocProps & HAflagBP).
          assert(blockToRemoveInCurrPartAddr <> blockParent).
          {
            intro. subst blockParent.
            specialize(Hwells0 blockChild startChild endChild HPflagChild HstartChild HendChild).
            destruct Hwells0 as (Hwells0 & _).
            assert(HstartCInRange: In startChild (getAllPaddrAux [blockToRemoveInCurrPartAddr] s0)).
            {
              simpl. destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartParent. rewrite <-HendParent.
              apply IL.getAllPaddrBlockIncl; lia.
            }
            assert(pdparent = currentPart).
            {
              destruct (beqAddr pdparent currentPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
              rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HBTRMappeds0.
              apply InFilterPresentInList in HblockParentMapped.
              specialize(Hdisjoints0 pdparent currentPart HparentIsPDT HcurrIsPDT HbeqParts).
              destruct Hdisjoints0 as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
              specialize(Hdisjoint blockToRemoveInCurrPartAddr HblockParentMapped). congruence.
            }
            subst pdparent. specialize(HBTRPsAddsNotUseds0 child startChild HchildIsChild HstartCInRange). exfalso.
            contradict HBTRPsAddsNotUseds0. unfold getUsedPaddr. apply in_or_app. right.
            apply IL.addrInBlockIsMapped with blockChild; trivial. simpl.
            destruct (lookup blockChild (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-HstartChild. rewrite <-HendChild. rewrite app_nil_r.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          split; try(split; try(split)); trivial.
          - unfold checkChild in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
            destruct (lookup blockParent (memory s0) beqAddr); trivial. destruct v; trivial.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset)))
              eqn:HbeqSh1s; trivial.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          - unfold sh1entryPDchild. rewrite Hs. simpl. rewrite IL.beqAddrTrue. intros childGlobalID HPDchild.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset)))
              eqn:HbeqSh1s.
            {
              rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. exfalso; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). apply HchildNotNull; assumption.
          - unfold sh1entryInChildLocation in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue. intros childLoc HchildLoc.
            destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset)))
              eqn:HbeqSh1s.
            {
              rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. exfalso; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). apply HlocProps.
            destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial.
            intro HbeqLocNull. specialize(HlocIsBE HbeqLocNull). unfold isBE in *. simpl in *.
            rewrite IL.beqAddrTrue in *. destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) childLoc)
              eqn:HbeqSh1Loc; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          (* END childsBlocksPropsInParent *)
        }

        assert(noChildImpliesAddressesNotShared s).
        { (* BEGIN noChildImpliesAddressesNotShared s *)
          intros partition pdentry block sh1entryaddrB HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild child addr
            HchildIsChild HaddrInBlock. rewrite HgetPartsEq in *. rewrite Hs in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite IL.beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(HpartIsPDT: isPDT partition s0) by (unfold isPDT; rewrite HlookupPart; trivial).
          assert(HchildIsPDT: isPDT child s) by (apply IL.childrenArePDT with partition; trivial).
          apply HPDTEq in HchildIsPDT. rewrite HgetMappedBEq in *; trivial. rewrite HgetChildrenEq in *; trivial.
          rewrite Hs in HaddrInBlock. simpl in *. rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
            try(simpl in *; exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryPDchild in *.
          rewrite Hs in HPDchild. simpl in *. rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) sh1entryaddrB) eqn:HbeqSh1s.
          - subst sh1entryaddrB. rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial.
            subst block. assert(partition = currentPart).
            {
              destruct (beqAddr partition currentPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
              rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HBTRMappeds0.
              apply InFilterPresentInList in HblockMapped.
              specialize(Hdisjoints0 partition currentPart HpartIsPDT HcurrIsPDT HbeqParts).
              destruct Hdisjoints0 as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
              specialize(Hdisjoint blockToRemoveInCurrPartAddr HblockMapped). congruence.
            }
            subst partition. rewrite HgetMappedPEq; trivial. apply HBTRPsAddsNotShareds0; assumption.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
            specialize(HnoChilds0 partition pdentry block sh1entryaddrB HpartIsPart HlookupPart HblockMapped Hsh1
              HPDchild child addr HchildIsChild HaddrInBlock). rewrite HgetMappedPEq; trivial.
          (* END noChildImpliesAddressesNotShared *)
        }

        assert(kernelsAreNotAccessible s).
        { (* BEGIN kernelsAreNotAccessible s *)
          intros block startaddr Hstart HPflag HstartIsKS. unfold bentryStartAddr in *. unfold bentryPFlag in *.
          unfold isKS in *. unfold bentryAFlag. rewrite Hs in Hstart. rewrite Hs in HPflag. rewrite Hs in HstartIsKS.
          rewrite Hs. simpl in *. rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) startaddr) eqn:HbeqSh1Start;
            try(exfalso; congruence).
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
            try(congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(HkernNotAccs0 block startaddr Hstart HPflag HstartIsKS). assumption.
          (* END kernelsAreNotAccessible *)
        }

        assert(blockAndNextAreSideBySide s).
        { (* BEGIN blockAndNextAreSideBySide s *)
          intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
            Hnext. assert(HpartIsPDT: isPDT partition s) by (apply IL.partitionsArePDT; trivial).
          rewrite HgetPartsEq in *. apply HPDTEq in HpartIsPDT. rewrite HgetMappedBEq in *; trivial.
          unfold bentryEndAddr in *. unfold scentryNext in *. rewrite Hs in HendBlock. rewrite Hs in Hnext.
          simpl in *. rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
            try(exfalso; congruence).
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          specialize(HnextBlockSides0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock
            Hsce HbeqNextNull Hnext). destruct HnextBlockSides0 as (HstartNext & HnextMapped).
          split; trivial. unfold bentryStartAddr in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) scnext) eqn:HbeqSh1Next.
          {
            rewrite <-beqAddrTrue in HbeqSh1Next. subst scnext. rewrite HlookupBTRSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          (* END blockAndNextAreSideBySide *)
        }

        assert(parentBlocksBoundsIfNoNext s).
        { (* BEGIN parentBlocksBoundsIfNoNext s *)
          intros partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock HendBlock
            Hsce Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEq in *. rewrite Hs in HlookupPart.
          unfold bentryEndAddr in *. unfold bentryStartAddr in *. rewrite Hs in HendBlock. rewrite Hs in HstartBlock.
          unfold scentryNext in *. rewrite Hs in Hnext. simpl in *. rewrite IL.beqAddrTrue in *.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
            try(exfalso; congruence).
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
            try(exfalso; congruence).
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) partition) eqn:HbeqSh1Part;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          assert(HpartIsPDT: isPDT partition s0) by (unfold isPDT; rewrite HlookupPart; trivial).
          rewrite HgetMappedBEq in HblockMapped; trivial.
          specialize(HblockPBoundss0 partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped
            HstartBlock HendBlock Hsce Hnext HbeqPartRoot HlookupPart).
          destruct HblockPBoundss0 as [blockParent [startP (HblockPMapped & HstartP & HendP & HlebStarts)]].
          exists blockParent. exists startP. assert(isPDT (parent pdentry) s0).
          {
            unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
            destruct (lookup (parent pdentry) (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          rewrite HgetMappedBEq; trivial. unfold bentryStartAddr in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh1BP.
          {
            rewrite <-beqAddrTrue in HbeqSh1BP. subst blockParent. rewrite HlookupBTRSh1 in *. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); auto.
          (* END parentBlocksBoundsIfNoNext *)
        }

        assert(consistency s).
        { unfold consistency. unfold consistency2. intuition. }

        split. intuition. instantiate(1:= fun s => consistency s /\ partitionsIsolation s).
        split; auto. rewrite HgetPartsEq. split; try(split); trivial.
        - unfold isPDT in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr + sh1offset)) currentPart) eqn:HbeqSh1Curr.
          {
            rewrite <-beqAddrTrue in HbeqSh1Curr. subst currentPart. rewrite HlookupBTRSh1 in *. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct (lookup currentPart (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). exists p. reflexivity.
        - exists blockToRemoveInCurrPartAddr. unfold sh1entryAddr in *.
          destruct (lookup blockToRemoveInCurrPartAddr (memory s0) beqAddr) eqn:Hlookup; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). exists b. rewrite HgetMappedBEq; trivial. unfold bentryPFlag.
          unfold bentryAFlag. unfold bentryStartAddr. unfold bentryEndAddr. unfold checkChild. rewrite Hs. simpl.
          rewrite IL.beqAddrTrue.
          destruct (beqAddr (CPaddr (blockToRemoveInCurrPartAddr+sh1offset)) blockToRemoveInCurrPartAddr) eqn:Hbeq.
          { rewrite <-beqAddrTrue in Hbeq. rewrite Hbeq in *. exfalso; congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial. split; trivial. split; trivial.
          split; trivial. split; trivial. split; trivial. simpl. rewrite Hlookup. reflexivity.
      }
      intro recWriteEnded. destruct recWriteEnded.
      --- unfold negb. eapply weaken. apply WP.ret. intros s Hprops. simpl.
          destruct Hprops as (HPI & HKDI & HVS & [s0 [pdentryBase [statesList [parentsList (_ & _ & _ & Hconsists0 & _
            & HparentsList & Hlast & HlookupCurrs0 & HlookupCurr & HcurrIsParts0 & Hconsist & HnoDupPaddr & Hshared &
            Hrange & HchildBlockProps & HnoChild & HkernNotAcc & HnextBlockSide & HparentBounds & Hbase & Haccess &
            HlastPart & HisBuilt)]]]]). unfold consistency. unfold consistency2. intuition.
          unfold childLocMappedInChild. intros part block sh1entryaddr blockChild idchild. revert HisBuilt.
          destruct Hbase as [blockBase [bentryBase [bentryBases0 (HlookupBases0 & HPflags0 & HAflags0 & HbaseMappeds0
            & _ & HstartBs0 & HendBs0 & HcheckChildBs0 & _)]]].
          apply isBuiltFromWriteAccessibleRec.childLocMappedInChildPartialPreservedIsBuiltRec with pdentryBase
            blockBase; trivial.
          1,2,3,4,5,6,7,8,9: unfold consistency in *; unfold consistency1 in *; intuition.
          1,2: unfold consistency in *; unfold consistency2 in *; intuition.
          revert part block sh1entryaddr blockChild idchild.
          unfold consistency in *; unfold consistency2 in *; intuition.
      --- eapply weaken. apply WP.ret. intros s Hprops. simpl.
          destruct Hprops as (HPI & HKDI & HVS & [s0 [pdentryBase [statesList [parentsList (_ & _ & _ & Hconsists0 & _
            & HparentsList & Hlast & HlookupCurrs0 & HlookupCurr & HcurrIsParts0 & Hconsist & HnoDupPaddr & Hshared &
            Hrange & HchildBlockProps & HnoChild & HkernNotAcc & HnextBlockSide & HparentBounds & Hbase & Haccess &
            HlastPart & HisBuilt)]]]]). unfold consistency. unfold consistency2. intuition.
          unfold childLocMappedInChild. intros part block sh1entryaddr blockChild idchild. revert HisBuilt.
          destruct Hbase as [blockBase [bentryBase [bentryBases0 (HlookupBases0 & HPflags0 & HAflags0 & HbaseMappeds0
            & _ & HstartBs0 & HendBs0 & HcheckChildBs0 & _)]]].
          apply isBuiltFromWriteAccessibleRec.childLocMappedInChildPartialPreservedIsBuiltRec with pdentryBase
            blockBase; trivial.
          1,2,3,4,5,6,7,8,9: unfold consistency in *; unfold consistency1 in *; intuition.
          1,2: unfold consistency in *; unfold consistency2 in *; intuition.
          revert part block sh1entryaddr blockChild idchild.
          unfold consistency in *; unfold consistency2 in *; intuition.
    * (* case recRemoveSubblocksEnded = false *)
      unfold negb. eapply weaken. apply WP.ret. intros s Hprops.
      destruct Hprops as (_ & _ & _ & Hcontra). exfalso; congruence.
- (* case isBlockCut = false *)
  eapply bindRev.
  { (** MAL.readBlockAccessibleFromBlockEntryAddr *)
    eapply weaken. apply readBlockAccessibleFromBlockEntryAddr. intros s Hprops. simpl.
    split. apply Hprops. intuition.
  }
  intro addrIsAccessible. destruct addrIsAccessible.
  + (* case addrIsAccessible = true *)
    eapply bindRev.
    { (** removeBlockInDescendantsRec **) (*TODO HERE*)
      eapply weaken. apply ?. intros s Hprops. simpl.
    }
    intro recRemoveInDescendantsEnded. destruct recRemoveInDescendantsEnded.
    * (* case recRemoveInDescendantsEnded = true *)
      eapply bindRev.
      { (** MAL.writeSh1EntryFromBlockEntryAddr **)
        eapply weaken. apply writeSh1EntryFromBlockEntryAddr. intros s Hprops. simpl. admit.
      }
      intro. eapply weaken. apply WP.ret. intros s Hprops. simpl.
      admit.
    * (* case recRemoveInDescendantsEnded = false *)
      unfold negb. eapply weaken. apply WP.ret. intros s Hprops. simpl. admit.
      
  + (* case addrIsAccessible = false *)
    unfold negb. eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
Admitted.
