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
    intros part child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
    rewrite HgetPartsEqsA in *. assert(HgetChildrenEq: getChildren part a = getChildren part s0).
    { apply getChildrenEqRemove with idPDchild blockToRemove; trivial. }
    rewrite HgetChildrenEq in *.
    assert(HaddrMappedChilds0: In addr (getMappedPaddr child s0)).
    {
      destruct (beqAddr idPDchild child) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst child.
        pose proof (getMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in HaddrMappedChild. apply in_or_app.
        destruct HaddrMappedChild; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    assert(HBTRAccMapped: In blockToRemove (getAccessibleMappedBlocks idPDchild s0)).
    { apply IL.accessibleBlockIsAccessibleMapped; trivial. }
    assert(HaddrAccMappedParents0: In addr (getAccessibleMappedPaddr part s0)).
    {
      destruct (beqAddr idPDchild part) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. pose proof (getAccessibleMappedPaddrEqRemPartRemove
          blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRAccMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE
          HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite HeqA in *.
        rewrite Heqs0. apply in_app_or in HaddrAccMappedParent. apply in_or_app. destruct HaddrAccMappedParent; auto.
        right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getAccessibleMappedPaddrEqRemove with (blockToRemove:=blockToRemove)
          (s:=a) (removePart:=idPDchild); trivial.
    }
    specialize(Haccess part child addr HparentIsPart HchildIsChild HaddrAccMappedParents0 HaddrMappedChilds0).
    destruct (beqAddr idPDchild child) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. subst child.
      pose proof (getAccessibleMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT
        HBTRAccMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
      destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA. rewrite Heqs0 in *. apply in_or_app. apply in_app_or in Haccess.
      destruct Haccess as [HmappedLeft | HmappedRest]; auto. right. apply in_app_or in HmappedRest.
      destruct HmappedRest as [Hcontra | Hres]; trivial. simpl in *. unfold bentryAFlag in *.
      assert(HBEBis: exists bentry0 l newEnd,
        lookup blockToRemove (memory s0) beqAddr = Some (BE bentry0)
        /\ pdentryFirstFreeSlot idPDchild newEnd s0
        /\ lookup blockToRemove (memory a) beqAddr =
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
      rewrite Hlookups0 in Hcontra. rewrite <-HAflagBTR in *. assert(HchildIsPDT: isPDT idPDchild s0).
      { destruct HPDT as [pdentry0 [_ (Hlookup0 & _)]]. unfold isPDT. rewrite Hlookup0. trivial. }
      specialize(HnoDupMappedP idPDchild HchildIsPDT).
      pose proof (getMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRMapped HBE
        Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
      destruct Heqs as [leftMapped [rightMapped (HeqMappedA & HeqMappeds0)]]. rewrite HeqMappeds0 in HnoDupMappedP.
      rewrite HeqMappedA in *. apply Lib.NoDupSplitInclIff in HnoDupMappedP.
      destruct HnoDupMappedP as ((_ & HnoDupMappedP) & HdisjointLeft). apply Lib.NoDupSplitInclIff in HnoDupMappedP.
      destruct HnoDupMappedP as (_ & HdisjointRight). contradict HaddrMappedChild. apply Lib.in_or_app_neg.
      apply Lib.disjointPermut in HdisjointLeft. specialize(HdisjointRight addr Hcontra).
      assert(HcontraBis: In addr (getAllPaddrAux [blockToRemove] s0 ++ rightMapped)).
      { apply in_or_app. auto. }
      specialize(HdisjointLeft addr HcontraBis). auto.
    - rewrite <-beqAddrFalse in *. rewrite getAccessibleMappedPaddrEqRemove with (blockToRemove:=blockToRemove)
        (s0:=s0) (removePart:=idPDchild); trivial.
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
    intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild HaddrInBP
      HblockPMapped Hsh1. assert(HbeqBlocksP: blockToRemove <> blockParent).
    {
      intro Hcontra. subst blockParent. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      apply IL.mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
      rewrite Hlookups in Hlookup. injection Hlookup as HbentriesEq. subst bentry. simpl in *. congruence.
    }
    rewrite HgetPartsEqsA in *. assert(HgetChildrenEq: getChildren pdparent a = getChildren pdparent s0).
    { apply getChildrenEqRemove with idPDchild blockToRemove; trivial. }
    rewrite HgetChildrenEq in *. unfold sh1entryAddr in *. destruct (beqAddr idPDchild blockParent) eqn:HbeqChildBP.
    {
      rewrite <-beqAddrTrue in HbeqChildBP. subst blockParent. destruct HPDT as [_ [pdentry1 (_ & HlookupA & _)]].
      rewrite HlookupA in *. exfalso; congruence.
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
        (removePart:=idPDchild) in HaddrUsedChild; trivial. apply in_app_or in HaddrUsedChild. apply in_or_app.
      destruct HaddrUsedChild as [Hconfig | Hmapped]; auto. right.
      destruct (beqAddr idPDchild child) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst child.
        pose proof (getMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in Hmapped. apply in_or_app.
        destruct Hmapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    assert(HaddrInBPs0: In addr (getAllPaddrAux [blockParent] s0)).
    { simpl in *. rewrite <-HlookupsEq; trivial. }
    assert(HblockPMappeds0: In blockParent (getMappedBlocks pdparent s0)).
    {
      destruct (beqAddr idPDchild pdparent) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst pdparent. pose proof (getMappedBlocksEqRemPartRemove blockToRemove
          a s0 idPDchild HnoDup HPDT HBTRMapped HBE Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs.
        destruct Heqs as [leftList [rightList (HeqA & Heqs0)]]. rewrite Heqs0. rewrite HeqA in *. apply in_or_app.
        apply in_app_or in HblockPMapped. destruct HblockPMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *.
        rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a) (removePart:=idPDchild); trivial.
    }
    specialize(Hshared pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChilds0
      HaddrInBPs0 HblockPMappeds0 Hsh1). unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
    assert(Hsh1PIsSHE: isSHE (CPaddr (blockParent+sh1offset)) s0).
    {
      unfold isSHE.
      destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr); try(destruct Hshared; congruence).
      destruct v; try(destruct Hshared; congruence). trivial.
    }
    unfold isSHE in *. destruct (beqAddr idPDchild (CPaddr (blockParent+sh1offset))) eqn:HbeqPartSh1.
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
    rewrite HgetPartsEqsA in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
    destruct (beqAddr idPDchild blockChild) eqn:HbeqChildBlockC.
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
    destruct (beqAddr idPDchild blockParent) eqn:HbeqChildBlockP.
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
    assert(HlookupBlockCEq: lookup blockChild (memory a) beqAddr = lookup blockChild (memory s0) beqAddr).
    { rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
    assert(HlookupBlockPEq: lookup blockParent (memory a) beqAddr = lookup blockParent (memory s0) beqAddr).
    { rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. }
    rewrite HlookupBlockCEq in *. rewrite HlookupBlockPEq in *.
    assert(HblockCMappeds0: In blockChild (getMappedBlocks child s0)).
    {
      destruct (beqAddr idPDchild child) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst child.
        pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in HblockCMapped. apply in_or_app.
        destruct HblockCMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    assert(HblockPMappeds0: In blockParent (getMappedBlocks pdparent s0)).
    {
      destruct (beqAddr idPDchild pdparent) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst pdparent.
        pose proof (getMappedBlocksEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in HblockPMapped. apply in_or_app.
        destruct HblockPMapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedBlocksEqRemove with (block:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    assert(HgetChildrenEq: getChildren pdparent a = getChildren pdparent s0).
    { apply getChildrenEqRemove with idPDchild blockToRemove; trivial. }
    rewrite HgetChildrenEq in *.
    specialize(HchildBlockProps child pdparent blockChild startChild endChild blockParent startParent endParent
      HparentIsPart HchildIsChild HblockCMappeds0 HstartC HendC HPflagC HblockPMappeds0 HstartP HendP HPflagP
      HlebStarts HgebEnds).
    destruct HchildBlockProps as (HcheckChild & HPDchildNotNull & HchildLocNotNull & HaccIfBounds).
    assert(HlookupSh1Eq: lookup (CPaddr (blockParent+sh1offset)) (memory a) beqAddr
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

Lemma kernelsAreNotAccessiblePreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
(*noDupKSEntriesList s0
-> nullAddrExists s0
-> noDupMappedBlocksList s0
-> DisjointKSEntries s0
-> wellFormedFstShadowIfBlockEntry s0
-> wellFormedBlock s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
-> noDupMappedPaddrList s0
->*) kernelsAreNotAccessible s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> kernelsAreNotAccessible s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList (*HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 Hwell HparentOfPart HisChild HnoChild HnoDupMappedP*) HkernNotAcc HblocksList
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
  assert(HkernNotAccA: kernelsAreNotAccessible a).
  { (* BEGIN kernelsAreNotAccessible s *)
    intros block startaddr Hstart HPflag HstartIsKS. unfold bentryPFlag in *.
    assert(HbeqBlocks: blockToRemove <> block).
    {
      intro Hcontra. subst block. destruct HBE as [bentry0 [newEnd [l (_ & _ & Hlookups)]]].
      unfold bentryPFlag in *. rewrite Hlookups in *. simpl in *. congruence.
    }
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryAFlag.
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
    (* END kernelsAreNotAccessible *)
  }
  rewrite HblocksListEq in Hlast. apply IL.lastRec in Hlast.
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

Lemma partitionsIsolationPreservedRemoveRec s s0 idPDchild blockToRemove statesList blocksList:
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
-> partitionsIsolation s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> partitionsIsolation s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 (*Hwell HparentOfPart HisChild HnoChild HnoDupMappedP*) HPI HblocksList
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
  assert(HPIA: partitionsIsolation a).
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren addr HaddrUsed1.
    rewrite HgetPartsEqsA in *. assert(HgetChildrenEq: getChildren pdparent a = getChildren pdparent s0).
    { apply getChildrenEqRemove with idPDchild blockToRemove; trivial. }
    rewrite HgetChildrenEq in *. assert(HaddrUsed1s0: In addr (getUsedPaddr child1 s0)).
    {
      unfold getUsedPaddr in *. apply in_or_app. apply in_app_or in HaddrUsed1.
      rewrite <-getConfigPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=a) (removePart:=idPDchild); trivial.
      destruct HaddrUsed1 as [Hconfig | Hmapped]; auto. right. destruct (beqAddr idPDchild child1) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst child1.
        pose proof (getMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRMapped HBE
          Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
        rewrite HeqA in *. rewrite Heqs0. apply in_app_or in Hmapped. apply in_or_app.
        destruct Hmapped; auto. right. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=a)
          (removePart:=idPDchild); trivial.
    }
    specialize(HPI pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren addr HaddrUsed1s0).
    contradict HPI. unfold getUsedPaddr in *. apply in_or_app. apply in_app_or in HPI.
    rewrite <-getConfigPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=a) (removePart:=idPDchild); trivial.
    destruct HPI as [Hconfig | Hmapped]; auto. right. destruct (beqAddr idPDchild child2) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. subst child2.
      pose proof (getMappedPaddrEqRemPartRemove blockToRemove a s0 idPDchild HnoDup HnoDupMapped HPDT HBTRMapped HBE
        Hsh1IsSHE HSHE HsceIsSCE HSCE HlookupsEq) as Heqs. destruct Heqs as [leftList [rightList (HeqA & Heqs0)]].
      rewrite HeqA in *. rewrite Heqs0. apply in_app_or in Hmapped. apply in_or_app.
      destruct Hmapped; auto. right. apply in_or_app. auto.
    - rewrite <-beqAddrFalse in *. rewrite <-getMappedPaddrEqRemove with (blockToRemove:=blockToRemove) (s:=a)
        (removePart:=idPDchild); trivial.
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
(*-> wellFormedBlock s0
-> parentOfPartitionIsPartition s0
-> isChild s0
-> noChildImpliesAddressesNotShared s0
-> noDupMappedPaddrList s0*)
-> kernelDataIsolation s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> kernelDataIsolation s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 (*Hwell HparentOfPart HisChild HnoChild HnoDupMappedP*) HKDI HblocksList
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
(*-> wellFormedBlock s0
-> parentOfPartitionIsPartition s0
-> isChild s0*)
-> noChildImpliesAddressesNotShared s0
(*-> noDupMappedPaddrList s0*)
-> kernelDataIsolation s0
-> verticalSharing s0
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> nullAddr = last blocksList blockToRemove
-> verticalSharing s.
Proof.
revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove blocksList HnoDup Hnull
  HnoDupMapped Hdisjoint HwellSh1 HnoDupTree (*Hwell HparentOfPart HisChild*) HnoChild (*HnoDupMappedP*) HKDI HVS
  HblocksList Hlast.
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

Lemma getMappedInclRemoveRecNotInList block s s0 idPDchild blockToRemove statesList blocksList:
In block (getMappedBlocks idPDchild s)
-> noDupKSEntriesList s0
-> ~In block (blockToRemove::blocksList)
-> removedBlockRec s s0 idPDchild blockToRemove statesList blocksList
-> In block (getMappedBlocks idPDchild s0).
Proof.
intro HblockMapped. revert s0 blockToRemove blocksList. induction statesList; simpl; intros s0 blockToRemove
  blocksList HnoDup HblockNotIn HblocksList; try(destruct HblocksList; subst s; assumption).
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
{{fun isBlockRemoved s => (isBlockRemoved = false -> P s /\ consistency s)
    /\ (isBlockRemoved = true -> consistency1 s (*TODO that will be modified, not entirely true*)
        /\ exists statesList blocksList s0,
            removedBlockRec s s0 idPDchild blockToRemoveInChildAddr statesList blocksList
            /\ nullAddr = last blocksList blockToRemoveInChildAddr
            /\ P s0)
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
    eapply weaken. apply ret. intros s Hprops. simpl. split; intro; try(exfalso; congruence). intuition.
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
      { (** writeAccessibleRec *)
        eapply weaken. apply writeAccessibleRec. intros s Hprops. simpl.
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
              apply getMappedInclRemoveRecNotInList; trivial.
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

        split.
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

        split.
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

        split.
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

        assert(consistency1 s).
        {
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

          assert(PDTIfPDFlag s).
          { (* BEGIN PDTIfPDFlag s *)
            assert(Hcons0: PDTIfPDFlag s1) by (unfold consistency1 in *; intuition).
            intros block sh1entryaddrBis HcheckChild. admit. (*TODO HERE broken*)
            
            
            
            
            (* END PDTIfPDFlag *)
          }

          assert(AccessibleNoPDFlag s).
          { (* BEGIN AccessibleNoPDFlag s *)
            assert(Hcons0: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
            intros block sh1entryaddrBis HblockIsBE Hsh1 HAflag. admit. (*TODO HERE broken*)
            
            
            
            
            (* END AccessibleNoPDFlag *)
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
              rewrite <-beqAddrTrue in HbeqBTRNextAddr. (*TODO HERE*) subst nextKSAddr.
            
            
            
            
            
            (* END NextKSOffsetIsPADDR *)
          }

          assert(NoDupInFreeSlotsList s).
          { (* BEGIN NoDupInFreeSlotsList s *)
            assert(Hcons0: NoDupInFreeSlotsList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros partition pdentry HlookupPart.
            
            
            
            
            (* END NoDupInFreeSlotsList *)
          }

          assert(freeSlotsListIsFreeSlot s).
          { (* BEGIN freeSlotsListIsFreeSlot s *)
            assert(Hcons0: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition).
            intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
            
            
            
            
            (* END freeSlotsListIsFreeSlot *)
          }

          assert(DisjointFreeSlotsLists s).
          { (* BEGIN DisjointFreeSlotsLists s *)
            assert(Hcons0: DisjointFreeSlotsLists s0) by (unfold consistency1 in *; intuition).
            intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
            
            
            
            
            (* END DisjointFreeSlotsLists *)
          }

          assert(inclFreeSlotsBlockEntries s).
          { (* BEGIN inclFreeSlotsBlockEntries s *)
            assert(Hcons0: inclFreeSlotsBlockEntries s0) by (unfold consistency1 in *; intuition).
            intros partition HpartIsPDT.
            
            
            
            
            (* END inclFreeSlotsBlockEntries *)
          }

          assert(DisjointKSEntries s).
          { (* BEGIN DisjointKSEntries s *)
            assert(Hcons0: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
            
            
            
            
            (* END DisjointKSEntries *)
          }

          assert(noDupPartitionTree s).
          { (* BEGIN noDupPartitionTree s *)
            assert(Hcons0: noDupPartitionTree s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            
            
            
            
            
            (* END noDupPartitionTree *)
          }

          assert(isParent s).
          { (* BEGIN isParent s *)
            assert(Hcons0: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros partition pdparent HparentIsPart HpartIsChild.
            
            
            
            
            (* END isParent *)
          }

          assert(isChild s).
          { (* BEGIN isChild s *)
            assert(Hcons0: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot.
            
            
            
            
            (* END isChild *)
          }

          assert(noDupKSEntriesList s).
          { (* BEGIN noDupKSEntriesList s *)
            assert(Hcons0: noDupKSEntriesList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros partition HpartIsPDT.
            
            
            
            
            (* END noDupKSEntriesList *)
          }

          assert(noDupMappedBlocksList s).
          { (* BEGIN noDupMappedBlocksList s *)
            assert(Hcons0: noDupMappedBlocksList s0) by (unfold consistency1 in *; intuition).
            intros partition HpartIsPDT.
            
            
            
            
            (* END noDupMappedBlocksList *)
          }

          assert(wellFormedBlock s).
          { (* BEGIN wellFormedBlock s *)
            assert(Hcons0: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros block startaddr endaddr HPflag HstartBlock HendBlock.
            
            
            
            
            (* END wellFormedBlock *)
          }

          assert(parentOfPartitionIsPartition s).
          { (* BEGIN parentOfPartitionIsPartition s *)
            assert(Hcons0: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
            intros partition pdentry HlookupPart.
            
            
            
            
            (* END parentOfPartitionIsPartition *)
          }

          assert(NbFreeSlotsISNbFreeSlotsInList s).
          { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
            assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros partition nbfreeslots HpartIsPDT HnbFree.
            
            
            
            
            (* END NbFreeSlotsISNbFreeSlotsInList *)
          }

          assert(maxNbPrepareIsMaxNbKernels s).
          { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
            assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by (unfold consistency1 in *; intuition).
            intros partition kernList HlistOfKerns.
            
            
            
            
            (* END maxNbPrepareIsMaxNbKernels *)
          }

          assert(blockInChildHasAtLeastEquivalentBlockInParent s).
          { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
            assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0)
              by (unfold consistency1 in *; intuition). intros pdparent child block startChild endChild
              HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild.
            
            
            
            
            (* END blockInChildHasAtLeastEquivalentBlockInParent *)
          }

          assert(partitionTreeIsTree s).
          { (* BEGIN partitionTreeIsTree s *)
            assert(Hcons0: partitionTreeIsTree s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
            
            
            
            
            (* END partitionTreeIsTree *)
          }

          assert(kernelEntriesAreValid s).
          { (* BEGIN kernelEntriesAreValid s *)
            assert(Hcons0: kernelEntriesAreValid s0) by (unfold consistency1 in *; intuition).
            intros kernel idx HkernIsKS Hidx.
            
            
            
            
            (* END kernelEntriesAreValid *)
          }

          assert(nextKernelIsValid s).
          { (* BEGIN nextKernelIsValid s *)
            assert(Hcons0: nextKernelIsValid s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros kernel HkernIsKS.
            
            
            
            
            (* END nextKernelIsValid *)
          }

          assert(noDupListOfKerns s).
          { (* BEGIN noDupListOfKerns s *)
            assert(Hcons0: noDupListOfKerns s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros partition kernList HlistOfKerns.
            
            
            
            
            (* END noDupListOfKerns *)
          }

          assert(MPUsizeIsBelowMax s).
          { (* BEGIN MPUsizeIsBelowMax s *)
            assert(Hcons0: MPUsizeIsBelowMax s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros partition MPUlist HMPU.
            
            
            
            
            (* END MPUsizeIsBelowMax *)
          }

          assert(originIsParentBlocksStart s).
          { (* BEGIN originIsParentBlocksStart s *)
            assert(Hcons0: originIsParentBlocksStart s0) by (unfold consistency1 in *; intuition).
            intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
            
            
            
            
            (* END originIsParentBlocksStart *)
          }

          assert(nextImpliesBlockWasCut s).
          { (* BEGIN nextImpliesBlockWasCut s *)
            assert(Hcons0: nextImpliesBlockWasCut s0) by (unfold consistency1 in *; intuition).
            intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
              Hsce HbeqNextNull Hnext HbeqPartRoot.
            
            
            
            
            (* END nextImpliesBlockWasCut *)
          }

          assert(blocksAddressesTypes s).
          { (* BEGIN blocksAddressesTypes s *)
            assert(Hcons0: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros block startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock.
            
            
            
            
            (* END blocksAddressesTypes *)
          }

          assert(notPDTIfNotPDflag s).
          { (* BEGIN notPDTIfNotPDflag s *)
            assert(Hcons0: notPDTIfNotPDflag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros block startaddr sh1entryaddr HstartBlock Hsh1 HPflag HPDflag HPDchild.
            
            
            
            
            (* END notPDTIfNotPDflag *)
          }

          assert(nextKernAddrIsInSameBlock s).
          { (* BEGIN nextKernAddrIsInSameBlock s *)
            assert(Hcons0: nextKernAddrIsInSameBlock s0) by (unfold consistency1 in *; intuition).
            intros block kernel startaddr endaddr HstartBlock HendBlock HPflagBlock HPDchildBlock HkernIsKS.
            
            
            
            
            (* END nextKernAddrIsInSameBlock *)
          }

          assert(blockBelongsToAPart s).
          { (* BEGIN blockBelongsToAPart s *)
            assert(Hcons0: blockBelongsToAPart s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros block HPflagBlock.
            
            
            
            
            (* END blockBelongsToAPart *)
          }

          assert(PDflagMeansNoChild s).
          { (* BEGIN PDflagMeansNoChild s *)
            assert(Hcons0: PDflagMeansNoChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros block HblockIsBE HPDflagBlock.
            
            
            
            
            (* END PDflagMeansNoChild *)
          }

          assert(nbPrepareIsNbKern s).
          { (* BEGIN nbPrepareIsNbKern s *)
            assert(Hcons0: nbPrepareIsNbKern s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros partition pdentry HlookupPart.
            
            
            
            
           (* END nbPrepareIsNbKern *)
          }

          assert(pdchildIsPDT s).
          { (* BEGIN pdchildIsPDT s *)
            assert(Hcons0: pdchildIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            intros part block sh1entryaddr idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
            
            
            
            
            (* END pdchildIsPDT *)
          }
          unfold consistency1. intuition.
        }

      }
      intro recWriteEnded. destruct recWriteEnded.

			-- (* case_eq recWriteEnded = true *)
				intros. simpl.
				{	(** ret *)
					eapply weaken. apply ret.
					intros. simpl. admit.
				}
			-- (* case_eq recWriteEnded = false *)
				intros. simpl.
				{ (** ret *)
					eapply weaken. apply ret.
					intros. simpl. admit.
				}
		* (* case recRemoveSubblocksEnded = false *)
			intros. simpl.
			{ (** ret *)
				eapply weaken. apply ret.
				intros. simpl. intuition.
			}
- (* case_eq isBlockCut = false *)
	intros. simpl.
	eapply bindRev.
	{ (** MAL.readBlockAccessibleFromBlockEntryAddr *)
		eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
		intros. simpl. split. apply H0. intuition.
	}
	intro addrIsAccessible.
	case_eq addrIsAccessible.
	+ (* case_eq addrIsAccessible = true *)
		intros. simpl. admit.
	+ (* case_eq addrIsAccessible = false *)
		intros. simpl.
		eapply weaken. apply ret.
		intros. simpl. intuition.
Admitted.
