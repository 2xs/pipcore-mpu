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
Require Import Proof.invariants.findBlockInKSWithAddr Proof.invariants.checkBlockCut freeSlot.
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
- destruct HblocksList as [blockChild [blocksListRec (HlistsEq & HbeqBlockNull & Hnext & HPDT & HBE & HSHE & HSCE &
    HlookupsEq & HblocksListRec)]]. assert(HblockIsBEA: isBE block a).
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

(*Lemma isBEEqRemoveRecRev block s s0 partition blockToRemove statesList blocksList:
isBE block s
-> removedBlockRec s s0 partition blockToRemove statesList blocksList
-> isBE block s0.
Proof.

Qed.*)

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

Lemma getMappedBlocksEqRemoveRec blockToRemove s s0 removePart statesList blocksList partition:
removePart <> partition
-> DisjointKSEntries s0
-> wellFormedBlock s0
-> wellFormedFstShadowIfBlockEntry s0
-> noDupKSEntriesList s0
-> nullAddrExists s0
-> AccessibleNoPDFlag s0
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
  Hdisjoint Hwell Hsh1IsSHE HnoDup Hnull HaccNoPD HnoDupMapped HnoDupPaddr HnextBlocksList HremovePartIsPart
  HblockTRMapped HblocksList.
- destruct HblocksList as (_ & Hs). subst s. reflexivity.
- destruct HblocksList as [blockChild [blocksListRec (HlistsEq & HbeqBlockNull & Hnext & HPDT & HBE & HSHE & HSCE &
    HlookupsEq & HblocksListRec)]]. assert(HblockTRIsBE: isBE blockToRemove s0).
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
  destruct HnextBlocksList as (HAflag & HPflag & HblockTRMappeds & HPDchild & HnextBis & HnextBlockSidePartial &
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
  + apply AccessibleNoPDFlagPreservedRemove with s0 removePart blockToRemove; trivial.
  + apply noDupMappedBlocksListPreservedRemove with s0 removePart blockToRemove; trivial.
  + apply noDupMappedPaddrListPreservedRemove with s0 removePart blockToRemove; trivial.
  + assert(HgetPartsEq: getPartitions multiplexer a = getPartitions multiplexer s0).
    {
      apply getPartitionsEqRemove with removePart blockToRemove; trivial.
      assert(Hsh1: sh1entryAddr blockToRemove (CPaddr (blockToRemove+sh1offset)) s0).
      {
        destruct HBE as [bentry0 [_ [_ (Hlookups0 & _)]]]. unfold sh1entryAddr. rewrite Hlookups0. reflexivity.
      }
      specialize(HaccNoPD blockToRemove (CPaddr (blockToRemove+sh1offset)) HblockTRIsBE Hsh1 HAflag). assumption.
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
    /\ exists statesList blocksList s0,
        removedBlockRec s s0 idPDchild firstBlockToRemove statesList blocksList
        /\ nullAddr = last blocksList firstBlockToRemove
        /\ P s0
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
    split; trivial. split; trivial. rewrite <-beqAddrTrue in *. subst blockToRemove.
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
      destruct Hblock as (HblockTRMapped & HAflag). (*TODO come here to add props about blockToRemove*)
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
      split; trivial. split; trivial. split; trivial. split; trivial.
    * destruct HblocksList as [blockChild [blocksListRec (HblocksListEq & HbeqFirstNull & Hnext & HPDTinit & HBEinit &
        HSHEinit & HSCEinit & HlookupsEqInit & HblocksList)]]. exists blockChild. exists (blocksListRec++[nextBlock]).
      rewrite HblocksListEq. split; auto. split; trivial. split; trivial. split; trivial. split; trivial.
      split; trivial. split; trivial. split; trivial. apply IHstatesList; trivial. rewrite HblocksListEq in Hlast.
      apply IL.lastRec in Hlast. assumption.
Qed.

Lemma removeSubblocksRec (idPDchild subblockAddr: paddr) P :
{{ fun s => P s /\ consistency s
						/\ isBE subblockAddr s (* to be removed *)}}
Internal.removeSubblocksRec idPDchild subblockAddr
{{fun recRemoveSubblocksEnded s => P s /\ consistency s}}.
Proof.
unfold removeSubblocksRec.
eapply weaken. apply removeSubblocksRecAux.
intros. simpl. intuition.
Qed.


Lemma removeBlockInChildAndDescendants (currentPart blockToRemoveInCurrPartAddr idPDchild
  blockToRemoveInChildAddr : paddr) P :
{{ fun s => P s /\ consistency s /\ isBE blockToRemoveInCurrPartAddr s
    /\ isBE blockToRemoveInChildAddr s
    /\ (exists partition, In blockToRemoveInCurrPartAddr (getMappedBlocks partition s)
        /\ In partition (getPartitions multiplexer s))
    /\ (exists sh1entryaddr,
        sh1entryPDchild sh1entryaddr idPDchild s
        /\ sh1entryAddr blockToRemoveInCurrPartAddr sh1entryaddr s
        /\ sh1entryInChildLocation sh1entryaddr blockToRemoveInChildAddr s)
    /\ beqAddr nullAddr blockToRemoveInChildAddr = false
    /\ beqAddr nullAddr idPDchild = false }}
Internal.removeBlockInChildAndDescendants currentPart blockToRemoveInCurrPartAddr idPDchild blockToRemoveInChildAddr
{{fun isBlockRemoved s => P s /\ consistency s }}.
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
    destruct Hprops as (((HP & Hconsist & HblockIsBE & HblockChildIsBE & Hpart & Hsh1 & HbeqNullBlock & HbeqNullChild)
      & Hstart) & [blockStart [blockOrigin [blockNext (Horigin & Hnext & HstartChild & HisCut)]]]). split; trivial.
    destruct Hpart as [partition (HblockMapped & HpartIsPart)]. rewrite beqAddrSym in *. rewrite <-beqAddrFalse in *.
    destruct Hsh1 as [sh1entryaddr (HPDchild & Hsh1 & HchildLoc)].
    assert(HchildIsChild: pdchildIsPDT s) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HchildIsChild partition blockToRemoveInCurrPartAddr sh1entryaddr idPDchild HpartIsPart HblockMapped
      Hsh1 HPDchild HbeqNullChild).
    assert(HlocMapped: childLocMappedInChild s) by (unfold consistency in *; unfold consistency2 in *; intuition).
    specialize(HlocMapped partition blockToRemoveInCurrPartAddr sh1entryaddr blockToRemoveInChildAddr idPDchild
      HpartIsPart HblockMapped Hsh1 HPDchild HchildLoc HbeqNullChild HbeqNullBlock).
    assert(HchildIsPart: In idPDchild (getPartitions multiplexer s)).
    {
      apply IL.childrenPartitionInPartitionList with partition; trivial.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    split. exists idPDchild. auto. split; trivial. instantiate(1 := blockToRemoveInChildAddr). exists [].
    simpl. split; trivial.
	}
	intro isRemovePossible. destruct (negb isRemovePossible) eqn:HremovePossible.
  + (* case_eq isRemovePossible = false *)
    eapply weaken. apply ret. intros s Hprops. simpl. intuition.
  + (* case_eq isRemovePossible = true *)
    eapply bindRev.
    { (** removeSubblocksRec *)
      eapply weaken. (*TODO HERE*) apply removeSubblocksRec.
      intros. simpl. split. apply H1. intuition.
    }
    intro recRemoveSubblocksEnded.
			case_eq recRemoveSubblocksEnded.
			* (* case_eq recRemoveSubblocksEnded = true *)
				intros. simpl.
				eapply bindRev.
				{ (** MAL.writeBlockAccessibleFromBlockEntryAddr *)
						eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr.
						intros. simpl. admit.
				}
				intros.
				eapply bindRev. admit.
			(*{ (** writeAccessibleRec *)
				eapply weaken. apply writeAccessibleRec.
				intros. simpl. split. apply H1. intuition.
			}*)
			intro recWriteEnded.
			case_eq recWriteEnded.
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
		* (* case_eq recRemoveSubblocksEnded = false *)
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
