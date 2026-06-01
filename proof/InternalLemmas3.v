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

(** * Summary
    This file contains several internal lemmas to help prove invariants *)
From Stdlib Require List Lia Arith Classical_Prop EqNat.
Import Lia Compare_dec Lists.List PeanoNat.
Require Import Model.ADT Model.Monad Model.MAL Model.Lib Core.Internal.

Require Import Proof.Isolation Proof.Consistency Proof.StateLib.
Require Import DependentTypeLemmas InternalLemmas InternalLemmas2.

Require Import Stdlib.Logic.ProofIrrelevance Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Program.Equality.

Module IL := InternalLemmas.

Import List.ListNotations.

Lemma childrenArePDTPartial partition child s blockToDelete blockTDStart:
(forall idPDchild sh1entryaddr part, idPDchild <> blockToDelete
    -> In part (getPartitions multiplexer s)
    -> In idPDchild (getMappedBlocks part s)
    -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
    -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
        /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> In partition (getPartitions multiplexer s)
-> In child (getChildren partition s)
-> bentryStartAddr blockToDelete blockTDStart s
-> child <> blockTDStart
-> isPDT child s.
Proof.
intros HPDTIfPDFlag HpartIsPart Hchild HstartBTD HbeqChildBTDS. unfold getChildren in *.
destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
assert(Hres: exists block, In block (getMappedBlocks partition s) /\ bentryStartAddr block child s
  /\ sh1entryPDflag (CPaddr (block+sh1offset)) true s).
{
  induction (getMappedBlocks partition s); try(simpl in *; exfalso; congruence).
  unfold getPDs in *. simpl in *. destruct (childFilter s a) eqn:Hcheck;
    try(specialize(IHl Hchild); destruct IHl as [block (HblockIn & Hstart)]; exists block; auto).
  simpl in *. destruct Hchild as [HchildFromA | Hchild];
    try(specialize(IHl Hchild); destruct IHl as [block (HblockIn & Hstart)]; exists block; auto).
  unfold childFilter in Hcheck. exists a. split; auto. unfold bentryStartAddr.
  destruct (lookup a (memory s) beqAddr) eqn:Hlookupa ; try(congruence).
  destruct v eqn:Hv ; try(congruence). split; auto. unfold sh1entryPDflag. unfold CPaddr.
  unfold Paddr.addPaddrIdx in *. destruct (le_dec (a + sh1offset) maxAddr); try(exfalso; congruence).
  replace {| p := a + sh1offset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 a sh1offset l0 |}
    with {| p := a + sh1offset; Hp := ADT.CPaddr_obligation_1 (a + sh1offset) l0 |} in *; try(f_equal).
  destruct (lookup {| p := a + sh1offset; Hp := ADT.CPaddr_obligation_1 (a + sh1offset) l0 |} (memory s) beqAddr);
    try(congruence). destruct v0; congruence.
}
destruct Hres as [block (HblockMapped & Hstart & HPDflag)].
assert(Hprop: true = checkChild block s (CPaddr (block + sh1offset))
  /\ sh1entryAddr block (CPaddr (block + sh1offset)) s).
{
  unfold checkChild. unfold sh1entryAddr. unfold sh1entryPDflag in *. unfold bentryStartAddr in *.
  destruct (lookup block (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). split; trivial.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). assumption.
}
assert(HbeqBlockBTD: block <> blockToDelete).
{
  intro. subst block. unfold bentryStartAddr in *.
  destruct (lookup blockToDelete (memory s) beqAddr); try(congruence). destruct v; congruence.
}
specialize (HPDTIfPDFlag block (CPaddr (block+sh1offset)) partition HbeqBlockBTD HpartIsPart HblockMapped Hprop).
destruct HPDTIfPDFlag as (_ & _ & [startB (HstartB & Hres)]). unfold bentryStartAddr in *. unfold entryPDT in *.
destruct (lookup block (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
rewrite <-Hstart in *. subst startB. unfold isPDT. destruct (lookup child (memory s) beqAddr); try(congruence).
destruct v; try(congruence). trivial.
Qed.

Lemma getPartitionsAuxEqBEPDflagFalsePartial partition addr newEntry bentry0 sh1entryaddr s0 n blockToDelete
  blockTDStart:
isPDT partition s0
-> lookup addr (memory s0) beqAddr = Some (BE bentry0)
-> (forall idPDchild sh1entryaddr part, idPDchild <> blockToDelete
    -> In part (getPartitions multiplexer s0)
    -> In idPDchild (getMappedBlocks part s0)
    -> true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0
    -> bentryAFlag idPDchild false s0 /\ bentryPFlag idPDchild true s0
        /\ (exists startaddr, bentryStartAddr idPDchild startaddr s0 /\ entryPDT idPDchild startaddr s0))
-> bentryStartAddr blockToDelete blockTDStart s0
-> lookup blockTDStart (memory s0) beqAddr = None
-> sh1entryAddr addr sh1entryaddr s0
-> sh1entryPDflag sh1entryaddr false s0
-> noDupPartitionTree s0
-> In partition (getPartitions multiplexer s0)
-> getPartitionsAux n partition {|
                                  currentPartition := currentPartition s0;
                                  memory := add addr (BE newEntry) (memory s0) beqAddr
                                |}
    = getPartitionsAux n partition s0.
Proof.
revert partition. set (s := {| currentPartition := currentPartition s0; memory := _ |}).
induction n; intros partition HpartIsPDT HlookupAddrs0 HPDTIfPDflagPartial HstartBTDs0 HlookupStarts0; intros;
  simpl; f_equal.
assert(HChildrenEq: (getChildren partition s) = (getChildren partition s0)).
{
  apply getChildrenEqBEPDflagFalse with bentry0 sh1entryaddr; trivial.
}
rewrite HChildrenEq. clear HChildrenEq.
assert(HchildrenArePDT : forall child, In child (getChildren partition s0) -> child <> blockTDStart
  -> isPDT child s0).
{
  intros. apply childrenArePDTPartial with partition blockToDelete blockTDStart; trivial.
}
assert(HchildrenAreParts: forall child, In child (getChildren partition s0)
  -> In child (getPartitions multiplexer s0)).
{
  intros child HchildIsChild. apply childrenPartitionInPartitionList with partition; trivial.
}
assert(HlookupStart: lookup blockTDStart (memory s) beqAddr = None).
{
  simpl. destruct (beqAddr addr blockTDStart) eqn:HbeqAddrStart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqAddrStart. subst addr. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
}
induction (getChildren partition s0); simpl; trivial. f_equal.
- destruct (beqAddr a blockTDStart) eqn:HbeqAStart.
  + rewrite <-DTL.beqAddrTrue in HbeqAStart. subst a. clear IHn. clear IHl. destruct n; simpl; f_equal.
    unfold getChildren. rewrite HlookupStart. rewrite HlookupStarts0. reflexivity.
  + simpl in *. rewrite <-beqAddrFalse in *. eapply IHn; trivial.
    * apply HchildrenArePDT; auto.
    * apply HchildrenAreParts; auto.
- simpl in *. apply IHl; intuition.
Qed.

Lemma getPartitionsEqBEPDflagFalse partition addr newEntry bentry0 sh1entryaddr s0 blockToDelete blockTDStart:
isPDT partition s0
-> (forall idPDchild sh1entryaddr part, idPDchild <> blockToDelete
    -> In part (getPartitions multiplexer s0)
    -> In idPDchild (getMappedBlocks part s0)
    -> true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0
    -> bentryAFlag idPDchild false s0 /\ bentryPFlag idPDchild true s0
        /\ (exists startaddr, bentryStartAddr idPDchild startaddr s0 /\ entryPDT idPDchild startaddr s0))
-> bentryStartAddr blockToDelete blockTDStart s0
-> lookup blockTDStart (memory s0) beqAddr = None
-> lookup addr (memory s0) beqAddr = Some (BE bentry0)
-> sh1entryAddr addr sh1entryaddr s0
-> sh1entryPDflag sh1entryaddr false s0
-> noDupPartitionTree s0
-> In partition (getPartitions multiplexer s0)
-> getPartitions partition {|
                              currentPartition := currentPartition s0;
                              memory := add addr (BE newEntry) (memory s0) beqAddr
                            |}
    = getPartitions partition s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}).
intros HPDTs0 HPDTIfPDflags0 HstartBTD HlookupStart Hlookupaddrs0 Hsh1addrs0 Hpdflags0 HnoDupTree HpartIsPart.
unfold getPartitions.
apply getPartitionsAuxEqBEPDflagFalsePartial with bentry0 sh1entryaddr blockToDelete blockTDStart; trivial.
Qed.

Lemma firstFreeSlotPointerIsFirstFreeLight (pd:paddr) (s:state) (pdentry:PDTable) (slotListPd:list optionPaddr)
                                      (nbfree:index):
slotListPd = getFreeSlotsList pd s
-> lookup pd (memory s) beqAddr = Some (PDT pdentry)
-> firstfreeslot pdentry <> nullAddr
-> length (getFreeSlotsList pd s) = nbfree
-> pdentryNbFreeSlots pd nbfree s
-> FirstFreeSlotPointerIsBEAndFreeSlot s
-> exists remainsSlotsList b newNbFree,
    getFreeSlotsList pd s = SomePaddr (firstfreeslot pdentry)::remainsSlotsList
    /\ lookup (firstfreeslot pdentry) (memory s) beqAddr = Some (BE b)
    /\ StateLib.Index.pred (nbfreeslots pdentry) = Some newNbFree
    /\ remainsSlotsList = getFreeSlotsListRec maxIdx (endAddr (blockrange b)) s newNbFree.
Proof.
intros HgetFreeSlotsList HlookupPd HfirstFreeNotNull HnbfreeIsLength HnbfreeIsNbFreeSlots HfirstFreeBE.
assert(Hsucc: maxIdx + 1 = S maxIdx) by lia.
destruct (getFreeSlotsList pd s) as [ | firstSlotPd slotList] eqn:HfreeSlotsListsPd;
  unfold getFreeSlotsList in HfreeSlotsListsPd; rewrite HlookupPd in HfreeSlotsListsPd;
  rewrite beqAddrFalse in HfirstFreeNotNull; rewrite HfirstFreeNotNull in HfreeSlotsListsPd;
  rewrite FreeSlotsListRec_unroll in HfreeSlotsListsPd; unfold getFreeSlotsListAux in HfreeSlotsListsPd;
  rewrite Hsucc in HfreeSlotsListsPd.
{
  destruct (StateLib.Index.ltb (ADT.nbfreeslots pdentry) zero); try(exfalso; congruence).
  destruct (lookup (firstfreeslot pdentry) (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  - destruct (StateLib.Index.pred (ADT.nbfreeslots pdentry)); try(exfalso; congruence).
  - rewrite HfirstFreeNotNull in HfreeSlotsListsPd. congruence.
}
assert(HnbfreeIsPos: StateLib.Index.ltb (ADT.nbfreeslots pdentry) zero = false).
{
  unfold StateLib.Index.ltb. rewrite PeanoNat.Nat.ltb_nlt. unfold zero. intro Hcontra.
  apply indexLtZero with (ADT.nbfreeslots pdentry). assumption.
}
rewrite HnbfreeIsPos in HfreeSlotsListsPd. rewrite <-beqAddrFalse in HfirstFreeNotNull.
specialize(HfirstFreeBE pd pdentry HlookupPd HfirstFreeNotNull).
destruct HfirstFreeBE as [HfirstPisBE HfirstPisFree]. unfold isBE in HfirstPisBE.
destruct (lookup (firstfreeslot pdentry) (memory s) beqAddr) eqn:HlookupFirstFreeP; try(exfalso; congruence).
destruct v; try(exfalso; congruence). unfold pdentryNbFreeSlots in HnbfreeIsNbFreeSlots.
rewrite HlookupPd in HnbfreeIsNbFreeSlots. rewrite HnbfreeIsNbFreeSlots in *. simpl in HnbfreeIsLength.
assert(Hpred: exists newNbFree, StateLib.Index.pred (ADT.nbfreeslots pdentry) = Some newNbFree).
{
  unfold Index.pred in *. destruct (Compare_dec.gt_dec (ADT.nbfreeslots pdentry) 0); try(lia).
  set(newNbFree := {|
                     i := ADT.nbfreeslots pdentry - 1;
                     Hi := StateLib.Index.pred_obligation_1 (ADT.nbfreeslots pdentry) g
                   |}).
  exists newNbFree. reflexivity.
}
destruct Hpred as [newNbFree Hpred]. rewrite Hpred in *.
apply eq_sym in HfreeSlotsListsPd.
set(getFreeRemain:= getFreeSlotsListRec maxIdx (endAddr (blockrange b)) s newNbFree).
exists getFreeRemain. exists b. exists newNbFree. subst getFreeRemain. intuition.
Qed.

(*Lemma getPDsEqSHENotInListLight (block: paddr) newEntry s0 pdlist:
nullAddrExists s0
-> isSHE (CPaddr (block+sh1offset)) s0
-> ~In block pdlist
-> getPDs pdlist {|
                   currentPartition := currentPartition s0;
                   memory := add (CPaddr (block+sh1offset)) (SHE newEntry) (memory s0) beqAddr
                 |}
    = getPDs pdlist s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}).
intros Hnull Hsh1IsSHE. unfold nullAddrExists in *. unfold isPADDR in *.
unfold getPDs. induction pdlist; simpl; intro HblockNotIn; try(reflexivity). apply not_or_and in HblockNotIn.
destruct HblockNotIn as (HbeqABlock & HblockNotIn).
destruct (beqAddr (CPaddr (block+sh1offset)) (CPaddr (a + sh1offset))) eqn:HbeqSh1s.
{
  rewrite <-DTL.beqAddrTrue in HbeqSh1s. exfalso. apply CPaddrAddEq in HbeqSh1s; try(congruence). intro Hcontra.
  rewrite Hcontra in *. unfold isSHE in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
  destruct v; congruence.
}
unfold isSHE in *. assert(HfilterEq: childFilter s a = childFilter s0 a).
{
  destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). eapply childFilterEqSHENotAddr with s1; trivial.
}
rewrite HfilterEq. specialize(IHpdlist HblockNotIn). destruct (childFilter s0 a); trivial. simpl.
rewrite IHpdlist. destruct (beqAddr (CPaddr (block+sh1offset)) a) eqn:HbeqSh1A.
- rewrite <-DTL.beqAddrTrue in HbeqSh1A. subst a.
  destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
Qed.*)

(*Lemma getChildrenEqSHENotInListLight partition (block: paddr) newEntry s0:
nullAddrExists s0
-> isSHE (CPaddr (block+sh1offset)) s0
-> (forall part, ~In block (getMappedBlocks part s0))
-> getChildren partition {|
                           currentPartition := currentPartition s0;
                           memory := add (CPaddr (block+sh1offset)) (SHE newEntry) (memory s0) beqAddr
                          |}
    = getChildren partition s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}).
intros Hnull Hsh1IsSHE HblockNotIn. unfold getChildren. simpl.
destruct (beqAddr (CPaddr (block + sh1offset)) partition) eqn:HbeqSh1Part.
{ (* sh1entryaddr = partition *)
  rewrite <- DTL.beqAddrTrue in HbeqSh1Part. rewrite HbeqSh1Part in *. unfold isSHE in *.
  destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
}
(* sh1entryaddr <> partition *)
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
assert(HmappedEq: getMappedBlocks partition s = getMappedBlocks partition s0).
{ eapply getMappedBlocksEqSHE; trivial. unfold isPDT. rewrite HlookupPart. trivial. }
rewrite HmappedEq in *. apply getPDsEqSHENotInListLight; trivial.
Qed.*)

Lemma getPartitionsAuxEqSHEPDflagNoChange partition (block: paddr) newEntry sh1entry0 s0 n :
lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr = Some(SHE sh1entry0)
-> PDflag newEntry = PDflag sh1entry0
-> getPartitionsAux n partition {|
                                  currentPartition := currentPartition s0;
                                  memory := add (CPaddr (block+sh1offset)) (SHE newEntry) (memory s0) beqAddr
                                |}
    = getPartitionsAux n partition s0.
Proof.
intros HlookupSh1 HPDflagEq.
revert partition. set (s := {| currentPartition := currentPartition s0; memory := _ |}).
induction n; simpl; intro partition; f_equal. unfold getChildren. unfold getMappedBlocks. unfold getKSEntries.
destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart.
- destruct v.
  1-3,5: simpl lookup; destruct (beqAddr (CPaddr (block + sh1offset)) partition) eqn:HbeqSh1Part; trivial;
    rewrite <-beqAddrFalse in *; rewrite removeDupIdentity; auto; rewrite HlookupPart; reflexivity.
  assert(HgetChildrenEq: getChildren partition s = getChildren partition s0).
  {
	  apply getChildrenEqSHE with sh1entry0; trivial. unfold isPDT. rewrite HlookupPart. trivial.
  }
  unfold getChildren in HgetChildrenEq. unfold getMappedBlocks in HgetChildrenEq. unfold getKSEntries in *.
  rewrite HgetChildrenEq. clear HgetChildrenEq. rewrite HlookupPart.
  destruct (beqAddr (structure p) nullAddr); trivial.
  induction (getPDs (filterPresent (filterOptionPaddr (getKSEntriesAux (maxNbPrepare + 1) (structure p) s0)) s0)
     s0); simpl; trivial. rewrite IHl. f_equal. apply IHn.
- simpl lookup. destruct (beqAddr (CPaddr (block + sh1offset)) partition) eqn:HbeqSh1Part; trivial.
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite HlookupPart. reflexivity.
Qed.

Lemma getPartitionsEqSHEPDflagNoChange partition (block: paddr) newEntry sh1entry0 s0:
lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr = Some(SHE sh1entry0)
-> PDflag newEntry = PDflag sh1entry0
-> getPartitions partition {|
                             currentPartition := currentPartition s0;
                             memory := add (CPaddr (block+sh1offset)) (SHE newEntry) (memory s0) beqAddr
                           |}
    = getPartitions partition s0.
Proof.
unfold getPartitions. apply getPartitionsAuxEqSHEPDflagNoChange.
Qed.

Lemma partitionsAuxAreStarts n part basePart s:
In part (getPartitionsAux n basePart s)
-> part <> basePart
-> exists pdparent blockParent, In pdparent (getPartitionsAux n basePart s)
    /\ In blockParent (getMappedBlocks pdparent s)
    /\ sh1entryPDflag (CPaddr (blockParent+sh1offset)) true s
    /\ bentryStartAddr blockParent part s.
Proof.
revert basePart. induction n; simpl; intros basePart HpartIsPart HbeqPartBase; try(exfalso; congruence).
destruct HpartIsPart as [Hcontra | HpartIsPart]; try(exfalso; congruence).
assert(HchildrenAreStarts: forall child, In child (getChildren basePart s)
  -> exists block, In block (getMappedBlocks basePart s)
      /\ sh1entryPDflag (CPaddr (block+sh1offset)) true s /\ bentryStartAddr block child s).
{
  intros child HchildIsChild. unfold getChildren in HchildIsChild.
  destruct (lookup basePart (memory s) beqAddr); try(exfalso; simpl in *; congruence).
  destruct v; try(exfalso; simpl in *; congruence).
  induction (getMappedBlocks basePart s); simpl in *; try(exfalso; congruence). unfold getPDs in *. simpl in *.
  assert(Hrec: In child (getPDsPaddr (filter (childFilter s) l) s)
    -> exists block, (a = block \/ In block l)
        /\ sh1entryPDflag (CPaddr (block + sh1offset)) true s /\ bentryStartAddr block child s).
  {
    intro Hchild. specialize(IHl Hchild). destruct IHl as [block (HblockIn & HPDflag & Hstart)]. exists block. auto.
  }
  destruct (childFilter s a) eqn:HchildF; try(apply Hrec; assumption). simpl in *. unfold childFilter in *.
  destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(exfalso; congruence). destruct v; try(exfalso; congruence).
  destruct HchildIsChild as [HchildIsStart | HchildIsChild]; try(apply Hrec; assumption). exists a. split; auto.
  unfold bentryStartAddr. rewrite HlookupA. split; auto. unfold sh1entryPDflag. unfold Paddr.addPaddrIdx in *.
  unfold CPaddr. destruct (le_dec (a + sh1offset) maxAddr); try(exfalso; congruence).
  assert(Heq: StateLib.Paddr.addPaddrIdx_obligation_1 a sh1offset l0 = ADT.CPaddr_obligation_1 (a + sh1offset) l0)
    by (apply proof_irrelevance). rewrite Heq in *.
  destruct (lookup {| p := a + sh1offset; Hp := ADT.CPaddr_obligation_1 (a + sh1offset) l0 |} (memory s) beqAddr);
    try(congruence). destruct v; congruence.
}
induction (getChildren basePart s); simpl in *; try(exfalso; congruence).
assert(HchildrenAreStartsRec: forall child, In child l
  -> exists block, In block (getMappedBlocks basePart s)
       /\ sh1entryPDflag (CPaddr (block + sh1offset)) true s /\ bentryStartAddr block child s).
{ intros. apply HchildrenAreStarts; auto. }
assert(Hrec: In part (flat_map (fun p : paddr => getPartitionsAux n p s) l)
  -> exists pdparent blockParent,
      (basePart = pdparent
        \/ In pdparent (getPartitionsAux n a s ++ flat_map (fun p : paddr => getPartitionsAux n p s) l))
      /\ In blockParent (getMappedBlocks pdparent s)
      /\ sh1entryPDflag (CPaddr (blockParent+sh1offset)) true s
      /\ bentryStartAddr blockParent part s).
{
  intro HpartIsPartRec. specialize(IHl HpartIsPartRec HchildrenAreStartsRec).
  destruct IHl as [pdparent [blockParent (HparentIsPart & HblockPMapped & HPDflagP & HstartP)]]. exists pdparent.
  exists blockParent. split; auto. destruct HparentIsPart as [HparentIsBase | HparentIsPart]; auto. right.
  apply in_or_app. auto.
}
apply in_app_or in HpartIsPart. destruct HpartIsPart as [HpartInA | HpartIsPart]; try(apply Hrec; assumption).
destruct (beqAddr part a) eqn:HbeqPartA.
- rewrite <-DTL.beqAddrTrue in HbeqPartA. subst a. assert(Htriv: part = part \/ In part l) by auto.
  specialize(HchildrenAreStarts part Htriv). destruct HchildrenAreStarts as [blockP Hprops]. exists basePart.
  exists blockP. auto.
- rewrite <-beqAddrFalse in *. specialize(IHn a HpartInA HbeqPartA).
  destruct IHn as [pdparent [blockP (HparentIsPart & Hprops)]]. exists pdparent. exists blockP. split; trivial.
  right. apply in_or_app. auto.
Qed.

Lemma partitionsAreStarts part s:
In part (getPartitions multiplexer s)
-> part <> multiplexer
-> exists pdparent blockParent, In pdparent (getPartitions multiplexer s)
    /\ In blockParent (getMappedBlocks pdparent s)
    /\ sh1entryPDflag (CPaddr (blockParent+sh1offset)) true s
    /\ bentryStartAddr blockParent part s.
Proof.
unfold getPartitions. apply partitionsAuxAreStarts.
Qed.

Lemma partitionGivesParentsListAux n part newRoot s:
isPADDR nullAddr s
-> isParent s
-> parentOfPartitionIsPartition s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> noDupPartitionTree s
-> In newRoot (getPartitions multiplexer s)
-> In part (getPartitionsAux (S n) newRoot s)
-> In newRoot (part::filterOptionPaddr (completeParentsListRec n part s)).
Proof.
intros Hnull HisParent HparentOfPart HPDTIfPDFlag HmultIsPDT HnoDupTree. revert newRoot.
induction n; intros newRoot HrootIsPart HpartIsPart.
- simpl in *. destruct HpartIsPart as [Heq | Hcontra]; auto. right.
  induction (getChildren newRoot s); simpl in *; congruence.
- set(nextN := S n). fold nextN in HpartIsPart. fold nextN in IHn. cbn -[nextN nullAddr] in *.
  destruct HpartIsPart as [Heq | HpartIsPart]; auto. right.
  assert(Hchildren: forall child, In child (getChildren newRoot s)
    -> pdentryParent child newRoot s /\ beqAddr child constantRootPartM = false
        /\ In child (getPartitions multiplexer s)).
  {
    intros child HchildIsChild. rewrite <-beqAddrFalse. specialize(HisParent child newRoot HrootIsPart HchildIsChild).
    split; trivial. unfold pdentryParent in *.
    destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild). rewrite <-HisParent in *.
    destruct HparentOfPart as (HparentIsPart & HparentOfRoot & HbeqNewRootChild).
    assert(HbeqChildRoot: child <> constantRootPartM).
    {
      intro Hcontra. specialize(HparentOfRoot Hcontra). assert(isPDT newRoot s).
      { apply partitionsArePDT; trivial. }
      rewrite HparentOfRoot in *. unfold isPADDR in *. unfold isPDT in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    split; trivial. apply childrenPartitionInPartitionList with newRoot; trivial.
  }
  induction (getChildren newRoot s); cbn -[nextN] in *; try(exfalso; congruence).
  assert(HchildrenRec: forall child, In child l
   -> pdentryParent child newRoot s /\ beqAddr child constantRootPartM = false
        /\ In child (getPartitions multiplexer s)).
  { intros. apply Hchildren; auto. }
  assert(Hrec: In part (flat_map (fun p : paddr => getPartitionsAux nextN p s) l)
    -> In newRoot (filterOptionPaddr (completeParentsListRec nextN part s))).
  { intro. apply IHl; assumption. }
  apply in_app_or in HpartIsPart. destruct HpartIsPart as [HpartIsPartA | HpartIsPart]; try(apply Hrec; assumption).
  assert(Htriv: a = a \/ In a l) by auto. specialize(Hchildren a Htriv).
  destruct Hchildren as (Hparent & HbeqARoot & HaIsPart). specialize(IHn a HaIsPart HpartIsPartA).
  destruct IHn as [Heq | IHn].
  + subst a. simpl. unfold pdentryParent in *. destruct (lookup part (memory s) beqAddr); try(simpl; congruence).
    destruct v; try(simpl; congruence). rewrite HbeqARoot. simpl. rewrite <-Hparent. auto.
  + replace nextN with (n+1); try(lia). apply completeParentsListRecApp with a; trivial. simpl.
    unfold pdentryParent in *. destruct (lookup a (memory s) beqAddr); try(simpl; congruence).
    destruct v; try(simpl; congruence). rewrite HbeqARoot. simpl. rewrite <-Hparent. auto.
Qed.

Lemma ancestorChild pdparent n basePart s:
isChild s
-> parentOfPartitionIsPartition s
-> In pdparent (filterOptionPaddr (completeParentsListRec n basePart s))
-> In basePart (getPartitions multiplexer s)
-> exists child, In child (getChildren pdparent s)
      /\ In child (basePart::filterOptionPaddr (completeParentsListRec n basePart s)).
Proof.
intros HisChild HparentOfPart. revert basePart.
induction n; simpl; intros basePart HparentIsAnc HbaseIsPart; try(exfalso; congruence).
destruct (lookup basePart (memory s) beqAddr) eqn:HlookupBase; try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
destruct (beqAddr basePart constantRootPartM) eqn:HbeqBaseRoot; try(simpl in *; exfalso; congruence). simpl in *.
destruct (beqAddr (parent p) pdparent) eqn:HbeqParents.
- rewrite <-DTL.beqAddrTrue in HbeqParents. exists basePart. split; auto. rewrite <-beqAddrFalse in *.
  apply HisChild; trivial. unfold pdentryParent. rewrite HlookupBase. auto.
- rewrite <-beqAddrFalse in *. destruct HparentIsAnc as [Hcontra | HparentIsAnc]; try(exfalso; congruence).
  specialize(HparentOfPart basePart p HlookupBase). destruct HparentOfPart as (HparentIsPart & _).
  specialize(HparentIsPart HbeqBaseRoot). destruct HparentIsPart as (_ & HparentIsPart).
  specialize(IHn (parent p) HparentIsAnc HparentIsPart).
  destruct IHn as [child (HchildIsChild & HchildIsAnc)]. exists child. auto.
Qed.

Lemma mappedAddrIsInBloodline part1 part2 s:
isPADDR nullAddr s
-> isParent s
-> wellFormedBlock s
-> parentOfPartitionIsPartition s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> noDupPartitionTree s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupMappedPaddrList s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> partitionNotAutoMapped s
-> partitionsIsolation s
-> In part1 (getMappedPaddr part2 s)
-> In part2 (getPartitions multiplexer s)
-> In part1 (getPartitions multiplexer s)
-> part1 <> part2
-> In part2 (filterOptionPaddr (completeParentsList part1 s)).
Proof.
intros Hnull HisParent Hwell HparentOfPart HPDTIfPDFlag HmultIsPDT HnoDupTree Htree HnoDupMapped HnoDupMappedP
  HisChild HblockEquivP HpartNotMapped HPI Hpart1Mapped2 Hpart2IsPart Hpart1IsPart HbeqParts.
assert(HchildPaddrInclParent: childPaddrIsIntoParent s) by (apply blockInclImpliesAddrIncl; trivial).
destruct (beqAddr part1 multiplexer) eqn:HbeqPart1Mult.
{
  rewrite <-DTL.beqAddrTrue in HbeqPart1Mult. subst part1. exfalso.
  assert(HmultMappedMult: In multiplexer (getMappedPaddr multiplexer s)).
  {
    apply addrBelongToAncestors with part2; trivial. unfold getPartitions in Hpart2IsPart.
    replace (maxAddr+2) with (S (maxAddr+1)) in *; try(lia).
    apply partitionGivesParentsListAux in Hpart2IsPart; trivial. simpl in *.
    destruct Hpart2IsPart as [Hcontra | Hpart2IsPart]; try(exfalso; congruence). unfold completeParentsList.
    revert Hpart2IsPart. apply completeParentsListRecN; lia.
  }
  contradict HmultMappedMult. apply HpartNotMapped; trivial.
}
rewrite <-beqAddrFalse in *. pose proof (partitionsAreStarts part1 s Hpart1IsPart HbeqPart1Mult) as Hprops1.
destruct Hprops1 as [pdparent [blockParent (HparentIsPart & HblockPMapped & HPDflagP & HstartP)]].
assert(Hpart1MappedParent: In part1 (getMappedPaddr pdparent s)).
{
  apply addrInBlockIsMapped with blockParent; trivial.
  assert(Hprops: bentryPFlag blockParent true s /\ exists endaddr, bentryEndAddr blockParent endaddr s).
  {
    apply mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & Hpres)].
    unfold bentryPFlag. unfold bentryEndAddr. rewrite Hlookup. split; auto. exists (endAddr (blockrange bentry)).
    reflexivity.
  }
  destruct Hprops as (HPflagP & [endaddr HendP]). specialize(Hwell blockParent part1 endaddr HPflagP HstartP HendP).
  destruct Hwell as (Hwell & _). simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
  destruct (lookup blockParent (memory s) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
  rewrite <-HstartP. rewrite <-HendP. rewrite app_nil_r. apply getAllPaddrBlockIncl; lia.
}
pose proof (addressesBloodline part1 part2 pdparent s HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT
  Hnull Htree HnoDupMapped HnoDupMappedP Hwell HisChild HblockEquivP HPI Hpart2IsPart HparentIsPart Hpart1Mapped2
  Hpart1MappedParent) as Hbloodline. assert(HparentIsPDT: isPDT pdparent s) by (apply partitionsArePDT; trivial).
assert(Hparent: pdentryParent part1 pdparent s).
{
  assert(Hpart1IsChild: In part1 (getChildren pdparent s)).
  {
    apply mappedPDTIsChild with blockParent (CPaddr (blockParent+sh1offset)); trivial.
    1,2: unfold checkChild; unfold sh1entryAddr; unfold bentryStartAddr in *;
      destruct (lookup blockParent (memory s) beqAddr); try(exfalso; congruence); destruct v;
      try(exfalso; congruence); trivial.
    unfold sh1entryPDflag in *.
    destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). assumption.
  }
  apply HisParent; trivial.
}
unfold multiplexer in HbeqPart1Mult. destruct Hbloodline as [Hpart2IsAnc | Hbloodline].
- assert(HparentsList: isParentsList s [pdparent] part1).
  {
    simpl. unfold isPDT in *. destruct (lookup pdparent (memory s) beqAddr); try(congruence).
    destruct v; try(congruence). split; try(split); trivial.
    unfold pdentryParent in *. destruct (lookup part1 (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists p0. auto.
  }
  assert(Hlast: pdparent = last [pdparent] part1) by auto.
  pose proof (completeParentsListAdd part1 pdparent [pdparent] s HparentOfPart Htree HparentsList Hlast) as Heq.
  rewrite Heq. apply in_or_app. auto.
- destruct (beqAddr pdparent part2) eqn:HbeqParent2.
  + rewrite <-DTL.beqAddrTrue in HbeqParent2. subst part2. unfold completeParentsList. simpl.
    unfold pdentryParent in *. destruct (lookup part1 (memory s) beqAddr); try(simpl; congruence).
    destruct v; try(simpl; congruence). rewrite beqAddrFalse in *. rewrite HbeqPart1Mult. simpl. auto.
  + rewrite <-beqAddrFalse in *. destruct Hbloodline as [Hcontra | HparentIsAnc]; try(exfalso; congruence). exfalso.
    assert(HancChild: exists child, In child (getChildren pdparent s)
      /\ In child (part2::filterOptionPaddr (completeParentsList part2 s))).
    {
      unfold completeParentsList in *. apply ancestorChild; trivial.
    }
    destruct HancChild as [child (HchildIsChild & HchildIsAnc)].
    assert(Hpart1MappedChild: In part1 (getMappedPaddr child s)).
    {
      simpl in HchildIsAnc. destruct HchildIsAnc as [HchildIs2 | HchildIsAnc].
      - subst child. assumption.
      - apply addrBelongToAncestors with part2; trivial.
        apply childrenPartitionInPartitionList with pdparent; trivial.
    }
    assert(Hpart1UsedChild: In part1 (getUsedPaddr child s)).
    {
      unfold getUsedPaddr. apply in_or_app. auto.
    }
    assert(child = part1).
    {
      destruct (beqAddr child part1) eqn:HbeqChildren; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
      rewrite <-beqAddrFalse in *. assert(Hpart1IsChild: In part1 (getChildren pdparent s)).
      { apply HisChild; trivial. }
      assert(Hpart1UsedIn1: In part1 (getUsedPaddr part1 s)).
      {
        unfold getUsedPaddr. apply in_or_app. left. unfold getConfigPaddr. apply in_or_app. left. simpl.
        unfold pdentryParent in *. destruct (lookup part1 (memory s) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence). rewrite app_nil_r. apply getAllPaddrBlockAuxIncl; try(lia).
        unfold Constants.PDStructureTotalLength. cbn. unfold CIndex. pose proof Constants.maxIdxBiggerThanMinBlock.
        destruct (le_dec 13 maxIdx); try(lia). simpl. lia.
      }
      specialize(HPI pdparent child part1 HparentIsPart HchildIsChild Hpart1IsChild HbeqChildren part1
        Hpart1UsedChild). congruence.
    }
    subst child. contradict Hpart1MappedChild. apply HpartNotMapped; trivial.
    (*in other proofs, use parentsListGivesPartitions ?*)
Qed.

Lemma mappedAddrIsInDescendants part1 part2 s:
isPADDR nullAddr s
-> isParent s
-> wellFormedBlock s
-> parentOfPartitionIsPartition s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> noDupPartitionTree s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupMappedPaddrList s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> partitionNotAutoMapped s
-> partitionsIsolation s
-> In part1 (getMappedPaddr part2 s)
-> In part2 (getPartitions multiplexer s)
-> In part1 (getPartitions multiplexer s)
-> part1 <> part2
-> In part1 (getPartitions part2 s).
Proof.
intros.
assert(Hbloodline: In part2 (filterOptionPaddr (completeParentsList part1 s))).
{ apply mappedAddrIsInBloodline; trivial. }
apply parentsListGivesPartitions; trivial. simpl. auto.
Qed.

(* Lemma getKSAuxInclAllPaddrKern n m kernel s addr:
In addr (filterOptionPaddr (getKSEntriesInStructAux n kernel s m))
-> exists offset, offset <= m /\ p addr = kernel + offset.
Proof.
revert kernel m. induction n; simpl; intros kernel m HaddrIn; try(exfalso; congruence).
unfold Paddr.addPaddrIdx in *. destruct (le_dec (kernel + m) maxAddr); try(simpl in *; exfalso; congruence).
set(block := {| p := kernel + m; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 kernel m l |}). fold block in HaddrIn.
destruct (lookup block (memory s) beqAddr); try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
Qed. *)

Lemma getKSEntriesInStructAuxEqNoImpact n (kernel:paddr) s s0 nbleft startaddr endaddr:
(forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
  -> ~ In addr (getAllPaddrBlockAux 0 kernel Constants.kernelStructureTotalLength))
-> nbleft < Constants.kernelStructureTotalLength
-> getKSEntriesInStructAux (nbleft+n) kernel s (CIndex nbleft)
    = getKSEntriesInStructAux (nbleft+n) kernel s0 (CIndex nbleft).
Proof.
intros HaddrsOutRange HaddrsInRange.
induction nbleft; intros HltLeftLenMax.
- destruct n; try(reflexivity). simpl. destruct (Paddr.addPaddrIdx kernel (CIndex 0)) eqn:HaddKernIdx; trivial.
  assert(HlookupPEq: lookup p (memory s) beqAddr = lookup p (memory s0) beqAddr).
  {
    apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra. contradict Hcontra. cbn in HaddKernIdx.
    unfold Paddr.addPaddrIdx in *. simpl in HaddKernIdx.
    destruct (le_dec (kernel + 0) maxAddr); try(exfalso; congruence).
    injection HaddKernIdx as HaddKernIdx. subst p. apply getAllPaddrBlockAuxIncl; simpl p; lia.
  }
  rewrite HlookupPEq. destruct (lookup p (memory s0) beqAddr); trivial.
- simpl. destruct (Paddr.addPaddrIdx kernel (CIndex (S nbleft))) eqn:HaddKernIdx; trivial.
  assert(Constants.kernelStructureTotalLength <= maxIdx).
  {
    pose proof maxNbFreeSlotsLessThanMaxIdx. pose proof maxNbPrepareNotZero.
    apply multImplLeb with maxNbPrepare; assumption.
  }
  assert(HlookupPEq: lookup p (memory s) beqAddr = lookup p (memory s0) beqAddr).
  {
    apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra. contradict Hcontra.
    unfold Paddr.addPaddrIdx in *. destruct (le_dec (kernel + CIndex (S nbleft)) maxAddr); try(exfalso; congruence).
    injection HaddKernIdx as HaddKernIdx. subst p. apply getAllPaddrBlockAuxIncl; simpl p; try(lia). unfold CIndex.
    destruct (le_dec (S nbleft) maxIdx); try(lia). simpl i. lia.
  }
  rewrite HlookupPEq. destruct (lookup p (memory s0) beqAddr); trivial. destruct v; trivial.
  assert(HidxEq: indexEq (CIndex (S nbleft)) zero = false).
  {
    apply beqIdxFalse. apply index_neq_i. cbn. unfold CIndex. destruct (le_dec (S nbleft) maxIdx); try(lia). simpl.
    lia.
  }
  rewrite HidxEq. assert(Hpred: Index.pred (CIndex (S nbleft)) = Some (CIndex nbleft)).
  {
    unfold CIndex. destruct (le_dec (S nbleft) maxIdx); try(lia). destruct (le_dec nbleft maxIdx); try(lia).
    unfold Index.pred. simpl. f_equal. apply index_eq_i. simpl. lia.
  }
  rewrite Hpred. rewrite IHnbleft; try(lia). reflexivity.
Qed.

Lemma getKSEntriesAuxEqNoImpact m n kernel s s0 startaddr endaddr:
isPADDR nullAddr s0
-> nextKernelIsValid s0
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> m > 0
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getAllPaddrConfigAux (filterOptionPaddr (getConfigBlocksAux (n+m) kernel s0 (CIndex n))) s0)
        /\ addr <> nullAddr)
-> S n <= maxIdx
-> (exists lastKern default,
      last (filterOptionPaddr (getConfigBlocksAux (n+m) kernel s0 (CIndex n))) default = lastKern
      /\ lookup (CPaddr (lastKern+nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr))
-> isKS kernel s0
-> getKSEntriesAux (S n) kernel s = getKSEntriesAux (S n) kernel s0.
Proof.
intros Hnull HnextProps HaddrsOutRange HgtMZero. revert kernel.
induction n; intros kernel HaddrsInRange HltNMax HlastConfig HkernIsKS.
- simpl in *. destruct (Paddr.addPaddrIdx kernel nextoffset) eqn:HaddKernNext; trivial.
  assert(HaddKernNextCopy: Paddr.addPaddrIdx kernel nextoffset = Some p) by assumption.
  unfold Paddr.addPaddrIdx in HaddKernNext.
  destruct (le_dec (kernel + nextoffset) maxAddr) eqn:HlebNextMax; try(exfalso; congruence).
  injection HaddKernNext as HaddKernNext. specialize(HnextProps kernel HkernIsKS).
  destruct HnextProps as (_ & [nextAddr (HlookupNextAddr & HnextProps)]).
  assert(HaddrsInRangeSpec: forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~ In addr (getAllPaddrBlockAux 0 kernel Constants.kernelStructureTotalLength)).
  {
    intros addr HaddrIn. apply HaddrsInRange in HaddrIn. destruct HaddrIn as (HaddrIn & _).
    destruct m; try(lia). simpl in HaddrIn. unfold isKS in *.
    destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; try(congruence). destruct v; try(congruence).
    unfold Paddr.addPaddrIdx in HaddrIn. rewrite HlebNextMax in *. rewrite HlookupNextAddr in *. simpl in HaddrIn.
    rewrite HlookupKern in *. rewrite app_nil_r in *. assumption.
  }
  assert(HlookupPEq: lookup p (memory s) beqAddr = lookup p (memory s0) beqAddr).
  {
    apply HaddrsOutRange. intro Hcontra. apply HaddrsInRangeSpec in Hcontra. contradict Hcontra. subst p.
    apply getAllPaddrBlockAuxIncl; simpl p; try(lia). rewrite kernelStructureTotalLengthVal. rewrite nextoffsetVal.
    lia.
  }
  rewrite HlookupPEq. subst p. rewrite HlookupNextAddr.
  assert(HgetStructAuxEq: getKSEntriesInStructAux (maxIdx + 1) kernel s (CIndex 7)
    = getKSEntriesInStructAux (maxIdx + 1) kernel s0 (CIndex 7)).
  {
    assert(Heq: exists n, maxIdx+1 = 7+n).
    {
      pose proof maxIdxBiggerThanNbOfKernels as Hgt. cbn in Hgt. exists (maxIdx-6). lia.
    }
    destruct Heq as [n Heq]. rewrite Heq.
    apply getKSEntriesInStructAuxEqNoImpact with startaddr endaddr; trivial. rewrite kernelStructureTotalLengthVal.
    cbn. lia.
  }
  rewrite HgetStructAuxEq. assert(HbeqNextNull: beqAddr nextAddr nullAddr = true).
  {
    assert(Hm: exists n, m = S n).
    { destruct m; try(lia). exists m. reflexivity. }
    destruct HlastConfig as [lastKern [default (HlastConfig & HlookupLast)]]. rewrite <-DTL.beqAddrTrue.
    destruct Hm as [n Hm]. subst m. simpl in HlastConfig. unfold isKS in *.
    destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite HaddKernNextCopy in *. rewrite HlookupNextAddr in HlastConfig.
    simpl in HlastConfig. subst lastKern. unfold CPaddr in HlookupLast. rewrite HlebNextMax in *.
    rewrite HlookupNextAddr in *. injection HlookupLast as Hres. assumption.
  }
  rewrite HbeqNextNull. rewrite <-DTL.beqAddrTrue in HbeqNextNull. subst nextAddr. unfold isPADDR in *.
  assert(HlookupNullEq: lookup nullAddr (memory s) beqAddr = lookup nullAddr (memory s0) beqAddr).
  {
    apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra. destruct Hcontra as (_ & Hcontra).
    congruence.
  }
  rewrite HlookupNullEq. reflexivity.
- set(succ := S n). fold succ in IHn. cbn -[succ nullAddr]. simpl in HlastConfig.
  destruct (Paddr.addPaddrIdx kernel nextoffset) eqn:HaddKernNext; trivial.
  assert(HaddKernNextCopy: Paddr.addPaddrIdx kernel nextoffset = Some p) by assumption.
  unfold Paddr.addPaddrIdx in HaddKernNext.
  destruct (le_dec (kernel + nextoffset) maxAddr) eqn:HlebNextMax; try(exfalso; congruence).
  injection HaddKernNext as HaddKernNext. assert(HnextPropsCopy: nextKernelIsValid s0) by assumption.
  specialize(HnextProps kernel HkernIsKS). destruct HnextProps as (_ & [nextAddr (HlookupNextAddr & HnextProps)]).
  assert(Hpred: Index.pred (CIndex (S n)) = Some(CIndex n)).
  {
    unfold CIndex. destruct (le_dec (S n) maxIdx); try(lia). destruct (le_dec n maxIdx); try(lia).
    unfold Index.pred. simpl. f_equal. apply index_eq_i. simpl. lia.
  }
  assert(HaddrsInRangeSpec: (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
      -> ~ In addr (getAllPaddrBlockAux 0 kernel Constants.kernelStructureTotalLength)
          /\ ~In addr (getAllPaddrConfigAux (filterOptionPaddr (getConfigBlocksAux (n+m) nextAddr s0 (CIndex n))) s0)
          /\ addr <> nullAddr)).
  {
    intros addr HaddrIn. apply HaddrsInRange in HaddrIn. destruct HaddrIn as (HaddrIn & HbeqAddrNull).
    destruct m; try(lia). simpl in HaddrIn. unfold isKS in *.
    destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). unfold Paddr.addPaddrIdx in HaddrIn. rewrite HlebNextMax in *.
    rewrite HlookupNextAddr in *. rewrite Hpred in *. simpl in HaddrIn. rewrite HlookupKern in *.
    apply Lib.in_app_or_neg in HaddrIn. destruct HaddrIn. auto.
  }
  assert(HaddrsInRangeSpecBis: (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
      -> ~ In addr (getAllPaddrBlockAux 0 kernel Constants.kernelStructureTotalLength))
    /\ (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
        -> ~In addr (getAllPaddrConfigAux (filterOptionPaddr (getConfigBlocksAux (n+m) nextAddr s0 (CIndex n))) s0)
          /\ addr <> nullAddr)).
  { split; intros; apply HaddrsInRangeSpec; assumption. }
  clear HaddrsInRangeSpec. destruct HaddrsInRangeSpecBis as (HaddrsInRangeSpec & HaddrsInRangeRec).
  assert(HlookupPEq: lookup p (memory s) beqAddr = lookup p (memory s0) beqAddr).
  {
    apply HaddrsOutRange. intro Hcontra. apply HaddrsInRangeSpec in Hcontra. contradict Hcontra. subst p.
    apply getAllPaddrBlockAuxIncl; simpl p; try(lia). rewrite kernelStructureTotalLengthVal. rewrite nextoffsetVal.
    lia.
  }
  rewrite HlookupPEq. subst p. rewrite HlookupNextAddr in *.
  assert(HgetStructAuxEq: getKSEntriesInStructAux (maxIdx + 1) kernel s (CIndex 7)
    = getKSEntriesInStructAux (maxIdx + 1) kernel s0 (CIndex 7)).
  {
    assert(Heq: exists n, maxIdx+1 = 7+n).
    {
      pose proof maxIdxBiggerThanNbOfKernels as Hgt. cbn in Hgt. exists (maxIdx-6). lia.
    }
    destruct Heq as [n1 Heq]. rewrite Heq.
    apply getKSEntriesInStructAuxEqNoImpact with startaddr endaddr; trivial. rewrite kernelStructureTotalLengthVal.
    cbn. lia.
  }
  rewrite HgetStructAuxEq. unfold isKS in HkernIsKS.
  destruct (lookup kernel (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  rewrite Hpred in *. simpl filterOptionPaddr in HlastConfig.
  destruct (beqAddr nextAddr nullAddr) eqn:HbeqNextNull.
  + rewrite <-DTL.beqAddrTrue in HbeqNextNull. subst nextAddr. unfold isPADDR in *.
    assert(HlookupNullEq: lookup nullAddr (memory s) beqAddr = lookup nullAddr (memory s0) beqAddr).
    {
      apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra. destruct Hcontra as (_ & Hcontra).
      congruence.
    }
    rewrite HlookupNullEq. unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); trivial.
    destruct v; try(exfalso; congruence). reflexivity.
  + rewrite <-beqAddrFalse in *. destruct HnextProps as [HnextIsKS | Hcontra]; try(exfalso; congruence).
    assert(HlebSuccMax: succ <= maxIdx) by lia.
    assert(HlastConfigRec: exists lastKern default,
      last (filterOptionPaddr (getConfigBlocksAux (n + m) nextAddr s0 (CIndex n))) default = lastKern
      /\ lookup (CPaddr (lastKern + nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr)).
    {
      destruct HlastConfig as [lastKern [default (HlastConfig & HlookupNextLast)]]. exists lastKern. exists kernel.
      split; trivial. apply eq_sym. apply eq_sym in HlastConfig. apply lastRec in HlastConfig. assumption.
    }
    specialize(IHn nextAddr HaddrsInRangeRec HlebSuccMax HlastConfigRec HnextIsKS). rewrite IHn.
    assert(HlookupNextEq: lookup nextAddr (memory s) beqAddr = lookup nextAddr (memory s0) beqAddr).
    {
      apply HaddrsOutRange. intro Hcontra. apply HaddrsInRangeRec in Hcontra. destruct Hcontra as (Hcontra & _).
      contradict Hcontra. destruct m; try(lia). rewrite <-plus_n_Sm. simpl. unfold isKS in *.
      specialize(HnextPropsCopy nextAddr HnextIsKS).
      destruct HnextPropsCopy as (HlebNextNextMax & [nextAddrRec (HlookupNextAddrRec & _)]).
      destruct (lookup nextAddr (memory s0) beqAddr) eqn:HlookupNext; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). unfold Paddr.addPaddrIdx.
      destruct (le_dec (nextAddr + nextoffset) maxAddr); try(lia). rewrite HlookupNextAddrRec.
      assert(In nextAddr (getAllPaddrBlockAux 0 nextAddr Constants.kernelStructureTotalLength)).
      {
        rewrite kernelStructureTotalLengthVal. apply getAllPaddrBlockAuxIncl; lia.
      }
      destruct (Index.pred (CIndex n)); simpl; rewrite HlookupNext; apply in_or_app; auto.
    }
    rewrite HlookupNextEq. reflexivity.
Qed.

Lemma getKSEntriesEqNoImpact part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0) /\ ~In addr (getConfigPaddr part s0) /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getKSEntries part s = getKSEntries part s0.
Proof.
intros Hstruct Hnull HnextProps HmaxPrepIsLen HpartIsParts0 HaddrsInRange HaddrsOutRange. unfold getKSEntries.
assert(HlookupPartEq: lookup part (memory s) beqAddr = lookup part (memory s0) beqAddr).
{
  assert(HpropsOr: In part (getAllPaddrBlock startaddr endaddr) \/ ~In part (getAllPaddrBlock startaddr endaddr))
    by (apply classic).
  destruct HpropsOr as [Hcontra | Hres].
  { exfalso. apply HaddrsInRange in Hcontra. destruct Hcontra. congruence. }
  apply HaddrsOutRange; assumption.
}
rewrite HlookupPartEq. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull; trivial. rewrite <-beqAddrFalse in *.
assert(HstructCopy: StructurePointerIsKS s0) by assumption.
specialize(Hstruct part p HlookupPart HbeqStructNull). rewrite Nat.add_1_r. pose proof maxNbPrepareNbLessThanMaxIdx.
apply getKSEntriesAuxEqNoImpact with (maxIdx+1-maxNbPrepare) startaddr endaddr; trivial; try(lia).
- intros addr HaddrIn. apply HaddrsInRange in HaddrIn. destruct HaddrIn as (_ & HaddrIn & HbeqAddrNull).
  unfold getConfigPaddr in *. apply Lib.in_app_or_neg in HaddrIn. destruct HaddrIn as (_ & HaddrIn).
  unfold getConfigBlocks in *. rewrite HlookupPart in *.
  replace (maxNbPrepare + (maxIdx + 1 - maxNbPrepare)) with (maxIdx+1); try(lia). auto.
- replace (maxNbPrepare + (maxIdx + 1 - maxNbPrepare)) with (maxIdx+1); try(lia).
  assert(HlookupPartCopy: lookup part (memory s0) beqAddr = Some (PDT p)) by assumption.
  assert(HlookupPartTri: lookup part (memory s0) beqAddr = Some (PDT p)) by assumption.
  apply completeKernListIsConfig in HlookupPartCopy; trivial. unfold getConfigBlocks in *.
  rewrite HlookupPart in HlookupPartCopy. rewrite HlookupPartCopy. apply completeKernList in HlookupPart; trivial.
  clear HlookupPartCopy. destruct (completeListOfKernels (structure p) s0); simpl in HlookupPart.
  {
    destruct HlookupPart as [pdentry (Hlookup & HstructEq)]. rewrite Hlookup in *.
    injection HlookupPartTri as HpdentriesEq. subst p. exfalso; congruence.
  }
  destruct HlookupPart as [pdentry (Hlookup & _ & HstructEq & HisComplete)]. rewrite Hlookup in *.
  injection HlookupPartTri as HpdentriesEq. subst p. subst p0. unfold isCompleteListOfKernelsAux in *.
  destruct HisComplete as (_ & [kernel (Hlast & HlookupNextLast)]). exists kernel. exists (structure pdentry).
  split; trivial. apply eq_sym. apply lastRecInc; auto.
Qed.

Lemma getMappedBlocksEqNoImpact part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> BlocksRangeFromKernelStartIsBE s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0) /\ ~In addr (getConfigPaddr part s0) /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getMappedBlocks part s = getMappedBlocks part s0.
Proof.
intros Hstruct Hnull HnextProps HmaxPrepIsLen HblkidxAreBE HpartIsParts0 HaddrsInRange HaddrsOutRange.
unfold getMappedBlocks.
rewrite getKSEntriesEqNoImpact with (s0:=s0) (startaddr:=startaddr) (endaddr:=endaddr); trivial.
assert(HremovedAddrsNotKS: forall addr, In addr (getAllPaddrBlock startaddr endaddr)
  -> ~In addr (filterOptionPaddr (getKSEntries part s0))).
{
  intros addr HaddrIn. specialize(HaddrsInRange addr HaddrIn). destruct HaddrsInRange as (_ & HaddrNotConfig & _).
  contradict HaddrNotConfig. apply inclKSEntriesConfig; trivial.
}
induction (filterOptionPaddr (getKSEntries part s0)); simpl in *; trivial.
assert(HremovedAddrsNotKSRec: forall addr, In addr (getAllPaddrBlock startaddr endaddr) -> ~ In addr l).
{
  intros addr HaddrIn. specialize(HremovedAddrsNotKS addr HaddrIn). apply not_or_and in HremovedAddrsNotKS.
  destruct HremovedAddrsNotKS. assumption.
}
specialize(IHl HremovedAddrsNotKSRec). rewrite IHl.
assert(HlookupAEq: lookup a (memory s) beqAddr = lookup a (memory s0) beqAddr).
{
  apply HaddrsOutRange. intro Hcontra. apply HremovedAddrsNotKS in Hcontra. apply not_or_and in Hcontra.
  destruct Hcontra. congruence.
}
rewrite HlookupAEq. reflexivity.
Qed.

Lemma getAccessibleMappedBlocksEqNoImpact part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> BlocksRangeFromKernelStartIsBE s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0) /\ ~In addr (getConfigPaddr part s0) /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s0.
Proof.
intros Hstruct Hnull HnextProps HmaxPrepIsLen HblkidxAreBE HpartIsParts0 HaddrsInRange HaddrsOutRange.
unfold getAccessibleMappedBlocks.
rewrite getMappedBlocksEqNoImpact with (s0:=s0) (startaddr:=startaddr) (endaddr:=endaddr); trivial.
assert(HlookupPartEq: lookup part (memory s) beqAddr = lookup part (memory s0) beqAddr).
{
  assert(HpropsOr: In part (getAllPaddrBlock startaddr endaddr) \/ ~In part (getAllPaddrBlock startaddr endaddr))
    by (apply classic).
  destruct HpropsOr as [Hcontra | Hres].
  { exfalso. apply HaddrsInRange in Hcontra. destruct Hcontra. congruence. }
  apply HaddrsOutRange; assumption.
}
rewrite HlookupPartEq. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
assert(HremovedAddrsNotKS: forall addr, In addr (getAllPaddrBlock startaddr endaddr)
  -> ~In addr (getMappedBlocks part s0)).
{
  intros addr HaddrIn. specialize(HaddrsInRange addr HaddrIn). destruct HaddrsInRange as (_ & HaddrNotConfig & _).
  contradict HaddrNotConfig. unfold getMappedBlocks in *. apply InFilterPresentInList in HaddrNotConfig.
  apply inclKSEntriesConfig; trivial.
}
induction (getMappedBlocks part s0); simpl in *; trivial.
assert(HremovedAddrsNotKSRec: forall addr, In addr (getAllPaddrBlock startaddr endaddr) -> ~ In addr l).
{
  intros addr HaddrIn. specialize(HremovedAddrsNotKS addr HaddrIn). apply not_or_and in HremovedAddrsNotKS.
  destruct HremovedAddrsNotKS. assumption.
}
specialize(IHl HremovedAddrsNotKSRec). rewrite IHl.
assert(HlookupAEq: lookup a (memory s) beqAddr = lookup a (memory s0) beqAddr).
{
  apply HaddrsOutRange. intro Hcontra. apply HremovedAddrsNotKS in Hcontra. apply not_or_and in Hcontra.
  destruct Hcontra. congruence.
}
rewrite HlookupAEq. reflexivity.
Qed.

Lemma getMappedPaddrEqNoImpact part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> BlocksRangeFromKernelStartIsBE s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0) /\ ~In addr (getConfigPaddr part s0) /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getMappedPaddr part s = getMappedPaddr part s0.
Proof.
intros Hstruct Hnull HnextProps HmaxPrepIsLen HblkidxAreBE HpartIsParts0 HaddrsInRange HaddrsOutRange.
unfold getMappedPaddr.
rewrite getMappedBlocksEqNoImpact with (s0:=s0) (startaddr:=startaddr) (endaddr:=endaddr); trivial.
assert(HremovedAddrsNotKS: forall addr, In addr (getAllPaddrBlock startaddr endaddr)
  -> ~In addr (getMappedBlocks part s0)).
{
  intros addr HaddrIn. specialize(HaddrsInRange addr HaddrIn). destruct HaddrsInRange as (_ & HaddrNotConfig & _).
  contradict HaddrNotConfig. unfold getMappedBlocks in *. apply InFilterPresentInList in HaddrNotConfig.
  apply inclKSEntriesConfig; trivial.
}
induction (getMappedBlocks part s0); simpl in *; trivial.
assert(HremovedAddrsNotKSRec: forall addr, In addr (getAllPaddrBlock startaddr endaddr) -> ~ In addr l).
{
  intros addr HaddrIn. specialize(HremovedAddrsNotKS addr HaddrIn). apply not_or_and in HremovedAddrsNotKS.
  destruct HremovedAddrsNotKS. assumption.
}
specialize(IHl HremovedAddrsNotKSRec). rewrite IHl.
assert(HlookupAEq: lookup a (memory s) beqAddr = lookup a (memory s0) beqAddr).
{
  apply HaddrsOutRange. intro Hcontra. apply HremovedAddrsNotKS in Hcontra. apply not_or_and in Hcontra.
  destruct Hcontra. congruence.
}
rewrite HlookupAEq. reflexivity.
Qed.

Lemma getAccessibleMappedPaddrEqNoImpact part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> BlocksRangeFromKernelStartIsBE s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0) /\ ~In addr (getConfigPaddr part s0) /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s0.
Proof.
intros Hstruct Hnull HnextProps HmaxPrepIsLen HblkidxAreBE HpartIsParts0 HaddrsInRange HaddrsOutRange.
unfold getAccessibleMappedPaddr.
rewrite getAccessibleMappedBlocksEqNoImpact with (s0:=s0) (startaddr:=startaddr) (endaddr:=endaddr); trivial.
assert(HremovedAddrsNotKS: forall addr, In addr (getAllPaddrBlock startaddr endaddr)
  -> ~In addr (getAccessibleMappedBlocks part s0)).
{
  intros addr HaddrIn. specialize(HaddrsInRange addr HaddrIn). destruct HaddrsInRange as (_ & HaddrNotConfig & _).
  contradict HaddrNotConfig. unfold getAccessibleMappedBlocks in *.
  destruct (lookup part (memory s0) beqAddr); try(simpl in *; exfalso; congruence).
  destruct v; try(simpl in *; exfalso; congruence). apply InFilterAccessibleInList in HaddrNotConfig.
  unfold getMappedBlocks in *. apply InFilterPresentInList in HaddrNotConfig.
  apply inclKSEntriesConfig; trivial.
}
induction (getAccessibleMappedBlocks part s0); simpl in *; trivial.
assert(HremovedAddrsNotKSRec: forall addr, In addr (getAllPaddrBlock startaddr endaddr) -> ~ In addr l).
{
  intros addr HaddrIn. specialize(HremovedAddrsNotKS addr HaddrIn). apply not_or_and in HremovedAddrsNotKS.
  destruct HremovedAddrsNotKS. assumption.
}
specialize(IHl HremovedAddrsNotKSRec). rewrite IHl.
assert(HlookupAEq: lookup a (memory s) beqAddr = lookup a (memory s0) beqAddr).
{
  apply HaddrsOutRange. intro Hcontra. apply HremovedAddrsNotKS in Hcontra. apply not_or_and in Hcontra.
  destruct Hcontra. congruence.
}
rewrite HlookupAEq. reflexivity.
Qed.

Lemma getChildrenEqNoImpact part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> BlocksRangeFromKernelStartIsBE s0
-> FirstFreeSlotPointerIsBEAndFreeSlot s0
-> wellFormedFstShadowIfBlockEntry s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0) /\ ~In addr (getConfigPaddr part s0) /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getChildren part s = getChildren part s0.
Proof.
intros Hstruct Hnull HnextProps HmaxPrepIsLen HblkidxAreBE HfirstFree HwellSh1 HpartIsParts0 HaddrsInRange
  HaddrsOutRange.
unfold getChildren. unfold getPDs.
rewrite getMappedBlocksEqNoImpact with (s0:=s0) (startaddr:=startaddr) (endaddr:=endaddr); trivial.
assert(HlookupPartEq: lookup part (memory s) beqAddr = lookup part (memory s0) beqAddr).
{
  assert(HpropsOr: In part (getAllPaddrBlock startaddr endaddr) \/ ~In part (getAllPaddrBlock startaddr endaddr))
    by (apply classic).
  destruct HpropsOr as [Hcontra | Hres].
  { exfalso. apply HaddrsInRange in Hcontra. destruct Hcontra. congruence. }
  apply HaddrsOutRange; assumption.
}
rewrite HlookupPartEq. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
assert(HremovedAddrsNotKS: forall addr, In addr (getMappedBlocks part s0)
  -> ~In addr (getAllPaddrBlock startaddr endaddr)
      /\ ~In (CPaddr (addr+sh1offset)) (getAllPaddrBlock startaddr endaddr)).
{
  intros addr HaddrIn. split; intro Hcontra.
  - specialize(HaddrsInRange addr Hcontra). destruct HaddrsInRange as (_ & HaddrNotConfig & _).
    contradict HaddrNotConfig. unfold getMappedBlocks in *. apply InFilterPresentInList in HaddrIn.
    apply inclKSEntriesConfig; trivial.
  - specialize(HaddrsInRange (CPaddr (addr+sh1offset)) Hcontra). destruct HaddrsInRange as (_ & HaddrNotConfig & _).
    contradict HaddrNotConfig. unfold getConfigPaddr. apply in_or_app. right. unfold getMappedBlocks in *.
    unfold getKSEntries in *. unfold getConfigBlocks. rewrite HlookupPart in *.
    destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull; try(simpl in *; exfalso; congruence).
    pose proof (nbKernEq part p s0 Hstruct HfirstFree Hnull HnextProps HblkidxAreBE HmaxPrepIsLen HlookupPart)
      as HlenEq. unfold getKSEntries in HlenEq. rewrite HlookupPart in *. rewrite HbeqStructNull in *.
    rewrite <-beqAddrFalse in *. specialize(Hstruct part p HlookupPart HbeqStructNull).
    apply InFilterPresentInList in HaddrIn. pose proof maxNbPrepareNbLessThanMaxIdx.
    replace (maxIdx+1) with (maxNbPrepare + (maxIdx+1-maxNbPrepare)); try(lia).
    apply KSEntryAddrIsConfigAddr; trivial; try(lia).
    + rewrite kernelStructureTotalLengthVal. cbn. lia.
    + rewrite Nat.add_1_r in HlenEq. rewrite HlenEq.
      assert(HnotFulls0: length (completeListOfKernels (structure p) s0) <= maxNbPrepare).
      {
        pose proof (completeKernListIsListOfKern part p s0 Hnull HnextProps HlookupPart) as HkernList.
        specialize(HmaxPrepIsLen part (completeListOfKernels (structure p) s0) HkernList). assumption.
      }
      apply Nat.mul_le_mono_r; lia.
}
assert(HblocksGiveSh1s:  forall addr, In addr (getMappedBlocks part s0)
  -> isSHE (CPaddr (addr+sh1offset)) s0).
{
  intros addr HaddrMapped. assert(HaddrIsBE: isBE addr s0).
  {
    apply mappedBlockIsBE in HaddrMapped. destruct HaddrMapped as [bentry (Hlookup & _)]. unfold isBE.
    rewrite Hlookup. trivial.
  }
  specialize(HwellSh1 addr HaddrIsBE). assumption.
}
induction (getMappedBlocks part s0); simpl in *; trivial.
assert(HremovedAddrsNotKSRec: forall addr, In addr l
  -> ~In addr (getAllPaddrBlock startaddr endaddr)
      /\ ~In (CPaddr (addr + sh1offset)) (getAllPaddrBlock startaddr endaddr)).
{ intros. apply HremovedAddrsNotKS; auto. }
assert(HblocksGiveSh1sRec: forall addr, In addr l -> isSHE (CPaddr (addr + sh1offset)) s0).
{ intros. apply HblocksGiveSh1s; auto. }
specialize(IHl HremovedAddrsNotKSRec HblocksGiveSh1sRec).
assert(Htriv: a = a \/ In a l) by auto. specialize(HremovedAddrsNotKS a Htriv). specialize(HblocksGiveSh1s a Htriv).
destruct HremovedAddrsNotKS as (HaNotIn & HaSh1NotIn). unfold childFilter. rewrite HaddrsOutRange; trivial.
destruct (lookup a (memory s0) beqAddr); trivial. destruct v; trivial.
assert(Hsh1Eq: Paddr.addPaddrIdx a sh1offset = Some (CPaddr (a+sh1offset))).
{
  unfold Paddr.addPaddrIdx. unfold CPaddr. unfold isSHE in *. unfold CPaddr in HblocksGiveSh1s.
  destruct (le_dec (a + sh1offset) maxAddr); f_equal. exfalso.
  assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (a + sh1offset) n |} = nullAddr)
    by (cbn; f_equal; apply proof_irrelevance). rewrite HnullEq in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
rewrite Hsh1Eq in *. rewrite HaddrsOutRange; trivial. unfold isSHE in *.
destruct (lookup (CPaddr (a + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
destruct v; try(exfalso; congruence). destruct (PDflag s1); trivial. simpl. rewrite HaddrsOutRange; trivial.
f_equal. assumption.
Qed.

Lemma getPartitionsAuxEqNoImpact n part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> BlocksRangeFromKernelStartIsBE s0
-> FirstFreeSlotPointerIsBEAndFreeSlot s0
-> wellFormedFstShadowIfBlockEntry s0
-> noDupPartitionTree s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0)
        /\ (forall partition, In partition (getPartitions multiplexer s0) -> ~In addr (getConfigPaddr partition s0))
        /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getPartitionsAux n part s = getPartitionsAux n part s0.
Proof.
intros Hstruct Hnull HnextProps HmaxPrepIsLen HblkidxAreBE HfirstFree HnoDupTree HwellSh1 HpartIsParts0 HaddrsInRange
  HaddrsOutRange. revert part HpartIsParts0.
induction n; simpl; intros; f_equal.
assert(HaddrsInRangePart: forall addr, In addr (getAllPaddrBlock startaddr endaddr)
  -> ~ In addr (getPartitions multiplexer s0)
      /\ ~ In addr (getConfigPaddr part s0)
      /\ addr <> nullAddr).
{
  intros addr HaddrIn. specialize(HaddrsInRange addr HaddrIn).
  destruct HaddrsInRange as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). split; try(split); trivial.
  apply HaddrNotConfig; assumption.
}
rewrite getChildrenEqNoImpact with (s0:=s0) (startaddr:=startaddr) (endaddr:=endaddr); trivial.
assert(HchildrenAreParts: forall child, In child (getChildren part s0) -> In child (getPartitions multiplexer s0)).
{ intro child. apply childrenPartitionInPartitionList; assumption. }
induction (getChildren part s0); simpl in *; trivial.
assert(HchildrenArePartsRec: forall child, In child l -> In child (getPartitions multiplexer s0)).
{ intros. apply HchildrenAreParts; auto. }
assert(Htriv: a = a \/ In a l) by auto. specialize(HchildrenAreParts a Htriv). rewrite IHl; trivial.
rewrite IHn; trivial.
Qed.

Lemma getPartitionsEqNoImpact part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> BlocksRangeFromKernelStartIsBE s0
-> FirstFreeSlotPointerIsBEAndFreeSlot s0
-> wellFormedFstShadowIfBlockEntry s0
-> noDupPartitionTree s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0)
        /\ (forall partition, In partition (getPartitions multiplexer s0) -> ~In addr (getConfigPaddr partition s0))
        /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getPartitions part s = getPartitions part s0.
Proof.
unfold getPartitions. apply getPartitionsAuxEqNoImpact.
Qed.

Lemma getFreeSlotsListRecEqNoImpact n (nbleft: index) freeBlock s s0:
lookup nullAddr (memory s) beqAddr = lookup nullAddr (memory s0) beqAddr
-> (forall block, In (SomePaddr block) (getFreeSlotsListRec n freeBlock s0 nbleft)
    -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr)
-> wellFormedFreeSlotsList (getFreeSlotsListRec n freeBlock s0 nbleft) <> False
-> getFreeSlotsListRec n freeBlock s nbleft = getFreeSlotsListRec n freeBlock s0 nbleft.
Proof.
intro HlookupNullEq. revert freeBlock nbleft.
induction n; simpl; intros freeBlock nbleft HlookupFreeBlocksEq Hwell; trivial.
destruct (lookup freeBlock (memory s0) beqAddr) eqn:HlookupFrees0; try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
- destruct (Index.pred nbleft) eqn:Hpred; try(simpl in *; exfalso; congruence). simpl in *.
  assert(HlookupFreeBlocksEqRec: forall block,
    In (SomePaddr block) (getFreeSlotsListRec n (endAddr (blockrange b)) s0 i)
    -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
  { intros. apply HlookupFreeBlocksEq; auto. }
  assert(Htriv: SomePaddr freeBlock = SomePaddr freeBlock
    \/ In (SomePaddr freeBlock) (getFreeSlotsListRec n (endAddr (blockrange b)) s0 i)) by auto.
  specialize(HlookupFreeBlocksEq freeBlock Htriv). rewrite HlookupFreeBlocksEq. rewrite HlookupFrees0. f_equal.
  apply IHn; assumption.
- destruct (beqAddr freeBlock nullAddr) eqn:HbeqFBNull; try(simpl in *; exfalso; congruence).
  rewrite <-DTL.beqAddrTrue in HbeqFBNull. subst freeBlock. rewrite HlookupNullEq. rewrite HlookupFrees0. reflexivity.
Qed.

Lemma getFreeSlotsListEqNoImpact part s s0 startaddr endaddr:
StructurePointerIsKS s0
-> isPADDR nullAddr s0
-> nextKernelIsValid s0
-> inclFreeSlotsBlockEntries s0
-> BlocksRangeFromKernelStartIsBE s0
-> NoDupInFreeSlotsList s0
-> In part (getPartitions multiplexer s0)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0) /\ ~In addr (getConfigPaddr part s0) /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> getFreeSlotsList part s = getFreeSlotsList part s0.
Proof.
intros Hstruct Hnull HmaxPrepIsLen HinclFreeKS HblkidxAreBE HnoDupFree HpartIsParts0 HaddrsInRange HaddrsOutRange.
unfold getFreeSlotsList.
assert(HlookupPartEq: lookup part (memory s) beqAddr = lookup part (memory s0) beqAddr).
{
  assert(HpropsOr: In part (getAllPaddrBlock startaddr endaddr) \/ ~In part (getAllPaddrBlock startaddr endaddr))
    by (apply classic).
  destruct HpropsOr as [Hcontra | Hres].
  { exfalso. apply HaddrsInRange in Hcontra. destruct Hcontra. congruence. }
  apply HaddrsOutRange; assumption.
}
rewrite HlookupPartEq. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial. assert(HpartIsPDT: isPDT part s0).
{ unfold isPDT. rewrite HlookupPart. trivial. }
specialize(HinclFreeKS part HpartIsPDT). specialize(HnoDupFree part p HlookupPart). unfold getFreeSlotsList in *.
rewrite HlookupPart in *. rewrite HbeqFirstNull in *.
destruct HnoDupFree as [optFreeList (Hopt & HwellOpt & _)]. subst optFreeList.
assert(HfreeAreNotInRange: forall block,
  In (SomePaddr block) (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
  -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
{
  intros block HblockIsFree. apply HinclFreeKS in HblockIsFree. apply HaddrsOutRange. intro Hcontra.
  apply HaddrsInRange in Hcontra. destruct Hcontra as (_ & HblockNotConfig & _). contradict HblockNotConfig.
  apply inclKSEntriesConfig; trivial. apply optionIsInFilter; assumption.
}
apply getFreeSlotsListRecEqNoImpact; trivial. apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra.
destruct Hcontra as (_ & _ & Hcontra). congruence.
Qed.

Lemma isListOfKernelsAuxImplNoImpact kernList kernel s s0 startaddr endaddr:
(forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = None)
-> isListOfKernelsAux kernList kernel s
-> isListOfKernelsAux kernList kernel s0.
Proof.
intros HaddrsOutRange HaddrsInRange. revert kernel.
induction kernList; simpl; intros kernel HkernList; trivial.
destruct HkernList as (HlookupNext & HlebNextMax & HbeqANull & HkernListRec). split; auto.
assert(HpropsOr: In (CPaddr (kernel+nextoffset)) (getAllPaddrBlock startaddr endaddr)
  \/ ~In (CPaddr (kernel+nextoffset)) (getAllPaddrBlock startaddr endaddr)) by (apply classic).
destruct HpropsOr as [Hcontra | Hres].
{ apply HaddrsInRange in Hcontra. exfalso; congruence. }
rewrite <-HaddrsOutRange; assumption.
Qed.

Lemma isListOfKernelsImplNoImpact kernList part s s0 startaddr endaddr:
(forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = None)
-> isListOfKernels kernList part s
-> isListOfKernels kernList part s0.
Proof.
intros HaddrsOutRange HaddrsInRange HkernList. unfold isListOfKernels in *.
destruct kernList; trivial. destruct HkernList as [pdentry (HlookupPart & HbeqStructNull & Hstruct & HkernListAux)].
exists pdentry. split; try(split; try(split)); auto.
- assert(HpropsOr: In part (getAllPaddrBlock startaddr endaddr) \/ ~In part (getAllPaddrBlock startaddr endaddr))
    by (apply classic).
  destruct HpropsOr as [Hcontra | Hres].
  { exfalso. apply HaddrsInRange in Hcontra. congruence. }
  rewrite <-HaddrsOutRange; assumption.
- apply isListOfKernelsAuxImplNoImpact with s startaddr endaddr; assumption.
Qed.

Lemma isParentsListImplNoImpact parentsList part s s0 startaddr endaddr:
(forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = None)
-> isParentsList s parentsList part
-> isParentsList s0 parentsList part.
Proof.
intros HaddrsOutRange HaddrsInRange. revert part.
induction parentsList; simpl; intros part HparentsList; trivial.
assert(HpropsOr: In a (getAllPaddrBlock startaddr endaddr) \/ ~In a (getAllPaddrBlock startaddr endaddr))
  by (apply classic). destruct HpropsOr as [Hcontra | Hres].
{ apply HaddrsInRange in Hcontra. rewrite Hcontra in *. exfalso; congruence. }
rewrite HaddrsOutRange in HparentsList; trivial. destruct (lookup a (memory s0) beqAddr); trivial.
destruct v; trivial. destruct HparentsList as (HbeqPartRoot & [pdentry (HlookupPart & Hparent)] & HparentsListRec).
split; try(split); auto. exists pdentry. split; trivial. rewrite <-HaddrsOutRange; trivial. intro Hcontra.
apply HaddrsInRange in Hcontra. congruence.
Qed.

Lemma completeListOfKernelsAuxEqNoImpact n m kernel s s0 startaddr endaddr:
nextKernelIsValid s0
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> n <= maxIdx
-> isKS kernel s0
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getAllPaddrConfigAux (filterOptionPaddr (getConfigBlocksAux (n+m) kernel s0 (CIndex n))) s0))
-> completeListOfKernelsAux n kernel s = completeListOfKernelsAux n kernel s0.
Proof.
intros HnextProps HaddrsOutRange. revert kernel.
induction n; simpl; intros kernel HlebNMax HkernIsKS HaddrsInRange; trivial.
specialize(HnextProps kernel HkernIsKS). destruct HnextProps as (HlebNextMax & [nextAddr (HlookupNext & HnextProps)]).
unfold isKS in *. destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
assert(HnextEq: Paddr.addPaddrIdx kernel nextoffset = Some (CPaddr (kernel+nextoffset))).
{
  unfold Paddr.addPaddrIdx. unfold CPaddr. destruct (le_dec (kernel + nextoffset) maxAddr); try(lia). f_equal.
}
rewrite HnextEq in *. unfold CPaddr. unfold CPaddr in HaddrsInRange.
destruct (le_dec (kernel + nextoffset) maxAddr); try(lia). rewrite HlookupNext in *.
assert(Hpred: Index.pred (CIndex (S n)) = Some(CIndex n)).
{
  unfold CIndex. destruct (le_dec (S n) maxIdx); try(lia). destruct (le_dec n maxIdx); try(lia).
  unfold Index.pred. simpl. f_equal. apply index_eq_i. simpl. lia.
}
rewrite Hpred in *. simpl in HaddrsInRange. rewrite HlookupKern in *.
assert(HnextNotIn: ~In {| p := kernel + nextoffset; Hp := ADT.CPaddr_obligation_1 (kernel + nextoffset) l |}
  (getAllPaddrBlock startaddr endaddr)).
{
  intro Hcontra. apply HaddrsInRange in Hcontra. apply Lib.in_app_or_neg in Hcontra.
  destruct Hcontra as (Hcontra & _). contradict Hcontra. rewrite kernelStructureTotalLengthVal.
  apply getAllPaddrBlockAuxIncl; simpl p; try(rewrite nextoffsetVal); try(lia).
}
rewrite HaddrsOutRange; trivial. rewrite HlookupNext. destruct (beqAddr nextAddr nullAddr) eqn:HbeqNextNull; trivial.
f_equal. rewrite <-beqAddrFalse in *. destruct HnextProps as [HnextIsKS | Hcontra]; try(exfalso; congruence).
apply IHn; trivial.
- lia.
- intros addr HaddrIn. apply HaddrsInRange in HaddrIn. apply Lib.in_app_or_neg in HaddrIn. destruct HaddrIn.
  assumption.
Qed.

Lemma completeListOfKernelsEqNoImpact n kernel s s0 startaddr endaddr:
nextKernelIsValid s0
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isKS kernel s0
-> maxNbPrepare <= n
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getAllPaddrConfigAux (filterOptionPaddr
          (getConfigBlocksAux n kernel s0 (CIndex maxNbPrepare))) s0))
-> completeListOfKernels kernel s = completeListOfKernels kernel s0.
Proof.
intros HnextProps HaddrsOutRange HkernIsKS HlebMaxPrepN HaddrsInRange. unfold completeListOfKernels.
assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s0) beqAddr).
{
  apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra. contradict Hcontra.
  pose proof maxNbPrepareNotZero. destruct n; try(lia). simpl.
  specialize(HnextProps kernel HkernIsKS).
  destruct HnextProps as (HlebNextMax & [nextAddr (HlookupNext & HnextProps)]). unfold isKS in *.
  destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). unfold Paddr.addPaddrIdx.
  destruct (le_dec (kernel + nextoffset) maxAddr); try(lia). rewrite HlookupNext.
  assert(In kernel (getAllPaddrBlockAux 0 kernel Constants.kernelStructureTotalLength)).
  { rewrite kernelStructureTotalLengthVal. apply getAllPaddrBlockAuxIncl; lia. }
  destruct (Index.pred (CIndex maxNbPrepare)); simpl; rewrite HlookupKern; apply in_or_app; auto.
}
rewrite HlookupKernEq. assert(Heq: completeListOfKernelsAux maxNbPrepare kernel s
  = completeListOfKernelsAux maxNbPrepare kernel s0).
{
  apply completeListOfKernelsAuxEqNoImpact with (n-maxNbPrepare) startaddr endaddr; trivial.
  - pose proof maxNbPrepareNbLessThanMaxIdx. lia.
  - replace (maxNbPrepare + (n - maxNbPrepare)) with n; try(lia). assumption.
}
rewrite Heq. reflexivity.
Qed.

Lemma partitionsArePDTAuxPartial n part basePart s blockToDelete blockTDStart:
noDupPartitionTree s
-> (forall idPDchild sh1entryaddr part,
        idPDchild <> blockToDelete
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> bentryStartAddr blockToDelete blockTDStart s
-> ~In blockTDStart (getPartitions multiplexer s)
-> In basePart (getPartitions multiplexer s)
-> isPDT basePart s
-> In part (getPartitionsAux n basePart s)
-> isPDT part s.
Proof.
intros HnoDupTree HPDTIfPDFlagPartial Hstart HstartNotPart. revert basePart.
induction n; simpl; intros basePart HbaseIsPart HbaseIsPDT HpartInBase; try(exfalso; congruence).
destruct HpartInBase as [Heq | HpartInBase]; try(subst part; assumption).
assert(HchildrenAreParts: forall child, In child (getChildren basePart s) -> In child (getPartitions multiplexer s)).
{
  intros child HchildIsChild. apply childrenPartitionInPartitionList with basePart; trivial.
}
assert(HchildrenArePDTs: forall child, In child (getChildren basePart s) -> isPDT child s).
{
  intros child HchildIsChild. apply childrenArePDTPartial with basePart blockToDelete blockTDStart; trivial.
  apply childrenPartitionInPartitionList in HchildIsChild; trivial. intro. subst child. congruence.
}
induction (getChildren basePart s); simpl in *; try(exfalso; congruence).
assert(forall child : paddr, In child l -> In child (getPartitions multiplexer s)).
{ intros. apply HchildrenAreParts; auto. }
assert(forall child : paddr, In child l -> isPDT child s).
{ intros. apply HchildrenArePDTs; auto. }
apply in_app_or in HpartInBase. destruct HpartInBase as [HpartInA | HpartInBase]; try(apply IHl; assumption).
apply IHn with a; trivial.
- apply HchildrenAreParts; auto.
- apply HchildrenArePDTs; auto.
Qed.

Lemma partitionsArePDTPartial part s blockToDelete blockTDStart:
multiplexerIsPDT s
-> noDupPartitionTree s
-> (forall idPDchild sh1entryaddr part,
        idPDchild <> blockToDelete
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> bentryStartAddr blockToDelete blockTDStart s
-> ~In blockTDStart (getPartitions multiplexer s)
-> In part (getPartitions multiplexer s)
-> isPDT part s.
Proof.
intros HmultIsPDT HnoDupTree HPDTIfPDFlagPartial Hstart HstartNotPart. unfold getPartitions.
apply partitionsArePDTAuxPartial with blockToDelete blockTDStart; trivial. unfold getPartitions.
replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
Qed.

Lemma getConfigBlocksAuxEqNoImpact n m kernel s s0 startaddr endaddr:
isPADDR nullAddr s0
-> nextKernelIsValid s0
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> m > 0
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getAllPaddrConfigAux (filterOptionPaddr (getConfigBlocksAux (n+m) kernel s0 (CIndex n))) s0)
        /\ addr <> nullAddr)
-> S n <= maxIdx
-> isKS kernel s0
-> getConfigBlocksAux (n+m) kernel s (CIndex n) = getConfigBlocksAux (n+m) kernel s0 (CIndex n).
Proof.
intros Hnull HnextProps HaddrsOutRange HgtMZero. revert kernel.
induction n; intros kernel HaddrsInRange HltNMax (* HlastConfig *) HkernIsKS.
- destruct m; try(lia). simpl in *. specialize(HnextProps kernel HkernIsKS).
  destruct HnextProps as (HlebNextMax & [nextAddr (HlookupNextAddr & HnextProps)]). unfold Paddr.addPaddrIdx in *.
  destruct (le_dec (kernel + nextoffset) maxAddr) eqn:HaddKernNext; try(lia). rewrite HlookupNextAddr in *.
  unfold isKS in *. destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). simpl in HaddrsInRange. rewrite HlookupKern in *. rewrite app_nil_r in *.
  assert(HlookupKerns: lookup kernel (memory s) beqAddr = Some (BE b)).
  {
    rewrite <-HlookupKern. apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra.
    destruct Hcontra as (Hcontra & _). contradict Hcontra. rewrite kernelStructureTotalLengthVal.
    apply getAllPaddrBlockAuxIncl; lia.
  }
  rewrite HlookupKerns. rewrite HaddrsOutRange.
  + rewrite HlookupNextAddr. reflexivity.
  + intro Hcontra. apply HaddrsInRange in Hcontra. destruct Hcontra as (Hcontra & _). contradict Hcontra.
    rewrite kernelStructureTotalLengthVal. pose proof nextoffsetVal. apply getAllPaddrBlockAuxIncl; simpl p; lia.
- simpl in *. specialize(HnextProps kernel HkernIsKS).
  destruct HnextProps as (HlebNextMax & [nextAddr (HlookupNextAddr & HnextProps)]). unfold Paddr.addPaddrIdx in *.
  destruct (le_dec (kernel + nextoffset) maxAddr) eqn:HaddKernNext; try(lia). rewrite HlookupNextAddr in *.
  unfold isKS in *. destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  assert(Hpred: Index.pred (CIndex (S n)) = Some(CIndex n)).
  {
    unfold CIndex. destruct (le_dec (S n) maxIdx); try(lia). destruct (le_dec n maxIdx); try(lia).
    unfold Index.pred. simpl. f_equal. apply index_eq_i. simpl. lia.
  }
  rewrite Hpred in *. simpl in HaddrsInRange. rewrite HlookupKern in *.
  assert(HlookupKerns: lookup kernel (memory s) beqAddr = Some (BE b)).
  {
    rewrite <-HlookupKern. apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra.
    destruct Hcontra as (Hcontra & _). contradict Hcontra. apply in_or_app. left.
    rewrite kernelStructureTotalLengthVal. apply getAllPaddrBlockAuxIncl; lia.
  }
  rewrite HlookupKerns. assert(HlookupNextAddrs: lookup
      {| p:= kernel+nextoffset; Hp:= StateLib.Paddr.addPaddrIdx_obligation_1 kernel nextoffset l |} (memory s) beqAddr
    = Some (PADDR nextAddr)).
  {
    rewrite <-HlookupNextAddr with (StateLib.Paddr.addPaddrIdx_obligation_1 kernel nextoffset l).
    apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra. destruct Hcontra as (Hcontra & _).
    apply Lib.in_app_or_neg in Hcontra. destruct Hcontra as (Hcontra & _). contradict Hcontra.
    rewrite kernelStructureTotalLengthVal. pose proof nextoffsetVal. apply getAllPaddrBlockAuxIncl; simpl p; lia.
  }
  rewrite HlookupNextAddrs. f_equal. destruct (beqAddr nextAddr nullAddr) eqn:HbeqNextNull.
  + rewrite <-DTL.beqAddrTrue in HbeqNextNull. subst nextAddr. destruct m; try(lia). rewrite <-Nat.add_succ_comm.
    simpl. unfold isPADDR in *.
    assert(HlookupNullEq: lookup nullAddr (memory s) beqAddr = lookup nullAddr (memory s0) beqAddr).
    {
      apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra. destruct Hcontra as (_ & Hcontra).
      congruence.
    }
    rewrite HlookupNullEq. unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); trivial.
    destruct v; try(exfalso; congruence). reflexivity.
  + rewrite <-beqAddrFalse in *. destruct HnextProps as [HnextIsKS | Hcontra]; try(exfalso; congruence).
    apply IHn; trivial.
    * intros addr HaddrInRange. specialize(HaddrsInRange addr HaddrInRange).
      destruct HaddrsInRange as (HaddrNotConfig & HbeqAddrNull). split; trivial.
      apply Lib.in_app_or_neg in HaddrNotConfig. apply HaddrNotConfig.
    * lia.
Qed.

Lemma getConfigBlocksEqNoImpact part s s0 startaddr endaddr:
isPADDR nullAddr s0
-> nextKernelIsValid s0
-> StructurePointerIsKS s0
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0)
        /\ ~In addr (getAllPaddrConfigAux (getConfigBlocks part s0) s0)
        /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> In part (getPartitions multiplexer s0)
-> getConfigBlocks part s = getConfigBlocks part s0.
Proof.
intros Hnull HnextProps Hstruct HaddrsInRange HaddrsOutRange HpartIsPart. unfold getConfigBlocks in *.
assert(HlookupPartEq: lookup part (memory s) beqAddr = lookup part (memory s0) beqAddr).
{
  assert(HpropsOr: In part (getAllPaddrBlock startaddr endaddr) \/ ~In part (getAllPaddrBlock startaddr endaddr))
    by (apply classic).
  destruct HpropsOr as [Hcontra | Hres].
  { exfalso. apply HaddrsInRange in Hcontra. destruct Hcontra. congruence. }
  apply HaddrsOutRange; assumption.
}
rewrite HlookupPartEq. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull.
- rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull in *. rewrite Nat.add_1_r. simpl.
  unfold isPADDR in *.
  assert(HlookupNullEq: lookup nullAddr (memory s) beqAddr = lookup nullAddr (memory s0) beqAddr).
  {
    apply HaddrsOutRange. intro Hcontra. apply HaddrsInRange in Hcontra. destruct Hcontra as (_ & _ & Hcontra).
    congruence.
  }
  rewrite HlookupNullEq. unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); trivial.
  destruct v; try(exfalso; congruence). reflexivity.
- rewrite <-beqAddrFalse in *. (* assert(HstructCopy: StructurePointerIsKS s0) by assumption. *)
  specialize(Hstruct part p HlookupPart HbeqStructNull). pose proof maxNbPrepareNbLessThanMaxIdx.
  replace (maxIdx+1) with (maxNbPrepare+(maxIdx+1-maxNbPrepare)); try(lia). f_equal.
  apply getConfigBlocksAuxEqNoImpact with startaddr endaddr; trivial; try(lia); trivial.
  replace (maxNbPrepare+(maxIdx+1-maxNbPrepare)) with (maxIdx+1); try(lia). intros addr HaddrInRange.
  specialize(HaddrsInRange addr HaddrInRange). apply HaddrsInRange.
Qed.

Lemma getConfigPaddrEqNoImpact part s s0 startaddr endaddr:
isPADDR nullAddr s0
-> nextKernelIsValid s0
-> StructurePointerIsKS s0
-> (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
    -> ~In addr (getPartitions multiplexer s0)
        /\ ~In addr (getAllPaddrConfigAux (getConfigBlocks part s0) s0)
        /\ addr <> nullAddr)
-> (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> In part (getPartitions multiplexer s0)
-> getConfigPaddr part s = getConfigPaddr part s0.
Proof.
intros Hnull HnextProps Hstruct HaddrsInRange HaddrsOutRange HpartIsPart. unfold getConfigPaddr.
assert(HgetConfigBEq: getConfigBlocks part s = getConfigBlocks part s0).
{ apply getConfigBlocksEqNoImpact with startaddr endaddr; trivial. }
rewrite HgetConfigBEq. assert(Heq: getAllPaddrPDTAux [part] s = getAllPaddrPDTAux [part] s0).
{
  simpl. assert(HlookupPartEq: lookup part (memory s) beqAddr = lookup part (memory s0) beqAddr).
  {
    assert(HpropsOr: In part (getAllPaddrBlock startaddr endaddr) \/ ~In part (getAllPaddrBlock startaddr endaddr))
      by (apply classic).
    destruct HpropsOr as [Hcontra | Hres].
    { exfalso. apply HaddrsInRange in Hcontra. destruct Hcontra. congruence. }
    apply HaddrsOutRange; assumption.
  }
  rewrite HlookupPartEq. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial.
}
rewrite Heq. f_equal. clear HgetConfigBEq.
assert(HconfigAreBE: forall block, In block (getConfigBlocks part s0) -> isBE block s0).
{ intro block. apply configBlocksAreBE. }
induction (getConfigBlocks part s0); simpl in *; trivial.
assert(HlookupAEq: lookup a (memory s) beqAddr = lookup a (memory s0) beqAddr).
{
  assert(HpropsOr: In a (getAllPaddrBlock startaddr endaddr) \/ ~In a (getAllPaddrBlock startaddr endaddr))
    by (apply classic).
  destruct HpropsOr as [Hcontra | Hres].
  {
    exfalso. apply HaddrsInRange in Hcontra. destruct Hcontra as (_ & Hcontra & _). unfold isBE in *.
    assert(Htriv: a = a \/ In a l) by auto. specialize(HconfigAreBE a Htriv).
    destruct (lookup a (memory s0) beqAddr); try(congruence). destruct v; try(congruence). contradict Hcontra.
    apply in_or_app. left. rewrite kernelStructureTotalLengthVal. apply getAllPaddrBlockAuxIncl; lia.
  }
  apply HaddrsOutRange; assumption.
}
rewrite HlookupAEq. assert(HconfigAreBERec: forall block, In block l -> isBE block s0).
{ intros. apply HconfigAreBE; auto. }
assert(forall addr, In addr (getAllPaddrBlock startaddr endaddr)
   -> ~In addr (getPartitions multiplexer s0) /\ ~ In addr (getAllPaddrConfigAux l s0) /\ addr <> nullAddr).
{
  intros addr HaddrInRange. specialize(HaddrsInRange addr HaddrInRange). unfold isBE in *.
  assert(Htriv: a = a \/ In a l) by auto. specialize(HconfigAreBE a Htriv).
  destruct (lookup a (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  destruct HaddrsInRange as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). split; try(split); trivial.
  contradict HaddrNotConfig. apply in_or_app. auto.
}
rewrite IHl; trivial.
Qed.

Lemma completeParentsListChildPartial part1 part2 s blockToDelete blockTDStart:
(forall idPDchild sh1entryaddr part,
  idPDchild <> blockToDelete
  -> In part (getPartitions multiplexer s)
  -> In idPDchild (getMappedBlocks part s)
  -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
  -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
      /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> multiplexerIsPDT s
-> parentOfPartitionIsPartition s
-> noDupPartitionTree s
-> bentryStartAddr blockToDelete blockTDStart s
-> ~In blockTDStart (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In part1 (filterOptionPaddr (completeParentsList part2 s))
-> exists child, pdentryParent child part1 s
                /\ In child (getPartitions multiplexer s)
                /\ In child (part2::(filterOptionPaddr (completeParentsList part2 s))).
Proof.
intros HPDTIfPDFlag HmultIsPDT HparentOfPart HnoDupTree Hstart HstartNotPart. unfold completeParentsList.
revert part2.
induction (S (S maxAddr)); intros part2 Hpart2IsPart Hpart1IsAnc; simpl in *; try(exfalso; congruence).
assert(Hpart2IsPDT: isPDT part2 s).
{ apply partitionsArePDTPartial with blockToDelete blockTDStart; assumption. }
unfold isPDT in *. destruct (lookup part2 (memory s) beqAddr) eqn:HlookupPart2; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct (beqAddr part2 constantRootPartM) eqn:HbeqPart2Root; try(simpl in *; exfalso; congruence).
simpl in *. specialize(HparentOfPart part2 p HlookupPart2). destruct HparentOfPart as (HparentIsPart & _).
rewrite <-beqAddrFalse in HbeqPart2Root. specialize(HparentIsPart HbeqPart2Root).
destruct HparentIsPart as (_ & HparentIsPart). specialize(IHn (parent p) HparentIsPart).
destruct Hpart1IsAnc as [HparentIsPart1 | Hpart1IsAncRec].
- exists part2. unfold pdentryParent. rewrite HlookupPart2. split. intuition. split. assumption. left.
  reflexivity.
- specialize(IHn Hpart1IsAncRec). destruct IHn as [child (Hparent & HchildIsPart & HpropsOr)]. exists child.
  split. assumption. split. assumption. right. assumption.
Qed.

Lemma lastDescendantBlockAux n part s block startaddr:
isPADDR nullAddr s
-> wellFormedFstShadowIfBlockEntry s
-> partitionTreeIsTree s
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> isParent s
-> PDflagMeansNoChild s
-> childBlockNullIfChildNull s
-> pdchildIsPDT s
-> childLocHasSameStart s
-> In part (getPartitions multiplexer s)
-> isPDT part s
-> In block (getMappedBlocks part s)
-> bentryStartAddr block startaddr s
-> (forall desc parentsList, isParentsList s parentsList desc
    -> part = last parentsList nullAddr
    -> length parentsList <= n)
-> (exists desc blockDesc, In desc (getPartitions multiplexer s) /\ In blockDesc (getMappedBlocks desc s)
      /\ bentryStartAddr blockDesc startaddr s
      /\ sh1entryInChildLocationWeak (CPaddr (blockDesc+sh1offset)) nullAddr s).
Proof.
intros Hnull HwellSh1 Htree HnoDupTree HparentOfPart HisParent HnoChild HnullEquiv HPDchildIsPDT HsameStart.
revert part block. induction n; simpl; intros part block HpartIsPart HpartIsPDT HblockMapped Hstart HlenBound.
- assert(HblockIsBE: isBE block s).
  {
    apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)]. unfold isBE.
    rewrite Hlookup. trivial.
  }
  specialize(HwellSh1 block HblockIsBE). unfold isSHE in *.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  assert(HPDchild: exists idchild, sh1entryPDchild (CPaddr (block+sh1offset)) idchild s).
  { unfold sh1entryPDchild. rewrite HlookupSh1. exists (PDchild s0). reflexivity. }
  destruct HPDchild as [idchild HPDchild].
  assert(Hloc: exists blockChild, sh1entryInChildLocationWeak (CPaddr (block+sh1offset)) blockChild s).
  {
    unfold sh1entryInChildLocationWeak. exists (inChildLocation s0). rewrite HlookupSh1. reflexivity.
  }
  destruct Hloc as [blockChild Hloc]. assert(Hsh1: sh1entryAddr block (CPaddr (block+sh1offset)) s).
  {
    unfold isBE in *. unfold sh1entryAddr. destruct (lookup block (memory s) beqAddr); try(congruence).
    destruct v; congruence.
  }
  destruct (beqAddr idchild nullAddr) eqn:HbeqPDchildNull.
  + rewrite <-DTL.beqAddrTrue in HbeqPDchildNull. subst idchild. exists part. exists block.
    assert(blockChild = nullAddr).
    {
      specialize(HnullEquiv part block (CPaddr (block+sh1offset)) HpartIsPart HblockMapped Hsh1 HPDchild).
      unfold sh1entryInChildLocation in *. unfold sh1entryInChildLocationWeak in *. rewrite HlookupSh1 in *.
      destruct HnullEquiv as (HnullEquiv & _). rewrite <-HnullEquiv in *. assumption.
    }
    subst blockChild. auto.
  + rewrite <-beqAddrFalse in *. destruct (beqAddr blockChild nullAddr) eqn:HbeqBCNull.
    * rewrite <-DTL.beqAddrTrue in HbeqBCNull. subst blockChild. exists part. exists block. auto.
    * specialize(HPDchildIsPDT part block (CPaddr (block+sh1offset)) idchild HpartIsPart HblockMapped Hsh1 HPDchild
        HbeqPDchildNull). specialize(HisParent idchild part HpartIsPart HPDchildIsPDT). unfold pdentryParent in *.
      assert(HparentsList: isParentsList s [part] idchild).
      {
        simpl. unfold isPDT in *. destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; try(congruence).
        destruct v; try(congruence).
        destruct (lookup idchild (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). split; try(split); trivial; try(exists p0; auto).
        specialize(HparentOfPart idchild p0 HlookupChild). destruct HparentOfPart as (_ & HparentOfRoot & _).
        intro Hcontra. specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *. subst part. unfold isPADDR in *.
        rewrite HlookupPart in *. congruence.
      }
      assert(Hlast: part = last [part] nullAddr) by auto.
      specialize(HlenBound idchild [part] HparentsList Hlast). simpl in HlenBound. lia.
- assert(HblockIsBE: isBE block s).
  {
    apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)]. unfold isBE.
    rewrite Hlookup. trivial.
  }
  specialize(HwellSh1 block HblockIsBE). unfold isSHE in *.
  destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  assert(HPDchild: exists idchild, sh1entryPDchild (CPaddr (block+sh1offset)) idchild s).
  { unfold sh1entryPDchild. rewrite HlookupSh1. exists (PDchild s0). reflexivity. }
  destruct HPDchild as [idchild HPDchild].
  assert(Hloc: exists blockChild, sh1entryInChildLocationWeak (CPaddr (block+sh1offset)) blockChild s).
  {
    unfold sh1entryInChildLocationWeak. exists (inChildLocation s0). rewrite HlookupSh1. reflexivity.
  }
  destruct Hloc as [blockChild Hloc]. assert(Hsh1: sh1entryAddr block (CPaddr (block+sh1offset)) s).
  {
    unfold isBE in *. unfold sh1entryAddr. destruct (lookup block (memory s) beqAddr); try(congruence).
    destruct v; congruence.
  }
  destruct (beqAddr idchild nullAddr) eqn:HbeqPDchildNull.
  + rewrite <-DTL.beqAddrTrue in HbeqPDchildNull. subst idchild. exists part. exists block.
    assert(blockChild = nullAddr).
    {
      specialize(HnullEquiv part block (CPaddr (block+sh1offset)) HpartIsPart HblockMapped Hsh1 HPDchild).
      unfold sh1entryInChildLocation in *. unfold sh1entryInChildLocationWeak in *. rewrite HlookupSh1 in *.
      destruct HnullEquiv as (HnullEquiv & _). rewrite <-HnullEquiv in *. assumption.
    }
    subst blockChild. auto.
  + rewrite <-beqAddrFalse in *. destruct (beqAddr blockChild nullAddr) eqn:HbeqBCNull.
    * rewrite <-DTL.beqAddrTrue in HbeqBCNull. subst blockChild. exists part. exists block. auto.
    * rewrite <-beqAddrFalse in *.
      specialize(HPDchildIsPDT part block (CPaddr (block+sh1offset)) idchild HpartIsPart HblockMapped Hsh1 HPDchild
        HbeqPDchildNull). specialize(HisParent idchild part HpartIsPart HPDchildIsPDT).
      assert(HPDflag: sh1entryPDflag (CPaddr (block+sh1offset)) false s).
      {
        unfold sh1entryPDflag. rewrite HlookupSh1. destruct (PDflag s0) eqn:HPDflagVal; trivial. exfalso.
        assert(HPDflag: sh1entryPDflag (CPaddr (block+sh1offset)) true s).
        { unfold sh1entryPDflag. rewrite HlookupSh1. auto. }
        specialize(HnoChild block HblockIsBE HPDflag). unfold sh1entryPDchild in *. rewrite HlookupSh1 in *.
        rewrite <-HnoChild in *. congruence.
      }
      specialize(HsameStart part block (CPaddr (block+sh1offset)) blockChild idchild HpartIsPart HblockMapped Hsh1
        HPDchild Hloc HbeqPDchildNull HbeqBCNull). destruct HsameStart as (HsameStart & HblockCMapped).
      apply HsameStart in Hstart. assert(HchildIsPart: In idchild (getPartitions multiplexer s)).
      { apply childrenPartitionInPartitionList with part; assumption. }
      apply IHn with idchild blockChild; trivial.
      --- unfold isPDT. unfold pdentryParent in *. destruct (lookup idchild (memory s) beqAddr); try(congruence).
          destruct v; congruence.
      --- intros desc parentsList HparentsList Hlast.
          assert(HparentsListExt: isParentsList s (parentsList++[part]) desc).
          {
            apply parentsListCons with idchild; trivial.
            - simpl. unfold isPDT in *. destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; try(congruence).
              destruct v; try(congruence). unfold pdentryParent in *.
              destruct (lookup idchild (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
              destruct v; try(exfalso; congruence). split; try(split); trivial; try(exists p0; auto).
              specialize(HparentOfPart idchild p0 HlookupChild). destruct HparentOfPart as (_ & HparentOfRoot & _).
              intro Hcontra. specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *. subst part.
              unfold isPADDR in *. rewrite HlookupPart in *. congruence.
            - destruct parentsList.
              { simpl in *. congruence. }
              apply lastRec in Hlast. apply lastRecInc; assumption.
          }
          assert(HlastExt: part = last (parentsList++[part]) nullAddr) by (apply eq_sym; apply last_last).
          apply HlenBound in HparentsListExt; trivial. rewrite length_app in HparentsListExt. simpl in *. lia.
Qed.

Lemma lastDescendantBlock part s block startaddr:
isPADDR nullAddr s
-> wellFormedFstShadowIfBlockEntry s
-> partitionTreeIsTree s
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> isParent s
-> PDflagMeansNoChild s
-> childBlockNullIfChildNull s
-> pdchildIsPDT s
-> childLocHasSameStart s
-> In part (getPartitions multiplexer s)
-> isPDT part s
-> In block (getMappedBlocks part s)
-> bentryStartAddr block startaddr s
-> (exists desc blockDesc, In desc (getPartitions multiplexer s) /\ In blockDesc (getMappedBlocks desc s)
      /\ bentryStartAddr blockDesc startaddr s
      /\ sh1entryInChildLocationWeak (CPaddr (blockDesc+sh1offset)) nullAddr s).
Proof.
intros Hnull HwellSh1 Htree HnoDupTree HparentOfPart HisParent HnoChild HnullEquiv HPDchildIsPDT HsameStart
  HpartIsPart HpartIsPDT HblockMapped Hstart.
assert(HparentsListLen: forall desc parentsList, isParentsList s parentsList desc
  -> part = last parentsList nullAddr
  -> length parentsList <= maxAddr+1).
{
  intros desc parentsList HparentsList _. apply parentOfPartNotInParentsListsTail in HparentsList; trivial.
  apply lengthNoDupPartitions; trivial.
}
revert HparentsListLen. apply lastDescendantBlockAux with block; trivial.
Qed.

Lemma configAddressesBloodline part1 part2 addr s:
parentOfPartitionIsPartition s
-> isChild s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> noDupPartitionTree s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> wellFormedBlock s
-> isParent s
-> nullAddrExists s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupMappedPaddrList s
-> configAddrNotMappedInChild s
-> partitionsIsolation s
-> verticalSharing s
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In addr (getMappedPaddr part1 s)
-> In addr (getConfigPaddr part2 s)
-> In part1 (part2::filterOptionPaddr (completeParentsList part2 s)).
Proof.
intros HparentOfPart HisChild HPDTIfPDFlag HmultIsPDT HnoDupTree HequivParent Hwell HisParent Hnull Htree
  HnoDupMappedB HnoDupMappedP HconfigNotShared HPI HVS Hpart1IsPart Hpart2IsPart HaddrMapped1 HaddrConfig2.
assert(HaddrNotShared: forall child, In child (getChildren part2 s) -> ~In addr (getMappedPaddr child s)).
{
  intros child HchildIsChild. specialize(HconfigNotShared part2 child addr Hpart2IsPart HchildIsChild HaddrConfig2).
  assumption.
}
destruct (beqAddr part2 constantRootPartM) eqn:HbeqPart2Root.
- rewrite <-DTL.beqAddrTrue in HbeqPart2Root. subst part2.
  assert(Hpart1NotDesc: ~In constantRootPartM (filterOptionPaddr (completeParentsList part1 s))).
  {
    intro Hcontra. assert(Hchild: exists child, pdentryParent child constantRootPartM s
      /\ In child (getPartitions multiplexer s)
      /\ In child (part1::filterOptionPaddr (completeParentsList part1 s))).
    { apply completeParentsListChild; trivial. }
    destruct Hchild as [child (Hparent & HchildIsPart & HchildIsAnc)].
    assert(HbeqChildRoot: child <> constantRootPartM).
    {
      unfold pdentryParent in *.
      destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild). rewrite <-Hparent in *.
      destruct HparentOfPart as (_ & _ & Hres). auto.
    }
    assert(isChild s) by assumption.
    specialize(HisChild child constantRootPartM HchildIsPart Hparent HbeqChildRoot).
    specialize(HaddrNotShared child HisChild). contradict HaddrNotShared. simpl in HchildIsAnc.
    destruct HchildIsAnc as [Heq | HchildIsAnc]; try(subst child; assumption). revert HaddrMapped1.
    apply addrBelongToAncestors; trivial. apply blockInclImpliesAddrIncl; trivial.
  }
  simpl. left. destruct (beqAddr constantRootPartM part1) eqn:HbeqRootPart1; try(rewrite DTL.beqAddrTrue; assumption).
  exfalso. rewrite <-beqAddrFalse in *. contradict Hpart1NotDesc.
  apply getPartitionsGivesAncestor with (maxAddr+2); trivial. apply partitionsArePDT; trivial.
- rewrite <-beqAddrFalse in *.
  assert(Hlookup2: exists pdentry2, lookup part2 (memory s) beqAddr = Some(PDT pdentry2)).
  { apply isPDTLookupEq. apply partitionsArePDT; trivial. }
  destruct Hlookup2 as [pdentry2 Hlookup2]. assert(HparentOfPartCopy: parentOfPartitionIsPartition s) by assumption.
  specialize(HparentOfPartCopy part2 pdentry2 Hlookup2).
  destruct HparentOfPartCopy as (HparentIsPart & _ & HbeqParentPart2). specialize(HparentIsPart HbeqPart2Root).
  destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
  assert(Hparent: pdentryParent part2 (parent pdentry2) s) by (unfold pdentryParent; rewrite Hlookup2; reflexivity).
  assert(Hpart2IsChild: isChild s) by assumption.
  specialize(Hpart2IsChild part2 (parent pdentry2) Hpart2IsPart Hparent HbeqPart2Root).
  assert(HaddrUsedParent: In addr (getUsedPaddr part2 s)).
  { unfold getUsedPaddr. apply in_or_app. auto. }
  assert(HVSCopy: verticalSharing s) by assumption.
  specialize(HVS (parent pdentry2) part2 HparentIsPart Hpart2IsChild addr HaddrUsedParent).
  pose proof (addressesBloodline addr part1 (parent pdentry2) s HisParent HnoDupTree HparentOfPart HPDTIfPDFlag
    HmultIsPDT Hnull Htree HnoDupMappedB HnoDupMappedP Hwell HisChild HequivParent HPI Hpart1IsPart HparentIsPart
    HaddrMapped1 HVS) as Hbloodline.
  destruct Hbloodline as [Hpart1IsAncParent | [HbeqPart1Parent | HparentIsAnc1]].
  + simpl. right. unfold completeParentsList in *.
    assert(HlistEq: filterOptionPaddr (completeParentsListRec (S maxAddr) (parent pdentry2) s)
      = filterOptionPaddr (completeParentsListRec (S (S maxAddr)) (parent pdentry2) s)).
    {
      apply completeParentsListRecEqIfLenLowEnough; try(lia). replace (S maxAddr) with (maxAddr+1); try(lia).
      apply lengthNoDupPartitions. apply parentOfPartNotInParentsListsTail with (parent pdentry2) s; trivial.
      apply completeParentsListIsParentsListAux; trivial. unfold isPDT. rewrite HlookupParent. trivial.
    }
    rewrite <-HlistEq in Hpart1IsAncParent. replace (S maxAddr) with (maxAddr+1) in *; try(lia). simpl.
    rewrite Hlookup2. rewrite beqAddrFalse in *. rewrite HbeqPart2Root. simpl. auto.
  + simpl. right. unfold completeParentsList. replace (S maxAddr) with (maxAddr+1); try(lia). simpl.
    rewrite Hlookup2. rewrite beqAddrFalse in *. rewrite HbeqPart2Root. simpl. auto.
  + simpl. left. assert(Hchild: exists child, pdentryParent child (parent pdentry2) s
      /\ In child (getPartitions multiplexer s)
      /\ In child (part1 :: filterOptionPaddr (completeParentsList part1 s))).
    { apply completeParentsListChild; trivial. }
    destruct Hchild as [child (HparentB & HchildIsPart & HchildIsAnc)]. assert(child = part2).
    {
      assert(HbeqChildRoot: child <> constantRootPartM).
      {
        unfold pdentryParent in *.
        destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild). rewrite <-HparentB in *.
        destruct HparentOfPart as (_ & HparentOfRoot & _). intro Hcontra. specialize(HparentOfRoot Hcontra).
        rewrite HparentOfRoot in *. unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupParent in *.
        congruence.
      }
      assert(HisChildCopy: isChild s) by assumption.
      specialize(HisChild child (parent pdentry2) HchildIsPart HparentB HbeqChildRoot).
      destruct (beqAddr child part2) eqn:HbeqChildren; try(rewrite DTL.beqAddrTrue; assumption).
      rewrite <-beqAddrFalse in *. assert(HaddrUsedChild: In addr (getUsedPaddr child s)).
      {
        unfold getUsedPaddr. apply in_or_app. simpl in HchildIsAnc. destruct HchildIsAnc as [Heq | HchildIsAnc].
        - subst child. auto.
        - right. assert(Hlookup1: exists pdentry1, lookup part1 (memory s) beqAddr = Some(PDT pdentry1)).
          { apply isPDTLookupEq. apply partitionsArePDT; trivial. }
          destruct Hlookup1 as [pdentry1 Hlookup1]. assert(HbeqPart1Root: part1 <> constantRootPartM).
          {
            unfold completeParentsList in HchildIsAnc. replace (S maxAddr) with (maxAddr+1) in *; try(lia).
            simpl in HchildIsAnc. rewrite Hlookup1 in *.
            destruct (beqAddr part1 constantRootPartM) eqn:Hres; try(simpl in HchildIsAnc; exfalso; congruence).
            rewrite <-beqAddrFalse in *. assumption.
          }
          assert(In (parent pdentry1) (getPartitions multiplexer s)).
          {
            specialize(HparentOfPart part1 pdentry1 Hlookup1). destruct HparentOfPart as (Hparent1IsPart & _).
            specialize(Hparent1IsPart HbeqPart1Root). apply Hparent1IsPart.
          }
          assert(HaddrMappedParent1: In addr (getMappedPaddr (parent pdentry1) s)).
          {
            unfold verticalSharing in *. unfold incl in *. apply HVSCopy with part1; trivial.
            - unfold isChild in *. apply HisChildCopy; trivial. unfold pdentryParent. rewrite Hlookup1. reflexivity.
            - unfold getUsedPaddr. apply in_or_app. auto.
          }
          unfold completeParentsList in HchildIsAnc. replace (S maxAddr) with (maxAddr+1) in *; try(lia).
          simpl in HchildIsAnc. rewrite Hlookup1 in *. rewrite beqAddrFalse in *. rewrite HbeqPart1Root in *.
          simpl in HchildIsAnc. destruct HchildIsAnc as [Heq | HchildIsAnc]; try(rewrite Heq in *; assumption).
          assert(HchildIsAncRec: In child (filterOptionPaddr (completeParentsList (parent pdentry1) s))).
          {
            unfold completeParentsList. revert HchildIsAnc. apply completeParentsListRecN; lia.
          }
          revert HaddrMappedParent1. apply addrBelongToAncestors; trivial. apply blockInclImpliesAddrIncl; trivial.
      }
      specialize(HPI (parent pdentry2) child part2 HparentIsPart HisChild Hpart2IsChild HbeqChildren addr
        HaddrUsedChild). exfalso; congruence.
    }
    subst child. simpl in HchildIsAnc. destruct HchildIsAnc as [Hres | HchildIsAnc]; auto. exfalso.
    clear HparentB. clear HchildIsPart.
    assert(Hchild: exists child, pdentryParent child part2 s
      /\ In child (getPartitions multiplexer s)
      /\ In child (part1 :: filterOptionPaddr (completeParentsList part1 s))).
    { apply completeParentsListChild; trivial. }
    destruct Hchild as [child (HparentB & HchildIsPart & HchildBIsAnc)].
    assert(HbeqChildRoot: child <> constantRootPartM).
    {
      unfold pdentryParent in *.
      destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild). rewrite <-HparentB in *.
      destruct HparentOfPart as (_ & HparentOfRoot & _). intro Hcontra. specialize(HparentOfRoot Hcontra).
      rewrite HparentOfRoot in *. unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hlookup2 in *.
      congruence.
    }
    assert(isChild s) by assumption.
    specialize(HisChild child part2 HchildIsPart HparentB HbeqChildRoot). specialize(HaddrNotShared child HisChild).
    contradict HaddrNotShared. simpl in HchildBIsAnc.
    destruct HchildBIsAnc as [Heq | HchildBIsAnc]; try(subst child; assumption). revert HaddrMapped1.
    apply addrBelongToAncestors; trivial. apply blockInclImpliesAddrIncl; trivial.
Qed.

Lemma addrInKernIsConfig addr (kernel: paddr) l s:
In kernel l
-> isBE kernel s
-> In addr (getAllPaddrBlockAux 0 kernel Constants.kernelStructureTotalLength)
-> In addr (getAllPaddrConfigAux l s).
Proof.
induction l; simpl; intros HkernIn HkernIsBE HaddrIn; try(congruence). destruct HkernIn as [Heq | HkernIn].
- subst a. unfold isBE in *. destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). apply in_or_app. left. assumption.
- specialize(IHl HkernIn HkernIsBE HaddrIn). destruct (lookup a (memory s) beqAddr); try(assumption).
  destruct v; try(assumption). apply in_or_app. right. assumption.
Qed.

(*TODO HERE not sure the next lemmas will be applicable*)

Lemma getPartitionsGivesAncestorPartial n partition newRoot s exceptionBlock blockStart:
(* isParent s *)
(forall partition pdparent,
    partition <> blockStart
    -> In pdparent (getPartitions multiplexer s)
    -> In partition (getChildren pdparent s) -> pdentryParent partition pdparent s)
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> (* PDTIfPDFlag s *)
    (forall idPDchild sh1entryaddr part, idPDchild <> exceptionBlock
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> bentryStartAddr exceptionBlock blockStart s
-> lookup blockStart (memory s) beqAddr = None
-> isPDT partition s
-> In newRoot (getPartitions multiplexer s)
-> In partition (getPartitionsAux n newRoot s)
-> newRoot <> partition
-> In newRoot (filterOptionPaddr (completeParentsList partition s)).
Proof.
intros HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HstartExcept
  HlookupStart HpartIsPDT.
revert newRoot. induction n; simpl; try(intros; exfalso; congruence).
intros newRoot HnewRootIsPart HpartIsPart HbeqPartNewRoot.
destruct HpartIsPart as [HbeqRootPart | HpartIsPartRec]; try(exfalso; congruence).
assert(Hchildren: forall child, In child (getChildren newRoot s)
          -> child <> blockStart
          -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
{
  intros child HchildIsChild HbeqChildStart.
  specialize(HisParent child newRoot HbeqChildStart HnewRootIsPart HchildIsChild). split. assumption.
  apply childrenPartitionInPartitionList with newRoot; assumption.
}
induction (getChildren newRoot s); simpl in *; try(exfalso; congruence). apply in_app_or in HpartIsPartRec.
assert(HchildrenRec: forall child, In child l
        -> child <> blockStart
        -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
{
  intros child HchildIsChild HbeqChildStart. apply Hchildren; auto.
}
destruct HpartIsPartRec as [HpartInPartsA | HpartIsPartRecRec]; try(apply IHl; assumption).
assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). assert(HbeqAStart: a <> blockStart).
{
  intros ->. clear IHn. clear IHl. destruct n; simpl in HpartInPartsA; try(congruence).
  destruct HpartInPartsA as [<- | Hcontra]; unfold isPDT in *; unfold getChildren in *; rewrite HlookupStart in *;
    simpl in *; congruence.
}
specialize(Hchildren a HeqTriv HbeqAStart). destruct Hchildren as (HparentA & HaIsPart).
destruct (beqAddr a partition) eqn:HbeqAPart.
- rewrite <-DTL.beqAddrTrue in HbeqAPart. subst a. unfold completeParentsList. pose proof maxAddrNotZero.
  destruct maxAddr; try(lia). simpl. unfold pdentryParent in HparentA.
  destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). destruct (beqAddr partition constantRootPartM) eqn:HbeqPartRoot.
  {
    rewrite <-DTL.beqAddrTrue in HbeqPartRoot. subst partition. simpl.
    specialize(HparentOfPart constantRootPartM p HlookupPart). destruct HparentOfPart as (_ & HparentOfRoot & _).
    assert(Heq: constantRootPartM = constantRootPartM) by reflexivity. specialize(HparentOfRoot Heq).
    rewrite <-HparentA in *. rewrite HparentOfRoot in *.
    assert(HnullIsPDT: isPDT nullAddr s).
    { apply partitionsArePDTPartial with exceptionBlock blockStart; assumption. }
    unfold isPDT in *. unfold nullAddrExists in *. unfold isPADDR in *.
    destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-HparentA. simpl. left. reflexivity.
- rewrite <-beqAddrFalse in HbeqAPart. specialize(IHn a HaIsPart HpartInPartsA HbeqAPart).
  revert IHn. apply parentIsInParentList; try(assumption).
  apply partitionsArePDTPartial with exceptionBlock blockStart; assumption.
Qed.

Lemma addrBelongToAncestorsPartial desc partition addr s exceptionBlock blockStart:
isChild s
-> (* PDTIfPDFlag s *)
    (forall idPDchild sh1entryaddr part, idPDchild <> exceptionBlock
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> multiplexerIsPDT s
-> parentOfPartitionIsPartition s
-> noDupPartitionTree s
-> childPaddrIsIntoParent s
-> bentryStartAddr exceptionBlock blockStart s
-> ~In blockStart (getPartitions multiplexer s)
-> In desc (getPartitions multiplexer s)
-> In partition (getPartitions multiplexer s)
-> In partition (filterOptionPaddr (completeParentsList desc s))
-> In addr (getMappedPaddr desc s)
-> In addr (getMappedPaddr partition s).
Proof.
intros HisChild HPDTIfPDFlag HmultIsPDT HparentOfPart HnoDupTree HchildInclParent HstartExcept HstartNotPart
  HdescIsPart HpartIsPart HdescIsDesc HaddrMappedDesc.
revert desc HaddrMappedDesc HdescIsPart HdescIsDesc.
unfold completeParentsList in *. induction (S (S maxAddr)); intros; simpl in *; try(exfalso; congruence).
assert(HdescIsPDT: isPDT desc s).
{ apply partitionsArePDTPartial with exceptionBlock blockStart; assumption. }
unfold isPDT in HdescIsPDT. destruct (lookup desc (memory s) beqAddr) eqn:HlookupDesc; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct (beqAddr desc constantRootPartM) eqn:HbeqDescRoot; simpl in *; try(exfalso; congruence).
specialize(HparentOfPart desc p HlookupDesc). destruct HparentOfPart as (HparentIsPart & _).
rewrite <-beqAddrFalse in *. specialize(HparentIsPart HbeqDescRoot).
destruct HparentIsPart as (_ & HparentIsPart).
assert(HaddrMappedParent: In addr (getMappedPaddr (parent p) s)).
{
  assert(Hparent: pdentryParent desc (parent p) s).
  {
    unfold pdentryParent. rewrite HlookupDesc. reflexivity.
  }
  assert(HdescIsChild: In desc (getChildren (parent p) s)).
  {
    specialize(HisChild desc (parent p) HdescIsPart Hparent HbeqDescRoot). assumption.
  }
  specialize(HchildInclParent (parent p) desc addr HparentIsPart HdescIsChild HaddrMappedDesc). assumption.
}
destruct HdescIsDesc as [HpartIsParent | HdescIsDescRec]; try(apply IHn with (parent p); assumption).
rewrite HpartIsParent in *. assumption.
Qed.

Lemma addrCannotBeInSeparateBloodlinesPartial n addr part part1 part2 newRoot l s exceptionBlock blockStart:
partitionsIsolation s
-> isChild s
-> (* isParent s *)
    (forall partition pdparent,
      partition <> blockStart
      -> In pdparent (getPartitions multiplexer s)
      -> In partition (getChildren pdparent s) -> pdentryParent partition pdparent s)
-> parentOfPartitionIsPartition s
-> noDupPartitionTree s
-> (* PDTIfPDFlag s *)
    (forall idPDchild sh1entryaddr part, idPDchild <> exceptionBlock
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> wellFormedBlock s
-> bentryStartAddr exceptionBlock blockStart s
-> ~In blockStart (getPartitions multiplexer s)
-> lookup blockStart (memory s) beqAddr = None
-> In addr (getMappedPaddr part1 s)
-> In addr (getMappedPaddr part2 s)
-> In part1 (getPartitionsAux n part s)
-> In part2 (flat_map (fun p : paddr => getPartitionsAux n p s) l)
-> (forall child, In child l -> child <> blockStart
      -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)
          /\ child <> constantRootPartM)
-> ~ In part l
-> pdentryParent part newRoot s
-> In part (getPartitions multiplexer s)
-> In newRoot (getPartitions multiplexer s)
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> part <> constantRootPartM
-> False.
Proof.
intros HPI HisChild HisParent HparentOfPart HnoDupTree HPDTIfPDFlag HmultIsPDT HnullExists Htree
  HblockEquivParent HwellFormed HstartExcept HstartNotPart HlookupStart HaddrMapped1 HaddrMapped2 Hpart1IsPart
  Hpart2IsPart HlistElAreChildren HpartNotInList Hparent HpartIsPart HnewRootIsPart Hpart1IsPartM
  Hpart2IsPartM HbeqPartRoot.
induction l; simpl in *; try(congruence). apply in_app_or in Hpart2IsPart.
assert(HlistElAreChildrenRec: forall child, In child l
        -> child <> blockStart
        -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)
          /\ child <> constantRootPartM).
{ intros child HchildIn HbeqChildStart. apply HlistElAreChildren; auto. }
apply not_or_and in HpartNotInList. destruct HpartNotInList as (HbeqAPart & HpartNotInListRec).
destruct Hpart2IsPart as [Hpart2IsPart | Hpart2IsPartRec]; try(apply IHl; assumption).
assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). assert(HbeqAStart: a <> blockStart).
{
  intros ->. clear Hpart1IsPart. clear IHl. destruct n; simpl in Hpart2IsPart; try(congruence).
  destruct Hpart2IsPart as [<- | Hcontra]; try(congruence). unfold getChildren in *. rewrite HlookupStart in *.
  simpl in Hcontra. congruence.
}
specialize(HlistElAreChildren a HeqTriv HbeqAStart).
destruct HlistElAreChildren as (HaIsChild & HaIsPart & HbeqARoot). assert(Hchild1: In a (getChildren newRoot s)).
{
  specialize(HisChild a newRoot HaIsPart HaIsChild HbeqARoot). assumption.
}
assert(Hchild2: In part (getChildren newRoot s)).
{
  specialize(HisChild part newRoot HpartIsPart Hparent HbeqPartRoot). assumption.
}
specialize(HPI newRoot a part HnewRootIsPart Hchild1 Hchild2 HbeqAPart).
assert(Hpart1IsPDT: isPDT part1 s).
{ apply partitionsArePDTPartial with exceptionBlock blockStart; assumption. }
assert(Hpart2IsPDT: isPDT part2 s).
{ apply partitionsArePDTPartial with exceptionBlock blockStart; assumption. }
pose proof (getPartitionsGivesAncestorPartial n part1 part s exceptionBlock blockStart HisParent HnoDupTree
  HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists Htree HstartExcept HstartNotPart HlookupStart
  Hpart1IsPDT HpartIsPart Hpart1IsPart) as Hancestor1.
pose proof (getPartitionsGivesAncestorPartial n part2 a s exceptionBlock blockStart HisParent HnoDupTree HparentOfPart
  HPDTIfPDFlag HmultIsPDT HnullExists Htree HstartExcept HstartNotPart HlookupStart Hpart2IsPDT HaIsPart Hpart2IsPart)
  as Hancestor2.
assert(HaddrMappedA: In addr (getUsedPaddr a s)).
{
  unfold getUsedPaddr. apply in_or_app. right. destruct (beqAddr a part2) eqn:HbeqAPart2.
  - rewrite <-DTL.beqAddrTrue in HbeqAPart2. subst a. assumption.
  - rewrite <-beqAddrFalse in HbeqAPart2. specialize(Hancestor2 HbeqAPart2).
    apply addrBelongToAncestorsPartial with part2 exceptionBlock blockStart; trivial.
    apply blockInclImpliesAddrIncl; assumption.
}
assert(HaddrMappedPart: In addr (getUsedPaddr part s)).
{
  unfold getUsedPaddr. apply in_or_app. right. destruct (beqAddr part part1) eqn:HbeqPartPart1.
  - rewrite <-DTL.beqAddrTrue in HbeqPartPart1. subst part. assumption.
  - rewrite <-beqAddrFalse in HbeqPartPart1. specialize(Hancestor1 HbeqPartPart1).
    apply addrBelongToAncestorsPartial with part1 exceptionBlock blockStart; trivial.
    apply blockInclImpliesAddrIncl; assumption.
}
specialize(HPI addr HaddrMappedA). congruence.
Qed.

Lemma addressesBloodlineAuxPartial part1 part2 newRoot addr n s exceptionBlock blockStart:
(* isParent s *)
(forall partition pdparent,
    partition <> blockStart
    -> In pdparent (getPartitions multiplexer s)
    -> In partition (getChildren pdparent s) -> pdentryParent partition pdparent s)
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> (* PDTIfPDFlag s *)
    (forall idPDchild sh1entryaddr part, idPDchild <> exceptionBlock
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupMappedPaddrList s
-> wellFormedBlock s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> partitionsIsolation s
-> bentryStartAddr exceptionBlock blockStart s
-> ~In blockStart (getPartitions multiplexer s)
-> lookup blockStart (memory s) beqAddr = None
-> isPDT part1 s
-> isPDT part2 s
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In addr (getMappedPaddr part1 s)
-> In addr (getMappedPaddr part2 s)
-> In newRoot (getPartitions multiplexer s)
-> In part1 (getPartitionsAux n newRoot s)
-> In part2 (getPartitionsAux n newRoot s)
-> In part1 (filterOptionPaddr (completeParentsList part2 s))
    \/ part1 = part2
    \/ In part2 (filterOptionPaddr (completeParentsList part1 s)).
Proof.
intros HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HnoDupBlocks
  HnoDupPaddr HwellFormed HisChild HblockEquivParent HPI HstartExcept HstartNotPart HlookupStart Hpart1IsPDT
  Hpart2IsPDT Hpart1IsPartM Hpart2IsPartM HaddrMapped1 HaddrMapped2.
revert newRoot. induction n.
{ simpl in *. intros. exfalso. congruence. }
intros newRoot HnewRootIsPart Hpart1IsPart Hpart2IsPart.
assert(Hchildren: forall child, In child (getChildren newRoot s)
          -> child <> blockStart
          -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
{
  intros child HchildIsChild HbeqChildStart.
  specialize(HisParent child newRoot HbeqChildStart HnewRootIsPart HchildIsChild). split.
  assumption. apply childrenPartitionInPartitionList with newRoot; assumption.
}
simpl in *. destruct (beqAddr newRoot part1) eqn:HbeqNewRootPart1.
- rewrite <-DTL.beqAddrTrue in HbeqNewRootPart1. subst part1. clear Hpart1IsPart.
  destruct (beqAddr newRoot part2) eqn:HbeqNewRootPart2.
  + rewrite <-DTL.beqAddrTrue in HbeqNewRootPart2. subst part2. right. left. reflexivity.
  + rewrite <-beqAddrFalse in HbeqNewRootPart2.
    destruct Hpart2IsPart as [Hcontra | Hpart2IsPartRec]; try(exfalso; congruence). left.
    induction (getChildren newRoot s); simpl in *; try(exfalso; congruence).
    apply in_app_or in Hpart2IsPartRec.
    assert(HchildrenRec: forall child, In child l
            -> child <> blockStart
            -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
    {
      intros child HbeqChildStart HchildInList. apply Hchildren; auto.
    }
    destruct Hpart2IsPartRec as [Hpart2IsPartA | Hpart2IsPartRecRec]; try(apply IHl; assumption).
    assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). destruct (beqAddr a blockStart) eqn:HbeqAStart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqAStart. subst a. assert(part2 = blockStart).
      {
        clear IHn. clear IHl. destruct n; simpl in Hpart2IsPartA; try(exfalso; congruence).
        destruct Hpart2IsPartA as [Hres | Hcontra]; auto. unfold getChildren in *. rewrite HlookupStart in *.
        simpl in Hcontra. exfalso; congruence.
      }
      subst part2. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. specialize(Hchildren a HeqTriv HbeqAStart).
    destruct Hchildren as (HparentA & HAIsPart). destruct (beqAddr a part2) eqn:HbeqAPart2.
    * rewrite <-DTL.beqAddrTrue in HbeqAPart2. subst a. unfold pdentryParent in HparentA.
      unfold completeParentsList. simpl.
      destruct (lookup part2 (memory s) beqAddr) eqn:HlookupPart2; try(simpl; congruence).
      destruct v; try(simpl; congruence). destruct (beqAddr part2 constantRootPartM) eqn:HbeqPart2Root.
      {
        simpl. rewrite <-DTL.beqAddrTrue in HbeqPart2Root. specialize(HparentOfPart part2 p HlookupPart2).
        destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot HbeqPart2Root).
        rewrite <-HparentA in *. rewrite HparentOfRoot in *. unfold isPDT in *. unfold nullAddrExists in *.
        unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-HparentA. simpl. left. reflexivity.
    * rewrite <-beqAddrFalse in HbeqAPart2.
      pose proof (getPartitionsGivesAncestorPartial n part2 a s exceptionBlock blockStart HisParent HnoDupTree
        HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HstartExcept HstartNotPart HlookupStart
        Hpart2IsPDT HAIsPart Hpart2IsPartA HbeqAPart2) as Hres.
      apply parentIsInParentList with a; assumption.
- rewrite <-beqAddrFalse in HbeqNewRootPart1.
  destruct Hpart1IsPart as [Hcontra | Hpart1IsPartRec]; try(exfalso; congruence).
  destruct (beqAddr newRoot part2) eqn:HbeqNewRootPart2.
  + rewrite <-DTL.beqAddrTrue in HbeqNewRootPart2. subst part2. clear Hpart2IsPart. right. right.
    induction (getChildren newRoot s); simpl in *; try(exfalso; congruence).
    apply in_app_or in Hpart1IsPartRec.
    assert(HchildrenRec: forall child, In child l
            -> child <> blockStart
            -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
    {
      intros child HchildInList HbeqChildStart. apply Hchildren; auto.
    }
    destruct Hpart1IsPartRec as [Hpart1IsPartA | Hpart1IsPartRecRec]; try(apply IHl; assumption).
    assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). assert(HbeqAStart: a <> blockStart).
    {
      intros ->. clear IHn. clear IHl. destruct n; simpl in Hpart1IsPartA; try(congruence).
      destruct Hpart1IsPartA as [<- | Hcontra]; try(congruence). unfold getChildren in *. rewrite HlookupStart in *.
      simpl in Hcontra; congruence.
    }
    specialize(Hchildren a HeqTriv HbeqAStart). destruct Hchildren as (HparentA & HAIsPart).
    destruct (beqAddr a part1) eqn:HbeqAPart1.
    * rewrite <-DTL.beqAddrTrue in HbeqAPart1. subst a. unfold pdentryParent in *. unfold completeParentsList.
      simpl. destruct (lookup part1 (memory s) beqAddr) eqn:HlookupPart1; try(simpl; congruence).
      destruct v; try(simpl; congruence). destruct (beqAddr part1 constantRootPartM) eqn:HbeqPart1Root.
      {
        simpl. specialize(HparentOfPart part1 p HlookupPart1). destruct HparentOfPart as (_ & HparentOfRoot & _).
        rewrite <-DTL.beqAddrTrue in HbeqPart1Root. specialize(HparentOfRoot HbeqPart1Root).
        rewrite <-HparentA in *. rewrite HparentOfRoot in *. unfold isPDT in *. unfold nullAddrExists in *.
        unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-HparentA. simpl. left. reflexivity.
    * rewrite <-beqAddrFalse in HbeqAPart1.
      pose proof (getPartitionsGivesAncestorPartial n part1 a s exceptionBlock blockStart HisParent HnoDupTree
          HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HstartExcept HstartNotPart HlookupStart
          Hpart1IsPDT HAIsPart Hpart1IsPartA HbeqAPart1) as Hres.
      apply parentIsInParentList with a; assumption.
  + rewrite <-beqAddrFalse in HbeqNewRootPart2.
    destruct Hpart2IsPart as [Hcontra | Hpart2IsPartRec]; try(exfalso; congruence).
    assert(HnoDupChildren: NoDup (getChildren newRoot s)).
    {
      apply noDupGetChildren; try(assumption).
      apply partitionsArePDTPartial with exceptionBlock blockStart; assumption.
    }
    induction (getChildren newRoot s); simpl in *; try(exfalso; congruence). apply in_app_or in Hpart1IsPartRec.
    apply in_app_or in Hpart2IsPartRec. apply NoDup_cons_iff in HnoDupChildren.
    destruct HnoDupChildren as (HaNotInList & HnoDupChildrenRec).
    assert(HchildrenRec: forall child, In child l
            -> child <> blockStart
            -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
    {
      intros child HchildInList HbeqChildStart. apply Hchildren; auto.
    }
    assert(HeqTriv: a = a \/ In a l) by (left; reflexivity).
    assert(forall child, In child l -> child <> blockStart
              -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)
                  /\ child <> constantRootPartM).
    {
      intros child HchildIn HbeqChildStart. specialize(HchildrenRec child HchildIn HbeqChildStart).
      destruct HchildrenRec as (Hparent & HchildIsPart). split. assumption. split. assumption.
      unfold pdentryParent in *. intro Hcontra.
      destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(congruence). destruct v; try(congruence).
      specialize(HparentOfPart child p HlookupChild). destruct HparentOfPart as (_ & HparentOfRoot & _).
      specialize(HparentOfRoot Hcontra). rewrite <-Hparent in *. rewrite HparentOfRoot in *.
      assert(HnullIsPDT: isPDT nullAddr s).
      { apply partitionsArePDTPartial with exceptionBlock blockStart; assumption. }
      unfold isPDT in *. unfold nullAddrExists in *. unfold isPADDR in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    destruct (beqAddr a blockStart) eqn:HbeqAStart.
    * rewrite <-DTL.beqAddrTrue in HbeqAStart. subst a.
      assert(Hrec: In part1 (flat_map (fun p : paddr => getPartitionsAux n p s) l)
        /\ In part2 (flat_map (fun p : paddr => getPartitionsAux n p s) l)).
      {
        clear IHl. clear IHn. assert(~In part1 (getPartitionsAux n blockStart s)).
        {
          clear Hpart1IsPartRec. clear Hpart2IsPartRec. intro Hcontra. destruct n; simpl in Hcontra; try(congruence).
          destruct Hcontra as [<- | Hcontra]; try(congruence). unfold getChildren in *. rewrite HlookupStart in *.
          simpl in Hcontra. congruence.
        }
        assert(~In part2 (getPartitionsAux n blockStart s)).
        {
          clear Hpart1IsPartRec. clear Hpart2IsPartRec. intro Hcontra. destruct n; simpl in Hcontra; try(congruence).
          destruct Hcontra as [<- | Hcontra]; try(congruence). unfold getChildren in *. rewrite HlookupStart in *.
          simpl in Hcontra. congruence.
        }
        destruct Hpart1IsPartRec; try(exfalso; congruence). destruct Hpart2IsPartRec; try(exfalso; congruence).
        auto.
      }
      destruct Hrec. apply IHl; assumption.
    * rewrite <-beqAddrFalse in *. specialize(Hchildren a HeqTriv HbeqAStart). clear HeqTriv.
      destruct Hchildren as (HparentA & HaIsPart). assert(HbeqARoot: a <> constantRootPartM).
      {
        unfold pdentryParent in *. intro Hcontra.
        destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(congruence). destruct v; try(congruence).
        specialize(HparentOfPart a p HlookupA). destruct HparentOfPart as (_ & HparentOfRoot & _).
        specialize(HparentOfRoot Hcontra). rewrite <-HparentA in *. rewrite HparentOfRoot in *.
        assert(HnullIsPDT: isPDT nullAddr s).
        { apply partitionsArePDTPartial with exceptionBlock blockStart; assumption. }
        unfold isPDT in *. unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      destruct Hpart1IsPartRec as [Hpart1IsPartA | Hpart1IsPartRecRec].
      --- destruct Hpart2IsPartRec as [Hpart2IsPartA | Hpart2IsPartRecRec]; try(apply IHn with a; assumption).
          exfalso. apply addrCannotBeInSeparateBloodlinesPartial with n addr a part1 part2 newRoot l s exceptionBlock
            blockStart; assumption.
      --- destruct Hpart2IsPartRec as [Hpart2IsPartA | Hpart2IsPartRecRec]; try(apply IHl; assumption).
          exfalso. apply addrCannotBeInSeparateBloodlinesPartial with n addr a part2 part1 newRoot l s exceptionBlock
            blockStart; assumption.
Qed.

Lemma addressesBloodlinePartial addr part1 part2 s exceptionBlock blockStart:
(* isParent s *)
(forall partition pdparent,
    partition <> blockStart
    -> In pdparent (getPartitions multiplexer s)
    -> In partition (getChildren pdparent s) -> pdentryParent partition pdparent s)
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> (* PDTIfPDFlag s *)
    (forall idPDchild sh1entryaddr part, idPDchild <> exceptionBlock
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupMappedPaddrList s
-> wellFormedBlock s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> partitionsIsolation s
-> bentryStartAddr exceptionBlock blockStart s
-> ~In blockStart (getPartitions multiplexer s)
-> lookup blockStart (memory s) beqAddr = None
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In addr (getMappedPaddr part1 s)
-> In addr (getMappedPaddr part2 s)
-> In part1 (filterOptionPaddr (completeParentsList part2 s))
    \/ part1 = part2
    \/ In part2 (filterOptionPaddr (completeParentsList part1 s)).
Proof.
intros HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HnoDupBlocks
  HnoDupPaddr HwellFormed HisChild HblockEquivParent HPI Hpart1IsPart Hpart2IsPart HstartExcept HstartNotPart
  HlookupStart HaddrMapped1 HaddrMapped2.
apply addressesBloodlineAuxPartial with multiplexer addr (maxAddr + 2) exceptionBlock blockStart; try(assumption).
- apply partitionsArePDTPartial with exceptionBlock blockStart; assumption.
- apply partitionsArePDTPartial with exceptionBlock blockStart; assumption.
- unfold getPartitions. replace (maxAddr + 2) with (S(maxAddr + 1)); try(lia). simpl. left. reflexivity.
Qed.

Lemma addressesBloodlineIfNotSharedPartial s part1 part2 addr block exceptionBlock blockStart:
(* isParent s *)
(forall partition pdparent,
    partition <> blockStart
    -> In pdparent (getPartitions multiplexer s)
    -> In partition (getChildren pdparent s) -> pdentryParent partition pdparent s)
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> (* PDTIfPDFlag s *)
    (forall idPDchild sh1entryaddr part, idPDchild <> exceptionBlock
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupMappedPaddrList s
-> wellFormedBlock s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> noChildImpliesAddressesNotShared s
-> partitionsIsolation s
-> bentryStartAddr exceptionBlock blockStart s
-> ~In blockStart (getPartitions multiplexer s)
-> lookup blockStart (memory s) beqAddr = None
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In addr (getAllPaddrAux [block] s)
-> In block (getMappedBlocks part1 s)
-> sh1entryPDchild (CPaddr (block + sh1offset)) nullAddr s
-> In addr (getMappedPaddr part2 s)
-> In part2 (part1::(filterOptionPaddr (completeParentsList part1 s))).
Proof.
intros HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HnoDupBlocks
  HnoDupPaddr HwellFormed HisChild HblockEquivParent HnoChild HPI HstartExcept HstartNotPart HlookupStart Hpart1IsPart
  Hpart2IsPart HaddrInBlock HblockMapped1 HPDchild HaddrMapped2.
assert(Hres: In part1 (filterOptionPaddr (completeParentsList part2 s))
              \/ part1 = part2
              \/ In part2 (filterOptionPaddr (completeParentsList part1 s))).
{
  apply addressesBloodlinePartial with addr exceptionBlock blockStart; trivial.
  apply addrInBlockIsMapped with block; assumption.
}
simpl. destruct Hres as [Hcontra | Hres]; try(assumption). exfalso.
assert(Hpart1IsPDT: isPDT part1 s).
{ apply partitionsArePDTPartial with exceptionBlock blockStart; assumption. }
unfold isPDT in *. destruct (lookup part1 (memory s) beqAddr) eqn:HlookupPart1; try(congruence).
destruct v; try(congruence).
assert(HeqTriv: CPaddr (block + sh1offset) = CPaddr (block + sh1offset)) by reflexivity.
specialize(HnoChild part1 p block (CPaddr (block + sh1offset)) Hpart1IsPart HlookupPart1 HblockMapped1 HeqTriv
  HPDchild). clear Hpart1IsPDT. clear HeqTriv.
pose proof (completeParentsListChildPartial part1 part2 s exceptionBlock blockStart HPDTIfPDFlag HmultIsPDT
  HparentOfPart HnoDupTree HstartExcept HstartNotPart Hpart2IsPart Hcontra) as HcontraChild.
destruct HcontraChild as [child (Hparent & HchildIsPart & HchildIsAnc)].
assert(HbeqChildRoot: child <> constantRootPartM).
{
  unfold pdentryParent in *. intro HbeqChildRoot.
  destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(congruence). destruct v; try(congruence).
  specialize(HparentOfPart child p0 HlookupChild). destruct HparentOfPart as (_ & HparentOfRoot & _).
  specialize(HparentOfRoot HbeqChildRoot). rewrite <-Hparent in *. rewrite HparentOfRoot in *.
  unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupPart1 in *. congruence.
}
assert(HchildIsChild: In child (getChildren part1 s)).
{
  specialize(HisChild child part1 HchildIsPart Hparent HbeqChildRoot). assumption.
}
specialize(HnoChild child addr HchildIsChild HaddrInBlock). simpl in HchildIsAnc.
destruct HchildIsAnc as [HbeqPart2Child | HchildIsAncRec]; try(congruence). contradict HnoChild.
apply addrBelongToAncestorsPartial with part2 exceptionBlock blockStart; trivial.
apply blockInclImpliesAddrIncl; assumption.
Qed.
