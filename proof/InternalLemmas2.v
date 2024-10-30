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
Require Import Model.ADT Model.Monad Model.MAL Model.Lib Core.Internal.

Require Import DependentTypeLemmas.
Require Import Proof.Isolation Proof.Consistency Proof.StateLib Proof.InternalLemmas.

Require Import List Coq.Logic.ProofIrrelevance Lia Classical_Prop Compare_dec EqNat Arith.
Require Import Coq.Program.Equality FunctionalExtensionality.

Module DTL := DependentTypeLemmas.

Import List.ListNotations.

Lemma isParentsListEqPDTExternalPart partition newPart newPDEntry parentsList s0 s1:
~ In newPart parentsList
-> beqAddr newPart partition = false
-> s1 = {|
       currentPartition := currentPartition s0;
       memory := add newPart (PDT newPDEntry) (memory s0) beqAddr
     |}
-> isParentsList s1 parentsList partition
-> isParentsList s0 parentsList partition.
Proof.
intros HnewIsExtern HbeqNewPart Hs1. revert partition HbeqNewPart. induction parentsList.
- (* parentsList = [] *)
  simpl. intros. trivial.
- (* parentsList = a::l *)
  simpl. intros partition HbeqNewPart HparentsLists1. rewrite Hs1 in HparentsLists1. simpl in *.
  apply not_or_and in HnewIsExtern. destruct HnewIsExtern as (HbeqANew & HnewIsExternRec).
  specialize(IHparentsList HnewIsExternRec). rewrite beqAddrFalse in HbeqANew. rewrite beqAddrSym in HbeqANew.
  rewrite HbeqANew in HparentsLists1. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in HparentsLists1; try(apply not_eq_sym; assumption).
  destruct (lookup a (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
  destruct HparentsLists1 as [HpartNotRoot ((pdentry0 & (HpdentryEq & Ha)) & HparentsLists1)].
  rewrite beqAddrFalse in HbeqNewPart. rewrite HbeqNewPart in HpdentryEq. rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in HpdentryEq; try(apply not_eq_sym; assumption). split. assumption. split.
  + exists pdentry0. split; assumption.
  + rewrite <-Hs1 in HparentsLists1. apply IHparentsList; try(assumption). rewrite <-beqAddrFalse. assumption.
Qed.

Lemma isListOfKernelsEqPDTNewEmptyPart partition newPart newPDEntry kernList s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> structure newPDEntry = nullAddr
-> isListOfKernels kernList partition {|
                                        currentPartition := currentPartition s0;
                                        memory := add newPart (PDT newPDEntry)
                                                    (memory s0) beqAddr
                                      |}
-> isListOfKernels kernList partition s0.
Proof.
intros HlookupAddr HstructureEq HisKernLists. destruct kernList.
- intuition.
- simpl in *. destruct HisKernLists as [newPdentry HisKernLists].
  destruct (beqAddr newPart partition) eqn:HbeqNewPart.
  {
    destruct HisKernLists as (Hlookups & Hcontra & HisKernLists). injection Hlookups as HpdentriesEq.
    subst newPdentry. congruence.
  }
  exists newPdentry. rewrite <-beqAddrFalse in HbeqNewPart.
  rewrite removeDupIdentity in HisKernLists; try(apply not_eq_sym; assumption). split. intuition. split.
  intuition. split. intuition. apply isListOfKernelsAuxEqPDT with newPart newPDEntry; intuition.
Qed.

Lemma filterPresentEqPDTNotBE addr' newEntry s0 blocklist:
~ isBE addr' s0 ->
filterPresent blocklist {|
						currentPartition := currentPartition s0;
						memory := add addr' (PDT newEntry)
            (memory s0) beqAddr |} =
filterPresent blocklist s0.
Proof.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
intros HaddrNotBEs0.
induction blocklist.
- intuition.
- simpl.
	destruct (beqAddr addr' a) eqn:Hf; rewrite IHblocklist.
	-- rewrite <- DTL.beqAddrTrue in Hf.
     subst a.
     unfold isBE in *.
     destruct (lookup addr' (memory s0) beqAddr) eqn:Hff ; try(reflexivity).
     destruct v ; try(reflexivity). contradict HaddrNotBEs0. trivial.
	-- rewrite <- beqAddrFalse in *.
     repeat rewrite removeDupIdentity ; intuition.
Qed.

Lemma getMappedBlocksEqPDTNewEmptyPart partition newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> structure newPDEntry = nullAddr
-> StructurePointerIsKS s0
-> getMappedBlocks partition {|
						               currentPartition := currentPartition s0;
						               memory := add newPart (PDT newPDEntry)
                           (memory s0) beqAddr |}
    = getMappedBlocks partition s0.
Proof.
set (s':= {|
            currentPartition := currentPartition s0;
            memory := _ |}). intros HlookupNews0 HbeqStructNull HstructIsKS. unfold getMappedBlocks.
assert(HgetKSEq: getKSEntries partition s' = getKSEntries partition s0).
{
  apply getKSEntriesEqPDTNewEmptyPart; assumption.
}
rewrite HgetKSEq. apply filterPresentEqPDTNotBE. unfold isBE.
destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & HbeqAncStructNull)]]; rewrite HlookupNews0;
  intro; congruence.
Qed.

Lemma childFilterEqPDTNewEmptyPart newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> childFilter {|
	               currentPartition := currentPartition s0;
	               memory := add newPart (PDT newPDEntry)
                 (memory s0) beqAddr |}
    = childFilter s0.
Proof.
set (s':= {|
            currentPartition := currentPartition s0;
            memory := _ |}). intro HlookupNews0. unfold childFilter. extensionality block.
simpl. destruct (beqAddr newPart block) eqn:HbeqNewBlock.
- rewrite <-DTL.beqAddrTrue in HbeqNewBlock. subst block.
  destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & HbeqAncStructNull)]]; rewrite HlookupNews0;
    reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  destruct (lookup block (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
  destruct (Paddr.addPaddrIdx block sh1offset); try(reflexivity).
  destruct (beqAddr newPart p) eqn:HbeqNewP.
  + rewrite <-DTL.beqAddrTrue in HbeqNewP. subst p.
    destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & HbeqAncStructNull)]]; rewrite HlookupNews0;
    reflexivity.
  + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
Qed.

Lemma getPDsPaddrEqPDTNewEmptyPart list newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> getPDsPaddr list {|
	                    currentPartition := currentPartition s0;
	                    memory := add newPart (PDT newPDEntry)
                      (memory s0) beqAddr |}
    = getPDsPaddr list s0.
Proof.
set (s':= {|
            currentPartition := currentPartition s0;
            memory := _ |}). intro HlookupNews0. unfold getPDsPaddr. f_equal. extensionality block.
simpl. destruct (beqAddr newPart block) eqn:HbeqNewBlock.
- rewrite <-DTL.beqAddrTrue in HbeqNewBlock. subst block.
  destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & HbeqAncStructNull)]]; rewrite HlookupNews0;
    reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
Qed.

Lemma getPDsEqPDTNewEmptyPart partition newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> getPDs partition {|
						               currentPartition := currentPartition s0;
						               memory := add newPart (PDT newPDEntry)
                           (memory s0) beqAddr |}
    = getPDs partition s0.
Proof.
set (s':= {|
            currentPartition := currentPartition s0;
            memory := _ |}). intro HlookupNews0. unfold getPDs.
assert(HgetChildFilterEq: childFilter s' = childFilter s0).
{
  apply childFilterEqPDTNewEmptyPart; assumption.
}
rewrite HgetChildFilterEq. apply getPDsPaddrEqPDTNewEmptyPart. assumption.
Qed.

Lemma getChildrenEqPDTNewEmptyPart partition newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> structure newPDEntry = nullAddr
-> StructurePointerIsKS s0
-> getChildren partition {|
						               currentPartition := currentPartition s0;
						               memory := add newPart (PDT newPDEntry)
                           (memory s0) beqAddr |}
    = getChildren partition s0.
Proof.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
intros HlookupNews0 HbeqStructNull HstructIsKS.
unfold getChildren.
unfold s'. simpl.

destruct (beqAddr newPart partition) eqn:HbeqNewPart.
- (* newPart = partition *)
  rewrite <-DTL.beqAddrTrue in HbeqNewPart. subst newPart. unfold getMappedBlocks. unfold getKSEntries. simpl.
  rewrite beqAddrTrue. rewrite DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. simpl.
  unfold getPDs at 1. simpl.
  destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & HbeqAncStructNull)]]; rewrite HlookupNews0.
  + reflexivity.
  + rewrite DTL.beqAddrTrue in HbeqAncStructNull. rewrite HbeqAncStructNull. simpl. unfold getPDs. simpl.
    reflexivity.

- (* newPart <> partition *)
  rewrite <- beqAddrFalse in *.
  repeat rewrite removeDupIdentity ; try(apply not_eq_sym; assumption).
  destruct (lookup partition (memory s0) beqAddr) ; try(reflexivity).
  destruct v ; try(reflexivity). fold s'.
  assert(HEq :  getMappedBlocks partition s' = getMappedBlocks partition s0).
  { eapply getMappedBlocksEqPDTNewEmptyPart; assumption. }
  rewrite HEq.
  apply getPDsEqPDTNewEmptyPart. assumption.
Qed.

Lemma getPartitionsAuxEqPDTNewEmptyPart partition newPart newPDEntry s0 n:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> structure newPDEntry = nullAddr
-> StructurePointerIsKS s0
-> PDTIfPDFlag s0
-> getPartitionsAux n partition {|
                                  currentPartition := currentPartition s0;
                                  memory := add newPart (PDT newPDEntry)
                                              (memory s0) beqAddr |}
    = getPartitionsAux n partition s0.
Proof.
revert n partition.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
induction n.
- intros.
	unfold getPartitionsAux in *.
	intuition.
- intros partition Hlookupds0 HbeqStructNull HstructIsKSs0 HPDTIfPDflags0.
	unfold getPartitionsAux.
	fold getPartitionsAux.
	f_equal.
	assert(HChildrenEq: (getChildren partition s') = (getChildren partition s0)).
	{
		apply getChildrenEqPDTNewEmptyPart; assumption.
	}
	rewrite HChildrenEq.
	rewrite flat_map_concat_map. rewrite flat_map_concat_map.
	f_equal.
	clear HChildrenEq.
	assert(HchildrenArePDT : forall child, In child (getChildren partition s0) ->
					isPDT child s0).
	{ intros.
		apply childrenArePDT with partition ; intuition.
	}
	induction (getChildren partition s0).
	-- intuition.
	-- simpl in *. f_equal.
			--- apply IHn ; intuition.
			--- intuition.
Qed.

Lemma getPartitionsEqPDTNewEmptyPart partition newPart newPDEntry s0 :
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> structure newPDEntry = nullAddr
-> StructurePointerIsKS s0
-> PDTIfPDFlag s0
-> getPartitions partition {|
						currentPartition := currentPartition s0;
						memory := add newPart (PDT newPDEntry)
            (memory s0) beqAddr |} =
getPartitions partition s0.
Proof.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
intros HlookupNews0 HbeqStructNull HstructKSs0 HPDTIfPDflags0.
unfold getPartitions.
assert(HPartitionsEq : (getPartitionsAux (maxAddr + 2) partition s') =
													(getPartitionsAux (maxAddr + 2) partition s0)).
{
	apply getPartitionsAuxEqPDTNewEmptyPart; assumption.
}
rewrite HPartitionsEq.
trivial.

Qed.

Fixpoint completeParentsListRec timeout partition s :=
match timeout with
| S timeout1 =>
    match lookup partition (memory s) beqAddr with
    | Some (PDT pdentry) =>
        match beqAddr partition constantRootPartM with
        | true => []
        | false => SomePaddr(parent pdentry)::(completeParentsListRec timeout1 (parent pdentry) s)
        end
    | _ => [NonePaddr]
    end
| _ => [NonePaddr]
end.

Definition completeParentsList partition s := completeParentsListRec (S (S maxAddr)) partition s.

Lemma completeParentsListIsParentsListAux n basePart s:
parentOfPartitionIsPartition s
-> isPDT basePart s
-> isParentsList s (filterOptionPaddr (completeParentsListRec n basePart s)) basePart.
Proof.
intros HparentOfPart. revert basePart.
induction n; simpl; trivial; intros basePart HbaseIsPDT. unfold isPDT in HbaseIsPDT.
destruct (lookup basePart (memory s) beqAddr) eqn: HlookupBase; simpl; trivial. destruct v; simpl; trivial.
destruct (beqAddr basePart constantRootPartM) eqn:HbeqBaseRoot; simpl; trivial.
rewrite <-beqAddrFalse in *. specialize(HparentOfPart basePart p HlookupBase).
destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqBaseRoot).
destruct HparentIsPart as ([parentEntry HlookupParent] & _). rewrite HlookupParent. split. assumption. split.
- exists p. split. assumption. reflexivity.
- apply IHn. unfold isPDT. rewrite HlookupParent. trivial.
Qed.

Lemma completeParentsListIsParentsList basePart s:
parentOfPartitionIsPartition s
-> isPDT basePart s
-> isParentsList s (filterOptionPaddr (completeParentsList basePart s)) basePart.
Proof.
unfold completeParentsList. apply completeParentsListIsParentsListAux.
Qed.

Lemma parentIsInParentListAux n child pdparent basePart s:
parentOfPartitionIsPartition s
-> nullAddrExists s
-> pdentryParent child pdparent s
-> isPDT pdparent s
-> n > length (filterOptionPaddr (completeParentsListRec n basePart s))
-> In child (filterOptionPaddr (completeParentsListRec n basePart s))
-> In pdparent (filterOptionPaddr (completeParentsListRec n basePart s)).
Proof.
intros HparentOfPart HnullExists Hparent HparentIsPDT. revert basePart.
induction n; simpl in *; intros basePart Hn HchildInList; try(exfalso; congruence).
destruct (lookup basePart (memory s) beqAddr) eqn:HlookupBase; try(simpl in *; congruence).
destruct v; try(simpl in *; congruence).
destruct (beqAddr basePart constantRootPartM) eqn:HbeqBaseRoot; simpl in *; try(congruence). right.
assert(HnRec: n > length (filterOptionPaddr (completeParentsListRec n (parent p) s))) by lia.
destruct HchildInList as [HchildIsParentBase | HchildInListRec].
- rewrite HchildIsParentBase. destruct n; try(lia). simpl. unfold pdentryParent in Hparent.
  destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(simpl; congruence).
  destruct v; try(simpl; congruence).
  destruct (beqAddr child constantRootPartM) eqn:HbeqChildRoot.
  {
    simpl. rewrite <-DTL.beqAddrTrue in HbeqChildRoot. specialize(HparentOfPart child p0 HlookupChild).
    destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot HbeqChildRoot).
    rewrite <-Hparent in *. subst pdparent. unfold isPDT in *. unfold nullAddrExists in *. unfold isPADDR in *.
    destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  simpl. rewrite <-Hparent. left. reflexivity.
- apply IHn; assumption.
Qed.

Lemma parentIsInParentList child pdparent basePart s:
partitionTreeIsTree s
-> parentOfPartitionIsPartition s
-> nullAddrExists s
-> pdentryParent child pdparent s
-> isPDT pdparent s
-> isPDT basePart s
-> In child (filterOptionPaddr (completeParentsList basePart s))
-> In pdparent (filterOptionPaddr (completeParentsList basePart s)).
Proof.
intros. unfold completeParentsList. apply parentIsInParentListAux with child; try(assumption).
assert(HnoDupList: NoDup (filterOptionPaddr (completeParentsList basePart s))).
{
  apply parentOfPartNotInParentsListsTail with basePart s; try(assumption).
  apply completeParentsListIsParentsList; assumption.
}
pose proof (lengthNoDupPartitions (filterOptionPaddr (completeParentsList basePart s)) HnoDupList).
unfold completeParentsList in *. lia.
Qed.

Lemma getPartitionsGivesAncestor n partition newRoot s:
isParent s
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> isPDT partition s
-> In newRoot (getPartitions multiplexer s)
-> In partition (getPartitionsAux n newRoot s)
-> newRoot <> partition
-> In newRoot (filterOptionPaddr (completeParentsList partition s)).
Proof.
intros HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HpartIsPDT.
revert newRoot. induction n; simpl; try(intros; exfalso; congruence).
intros newRoot HnewRootIsPart HpartIsPart HbeqPartNewRoot.
destruct HpartIsPart as [HbeqRootPart | HpartIsPartRec]; try(exfalso; congruence).
assert(Hchildren: forall child, In child (getChildren newRoot s)
          -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
{
  intros child HchildIsChild. specialize(HisParent child newRoot HnewRootIsPart HchildIsChild). split. assumption.
  apply childrenPartitionInPartitionList with newRoot; assumption.
}
induction (getChildren newRoot s); simpl in *; try(exfalso; congruence). apply in_app_or in HpartIsPartRec.
assert(HchildrenRec: forall child, In child l
        -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
{
  intros child HchildIsChild. apply Hchildren. right. assumption.
}
destruct HpartIsPartRec as [HpartInPartsA | HpartIsPartRecRec]; try(apply IHl; assumption).
assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). specialize(Hchildren a HeqTriv).
destruct Hchildren as (HparentA & HaIsPart).
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
    { apply partitionsArePDT; assumption. }
    unfold isPDT in *. unfold nullAddrExists in *. unfold isPADDR in *.
    destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-HparentA. simpl. left. reflexivity.
- rewrite <-beqAddrFalse in HbeqAPart. specialize(IHn a HaIsPart HpartInPartsA HbeqAPart).
  revert IHn. apply parentIsInParentList; try(assumption). apply partitionsArePDT; assumption.
Qed.

(*Lemma NoDupListNoDupGetPDs l s:
NoDup l -> NoDup (getPDs l s).
Proof.
intro HnoDup. unfold getPDs.
assert(HnoDupFilter: NoDup (filter (childFilter s) l)).
{ apply NoDup_filter. assumption. }
induction (filter (childFilter s) l); simpl; try(apply NoDup_nil). apply NoDup_cons_iff in HnoDupFilter.
apply NoDup_cons_iff. destruct HnoDupFilter as (HaNotInList & HnoDupFilterRec).
split; try(apply IHl0; assumption).
Qed.*)

Lemma NotInPaddrListNotInGetPDsPaddr addr l s:
(forall block, In block l -> exists bentry, lookup block (memory s) beqAddr = Some(BE bentry)
    /\ startAddr (blockrange bentry) < endAddr (blockrange bentry))
-> ~ In addr (getAllPaddrAux l s)
-> ~ In addr (getPDsPaddr l s).
Proof.
intros Hblocks HaddrIn. contradict HaddrIn. induction l; simpl in *; try(congruence).
assert(HblocksRec: forall block, In block l -> exists bentry, lookup block (memory s) beqAddr = Some(BE bentry)
    /\ startAddr (blockrange bentry) < endAddr (blockrange bentry)).
{
  intros block HblockIn. apply Hblocks. right. assumption.
}
assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). specialize(Hblocks a HeqTriv).
destruct Hblocks as [bentry (HlookupA & HwellFormed)]. rewrite HlookupA. apply in_or_app.
destruct HaddrIn as [Hleft | Hright]; try(right; apply IHl; assumption). left. subst addr. rewrite HlookupA.
apply getAllPaddrBlockIncl; lia.
Qed.

Lemma noDupGetChildren partition s:
noDupMappedBlocksList s
-> noDupUsedPaddrList s
-> wellFormedBlock s
-> isPDT partition s
-> NoDup (getChildren partition s).
Proof.
intros HnoDupBlocks HnoDupPaddr HwellFormedBlock HpartIsPDT. specialize(HnoDupBlocks partition HpartIsPDT).
unfold getChildren.
destruct (lookup partition (memory s) beqAddr); try(apply NoDup_nil). destruct v; try(apply NoDup_nil).
assert(HblocksAreBE: forall block, In block (getMappedBlocks partition s) -> isBE block s).
{
  intros block HblockMapped. apply mappedBlockIsBE in HblockMapped. unfold isBE.
  destruct HblockMapped as [bentry (HlookupBlock & _)]. rewrite HlookupBlock. trivial.
}
assert(HwellFormed: forall block bentry, In block (getMappedBlocks partition s)
          -> lookup block (memory s) beqAddr = Some(BE bentry)
          -> startAddr (blockrange bentry) < endAddr (blockrange bentry)).
{
  intros block bentry HblockMapped HlookupBlock. apply mappedBlockIsBE in HblockMapped.
  destruct HblockMapped as [bentryBis (HlookupBlockBis & Hpresent)]. rewrite HlookupBlock in HlookupBlockBis.
  injection HlookupBlockBis as HlookupBlockBis. subst bentryBis.
  assert(HPFlag: bentryPFlag block true s) by (unfold bentryPFlag; rewrite HlookupBlock; intuition).
  assert(Hstart: bentryStartAddr block (startAddr (blockrange bentry)) s).
  { unfold bentryStartAddr; rewrite HlookupBlock; reflexivity. }
  assert(Hend: bentryEndAddr block (endAddr (blockrange bentry)) s).
  { unfold bentryEndAddr; rewrite HlookupBlock; reflexivity. }
  specialize(HwellFormedBlock block (startAddr (blockrange bentry)) (endAddr (blockrange bentry)) HPFlag Hstart
    Hend). apply HwellFormedBlock.
}
specialize(HnoDupPaddr partition HpartIsPDT). unfold getUsedPaddr in *. apply NoDup_app_remove_l in HnoDupPaddr.
unfold getMappedPaddr in HnoDupPaddr. unfold getPDs. set(l := getMappedBlocks partition s). fold l in HnoDupPaddr.
fold l in HnoDupBlocks.
assert(HnoDupFilter: NoDup (filter (childFilter s) l)).
{ apply NoDup_filter. assumption. }
assert(Hincl: incl (filter (childFilter s) l) l).
{ apply incl_filter. }
assert(HnoDupPaddrF: NoDup (getAllPaddrAux (filter (childFilter s) l) s)).
{
  apply NoDupPaddrListNoDupPaddrFilterChild; assumption.
}
induction (filter (childFilter s) l); simpl; try(apply NoDup_nil). apply NoDup_cons_iff in HnoDupFilter.
apply NoDup_cons_iff. destruct HnoDupFilter as (HaNotInList & HnoDupFilterRec). apply incl_cons_inv in Hincl.
destruct Hincl as (HaInList & HinclRec). simpl in HnoDupPaddrF.
assert(Hprop: forall block, In block l0
        -> exists bentry, lookup block (memory s) beqAddr = Some (BE bentry)
            /\ startAddr (blockrange bentry) < endAddr (blockrange bentry)).
{
  intros block HblockIn. specialize(HinclRec block HblockIn). specialize(HblocksAreBE block HinclRec).
  unfold isBE in *. destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. split. reflexivity.
  specialize(HwellFormed block b HinclRec HlookupBlock). assumption.
}
specialize(HblocksAreBE a HaInList). unfold isBE in *.
destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(exfalso; congruence).
destruct v; try(exfalso; congruence). apply Lib.NoDupSplitInclIff in HnoDupPaddrF.
destruct HnoDupPaddrF as ((HnoDupBlock & HnoDupPaddrFRec) & Hdisjoint). split; try(apply IHl0; assumption).
assert(HstartInBlock: In (startAddr (blockrange b))
                          (getAllPaddrBlock (startAddr (blockrange b)) (endAddr (blockrange b)))).
{
  specialize(HwellFormed a b HaInList HlookupA). apply getAllPaddrBlockIncl; lia.
}
specialize(Hdisjoint (startAddr (blockrange b)) HstartInBlock). revert Hdisjoint.
apply NotInPaddrListNotInGetPDsPaddr. assumption.
Qed.

Lemma addrBelongToAncestors desc partition addr s:
isChild s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> parentOfPartitionIsPartition s
-> childPaddrIsIntoParent s
-> In desc (getPartitions multiplexer s)
-> In partition (getPartitions multiplexer s)
-> In partition (filterOptionPaddr (completeParentsList desc s))
-> In addr (getMappedPaddr desc s)
-> In addr (getMappedPaddr partition s).
Proof.
intros HisChild HPDTIfPDFlag HmultIsPDT HparentOfPart HchildInclParent HdescIsPart HpartIsPart HdescIsDesc
  HaddrMappedDesc.
revert desc HaddrMappedDesc HdescIsPart HdescIsDesc.
unfold completeParentsList in *. induction (S (S maxAddr)); intros; simpl in *; try(exfalso; congruence).
assert(HdescIsPDT: isPDT desc s).
{ apply partitionsArePDT; assumption. }
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

Lemma addrCannotBeInSeparateBloodlines n addr part part1 part2 newRoot l s:
partitionsIsolation s
-> isChild s
-> isParent s
-> parentOfPartitionIsPartition s
-> noDupPartitionTree s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> wellFormedBlock s
-> In addr (getMappedPaddr part1 s)
-> In addr (getMappedPaddr part2 s)
-> In part1 (getPartitionsAux n part s)
-> In part2 (flat_map (fun p : paddr => getPartitionsAux n p s) l)
-> (forall child, In child l -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)
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
  HblockEquivParent HwellFormed HaddrMapped1 HaddrMapped2 Hpart1IsPart Hpart2IsPart HlistElAreChildren
  HpartNotInList Hparent HpartIsPart HnewRootIsPart Hpart1IsPartM Hpart2IsPartM HbeqPartRoot.
induction l; simpl in *; try(congruence). apply in_app_or in Hpart2IsPart.
assert(HlistElAreChildrenRec: forall child,
        In child l -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)
          /\ child <> constantRootPartM).
{ intros child HchildIn. apply HlistElAreChildren. right. assumption. }
apply not_or_and in HpartNotInList. destruct HpartNotInList as (HbeqAPart & HpartNotInListRec).
destruct Hpart2IsPart as [Hpart2IsPart | Hpart2IsPartRec]; try(apply IHl; assumption).
assert(HeqTriv: a = a \/ In a l) by (left; reflexivity).
specialize(HlistElAreChildren a HeqTriv). destruct HlistElAreChildren as (HaIsChild & HaIsPart & HbeqARoot).
assert(Hchild1: In a (getChildren newRoot s)).
{
  specialize(HisChild a newRoot HaIsPart HaIsChild HbeqARoot). assumption.
}
assert(Hchild2: In part (getChildren newRoot s)).
{
  specialize(HisChild part newRoot HpartIsPart Hparent HbeqPartRoot). assumption.
}
specialize(HPI newRoot a part HnewRootIsPart Hchild1 Hchild2 HbeqAPart).
assert(Hpart1IsPDT: isPDT part1 s).
{ apply partitionsArePDT; assumption. }
assert(Hpart2IsPDT: isPDT part2 s).
{ apply partitionsArePDT; assumption. }
pose proof (getPartitionsGivesAncestor n part1 part s HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT
  HnullExists Htree Hpart1IsPDT HpartIsPart Hpart1IsPart) as Hancestor1.
pose proof (getPartitionsGivesAncestor n part2 a s HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT
  HnullExists Htree Hpart2IsPDT HaIsPart Hpart2IsPart) as Hancestor2.
assert(HaddrMappedA: In addr (getUsedPaddr a s)).
{
  unfold getUsedPaddr. apply in_or_app. right. destruct (beqAddr a part2) eqn:HbeqAPart2.
  - rewrite <-DTL.beqAddrTrue in HbeqAPart2. subst a. assumption.
  - rewrite <-beqAddrFalse in HbeqAPart2. specialize(Hancestor2 HbeqAPart2).
    apply addrBelongToAncestors with part2; try(assumption). apply blockInclImpliesAddrIncl; assumption.
}
assert(HaddrMappedPart: In addr (getUsedPaddr part s)).
{
  unfold getUsedPaddr. apply in_or_app. right. destruct (beqAddr part part1) eqn:HbeqPartPart1.
  - rewrite <-DTL.beqAddrTrue in HbeqPartPart1. subst part. assumption.
  - rewrite <-beqAddrFalse in HbeqPartPart1. specialize(Hancestor1 HbeqPartPart1).
    apply addrBelongToAncestors with part1; try(assumption). apply blockInclImpliesAddrIncl; assumption.
}
specialize(HPI addr HaddrMappedA). congruence.
Qed.

Lemma addressesBloodlineAux part1 part2 newRoot addr n s:
isParent s
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupUsedPaddrList s
-> wellFormedBlock s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> partitionsIsolation s
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
  HnoDupPaddr HwellFormed HisChild HblockEquivParent HPI Hpart1IsPDT Hpart2IsPDT Hpart1IsPartM Hpart2IsPartM
  HaddrMapped1 HaddrMapped2.
revert newRoot. induction n.
{ simpl in *. intros. exfalso. congruence. }
intros newRoot HnewRootIsPart Hpart1IsPart Hpart2IsPart.
assert(Hchildren: forall child, In child (getChildren newRoot s)
          -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
{
  intros child HchildIsChild. specialize(HisParent child newRoot HnewRootIsPart HchildIsChild). split.
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
            -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
    {
      intros child HchildInList. apply Hchildren. right. assumption.
    }
    destruct Hpart2IsPartRec as [Hpart2IsPartA | Hpart2IsPartRecRec]; try(apply IHl; assumption).
    assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). specialize(Hchildren a HeqTriv).
    destruct Hchildren as (HparentA & HAIsPart).
    destruct (beqAddr a part2) eqn:HbeqAPart2.
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
      pose proof (getPartitionsGivesAncestor n part2 a s HisParent HnoDupTree HparentOfPart HPDTIfPDFlag
        HmultIsPDT HnullExists HpartTreeIsTree Hpart2IsPDT HAIsPart Hpart2IsPartA HbeqAPart2) as Hres.
      apply parentIsInParentList with a; assumption.
- rewrite <-beqAddrFalse in HbeqNewRootPart1.
  destruct Hpart1IsPart as [Hcontra | Hpart1IsPartRec]; try(exfalso; congruence).
  destruct (beqAddr newRoot part2) eqn:HbeqNewRootPart2.
  + rewrite <-DTL.beqAddrTrue in HbeqNewRootPart2. subst part2. clear Hpart2IsPart. right. right.
    induction (getChildren newRoot s); simpl in *; try(exfalso; congruence).
    apply in_app_or in Hpart1IsPartRec.
    assert(HchildrenRec: forall child, In child l
            -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
    {
      intros child HchildInList. apply Hchildren. right. assumption.
    }
    destruct Hpart1IsPartRec as [Hpart1IsPartA | Hpart1IsPartRecRec]; try(apply IHl; assumption).
    assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). specialize(Hchildren a HeqTriv).
    destruct Hchildren as (HparentA & HAIsPart).
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
      pose proof (getPartitionsGivesAncestor n part1 a s HisParent HnoDupTree HparentOfPart HPDTIfPDFlag
          HmultIsPDT HnullExists HpartTreeIsTree Hpart1IsPDT HAIsPart Hpart1IsPartA HbeqAPart1) as Hres.
      apply parentIsInParentList with a; assumption.
  + rewrite <-beqAddrFalse in HbeqNewRootPart2.
    destruct Hpart2IsPart as [Hcontra | Hpart2IsPartRec]; try(exfalso; congruence).
    assert(HnoDupChildren: NoDup (getChildren newRoot s)).
    { apply noDupGetChildren; try(assumption). apply partitionsArePDT; assumption. }
    induction (getChildren newRoot s); simpl in *; try(exfalso; congruence). apply in_app_or in Hpart1IsPartRec.
    apply in_app_or in Hpart2IsPartRec. apply NoDup_cons_iff in HnoDupChildren.
    destruct HnoDupChildren as (HaNotInList & HnoDupChildrenRec).
    assert(HchildrenRec: forall child, In child l
            -> pdentryParent child newRoot s /\ In child (getPartitions multiplexer s)).
    {
      intros child HchildInList. apply Hchildren. right. assumption.
    }
    assert(HeqTriv: a = a \/ In a l) by (left; reflexivity). specialize(Hchildren a HeqTriv). clear HeqTriv.
    destruct Hchildren as (HparentA & HaIsPart).
    assert(HbeqARoot: a <> constantRootPartM).
    {
      unfold pdentryParent in *. intro Hcontra.
      destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(congruence). destruct v; try(congruence).
      specialize(HparentOfPart a p HlookupA). destruct HparentOfPart as (_ & HparentOfRoot & _).
      specialize(HparentOfRoot Hcontra). rewrite <-HparentA in *. rewrite HparentOfRoot in *.
      assert(HnullIsPDT: isPDT nullAddr s).
      { apply partitionsArePDT; assumption. }
      unfold isPDT in *. unfold nullAddrExists in *. unfold isPADDR in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    assert(forall child, In child l ->
              pdentryParent child newRoot s /\
              In child (getPartitions multiplexer s) /\ child <> constantRootPartM).
    {
      intros child HchildIn. specialize(HchildrenRec child HchildIn).
      destruct HchildrenRec as (Hparent & HchildIsPart). split. assumption. split. assumption.
      unfold pdentryParent in *. intro Hcontra.
      destruct (lookup child (memory s) beqAddr) eqn:HlookupChild; try(congruence). destruct v; try(congruence).
      specialize(HparentOfPart child p HlookupChild). destruct HparentOfPart as (_ & HparentOfRoot & _).
      specialize(HparentOfRoot Hcontra). rewrite <-Hparent in *. rewrite HparentOfRoot in *.
      assert(HnullIsPDT: isPDT nullAddr s).
      { apply partitionsArePDT; assumption. }
      unfold isPDT in *. unfold nullAddrExists in *. unfold isPADDR in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    destruct Hpart1IsPartRec as [Hpart1IsPartA | Hpart1IsPartRecRec].
    * destruct Hpart2IsPartRec as [Hpart2IsPartA | Hpart2IsPartRecRec]; try(apply IHn with a; assumption).
      exfalso. apply addrCannotBeInSeparateBloodlines with n addr a part1 part2 newRoot l s; assumption.
    * destruct Hpart2IsPartRec as [Hpart2IsPartA | Hpart2IsPartRecRec]; try(apply IHl; assumption).
      exfalso. apply addrCannotBeInSeparateBloodlines with n addr a part2 part1 newRoot l s; assumption.
Qed.

Lemma addressesBloodline addr part1 part2 s:
isParent s
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupUsedPaddrList s
-> wellFormedBlock s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> partitionsIsolation s
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In addr (getMappedPaddr part1 s)
-> In addr (getMappedPaddr part2 s)
-> In part1 (filterOptionPaddr (completeParentsList part2 s))
    \/ part1 = part2
    \/ In part2 (filterOptionPaddr (completeParentsList part1 s)).
Proof.
intros HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HnoDupBlocks
  HnoDupPaddr HwellFormed HisChild HblockEquivParent HPI Hpart1IsPart Hpart2IsPart HaddrMapped1 HaddrMapped2.
apply addressesBloodlineAux with multiplexer addr (maxAddr + 2); try(assumption).
- apply partitionsArePDT; assumption.
- apply partitionsArePDT; assumption.
- unfold getPartitions. replace (maxAddr + 2) with (S(maxAddr + 1)); try(lia). simpl. left. reflexivity.
Qed.

Lemma completeParentsListChild part1 part2 s:
PDTIfPDFlag s
-> multiplexerIsPDT s
-> parentOfPartitionIsPartition s
-> In part2 (getPartitions multiplexer s)
-> In part1 (filterOptionPaddr (completeParentsList part2 s))
-> exists child, pdentryParent child part1 s
                /\ In child (getPartitions multiplexer s)
                /\ In child (part2::(filterOptionPaddr (completeParentsList part2 s))).
Proof.
intros HPDTIfPDFlag HmultIsPDT HparentOfPart. unfold completeParentsList. revert part2.
induction (S (S maxAddr)); intros part2 Hpart2IsPart Hpart1IsAnc; simpl in *; try(exfalso; congruence).
assert(Hpart2IsPDT: isPDT part2 s).
{ apply partitionsArePDT; assumption. }
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

Lemma addressesBloodlineIfNotShared s part1 part2 addr block:
isParent s
-> noDupPartitionTree s
-> parentOfPartitionIsPartition s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> nullAddrExists s
-> partitionTreeIsTree s
-> noDupMappedBlocksList s
-> noDupUsedPaddrList s
-> wellFormedBlock s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> noChildImpliesAddressesNotShared s
-> partitionsIsolation s
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In addr (getAllPaddrAux [block] s)
-> In block (getMappedBlocks part1 s)
-> sh1entryPDchild (CPaddr (block + sh1offset)) nullAddr s
-> In addr (getMappedPaddr part2 s)
-> In part2 (part1::(filterOptionPaddr (completeParentsList part1 s))).
Proof.
intros HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HnoDupBlocks
  HnoDupPaddr HwellFormed HisChild HblockEquivParent HnoChild HPI Hpart1IsPart Hpart2IsPart HaddrInBlock
  HblockMapped1 HPDchild HaddrMapped2.
assert(Hres: In part1 (filterOptionPaddr (completeParentsList part2 s))
              \/ part1 = part2
              \/ In part2 (filterOptionPaddr (completeParentsList part1 s))).
{
  apply addressesBloodline with addr; try(assumption). apply addrInBlockIsMapped with block; assumption.
}
simpl. destruct Hres as [Hcontra | Hres]; try(assumption). exfalso.
assert(Hpart1IsPDT: isPDT part1 s).
{ apply partitionsArePDT; assumption. }
unfold isPDT in *. destruct (lookup part1 (memory s) beqAddr) eqn:HlookupPart1; try(congruence).
destruct v; try(congruence).
assert(HeqTriv: CPaddr (block + sh1offset) = CPaddr (block + sh1offset)) by reflexivity.
specialize(HnoChild part1 p block (CPaddr (block + sh1offset)) Hpart1IsPart HlookupPart1 HblockMapped1 HeqTriv
  HPDchild). clear Hpart1IsPDT. clear HeqTriv.
pose proof (completeParentsListChild part1 part2 s HPDTIfPDFlag HmultIsPDT HparentOfPart Hpart2IsPart Hcontra)
  as HcontraChild. destruct HcontraChild as [child (Hparent & HchildIsPart & HchildIsAnc)].
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
apply addrBelongToAncestors with part2; try(assumption). apply blockInclImpliesAddrIncl; assumption.
Qed.

Lemma completeParentsListRecN m n part1 part2 s:
m >= n
-> In part1 (filterOptionPaddr (completeParentsListRec n part2 s))
-> In part1 (filterOptionPaddr (completeParentsListRec m part2 s)).
Proof.
intro HlebMN. assert(Hplus: m = n + (m-n)) by lia. rewrite Hplus. clear Hplus.
revert m part2 HlebMN. induction n; simpl; intros m part2 HlebMN Hpart1IsAnc; try(exfalso; congruence).
destruct (lookup part2 (memory s) beqAddr) eqn:HlookupPart2; try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
destruct (beqAddr part2 constantRootPartM) eqn:HbeqPart2Root; try(simpl in *; exfalso; congruence). simpl in *.
destruct Hpart1IsAnc as [Hpart1IsParent | Hpart1IsAncRec].
- left. assumption.
- right. assert(HlebRec: m-1 >= n) by lia. specialize(IHn (m-1) (parent p) HlebRec Hpart1IsAncRec).
  replace (m - S n) with (m - 1 - n); try(lia). assumption.
Qed.

Lemma completeParentsListRecRec n child part pdparent s:
pdentryParent child pdparent s
-> beqAddr child constantRootPartM = false
-> In child (filterOptionPaddr (completeParentsListRec n part s))
-> In pdparent (filterOptionPaddr (completeParentsListRec (S n) part s)).
Proof.
intros Hparent HbeqChildRoot. revert part. induction n; simpl; intros part HchildIsAnc; try(exfalso; congruence).
destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; try(simpl in *; congruence).
destruct v; try(simpl in *; congruence). destruct (beqAddr part constantRootPartM); try(simpl in *; congruence).
simpl in *. destruct HchildIsAnc as [HchildIsParent | HchildIsAncRec].
- right. rewrite HchildIsParent in *. unfold pdentryParent in *.
  destruct (lookup child (memory s) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
  rewrite HbeqChildRoot. rewrite <-Hparent. simpl. left. reflexivity.
- right. apply IHn; assumption.
Qed.

Lemma completeParentsListRecApp n m part1 parent1 parent2 s:
In parent2 (filterOptionPaddr (completeParentsListRec m parent1 s))
-> In parent1 (filterOptionPaddr (completeParentsListRec n part1 s))
-> In parent2 (filterOptionPaddr (completeParentsListRec (n+m) part1 s)).
Proof.
intro Hparent2. revert part1. induction n; simpl in *; intros part1 Hparent1; try(exfalso; congruence).
destruct (lookup part1 (memory s) beqAddr) eqn:HlookupPart1; simpl in *; try(congruence).
destruct v; simpl in *; try(congruence).
destruct (beqAddr part1 constantRootPartM) eqn:HbeqPart1Root; simpl in *; try(congruence).
destruct Hparent1 as [Hparent1IsParent | Hparent1Rec].
- rewrite Hparent1IsParent. right. apply completeParentsListRecN with m. lia. assumption.
- right. apply IHn. assumption.
Qed.

Lemma completeParentsListOrientation part1 part2 s:
parentOfPartitionIsPartition s
-> partitionTreeIsTree s
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In part1 (filterOptionPaddr (completeParentsList part2 s))
-> ~ In part2 (filterOptionPaddr (completeParentsList part1 s)).
Proof.
intros HparentOfPart Htree Hpart1IsPart Hpart2IsPart Hpart1IsAnc Hcontra. unfold completeParentsList in *.
pose proof (completeParentsListRecApp (S (S maxAddr)) (S (S maxAddr)) part1 part2 part1 s Hpart1IsAnc Hcontra) as
  Hpart1IsAncOfPart1.
replace (S (S maxAddr) + S (S maxAddr)) with (S ((S maxAddr) + S (S maxAddr))) in *; try(lia).
set(n := S maxAddr + S (S maxAddr)). fold n in Hpart1IsAncOfPart1.
cbn -[n constantRootPartM] in Hpart1IsAncOfPart1.
destruct (lookup part1 (memory s) beqAddr) eqn:HlookupPart1; try(simpl in *; congruence).
destruct v; try(simpl in *; congruence).
destruct (beqAddr part1 constantRootPartM) eqn:HbeqPart1Root; try(simpl in *; congruence).
assert(HparentOfPartCopy: parentOfPartitionIsPartition s) by assumption.
specialize(HparentOfPartCopy part1 p HlookupPart1).
destruct HparentOfPartCopy as (HparentIsPart & _ & HbeqParentPart). rewrite <-beqAddrFalse in *.
specialize(HparentIsPart HbeqPart1Root). destruct HparentIsPart as ([parentEntry HlookupParent] & _).
cbn -[completeParentsListRec] in Hpart1IsAncOfPart1.
destruct Hpart1IsAncOfPart1 as [HcontraBis | Hpart1IsAncOfPart1]; try(congruence).
assert(HparentIsPDT: isPDT (parent p) s).
{
  unfold isPDT. rewrite HlookupParent. trivial.
}
pose proof (completeParentsListIsParentsListAux n (parent p) s HparentOfPart HparentIsPDT) as HparentsList.
assert(Hparent: pdentryParent part1 (parent p) s).
{ unfold pdentryParent. rewrite HlookupPart1. reflexivity. }
specialize(Htree part1 (parent p) (filterOptionPaddr (completeParentsListRec n (parent p) s)) HbeqPart1Root
  Hpart1IsPart Hparent HparentsList). subst n. contradict Htree. apply Hpart1IsAncOfPart1.
Qed.
