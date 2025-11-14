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
From Stdlib Require Import List Lia EqNat Arith Classical_Prop FunctionalExtensionality.
Import Compare_dec.
Require Import Model.ADT Model.Monad Model.MAL Model.Lib Core.Internal.

Require Import DependentTypeLemmas.
Require Import Proof.Isolation Proof.Consistency Proof.StateLib Proof.InternalLemmas.

Require Import Stdlib.Logic.ProofIrrelevance.
Require Import Stdlib.Program.Equality.

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

Lemma getAllPaddrAuxEqPDTNewPart blockList newPart newPDEntry s0:
lookup newPart (memory s0) beqAddr = None
-> getAllPaddrAux blockList {|
						                  currentPartition := currentPartition s0;
						                  memory := add newPart (PDT newPDEntry)
                              (memory s0) beqAddr |}
    = getAllPaddrAux blockList s0.
Proof.
intro HlookupNew. induction blockList.
- simpl. reflexivity.
- simpl. destruct (beqAddr newPart a) eqn:HbeqNewA.
  + rewrite <-DTL.beqAddrTrue in HbeqNewA. subst a. rewrite HlookupNew. assumption.
  + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup a (memory s0) beqAddr); try(assumption). destruct v; try(assumption). f_equal. assumption.
Qed.

Lemma getConfigBlocksAuxEqPDTNewEmptyPart n kernel maxStructNbleft newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> getConfigBlocksAux n kernel {|
						                      currentPartition := currentPartition s0;
						                      memory := add newPart (PDT newPDEntry)
                                  (memory s0) beqAddr |} maxStructNbleft
    = getConfigBlocksAux n kernel s0 maxStructNbleft.
Proof.
intros HlookupNews0. revert kernel maxStructNbleft. induction n; intros kernel maxStructNbleft; simpl;
  try(reflexivity). destruct (beqAddr newPart kernel) eqn:HbeqNewKern.
+ rewrite <-DTL.beqAddrTrue in HbeqNewKern. subst kernel.
  destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & Hstruct)]]; rewrite HlookupNews0; reflexivity.
+ rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  destruct (lookup kernel (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
  destruct (Paddr.addPaddrIdx kernel nextoffset); try(reflexivity).
  destruct (beqAddr newPart p) eqn:HbeqNewP.
  * rewrite <-DTL.beqAddrTrue in HbeqNewP. subst p.
    destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & Hstruct)]]; rewrite HlookupNews0;
      reflexivity.
  * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup p (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
    destruct (Index.pred maxStructNbleft); try(reflexivity). f_equal. apply IHn.
Qed.

Lemma getConfigBlocksEqPDTNewEmptyPart partition newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> structure newPDEntry = nullAddr
-> nullAddrExists s0
-> getConfigBlocks partition {|
						                  currentPartition := currentPartition s0;
						                  memory := add newPart (PDT newPDEntry)
                              (memory s0) beqAddr |}
    = getConfigBlocks partition s0.
Proof.
intros HlookupNews0 HbeqStructNull Hnull. unfold getConfigBlocks. simpl.
destruct (beqAddr newPart partition) eqn:HbeqNewPart.
- rewrite HbeqStructNull. rewrite <-DTL.beqAddrTrue in HbeqNewPart. subst partition.
  unfold nullAddrExists in *. unfold isPADDR in *.
  destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & Hstruct)]].
  + rewrite HlookupNews0. rewrite MaxIdxNextEq. simpl. destruct (beqAddr newPart nullAddr) eqn:HbeqNewNull.
    { simpl; reflexivity. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). destruct (beqAddr p nullAddr); simpl; reflexivity.
  + rewrite HlookupNews0. rewrite Hstruct. rewrite MaxIdxNextEq. simpl.
    destruct (beqAddr newPart nullAddr) eqn:HbeqNewNull.
    { rewrite <-DTL.beqAddrTrue in HbeqNewNull. subst newPart. rewrite HlookupNews0 in *. exfalso; congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  destruct (lookup partition (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity). f_equal.
  apply getConfigBlocksAuxEqPDTNewEmptyPart. assumption.
Qed.

Lemma getAllPaddrConfigAuxEqPDTNewEmptyPart kernList newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> getAllPaddrConfigAux kernList {|
						                      currentPartition := currentPartition s0;
						                      memory := add newPart (PDT newPDEntry)
                                  (memory s0) beqAddr |}
    = getAllPaddrConfigAux kernList s0.
Proof.
intro HlookupNews0. induction kernList; simpl; try(reflexivity).
destruct (beqAddr newPart a) eqn:HbeqNewA.
- rewrite <-DTL.beqAddrTrue in HbeqNewA. subst a.
  destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & Hstruct)]]; rewrite HlookupNews0; assumption.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  destruct (lookup a (memory s0) beqAddr); try(assumption). destruct v; try(assumption). f_equal. assumption.
Qed.

Lemma getConfigPaddrEqPDTNewEmptyPart partition newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> structure newPDEntry = nullAddr
-> nullAddrExists s0
-> beqAddr newPart partition = false
-> getConfigPaddr partition {|
						                  currentPartition := currentPartition s0;
						                  memory := add newPart (PDT newPDEntry)
                              (memory s0) beqAddr |}
    = getConfigPaddr partition s0.
Proof.
intros HlookupNews0 HbeqStructNull Hnull HbeqNewPart. unfold getConfigPaddr.
rewrite getConfigBlocksEqPDTNewEmptyPart; try(assumption).
rewrite getAllPaddrConfigAuxEqPDTNewEmptyPart; try(assumption). f_equal. simpl. rewrite HbeqNewPart.
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
destruct (lookup partition (memory s0) beqAddr); reflexivity.
Qed.

Lemma filterAccessibleEqPDTNewPart blockList newPart newPDEntry s0:
(lookup newPart (memory s0) beqAddr = None
  \/ exists pdentry, lookup newPart (memory s0) beqAddr = Some(PDT pdentry) /\ structure pdentry = nullAddr)
-> filterAccessible blockList {|
						                    currentPartition := currentPartition s0;
						                    memory := add newPart (PDT newPDEntry)
                                (memory s0) beqAddr |}
    = filterAccessible blockList s0.
Proof.
intro HlookupNews0. induction blockList; simpl; try(reflexivity). destruct (beqAddr newPart a) eqn:HbeqNewA.
- rewrite <-DTL.beqAddrTrue in HbeqNewA. subst a.
  destruct HlookupNews0 as [HlookupNews0 | [pdentry (HlookupNews0 & Hstruct)]]; rewrite HlookupNews0; assumption.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  destruct (lookup a (memory s0) beqAddr); try(assumption). destruct v; try(assumption).
  destruct (accessible b); try(assumption). f_equal. assumption.
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

Lemma parentsListGivesPartitionsAux n partition newRoot s:
isChild s
-> parentOfPartitionIsPartition s
-> In partition (getPartitions multiplexer s)
-> In newRoot (partition::filterOptionPaddr (completeParentsListRec n partition s))
-> In partition (getPartitionsAux (S n) newRoot s).
Proof.
intros HisChild HparentOfPart. revert partition. induction n; simpl; intros partition HpartIsPart HrootIsAnc.
- left. intuition.
- simpl in *. destruct HrootIsAnc as [HbeqPartRoot | HrootIsAnc]; try(left; apply eq_sym; assumption). right.
  destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(simpl in *; exfalso; congruence).
  destruct v; try(simpl in *; exfalso; congruence).
  destruct (beqAddr partition constantRootPartM) eqn:HbeqPartRoot; try(simpl in *; exfalso; congruence).
  assert(HparentOfPartCopy: parentOfPartitionIsPartition s) by assumption.
  rewrite <-beqAddrFalse in HbeqPartRoot. specialize(HparentOfPartCopy partition p HlookupPart).
  destruct HparentOfPartCopy as (HparentIsPart & _). specialize(HparentIsPart HbeqPartRoot).
  destruct HparentIsPart as ([pdentryPdparent HlookupParent] & HparentIsPart). simpl in *.
  specialize(IHn (parent p) HparentIsPart HrootIsAnc). clear HrootIsAnc. destruct IHn as [HrootIsParent | HrootIsAnc].
  + subst newRoot. assert(Hparent: pdentryParent partition (parent p) s).
    { unfold pdentryParent. rewrite HlookupPart. reflexivity. }
    specialize(HisChild partition (parent p) HpartIsPart Hparent HbeqPartRoot).
    induction (getChildren (parent p) s); simpl in *; try(congruence).
    destruct HisChild as [HaIsPart | HpartInList].
    * left. assumption.
    * right. apply in_or_app. right. apply IHl. assumption.
  + induction (getChildren newRoot s); simpl in *; try(congruence). apply in_app_or in HrootIsAnc.
    right. apply in_or_app. destruct HrootIsAnc as [HparentDescA | HrootIsAncRec].
    * left. clear IHl. clear HparentIsPart. clear HlookupParent.
      revert partition p a HlookupPart HparentDescA HbeqPartRoot HpartIsPart.
      induction n; simpl; intros; try(exfalso; congruence). destruct HparentDescA as [HparentIsA | HparentDescARec].
      -- subst a. assert(Hparent: pdentryParent partition (parent p) s).
         { unfold pdentryParent. rewrite HlookupPart. reflexivity. }
         specialize(HisChild partition (parent p) HpartIsPart Hparent HbeqPartRoot).
         induction (getChildren (parent p) s); simpl in *; try(congruence).
         destruct HisChild as [HaIsPart | HpartInList].
         ++ left. assumption.
         ++ right. apply in_or_app. right. apply IHl0. assumption.
      -- induction (getChildren a s); simpl in *; try(congruence). apply in_app_or in HparentDescARec.
         destruct HparentDescARec as [HparentDescA0 | HparentDescARecRec].
         ++ specialize(IHn partition p a0 HlookupPart HparentDescA0 HbeqPartRoot HpartIsPart). right. apply in_or_app.
            left. assumption.
         ++ right. apply in_or_app. right. apply IHl0. assumption.
    * right. apply IHl. assumption.
Qed.

Lemma getPartitionsEnd partition s n:
length (getPartitionsAux n partition s) < n
-> getPartitionsAux (S n) partition s = getPartitionsAux n partition s.
Proof.
revert partition. induction n; simpl; intros partition Hlen; try(lia).
assert(HlenBis: length (flat_map (fun p : paddr => getPartitionsAux n p s) (getChildren partition s)) < n) by lia.
clear Hlen. f_equal. induction (getChildren partition s); simpl in *; try(reflexivity). rewrite length_app in HlenBis.
assert(Hlen: length (flat_map (fun p : paddr => getPartitionsAux n p s) l) < n) by lia.
specialize(IHl Hlen). rewrite IHl. assert(HlenA: length (getPartitionsAux n a s) < n) by lia.
specialize(IHn a HlenA). rewrite <-IHn. apply app_comm_cons.
Qed.

Lemma getPartitionsEndAny partition s n m:
n < m
-> length (getPartitionsAux n partition s) < n
-> getPartitionsAux m partition s = getPartitionsAux n partition s.
Proof.
intro HltNM. assert(Hm: m = n + (m - n)) by lia. rewrite Hm in *. clear Hm.
induction (m - n); simpl; intros Hlen; try(lia).
replace (n + S n0) with (S (n + n0)) in *; try(lia). destruct (le_lt_dec (n+n0) n).
- assert(Hn: n = n + n0) by lia. rewrite <-Hn in *. apply getPartitionsEnd. assumption.
- specialize(IHn0 l Hlen). rewrite <-IHn0. apply getPartitionsEnd. rewrite IHn0. lia.
Qed.

Lemma getPartitionsLenDescendants n partition newRoot s:
In partition (getPartitionsAux n newRoot s)
-> length (getPartitionsAux n newRoot s) < n
-> length (getPartitionsAux n partition s) < n.
Proof.
revert newRoot partition. induction n; simpl; intros newRoot partition HpartIsPart HlenRoot; try(lia).
destruct HpartIsPart as [HrootIsPart | HpartIsPartRec]; try(subst partition; assumption).
apply Nat.succ_lt_mono in HlenRoot.
assert(Hres: length (flat_map (fun p : paddr => getPartitionsAux n p s) (getChildren partition s)) < n).
{
  induction (getChildren newRoot s); simpl in *; try(exfalso; congruence). rewrite length_app in HlenRoot.
  apply in_app_or in HpartIsPartRec. destruct HpartIsPartRec as [HpartDesA | HpartIsPartRec].
  - clear IHl. assert(HlenPart: length (getPartitionsAux n partition s) < n).
    { apply IHn with a. assumption. lia. }
    assert(HgetPartsEq: getPartitionsAux (S n) partition s = getPartitionsAux n partition s).
    { apply getPartitionsEnd. assumption. }
    rewrite <-HgetPartsEq in HlenPart. simpl in *. lia.
  - apply IHl. assumption. lia.
}
lia.
Qed.

Lemma noDupPartitionTreeChildrenAux n newRoot s partition:
NoDup (getPartitionsAux n newRoot s)
-> length (getPartitionsAux n newRoot s) < n
-> In partition (getChildren newRoot s)
-> NoDup (getPartitionsAux n partition s).
Proof.
intros HnoDup HlenRoot HpartIsPart.
assert(HgetPartsRootEq: getPartitionsAux (S n) newRoot s = getPartitionsAux n newRoot s).
{ apply getPartitionsEnd. assumption. }
rewrite <-HgetPartsRootEq in *. clear HgetPartsRootEq. simpl in *. apply NoDup_cons_iff in HnoDup. clear HlenRoot.
destruct HnoDup as (_ & HnoDupRec). induction (getChildren newRoot s); simpl in *; try(exfalso; congruence).
apply Lib.NoDupSplitInclIff in HnoDupRec. destruct HnoDupRec as ((HnoDupDescA & HnoDupRec) & _).
destruct HpartIsPart as [HaIsPart | HpartIsDesc]; try(subst a; assumption). apply IHl; assumption.
Qed.

Lemma noDupPartitionTreeRecAux n partition newRoot s:
NoDup (getPartitionsAux n newRoot s)
-> length (getPartitionsAux n newRoot s) < n
-> In partition (getPartitionsAux n newRoot s)
-> NoDup (getPartitionsAux n partition s).
Proof.
revert partition newRoot. induction n; intros partition newRoot HnoDup Hlen HpartIsPart;
  try(simpl in *; exfalso; congruence).
assert(HnoDupCopy: NoDup (getPartitionsAux (S n) newRoot s)) by assumption. simpl in HnoDup.
apply NoDup_cons_iff in HnoDup. simpl. apply NoDup_cons_iff. destruct HnoDup as (HrootNotInDesc & HnoDupDesc).
assert(HlenBis: length (flat_map (fun p : paddr => getPartitionsAux n p s) (getChildren newRoot s)) < n)
  by (simpl in *; lia).
destruct HpartIsPart as [HpartIsRoot | HpartIsDesc]; try(subst partition; split; assumption).
assert(Hchildren: forall partition, In partition (getChildren newRoot s)
          -> NoDup (getPartitionsAux (S n) partition s)).
{ intro part. apply noDupPartitionTreeChildrenAux; assumption. }
simpl in HpartIsDesc.
induction (getChildren newRoot s); try(simpl in *; exfalso; congruence). simpl in HrootNotInDesc. simpl in HlenBis.
simpl in HnoDupDesc. simpl in HpartIsDesc. apply Lib.in_app_or_neg in HrootNotInDesc.
destruct HrootNotInDesc as (HrootNotDescA & HrootNotInDescRec). apply Lib.NoDupSplitInclIff in HnoDupDesc.
destruct HnoDupDesc as ((HnoDupDescA & HnoDupDescRec) & HdisjointDesc). rewrite length_app in HlenBis.
assert(HlenA: length (getPartitionsAux n a s) < n) by lia.
assert(HlenRec: length (flat_map (fun p : paddr => getPartitionsAux n p s) l) < n) by lia. clear HlenBis.
specialize(IHl HrootNotInDescRec HnoDupDescRec). apply in_app_or in HpartIsDesc.
assert(HchildrenRec: forall partition, In partition l -> NoDup (getPartitionsAux (S n) partition s)).
{ intros part HpartInList. apply Hchildren. simpl. right. assumption. }
destruct HpartIsDesc as [HpartDescA | HpartIsDescRec]; try(apply IHl; assumption).
clear IHl. assert(Htmp: In a (a :: l)) by (simpl; left; reflexivity). specialize(Hchildren a Htmp). clear Htmp.
assert(HgetPartsAEq: getPartitionsAux (S n) a s = getPartitionsAux n a s).
{ apply getPartitionsEnd. assumption. }
rewrite HgetPartsAEq in *. specialize(IHn partition a Hchildren HlenA HpartDescA).
assert(HlenPart: length (getPartitionsAux n partition s) < n).
{ apply getPartitionsLenDescendants with a; assumption. }
assert(HgetPartsEq: getPartitionsAux (S n) partition s = getPartitionsAux n partition s).
{ apply getPartitionsEnd. assumption. }
rewrite <-HgetPartsEq in IHn. simpl in IHn. apply NoDup_cons_iff in IHn. assumption.
Qed.

Lemma noDupPartitionTreeRec partition s:
noDupPartitionTree s
-> In partition (getPartitions multiplexer s)
-> NoDup (getPartitions partition s).
Proof.
intros HnoDup HpartIsPart. unfold noDupPartitionTree in *.
assert(Hlen: length (getPartitions multiplexer s) <= maxAddr+1).
{ apply lengthNoDupPartitions. assumption. }
unfold getPartitions in *. replace (maxAddr + 2) with (S (maxAddr + 1)) in *; try(lia).
apply noDupPartitionTreeRecAux with multiplexer; try(assumption). lia.
Qed.

Lemma parentsListGivesPartitions partition newRoot s:
isChild s
-> parentOfPartitionIsPartition s
-> noDupPartitionTree s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> In partition (getPartitions multiplexer s)
-> In newRoot (partition::filterOptionPaddr (completeParentsList partition s))
-> In partition (getPartitions newRoot s).
Proof.
intros HisChild HparentOfPart HnoDupTree HPDTIfPDFlag HmultIsPDT HpartIsPart HrootIsAnc.
assert(Hres: In partition (getPartitionsAux (S (S (S maxAddr))) newRoot s)).
{
  unfold completeParentsList in *. apply parentsListGivesPartitionsAux; assumption.
}
assert(Hlen: length (getPartitions newRoot s) <= maxAddr + 1).
{
  apply lengthNoDupPartitions. apply noDupPartitionTreeRec. assumption.
  simpl in HrootIsAnc.  destruct HrootIsAnc as [HrootIsPart | HrootIsAncRec].
  - subst partition. assumption.
  - revert HrootIsAncRec. apply partInParentsListIsPartition with partition; try(assumption).
    apply completeParentsListIsParentsList. assumption.
    apply partitionsArePDT; assumption.
}
unfold getPartitions in *. replace (maxAddr + 2) with (S (S maxAddr)) in *; try(lia).
assert(HgetPartsEq: getPartitionsAux (S (S (S maxAddr))) newRoot s = getPartitionsAux (S (S maxAddr)) newRoot s).
{ apply getPartitionsEnd. lia. }
rewrite HgetPartsEq in *. assumption.
Qed.

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
-> noDupMappedPaddrList s
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
specialize(HnoDupPaddr partition HpartIsPDT).
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

Lemma equivalentAncestorsBlock desc blockDesc startDesc endDesc partition s:
isChild s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> parentOfPartitionIsPartition s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> In desc (getPartitions multiplexer s)
-> In partition (getPartitions multiplexer s)
-> In partition (filterOptionPaddr (completeParentsList desc s))
-> bentryStartAddr blockDesc startDesc s
-> bentryEndAddr blockDesc endDesc s
-> In blockDesc (getMappedBlocks desc s)
-> exists blockAnc startAnc endAnc, In blockAnc (getMappedBlocks partition s)
    /\ bentryStartAddr blockAnc startAnc s
    /\ bentryEndAddr blockAnc endAnc s
    /\ startAnc <= startDesc /\ endAnc >= endDesc.
Proof.
intros HisChild HPDTIfPDFlag HmultIsPDT HparentOfPart HequivParent HdescIsPart HpartIsPart HdescIsDesc.
revert desc blockDesc startDesc endDesc HdescIsPart HdescIsDesc.
unfold completeParentsList in *. induction (S (S maxAddr)); intros desc blockDesc startDesc endDesc HdescIsPart
  HdescIsDesc HstartDesc HendDesc HblockDescMapped; simpl in *; try(exfalso; congruence).
assert(HdescIsPDT: isPDT desc s).
{ apply partitionsArePDT; assumption. }
unfold isPDT in HdescIsPDT. destruct (lookup desc (memory s) beqAddr) eqn:HlookupDesc; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct (beqAddr desc constantRootPartM) eqn:HbeqDescRoot; simpl in *; try(exfalso; congruence).
specialize(HparentOfPart desc p HlookupDesc). destruct HparentOfPart as (HparentIsPart & _).
rewrite <-beqAddrFalse in *. specialize(HparentIsPart HbeqDescRoot).
destruct HparentIsPart as (_ & HparentIsPart).
assert(Hparent: pdentryParent desc (parent p) s).
{ unfold pdentryParent. rewrite HlookupDesc. reflexivity. }
assert(HdescIsChild: In desc (getChildren (parent p) s)).
{ specialize(HisChild desc (parent p) HdescIsPart Hparent HbeqDescRoot). assumption. }
assert(HPflagDesc: bentryPFlag blockDesc true s).
{
  apply mappedBlockIsBE in HblockDescMapped. destruct HblockDescMapped as [bentry (HlookupBlockDesc & Hpresent)].
  unfold bentryPFlag. rewrite HlookupBlockDesc. apply eq_sym. assumption.
}
specialize(HequivParent (parent p) desc blockDesc startDesc endDesc HparentIsPart HdescIsChild HblockDescMapped
  HstartDesc HendDesc HPflagDesc).
destruct HdescIsDesc as [HpartIsParent | HdescIsDescRec]; try(rewrite HpartIsParent in *; assumption).
destruct HequivParent as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & HendParent &
  HlebStart & HgebEnd)]]]. specialize(IHn (parent p) blockParent startParent endParent HparentIsPart HdescIsDescRec
  HstartParent HendParent HblockParentMapped). destruct IHn as [blockAnc [startAnc [endAnc (HblockAncMapped &
  HstartAnc & HendAnc & HlebStartBis & HgebEndBis)]]]. exists blockAnc. exists startAnc. exists endAnc. split.
assumption. split. assumption. split. assumption. split; lia.
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
-> noDupMappedPaddrList s
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
-> noDupMappedPaddrList s
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
-> noDupMappedPaddrList s
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

(*Lemma PDflagImpliesNoChild block s:
partitionsIsolation s
-> noDupUsedPaddrList s
-> blockBelongsToAPart s
-> PDTIfPDFlag s
-> multiplexerIsPDT s
-> nullAddrExists s
-> isInChildIfPDchild s
-> wellFormedBlock s
-> isBE block s
-> sh1entryPDflag (CPaddr (block + sh1offset)) true s
-> sh1entryPDchild (CPaddr (block + sh1offset)) nullAddr s.
Proof.
intros HPI HnoDupUsed HblockInPart HPDTIfPDFlag HmultIsPDT Hnull HchildIfPDchild HwellFormed HblockIsBE HPDflag.
specialize(HblockInPart block HblockIsBE). destruct HblockInPart as [partition (HpartIsPart & HblockMappedPart)].
unfold isBE in *. destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
assert(HpartIsPDT: isPDT partition s).
{ apply partitionsArePDT; assumption. }
assert(HstartIsChild: In (startAddr (blockrange b)) (getChildren partition s)).
{
  unfold getChildren. unfold isPDT in *. destruct (lookup partition (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). unfold getPDs. induction (getMappedBlocks partition s).
  - simpl in *. congruence.
  - simpl in *. destruct HblockMappedPart as [HaIsBlock | HblockMappedPartRec].
    + subst a. assert(HisChild: childFilter s block = true).
      {
        unfold childFilter. rewrite HlookupBlock. unfold Paddr.addPaddrIdx. unfold sh1entryPDflag in *.
        unfold CPaddr in HPDflag. destruct (le_dec (block + sh1offset) maxAddr).
        - assert(Heq: {| p := block + sh1offset; Hp := ADT.CPaddr_obligation_1 (block + sh1offset) l0 |}
                    = {| p := block + sh1offset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 block sh1offset l0 |}).
          { f_equal. }
          rewrite Heq in *.
          destruct (lookup {| p := block + sh1offset;
                              Hp := StateLib.Paddr.addPaddrIdx_obligation_1 block sh1offset l0 |}
                    (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
          apply eq_sym. assumption.
        - exfalso. unfold nullAddrExists in *. unfold isPADDR in *.
          assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          rewrite HnullEq in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
          destruct v; congruence.
      }
      rewrite HisChild. simpl. rewrite HlookupBlock. left. reflexivity.
    + specialize(IHl HblockMappedPartRec). destruct (childFilter s a); try(assumption). simpl. right. assumption.
}
specialize(HnoDupUsed partition HpartIsPDT).
assert(HPDflagCopy: sh1entryPDflag (CPaddr (block + sh1offset)) true s) by assumption.
unfold sh1entryPDflag in HPDflagCopy. unfold sh1entryPDchild.
destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(congruence).
destruct v; try(congruence). destruct (beqAddr nullAddr (PDchild s0)) eqn:HbeqNullChild.
- rewrite <-DTL.beqAddrTrue in HbeqNullChild. assumption.
- rewrite <-beqAddrFalse in *. exfalso. apply not_eq_sym in HbeqNullChild.
  assert(HPDchild: sh1entryPDchild (CPaddr (block + sh1offset)) (PDchild s0) s).
  {
    unfold sh1entryPDchild. rewrite HlookupSh1. reflexivity.
  }
  specialize(HchildIfPDchild block partition (PDchild s0) HpartIsPart HblockMappedPart HPDchild HbeqNullChild).
  destruct HchildIfPDchild as (HchildIsChild & HblocksAddrMappedChild).
  (*pose proof (childrenArePDT partition (startAddr (blockrange b)) s HPDTIfPDFlag HstartIsChild) as HstartIsPDT.*)
  assert(HstartInBlock: In (startAddr (blockrange b)) (getAllPaddrAux [block] s)).
  {
    simpl. rewrite HlookupBlock. rewrite app_nil_r.
    assert(HPFlag: bentryPFlag block true s).
    {
      apply mappedBlockIsBE in HblockMappedPart. destruct HblockMappedPart as [bentry (HlookupBlockBis & Hpresent)].
      unfold bentryPFlag. rewrite HlookupBlockBis. apply eq_sym. assumption.
    }
    assert(Hstart: bentryStartAddr block (startAddr (blockrange b)) s).
    {
      apply lookupBEntryStartAddr; assumption.
    }
    assert(Hend: bentryEndAddr block (endAddr (blockrange b)) s).
    {
      apply lookupBEntryEndAddr; assumption.
    }
    specialize(HwellFormed block (startAddr (blockrange b)) (endAddr (blockrange b)) HPFlag Hstart Hend).
    destruct HwellFormed as (HwellFormed & _). apply getAllPaddrBlockIncl; lia.
  }
  specialize(HblocksAddrMappedChild (startAddr (blockrange b)) HstartInBlock).
Qed.*)

(*Lemma addressesBloodlineIfPart s part1 part2 addr block:
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
-> noChildImpliesAddressesNotShared s (**)
-> partitionsIsolation s
-> In part1 (getPartitions multiplexer s)
-> In part2 (getPartitions multiplexer s)
-> In addr (getAllPaddrAux [block] s)
-> In block (getMappedBlocks part1 s)
-> sh1entryPDflag (CPaddr (block + sh1offset)) true s
-> In addr (getMappedPaddr part2 s)
-> In part2 (part1::(filterOptionPaddr (completeParentsList part1 s))).
Proof.
intros HisParent HnoDupTree HparentOfPart HPDTIfPDFlag HmultIsPDT HnullExists HpartTreeIsTree HnoDupBlocks
  HnoDupPaddr HwellFormed HisChild HblockEquivParent HnoChild HPI Hpart1IsPart Hpart2IsPart HaddrInBlock
  HblockMapped1 HPDflag HaddrMapped2.
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
Qed.*)

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

(* DUP *)
Lemma childFilterEqSHENotAddr addr' newEntry s0 (blockentryaddr: paddr) sh1entry0:
lookup addr' (memory s0) beqAddr = Some (SHE sh1entry0) ->
beqAddr addr' (CPaddr (blockentryaddr + sh1offset)) = false ->
childFilter {|
						currentPartition := currentPartition s0;
						memory := add addr' (SHE newEntry)
            (memory s0) beqAddr |} blockentryaddr =
childFilter s0 blockentryaddr.
Proof.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
intros HPDTaddrs0 HbeqAddrSh1.
unfold childFilter.
cbn.

	destruct (beqAddr addr' blockentryaddr) eqn:Hf ; try(exfalso ; congruence).
	-- rewrite <- DTL.beqAddrTrue in Hf.
		subst blockentryaddr.
		unfold isSHE in *.
		destruct (lookup addr' (memory s0) beqAddr) eqn:Hff ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
		trivial.
	--
			rewrite <- beqAddrFalse in Hf.
			repeat rewrite removeDupIdentity ; intuition.
			destruct (lookup blockentryaddr (memory s0) beqAddr) ; intuition.
			destruct v ; intuition.
			destruct (Paddr.addPaddrIdx blockentryaddr sh1offset) eqn:Hadd; intuition. unfold Paddr.addPaddrIdx in Hadd.
      unfold CPaddr in HbeqAddrSh1. destruct (le_dec (blockentryaddr + sh1offset) maxAddr); try(exfalso; congruence).
      injection Hadd as Hsh1Eq. subst p.
      replace {|
                p := blockentryaddr + sh1offset;
                Hp := StateLib.Paddr.addPaddrIdx_obligation_1 blockentryaddr sh1offset l
              |} with
        {| p := blockentryaddr + sh1offset; Hp := ADT.CPaddr_obligation_1 (blockentryaddr + sh1offset) l |};
        try(f_equal; apply proof_irrelevance). rewrite HbeqAddrSh1.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
Qed.

(* DUP *)
Lemma getPDsEqSHEPDflagTrue addr block startaddr sh1entryaddr newEntry s0 pdlist sh1entry0:
nullAddrExists s0 ->
lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0) ->
sh1entryAddr block sh1entryaddr s0 ->
bentryStartAddr block startaddr s0 ->
PDflag newEntry = true ->
In addr (getPDs pdlist {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |})
-> In addr (startaddr::getPDs pdlist s0).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HlookupSh1s0 Hsh1 Hstart HPDflagTrue. unfold nullAddrExists in *. unfold isPADDR in *.
unfold getPDs.
unfold s. simpl. fold s.
induction pdlist; simpl.
- intuition.
- destruct (beqAddr block a) eqn:HbeqBlocks.
  + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst a.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    {
      simpl. destruct (beqAddr sh1entryaddr block) eqn:HbeqSh1Block.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Block. subst block. unfold bentryStartAddr in Hstart.
        rewrite HlookupSh1s0 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HisChildFilt: childFilter s block = true).
    {
      unfold childFilter. rewrite HlookupBlockEq. unfold bentryStartAddr in *. unfold sh1entryAddr in *.
      destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      unfold Paddr.addPaddrIdx. subst sh1entryaddr. unfold CPaddr in *.
      destruct (le_dec (block + sh1offset) maxAddr).
      - replace {| p := block + sh1offset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 block sh1offset l |} with
          {| p := block + sh1offset; Hp := ADT.CPaddr_obligation_1 (block + sh1offset) l |};
          try(f_equal; apply proof_irrelevance). simpl. rewrite beqAddrTrue. assumption.
      - exfalso.
        assert(HeqNull: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HeqNull in *. rewrite HlookupSh1s0 in *. congruence.
    }
    rewrite HisChildFilt. simpl. destruct (beqAddr sh1entryaddr block) eqn:HbeqSh1Block.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Block. subst block. unfold bentryStartAddr in Hstart.
      rewrite HlookupSh1s0 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). intro HaddrInPDs.
    destruct HaddrInPDs as [HaddrIsStart | HaddrInPDsRec].
    * left. unfold bentryStartAddr in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). subst addr. assumption.
    * apply IHpdlist in HaddrInPDsRec. destruct (childFilter s0 block); try(assumption). simpl. right.
      unfold bentryStartAddr in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). subst startaddr. assumption.
  + assert(beqAddr sh1entryaddr (CPaddr (a + sh1offset)) = false).
    {
      rewrite <-beqAddrFalse in *. unfold sh1entryAddr in *. intro Hcontra.
      destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence). subst sh1entryaddr.
      unfold CPaddr in *. destruct (le_dec (block + sh1offset) maxAddr).
      - destruct (le_dec (a + sh1offset) maxAddr).
        + injection Hcontra as Heq. apply Nat.add_cancel_r in Heq. apply paddrEqNatEqEquiv in Heq. congruence.
        + rewrite Hcontra in *.
          assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (p a + i sh1offset) n |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1s0 in *. congruence.
      - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (p block + i sh1offset) n |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HnullEq in *. rewrite HlookupSh1s0 in *. congruence.
    }
    assert(HfilterEq: childFilter s a = (childFilter s0 a)).
    { eapply childFilterEqSHENotAddr with sh1entry0; intuition. }
    rewrite HfilterEq. intro HaddrInPDs.
    destruct (childFilter s0 a) ; intuition. simpl in *. destruct HaddrInPDs as [HaddrIsStart | HaddrInPDsRec].
    * right. left. destruct (beqAddr sh1entryaddr a) eqn:HbeqSh1A.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1A. subst a. unfold childFilter in *. simpl in HfilterEq.
        rewrite beqAddrTrue in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HaddrIsStart; try(apply not_eq_sym); assumption.
    * apply IHpdlist in HaddrInPDsRec. intuition.
Qed.

Lemma getChildrenEqSHEPDflagTrue partition addr block startaddr sh1entryaddr newEntry s0 sh1entry0:
nullAddrExists s0 ->
isPDT partition s0 ->
lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0) ->
sh1entryAddr block sh1entryaddr s0 ->
bentryStartAddr block startaddr s0 ->
PDflag newEntry = true ->
In addr (getChildren partition {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |})
-> In addr (startaddr::(getChildren partition s0)).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HPDTs0 HlookupSh1s0 Hsh1 Hstart HPDflag.
unfold getChildren. unfold s. intro HaddrInChildren. simpl in HaddrInChildren.

destruct (beqAddr sh1entryaddr partition) eqn:beqSh1Part ; try(exfalso ; congruence).
- (* sh1entryaddr = partition *)
	rewrite <- DTL.beqAddrTrue in beqSh1Part. fold s.
	subst sh1entryaddr.
	unfold isSHE in *. unfold isPDT in *.
	destruct (lookup partition (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
	destruct v ; try(exfalso ; congruence).

- (* sh1entryaddr <> partition *)
	rewrite <- beqAddrFalse in *.
	rewrite removeDupIdentity in HaddrInChildren; intuition. unfold isPDT in *.
	destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
	destruct v; try(exfalso; congruence).	fold s.	fold s in HaddrInChildren.
	assert(HSHEs0 : isSHE sh1entryaddr s0) by (unfold isSHE ; rewrite HlookupSh1s0; trivial).
	assert(HmappedEq: getMappedBlocks partition s = getMappedBlocks partition s0).
	{ eapply getMappedBlocksEqSHE; intuition. unfold isPDT. rewrite HlookupPart. trivial. }
	rewrite HmappedEq in *.
	apply getPDsEqSHEPDflagTrue with block sh1entryaddr newEntry sh1entry0; intuition.
Qed.

Lemma getPartitionsAuxEqSHEPDflagTrue partition addr block startaddr sh1entryaddr newEntry sh1entry0 s0 n :
nullAddrExists s0 ->
lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0) ->
sh1entryAddr block sh1entryaddr s0 ->
bentryStartAddr block startaddr s0 ->
PDflag newEntry = true ->
PDTIfPDFlag s0 ->
getChildren startaddr {|
                        currentPartition := currentPartition s0;
                        memory := add sh1entryaddr (SHE newEntry)
                                    (memory s0) beqAddr |} = [] ->
isPDT partition s0 ->
In addr (getPartitionsAux n partition {|
                currentPartition := currentPartition s0;
                memory := add sh1entryaddr (SHE newEntry)
                            (memory s0) beqAddr |})
-> startaddr = addr \/ In addr (getPartitionsAux n partition s0).
Proof.
intros Hnull HlookupSh1 Hsh1 Hstart HPDflag HPDTIfPDFlag HgetChildrenNew. revert partition.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}). fold s in HgetChildrenNew.
induction n; simpl; intros partition HpartIsPDT HaddrInParts; try(exfalso; congruence).
destruct HaddrInParts as [HaddrIsPart | HaddrInPartsRec]; try(right; left; assumption).
assert(Hchildren: forall addr, In addr (getChildren partition s)
                              -> In addr (startaddr :: getChildren partition s0)).
{
  intro addrBis. apply getChildrenEqSHEPDflagTrue with block sh1entry0; assumption.
}
induction (getChildren partition s); simpl in *; try(exfalso; congruence). apply in_app_or in HaddrInPartsRec.
assert(HchildrenRec: forall addr, In addr l -> In addr (startaddr :: getChildren partition s0)).
{
  intros addrBis Haddr. apply Hchildren. simpl. right. assumption.
}
assert(Hincl: In a (a :: l)) by (simpl; left; reflexivity). specialize(Hchildren a Hincl). simpl in *.
destruct HaddrInPartsRec as [HaddrInA | HaddrInPartsRecRec].
- destruct Hchildren as [HstartIsA | HAIsChild].
  + subst a. destruct n; simpl in HaddrInA; try(exfalso; congruence). rewrite HgetChildrenNew in HaddrInA.
    simpl in HaddrInA. destruct HaddrInA as [Hleft | Hcontra]; try(exfalso; congruence). left. assumption.
  + assert(HaIsPDT: isPDT a s0).
    { apply childrenArePDT with partition; assumption. }
    specialize(IHn a HaIsPDT HaddrInA). destruct IHn as [HstartIsAddr | HaddrInAs0]; try(left; assumption).
    right. right. clear HchildrenRec. clear IHl. induction (getChildren partition s0); simpl in *; try(congruence).
    apply in_or_app. destruct HAIsChild as [Ha | HAIsChildRec].
    * subst a0. left. assumption.
    * right. apply IHl0; assumption.
- apply IHl; assumption.
Qed.

(* DUP *)
Lemma getPartitionsEqSHEPDflagTrue partition addr block startaddr sh1entryaddr newEntry sh1entry0 s0:
nullAddrExists s0 ->
lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0) ->
sh1entryAddr block sh1entryaddr s0 ->
bentryStartAddr block startaddr s0 ->
PDflag newEntry = true ->
PDTIfPDFlag s0 ->
getChildren startaddr
  {|
    currentPartition := currentPartition s0;
    memory := add sh1entryaddr (SHE newEntry) (memory s0) beqAddr
  |} = [] ->
isPDT partition s0 ->
In addr (getPartitions partition {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |})
-> In addr (startaddr::getPartitions partition s0).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HlookupSh1 Hsh1 Hstart HPDflag HPDTIfPDflags0 HgetChildrenNew HPDTs0.
unfold getPartitions. apply getPartitionsAuxEqSHEPDflagTrue with block sh1entry0; assumption.
Qed.

(* DUP *)
Lemma getPDsEqSHEPDflagTrueRev addr block startaddr sh1entryaddr newEntry s0 pdlist sh1entry0:
nullAddrExists s0 ->
lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0) ->
sh1entryAddr block sh1entryaddr s0 ->
bentryStartAddr block startaddr s0 ->
PDflag newEntry = true
-> In addr (getPDs pdlist s0)
-> In addr (getPDs pdlist {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |}).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HlookupSh1s0 Hsh1 Hstart HPDflagTrue. unfold nullAddrExists in *. unfold isPADDR in *.
unfold getPDs.
unfold s. simpl. fold s.
induction pdlist; simpl.
- intuition.
- destruct (beqAddr block a) eqn:HbeqBlocks.
  + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst a.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    {
      simpl. destruct (beqAddr sh1entryaddr block) eqn:HbeqSh1Block.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Block. subst block. unfold bentryStartAddr in Hstart.
        rewrite HlookupSh1s0 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HisChildFilt: childFilter s block = true).
    {
      unfold childFilter. rewrite HlookupBlockEq. unfold bentryStartAddr in *. unfold sh1entryAddr in *.
      destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      unfold Paddr.addPaddrIdx. subst sh1entryaddr. unfold CPaddr in *.
      destruct (le_dec (block + sh1offset) maxAddr).
      - replace {| p := block + sh1offset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 block sh1offset l |} with
          {| p := block + sh1offset; Hp := ADT.CPaddr_obligation_1 (block + sh1offset) l |};
          try(f_equal; apply proof_irrelevance). simpl. rewrite beqAddrTrue. assumption.
      - exfalso.
        assert(HeqNull: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HeqNull in *. rewrite HlookupSh1s0 in *. congruence.
    }
    rewrite HisChildFilt. simpl. destruct (beqAddr sh1entryaddr block) eqn:HbeqSh1Block.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Block. subst block. unfold bentryStartAddr in Hstart.
      rewrite HlookupSh1s0 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). intro HaddrInPDs0.
    destruct (childFilter s0 block); try(right; apply IHpdlist; assumption). simpl in *.
    destruct HaddrInPDs0 as [HaddrIsStart | HaddrInPDs0Rec]; try(left; assumption). right. apply IHpdlist.
    assumption.
  + assert(beqAddr sh1entryaddr (CPaddr (a + sh1offset)) = false).
    {
      rewrite <-beqAddrFalse in *. unfold sh1entryAddr in *. intro Hcontra.
      destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence). subst sh1entryaddr.
      unfold CPaddr in *. destruct (le_dec (block + sh1offset) maxAddr).
      - destruct (le_dec (a + sh1offset) maxAddr).
        + injection Hcontra as Heq. apply Nat.add_cancel_r in Heq. apply paddrEqNatEqEquiv in Heq. congruence.
        + rewrite Hcontra in *.
          assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (p a + i sh1offset) n |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1s0 in *. congruence.
      - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (p block + i sh1offset) n |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HnullEq in *. rewrite HlookupSh1s0 in *. congruence.
    }
    assert(HfilterEq: childFilter s a = childFilter s0 a).
    { eapply childFilterEqSHENotAddr with sh1entry0; intuition. }
    rewrite HfilterEq. intro HaddrInPDs0.
    destruct (childFilter s0 a) ; intuition. simpl in *. destruct HaddrInPDs0 as [HaddrIsStart | HaddrInPDs0Rec].
    * left. destruct (beqAddr sh1entryaddr a) eqn:HbeqSh1A.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1A. subst a. unfold childFilter in *. simpl in HfilterEq.
        rewrite beqAddrTrue in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    * apply IHpdlist in HaddrInPDs0Rec. intuition.
Qed.

Lemma getChildrenEqSHEPDflagTrueRev partition addr block startaddr sh1entryaddr newEntry s0 sh1entry0:
nullAddrExists s0 ->
isPDT partition s0 ->
lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0) ->
sh1entryAddr block sh1entryaddr s0 ->
bentryStartAddr block startaddr s0 ->
PDflag newEntry = true
-> In addr (getChildren partition s0)
-> In addr (getChildren partition {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |}).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HPDTs0 HlookupSh1s0 Hsh1 Hstart HPDflag.
unfold getChildren. unfold s. intro HaddrInChildren. simpl.

destruct (beqAddr sh1entryaddr partition) eqn:beqSh1Part.
- (* sh1entryaddr = partition *)
	rewrite <- DTL.beqAddrTrue in beqSh1Part. fold s.
	subst sh1entryaddr.
	unfold isSHE in *. unfold isPDT in *.
	destruct (lookup partition (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
	destruct v ; try(exfalso ; congruence).

- (* sh1entryaddr <> partition *)
	rewrite <- beqAddrFalse in *.
	rewrite removeDupIdentity; intuition. unfold isPDT in *.
	destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
	destruct v; try(exfalso; congruence).	fold s.
	assert(HSHEs0 : isSHE sh1entryaddr s0) by (unfold isSHE ; rewrite HlookupSh1s0; trivial).
	assert(HmappedEq: getMappedBlocks partition s = getMappedBlocks partition s0).
	{ eapply getMappedBlocksEqSHE; intuition. unfold isPDT. rewrite HlookupPart. trivial. }
	rewrite HmappedEq in *.
	apply getPDsEqSHEPDflagTrueRev with block startaddr sh1entry0; intuition.
Qed.

Lemma getPartitionsAuxEqSHEPDflagTrueRev partition addr block startaddr sh1entryaddr newEntry sh1entry0 s0 n :
nullAddrExists s0 ->
lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0) ->
sh1entryAddr block sh1entryaddr s0 ->
bentryStartAddr block startaddr s0 ->
PDflag newEntry = true ->
PDTIfPDFlag {|
              currentPartition := currentPartition s0;
              memory := add sh1entryaddr (SHE newEntry)
                          (memory s0) beqAddr |} ->
getChildren startaddr s0 = [] ->
isPDT partition s0
-> In addr (getPartitionsAux n partition s0)
-> In addr (getPartitionsAux n partition {|
                currentPartition := currentPartition s0;
                memory := add sh1entryaddr (SHE newEntry)
                            (memory s0) beqAddr |}).
Proof.
intros Hnull HlookupSh1 Hsh1 Hstart HPDflag HPDTIfPDFlag HgetChildrenNew. revert partition.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}). fold s in HgetChildrenNew.
induction n; simpl; intros partition HpartIsPDT HaddrInParts; try(exfalso; congruence).
destruct HaddrInParts as [HaddrIsPart | HaddrInPartsRec]; try(left; assumption).
assert(Hchildren: forall addr, In addr (getChildren partition s0)
                              -> In addr (getChildren partition s)).
{
  intro addrBis. apply getChildrenEqSHEPDflagTrueRev with block startaddr sh1entry0; assumption.
}
induction (getChildren partition s0); simpl in *; try(exfalso; congruence). apply in_app_or in HaddrInPartsRec.
assert(HchildrenRec: forall addr, In addr l -> In addr (getChildren partition s)).
{
  intros addrBis Haddr. apply Hchildren. simpl. right. assumption.
}
assert(Hincl: In a (a :: l)) by (simpl; left; reflexivity). specialize(Hchildren a Hincl).
destruct HaddrInPartsRec as [HaddrInA | HaddrInPartsRecRec].
- assert(HaIsPDTs: isPDT a s).
  { apply childrenArePDT with partition; try(assumption). }
  assert(HaIsPDT: isPDT a s0).
  {
    unfold isPDT in *. simpl in *. destruct (beqAddr sh1entryaddr a) eqn:HbeqSh1A; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HaIsPDTs; try(apply not_eq_sym); assumption.
  }
  specialize(IHn a HaIsPDT HaddrInA). right. clear HchildrenRec. clear IHl.
  induction (getChildren partition s); simpl in *; try(congruence). apply in_or_app.
  destruct Hchildren as [Ha | HAIsChildRec].
  + subst a0. left. assumption.
  + right. apply IHl0; assumption.
- apply IHl; assumption.
Qed.

(* DUP *)
Lemma getPartitionsEqSHEPDflagTrueRev partition addr block startaddr sh1entryaddr newEntry sh1entry0 s0:
nullAddrExists s0 ->
lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0) ->
sh1entryAddr block sh1entryaddr s0 ->
bentryStartAddr block startaddr s0 ->
PDflag newEntry = true ->
PDTIfPDFlag {|
              currentPartition := currentPartition s0;
              memory := add sh1entryaddr (SHE newEntry)
                          (memory s0) beqAddr |} ->
getChildren startaddr s0 = [] ->
isPDT partition s0
-> In addr (getPartitions partition s0)
-> In addr (getPartitions partition {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |}).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HlookupSh1 Hsh1 Hstart HPDflag HPDTIfPDflags0 HgetChildrenNew HPDTs0.
unfold getPartitions. apply getPartitionsAuxEqSHEPDflagTrueRev with block startaddr sh1entry0; assumption.
Qed.

(* DUP *)
Lemma getPDsEqSHENotInList block sh1entryaddr newEntry s0 pdlist:
nullAddrExists s0 ->
isSHE sh1entryaddr s0
-> sh1entryAddr block sh1entryaddr s0
-> (forall block, In block pdlist -> ~ sh1entryAddr block sh1entryaddr s0)
-> getPDs pdlist {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |} = getPDs pdlist s0.
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HlookupSh1s0 Hsh1 HnotInList. unfold nullAddrExists in *. unfold isPADDR in *.
unfold getPDs. induction pdlist; simpl; try(reflexivity).
assert(HnotInListRec: forall block, In block pdlist -> ~ sh1entryAddr block sh1entryaddr s0).
{
  intros blockBis Hblock. apply HnotInList. simpl. right. assumption.
}
assert(HaIsA: In a (a :: pdlist)) by (simpl; left; reflexivity). specialize(HnotInList a HaIsA).
destruct (beqAddr sh1entryaddr (CPaddr (a + sh1offset))) eqn:HbeqSh1s.
{
  rewrite <-DTL.beqAddrTrue in HbeqSh1s. subst sh1entryaddr. unfold sh1entryAddr in *. exfalso.
  destruct (lookup block (memory s0) beqAddr) eqn:HlookupBlock; try(congruence). destruct v; try(congruence).
  unfold isSHE in *. unfold CPaddr in Hsh1. unfold CPaddr in HlookupSh1s0. destruct (le_dec (a + sh1offset) maxAddr).
  - destruct (le_dec (block + sh1offset) maxAddr).
    + injection Hsh1 as Heq. apply Nat.add_cancel_r in Heq. apply paddrEqNatEqEquiv in Heq. subst a.
      rewrite HlookupBlock in *. congruence.
    + rewrite Hsh1 in *.
      assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
      {
        unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
      }
      rewrite HnullEq in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (a + sh1offset) n |} = nullAddr).
    {
      unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
    }
    rewrite HnullEq in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
unfold isSHE in HlookupSh1s0.
assert(HfilterEq: childFilter s a = childFilter s0 a).
{
  destruct (lookup sh1entryaddr (memory s0) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). eapply childFilterEqSHENotAddr with s1; intuition.
}
rewrite HfilterEq. specialize(IHpdlist HnotInListRec). destruct (childFilter s0 a); try(assumption). simpl.
rewrite IHpdlist. destruct (beqAddr sh1entryaddr a) eqn:HbeqSh1A.
- rewrite <-DTL.beqAddrTrue in HbeqSh1A. subst a.
  destruct (lookup sh1entryaddr (memory s0) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
Qed.

Lemma getChildrenEqSHENotInList partition block sh1entryaddr newEntry s0:
nullAddrExists s0 ->
isPDT partition s0 ->
isSHE sh1entryaddr s0 ->
sh1entryAddr block sh1entryaddr s0 ->
(forall block, In block (getMappedBlocks partition s0) -> ~ sh1entryAddr block sh1entryaddr s0)
-> getChildren partition {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |} = getChildren partition s0.
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HPDTs0 HlookupSh1s0 Hsh1 HnotInList.
unfold getChildren. unfold s. simpl.

destruct (beqAddr sh1entryaddr partition) eqn:HbeqSh1Part.
{ (* sh1entryaddr = partition *)
	rewrite <- DTL.beqAddrTrue in HbeqSh1Part. fold s.
	subst sh1entryaddr.
	unfold isSHE in *. unfold isPDT in *.
	destruct (lookup partition (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
	destruct v ; try(exfalso ; congruence).
}
(* sh1entryaddr <> partition *)
rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition. unfold isPDT in *.
destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
destruct v; try(exfalso; congruence).	fold s.
assert(HmappedEq: getMappedBlocks partition s = getMappedBlocks partition s0).
{ eapply getMappedBlocksEqSHE; intuition. unfold isPDT. rewrite HlookupPart. trivial. }
rewrite HmappedEq in *.
apply getPDsEqSHENotInList with block; intuition.
Qed.

Lemma getPartitionsAuxEqSHENotInList partition block sh1entryaddr newEntry s0 n :
nullAddrExists s0 ->
isSHE sh1entryaddr s0 ->
sh1entryAddr block sh1entryaddr s0 ->
parentOfPartitionIsPartition s0 ->
isParent s0 ->
partitionTreeIsTree s0 ->
PDTIfPDFlag s0 ->
multiplexerIsPDT s0 ->
noDupPartitionTree s0 ->
In partition (getPartitions multiplexer s0) ->
(forall part, In partition (part::filterOptionPaddr (completeParentsList part s0))
    -> (forall blockBis, In blockBis (getMappedBlocks part s0)
          -> ~ sh1entryAddr blockBis sh1entryaddr s0)) ->
isPDT partition s0 ->
getPartitionsAux n partition {|
                currentPartition := currentPartition s0;
                memory := add sh1entryaddr (SHE newEntry)
                            (memory s0) beqAddr |} = getPartitionsAux n partition s0.
Proof.
intros Hnull HlookupSh1 Hsh1 HparentOfPart HisParent Htree HPDTIfPDFlag HmultIsPDT HnoDups0. revert partition.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
induction n; simpl; intros partition HpartIsPart Hsh1NotInChildren HpartIsPDT; try(reflexivity). f_equal.
assert(Hsh1NotInList: forall block, In block (getMappedBlocks partition s0)
          -> ~ sh1entryAddr block sh1entryaddr s0).
{
  assert(HpartInPartsAnc: In partition (partition::filterOptionPaddr (completeParentsList partition s0))).
  { simpl. left. reflexivity. }
  specialize(Hsh1NotInChildren partition HpartInPartsAnc). assumption.
}
assert(Hchildren: getChildren partition s = getChildren partition s0).
{
  apply getChildrenEqSHENotInList with block; assumption.
}
rewrite Hchildren. clear Hchildren. assert(Hparent: parentOfPartitionIsPartition s0) by assumption.
assert(HpartIsChildrensAnc: forall child, In child (getChildren partition s0)
        -> In partition (filterOptionPaddr (completeParentsList child s0))
            /\ In child (getPartitions multiplexer s0)
            /\ beqAddr child constantRootPartM = false
            /\ pdentryParent child partition s0).
{
  intros child HchildIsChild. unfold completeParentsList. simpl.
  specialize(HisParent child partition HpartIsPart HchildIsChild). unfold pdentryParent in *.
  destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). specialize(Hparent child p HlookupChild).
  destruct Hparent as (HparentIsPart & HparentOfRoot & _).
  destruct (beqAddr child constantRootPartM) eqn:HbeqChildRoot.
  {
    rewrite <-DTL.beqAddrTrue in HbeqChildRoot. specialize(HparentOfRoot HbeqChildRoot). subst partition.
    rewrite HparentOfRoot in *. exfalso. unfold nullAddrExists in *. unfold isPADDR in *. unfold isPDT in *.
    destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  }
  rewrite <-beqAddrFalse in HbeqChildRoot. subst partition. simpl. split.
  - left. reflexivity.
  - split; try(split; reflexivity). apply childrenPartitionInPartitionList with (parent p); assumption.
}
induction (getChildren partition s0); simpl in *; try(reflexivity).
assert(HpartIsChildrensAncRec: forall child, In child l
        -> In partition (filterOptionPaddr (completeParentsList child s0))
            /\ In child (getPartitions multiplexer s0) /\ beqAddr child constantRootPartM = false
            /\ pdentryParent child partition s0).
{
  intros child Hchild. apply HpartIsChildrensAnc. right. assumption.
}
specialize(IHl HpartIsChildrensAncRec). rewrite IHl. f_equal. assert(HaIsA: a = a \/ In a l) by (left; reflexivity).
specialize(HpartIsChildrensAnc a HaIsA).
destruct HpartIsChildrensAnc as (HpartIsAnc & HaIsPart & HbeqARoot & HaIsChild). apply IHn; try(assumption).
- intros part HpartIsDesc. apply Hsh1NotInChildren. right. destruct HpartIsDesc as [HpartIsA | HaIsAnc].
  + subst a. assumption.
  + apply parentIsInParentList with a; try(assumption). unfold completeParentsList in HaIsAnc. simpl in *.
    unfold isPDT. destruct (lookup part (memory s0) beqAddr); try(simpl in *; congruence).
    destruct v; try(simpl in *; congruence). trivial.
- apply partitionsArePDT; assumption.
Qed.

(* DUP *)
Lemma getPDsEqSHEPDflagTrueVal block startaddr sh1entryaddr newEntry s0 pdlist sh1entry0:
nullAddrExists s0
-> lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0)
-> sh1entryAddr block sh1entryaddr s0
-> bentryStartAddr block startaddr s0
-> In block pdlist
-> NoDup pdlist
-> PDflag newEntry = true
-> PDflag sh1entry0 = false
-> exists list1 list2, getPDs pdlist s0 = list1 ++ list2 /\
      getPDs pdlist {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |} = list1 ++ (startaddr::list2).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HlookupSh1s0 Hsh1 Hstart HblockInList HnoDupList HPDflagTrue HandPDflagFalse. unfold nullAddrExists in *.
unfold isPADDR in *. unfold getPDs. induction pdlist; simpl.
- exfalso. intuition.
- simpl in *. apply NoDup_cons_iff in HnoDupList. destruct HnoDupList as (HblockNotInList & HnoDupListRec).
  destruct HblockInList as [HaIsBlock | HblockInListRec].
  + subst a. exists [].
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    {
      simpl. destruct (beqAddr sh1entryaddr block) eqn:HbeqSh1Block.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Block. subst block. unfold bentryStartAddr in Hstart.
        rewrite HlookupSh1s0 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HisChildFilt: childFilter s block = true).
    {
      unfold childFilter. rewrite HlookupBlockEq. unfold bentryStartAddr in *. unfold sh1entryAddr in *.
      destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      unfold Paddr.addPaddrIdx. subst sh1entryaddr. unfold CPaddr in *.
      destruct (le_dec (block + sh1offset) maxAddr).
      - replace {| p := block + sh1offset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 block sh1offset l |} with
          {| p := block + sh1offset; Hp := ADT.CPaddr_obligation_1 (block + sh1offset) l |};
          try(f_equal; apply proof_irrelevance). simpl. rewrite beqAddrTrue. assumption.
      - exfalso.
        assert(HeqNull: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HeqNull in *. rewrite HlookupSh1s0 in *. congruence.
    }
    assert(HisChildFilts0: childFilter s0 block = false).
    {
      unfold childFilter. unfold bentryStartAddr in *. unfold sh1entryAddr in *.
      destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      unfold Paddr.addPaddrIdx. subst sh1entryaddr. unfold CPaddr in *.
      destruct (le_dec (block + sh1offset) maxAddr).
      - replace {| p := block + sh1offset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 block sh1offset l |} with
          {| p := block + sh1offset; Hp := ADT.CPaddr_obligation_1 (block + sh1offset) l |};
          try(f_equal; apply proof_irrelevance). rewrite HlookupSh1s0. assumption.
      - reflexivity.
    }
    rewrite HisChildFilt. rewrite HisChildFilts0. exists (getPDsPaddr (filter (childFilter s0) pdlist) s0).
    split. reflexivity. simpl. simpl in HlookupBlockEq. rewrite HlookupBlockEq. unfold bentryStartAddr in *.
    destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    rewrite <-Hstart. f_equal.
    assert(Hsh1IsSHE: isSHE sh1entryaddr s0).
    { unfold isSHE. rewrite HlookupSh1s0. trivial. }
    pose proof (getPDsEqSHENotInList block sh1entryaddr newEntry s0 pdlist Hnull Hsh1IsSHE Hsh1) as Hres.
    fold s in Hres. unfold getPDs in *. apply Hres. intros blockBis HblockBisInList Hcontra.
    assert(block <> blockBis).
    { intro Heq. subst blockBis. congruence. }
    unfold sh1entryAddr in *. destruct (lookup block (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). destruct (lookup blockBis (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). subst sh1entryaddr. unfold CPaddr in Hcontra. unfold CPaddr in HlookupSh1s0.
    destruct (le_dec (block + sh1offset) maxAddr).
    * destruct (le_dec (blockBis + sh1offset) maxAddr).
      -- injection Hcontra as Heq. apply Nat.add_cancel_r in Heq. apply paddrEqNatEqEquiv in Heq. congruence.
      -- rewrite Hcontra in *.
         assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockBis + sh1offset) n |} = nullAddr).
         { unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance. }
         rewrite HnullEq in *. rewrite HlookupSh1s0 in *. congruence.
    * assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
      { unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance. }
      rewrite HnullEq in *. rewrite HlookupSh1s0 in *. congruence.
  + specialize(IHpdlist HblockInListRec HnoDupListRec).
    assert(block <> a).
    { intro Hcontra. subst a. congruence. }
    assert(HchildFilEq: childFilter s a = childFilter s0 a).
    {
      unfold childFilter. simpl. destruct (beqAddr sh1entryaddr a) eqn:HbeqSh1A.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1A. subst a. rewrite HlookupSh1s0. reflexivity.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup a (memory s0) beqAddr) eqn:HlookupA; try(reflexivity). destruct v; try(reflexivity).
      destruct (Paddr.addPaddrIdx a sh1offset) eqn:Hadd; try(reflexivity).
      destruct (beqAddr sh1entryaddr p) eqn:HbeqSh1s.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1s. unfold Paddr.addPaddrIdx in Hadd. exfalso.
        destruct (le_dec (a + sh1offset) maxAddr) eqn:HleSh1a; try(congruence). injection Hadd as HeqP.
        unfold sh1entryAddr in *. destruct (lookup block (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). rewrite <-HeqP in HbeqSh1s. subst sh1entryaddr. unfold CPaddr in HbeqSh1s.
        unfold CPaddr in HlookupSh1s0. destruct (le_dec (block + sh1offset) maxAddr).
        - injection HbeqSh1s as Heq. apply Nat.add_cancel_r in Heq. apply paddrEqNatEqEquiv in Heq. congruence.
        - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (ADT.p block + i sh1offset) n |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1s0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    rewrite HchildFilEq. destruct IHpdlist as [leftList [rightList (Hlists0Eq & HlistsEq)]].
    destruct (childFilter s0 a).
    * simpl. rewrite Hlists0Eq. rewrite HlistsEq. destruct (beqAddr sh1entryaddr a) eqn:HbeqSh1A.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1A. subst a. rewrite HlookupSh1s0. exists (nullAddr :: leftList).
        exists rightList. split; reflexivity.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      set(firstElem := match lookup a (memory s0) beqAddr with
                        | Some (BE bentry) => startAddr (blockrange bentry)
                        | _ => nullAddr
                        end).
      exists (firstElem :: leftList). exists rightList. split; reflexivity.
    * exists leftList. exists rightList. split; assumption.
Qed.

Lemma getChildrenEqSHEPDflagTrueVal partition block startaddr sh1entryaddr newEntry s0 sh1entry0:
nullAddrExists s0
-> noDupMappedBlocksList s0
-> isPDT partition s0
-> lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0)
-> sh1entryAddr block sh1entryaddr s0
-> bentryStartAddr block startaddr s0
-> In block (getMappedBlocks partition s0)
-> PDflag newEntry = true
-> PDflag sh1entry0 = false
-> exists list1 list2, getChildren partition s0 = list1 ++ list2
      /\ getChildren partition {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |} = list1 ++ (startaddr::list2).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HnoDup HPDTs0 HlookupSh1s0 Hsh1 Hstart HblockMapped HPDflag HPDflagAnc.
unfold getChildren. simpl.

destruct (beqAddr sh1entryaddr partition) eqn:HbeqSh1Part.
{ (* sh1entryaddr = partition *)
	rewrite <- DTL.beqAddrTrue in HbeqSh1Part. subst sh1entryaddr. unfold isPDT in *. rewrite HlookupSh1s0 in *.
	exfalso; congruence.
}
(* sh1entryaddr <> partition *)
rewrite <- beqAddrFalse in *.
rewrite removeDupIdentity; try(apply not_eq_sym; assumption). unfold isPDT in *.
destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
assert(HSHEs0 : isSHE sh1entryaddr s0) by (unfold isSHE ; rewrite HlookupSh1s0; trivial).
assert(HmappedEq: getMappedBlocks partition s = getMappedBlocks partition s0).
{ eapply getMappedBlocksEqSHE; intuition. unfold isPDT. rewrite HlookupPart. trivial. }
rewrite HmappedEq in *.
apply getPDsEqSHEPDflagTrueVal with block sh1entry0; try(assumption). unfold noDupMappedBlocksList in *.
apply HnoDup. unfold isPDT. rewrite HlookupPart. trivial.
Qed.

Lemma noDupGetPartitionsAuxImplAux n partition s0:
NoDup (getPartitionsAux (S n) partition s0)
-> NoDup (getPartitionsAux n partition s0).
Proof.
revert partition. induction n; intros partition HnoDup; simpl; try(apply NoDup_nil). set(succ := S n).
fold succ in HnoDup. cbn -[succ] in HnoDup. apply NoDup_cons_iff in HnoDup. apply NoDup_cons_iff.
destruct HnoDup as (HpartNotInDesc & HnoDupRec). simpl in HpartNotInDesc.
induction (getChildren partition s0); cbn -[succ] in HpartNotInDesc; cbn -[succ] in HnoDupRec; try(split; assumption).
apply Lib.NoDupSplitInclIff in HnoDupRec. destruct HnoDupRec as ((HnoDupDescA & HnoDupRec) & HdisjointDesc).
apply not_or_and in HpartNotInDesc. destruct HpartNotInDesc as (HbeqAPart & HpartNotInDescRec).
apply Lib.in_app_or_neg in HpartNotInDescRec. destruct HpartNotInDescRec as (HpartNotInDescA & HpartNotInDescRec).
specialize(IHl HpartNotInDescRec HnoDupRec). destruct IHl as (HpartNotInDescRecN & HnoDupRecN). simpl.
specialize(IHn a HnoDupDescA). split.
- apply Lib.in_or_app_neg. split; try(assumption). contradict HpartNotInDescA.
  assert(Hnext: In partition (getPartitionsAux (S n) a s0)).
  {
    replace (S n) with (n+1); try(lia). apply getPartitionsAuxSbound. assumption.
  }
  simpl in Hnext. destruct Hnext; try(exfalso; congruence). assumption.
- apply Lib.NoDupSplitInclIff. split; try(split).
  + assumption.
  + assumption.
  + intros part HpartIsDescA. assert(HpartIsDescASucc: In part (getPartitionsAux succ a s0)).
    { subst succ. replace (S n) with (n+1); try(lia). apply getPartitionsAuxSbound. assumption. }
    specialize(HdisjointDesc part HpartIsDescASucc). clear HnoDupRec. clear HnoDupRecN. clear HpartNotInDescRecN.
    clear HpartNotInDescRec. induction l.
    * simpl. intuition.
    * cbn -[succ] in *. apply Lib.in_app_or_neg in HdisjointDesc. apply Lib.in_or_app_neg.
      destruct HdisjointDesc as (HpartNotDesA0 & HpartNotDescRec). split; try(apply IHl; assumption).
      contradict HpartNotDesA0. subst succ. replace (S n) with (n+1); try(lia).
      apply getPartitionsAuxSbound. assumption.
Qed.

Lemma noDupGetPartitionsAuxImpl m n partition s0:
m > n
-> NoDup (getPartitionsAux m partition s0)
-> NoDup (getPartitionsAux n partition s0).
Proof.
intro HgtMN. assert(Hm: m = n + (m - n)) by lia. rewrite Hm in *. clear Hm. revert HgtMN.
induction (m - n); simpl; intros HgtMN HnoDup; try(rewrite <-plus_n_O in *; assumption).
replace (n + S n0) with (S (n + n0)) in *; try(lia).
assert(HnoDupPred: NoDup (getPartitionsAux (n + n0) partition s0)).
{ apply noDupGetPartitionsAuxImplAux. assumption. }
destruct (gt_dec (n + n0) n).
- specialize(IHn0 g HnoDupPred). assumption.
- assert(Heq: n + n0 = n) by lia. rewrite Heq in *. assumption.
Qed.

Lemma getPartitionsAuxEqSHEPDflagTrueVal partition block startaddr sh1entryaddr newEntry sh1entry0 s0 n :
nullAddrExists s0
-> noDupMappedBlocksList s0
-> parentOfPartitionIsPartition s0
-> isParent s0
-> isChild s0
-> partitionTreeIsTree s0
-> PDTIfPDFlag s0
-> multiplexerIsPDT s0
-> noDupPartitionTree s0
-> DisjointKSEntries s0
-> noDupMappedPaddrList s0
-> wellFormedBlock s0
-> lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0)
-> sh1entryAddr block sh1entryaddr s0
-> bentryStartAddr block startaddr s0
-> PDflag newEntry = true
-> PDflag sh1entry0 = false
-> getChildren startaddr {|
                        currentPartition := currentPartition s0;
                        memory := add sh1entryaddr (SHE newEntry)
                                    (memory s0) beqAddr |} = []
-> n < S (S (S maxAddr))
-> n > length (getPartitionsAux n partition s0)
-> isPDT partition s0
-> In partition (getPartitions multiplexer s0)
-> (exists descPart, In descPart (getPartitions multiplexer s0) /\ In descPart (getPartitionsAux n partition s0)
        /\ In block (getMappedBlocks descPart s0))
-> NoDup (getPartitionsAux n partition s0)
-> exists list1 list2, getPartitionsAux n partition s0 = list1 ++ list2
    /\ getPartitionsAux n partition {|
                currentPartition := currentPartition s0;
                memory := add sh1entryaddr (SHE newEntry)
                            (memory s0) beqAddr |} = list1 ++ (startaddr::list2).
Proof.
intros Hnull HnoDupMapped HparentOfPart HisParent HisChild Htree HPDTIfPDFlag HmultIsPDT HnoDupTree Hdisjoint
  HnoDupUsed HwellFormedBlock HlookupSh1 Hsh1 Hstart HPDflag HancPDflag HgetChildrenNew HltNMax. revert partition.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}). fold s in HgetChildrenNew.
induction n; simpl; intros partition HnAboveLen HpartIsPDT HpartIsPart Hdesc HnoDupTreePart;
  destruct Hdesc as [descPart (HdescIsPart & Hdesc & HblockMapped)]; try(exfalso; congruence).
assert(HchildrenAreNotPart: forall child, In child (getChildren partition s0)
        -> In child (getPartitions multiplexer s0) /\ partition <> child /\ pdentryParent child partition s0).
{
  intros child HchildIsChild. pose proof (childrenPartitionInPartitionList s0 child partition HnoDupTree HpartIsPart
    HchildIsChild) as HchildIsPart. specialize(HisParent child partition HpartIsPart HchildIsChild). split.
  assumption. unfold pdentryParent in *.
  destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild). subst partition. split.
  apply HparentOfPart. reflexivity.
}
apply NoDup_cons_iff in HnoDupTreePart. destruct HnoDupTreePart as (HpartNotInSub & HnoDupTreePartRec).
assert(HnAboveLenRec: n > length (flat_map (fun p : paddr => getPartitionsAux n p s0) (getChildren partition s0)))
  by lia. destruct (beqAddr partition descPart) eqn:HbeqPartDesc.
- rewrite <-DTL.beqAddrTrue in HbeqPartDesc. subst descPart.
  pose proof (getChildrenEqSHEPDflagTrueVal partition block startaddr sh1entryaddr newEntry s0 sh1entry0 Hnull
    HnoDupMapped HpartIsPDT HlookupSh1 Hsh1 Hstart HblockMapped HPDflag HancPDflag) as Hchildren.
  destruct Hchildren as [childList1 [childList2 (HgetChildrens0 & HgetChildrens)]]. rewrite HgetChildrens0.
  fold s in HgetChildrens. rewrite HgetChildrens. rewrite flat_map_app. rewrite flat_map_app. simpl.
  exists (partition::flat_map (fun p : paddr => getPartitionsAux n p s0) childList1).
  exists (flat_map (fun p : paddr => getPartitionsAux n p s0) childList2). split. reflexivity.
  rewrite <-app_comm_cons. f_equal.
  rewrite HgetChildrens0 in HchildrenAreNotPart.
  assert(Hsh1NotInList1: forall child, In child childList1
          -> forall part, In child (part :: filterOptionPaddr (completeParentsList part s0))
          -> forall blockBis : paddr, In blockBis (getMappedBlocks part s0)
          -> ~ sh1entryAddr blockBis sh1entryaddr s0).
  {
    intros child Hchild part HchildIsAnc blockBis HblockBisMapped Hcontra.
    assert(HchildIsChild: In child (childList1 ++ childList2)) by (apply in_or_app; left; assumption).
    specialize(HchildrenAreNotPart child HchildIsChild). clear HchildIsChild.
    destruct HchildrenAreNotPart as (_ & HbeqPartChild & HchildIsChild).
    assert(HblocksEq: blockBis = block).
    {
      destruct (beqAddr blockBis block) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
      rewrite <-beqAddrFalse in HbeqBlocks. unfold sh1entryAddr in *.
      destruct (lookup blockBis (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence). subst sh1entryaddr.
      unfold nullAddrExists in *. unfold isPADDR in *.
      unfold CPaddr in Hcontra. unfold CPaddr in HlookupSh1. destruct (le_dec (block + sh1offset) maxAddr).
      - destruct (le_dec (blockBis + sh1offset) maxAddr).
        + injection Hcontra as Hcontra. apply Nat.add_cancel_r in Hcontra. apply paddrEqNatEqEquiv in Hcontra.
          congruence.
        + rewrite Hcontra in *.
          assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockBis + sh1offset) n0 |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n0 |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
    }
    subst blockBis. destruct (beqAddr part partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. simpl in HchildIsAnc.
      destruct HchildIsAnc as [Hcontra2 | HchildIsAnc]; try(congruence).
      assert(HpartIsAnc: In partition (filterOptionPaddr (completeParentsList partition s0))).
      { apply parentIsInParentList with child; assumption. }
      pose proof (completeParentsListOrientation partition partition s0 HparentOfPart Htree HpartIsPart HpartIsPart
        HpartIsAnc). congruence.
    - rewrite <-beqAddrFalse in HbeqParts. assert(HpartBisIsPDT: isPDT part s0).
      {
        unfold isPDT. unfold getMappedBlocks in HblockBisMapped. unfold getKSEntries in HblockBisMapped.
        destruct (lookup part (memory s0) beqAddr); try(simpl in *; congruence).
        destruct v; try(simpl in *; congruence). trivial.
      }
      specialize(Hdisjoint part partition HpartBisIsPDT HpartIsPDT HbeqParts).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      unfold getMappedBlocks in *. apply InFilterPresentInList in HblockBisMapped.
      apply InFilterPresentInList in HblockMapped. specialize(Hdisjoint block HblockBisMapped). congruence.
  }
  (*DUP*)
  assert(Hsh1NotInList2: forall child, In child childList2
          -> forall part, In child (part :: filterOptionPaddr (completeParentsList part s0))
          -> forall blockBis : paddr, In blockBis (getMappedBlocks part s0)
          -> ~ sh1entryAddr blockBis sh1entryaddr s0).
  {
    intros child Hchild part HchildIsAnc blockBis HblockBisMapped Hcontra.
    assert(HchildIsChild: In child (childList1 ++ childList2)) by (apply in_or_app; right; assumption).
    specialize(HchildrenAreNotPart child HchildIsChild). clear HchildIsChild.
    destruct HchildrenAreNotPart as (_ & HbeqPartChild & HchildIsChild).
    assert(HblocksEq: blockBis = block).
    {
      destruct (beqAddr blockBis block) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
      rewrite <-beqAddrFalse in HbeqBlocks. unfold sh1entryAddr in *.
      destruct (lookup blockBis (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence). subst sh1entryaddr.
      unfold nullAddrExists in *. unfold isPADDR in *.
      unfold CPaddr in Hcontra. unfold CPaddr in HlookupSh1. destruct (le_dec (block + sh1offset) maxAddr).
      - destruct (le_dec (blockBis + sh1offset) maxAddr).
        + injection Hcontra as Hcontra. apply Nat.add_cancel_r in Hcontra. apply paddrEqNatEqEquiv in Hcontra.
          congruence.
        + rewrite Hcontra in *.
          assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockBis + sh1offset) n0 |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n0 |} = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
    }
    subst blockBis. destruct (beqAddr part partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. simpl in HchildIsAnc.
      destruct HchildIsAnc as [Hcontra2 | HchildIsAnc]; try(congruence).
      assert(HpartIsAnc: In partition (filterOptionPaddr (completeParentsList partition s0))).
      { apply parentIsInParentList with child; assumption. }
      pose proof (completeParentsListOrientation partition partition s0 HparentOfPart Htree HpartIsPart HpartIsPart
        HpartIsAnc). congruence.
    - rewrite <-beqAddrFalse in HbeqParts. assert(HpartBisIsPDT: isPDT part s0).
      {
        unfold isPDT. unfold getMappedBlocks in HblockBisMapped. unfold getKSEntries in HblockBisMapped.
        destruct (lookup part (memory s0) beqAddr); try(simpl in *; congruence).
        destruct v; try(simpl in *; congruence). trivial.
      }
      specialize(Hdisjoint part partition HpartBisIsPDT HpartIsPDT HbeqParts).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      unfold getMappedBlocks in *. apply InFilterPresentInList in HblockBisMapped.
      apply InFilterPresentInList in HblockMapped. specialize(Hdisjoint block HblockBisMapped). congruence.
  }
  assert(Hlist1Eq: flat_map (fun p : paddr => getPartitionsAux n p s) childList1
                    = flat_map (fun p : paddr => getPartitionsAux n p s0) childList1).
  {
    clear HgetChildrens0. clear HgetChildrens. induction childList1; simpl in *; try(reflexivity).
    assert(HleftEq: getPartitionsAux n a s = getPartitionsAux n a s0).
    {
      assert(Htmp1: a = a \/ In a (childList1 ++ childList2)) by (left; reflexivity).
      assert(Htmp2: a = a \/ In a childList1) by (left; reflexivity). specialize(HchildrenAreNotPart a Htmp1).
      specialize(Hsh1NotInList1 a Htmp2). destruct HchildrenAreNotPart as (HaIsPart & _).
      apply getPartitionsAuxEqSHENotInList with block; try(assumption).
      - unfold isSHE. rewrite HlookupSh1. trivial.
      - apply partitionsArePDT; assumption.
    }
    rewrite HleftEq. f_equal. apply IHchildList1.
    - intros child Hchild. apply HchildrenAreNotPart. right. assumption.
    - intros child Hchild. apply Hsh1NotInList1. right. assumption.
  }
  assert(Hlist2Eq: flat_map (fun p : paddr => getPartitionsAux n p s) childList2
                    = flat_map (fun p : paddr => getPartitionsAux n p s0) childList2).
  {
    clear HgetChildrens0. clear HgetChildrens. induction childList2; simpl in *; try(reflexivity).
    assert(HleftEq: getPartitionsAux n a s = getPartitionsAux n a s0).
    {
      assert(Htmp1: In a (childList1 ++ a :: childList2)) by (apply in_or_app; right; simpl; left; reflexivity).
      assert(Htmp2: a = a \/ In a childList2) by (left; reflexivity). specialize(HchildrenAreNotPart a Htmp1).
      specialize(Hsh1NotInList2 a Htmp2). destruct HchildrenAreNotPart as (HaIsPart & _).
      apply getPartitionsAuxEqSHENotInList with block; try(assumption).
      - unfold isSHE. rewrite HlookupSh1. trivial.
      - apply partitionsArePDT; assumption.
    }
    rewrite HleftEq. f_equal. apply IHchildList2.
    - intros child Hchild. apply HchildrenAreNotPart. apply in_or_app. simpl. apply in_app_or in Hchild. intuition.
    - intros child Hchild. apply Hsh1NotInList2. right. assumption.
  }
  rewrite Hlist1Eq. rewrite Hlist2Eq. f_equal. destruct n; simpl in *; try(lia). rewrite HgetChildrenNew. simpl.
  reflexivity.
- rewrite <-beqAddrFalse in HbeqPartDesc. destruct Hdesc as [Hcontra | Hdesc]; try(exfalso; congruence).
  assert(HchildrenEq: getChildren partition s = getChildren partition s0).
  {
    unfold s. apply getChildrenEqSHENotInList with block; try(assumption).
    - unfold isSHE. rewrite HlookupSh1. trivial.
    - intros blockBis HblockBisMapped Hcontra.
      assert(HblocksEq: blockBis = block).
      {
        destruct (beqAddr blockBis block) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
        rewrite <-beqAddrFalse in HbeqBlocks. unfold sh1entryAddr in *.
        destruct (lookup blockBis (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
        destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence). subst sh1entryaddr.
        unfold nullAddrExists in *. unfold isPADDR in *.
        unfold CPaddr in Hcontra. unfold CPaddr in HlookupSh1. destruct (le_dec (block + sh1offset) maxAddr).
        - destruct (le_dec (blockBis + sh1offset) maxAddr).
          + injection Hcontra as Hcontra. apply Nat.add_cancel_r in Hcontra. apply paddrEqNatEqEquiv in Hcontra.
            congruence.
          + rewrite Hcontra in *.
            assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockBis + sh1offset) n0 |} = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
        - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n0 |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      }
      subst blockBis. assert(HdescIsPDT: isPDT descPart s0).
      {
        unfold isPDT. unfold getMappedBlocks in HblockMapped. unfold getKSEntries in HblockMapped.
        destruct (lookup descPart (memory s0) beqAddr); try(simpl in *; congruence).
        destruct v; try(simpl in *; congruence). trivial.
      }
      specialize(Hdisjoint partition descPart HpartIsPDT HdescIsPDT HbeqPartDesc).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      unfold getMappedBlocks in *. apply InFilterPresentInList in HblockBisMapped.
      apply InFilterPresentInList in HblockMapped. specialize(Hdisjoint block HblockBisMapped). congruence.
  }
  rewrite HchildrenEq. clear HchildrenEq. clear HnAboveLen.
  assert(Hrec: exists list1 list2,
          flat_map (fun p : paddr => getPartitionsAux n p s0) (getChildren partition s0) = list1 ++ list2
          /\ flat_map (fun p : paddr => getPartitionsAux n p s) (getChildren partition s0)
              = list1 ++ startaddr::list2).
  {
    assert(HnoDup: NoDup (getChildren partition s0)).
    { apply noDupGetChildren; assumption. }
    assert(HchildrenAreParts: forall child, In child (getChildren partition s0)
            -> In child (flat_map (fun p : paddr => getPartitionsAux n p s0) (getChildren partition s0))).
    {
      intros child HchildIsChild. clear Hdesc. clear IHn. clear HnoDup. clear HchildrenAreNotPart.
      clear HnoDupTreePartRec. clear HpartNotInSub.
      induction (getChildren partition s0); simpl in *; try(congruence). rewrite length_app in HnAboveLenRec.
      apply in_or_app. destruct HchildIsChild as [HchildIsA | HchildIsChildRec].
      - left. subst a. destruct n; simpl in *; try(lia). left. reflexivity.
      - right. apply IHl; try(assumption). lia.
    }
    clear HpartNotInSub.
    induction (getChildren partition s0); simpl in *; try(exfalso; congruence). rewrite length_app in HnAboveLenRec.
    apply NoDup_cons_iff in HnoDup. destruct HnoDup as (HaNotInList & HnoDupRec).
    (*apply Lib.in_app_or_neg in HpartNotInSub. destruct HpartNotInSub as (HpartNotInSubA & HpartNotInSubRec).*)
    apply Lib.NoDupSplitInclIff in HnoDupTreePartRec.
    destruct HnoDupTreePartRec as ((_ & HnoDupTreePartRecRec) & HdisjointTrees).
    assert(HchildrenArePartsRec: forall child, In child l
            -> In child (flat_map (fun p : paddr => getPartitionsAux n p s0) l)).
    {
      intros child Hchild. assert(Htmp: a = child \/ In child l) by (right; assumption).
      specialize(HchildrenAreParts child Htmp). apply in_app_or in HchildrenAreParts. clear Htmp.
      destruct HchildrenAreParts as [Hcontra | Hres]; try(assumption). exfalso.
      specialize(HdisjointTrees child Hcontra). destruct n; simpl in *; try(congruence). contradict HdisjointTrees.
      clear HnoDupRec. clear HaNotInList. clear HnoDupTreePartRecRec. clear HchildrenAreNotPart. clear Hdesc.
      clear HnAboveLenRec. clear IHl. induction l; simpl in *; try(congruence).
      destruct Hchild; try(left; assumption). right. apply in_or_app. right. apply IHl; assumption.
    }
    (*assert(Htmp: a = a \/ In a l) by (left; reflexivity). specialize(HchildrenAreParts a Htmp).*)
    assert(HnAboveLenRecRec: n > length (flat_map (fun p : paddr => getPartitionsAux n p s0) l)) by lia.
    apply in_app_or in Hdesc. destruct Hdesc as [HdescIsDescOfA | HdescRec].
    - assert(HflatEq: flat_map (fun p : paddr => getPartitionsAux n p s) l
                      = flat_map (fun p : paddr => getPartitionsAux n p s0) l).
      {
        assert(HnAboveLenA: length (getPartitionsAux n a s0) < n) by lia.
        clear HnAboveLenRec. clear IHl. clear HnoDupRec. clear HchildrenAreParts.
        induction l; simpl in *; try(reflexivity). apply not_or_and in HaNotInList.
        rewrite length_app in HnAboveLenRecRec.
        assert(HlenDescA: length (getPartitionsAux n a0 s0) < n) by lia.
        assert(HnAboveLenRecRecRec: n > length (flat_map (fun p : paddr => getPartitionsAux n p s0) l)) by lia.
        clear HnAboveLenRecRec. destruct HaNotInList as (HbeqAs & HaNotInListRec).
        assert(HchildrenAreNotPartRec: forall child, a = child \/ In child l
                -> In child (getPartitions multiplexer s0) /\ partition <> child /\ pdentryParent child partition s0).
        { intros child Hchild. apply HchildrenAreNotPart. intuition. }
        apply Lib.NoDupSplitInclIff in HnoDupTreePartRecRec.
        destruct HnoDupTreePartRecRec as ((_ & HnoDupTreePartRecRec) & HdisjointTreeA0).
        assert(HchildrenArePartsRecRec: forall child, In child l
                -> In child (flat_map (fun p : paddr => getPartitionsAux n p s0) l)).
        {
          intros child Hchild. assert(Htmp: a0 = child \/ In child l) by (right; assumption).
          specialize(HchildrenArePartsRec child Htmp). apply in_app_or in HchildrenArePartsRec.
          destruct HchildrenArePartsRec as [Hcontra | Hres]; try(assumption). exfalso.
          specialize(HdisjointTreeA0 child Hcontra). destruct n; simpl in *; try(congruence).
          contradict HdisjointTreeA0. clear HaNotInListRec. clear Htmp. clear HchildrenAreNotPartRec.
          clear HchildrenAreNotPart. clear HdisjointTrees. clear IHl. clear HnoDupTreePartRecRec.
          induction l; simpl in *; try(congruence).
          destruct Hchild; try(left; assumption). right. apply in_or_app. right. apply IHl; try(assumption).
          rewrite length_app in HnAboveLenRecRecRec. lia.
        }
        assert(Htmp: a = a0 \/ a0 = a0 \/ In a0 l) by (right; left; reflexivity).
        assert(Lib.disjoint (getPartitionsAux n a s0) (flat_map (fun p : paddr => getPartitionsAux n p s0) l)).
        {
          intros part HpartInA. specialize(HdisjointTrees part HpartInA). apply Lib.in_app_or_neg in HdisjointTrees.
          apply HdisjointTrees.
        }
        rewrite IHl; try(assumption). f_equal. unfold s. specialize(HchildrenAreNotPart a0 Htmp).
        destruct HchildrenAreNotPart as (Ha0IsPart & _ & Hparent).
        apply getPartitionsAuxEqSHENotInList with block; try(assumption).
        - unfold isSHE. rewrite HlookupSh1. trivial.
        - intros part HpartIsDescA0 blockBis HblockBisMapped Hcontra.
          assert(HblocksEq: blockBis = block).
          {
            destruct (beqAddr blockBis block) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
            rewrite <-beqAddrFalse in HbeqBlocks. unfold sh1entryAddr in *.
            destruct (lookup blockBis (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr. unfold nullAddrExists in *. unfold isPADDR in *.
            unfold CPaddr in Hcontra. unfold CPaddr in HlookupSh1. destruct (le_dec (block + sh1offset) maxAddr).
            - destruct (le_dec (blockBis + sh1offset) maxAddr).
              + injection Hcontra as Hcontra. apply Nat.add_cancel_r in Hcontra. apply paddrEqNatEqEquiv in Hcontra.
                congruence.
              + rewrite Hcontra in *.
                assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockBis + sh1offset) n0 |} = nullAddr).
                {
                  unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
                  apply proof_irrelevance.
                }
                rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
            - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n0 |} = nullAddr).
              {
                unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
                apply proof_irrelevance.
              }
              rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
          }
          assert(HdescIsPDT: isPDT descPart s0).
          {
            unfold getMappedBlocks in HblockMapped. unfold getKSEntries in HblockMapped. unfold isPDT.
            destruct (lookup descPart (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          subst blockBis. destruct (beqAddr part descPart) eqn:HbeqParts.
          + rewrite <-DTL.beqAddrTrue in HbeqParts. subst part.
            specialize(HdisjointTrees descPart HdescIsDescOfA). apply Lib.in_app_or_neg in HdisjointTrees.
            destruct HdisjointTrees as (HdescNotDescA0 & _).
            assert(HdescIsDescOfA0: In descPart (getPartitionsAux (S (S (S maxAddr))) a0 s0)).
            {
              unfold completeParentsList in *. apply parentsListGivesPartitionsAux; assumption.
            }
            assert(HgetPartsEq: getPartitionsAux (S (S (S maxAddr))) a0 s0 = getPartitionsAux n a0 s0).
            {
              apply getPartitionsEndAny; try(assumption). lia.
            }
            rewrite HgetPartsEq in *. congruence.
          + rewrite <-beqAddrFalse in HbeqParts. assert(HpartBisIsPDT: isPDT part s0).
            {
              unfold getMappedBlocks in HblockBisMapped. unfold getKSEntries in HblockBisMapped. unfold isPDT.
              destruct (lookup part (memory s0) beqAddr); try(simpl in *; congruence).
              destruct v; try(simpl in *; congruence). trivial.
            }
            specialize(Hdisjoint part descPart HpartBisIsPDT HdescIsPDT HbeqParts).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            unfold getMappedBlocks in *. apply InFilterPresentInList in HblockBisMapped.
            apply InFilterPresentInList in HblockMapped. specialize(Hdisjoint block HblockBisMapped). congruence.
        - apply partitionsArePDT; assumption.
      }
      rewrite HflatEq.
      assert(HgetPartsA: exists list1 list2, getPartitionsAux n a s0 = list1 ++ list2
              /\ getPartitionsAux n a s = list1 ++ startaddr :: list2).
      {
        assert(Htmp: a = a \/ In a l) by (left; reflexivity). specialize(HchildrenAreNotPart a Htmp).
        destruct HchildrenAreNotPart as (HaIsPart & _ & HparentPart).
        apply IHn; try(assumption); try(lia).
        - apply partitionsArePDT; assumption.
        - exists descPart. split; try(split); assumption.
        - assert(HnoDupTreeA: NoDup (getPartitionsAux (maxAddr + 2) a s0)).
          {
            unfold noDupPartitionTree in *. unfold getPartitions in HnoDupTree.
            apply noDupPartitionTreeRecAux with multiplexer; try(assumption).
            pose proof (lengthNoDupPartitions (getPartitionsAux (maxAddr + 2) multiplexer s0) HnoDupTree). lia.
          }
          apply noDupGetPartitionsAuxImpl with (maxAddr + 2); try(assumption). lia.
      }
      destruct HgetPartsA as [list1A [list2A (HgetPartsAs0 & HgetPartsAs)]]. exists list1A.
      exists (list2A ++ flat_map (fun p : paddr => getPartitionsAux n p s0) l). rewrite HgetPartsAs0.
      rewrite HgetPartsAs. split.
      + apply eq_sym. apply app_assoc.
      + rewrite <-app_assoc. f_equal.
    - assert(HgetPartsAEq: getPartitionsAux n a s = getPartitionsAux n a s0).
      {
        assert(Htmp: a = a \/ In a l) by (left; reflexivity). specialize(HchildrenAreNotPart a Htmp).
        destruct HchildrenAreNotPart as (HaIsPart & _ & HparentA).
        apply getPartitionsAuxEqSHENotInList with block; try(assumption).
        - unfold isSHE. rewrite HlookupSh1. trivial.
        - intros part HaIsAncPart blockBis HblockBisMapped Hcontra.
          assert(HblocksEq: blockBis = block).
          {
            destruct (beqAddr blockBis block) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
            rewrite <-beqAddrFalse in HbeqBlocks. unfold sh1entryAddr in *.
            destruct (lookup blockBis (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
            subst sh1entryaddr. unfold nullAddrExists in *. unfold isPADDR in *.
            unfold CPaddr in Hcontra. unfold CPaddr in HlookupSh1. destruct (le_dec (block + sh1offset) maxAddr).
            - destruct (le_dec (blockBis + sh1offset) maxAddr).
              + injection Hcontra as Hcontra. apply Nat.add_cancel_r in Hcontra. apply paddrEqNatEqEquiv in Hcontra.
                congruence.
              + rewrite Hcontra in *.
                assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockBis + sh1offset) n0 |} = nullAddr).
                {
                  unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
                  apply proof_irrelevance.
                }
                rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
            - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n0 |} = nullAddr).
              {
                unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
                apply proof_irrelevance.
              }
              rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
          }
          assert(HdescIsPDT: isPDT descPart s0).
          {
            unfold getMappedBlocks in HblockMapped. unfold getKSEntries in HblockMapped. unfold isPDT.
            destruct (lookup descPart (memory s0) beqAddr); try(simpl in *; congruence).
            destruct v; try(simpl in *; congruence). trivial.
          }
          subst blockBis. destruct (beqAddr part descPart) eqn:HbeqParts.
          + rewrite <-DTL.beqAddrTrue in HbeqParts. subst part.
            assert(HdescIsDescA: In descPart (getPartitionsAux n a s0)).
            {
              assert(HnAboveLenA: n > length (getPartitionsAux n a s0)) by lia. unfold completeParentsList in *.
              assert(HltNMaxRec: n < S (S (S maxAddr))) by lia.
              assert(HgetPartsEqA: getPartitionsAux (S (S (S maxAddr))) a s0 = getPartitionsAux n a s0).
              { apply getPartitionsEndAny; assumption. }
              rewrite <-HgetPartsEqA. apply parentsListGivesPartitionsAux; assumption.
            }
            specialize(HdisjointTrees descPart HdescIsDescA). congruence.
          + rewrite <-beqAddrFalse in HbeqParts. assert(HpartBisIsPDT: isPDT part s0).
            {
              unfold getMappedBlocks in HblockBisMapped. unfold getKSEntries in HblockBisMapped. unfold isPDT.
              destruct (lookup part (memory s0) beqAddr); try(simpl in *; congruence).
              destruct v; try(simpl in *; congruence). trivial.
            }
            specialize(Hdisjoint part descPart HpartBisIsPDT HdescIsPDT HbeqParts).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            unfold getMappedBlocks in *. apply InFilterPresentInList in HblockBisMapped.
            apply InFilterPresentInList in HblockMapped. specialize(Hdisjoint block HblockBisMapped). congruence.
        - unfold pdentryParent in *. unfold isPDT. destruct (lookup a (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
      }
      rewrite HgetPartsAEq.
      assert(HchildrenAreNotPartRec: forall child, In child l
              -> In child (getPartitions multiplexer s0) /\ partition <> child /\ pdentryParent child partition s0).
      { intros child HchildInL. apply HchildrenAreNotPart. right. assumption. }
      specialize(IHl HdescRec HnoDupTreePartRecRec HchildrenAreNotPartRec HnAboveLenRecRec HnoDupRec
        HchildrenArePartsRec). destruct IHl as [list1 [list2 (HlistsEqs0 & HlistsEqs)]].
      exists (getPartitionsAux n a s0 ++ list1). exists list2. rewrite HlistsEqs0. rewrite HlistsEqs. split.
      + apply app_assoc.
      + apply app_assoc.
  }
  destruct Hrec as [list1 [list2 (HlistsEqs0 & HlistsEqs)]]. exists (partition::list1). exists list2.
  rewrite HlistsEqs0. rewrite HlistsEqs. split.
  + apply app_comm_cons.
  + apply app_comm_cons.
Qed.

(* DUP *)
Lemma getPartitionsEqSHEPDflagTrueVal partition block blocksPart startaddr sh1entryaddr newEntry sh1entry0 s0:
nullAddrExists s0
-> noDupMappedBlocksList s0
-> parentOfPartitionIsPartition s0
-> isParent s0
-> isChild s0
-> partitionTreeIsTree s0
-> multiplexerIsPDT s0
-> noDupPartitionTree s0
-> DisjointKSEntries s0
-> noDupMappedPaddrList s0
-> wellFormedBlock s0
-> lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry0)
-> sh1entryAddr block sh1entryaddr s0
-> bentryStartAddr block startaddr s0
-> In block (getMappedBlocks blocksPart s0)
-> In blocksPart (getPartitions multiplexer s0)
-> PDflag newEntry = true
-> PDflag sh1entry0 = false
-> PDTIfPDFlag s0
-> noDupPartitionTree s0
-> getChildren startaddr
  {|
    currentPartition := currentPartition s0;
    memory := add sh1entryaddr (SHE newEntry) (memory s0) beqAddr
  |} = []
-> In partition (blocksPart:: filterOptionPaddr (completeParentsList blocksPart s0))
-> isPDT partition s0
-> In partition (getPartitions multiplexer s0)
-> exists list1 list2, getPartitions partition s0 = list1 ++ list2
    /\ getPartitions partition {|
						currentPartition := currentPartition s0;
						memory := add sh1entryaddr (SHE newEntry)
            (memory s0) beqAddr |} = list1 ++ (startaddr::list2).
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
intros Hnull HnoDupMapped HparentOfPart HisParent HisChild Htree HmultIsPDT HnoDupTree HdisjointKS HnoDupUsed
  HwellFormed HlookupSh1 Hsh1 Hstart HblockMapped HbloksPartIsPart HPDflag HancPDflag HPDTIfPDflags0 HnoDups0
  HgetChildrenNew HpartIsAncestor HPDTs0 HpartIsPart. assert(HnoDupTreeCopy: noDupPartitionTree s0) by assumption.
unfold noDupPartitionTree in HnoDupTree. unfold getPartitions in HnoDupTree. unfold completeParentsList in *.
replace (maxAddr + 2) with (S (S maxAddr)) in *; try(lia).
assert(HnoDupPart: NoDup (getPartitionsAux (maxAddr + 2) partition s0)).
{
  pose proof (noDupPartitionTreeRec partition s0 HnoDupTreeCopy HpartIsPart). unfold getPartitions in *. assumption.
}
apply getPartitionsAuxEqSHEPDflagTrueVal with block sh1entry0; try(assumption); try(lia).
- pose proof (lengthNoDupPartitions (getPartitionsAux (maxAddr + 2) partition s0) HnoDupPart). lia.
- exists blocksPart. split; try(split); try(assumption).
  replace (completeParentsListRec (S (S maxAddr)) blocksPart s0) with (completeParentsList blocksPart s0) in *;
    try(simpl; reflexivity).
  replace (getPartitionsAux (maxAddr + 2) partition s0) with (getPartitions partition s0);
    try(simpl; reflexivity). apply parentsListGivesPartitions; assumption.
Qed.

Lemma parentsListToRootIsCompleteAux n parentsList partition s:
isParentsList s parentsList partition
-> length parentsList <= n
-> constantRootPartM = last parentsList partition
-> parentsList = filterOptionPaddr(completeParentsListRec n partition s).
Proof.
revert n partition. induction parentsList; simpl.
- intros. subst partition. destruct n; simpl; try(reflexivity). rewrite beqAddrTrue.
  destruct (lookup constantRootPartM (memory s) beqAddr); try(simpl; reflexivity). destruct v; simpl; reflexivity.
- intros n partition HparentsList Hlen Hlast.
  destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  destruct HparentsList as (HbeqPartRoot & [pdentry (HlookupPart & HaIsParent)] & HparentsListRec).
  assert(HlenBis: length parentsList <= n - 1) by lia.
  assert(HlastRec: constantRootPartM = last parentsList a).
  {
    destruct parentsList; try(assumption). apply lastNotEmpty with partition; assumption.
  }
  specialize(IHparentsList (n-1) a HparentsListRec HlenBis HlastRec). replace n with (S (n-1)); try(lia). simpl.
  rewrite HlookupPart. rewrite beqAddrFalse in HbeqPartRoot. rewrite HbeqPartRoot. simpl. rewrite <-HaIsParent.
  rewrite <-IHparentsList. reflexivity.
Qed.

Lemma parentsListToRootIsComplete parentsList partition s:
partitionTreeIsTree s
-> parentOfPartitionIsPartition s
-> isParentsList s parentsList partition
-> constantRootPartM = last parentsList partition
-> parentsList = filterOptionPaddr(completeParentsList partition s).
Proof.
intros Htree HparentOfPart HparentsList Hlast. unfold completeParentsList.
apply parentsListToRootIsCompleteAux; try(assumption).
pose proof (parentOfPartNotInParentsListsTail partition parentsList s Htree HparentOfPart HparentsList) as HnoDup.
apply lengthNoDupPartitions in HnoDup. lia.
Qed.

Lemma addrInAccessibleMappedIsAccessibleInBlock partition addr s:
In addr (getAccessibleMappedPaddr partition s) ->
exists block, In addr (getAllPaddrAux [block] s) /\ In block (getMappedBlocks partition s)
  /\ bentryAFlag block true s.
Proof.
intros HinAccMapped. unfold getAccessibleMappedPaddr in *. unfold getAccessibleMappedBlocks in *.
assert(HPDT: isPDT partition s).
{
  unfold isPDT. destruct (lookup partition (memory s) beqAddr); intuition.
	destruct v ; intuition.
}
apply isPDTLookupEq in HPDT. destruct HPDT as [pdentry HlookupPart]. rewrite HlookupPart in *.
induction (getMappedBlocks partition s); simpl in *; try(exfalso; congruence).
destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(specialize(IHl HinAccMapped); destruct IHl as [block
  (HaddrInBlock & HblockInList & HAFlag)]; exists block; split; try(split); try(assumption); right; assumption).
destruct v; try(specialize(IHl HinAccMapped); destruct IHl as [block (HaddrInBlock & HblockInList & HAFlag)];
  exists block; split; try(split); try(assumption); right; assumption).
destruct (accessible b) eqn:Haccess; try(specialize(IHl HinAccMapped); destruct IHl as [block (HaddrInBlock &
  HblockInList & HAFlag)]; exists block; split; try(split); try(assumption); right; assumption). simpl in *.
rewrite HlookupA in *. apply in_app_or in HinAccMapped.
destruct HinAccMapped as [HinBlock | HinAccMapped]; try(specialize(IHl HinAccMapped); destruct IHl as [block
  (HaddrInBlock & HblockInList & HAFlag)]; exists block; split; try(split); try(assumption); right; assumption).
exists a. unfold bentryAFlag. rewrite HlookupA. rewrite app_nil_r. split. assumption. split. left. reflexivity.
apply eq_sym. assumption.
Qed.

Lemma accessAncestorMeansAllDescAccess n addr blockAnc blockDesc partAnc partDesc s:
isChild s
-> parentOfPartitionIsPartition s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> childsBlocksPropsInParent s
-> noDupMappedPaddrList s
-> In addr (getAllPaddrAux [blockAnc] s)
-> In blockAnc (getMappedBlocks partAnc s)
-> bentryAFlag blockAnc true s
-> In partDesc (getPartitions multiplexer s)
-> (forall parent child addr,
         In child (partDesc::filterOptionPaddr (completeParentsListRec n partDesc s)) ->
         In parent (getPartitions multiplexer s) ->
         In child (getChildren parent s) ->
         In addr (getAccessibleMappedPaddr parent s) ->
         In addr (getMappedPaddr child s) -> In addr (getAccessibleMappedPaddr child s))
-> In addr (getAllPaddrAux [blockDesc] s)
-> In blockDesc (getMappedBlocks partDesc s)
-> In partAnc (filterOptionPaddr (completeParentsListRec n partDesc s))
-> bentryAFlag blockDesc true s.
Proof.
intros HisChild HparentOfPart HequivBlockParent HchildBlockProps HnoDupUsed HaddrInBlockAnc HblockAncMapped
  HAFlagAnc. revert blockDesc partDesc.
induction n; intros blockDesc partDesc HpartDescIsPart HpartialAccess HaddrInBlockDesc HblockDescMapped HpartAncIsAnc;
  simpl in HpartAncIsAnc; try(exfalso; congruence).
destruct (lookup partDesc (memory s) beqAddr) eqn:HlookupDesc; try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
destruct (beqAddr partDesc constantRootPartM) eqn:HbeqDescRoot; try(simpl in *; exfalso; congruence).
assert(HdescIsChild: In partDesc (getChildren (parent p) s)).
{
  rewrite <-beqAddrFalse in HbeqDescRoot. assert(Hparent: pdentryParent partDesc (parent p) s).
  { unfold pdentryParent. rewrite HlookupDesc. reflexivity. }
  specialize(HisChild partDesc (parent p) HpartDescIsPart Hparent HbeqDescRoot). assumption.
}
assert(HPFlagDesc: bentryPFlag blockDesc true s).
{
  apply mappedBlockIsBE in HblockDescMapped. destruct HblockDescMapped as [bentry (HlookupBlockDesc & Hpresent)].
  unfold bentryPFlag. rewrite HlookupBlockDesc. apply eq_sym. assumption.
}
assert(HparentIsPart: In (parent p) (getPartitions multiplexer s)).
{
  specialize(HparentOfPart partDesc p HlookupDesc). destruct HparentOfPart as (HparentIsPart & _).
  rewrite <-beqAddrFalse in *. specialize(HparentIsPart HbeqDescRoot). apply HparentIsPart.
}
assert(HlookupBlockDesc: exists bentry, lookup blockDesc (memory s) beqAddr = Some(BE bentry)).
{
  unfold bentryPFlag in *. destruct (lookup blockDesc (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. reflexivity.
}
destruct HlookupBlockDesc as [bentry HlookupBlockDesc].
assert(HstartDesc: bentryStartAddr blockDesc (startAddr (blockrange bentry)) s).
{ apply lookupBEntryStartAddr. assumption. }
assert(HendDesc: bentryEndAddr blockDesc (endAddr (blockrange bentry)) s).
{ apply lookupBEntryEndAddr. assumption. }
specialize(HequivBlockParent (parent p) partDesc blockDesc (startAddr (blockrange bentry))
  (endAddr (blockrange bentry)) HparentIsPart HdescIsChild HblockDescMapped HstartDesc HendDesc HPFlagDesc).
destruct HequivBlockParent as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & HendParent &
  HlebStart & HgebEnd)]]].
assert(HdescIsDesc: In partDesc (partDesc::filterOptionPaddr (completeParentsListRec (S n) partDesc s))).
{ simpl. left. reflexivity. }
assert(HaddrInDesc: In addr (getMappedPaddr partDesc s)).
{ apply addrInBlockIsMapped with blockDesc; assumption. }
assert(HaddrInParent: In addr (getAllPaddrAux [blockParent] s)).
{
  simpl in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockDesc in *.
  destruct (lookup blockParent (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  subst startParent. subst endParent. rewrite app_nil_r in HaddrInBlockDesc. rewrite app_nil_r.
  apply getAllPaddrBlockInclRev in HaddrInBlockDesc. destruct HaddrInBlockDesc as (HlebStartAddr & HleAddrEnd & _).
  apply getAllPaddrBlockIncl; lia.
}
assert(HpartialAccessRec: forall pdparent child addr,
          In child ((parent p) :: filterOptionPaddr (completeParentsListRec n (parent p) s)) ->
          In pdparent (getPartitions multiplexer s) ->
          In child (getChildren pdparent s) ->
          In addr (getAccessibleMappedPaddr pdparent s) ->
          In addr (getMappedPaddr child s) -> In addr (getAccessibleMappedPaddr child s)).
{
  intros pdparent child addrBis HchildIsAnc HpdparentIsPart HchildIsChild HaddrAccMappedPdparent HaddrMappedChild.
  assert(HchildIsAncRec: In child (partDesc :: filterOptionPaddr (completeParentsListRec (S n) partDesc s))).
  {
    simpl. right. rewrite HlookupDesc. rewrite HbeqDescRoot. simpl in *. assumption.
  }
  specialize(HpartialAccess pdparent child addrBis HchildIsAncRec HpdparentIsPart HchildIsChild HaddrAccMappedPdparent
    HaddrMappedChild). assumption.
}
specialize(IHn blockParent (parent p) HparentIsPart HpartialAccessRec HaddrInParent HblockParentMapped).
simpl in HpartAncIsAnc. destruct HpartAncIsAnc as [HpartIsParent | HpartAncIsAncRec].
- subst partAnc. assert(HblocksEq: blockParent = blockAnc).
  {
    destruct (beqAddr blockParent blockAnc) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
    rewrite <-beqAddrFalse in *. assert(HparentIsPDT: isPDT (parent p) s).
    {
      unfold getChildren in *. unfold isPDT.
      destruct (lookup (parent p) (memory s) beqAddr); try(simpl in *; congruence).
      destruct v; try(simpl in *; congruence). trivial.
    }
    pose proof (DisjointPaddrInPart (parent p) blockParent blockAnc addr s HnoDupUsed HparentIsPDT HblockParentMapped
      HblockAncMapped HbeqBlocks HaddrInParent). congruence.
  }
  subst blockAnc. assert(HaddrAccMappedParent: In addr (getAccessibleMappedPaddr (parent p) s)).
  {
    apply addrInAccessibleBlockIsAccessibleMapped with blockParent; assumption.
  }
  specialize(HpartialAccess (parent p) partDesc addr HdescIsDesc HparentIsPart HdescIsChild HaddrAccMappedParent
    HaddrInDesc). apply addrInAccessibleMappedIsAccessible with partDesc addr; assumption.
- specialize(IHn HpartAncIsAncRec).
  assert(HaddrAccMappedParent: In addr (getAccessibleMappedPaddr (parent p) s)).
  { apply addrInAccessibleBlockIsAccessibleMapped with blockParent; assumption. }
  specialize(HpartialAccess (parent p) partDesc addr HdescIsDesc HparentIsPart HdescIsChild HaddrAccMappedParent
    HaddrInDesc). apply addrInAccessibleMappedIsAccessible with partDesc addr; assumption.
Qed.

Lemma accessibleAncestorHasSameBoundsAux n addr blockAnc blockDesc startaddr endaddr partAnc partDesc s:
isChild s
-> parentOfPartitionIsPartition s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> childsBlocksPropsInParent s
-> noDupMappedPaddrList s
-> In addr (getAllPaddrAux [blockAnc] s)
-> In blockAnc (getMappedBlocks partAnc s)
-> bentryAFlag blockAnc true s
-> In partDesc (getPartitions multiplexer s)
-> (forall parent child addrBis,
      In child (partDesc :: filterOptionPaddr (completeParentsListRec n partDesc s)) ->
      In parent (getPartitions multiplexer s) ->
      In child (getChildren parent s) ->
      In addrBis (getAccessibleMappedPaddr parent s) ->
      In addrBis (getMappedPaddr child s) -> In addrBis (getAccessibleMappedPaddr child s))
-> In addr (getAllPaddrAux [blockDesc] s)
-> In blockDesc (getMappedBlocks partDesc s)
-> In partAnc (filterOptionPaddr (completeParentsListRec n partDesc s))
-> bentryStartAddr blockDesc startaddr s
-> bentryEndAddr blockDesc endaddr s
-> bentryStartAddr blockAnc startaddr s /\ bentryEndAddr blockAnc endaddr s.
Proof.
intros HisChild HparentOfPart HequivBlockParent HchildBlockProps HnoDupUsed HaddrInBlockAnc HblockAncMapped
  HAFlagAnc. revert blockDesc partDesc.
induction n; intros blockDesc partDesc HpartDescIsPart HpartialAccess HaddrInBlockDesc HblockDescMapped HpartAncIsAnc
  HstartDesc HendDesc; simpl in HpartAncIsAnc; try(exfalso; congruence).
destruct (lookup partDesc (memory s) beqAddr) eqn:HlookupDesc; try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
destruct (beqAddr partDesc constantRootPartM) eqn:HbeqDescRoot; try(simpl in *; exfalso; congruence).
assert(HdescIsChild: In partDesc (getChildren (parent p) s)).
{
  rewrite <-beqAddrFalse in HbeqDescRoot. assert(Hparent: pdentryParent partDesc (parent p) s).
  { unfold pdentryParent. rewrite HlookupDesc. reflexivity. }
  specialize(HisChild partDesc (parent p) HpartDescIsPart Hparent HbeqDescRoot). assumption.
}
assert(HPFlagDesc: bentryPFlag blockDesc true s).
{
  apply mappedBlockIsBE in HblockDescMapped. destruct HblockDescMapped as [bentry (HlookupBlockDesc & Hpresent)].
  unfold bentryPFlag. rewrite HlookupBlockDesc. apply eq_sym. assumption.
}
assert(HparentIsPart: In (parent p) (getPartitions multiplexer s)).
{
  specialize(HparentOfPart partDesc p HlookupDesc). destruct HparentOfPart as (HparentIsPart & _).
  rewrite <-beqAddrFalse in *. specialize(HparentIsPart HbeqDescRoot). apply HparentIsPart.
}
assert(HequivBlockParentCopy: blockInChildHasAtLeastEquivalentBlockInParent s) by assumption.
specialize(HequivBlockParent (parent p) partDesc blockDesc startaddr endaddr HparentIsPart HdescIsChild
  HblockDescMapped HstartDesc HendDesc HPFlagDesc).
destruct HequivBlockParent as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & HendParent &
  HlebStart & HgebEnd)]]].
assert(HPFlagParent: bentryPFlag blockParent true s).
{
  apply mappedBlockIsBE in HblockParentMapped. destruct HblockParentMapped as [bentry (HlookupBlockParent & Hpres)].
  unfold bentryPFlag. rewrite HlookupBlockParent. apply eq_sym. assumption.
}
assert(HchildBlockPropsCopy: childsBlocksPropsInParent s) by assumption.
specialize(HchildBlockProps partDesc (parent p) blockDesc startaddr endaddr blockParent startParent endParent
  HparentIsPart HdescIsChild HblockDescMapped HstartDesc HendDesc HPFlagDesc HblockParentMapped HstartParent
  HendParent HPFlagParent HlebStart HgebEnd).
destruct HchildBlockProps as (_ & _ & _ & Hbounds).
assert(HaddrInParent: In addr (getAllPaddrAux [blockParent] s)).
{
  simpl in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
  destruct (lookup blockDesc (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  subst startaddr. subst endaddr.
  destruct (lookup blockParent (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  subst startParent. subst endParent. rewrite app_nil_r in HaddrInBlockDesc. rewrite app_nil_r.
  apply getAllPaddrBlockInclRev in HaddrInBlockDesc. destruct HaddrInBlockDesc as (HlebStartAddr & HleAddrEnd & _).
  apply getAllPaddrBlockIncl; lia.
}
assert(HpartialAccessRec: forall pdparent child addr,
          In child ((parent p) :: filterOptionPaddr (completeParentsListRec n (parent p) s)) ->
          In pdparent (getPartitions multiplexer s) ->
          In child (getChildren pdparent s) ->
          In addr (getAccessibleMappedPaddr pdparent s) ->
          In addr (getMappedPaddr child s) -> In addr (getAccessibleMappedPaddr child s)).
{
  intros pdparent child addrBis HchildIsAnc HpdparentIsPart HchildIsChild HaddrAccMappedPdparent HaddrMappedChild.
  assert(HchildIsAncRec: In child (partDesc :: filterOptionPaddr (completeParentsListRec (S n) partDesc s))).
  {
    simpl. right. rewrite HlookupDesc. rewrite HbeqDescRoot. simpl in *. assumption.
  }
  specialize(HpartialAccess pdparent child addrBis HchildIsAncRec HpdparentIsPart HchildIsChild HaddrAccMappedPdparent
    HaddrMappedChild). assumption.
}
specialize(IHn blockParent (parent p) HparentIsPart HpartialAccessRec HaddrInParent HblockParentMapped).
simpl in HpartAncIsAnc. destruct HpartAncIsAnc as [HpartIsParent | HpartAncIsAncRec].
- subst partAnc. assert(HblocksEq: blockParent = blockAnc).
  {
    destruct (beqAddr blockParent blockAnc) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
    rewrite <-beqAddrFalse in *. assert(HparentIsPDT: isPDT (parent p) s).
    {
      unfold getChildren in *. unfold isPDT.
      destruct (lookup (parent p) (memory s) beqAddr); try(simpl in *; congruence).
      destruct v; try(simpl in *; congruence). trivial.
    }
    pose proof (DisjointPaddrInPart (parent p) blockParent blockAnc addr s HnoDupUsed HparentIsPDT HblockParentMapped
      HblockAncMapped HbeqBlocks HaddrInParent). congruence.
  }
  subst blockAnc. assert(startParent = startaddr).
  {
    destruct (beqAddr startParent startaddr) eqn:HbeqStarts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
    rewrite <-beqAddrFalse in *. assert(Hcontra: startParent <> startaddr \/ endParent <> endaddr)
      by (left; assumption). specialize(Hbounds Hcontra). unfold bentryAFlag in *.
    destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  subst startParent. assert(endParent = endaddr).
  {
    destruct (beqAddr endParent endaddr) eqn:HbeqEnds; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
    rewrite <-beqAddrFalse in *. assert(Hcontra: startaddr <> startaddr \/ endParent <> endaddr)
      by (right; assumption). specialize(Hbounds Hcontra). unfold bentryAFlag in *.
    destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  subst endParent. split; assumption.
- assert(HAFlagParent: bentryAFlag blockParent true s).
  {
    apply accessAncestorMeansAllDescAccess with n addr blockAnc partAnc (parent p); assumption.
  }
  assert(startParent = startaddr).
  {
    destruct (beqAddr startParent startaddr) eqn:HbeqStarts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
    rewrite <-beqAddrFalse in *. assert(Hcontra: startParent <> startaddr \/ endParent <> endaddr)
      by (left; assumption). specialize(Hbounds Hcontra). unfold bentryAFlag in *.
    destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  subst startParent. assert(endParent = endaddr).
  {
    destruct (beqAddr endParent endaddr) eqn:HbeqEnds; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
    rewrite <-beqAddrFalse in *. assert(Hcontra: startaddr <> startaddr \/ endParent <> endaddr)
      by (right; assumption). specialize(Hbounds Hcontra). unfold bentryAFlag in *.
    destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  subst endParent. specialize(IHn HpartAncIsAncRec HstartParent HendParent). assumption.
Qed.

Lemma accessibleAncestorHasSameBounds addr blockAnc blockDesc startaddr endaddr partAnc partDesc s:
isChild s
-> parentOfPartitionIsPartition s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> childsBlocksPropsInParent s
-> noDupMappedPaddrList s
-> In addr (getAllPaddrAux [blockAnc] s)
-> In blockAnc (getMappedBlocks partAnc s)
-> bentryAFlag blockAnc true s
-> In partDesc (getPartitions multiplexer s)
-> (forall parent child addrBis,
      In child (partDesc :: filterOptionPaddr (completeParentsList partDesc s)) ->
      In parent (getPartitions multiplexer s) ->
      In child (getChildren parent s) ->
      In addrBis (getAccessibleMappedPaddr parent s) ->
      In addrBis (getMappedPaddr child s) -> In addrBis (getAccessibleMappedPaddr child s))
-> In addr (getAllPaddrAux [blockDesc] s)
-> In blockDesc (getMappedBlocks partDesc s)
-> In partAnc (filterOptionPaddr (completeParentsList partDesc s))
-> bentryStartAddr blockDesc startaddr s
-> bentryEndAddr blockDesc endaddr s
-> bentryStartAddr blockAnc startaddr s /\ bentryEndAddr blockAnc endaddr s.
Proof.
unfold completeParentsList. apply accessibleAncestorHasSameBoundsAux.
Qed.

Lemma parentsListIsInclInCompleteAux n part pdbasepart parentsList s:
In part parentsList
-> isParentsList s parentsList pdbasepart
-> length parentsList < n
-> In part (filterOptionPaddr (completeParentsListRec n pdbasepart s)).
Proof.
revert pdbasepart n. induction parentsList; intros pdbasepart n HpartIsParent HparentsList Hlen; simpl in *;
  try(exfalso; congruence). destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct HparentsList as (HbeqBaseRoot & [pdentryBase (HlookupBase & Hparent)] & HparentsListRec).
assert(HnMinus: exists nminus, n = S nminus).
{ exists (n-1). lia. }
destruct HnMinus as [nminus Hnminus]. rewrite Hnminus in *.
assert(HlenRec: length parentsList < nminus) by lia. simpl. rewrite HlookupBase. rewrite beqAddrFalse in *.
rewrite HbeqBaseRoot. simpl. destruct HpartIsParent as [HaIsPart | HpartIsParentRec].
- subst a. left. apply eq_sym. assumption.
- right. apply IHparentsList; try(assumption). rewrite Hparent in *. assumption.
Qed.

Lemma parentsListIsInclInComplete part pdbasepart parentsList s:
partitionTreeIsTree s
-> parentOfPartitionIsPartition s
-> In part parentsList
-> isParentsList s parentsList pdbasepart
-> In part (filterOptionPaddr (completeParentsList pdbasepart s)).
Proof.
intros Htree HparentOfPart HpartIsParent HparentsList. unfold completeParentsList.
assert(Hlen: length parentsList <= maxAddr + 1).
{
  apply PaddrListBoundedLength. revert HparentsList. apply parentOfPartNotInParentsListsTail; assumption.
}
apply parentsListIsInclInCompleteAux with parentsList; try(assumption); lia.
Qed.

Lemma oppositeCompleteParentsListsImpliesEq pdbasepartition pdparent part s:
parentOfPartitionIsPartition s
-> partitionTreeIsTree s
-> In part (getPartitions multiplexer s)
-> In pdparent (getPartitions multiplexer s)
-> In part (filterOptionPaddr (completeParentsList pdbasepartition s))
-> pdentryParent pdbasepartition pdparent s
-> beqAddr pdbasepartition constantRootPartM = false
-> In pdparent (filterOptionPaddr (completeParentsList part s))
-> part = pdparent.
Proof.
intros HparentOfPart Htree HpartIsPart HparentIsPart HpartIsAncBase Hparent HbeqBaseRoot HparentInAncPart.
apply completeParentsListOrientation in HparentInAncPart; try(assumption). unfold completeParentsList in *.
assert(HparentInAncPartRec: ~ In part (filterOptionPaddr (completeParentsListRec (S maxAddr) pdparent s))).
{
  contradict HparentInAncPart. apply completeParentsListRecN with (S maxAddr); try(assumption); lia.
}
set(succ := S maxAddr). fold succ in HpartIsAncBase. cbn -[succ] in HpartIsAncBase. unfold pdentryParent in *.
destruct (lookup pdbasepartition (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
rewrite HbeqBaseRoot in HpartIsAncBase. cbn -[succ] in HpartIsAncBase. subst succ. subst pdparent. apply eq_sym.
destruct HpartIsAncBase as [Hres | Hcontra]; try(assumption). exfalso; congruence.
Qed.

Lemma boundsOfParentsList parentsList pdbasepartition part1 part2 s:
parentOfPartitionIsPartition s
-> partitionTreeIsTree s
-> parentsList <> []
-> In part1 (getPartitions multiplexer s)
-> isParentsList s parentsList pdbasepartition
-> part2 = last parentsList pdbasepartition
-> In part1 (filterOptionPaddr (completeParentsList pdbasepartition s))
-> In part2 (part1::filterOptionPaddr (completeParentsList part1 s))
-> In part1 parentsList.
Proof.
intros HparentOfPart Htree HparentsListNotEmpty Hpart1IsPart. revert pdbasepartition. induction parentsList; intros
  pdbasepartition HparentsList Hlast Hpart1IsAncBase Hpart2IsAncPart1; try(simpl; congruence).
assert(HlastRec: part2 = last parentsList a) by (apply lastRec with pdbasepartition; assumption). simpl in *.
destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(exfalso; congruence). destruct v; try(exfalso; congruence).
destruct HparentsList as (HbeqBaseRoot & [pdentry (HlookupBase & HaIsParent)] & HparentsListRec).
clear HparentsListNotEmpty.
assert(HparentOfPartCopy: parentOfPartitionIsPartition s) by assumption.
specialize(HparentOfPartCopy pdbasepartition pdentry HlookupBase).
destruct HparentOfPartCopy as (HparentIsPart & _ & HbeqParentBase). specialize(HparentIsPart HbeqBaseRoot).
destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
assert(HparentsListEmpty: parentsList = [] \/ parentsList <> []) by (apply Classical_Prop.classic).
destruct HparentsListEmpty as [HparentsListEmpty | HparentsListNotEmpty].
- subst parentsList. subst a. left. subst part2. apply eq_sym.
  destruct (beqAddr part1 (parent pdentry)) eqn:HbeqPart1Parent; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
  rewrite <-beqAddrFalse in *. destruct Hpart2IsAncPart1 as [Hres | Hcontra]; try(congruence).
  assert(part1 = parent pdentry).
  {
    rewrite beqAddrFalse in *. apply oppositeCompleteParentsListsImpliesEq with pdbasepartition s; try(assumption).
    unfold pdentryParent. rewrite HlookupBase. reflexivity.
  }
  congruence.
- assert(HbeqBasePart2: a <> part2).
  { apply basePartNotLastInParentsLists with parentsList s; assumption. }
  destruct (beqAddr a part1) eqn:HbeqAPart1; try(rewrite <-DTL.beqAddrTrue in HbeqAPart1; left; assumption).
  assert(Hpart1IsAncBaseRec: In part1 (filterOptionPaddr (completeParentsList a s))).
  {
    unfold completeParentsList in *. set(succ := S maxAddr). fold succ in Hpart1IsAncBase.
    cbn -[succ] in Hpart1IsAncBase. rewrite HlookupBase in *. rewrite beqAddrFalse in *. rewrite HbeqBaseRoot in *.
    cbn -[succ] in Hpart1IsAncBase. rewrite <-HaIsParent in *. rewrite <-beqAddrFalse in *.
    destruct Hpart1IsAncBase as [Hcontra | Hres]; try(exfalso; congruence).
    apply completeParentsListRecN with succ; try(assumption); lia.
  }
  specialize(IHparentsList HparentsListNotEmpty a HparentsListRec HlastRec Hpart1IsAncBaseRec Hpart2IsAncPart1).
  right. assumption.
Qed.

Lemma getKSEntriesInStructAuxEqPrepare n kernel (idx: index) s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isKS kernel s0
-> BlocksRangeFromKernelStartIsBE s0
-> idx < kernelStructureEntriesNb
-> getKSEntriesInStructAux n kernel s idx = getKSEntriesInStructAux n kernel s0 idx.
Proof.
intros HlookupSomeEq HkernelIsKS HblockRange. revert idx.
induction n; intros idx HltIdxKernEntries; simpl; try(reflexivity). unfold Paddr.addPaddrIdx.
destruct (le_dec (kernel + idx) maxAddr); try(reflexivity).
specialize(HblockRange kernel idx HkernelIsKS HltIdxKernEntries).
assert(HpaddrEq: {| p := kernel + idx; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 kernel idx l |}
  = CPaddr (kernel+idx)).
{ unfold CPaddr. destruct (le_dec (kernel + idx) maxAddr); try(lia). f_equal. apply proof_irrelevance. }
rewrite HpaddrEq. unfold isBE in HblockRange.
destruct (lookup (CPaddr (kernel + idx)) (memory s0) beqAddr) eqn:HlookupKernIdx; try(exfalso; congruence).
destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupKernIdx.
destruct (indexEq idx zero) eqn:HbeqIdxZero; try(reflexivity). apply beqIdxFalse in HbeqIdxZero.
assert(i idx <> 0).
{
  intro Hcontra. assert(Hcontra2: i idx = i zero).
  { unfold zero. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl. assumption. }
  apply index_eq_i in Hcontra2. congruence.
}
unfold Index.pred. destruct (gt_dec idx 0); try(lia). f_equal. apply IHn. simpl. lia.
Qed.

Lemma getKSEntriesAuxEqPrepare n kernel s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> NextKSOffsetIsPADDR s0
-> NextKSIsKS s0
-> BlocksRangeFromKernelStartIsBE s0
-> nullAddrExists s0
-> isKS kernel s0
-> getKSEntriesAux n kernel s = getKSEntriesAux n kernel s0.
Proof.
intros HlookupSomeEq HnextOffset HnextKS HblockRange Hnull. revert kernel.
induction n; intros kernel HkernIsKS; simpl; try(reflexivity). unfold Paddr.addPaddrIdx.
destruct (le_dec (kernel + nextoffset) maxAddr); try(reflexivity).
set(nextAddr := {| p := kernel + nextoffset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 kernel nextoffset l |}).
assert(Hnext: nextKSAddr kernel nextAddr s0).
{
  unfold nextKSAddr. unfold isKS in *. destruct (lookup kernel (memory s0) beqAddr); try(congruence).
  destruct v; try(congruence). subst nextAddr. unfold CPaddr.
  destruct (le_dec (kernel + nextoffset) maxAddr); try(lia). f_equal. apply proof_irrelevance.
}
specialize(HnextOffset kernel nextAddr HkernIsKS Hnext). destruct HnextOffset as (HnextIsPADDR & HbeqNextNull).
unfold isPADDR in *. destruct (lookup nextAddr (memory s0) beqAddr) eqn:HlookupNext; try(exfalso; congruence).
destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (PADDR p); assumption). rewrite HlookupNext.
assert(HnextKSkern: nextKSentry nextAddr p s0).
{ unfold nextKSentry. rewrite HlookupNext. reflexivity. }
assert(HgetKSStructEq: getKSEntriesInStructAux (maxIdx + 1) kernel s (CIndex 7)
  = getKSEntriesInStructAux (maxIdx + 1) kernel s0 (CIndex 7)).
{
  apply getKSEntriesInStructAuxEqPrepare; try(assumption). unfold CIndex.
  pose proof Constants.maxIdxBiggerThanMinBlock. destruct (le_dec 7 maxIdx); try(lia). cbn. lia.
}
rewrite HgetKSStructEq. destruct (beqAddr p nullAddr) eqn:HbeqPNull.
- rewrite <-DTL.beqAddrTrue in HbeqPNull. subst p. unfold nullAddrExists in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s0) beqAddr) eqn:HlookupNull; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (PADDR p); assumption). rewrite HlookupNull.
  reflexivity.
- rewrite <-beqAddrFalse in HbeqPNull. specialize(HnextKS kernel nextAddr p HkernIsKS Hnext HnextKSkern HbeqPNull).
  unfold isKS in *. destruct (lookup p (memory s0) beqAddr) eqn:HlookupNextKS; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupNextKS.
  f_equal. apply IHn; try(assumption). rewrite HlookupNextKS. assumption.
Qed.

Lemma KSentriesStructAreBEAux n addr kernel idx s:
In addr (filterOptionPaddr (getKSEntriesInStructAux n kernel s idx))
-> isBE addr s.
Proof.
revert idx. induction n; simpl; intros idx HaddrInList; try(exfalso; congruence).
destruct (Paddr.addPaddrIdx kernel idx); try(simpl in *; exfalso; congruence).
destruct (lookup p (memory s) beqAddr) eqn:HlookupP; try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence). destruct (indexEq idx zero); simpl in *.
- destruct HaddrInList as [HaddrInList | Hcontra]; try(exfalso; congruence). subst p. unfold isBE. rewrite HlookupP.
  trivial.
- destruct (Index.pred idx); try(simpl in *; exfalso; congruence). simpl in HaddrInList.
  destruct HaddrInList as [HaddrIsFirst | Hrec].
  + subst p. unfold isBE. rewrite HlookupP. trivial.
  + apply IHn with i. assumption.
Qed.

Lemma KSentriesAreBEAux n addr kernel s:
In addr (filterOptionPaddr (getKSEntriesAux n kernel s))
-> isBE addr s.
Proof.
revert kernel. induction n; simpl; intros kernel HaddrInList; try(exfalso; congruence).
destruct (Paddr.addPaddrIdx kernel nextoffset); try(simpl in *; exfalso; congruence).
destruct (lookup p (memory s) beqAddr); try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
destruct (lookup p0 (memory s) beqAddr); try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
- rewrite filterOptionPaddrSplit in HaddrInList. apply in_app_or in HaddrInList.
  destruct HaddrInList as [HaddrInFirst | Hrec].
  + revert HaddrInFirst. apply KSentriesStructAreBEAux.
  + revert Hrec. apply IHn.
- destruct (beqAddr p0 nullAddr); try(simpl in *; exfalso; congruence). revert HaddrInList.
  apply KSentriesStructAreBEAux.
Qed.

Lemma KSentriesAreBE partition s addr:
In addr (filterOptionPaddr (getKSEntries partition s))
-> isBE addr s.
Proof.
intro HaddrInList. unfold getKSEntries in *.
destruct (lookup partition (memory s) beqAddr); try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
destruct (beqAddr (structure p) nullAddr); try(simpl in *; exfalso; congruence). revert HaddrInList.
apply KSentriesAreBEAux.
Qed.

Lemma getFreeSlotsListAuxEqPrepare n block nbleft s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> wellFormedFreeSlotsList (getFreeSlotsListRec n block s0 nbleft) <> False
-> getFreeSlotsListRec n block s nbleft = getFreeSlotsListRec n block s0 nbleft.
Proof.
intro HlookupSomeEq. rewrite FreeSlotsListRec_unroll. rewrite FreeSlotsListRec_unroll. revert block nbleft.
induction n; intros block nbleft HwellFormed; simpl; simpl in HwellFormed; try(reflexivity).
destruct (lookup block (memory s0) beqAddr) eqn:HlookupBlock; try(simpl in HwellFormed; exfalso; congruence).
rewrite HlookupSomeEq; try(exists v; assumption). rewrite HlookupBlock.
destruct v; try(simpl in HwellFormed; exfalso; congruence); try(reflexivity).
destruct (Index.pred nbleft); try(reflexivity). f_equal. rewrite FreeSlotsListRec_unroll.
rewrite FreeSlotsListRec_unroll. apply IHn. simpl in HwellFormed. rewrite FreeSlotsListRec_unroll in HwellFormed.
assumption.
Qed.

Lemma getPDsEqPrepare blockList s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> wellFormedFstShadowIfBlockEntry s0
-> (forall addr, In addr blockList -> isBE addr s0)
-> getPDs blockList s = getPDs blockList s0.
Proof.
intros HlookupSomeEq HwellFormedSh1. unfold getPDs.
induction blockList as [ | el blockList]; intro HblocksAreBE; simpl; try(reflexivity).
assert(HblocksAreBERec: forall addr, In addr blockList -> isBE addr s0).
{
  intros addr HaddrInList. apply HblocksAreBE. simpl. right. assumption.
}
specialize(IHblockList HblocksAreBERec). assert(HelIsEl: In el (el :: blockList)) by (simpl; left; reflexivity).
specialize(HblocksAreBE el HelIsEl). unfold isBE in HblocksAreBE.
assert(HfilterEq: childFilter s el = childFilter s0 el).
{
  unfold childFilter. specialize(HwellFormedSh1 el HblocksAreBE). unfold isSHE in HwellFormedSh1.
  destruct (lookup el (memory s0) beqAddr) eqn:HlookupEl; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupEl.
  destruct (Paddr.addPaddrIdx el sh1offset) eqn:Hadd; try(reflexivity). unfold Paddr.addPaddrIdx in Hadd.
  destruct (le_dec (el + sh1offset) maxAddr); try(exfalso; congruence). injection Hadd as Hadd.
  assert(Hp: p = CPaddr (el + sh1offset)).
  { unfold CPaddr. destruct (le_dec (el + sh1offset) maxAddr); try(lia). subst p. f_equal. apply proof_irrelevance. }
  rewrite Hp. destruct (lookup (CPaddr (el+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (SHE s1); assumption). rewrite HlookupSh1.
  reflexivity.
}
rewrite HfilterEq. destruct (childFilter s0 el); try(assumption). simpl. rewrite IHblockList. f_equal.
destruct (lookup el (memory s0) beqAddr) eqn:HlookupEl; try(exfalso; congruence).
destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupEl.
reflexivity.
Qed.

Lemma getPartsAuxEqPrepare n root s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> (forall partition, isPDT partition s0 -> getChildren partition s = getChildren partition s0)
-> PDTIfPDFlag s0
-> isPDT root s0
-> getPartitionsAux n root s = getPartitionsAux n root s0.
Proof.
intros HlookupSomeEq HgetChildrenEq HPDTIfPDFlag. revert root.
induction n; intros root HrootIsPDT; simpl; try(reflexivity).
f_equal. rewrite HgetChildrenEq; try(assumption).
assert(HchildrenArePDT: forall child, In child (getChildren root s0) -> isPDT child s0).
{
  intros child HchildIsChild. apply childrenArePDT with root; assumption.
}
induction (getChildren root s0) as [ | el childList]; simpl; try(reflexivity). f_equal.
- apply IHn. apply HchildrenArePDT. simpl. left. reflexivity.
- apply IHchildList. intros child HchildInList. apply HchildrenArePDT. simpl. right. assumption.
Qed.

Lemma getPartsEqPrepare root s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> (forall partition, isPDT partition s0 -> getChildren partition s = getChildren partition s0)
-> PDTIfPDFlag s0
-> isPDT root s0
-> getPartitions root s = getPartitions root s0.
Proof.
unfold getPartitions. apply getPartsAuxEqPrepare.
Qed.

Lemma getConfigBlocksAuxEqPrepare n kernel nbleft s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> NextKSOffsetIsPADDR s0
-> NextKSIsKS s0
-> nullAddrExists s0
-> (isKS kernel s0 \/ isPADDR kernel s0)
-> getConfigBlocksAux n kernel s nbleft = getConfigBlocksAux n kernel s0 nbleft.
Proof.
intros HlookupSomeEq HnextOffset HnextKS Hnull. revert kernel nbleft.
induction n; intros kernel nbleft HkernProps; simpl; try(reflexivity).
assert(HpropsOr: isPADDR kernel s0 \/ ~ isPADDR kernel s0) by (apply classic).
destruct HpropsOr as [HaddrIsPADDR | HkernIsNotPADDR].
- unfold isPADDR in HaddrIsPADDR.
  destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupAddr; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (PADDR p); assumption). rewrite HlookupAddr.
  reflexivity.
- destruct HkernProps as [HkernIsKS | Hcontra]; try(exfalso; congruence).
  specialize(HnextOffset kernel (CPaddr (kernel+nextoffset)) HkernIsKS). unfold isKS in HkernIsKS.
  assert(HkernIsKSCopy: isKS kernel s0) by assumption.
  destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupKern.
  assert(Hnext: nextKSAddr kernel (CPaddr (kernel+nextoffset)) s0).
  { unfold nextKSAddr. rewrite HlookupKern. reflexivity. }
  specialize(HnextOffset Hnext). destruct HnextOffset as (HnextOffset & HbeqNextNull). unfold Paddr.addPaddrIdx.
  destruct (le_dec (kernel + nextoffset) maxAddr); try(reflexivity).
  assert(HnextEq: {| p := kernel + nextoffset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 kernel nextoffset l |}
    = CPaddr (kernel + nextoffset)).
  { unfold CPaddr. destruct (le_dec (kernel + nextoffset) maxAddr); try(lia). f_equal. apply proof_irrelevance. }
  rewrite HnextEq. unfold isPADDR in HnextOffset.
  destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr) eqn:HlookupNext; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (PADDR p); assumption). rewrite HlookupNext.
  destruct (Index.pred nbleft); try(reflexivity). f_equal. apply IHn.
  assert(HnextKSAddr: nextKSentry (CPaddr (kernel + nextoffset)) p s0).
  { unfold nextKSentry. rewrite HlookupNext. reflexivity. }
  specialize(HnextKS kernel (CPaddr (kernel+nextoffset)) p HkernIsKSCopy Hnext HnextKSAddr).
  destruct (beqAddr p nullAddr) eqn:HbeqPNull.
  + rewrite <-DTL.beqAddrTrue in HbeqPNull. subst p. unfold nullAddrExists in *. right. assumption.
  + rewrite <-DTL.beqAddrFalse in HbeqPNull. left. apply HnextKS. assumption.
Qed.

Lemma getConfigBlocksEqPrepare part s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> NextKSOffsetIsPADDR s0
-> NextKSIsKS s0
-> nullAddrExists s0
-> StructurePointerIsKS s0
-> isPDT part s0
-> getConfigBlocks part s = getConfigBlocks part s0.
Proof.
intros HlookupSomeEq HnextOffset HnextKS Hnull Hstruct HpartIsPDT. unfold getConfigBlocks. unfold isPDT in HpartIsPDT.
destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (PDT p); assumption). rewrite HlookupPart.
specialize(Hstruct part p HlookupPart). f_equal. apply getConfigBlocksAuxEqPrepare; try(assumption).
destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull.
- rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. unfold nullAddrExists in *. right. assumption.
- rewrite <-DTL.beqAddrFalse in HbeqStructNull. left. apply Hstruct. assumption.
Qed.

Lemma getAllPaddrConfigAuxEqPrepare listKS s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> (forall kern, In kern listKS -> isBE kern s0)
-> getAllPaddrConfigAux listKS s = getAllPaddrConfigAux listKS s0.
Proof.
intro HlookupSomeEq. induction listKS as [ | kern listKS]; intro HlistKS; try(reflexivity). simpl.
assert(HlistKSRec: forall kern, In kern listKS -> isBE kern s0).
{ intros kernBis HkernBisInList. apply HlistKS. simpl. right. assumption. }
assert(Hkern: In kern (kern::listKS)).
{ simpl. left. reflexivity. }
specialize(HlistKS kern Hkern). unfold isBE in HlistKS.
destruct (lookup kern (memory s0) beqAddr) eqn:HlookupKern; try(exfalso; congruence).
destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (BE b); assumption). rewrite HlookupKern.
f_equal. apply IHlistKS. assumption.
Qed.

Lemma configBlocksAreBEAux block n kernel s nbleft:
In block (filterOptionPaddr (getConfigBlocksAux n kernel s nbleft))
-> isBE block s.
Proof.
revert kernel nbleft. induction n; intros kernel nbleft HblockInConfig; simpl in *; try(exfalso; congruence).
destruct (lookup kernel (memory s) beqAddr) eqn:HlookupKern; try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
- destruct (Paddr.addPaddrIdx kernel nextoffset); try(simpl in *; exfalso; congruence).
  destruct (lookup p (memory s) beqAddr); try(simpl in *; exfalso; congruence).
  destruct v; try(simpl in *; exfalso; congruence).
  destruct (Index.pred nbleft); try(simpl in *; exfalso; congruence). simpl in HblockInConfig.
  destruct HblockInConfig as [HblockIsKern | HblockInConfigRec]; try(revert HblockInConfigRec; apply IHn).
  subst block. unfold isBE. rewrite HlookupKern. trivial.
- destruct (beqAddr p nullAddr); simpl in *; exfalso; congruence.
Qed.

Lemma configBlocksAreBE block partition s:
In block (getConfigBlocks partition s)
-> isBE block s.
Proof.
intro HblockInConfig. unfold getConfigBlocks in *.
destruct (lookup partition (memory s) beqAddr); try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence). revert HblockInConfig. apply configBlocksAreBEAux.
Qed.

Lemma isListOfKernelsAuxEqPrepare kernList initKern s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isListOfKernelsAux kernList initKern s0
-> isListOfKernelsAux kernList initKern s.
Proof.
intro HlookupSomeEq. revert initKern.
induction kernList as [ | kern kernList]; intro initKern; try(intuition; congruence). simpl.
intros (HlookupNext & HlebNextMax & HbeqKernNull & Hrec). intuition.
rewrite HlookupSomeEq; try(exists (PADDR kern)); assumption.
Qed.

Lemma isListOfKernelsEqPrepare kernList partition s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isListOfKernels kernList partition s0
-> isListOfKernels kernList partition s.
Proof.
intros HlookupSomeEq HkernList. unfold isListOfKernels in *. destruct kernList; trivial.
destruct HkernList as [pdentry (HlookupPart & HbeqStructNull & Hstruct & Hrec)]. exists pdentry. intuition.
- rewrite HlookupSomeEq; try(exists (PDT pdentry)); assumption.
- revert Hrec. apply isListOfKernelsAuxEqPrepare; assumption.
Qed.

Lemma isListOfKernelsAuxEqPreparess0 kernList initKern s s0:
(forall addr kern, lookup (CPaddr (addr + nextoffset)) (memory s) beqAddr = Some(PADDR kern)
  -> kern <> nullAddr
  -> lookup (CPaddr (addr + nextoffset)) (memory s) beqAddr = lookup (CPaddr (addr + nextoffset)) (memory s0) beqAddr)
-> isListOfKernelsAux kernList initKern s
-> isListOfKernelsAux kernList initKern s0.
Proof.
intro HlookupPaddrEq. revert initKern.
induction kernList as [ | kern kernList]; intro initKern; try(intuition; congruence). simpl.
intros (HlookupNext & HlebNextMax & HbeqKernNull & Hrec). intuition.
rewrite HlookupPaddrEq with initKern kern in HlookupNext; assumption.
Qed.

Lemma isListOfKernelsEqPreparess0 kernList partition s s0:
(forall partition, isPDT partition s -> lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr)
-> (forall addr kern, lookup (CPaddr (addr + nextoffset)) (memory s) beqAddr = Some(PADDR kern)
    -> kern <> nullAddr
    -> lookup (CPaddr (addr + nextoffset)) (memory s) beqAddr
        = lookup (CPaddr (addr + nextoffset)) (memory s0) beqAddr)
-> isListOfKernels kernList partition s
-> isListOfKernels kernList partition s0.
Proof.
intros HlookupPdtEq HlookupPaddrEq HkernList. unfold isListOfKernels in *. destruct kernList; trivial.
destruct HkernList as [pdentry (HlookupPart & HbeqStructNull & Hstruct & Hrec)]. exists pdentry. intuition.
- rewrite HlookupPdtEq in HlookupPart; try(assumption). unfold isPDT. rewrite HlookupPart. trivial.
- revert Hrec. apply isListOfKernelsAuxEqPreparess0; try(assumption).
Qed.

Lemma isParentsListEqPrepare parentsList pdBase s s0:
(forall addr, (exists entry, lookup addr (memory s0) beqAddr = Some entry)
  -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
-> isParentsList s0 parentsList pdBase
-> isParentsList s parentsList pdBase.
Proof.
intros HlookupSomeEq. revert pdBase.
induction parentsList as [ | pdparent parentsList]; intros pdBase HparentsList; try(intuition; congruence).
simpl in *. destruct (lookup pdparent (memory s0) beqAddr) eqn:HlookupParent; try(exfalso; congruence).
destruct v; try(exfalso; congruence). rewrite HlookupSomeEq; try(exists (PDT p); assumption). rewrite HlookupParent.
destruct HparentsList as (HbeqBaseRoot & [pdentry (HlookupBase & Hparent)] & HparentsListRec). split. assumption.
split.
- exists pdentry. rewrite HlookupSomeEq; try(exists (PDT pdentry); assumption). rewrite HlookupBase. split.
  reflexivity. assumption.
- revert HparentsListRec. apply IHparentsList; assumption.
Qed.

Lemma isParentsListEqPreparess0 parentsList pdBase s s0:
(forall partition, isPDT partition s -> lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr)
-> isParentsList s parentsList pdBase
-> isParentsList s0 parentsList pdBase.
Proof.
intros HlookupPdtEq. revert pdBase.
induction parentsList as [ | pdparent parentsList]; intros pdBase HparentsList; try(intuition; congruence).
simpl in *. destruct (lookup pdparent (memory s) beqAddr) eqn:HlookupParent; try(exfalso; congruence).
destruct v; try(exfalso; congruence). rewrite <-HlookupPdtEq; try(unfold isPDT; rewrite HlookupParent; trivial).
destruct HparentsList as (HbeqBaseRoot & [pdentry (HlookupBase & Hparent)] & HparentsListRec). split. assumption.
split.
- exists pdentry. rewrite <-HlookupPdtEq; try(unfold isPDT; rewrite HlookupBase; trivial). split.
  reflexivity. assumption.
- revert HparentsListRec. apply IHparentsList; assumption.
Qed.

Lemma completeParentsListRecEqIfLenLowEnough part s n m:
n <= m
-> length (filterOptionPaddr (completeParentsListRec m part s)) <= n
-> filterOptionPaddr (completeParentsListRec n part s) = filterOptionPaddr (completeParentsListRec m part s).
Proof.
revert part m. induction n; simpl; intros part m Hleb Hlen.
- apply eq_sym. destruct (filterOptionPaddr (completeParentsListRec m part s)).
  + reflexivity.
  + simpl in Hlen. exfalso; lia.
- destruct m; try(lia).
  destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; try(simpl; rewrite HlookupPart; reflexivity).
  destruct v; try(simpl; rewrite HlookupPart; reflexivity).
  destruct (beqAddr part constantRootPartM) eqn:HbeqPartRoot;
    try(simpl; rewrite HlookupPart; rewrite HbeqPartRoot; reflexivity). simpl. simpl in Hlen.
  rewrite HlookupPart in *. rewrite HbeqPartRoot in *. simpl in *. f_equal.
  apply IHn; lia.
Qed.

Lemma completeParentsListAdd pdbasepartition partition parentsList s:
parentOfPartitionIsPartition s
-> partitionTreeIsTree s
-> isParentsList s parentsList pdbasepartition
-> partition = last parentsList pdbasepartition
-> filterOptionPaddr (completeParentsList pdbasepartition s)
    = parentsList ++ filterOptionPaddr (completeParentsList partition s).
Proof.
intros HparentOfPart Htree. revert pdbasepartition.
induction parentsList; simpl; intros pdbasepartition HparentsList Hlast.
- subst partition. reflexivity.
- destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). destruct HparentsList as (HbeqBaseRoot & [pdentry (HlookupBase & Hparent)]
    & HparentsListRec).
  assert(HlastRec: partition = last parentsList a).
  {
    destruct parentsList. simpl. assumption. apply lastNotEmpty with pdbasepartition. assumption.
  }
  specialize(IHparentsList a HparentsListRec HlastRec).
  assert(Hcomplete: filterOptionPaddr (completeParentsList pdbasepartition s)
    = a :: filterOptionPaddr (completeParentsList a s)).
  {
    unfold completeParentsList at 1. set(succ := S maxAddr). cbn -[succ completeParentsList]. rewrite HlookupBase.
    rewrite beqAddrFalse in HbeqBaseRoot. rewrite HbeqBaseRoot. rewrite <-Hparent. cbn -[succ completeParentsList].
    f_equal. apply completeParentsListRecEqIfLenLowEnough.
    - lia.
    - fold completeParentsList. assert(isParentsList s (filterOptionPaddr (completeParentsList a s)) a).
      {
        apply completeParentsListIsParentsList. assumption. unfold isPDT. rewrite HlookupA. trivial.
      }
      assert(NoDup (filterOptionPaddr (completeParentsList a s))).
      { apply parentOfPartNotInParentsListsTail with a s; assumption. }
      unfold completeParentsList in *. subst succ. rewrite <-Nat.add_1_r in *. rewrite <-Nat.add_1_r in *.
      apply PaddrListBoundedLength. assumption.
  }
  rewrite Hcomplete. f_equal. assumption.
Qed.

Lemma ancestorsAddrNotAccIfNotInDesc n partition ancPart addr blockAnc s:
parentOfPartitionIsPartition s
-> isChild s
-> blockInChildHasAtLeastEquivalentBlockInParent s
-> wellFormedBlock s
-> (forall parent child addr : paddr,
      In child (partition::filterOptionPaddr (completeParentsListRec n partition s)) ->
      In parent (getPartitions multiplexer s) ->
      In child (getChildren parent s) ->
      In addr (getAccessibleMappedPaddr parent s) ->
      In addr (getMappedPaddr child s) -> In addr (getAccessibleMappedPaddr child s))
-> In partition (getPartitions multiplexer s)
-> In ancPart (filterOptionPaddr (completeParentsListRec n partition s))
-> In addr (getMappedPaddr partition s)
-> ~In addr (getAccessibleMappedPaddr partition s)
-> In blockAnc (getMappedBlocks ancPart s)
-> In addr (getAllPaddrAux [blockAnc] s)
-> bentryAFlag blockAnc false s.
Proof.
intros HparentOfPart HisChild HequivParent HwellFormed.
revert partition. induction n; simpl; intros partition Haccess HpartIsPart HancIsAnc HaddrMappedPart HaddrNotAccPart
  HblockAncMapped HaddrInBlockAnc; try(exfalso; congruence).
destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(simpl in HancIsAnc; exfalso; congruence).
destruct v; try(simpl in HancIsAnc; exfalso; congruence).
destruct (beqAddr partition constantRootPartM) eqn:HbeqPartRoot; try(simpl in HancIsAnc; exfalso; congruence).
simpl in HancIsAnc.
assert(HaccessRec: forall pdparent child addr,
  In child ((parent p)::filterOptionPaddr (completeParentsListRec n (parent p) s))
  -> In pdparent (getPartitions multiplexer s)
  -> In child (getChildren pdparent s)
  -> In addr (getAccessibleMappedPaddr pdparent s)
  -> In addr (getMappedPaddr child s) -> In addr (getAccessibleMappedPaddr child s)).
{
  intros pdparent child addrBis Hchild.
  assert(HchildRec: partition = child
    \/ In child (filterOptionPaddr (SomePaddr (parent p) :: completeParentsListRec n (parent p) s))).
  { simpl. right. assumption. }
  specialize(Haccess pdparent child addrBis HchildRec). assumption.
}
assert(HparentOfPartCopy: parentOfPartitionIsPartition s) by assumption.
specialize(HparentOfPart partition p HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
rewrite <-beqAddrFalse in HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
destruct HparentIsPart as (HlookupParent & HparentIsPart).
assert(HchildIsChild: In partition (getChildren (parent p) s)).
{ unfold isChild in *. apply HisChild; try(assumption). unfold pdentryParent. rewrite HlookupPart. reflexivity. }
assert(HaddrNotAccParent: ~ In addr (getAccessibleMappedPaddr (parent p) s)).
{
  intro Hcontra. specialize(Haccess (parent p) partition addr). contradict HaddrNotAccPart.
  apply Haccess; try(assumption). left. reflexivity.
}
assert(HaddrMappedParent: In addr (getMappedPaddr (parent p) s)).
{
  assert(HchildPaddr: childPaddrIsIntoParent s) by (apply blockInclImpliesAddrIncl; assumption).
  unfold childPaddrIsIntoParent in *. apply HchildPaddr with partition; assumption.
}
destruct HancIsAnc as [HancIsParent | HancIsAncRec].
- rewrite HancIsParent in *. unfold bentryAFlag. destruct (lookup blockAnc (memory s) beqAddr) eqn:HlookupBlock;
    try(simpl in HaddrInBlockAnc; congruence). destruct v; try(simpl in HaddrInBlockAnc; congruence).
  destruct (Bool.eqb false (accessible b)) eqn:HbeqFalseAcc.
  + apply Bool.eqb_true_iff. assumption.
  + apply Bool.eqb_false_iff in HbeqFalseAcc. apply not_eq_sym in HbeqFalseAcc. exfalso.
    apply Bool.not_false_is_true in HbeqFalseAcc. contradict HaddrNotAccParent.
    apply addrInAccessibleBlockIsAccessibleMapped with blockAnc; try(assumption).
    * simpl. rewrite HlookupBlock. assumption.
    * unfold bentryAFlag. rewrite HlookupBlock. apply eq_sym. assumption.
- specialize(IHn (parent p) HaccessRec HparentIsPart HancIsAncRec HaddrMappedParent HaddrNotAccParent HblockAncMapped
    HaddrInBlockAnc). assumption.
Qed.

Lemma getFreeSlotsListRecEqBERev freeslotaddr addr' newEntry s0 n nbfreeslotsleft optionfreeslotslist:
nullAddrExists s0
-> freeslotaddr <> addr' ->
isBE addr' s0 ->
wellFormedFreeSlotsList optionfreeslotslist <> False ->
NoDup (filterOptionPaddr (optionfreeslotslist)) ->
~ In addr' (filterOptionPaddr (getFreeSlotsListRec n freeslotaddr s0 nbfreeslotsleft))
-> optionfreeslotslist = getFreeSlotsListRec n freeslotaddr {|
                          currentPartition := currentPartition s0;
                          memory := add addr' (BE newEntry)
                                      (memory s0) beqAddr |} nbfreeslotsleft
-> optionfreeslotslist = getFreeSlotsListRec n freeslotaddr s0 nbfreeslotsleft.
Proof.
intro Hnull.
assert(Hnbfreeslots : nbfreeslotsleft < maxIdx+1).
{ destruct nbfreeslotsleft. simpl ;lia. }
revert n nbfreeslotsleft freeslotaddr optionfreeslotslist Hnbfreeslots.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
induction n.
- intros. intuition.
- intros nbfreeslotsleft freeslotaddr optionfreeslotslist HltNbFreeMax HbeqFreeAddr HaddrIsBE HwellFormed HnoDup
    HaddrNotInList. repeat rewrite FreeSlotsListRec_unroll. simpl. intro Hlist.
  destruct (beqAddr addr' freeslotaddr) eqn:Hnoteq.
  { rewrite <- DTL.beqAddrTrue in Hnoteq. exfalso; congruence. }
  rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in Hlist; intuition. simpl in HaddrNotInList.
  destruct (lookup freeslotaddr (memory s0) beqAddr) eqn:HfreeSlot; intuition.
  destruct v; intuition.
  destruct (Index.pred nbfreeslotsleft) eqn:Hpred; intuition. subst. f_equal.
  specialize(IHn i (endAddr (blockrange b)) (getFreeSlotsListRec n (endAddr (blockrange b)) s' i)).
  simpl in *. apply not_or_and in HaddrNotInList. destruct HaddrNotInList as (_ & HaddrNotInList).
  apply IHn; try(assumption); try(reflexivity).
  + unfold Index.pred in *. destruct (gt_dec nbfreeslotsleft 0) ; intuition ; try congruence.
    inversion Hpred. simpl. lia.
  +	rewrite FreeSlotsListRec_unroll in HaddrNotInList. unfold getFreeSlotsListAux in HaddrNotInList.
    rewrite FreeSlotsListRec_unroll in HwellFormed. unfold getFreeSlotsListAux in HwellFormed. destruct n.
    { simpl in HwellFormed. exfalso; congruence. }
    destruct (Index.ltb i zero) eqn:Hf ; try(cbn in HwellFormed; exfalso; congruence).
    destruct (lookup (endAddr (blockrange b)) (memory s') beqAddr) eqn:HlookupEnd;
      try(cbn in HwellFormed; exfalso; congruence).
    destruct v; try(cbn in HwellFormed; exfalso; congruence).
    * assert(HendIsBE: isBE (endAddr (blockrange b)) s0).
      {
        unfold isBE. simpl in HlookupEnd. destruct (beqAddr addr' (endAddr (blockrange b))) eqn:HbeqAddrEnd.
        - rewrite <-DTL.beqAddrTrue in HbeqAddrEnd. subst addr'. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
          rewrite HlookupEnd. trivial.
      }
      unfold isBE in HendIsBE.
      destruct (lookup (endAddr (blockrange b)) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      destruct (Index.pred i) eqn:Hff; try(cbn in HwellFormed; exfalso; congruence). simpl in HaddrNotInList.
      apply not_or_and in HaddrNotInList. destruct HaddrNotInList as (Hres & HaddrNotInList). assumption.
    * destruct (beqAddr (endAddr (blockrange b)) nullAddr) eqn:HbeqEndNull;
        try(cbn in HwellFormed; exfalso; congruence). rewrite <-DTL.beqAddrTrue in HbeqEndNull. rewrite HbeqEndNull.
      intro Hcontra. subst addr'. unfold nullAddrExists in *. unfold isPADDR in *. unfold isBE in *.
      destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
  + apply NoDup_cons_iff in HnoDup. apply HnoDup.
Qed.

Lemma getKSEntriesInStructAuxEqPADDR kernel addr newEntry s0 n entriesleft:
lookup addr (memory s0) beqAddr = Some(PADDR nullAddr)
-> getKSEntriesInStructAux n kernel {|
                                      currentPartition := currentPartition s0;
                                      memory := add addr (PADDR newEntry) (memory s0) beqAddr |} entriesleft
  = getKSEntriesInStructAux n kernel s0 entriesleft.
Proof.
revert n kernel entriesleft. set (s:= {|
                                        currentPartition := currentPartition s0;
                                        memory := _ |}). induction n.
- intros. simpl. reflexivity.
- intros kernel entriesleft HlookupAddr. unfold getKSEntriesInStructAux. fold getKSEntriesInStructAux.
	destruct (Index.ltb entriesleft zero) eqn:HltbZero; trivial.
	destruct (Paddr.addPaddrIdx kernel entriesleft) eqn:Hadd; trivial. simpl.
	destruct (beqAddr addr p) eqn:HbeqAddrP.
	+ rewrite <-DTL.beqAddrTrue in HbeqAddrP. subst p. rewrite HlookupAddr. reflexivity.
	+ rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup p (memory s0) beqAddr) eqn:HlookupP; trivial. destruct v; trivial.
    destruct (beqIdx entriesleft zero) eqn:HisZero; trivial.
    destruct (Index.pred entriesleft) eqn:Hpredentry; trivial. f_equal. specialize (IHn kernel i).
    apply IHn; trivial.
Qed.

Definition isCompleteListOfKernelsAux kernList (initKern: paddr) s :=
isListOfKernelsAux kernList initKern s
/\ exists kernel, kernel = last kernList initKern
  /\ lookup (CPaddr (kernel+nextoffset)) (memory s) beqAddr = Some(PADDR nullAddr).

Definition isCompleteListOfKernels kernList partition s :=
match kernList with
| [] => (exists pdentry, lookup partition (memory s) beqAddr = Some (PDT pdentry)
          /\ structure pdentry = nullAddr)
| kern::nextKernList => exists pdentry, lookup partition (memory s) beqAddr = Some (PDT pdentry)
                          /\ structure pdentry <> nullAddr /\ structure pdentry = kern
                          /\ isCompleteListOfKernelsAux nextKernList kern s
end.

Lemma getKSEntriesAuxEqPADDRFromNone (kernel addr: paddr) newEntry s0 n:
nullAddrExists s0
-> nextKernelIsValid s0
(*-> newEntry <> nullAddr*)
-> addr + nextoffset <= maxAddr
(*-> (isKS newEntry s0 \/ newEntry = nullAddr)*)
-> n > 0
-> lookup (CPaddr (addr+nextoffset)) (memory s0) beqAddr = Some(PADDR nullAddr)
-> isKS kernel s0
-> (exists kernList, isCompleteListOfKernelsAux kernList kernel s0 /\ ~In addr (kernel::kernList)
      /\ NoDup (kernel::kernList))
-> (addr <> kernel
      -> getKSEntriesAux n kernel {|
                                    currentPartition := currentPartition s0;
                                    memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr |}
          = getKSEntriesAux n kernel s0)
    /\ (addr = kernel
        -> getKSEntriesAux n kernel {|
                                      currentPartition := currentPartition s0;
                                      memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr |}
            = getKSEntriesAux n kernel s0 ++ getKSEntriesAux (n-1) newEntry s0).
Proof.
intros Hnull HnextValid (*HbeqNewNull*) HlebNextMax (*HnewIsKS*) Hn HlookupAddr.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}).
revert kernel. induction n; try(lia).
assert(HnextValidCopy: nextKernelIsValid s0) by assumption. unfold nullAddrExists in *.
intros kernel HkernIsKS HkernList. simpl. (*specialize(HnextValid newEntry HnewIsKS).*)
specialize(HnextValidCopy kernel HkernIsKS). destruct HnextValidCopy as (HlebKernNextMax & HnextKern).
(*destruct HnextValid as (HlebNewNextMax & HnextNew).*)
destruct HkernList as [kernList (HkernList & HaddrNotInList & HnoDup)].
unfold isCompleteListOfKernelsAux in HkernList. destruct HnextKern as [kernNextAddr (HlookupKernNext & HkernNext)].
destruct HkernList as (HkernList & [lastKern (HlastKern & HlookupLast)]).
assert(addr <> kernel).
{
  simpl in HaddrNotInList. apply not_or_and in HaddrNotInList. destruct HaddrNotInList. apply not_eq_sym.
  assumption.
}
destruct (Paddr.addPaddrIdx kernel nextoffset) eqn:HaddKernNext;
  try(split; intro; try(reflexivity); exfalso; congruence).
assert(HstructEq: getKSEntriesInStructAux (maxIdx + 1) kernel s (CIndex 7)
  = getKSEntriesInStructAux (maxIdx + 1) kernel s0 (CIndex 7)).
{ apply getKSEntriesInStructAuxEqPADDR; assumption. }
rewrite HstructEq. assert(Hp: p = CPaddr (kernel+nextoffset)).
{
  unfold Paddr.addPaddrIdx in *. unfold CPaddr.
  destruct (le_dec (kernel + nextoffset) maxAddr); try(exfalso; congruence). injection HaddKernNext as Hres.
  rewrite <-Hres. f_equal.
}
subst p. destruct (beqAddr (CPaddr (addr+nextoffset)) (CPaddr (kernel + nextoffset))) eqn:HbeqAddrP.
+ rewrite <-DTL.beqAddrTrue in HbeqAddrP. assert(addr = kernel).
  {
    unfold CPaddr in HbeqAddrP. destruct (le_dec (addr + nextoffset) maxAddr); try(lia).
    destruct (le_dec (kernel + nextoffset) maxAddr); try(lia). injection HbeqAddrP as HbeqAddrP.
    apply paddrEqNatEqEquiv. lia.
  }
  simpl in HaddrNotInList. apply not_or_and in HaddrNotInList. destruct HaddrNotInList as (Hcontra & _).
  exfalso; congruence.
+ rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  split; intro HbeqBis; try(exfalso; congruence).
  destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr) eqn:HlookupP; trivial. destruct v; trivial.
  destruct (beqAddr (CPaddr (addr + nextoffset)) p) eqn:HbeqAddrP0.
  * rewrite <-DTL.beqAddrTrue in HbeqAddrP0. subst p. rewrite HlookupAddr. reflexivity.
  * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup p (memory s0) beqAddr) eqn:HlookupP0; trivial. destruct v; trivial. f_equal.
    destruct n; trivial. assert(Hsucc: S n > 0) by lia. specialize(IHn Hsucc p). apply IHn; trivial.
    --- unfold CPaddr in HlookupP. destruct (le_dec (kernel + nextoffset) maxAddr); try(lia).
        specialize(HlookupKernNext (ADT.CPaddr_obligation_1 (kernel + nextoffset) l)).
        rewrite HlookupKernNext in HlookupP. injection HlookupP as HlookupP. subst p.
        destruct HkernNext as [Hres | Hcontra]; trivial. exfalso. subst kernNextAddr. unfold isPADDR in *.
        rewrite HlookupP0 in *. congruence.
    --- simpl in HaddrNotInList. apply not_or_and in HaddrNotInList.
        destruct HaddrNotInList as (HbeqKernAddr & HaddrNotInList). apply NoDup_cons_iff in HnoDup.
        destruct HnoDup as (HkernNotInList & HnoDup). destruct kernList.
        {
          simpl in HlastKern. subst lastKern. rewrite HlookupP in *. injection HlookupLast as HlookupLast. subst p.
          exfalso. unfold isPADDR in *. rewrite HlookupP0 in *. congruence.
        }
        simpl in HkernList. destruct HkernList as (HlookupKernNextBis & _ & HbeqPNull & HkernList).
        rewrite HlookupKernNextBis in *. injection HlookupP as HlookupP. subst p0. exists kernList.
        split; try(split); trivial. exists lastKern. split; trivial. apply lastRec with kernel; trivial.
    --- simpl in HaddrNotInList. apply not_or_and in HaddrNotInList.
        destruct HaddrNotInList as (_ & HaddrNotInList). destruct kernList.
        {
          simpl in HlastKern. subst lastKern. rewrite HlookupP in *. injection HlookupLast as HlookupLast. subst p.
          exfalso. unfold isPADDR in *. rewrite HlookupP0 in *. congruence.
        }
        simpl in HkernList. destruct HkernList as (HlookupKernNextBis & _ & HbeqPNull & HkernList).
        rewrite HlookupKernNextBis in *. injection HlookupP as HlookupP. subst p0. simpl in HaddrNotInList.
        apply not_or_and in HaddrNotInList. destruct HaddrNotInList. apply not_eq_sym. trivial.
Qed.

Lemma getKSEntriesEqPADDR partition (addr: paddr) newEntry s0 pdentry:
nullAddrExists s0
-> nextKernelIsValid s0
-> StructurePointerIsKS s0
-> addr + nextoffset <= maxAddr
(*-> isKS newEntry s0*)
-> lookup (CPaddr (addr+nextoffset)) (memory s0) beqAddr = Some(PADDR nullAddr)
-> lookup partition (memory s0) beqAddr = Some (PDT pdentry)
-> (exists kernList, isCompleteListOfKernels kernList partition s0 /\ ~In addr kernList
      /\ NoDup kernList)
-> getKSEntries partition {|
						currentPartition := currentPartition s0;
						memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr |}
  = getKSEntries partition s0.
Proof.
set (s:= {|
           currentPartition := currentPartition s0;
           memory := _ |}).
intros Hnull HnextValid Hstruct HlebAddrNextMax (*HnewIsKS*) HlookupNextAddr HlookupPart HkernList.
unfold getKSEntries. simpl lookup. destruct (beqAddr (CPaddr (addr + nextoffset)) partition) eqn:beqAddrPart.
{ (* addr' = partition *)
  rewrite <-DTL.beqAddrTrue in beqAddrPart. rewrite beqAddrPart in *. exfalso; congruence.
}
(* addr' <> partition *)
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupPart.
destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull; trivial.
destruct HkernList as [kernList (HkernList & HaddrNotInList & HnoDup)]. destruct kernList.
{
  simpl in HkernList. destruct HkernList as [pdentryBis (HlookupPartBis & Hcontra)]. rewrite HlookupPartBis in *.
  injection HlookupPart as HlookupPart. subst pdentryBis. rewrite <-beqAddrFalse in *. exfalso; congruence.
}
simpl in HkernList. destruct HkernList as [pdentryBis (HlookupPartBis & _ & HstructP & HkernList)].
rewrite HlookupPartBis in *. injection HlookupPart as HlookupPart. subst pdentryBis. subst p.
apply getKSEntriesAuxEqPADDRFromNone; trivial; try(lia).
- rewrite <-beqAddrFalse in *. specialize(Hstruct partition pdentry HlookupPartBis HbeqStructNull). assumption.
- exists kernList. split; trivial. split; trivial.
- simpl in HaddrNotInList. apply not_or_and in HaddrNotInList. intuition.
Qed.

Lemma filterPresentEqPADDR addr newEntry s0 blocklist:
isPADDR addr s0
-> filterPresent blocklist {|
                             currentPartition := currentPartition s0;
                             memory := add addr (PADDR newEntry) (memory s0) beqAddr
                           |}
= filterPresent blocklist s0.
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}). intros HPADDR. induction blocklist; simpl; try(reflexivity).
destruct (beqAddr addr a) eqn:HbeqAddrA.
- rewrite <-DTL.beqAddrTrue in HbeqAddrA.
  subst a. unfold isPADDR in *. destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  destruct (lookup a (memory s0) beqAddr); trivial. destruct v; trivial. destruct (present b); trivial.
  f_equal. trivial.
Qed.

Lemma getMappedBlocksEqPADDR partition (addr:paddr) newEntry s0 pdentry:
nullAddrExists s0
-> nextKernelIsValid s0
-> StructurePointerIsKS s0
-> addr + nextoffset <= maxAddr
(*-> isKS newEntry s0*)
-> lookup (CPaddr (addr+nextoffset)) (memory s0) beqAddr = Some(PADDR nullAddr)
-> lookup partition (memory s0) beqAddr = Some (PDT pdentry)
-> (exists kernList, isCompleteListOfKernels kernList partition s0 /\ ~In addr kernList /\ NoDup kernList)
-> getMappedBlocks partition {|
                               currentPartition := currentPartition s0;
                               memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr |}
  = getMappedBlocks partition s0.
Proof.
set (s:= {|
           currentPartition := currentPartition s0;
           memory := _ |}).
intros Hnull HnextValid Hstruct HlebAddrNextMax (*HnewIsKS*) HlookupNextAddr HlookupPart HkernList.
assert(Heq: getKSEntries partition s = getKSEntries partition s0).
{ apply getKSEntriesEqPADDR with pdentry; intuition. }
unfold getMappedBlocks. rewrite Heq. apply filterPresentEqPADDR. unfold isPADDR. rewrite HlookupNextAddr. trivial.
Qed.

Lemma childFilterEqPADDR addr newEntry s0 block:
isPADDR addr s0 ->
childFilter {|
						currentPartition := currentPartition s0;
						memory := add addr (PADDR newEntry) (memory s0) beqAddr |} block
= childFilter s0 block.
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}). intros HPADDR. unfold childFilter. cbn.
destruct (beqAddr addr block) eqn:HbeqAddrBlock.
- rewrite <-DTL.beqAddrTrue in HbeqAddrBlock. subst block. unfold isPADDR in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso ; congruence).
  destruct v; try(exfalso ; congruence). trivial.
-	rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  destruct (lookup block (memory s0) beqAddr); trivial. destruct v; trivial.
  destruct (Paddr.addPaddrIdx block sh1offset); trivial. destruct (beqAddr addr p) eqn:HbeqAddrP.
  + rewrite <-DTL.beqAddrTrue in HbeqAddrP. subst p. unfold isPADDR in *.
    destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso ; congruence).
    trivial.
  + rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
Qed.

Lemma getPDsEqPADDR addr newEntry s0 pdlist:
isPADDR addr s0 ->
getPDs pdlist {|
                currentPartition := currentPartition s0;
                memory := add addr (PADDR newEntry) (memory s0) beqAddr |}
= getPDs pdlist s0.
Proof.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}). intros HPADDR. unfold getPDs. induction pdlist; simpl; try(reflexivity).
assert(Heq: childFilter s a = childFilter s0 a).
{ eapply childFilterEqPADDR; intuition. }
rewrite Heq. destruct (childFilter s0 a) eqn:Hfilter; trivial. simpl.
destruct (beqAddr addr a) eqn:HbeqAddrA.
- rewrite <-DTL.beqAddrTrue in HbeqAddrA. subst a. unfold isPADDR in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  f_equal. trivial.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  f_equal. trivial.
Qed.

Lemma getChildrenEqPADDR partition pdentry (addr:paddr) newEntry s0:
nullAddrExists s0
-> nextKernelIsValid s0
-> StructurePointerIsKS s0
-> addr + nextoffset <= maxAddr
(*-> isKS newEntry s0*)
-> lookup (CPaddr (addr+nextoffset)) (memory s0) beqAddr = Some(PADDR nullAddr)
-> lookup partition (memory s0) beqAddr = Some (PDT pdentry)
-> (exists kernList, isCompleteListOfKernels kernList partition s0 /\ ~In addr kernList /\ NoDup kernList)
-> getChildren partition {|
                           currentPartition := currentPartition s0;
                           memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr |}
  = getChildren partition s0.
Proof.
set (s:= {|
           currentPartition := currentPartition s0;
           memory := _ |}).
intros Hnull HnextValid Hstruct HlebAddrNextMax (*HnewIsKS*) HlookupNextAddr HlookupPart HkernList.
unfold getChildren. simpl. destruct (beqAddr (CPaddr (addr+nextoffset)) partition) eqn:HbeqNextPart.
{ (* addr' = partition *)
  rewrite <-DTL.beqAddrTrue in HbeqNextPart. rewrite HbeqNextPart in *. exfalso; congruence.
}
(* addr' <> partition *)
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupPart.
assert(HmappedEq: getMappedBlocks partition s = getMappedBlocks partition s0).
{ apply getMappedBlocksEqPADDR with pdentry; intuition. }
rewrite HmappedEq. apply getPDsEqPADDR. unfold isPADDR. rewrite HlookupNextAddr. trivial.
Qed.

Lemma completeKernListAux n kern s:
nextKernelIsValid s
-> isKS kern s
-> length (completeListOfKernelsAux n kern s) < n
-> isCompleteListOfKernelsAux (completeListOfKernelsAux n kern s) kern s.
Proof.
intros HnextValid HkernIsKS Hlen. revert kern HkernIsKS Hlen. induction n; intros; simpl; try(lia).
assert(HnextValidCopy: nextKernelIsValid s) by assumption.
unfold isCompleteListOfKernelsAux. specialize(HnextValidCopy kern HkernIsKS).
destruct HnextValidCopy as (HlebNextMax & [nextAddr (HlookupNext & HnextAddr)]).
assert(HnextEq: exists Hp, CPaddr (kern + nextoffset) = {| p := kern + nextoffset; Hp := Hp |}).
{
  unfold CPaddr. destruct (le_dec (kern + nextoffset) maxAddr); try(lia).
  exists (ADT.CPaddr_obligation_1 (kern + nextoffset) l). f_equal.
}
destruct HnextEq as [Hp HnextEq]. rewrite HnextEq. rewrite HlookupNext.
destruct (beqAddr nextAddr nullAddr) eqn:HbeqNextNull.
- simpl. split; trivial. exists kern. split; trivial. rewrite <-DTL.beqAddrTrue in HbeqNextNull. subst nextAddr.
  rewrite HnextEq. trivial.
- simpl. simpl in Hlen. rewrite HnextEq in *. rewrite HlookupNext in *. rewrite HbeqNextNull in *. simpl in Hlen.
  assert(HlenRec: length (completeListOfKernelsAux n nextAddr s) < n) by lia. rewrite <-beqAddrFalse in *.
  destruct HnextAddr as [HnextIsKS | Hcontra]; try(exfalso; congruence). specialize(IHn nextAddr HnextIsKS HlenRec).
  split.
  + split; trivial. split; trivial. split; trivial. unfold isCompleteListOfKernelsAux in IHn. apply IHn.
  + destruct n; try(lia).
    destruct (completeListOfKernelsAux (S n) nextAddr s) eqn:Hlist.
    * exists nextAddr. simpl in Hlist. split; trivial. specialize(HnextValid nextAddr HnextIsKS).
      destruct HnextValid as (HlebNextBisMax & [nextNext (HlookupNextNext & _)]). unfold CPaddr in Hlist.
      unfold CPaddr. destruct (le_dec (nextAddr + nextoffset) maxAddr); try(lia). rewrite HlookupNextNext in *.
      destruct (beqAddr nextNext nullAddr) eqn:HbeqNextNextNull; try(exfalso; congruence).
      rewrite <-DTL.beqAddrTrue in HbeqNextNextNull. subst nextNext. reflexivity.
    * unfold isCompleteListOfKernelsAux in IHn. destruct IHn as (_ & [kernLast (Hlast & HlookupLast)]).
      exists kernLast. split; trivial. apply lastNotEmpty with nextAddr. assumption.
Qed.

Lemma completeKernListIsListOfKernAux n kern s:
nextKernelIsValid s
-> isKS kern s
-> isListOfKernelsAux (completeListOfKernelsAux n kern s) kern s.
Proof.
intro HnextValid. revert kern. induction n; intros kern HkernIsKS; simpl; trivial.
destruct (lookup (CPaddr (kern + nextoffset)) (memory s) beqAddr) eqn:HlookupNext; try(simpl; trivial).
destruct v; try(simpl; trivial). destruct (beqAddr p nullAddr) eqn:HbeqPNull; try(simpl; trivial).
specialize(HnextValid kern HkernIsKS). destruct HnextValid as (HlebNextMax & [nextAddr (HlookupNextBis & Hnext)]).
split; trivial. split; trivial. rewrite <-beqAddrFalse in *. split; trivial. apply IHn. unfold CPaddr in HlookupNext.
destruct (le_dec (kern + nextoffset) maxAddr); try(lia). rewrite HlookupNextBis in HlookupNext.
injection HlookupNext as HlookupNext. subst p. destruct Hnext as [Hres | Hcontra]; try(exfalso; congruence). trivial.
Qed.

Lemma completeKernListIsListOfKern partition pdentry s:
nullAddrExists s
-> nextKernelIsValid s
-> lookup partition (memory s) beqAddr = Some(PDT pdentry)
-> isListOfKernels (completeListOfKernels (structure pdentry) s) partition s.
Proof.
intros Hnull HnextValid HlookupPart. unfold completeListOfKernels.
destruct (lookup (structure pdentry) (memory s) beqAddr) eqn:HlookupStruct; try(simpl; trivial; congruence).
destruct v; try(simpl; trivial; congruence).
destruct (indexEq (blockindex b) (CIndex 0)) eqn:HidxIsZero; try(simpl; trivial; congruence).
cbn -[completeListOfKernelsAux maxNbPrepare nullAddr]. exists pdentry. split; trivial. split.
- intro Hcontra. unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hcontra in *. rewrite HlookupStruct in *.
  congruence.
- split; trivial. apply completeKernListIsListOfKernAux; trivial. unfold isKS. rewrite HlookupStruct.
  apply beqIdxTrue in HidxIsZero. unfold zero. assumption.
Qed.

Lemma completeKernList partition pdentry s:
nullAddrExists s
-> nextKernelIsValid s
-> StructurePointerIsKS s
-> maxNbPrepareIsMaxNbKernels s
-> lookup partition (memory s) beqAddr = Some(PDT pdentry)
-> isCompleteListOfKernels (completeListOfKernels (structure pdentry) s) partition s.
Proof.
intros Hnull HnextValid Hstruct HmaxNb HlookupPart.
destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
- unfold completeListOfKernels. rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull in *.
  unfold nullAddrExists in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  simpl. exists pdentry. split; trivial.
- rewrite <-beqAddrFalse in *. unfold isCompleteListOfKernels.
  specialize(Hstruct partition pdentry HlookupPart HbeqStructNull).
  assert(HisComplete: isCompleteListOfKernelsAux (completeListOfKernelsAux maxNbPrepare (structure pdentry) s)
    (structure pdentry) s).
  {
    apply completeKernListAux; trivial.
    pose proof (completeKernListIsListOfKern partition pdentry s Hnull HnextValid HlookupPart) as HisListOfKern.
    specialize(HmaxNb partition (completeListOfKernels (structure pdentry) s) HisListOfKern).
    unfold completeListOfKernels in HmaxNb. unfold isKS in *.
    destruct (lookup (structure pdentry) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). assert(HidxIsZero: indexEq (blockindex b) (CIndex 0) = true).
    {
      destruct (indexEq (blockindex b) (CIndex 0)) eqn:HidxEq; try(reflexivity). exfalso.
      unfold indexEq in HidxEq. apply Nat.eqb_neq in HidxEq. unfold zero in *. destruct (blockindex b).
      destruct (CIndex 0). simpl in HidxEq. injection Hstruct as Hcontra. congruence.
    }
    rewrite HidxIsZero in *. cbn -[completeListOfKernelsAux maxNbPrepare] in HmaxNb. lia.
  }
  specialize(HnextValid (structure pdentry) Hstruct). unfold completeListOfKernels.
  assert(HstructIsKS: isKS (structure pdentry) s) by assumption. unfold isKS in HstructIsKS.
  destruct (lookup (structure pdentry) (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). assert(HidxIsZero: indexEq (blockindex b) (CIndex 0) = true).
  {
    destruct (indexEq (blockindex b) (CIndex 0)) eqn:HidxEq; try(reflexivity). exfalso.
    unfold indexEq in HidxEq. apply Nat.eqb_neq in HidxEq. unfold zero in *. destruct (blockindex b).
    destruct (CIndex 0). simpl in HidxEq. injection HstructIsKS as Hcontra. congruence.
  }
  rewrite HidxIsZero. exists pdentry. split; trivial. split; trivial. split; trivial.
Qed.

Lemma getPartitionsAuxEqPADDR partition pdentry (addr:paddr) newEntry s0 n:
nullAddrExists s0
-> nextKernelIsValid s0
-> StructurePointerIsKS s0
-> noDupListOfKerns s0
-> maxNbPrepareIsMaxNbKernels s0
-> PDTIfPDFlag s0
-> addr + nextoffset <= maxAddr
(*-> isKS newEntry s0*)
-> lookup (CPaddr (addr+nextoffset)) (memory s0) beqAddr = Some(PADDR nullAddr)
-> (forall part kernList, isListOfKernels kernList part s0 -> ~In addr kernList)
-> lookup partition (memory s0) beqAddr = Some (PDT pdentry)
-> getPartitionsAux n partition {|
                                  currentPartition := currentPartition s0;
                                  memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr
                                |}
= getPartitionsAux n partition s0.
Proof.
intros Hnull HnextValid Hstruct HnoDupKern HmaxNb HPDTIfPDFlag HlebNextMax (*HnewIsKS*) HlookupNext
  HkernList.
revert n partition pdentry.
set (s := {|
            currentPartition := currentPartition s0;
            memory := _ |}). induction n; intros partition pdentry HlookupPart; simpl; try(reflexivity).
f_equal. assert(HChildrenEq: (getChildren partition s) = (getChildren partition s0)).
{
  apply getChildrenEqPADDR with pdentry; trivial.
  assert(HkernListPart:isCompleteListOfKernels (completeListOfKernels (structure pdentry) s0) partition s0).
  { apply completeKernList; trivial. }
  exists (completeListOfKernels (structure pdentry) s0). split; trivial.
  assert(HlistOfKerns: isListOfKernels (completeListOfKernels (structure pdentry) s0) partition s0).
  { apply completeKernListIsListOfKern; trivial. }
  split.
  - apply HkernList with partition. trivial.
  - specialize(HnoDupKern partition (completeListOfKernels (structure pdentry) s0) HlistOfKerns). assumption.
}
rewrite HChildrenEq. rewrite flat_map_concat_map. rewrite flat_map_concat_map. f_equal. clear HChildrenEq.
assert(HchildrenArePDT : forall child, In child (getChildren partition s0) -> isPDT child s0).
{ intros. apply childrenArePDT with partition; assumption. }
induction (getChildren partition s0); simpl; f_equal.
- assert(HaIsChild: In a (a::l)) by (simpl; left; reflexivity). specialize(HchildrenArePDT a HaIsChild).
  unfold isPDT in *. destruct (lookup a (memory s0) beqAddr) eqn:HlookupA; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). apply IHn with p; assumption.
- apply IHl. intros child HchildInL. assert(HchildInLRec: In child (a::l)) by (simpl; right; assumption).
  apply HchildrenArePDT; assumption.
Qed.

Lemma getPartitionsEqPADDR partition (addr:paddr) newEntry s0:
nullAddrExists s0
-> nextKernelIsValid s0
-> StructurePointerIsKS s0
-> noDupListOfKerns s0
-> maxNbPrepareIsMaxNbKernels s0
-> PDTIfPDFlag s0
-> addr + nextoffset <= maxAddr
(*-> isKS newEntry s0*)
-> lookup (CPaddr (addr+nextoffset)) (memory s0) beqAddr = Some(PADDR nullAddr)
-> (forall part kernList, isListOfKernels kernList part s0 -> ~In addr kernList)
-> isPDT partition s0
-> getPartitions partition {|
                             currentPartition := currentPartition s0;
                             memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr
                           |}
= getPartitions partition s0.
Proof.
unfold getPartitions. intros. unfold isPDT in *.
destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
destruct v; try(exfalso; congruence). apply getPartitionsAuxEqPADDR with p; assumption.
Qed.

Lemma getKSEntriesAuxRemoveExtraFuelEq kern len s:
nullAddrExists s
-> nextKernelIsValid s
-> isKS kern s
-> (forall kernList, isListOfKernelsAux kernList kern s -> length kernList < len)
-> getKSEntriesAux (S len) kern s = getKSEntriesAux len kern s.
Proof.
intros Hnull HnextValid. revert kern. induction len; intros kern HkernIsKS Hprop.
- assert(HkernList: isListOfKernelsAux [] kern s) by (simpl; trivial).
  specialize(Hprop [] HkernList). simpl in Hprop. lia.
- apply eq_sym. set(succ:= S len). unfold succ at 1. cbn -[succ].
  destruct (Paddr.addPaddrIdx kern nextoffset) eqn:Hadd; trivial.
  destruct (lookup p (memory s) beqAddr) eqn:HlookupNextAddr; trivial. destruct v; trivial.
  destruct (lookup p0 (memory s) beqAddr) eqn:HlookupNextKS; trivial.
  assert(Hnext: nextKernelIsValid s) by assumption.
  specialize(Hnext kern HkernIsKS). destruct Hnext as (Hle & Hnext). destruct v; trivial. f_equal. subst succ.
  apply eq_sym. apply IHlen.
  + destruct Hnext as [nextAddr (HlookupNext & HnextType)]. unfold Paddr.addPaddrIdx in Hadd.
    destruct (le_dec (kern + nextoffset) maxAddr); try(lia). injection Hadd as Hp.
    specialize(HlookupNext (StateLib.Paddr.addPaddrIdx_obligation_1 kern nextoffset l)).
    rewrite Hp in HlookupNext. rewrite HlookupNextAddr in HlookupNext. injection HlookupNext as Heq.
    subst p0. destruct HnextType as [Hres | Hcontra]; try(assumption). exfalso. unfold nullAddrExists in Hnull.
    unfold isPADDR in Hnull. subst nextAddr. rewrite HlookupNextKS in Hnull. congruence.
  + intros kernList HkernList. assert(HkernListExt: isListOfKernelsAux (p0::kernList) kern s).
    {
      simpl. assert(Hp: p = CPaddr (kern + nextoffset)).
      {
        unfold Paddr.addPaddrIdx in Hadd. unfold CPaddr.
        destruct (le_dec (kern + nextoffset) maxAddr); try(exfalso; congruence). injection Hadd as Hres.
        subst p. f_equal.
      }
      rewrite <-Hp. split. assumption. split. assumption. split; try(assumption). intro Hcontra. subst p0.
      unfold nullAddrExists in Hnull. unfold isPADDR in Hnull. rewrite HlookupNextKS in Hnull. congruence.
    }
    assert(HresExt: length (p0::kernList) < S len) by (apply Hprop; assumption).
    simpl in HresExt. lia.
Qed.

Lemma listOfKernIsInclInCompleteAux n kernel kernList s:
nextKernelIsValid s
-> isKS kernel s
-> isListOfKernelsAux kernList kernel s
-> length kernList <= n
-> exists postList, completeListOfKernelsAux n kernel s = kernList ++ postList.
Proof.
intro HnextValid. revert kernel kernList. induction n; simpl; intros kernel kernList HkernIsKS HkernList Hlen.
- destruct kernList; simpl in Hlen; try(lia). exists []. reflexivity.
- destruct kernList as [ | nextKern kernList]; simpl in *.
  + exists (match lookup (CPaddr (kernel + nextoffset)) (memory s) beqAddr with
    | Some (PADDR nextAddr) =>
        if beqAddr nextAddr nullAddr then [] else nextAddr :: completeListOfKernelsAux n nextAddr s
    | _ => []
    end). reflexivity.
  + destruct HkernList as (HlookupNext & HlebNextMax & HbeqNextAddr & HkernList). rewrite HlookupNext.
    rewrite beqAddrFalse in HbeqNextAddr. rewrite HbeqNextAddr. specialize(HnextValid kernel HkernIsKS).
    destruct HnextValid as (_ & [nextAddr (HlookupNextBis & Hnext)]). unfold CPaddr in HlookupNext.
    destruct (le_dec (kernel + nextoffset) maxAddr); try(lia). rewrite HlookupNextBis in HlookupNext.
    injection HlookupNext as HlookupNext. subst nextAddr. rewrite <-beqAddrFalse in *.
    destruct Hnext as [HnextIsKS | Hcontra]; try(exfalso; congruence). assert(HlenRec: length kernList <= n) by lia.
    specialize(IHn nextKern kernList HnextIsKS HkernList HlenRec). destruct IHn as [postList Heq]. exists postList.
    f_equal. assumption.
Qed.

Lemma listOfKernIsInclInComplete kernel kernList s:
nextKernelIsValid s
-> isKS kernel s
-> isListOfKernelsAux kernList kernel s
-> length kernList <= maxNbPrepare
-> exists postList, completeListOfKernels kernel s = kernel::(kernList++postList).
Proof.
intros HnextValid HkernIsKS HkernList Hlen. unfold completeListOfKernels.
assert(HkernIsKSCopy: isKS kernel s) by assumption. unfold isKS in HkernIsKSCopy.
destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
unfold zero in HkernIsKSCopy. destruct (indexEq (blockindex b) (CIndex 0)) eqn:HbeqIdxZero;
  try(apply beqIdxFalse in HbeqIdxZero; exfalso; congruence). clear HkernIsKSCopy. clear HbeqIdxZero.
assert(Hres: exists postList, completeListOfKernelsAux maxNbPrepare kernel s = kernList ++ postList).
{ apply listOfKernIsInclInCompleteAux; trivial. }
destruct Hres as [postList Heq]. exists postList. f_equal. assumption.
Qed.

Lemma getKSEntriesEqPDTNewEmptyStruct currentPart pdentry newPDEntry kernel s0:
lookup currentPart (memory s0) beqAddr = Some(PDT pdentry)
-> structure newPDEntry = kernel
-> isKS kernel s0
-> lookup (CPaddr (kernel+nextoffset)) (memory s0) beqAddr = Some(PADDR(structure pdentry))
-> StructurePointerIsKS s0
-> nullAddrExists s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> length (completeListOfKernels (structure pdentry) s0) < maxNbPrepare
-> getKSEntries currentPart
         {|
           currentPartition := currentPartition s0;
           memory := add currentPart (PDT newPDEntry) (memory s0) beqAddr
         |}
  = (getKSEntriesInStructAux (maxIdx+1) kernel s0 (CIndex (kernelStructureEntriesNb-1)))
      ++ getKSEntries currentPart s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}).
intros HlookupCurr HnewStruct HkernIsKS HlookupNext Hstruct Hnull HnextValid HmaxPrep HcompKernLen.
unfold getKSEntries in *. simpl lookup. rewrite beqAddrTrue. rewrite HnewStruct. rewrite HlookupCurr in *.
unfold nullAddrExists in *. specialize(HmaxPrep currentPart). destruct (beqAddr kernel nullAddr) eqn:HbeqKernNull.
{
  rewrite <-DTL.beqAddrTrue in HbeqKernNull. rewrite HbeqKernNull in *. unfold isPADDR in *. unfold isKS in *.
  exfalso. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
assert(HnextValidCopy: nextKernelIsValid s0) by assumption.
specialize(HnextValid kernel HkernIsKS). destruct HnextValid as (HlebNextMax & _).
assert(HgetStructEq: getKSEntriesInStructAux (maxIdx + 1) kernel s (CIndex 7)
  = getKSEntriesInStructAux (maxIdx + 1) kernel s0 (CIndex 7)).
{
  apply getKSEntriesInStructAuxEqPDT.
  - intro Hcontra. rewrite Hcontra in *. unfold isKS in *. rewrite HlookupCurr in *. congruence.
  - unfold isBE. rewrite HlookupCurr. intuition.
}
destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
- simpl. unfold Paddr.addPaddrIdx. unfold CPaddr in HlookupNext. rewrite <-DTL.beqAddrTrue in HbeqStructNull.
  rewrite HbeqStructNull in *. destruct (le_dec (kernel + nextoffset) maxAddr); try(lia).
  replace {| p := kernel + nextoffset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 kernel nextoffset l |} with
      {| p := kernel + nextoffset; Hp := ADT.CPaddr_obligation_1 (kernel + nextoffset) l |};
    try(f_equal; apply proof_irrelevance).
  destruct (beqAddr currentPart
    {| p := kernel + nextoffset; Hp := ADT.CPaddr_obligation_1 (kernel + nextoffset) l |}) eqn:HbeqCurrNext.
  {
    rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupNext.
  destruct (beqAddr currentPart nullAddr) eqn:HbeqCurrNull.
  {
    rewrite <-DTL.beqAddrTrue in HbeqCurrNull. subst currentPart. unfold isPADDR in *. rewrite HlookupCurr in *.
    exfalso; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  rewrite beqAddrTrue. rewrite app_nil_r. assumption.
- assert(HgetKSEq: getKSEntriesAux (maxNbPrepare+1) kernel s = getKSEntriesAux (maxNbPrepare+1) kernel s0).
  {
    apply getKSEntriesAuxEqPDT. 1: intro Hcontra; rewrite Hcontra in *; unfold isKS in *. 2: unfold isPADDR.
    3: unfold isBE. 1,2,3: rewrite HlookupCurr in *; congruence.
  }
  rewrite HgetKSEq. assert(Heq: getKSEntriesAux (S (maxNbPrepare+1)) kernel s0
    = getKSEntriesAux (maxNbPrepare+1) kernel s0).
  {
    pose proof maxNbPrepareNotZero.
    apply getKSEntriesAuxRemoveExtraFuelEq; trivial. intros kernList HkernList. rewrite <-beqAddrFalse in *.
    specialize(Hstruct currentPart pdentry HlookupCurr HbeqStructNull). destruct kernList; try(simpl; lia).
    simpl in HkernList. simpl. destruct HkernList as (HlookupNextBis & _ & HbeqNextNull & HkernListRec).
    rewrite HlookupNext in HlookupNextBis. injection HlookupNextBis as HlookupNextBis. subst p.
    assert(HkernListBis: isListOfKernels ((structure pdentry)::kernList) currentPart s0).
    {
      simpl. exists pdentry. split; trivial. split; trivial. split; trivial.
    }
    specialize(HmaxPrep ((structure pdentry)::kernList) HkernListBis). cbn in HmaxPrep. lia.
  }
  cbn -[maxNbPrepare nullAddr] in Heq. unfold CPaddr in HlookupNext. unfold Paddr.addPaddrIdx in *.
  destruct (le_dec (kernel + nextoffset) maxAddr); try(lia).
  replace {| p := kernel + nextoffset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 kernel nextoffset l |} with
      {| p := kernel + nextoffset; Hp := ADT.CPaddr_obligation_1 (kernel + nextoffset) l |} in *;
    try(f_equal; apply proof_irrelevance). rewrite HlookupNext in *. specialize(HnextValidCopy kernel HkernIsKS).
  destruct HnextValidCopy as (_ & [nextAddr (HlookupNextBis & Hnext)]).
  specialize(HlookupNextBis (ADT.CPaddr_obligation_1 (kernel + nextoffset) l)). rewrite HlookupNext in HlookupNextBis.
  injection HlookupNextBis as HlookupNextBis. subst nextAddr. rewrite <-beqAddrFalse in *.
  destruct Hnext as [HnextIsKS | Hcontra]; try(exfalso; congruence). unfold isKS in HnextIsKS.
  destruct (lookup (structure pdentry) (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). apply eq_sym. cbn -[maxIdx maxNbPrepare]. assumption.
Qed.

Lemma getMappedBlocksEqPDTNewEmptyStruct partition currentPart pdentry newPDEntry kernel s0:
lookup currentPart (memory s0) beqAddr = Some(PDT pdentry)
-> structure newPDEntry = kernel
-> isKS kernel s0
-> lookup (CPaddr (kernel+nextoffset)) (memory s0) beqAddr = Some(PADDR(structure pdentry))
-> StructurePointerIsKS s0
-> nullAddrExists s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> length (completeListOfKernels (structure pdentry) s0) < maxNbPrepare
-> (forall block,
    In block (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1) kernel s0 (CIndex (kernelStructureEntriesNb-1))))
    -> bentryPFlag block false s0)
-> getMappedBlocks partition {|
						               currentPartition := currentPartition s0;
						               memory := add currentPart (PDT newPDEntry) (memory s0) beqAddr |}
    = getMappedBlocks partition s0.
Proof.
set (s:= {|
           currentPartition := currentPartition s0;
           memory := _ |}). intros HlookupNews0 HnewStruct HkernIsKS HnextIsStruct Hstruct Hnull HnextValid HmaxPrep
  Hlen HnewBlocksAreNotPres. unfold getMappedBlocks.
destruct (beqAddr partition currentPart) eqn:HbeqPartCurr.
- rewrite <-DTL.beqAddrTrue in HbeqPartCurr. subst partition. pose proof (getKSEntriesEqPDTNewEmptyStruct currentPart
    pdentry newPDEntry kernel s0 HlookupNews0 HnewStruct HkernIsKS HnextIsStruct Hstruct Hnull HnextValid HmaxPrep
    Hlen) as HgetKSEq. fold s in HgetKSEq. rewrite HgetKSEq. rewrite filterOptionPaddrSplit.
  rewrite filterPresentSplit. replace (filterPresent (filterOptionPaddr (getKSEntries currentPart s0)) s) with
    (filterPresent (filterOptionPaddr (getKSEntries currentPart s0)) s0); try(apply eq_sym; apply filterPresentEqPDT;
    unfold isPDT; rewrite HlookupNews0; trivial).
  assert(HnewIsEmpty: filterPresent (filterOptionPaddr
     (getKSEntriesInStructAux (maxIdx + 1) kernel s0 (CIndex (kernelStructureEntriesNb - 1)))) s = []).
  {
    clear HgetKSEq. induction (getKSEntriesInStructAux (maxIdx+1) kernel s0 (CIndex (kernelStructureEntriesNb-1)));
      simpl; trivial.
    assert(HnewBlocksAreNotPresRec: forall block, In block (filterOptionPaddr l) -> bentryPFlag block false s0).
    {
      intros block HblockInList. apply HnewBlocksAreNotPres. simpl. destruct a; trivial. simpl. right. assumption.
    }
    specialize(IHl HnewBlocksAreNotPresRec). destruct a as [block | ]; trivial. simpl.
    assert(HblockInList: In block (filterOptionPaddr (SomePaddr block :: l))) by (simpl; left; reflexivity).
    specialize(HnewBlocksAreNotPres block HblockInList). unfold bentryPFlag in HnewBlocksAreNotPres.
    destruct (beqAddr currentPart block) eqn:HbeqCurrBlock.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBlock. subst block. rewrite HlookupNews0 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    rewrite <-HnewBlocksAreNotPres. assumption.
  }
  rewrite HnewIsEmpty. rewrite app_nil_l. reflexivity.
- assert(HgetKSEq: getKSEntries partition s = getKSEntries partition s0).
  {
    rewrite <-beqAddrFalse in *. apply getKSEntriesEqPDTNotInPart; trivial. unfold isPADDR. 2: unfold isBE.
    1,2: rewrite HlookupNews0; intuition.
  }
  rewrite HgetKSEq. apply filterPresentEqPDT. unfold isPDT. rewrite HlookupNews0. trivial.
Qed.

Lemma getChildrenEqPDTNewEmptyStruct partition currentPart pdentry newPDEntry kernel s0:
lookup currentPart (memory s0) beqAddr = Some(PDT pdentry)
-> structure newPDEntry = kernel
-> isKS kernel s0
-> lookup (CPaddr (kernel+nextoffset)) (memory s0) beqAddr = Some(PADDR(structure pdentry))
-> StructurePointerIsKS s0
-> nullAddrExists s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> length (completeListOfKernels (structure pdentry) s0) < maxNbPrepare
-> (forall block,
    In block (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1) kernel s0 (CIndex (kernelStructureEntriesNb-1))))
    -> bentryPFlag block false s0)
-> isPDT partition s0
-> getChildren partition {|
						               currentPartition := currentPartition s0;
						               memory := add currentPart (PDT newPDEntry)
                           (memory s0) beqAddr |}
    = getChildren partition s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}).
intros HlookupNews0 HnewStruct HkernIsKS HnextIsStruct Hstruct Hnull HnextValid HmaxPrep Hlen HnewBlocksAreNotPres
  HpartIsPDT. unfold getChildren. unfold isPDT in *.
destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
assert(HlookupParts: exists pdentryParts, lookup partition (memory s) beqAddr = Some(PDT pdentryParts)).
{
  simpl. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
  - exists newPDEntry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. reflexivity.
  - exists p. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
destruct HlookupParts as [pdentryParts HlookupParts]. rewrite HlookupParts. unfold s.
rewrite getMappedBlocksEqPDTNewEmptyStruct with partition currentPart pdentry newPDEntry kernel s0; trivial.
apply getPDsEqPDT. unfold isPDT. rewrite HlookupNews0. trivial.
Qed.

Lemma getPartitionsAuxEqPDTNewEmptyStruct partition currentPart pdentry newPDEntry kernel s0 n:
lookup currentPart (memory s0) beqAddr = Some(PDT pdentry)
-> structure newPDEntry = kernel
-> isKS kernel s0
-> lookup (CPaddr (kernel+nextoffset)) (memory s0) beqAddr = Some(PADDR(structure pdentry))
-> StructurePointerIsKS s0
-> nullAddrExists s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> PDTIfPDFlag s0
-> length (completeListOfKernels (structure pdentry) s0) < maxNbPrepare
-> (forall block,
    In block (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1) kernel s0 (CIndex (kernelStructureEntriesNb-1))))
    -> bentryPFlag block false s0)
-> isPDT partition s0
-> getPartitionsAux n partition {|
                                  currentPartition := currentPartition s0;
                                  memory := add currentPart (PDT newPDEntry) (memory s0) beqAddr |}
    = getPartitionsAux n partition s0.
Proof.
intros HlookupNews0 HnewStruct HkernIsKS HlookupNext Hstruct Hnull HnextValid HmaxPrep HPDTIfPDFlag Hlen
  HnewBlocksAreNotPres. revert partition. set (s := {| currentPartition := currentPartition s0; memory := _ |}).
induction n; intros partition HpartIsPDT; simpl; f_equal.
assert(HgetChildrenEq: (getChildren partition s) = (getChildren partition s0)).
{ apply getChildrenEqPDTNewEmptyStruct with pdentry kernel; trivial. }
rewrite HgetChildrenEq. rewrite flat_map_concat_map. rewrite flat_map_concat_map. f_equal. clear HgetChildrenEq.
assert(HchildrenArePDT : forall child, In child (getChildren partition s0) -> isPDT child s0).
{ intros. apply childrenArePDT with partition ; intuition. }
induction (getChildren partition s0); simpl; trivial. f_equal.
- apply IHn. apply HchildrenArePDT. simpl. left. reflexivity.
- apply IHl. intros child HchildInList. apply HchildrenArePDT. simpl. right. assumption.
Qed.

Lemma getPartitionsEqPDTNewEmptyStruct partition currentPart pdentry newPDEntry kernel s0 :
lookup currentPart (memory s0) beqAddr = Some(PDT pdentry)
-> structure newPDEntry = kernel
-> isKS kernel s0
-> lookup (CPaddr (kernel+nextoffset)) (memory s0) beqAddr = Some(PADDR(structure pdentry))
-> StructurePointerIsKS s0
-> nullAddrExists s0
-> nextKernelIsValid s0
-> maxNbPrepareIsMaxNbKernels s0
-> PDTIfPDFlag s0
-> length (completeListOfKernels (structure pdentry) s0) < maxNbPrepare
-> (forall block,
    In block (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1) kernel s0 (CIndex (kernelStructureEntriesNb-1))))
    -> bentryPFlag block false s0)
-> isPDT partition s0
-> getPartitions partition {|
                             currentPartition := currentPartition s0;
                             memory := add currentPart (PDT newPDEntry) (memory s0) beqAddr |}
  = getPartitions partition s0.
Proof.
unfold getPartitions. apply getPartitionsAuxEqPDTNewEmptyStruct.
Qed.

Lemma completeListOfKernelsAuxEqBE n kernel block newBEntry s0:
~isPADDR block s0
-> completeListOfKernelsAux n kernel {|
                                       currentPartition := currentPartition s0;
                                       memory := add block (BE newBEntry) (memory s0) beqAddr
                                     |}
= completeListOfKernelsAux n kernel s0.
Proof.
intro HblockNotPADDR. revert kernel. induction n; intro; simpl; trivial. unfold isPADDR in *.
destruct (beqAddr block (CPaddr (kernel + nextoffset))) eqn:HbeqBlockNext.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite HbeqBlockNext in *.
  destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial. exfalso.
  contradict HblockNotPADDR. trivial.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial.
destruct (beqAddr p nullAddr); trivial. f_equal. apply IHn.
Qed.

Lemma completeListOfKernelsEqBE kernel block bentry newBEntry s0:
lookup block (memory s0) beqAddr = Some(BE bentry)
-> blockindex newBEntry = blockindex bentry
-> completeListOfKernels kernel {|
                                  currentPartition := currentPartition s0;
                                  memory := add block (BE newBEntry) (memory s0) beqAddr
                                |}
= completeListOfKernels kernel s0.
Proof.
intros HlookupBlock HidxEq. unfold completeListOfKernels. cbn -[maxNbPrepare nullAddr CIndex].
assert(Heq: completeListOfKernelsAux maxNbPrepare kernel
          {|
            currentPartition := currentPartition s0;
            memory := add block (BE newBEntry) (memory s0) beqAddr
          |}
        = completeListOfKernelsAux maxNbPrepare kernel s0).
{
  apply completeListOfKernelsAuxEqBE. unfold isPADDR. rewrite HlookupBlock. intuition.
}
rewrite Heq. destruct (beqAddr block kernel) eqn:HbeqBlockKern.
- rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlock. rewrite HidxEq. reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
Qed.

Lemma completeListOfKernelsAuxEqPDT n kernel part newPDTEntry s0:
~isPADDR part s0
-> completeListOfKernelsAux n kernel {|
                                       currentPartition := currentPartition s0;
                                       memory := add part (PDT newPDTEntry) (memory s0) beqAddr
                                     |}
= completeListOfKernelsAux n kernel s0.
Proof.
intro HnotPADDR. revert kernel. induction n; intro; simpl; trivial. unfold isPADDR in *.
destruct (beqAddr part (CPaddr (kernel + nextoffset))) eqn:HbeqPartNext.
{
  rewrite <-DTL.beqAddrTrue in HbeqPartNext. rewrite HbeqPartNext in *.
  destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial. exfalso.
  contradict HnotPADDR. trivial.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial.
destruct (beqAddr p nullAddr); trivial. f_equal. apply IHn.
Qed.

Lemma completeListOfKernelsEqPDT kernel part newPDTEntry s0:
isPDT part s0
-> completeListOfKernels kernel {|
                                  currentPartition := currentPartition s0;
                                  memory := add part (PDT newPDTEntry) (memory s0) beqAddr
                                |}
= completeListOfKernels kernel s0.
Proof.
intro HpartIsPDTs0. unfold completeListOfKernels. cbn -[maxNbPrepare nullAddr CIndex].
assert(Heq: completeListOfKernelsAux maxNbPrepare kernel
          {|
            currentPartition := currentPartition s0;
            memory := add part (PDT newPDTEntry) (memory s0) beqAddr
          |}
        = completeListOfKernelsAux maxNbPrepare kernel s0).
{
  apply completeListOfKernelsAuxEqPDT. unfold isPADDR. unfold isPDT in *.
  destruct (lookup part (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  intuition.
}
rewrite Heq. destruct (beqAddr part kernel) eqn:HbeqPartKern.
- rewrite <-DTL.beqAddrTrue in HbeqPartKern. subst part. unfold isPDT in *.
  destruct (lookup kernel (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
Qed.

Lemma completeListOfKernelsEqNewPDT kernel part newPDTEntry s0:
lookup part (memory s0) beqAddr = None
-> completeListOfKernels kernel {|
                                  currentPartition := currentPartition s0;
                                  memory := add part (PDT newPDTEntry) (memory s0) beqAddr
                                |}
= completeListOfKernels kernel s0.
Proof.
intro HpartIsNones0. unfold completeListOfKernels. cbn -[maxNbPrepare nullAddr CIndex].
assert(Heq: completeListOfKernelsAux maxNbPrepare kernel
          {|
            currentPartition := currentPartition s0;
            memory := add part (PDT newPDTEntry) (memory s0) beqAddr
          |}
        = completeListOfKernelsAux maxNbPrepare kernel s0).
{
  apply completeListOfKernelsAuxEqPDT. unfold isPADDR. rewrite HpartIsNones0. intuition.
}
rewrite Heq. destruct (beqAddr part kernel) eqn:HbeqPartKern.
- rewrite <-DTL.beqAddrTrue in HbeqPartKern. subst part. rewrite HpartIsNones0. reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
Qed.

Lemma completeListOfKernelsAuxEqSHE n kernel addr newSHEntry s0:
~isPADDR addr s0
-> completeListOfKernelsAux n kernel {|
                                       currentPartition := currentPartition s0;
                                       memory := add addr (SHE newSHEntry) (memory s0) beqAddr
                                     |}
= completeListOfKernelsAux n kernel s0.
Proof.
intro HnotPADDR. revert kernel. induction n; intro; simpl; trivial. unfold isPADDR in *.
destruct (beqAddr addr (CPaddr (kernel + nextoffset))) eqn:HbeqAddrNext.
{
  rewrite <-DTL.beqAddrTrue in HbeqAddrNext. rewrite HbeqAddrNext in *.
  destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial. exfalso.
  contradict HnotPADDR. trivial.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial.
destruct (beqAddr p nullAddr); trivial. f_equal. apply IHn.
Qed.

Lemma completeListOfKernelsEqSHE kernel addr newSHEntry s0:
isSHE addr s0
-> completeListOfKernels kernel {|
                                  currentPartition := currentPartition s0;
                                  memory := add addr (SHE newSHEntry) (memory s0) beqAddr
                                |}
= completeListOfKernels kernel s0.
Proof.
intro HpartIsSHEs0. unfold completeListOfKernels. cbn -[maxNbPrepare nullAddr CIndex].
assert(Heq: completeListOfKernelsAux maxNbPrepare kernel
          {|
            currentPartition := currentPartition s0;
            memory := add addr (SHE newSHEntry) (memory s0) beqAddr
          |}
        = completeListOfKernelsAux maxNbPrepare kernel s0).
{
  apply completeListOfKernelsAuxEqSHE. unfold isPADDR. unfold isSHE in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  intuition.
}
rewrite Heq. destruct (beqAddr addr kernel) eqn:HbeqAddrKern.
- rewrite <-DTL.beqAddrTrue in HbeqAddrKern. subst addr. unfold isSHE in *.
  destruct (lookup kernel (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
Qed.

Lemma completeListOfKernelsAuxEqSCE n kernel addr newSCEntry s0:
~isPADDR addr s0
-> completeListOfKernelsAux n kernel {|
                                       currentPartition := currentPartition s0;
                                       memory := add addr (SCE newSCEntry) (memory s0) beqAddr
                                     |}
= completeListOfKernelsAux n kernel s0.
Proof.
intro HnotPADDR. revert kernel. induction n; intro; simpl; trivial. unfold isPADDR in *.
destruct (beqAddr addr (CPaddr (kernel + nextoffset))) eqn:HbeqAddrNext.
{
  rewrite <-DTL.beqAddrTrue in HbeqAddrNext. rewrite HbeqAddrNext in *.
  destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial. exfalso.
  contradict HnotPADDR. trivial.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup (CPaddr (kernel + nextoffset)) (memory s0) beqAddr); trivial. destruct v; trivial.
destruct (beqAddr p nullAddr); trivial. f_equal. apply IHn.
Qed.

Lemma completeListOfKernelsEqSCE kernel addr newSCEntry s0:
isSCE addr s0
-> completeListOfKernels kernel {|
                                  currentPartition := currentPartition s0;
                                  memory := add addr (SCE newSCEntry) (memory s0) beqAddr
                                |}
= completeListOfKernels kernel s0.
Proof.
intro HpartIsSCEs0. unfold completeListOfKernels. cbn -[maxNbPrepare nullAddr CIndex].
assert(Heq: completeListOfKernelsAux maxNbPrepare kernel
          {|
            currentPartition := currentPartition s0;
            memory := add addr (SCE newSCEntry) (memory s0) beqAddr
          |}
        = completeListOfKernelsAux maxNbPrepare kernel s0).
{
  apply completeListOfKernelsAuxEqSCE. unfold isPADDR. unfold isSCE in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  intuition.
}
rewrite Heq. destruct (beqAddr addr kernel) eqn:HbeqAddrKern.
- rewrite <-DTL.beqAddrTrue in HbeqAddrKern. subst addr. unfold isSCE in *.
  destruct (lookup kernel (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
Qed.

Lemma completeListOfKernelsAuxEqPADDRNew n kernel (addr:paddr) newPADDREntry s0:
addr + nextoffset <= maxAddr
-> nextKernelIsValid s0
-> isKS kernel s0
-> ~In addr (kernel::completeListOfKernelsAux n kernel s0)
-> completeListOfKernelsAux n kernel
    {|
      currentPartition := currentPartition s0;
      memory := add (CPaddr(addr+nextoffset)) (PADDR newPADDREntry) (memory s0) beqAddr
    |}
= completeListOfKernelsAux n kernel s0.
Proof.
intros HlebNextAddrMax HnextValid. revert kernel.
induction n; simpl; intros kernel HkernIsKS HaddrNotInList; trivial. apply not_or_and in HaddrNotInList.
destruct HaddrNotInList as (HbeqKernAddr & HaddrNotInList). specialize(HnextValid kernel HkernIsKS).
destruct HnextValid as (HlebNextMax & [nextKern (HlookupNext & Hnext)]).
destruct (beqAddr (CPaddr (addr + nextoffset)) (CPaddr (kernel + nextoffset))) eqn:HbeqAddrNext.
{
  rewrite <-DTL.beqAddrTrue in HbeqAddrNext. unfold CPaddr in HbeqAddrNext.
  destruct (le_dec (addr + nextoffset) maxAddr); try(lia). destruct (le_dec (kernel + nextoffset) maxAddr); try(lia).
  injection HbeqAddrNext as HbeqAddrNext. apply Nat.add_cancel_r in HbeqAddrNext.
  apply paddrEqNatEqEquiv in HbeqAddrNext. exfalso; congruence.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
assert(HlookupNextKern: exists Hp, CPaddr (kernel + nextoffset) = {| p := p kernel + i nextoffset; Hp := Hp |}).
{
  unfold CPaddr. destruct (le_dec (kernel + nextoffset) maxAddr); try(lia).
  exists (ADT.CPaddr_obligation_1 (kernel + nextoffset) l). reflexivity.
}
destruct HlookupNextKern as [Hp HnextKernEq]. rewrite HnextKernEq. rewrite HlookupNext.
destruct (beqAddr nextKern nullAddr) eqn:HbeqNextNull; trivial. f_equal. apply IHn.
- rewrite <-beqAddrFalse in *. destruct Hnext as [HnextIsKS | Hcontra]; try(exfalso; congruence). assumption.
- rewrite HnextKernEq in HaddrNotInList. rewrite HlookupNext in HaddrNotInList.
  rewrite HbeqNextNull in HaddrNotInList. assumption.
Qed.

Lemma completeListOfKernelsEqPADDRNew kernel (addr:paddr) newPADDREntry s0:
addr + nextoffset <= maxAddr
-> nextKernelIsValid s0
-> isKS kernel s0
-> isPADDR (CPaddr (addr + nextoffset)) s0
-> ~In addr (completeListOfKernels kernel s0)
-> completeListOfKernels kernel
    {|
      currentPartition := currentPartition s0;
      memory := add (CPaddr(addr+nextoffset)) (PADDR newPADDREntry) (memory s0) beqAddr
    |}
= completeListOfKernels kernel s0.
Proof.
unfold completeListOfKernels. intros HlebNextAddrMax HnextValid HkernIsKS HnextIsPADDR HaddrNotInList.
assert(HkernIsKSCopy: isKS kernel s0) by assumption.
unfold isKS in HkernIsKS. simpl lookup. destruct (beqAddr (CPaddr (addr + nextoffset)) kernel) eqn:HbeqNextKern.
{
  unfold isPADDR in *. rewrite <-DTL.beqAddrTrue in HbeqNextKern. subst kernel. exfalso.
  destruct (lookup (CPaddr (addr + nextoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup kernel (memory s0) beqAddr) eqn:HlookupKern; trivial. destruct v; trivial.
destruct (indexEq (blockindex b) (CIndex 0)); trivial. f_equal. apply completeListOfKernelsAuxEqPADDRNew; trivial.
Qed.

Lemma isListOfKernelsAuxEqPADDR kernel (addr:paddr) newEntry kernList s0:
addr + nextoffset <= maxAddr
-> addr <> kernel
-> (forall klist, isListOfKernelsAux klist kernel s0 -> ~ In addr klist)
-> isListOfKernelsAux kernList kernel {|
                                        currentPartition := currentPartition s0;
                                        memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr
                                      |}
-> isListOfKernelsAux kernList kernel s0.
Proof.
intros HlebNextMax HbeqAddrKern HaddrNotInLists0 HisKernLists.
revert kernel HbeqAddrKern HaddrNotInLists0 HisKernLists. induction kernList; simpl; intros; trivial.
destruct (beqAddr (CPaddr (addr + nextoffset)) (CPaddr (kernel + nextoffset))) eqn:HbeqNexts.
{
  rewrite <-DTL.beqAddrTrue in HbeqNexts. unfold CPaddr in HbeqNexts.
  destruct HisKernLists as (HeqContra & HlebNextKernMax & HbeqANull & _).
  destruct (le_dec (addr + nextoffset) maxAddr); try(lia). destruct (le_dec (kernel + nextoffset) maxAddr); try(lia).
  apply paddrEqNatEqEquiv in HbeqNexts. simpl in HbeqNexts. apply Nat.add_cancel_r in HbeqNexts.
  apply paddrEqNatEqEquiv in HbeqNexts. exfalso; congruence.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
destruct HisKernLists as (HlookupNext & HlebNextKernMax & HbeqANull & HisKernLists). split; trivial. split; trivial.
split; trivial. apply IHkernList; trivial.
- assert(HpartKernList: isListOfKernelsAux [a] kernel s0).
  {
    simpl. split; trivial. split; trivial. split; trivial.
  }
  specialize(HaddrNotInLists0 [a] HpartKernList). simpl in HaddrNotInLists0. apply not_or_and in HaddrNotInLists0.
  apply not_eq_sym. apply HaddrNotInLists0.
- intros klist Hklist. assert(HklistRec: isListOfKernelsAux (a :: klist) kernel s0).
  {
    simpl. split; trivial. split; trivial. split; trivial.
  }
  specialize(HaddrNotInLists0 (a::klist) HklistRec). simpl in HaddrNotInLists0. apply not_or_and in HaddrNotInLists0.
  apply HaddrNotInLists0.
Qed.

Lemma isListOfKernelsEqPADDR partition (addr:paddr) newEntry kernList s0:
addr + nextoffset <= maxAddr
-> (forall klist, isListOfKernels klist partition s0 -> ~ In addr klist)
-> isListOfKernels kernList partition {|
                                        currentPartition := currentPartition s0;
                                        memory := add (CPaddr (addr+nextoffset)) (PADDR newEntry) (memory s0) beqAddr
                                      |}
-> isListOfKernels kernList partition s0.
Proof.
intros HlebNextMax HaddrNotInLists0 HisKernLists. destruct kernList as [ | kernel kernList].
- intuition.
- simpl in *. destruct HisKernLists as [pdentry (HlookupPart & HbeqStructNull & Hstruct & HisKernLists)].
  destruct (beqAddr (CPaddr (addr+nextoffset)) partition) eqn:HbeqNextPart; try(exfalso; congruence).
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists pdentry.
  split; trivial. split; trivial. split; trivial.
  apply isListOfKernelsAuxEqPADDR with addr newEntry; trivial.
  + assert(Hklist: isListOfKernels [kernel] partition s0).
    {
      simpl. exists pdentry. split; trivial. split; trivial. split; trivial.
    }
    specialize(HaddrNotInLists0 [kernel] Hklist). simpl in HaddrNotInLists0. apply not_or_and in HaddrNotInLists0.
    apply not_eq_sym. apply HaddrNotInLists0.
  + intros klist Hklist. assert(HklistRec: isListOfKernels (kernel::klist) partition s0).
    {
      simpl. exists pdentry. split; trivial. split; trivial. split; trivial.
    }
    specialize(HaddrNotInLists0 (kernel::klist) HklistRec). simpl in HaddrNotInLists0.
    apply not_or_and in HaddrNotInLists0. apply HaddrNotInLists0.
Qed.

Lemma getKSEntriesInStructAuxToIndexAux n (idx:index) block baseBlock s:
idx < n
-> In block (filterOptionPaddr (getKSEntriesInStructAux n baseBlock s idx))
-> exists kernIdx:index, kernIdx <= idx /\ block = CPaddr (baseBlock + kernIdx).
Proof.
revert idx. induction n; simpl; intros idx HltIdxN HblockInStruct; try(lia).
destruct (Paddr.addPaddrIdx baseBlock idx) eqn:Hadd; try(simpl in HblockInStruct; exfalso; congruence).
destruct (lookup p (memory s) beqAddr) eqn:HlookupP; try(simpl in HblockInStruct; exfalso; congruence).
destruct v; try(simpl in HblockInStruct; exfalso; congruence). unfold Paddr.addPaddrIdx in *.
assert(HpEq: p = CPaddr (baseBlock + idx)).
{
  unfold CPaddr. destruct (le_dec (baseBlock + idx) maxAddr); try(exfalso; congruence). injection Hadd as Hadd.
  subst p. f_equal.
}
destruct (beqAddr block p) eqn:HbeqBlockP.
- rewrite <-DTL.beqAddrTrue in HbeqBlockP. subst p. exists idx. split. lia. assumption.
- rewrite <-beqAddrFalse in *. apply not_eq_sym in HbeqBlockP. destruct (indexEq idx zero) eqn:HbeqIdxZero.
  {
    simpl in HblockInStruct. exfalso. destruct HblockInStruct as [Hcontra | Hfalse]; congruence.
  }
  destruct (Index.pred idx) eqn:Hpred; try(simpl in HblockInStruct; exfalso; congruence). simpl in HblockInStruct.
  destruct HblockInStruct as [Hcontra | HblockInStruct]; try(exfalso; congruence).
  unfold Index.pred in *. destruct (gt_dec idx 0); try(exfalso; congruence). injection Hpred as Hpred.
  assert(HltIdxNRec: i < n).
  { subst i. simpl. lia. }
  specialize(IHn i HltIdxNRec HblockInStruct). destruct IHn as [kernIdx (HlebIdxI & Hblock)]. exists kernIdx.
  split; trivial. subst i. simpl in HlebIdxI. lia.
Qed.

Lemma getKSEntriesInStructAuxToIndex block baseBlock s:
In block (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1) baseBlock s (CIndex (kernelStructureEntriesNb-1))))
-> exists kernIdx:index, kernIdx < kernelStructureEntriesNb /\ block = CPaddr (baseBlock + kernIdx).
Proof.
intro HblockInStruct. pose proof KSEntriesNbLessThanMaxIdx.
assert(HlebIdxMax: CIndex (kernelStructureEntriesNb - 1) < maxIdx+1).
{
  unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). cbn -[kernelStructureEntriesNb].
  lia.
}
pose proof (getKSEntriesInStructAuxToIndexAux (maxIdx+1) (CIndex (kernelStructureEntriesNb-1)) block baseBlock s
  HlebIdxMax HblockInStruct) as Hres. destruct Hres as [kernIdx (HlebIdxKernEntries & Hblock)]. exists kernIdx.
split; trivial. unfold CIndex in HlebIdxKernEntries. destruct (le_dec (kernelStructureEntriesNb-1) maxIdx); try(lia).
cbn -[kernelStructureEntriesNb] in HlebIdxKernEntries. pose proof KSEntriesNbNotZero. lia.
Qed.

Lemma getFreeSlotsListRecEqPADDR freeslotaddr addr newEntry s0 n nbfreeslotsleft:
isPADDR addr s0
-> beqAddr addr freeslotaddr = false
-> getFreeSlotsListRec n freeslotaddr {|
                                        currentPartition := currentPartition s0;
                                        memory := add addr (PADDR newEntry) (memory s0) beqAddr
                                      |} nbfreeslotsleft
    = getFreeSlotsListRec n freeslotaddr s0 nbfreeslotsleft.
Proof.
intro HaddrIsPADDR. revert freeslotaddr nbfreeslotsleft.
set(s := {| currentPartition := currentPartition s0; memory := _ |}).
induction n; intros freeslotaddr nbfreeslotsleft HbeqFreeAddr; simpl; trivial. rewrite HbeqFreeAddr.
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup freeslotaddr (memory s0) beqAddr) eqn:HlookupFree; trivial. destruct v; trivial.
destruct (Index.pred nbfreeslotsleft) eqn:Hpred; trivial. f_equal.
specialize(IHn (endAddr (blockrange b)) i).
destruct (beqAddr addr (endAddr (blockrange b))) eqn:HbeqEndFree.
- rewrite <-DTL.beqAddrTrue in HbeqEndFree. rewrite <-HbeqEndFree in *. repeat rewrite FreeSlotsListRec_unroll.
  unfold getFreeSlotsListAux. simpl. destruct n; intuition. rewrite beqAddrTrue. unfold isPADDR in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  trivial.
- rewrite <-beqAddrFalse in *. apply IHn; trivial.
Qed.

Lemma getFreeSlotsListRecNext block bentry n (nidx:index) baseBlock s:
lookup block (memory s) beqAddr = Some (BE bentry)
-> isBE (endAddr (blockrange bentry)) s
-> nidx < maxIdx
-> In block (filterOptionPaddr (getFreeSlotsListRec n baseBlock s nidx))
-> In (endAddr (blockrange bentry)) (filterOptionPaddr (getFreeSlotsListRec (S n) baseBlock s (CIndex (nidx+1)))).
Proof.
intros HlookupBlock HendIsBE. revert baseBlock nidx. induction n; intros baseBlock nidx HltIdxMax HblockInList;
  simpl in HblockInList; try(exfalso; congruence).
destruct (lookup baseBlock (memory s) beqAddr) eqn:HlookupBase; try(simpl in HblockInList; exfalso; congruence).
destruct v; try(simpl in HblockInList; exfalso; congruence).
- unfold Index.pred in *. destruct (gt_dec nidx 0) eqn:Hgt; try(simpl in HblockInList; exfalso; congruence).
  simpl in HblockInList. set(succ := S n). cbn -[succ nullAddr]. rewrite HlookupBase.
  assert(Hnext: Index.pred (CIndex (nidx + 1)) = Some nidx).
  {
    unfold CIndex. destruct (le_dec (nidx + 1) maxIdx); try(lia). unfold Index.pred. simpl.
    destruct (gt_dec (nidx + 1) 0); try(lia). f_equal. apply index_eq_i. simpl. lia.
  }
  rewrite Hnext. cbn -[succ nullAddr]. right.
  set(idxPred := {| i := nidx - 1; Hi := StateLib.Index.pred_obligation_1 nidx g |}). fold idxPred in HblockInList.
  assert(i idxPred = nidx -1) by (simpl; reflexivity). unfold isBE in *.
  assert(HltIdxMaxRec: idxPred < maxIdx) by lia. destruct HblockInList as [HblockIsBase | HblockInListRec].
  + subst block. rewrite HlookupBase in HlookupBlock. injection HlookupBlock as HlookupBlock. subst b. simpl.
    destruct (lookup (endAddr (blockrange bentry)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). unfold Index.pred. rewrite Hgt. simpl. left. reflexivity.
  + specialize(IHn (endAddr (blockrange b)) idxPred HltIdxMaxRec HblockInListRec).
    assert(HnextIsIdx: CIndex (idxPred + 1) = nidx).
    {
      unfold CIndex. destruct (le_dec (idxPred + 1) maxIdx); try(lia). apply index_eq_i. simpl. lia.
    }
    rewrite HnextIsIdx in *. assumption.
- destruct (beqAddr baseBlock nullAddr); simpl in HblockInList; exfalso; congruence.
Qed.

Lemma getFreeSlotsListRecNextLenBounded block bentry n (nidx:index) baseBlock s:
lookup block (memory s) beqAddr = Some (BE bentry)
-> isBE (endAddr (blockrange bentry)) s
-> nidx > length (filterOptionPaddr (getFreeSlotsListRec n baseBlock s nidx))
-> In block (filterOptionPaddr (getFreeSlotsListRec n baseBlock s nidx))
-> In (endAddr (blockrange bentry)) (filterOptionPaddr (getFreeSlotsListRec (S n) baseBlock s nidx)).
Proof.
intros HlookupBlock HendIsBE. revert baseBlock nidx. induction n; intros baseBlock nidx HgtIdxLen HblockInList;
  simpl in HblockInList; try(exfalso; congruence). simpl in HgtIdxLen.
destruct (lookup baseBlock (memory s) beqAddr) eqn:HlookupBase; try(simpl in HblockInList; exfalso; congruence).
destruct v; try(simpl in HblockInList; exfalso; congruence).
- unfold Index.pred in *. destruct (gt_dec nidx 0) eqn:Hgt; try(simpl in HgtIdxLen; lia). simpl in HgtIdxLen.
  simpl in HblockInList. set(succ := S n). cbn -[succ nullAddr]. rewrite HlookupBase. unfold Index.pred. rewrite Hgt.
  cbn -[succ nullAddr]. right. set(idxPred := {| i := nidx - 1; Hi := StateLib.Index.pred_obligation_1 nidx g |}).
  fold idxPred in HblockInList. fold idxPred in HgtIdxLen.
  assert(i idxPred = nidx -1) by (simpl; reflexivity). unfold isBE in *.
  assert(HgtIdxLenRec: idxPred > length (filterOptionPaddr (getFreeSlotsListRec n (endAddr (blockrange b)) s
    idxPred))) by lia. destruct HblockInList as [HblockIsBase | HblockInListRec].
  + subst block. rewrite HlookupBase in HlookupBlock. injection HlookupBlock as HlookupBlock. subst b. simpl.
    destruct (lookup (endAddr (blockrange bentry)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). unfold Index.pred. destruct (gt_dec idxPred 0).
    * simpl. left. reflexivity.
    * assert(Hcontra: i idxPred = 0) by lia. rewrite Hcontra in HgtIdxLenRec. lia.
  + specialize(IHn (endAddr (blockrange b)) idxPred HgtIdxLenRec HblockInListRec). assumption.
- destruct (beqAddr baseBlock nullAddr); simpl in HblockInList; exfalso; congruence.
Qed.

Lemma getFreeSlotsListRecMaxLen block n nidx s:
length (filterOptionPaddr (getFreeSlotsListRec n block s nidx)) <= min n nidx.
Proof.
revert block nidx. induction n; simpl getFreeSlotsListRec; intros; try(simpl; lia).
destruct (lookup block (memory s) beqAddr); try(simpl; lia). destruct v; try(simpl; lia).
- destruct (Index.pred nidx) eqn:Hpred; try(simpl; lia). specialize(IHn (endAddr (blockrange b)) i). simpl.
  assert(Hnidx: ADT.i nidx = S i).
  {
    unfold Index.pred in Hpred. destruct (gt_dec nidx 0); try(exfalso; congruence). injection Hpred as Hpred.
    subst i. simpl. lia.
  }
  rewrite Hnidx. lia.
- destruct (beqAddr block nullAddr); simpl; lia.
Qed.

Lemma optionIsInFilter addr addrList:
In (SomePaddr addr) addrList
<-> In addr (filterOptionPaddr addrList).
Proof.
induction addrList as [ | firstAddr addrList]; simpl; try(intuition; congruence). split.
- intro Hsome. destruct Hsome as [Hfirst | HsomeRec].
  + rewrite Hfirst. simpl. left. reflexivity.
  + destruct firstAddr; try(apply IHaddrList; assumption). simpl. right. apply IHaddrList; assumption.
- intro Hin. destruct firstAddr.
  + simpl in Hin. destruct Hin as [Hleft | Hright].
    * left. subst p. reflexivity.
    * right. apply IHaddrList; assumption.
  + right. apply IHaddrList; assumption.
Qed.

Lemma filterOptNoDup addrList:
NoDup addrList
-> NoDup (filterOptionPaddr addrList).
Proof.
induction addrList; simpl; intro HnoDup; try(apply NoDup_nil). apply NoDup_cons_iff in HnoDup.
destruct HnoDup as (HaNotInList & HnoDup). destruct a; try(apply IHaddrList; assumption). apply NoDup_cons.
- contradict HaNotInList. apply optionIsInFilter; assumption.
- apply IHaddrList; assumption.
Qed.

Lemma freeIsNotNull block n firstFree s nidx: nullAddrExists s
-> In (SomePaddr block) (getFreeSlotsListRec n firstFree s nidx) -> block <> nullAddr.
Proof.
intro Hnull. revert firstFree nidx. induction n; simpl; intros firstFree nidx HblockIn;
  try(destruct HblockIn as [Hcontra | Hcontra]; exfalso; congruence). intro Hcontra. unfold nullAddrExists in *.
destruct (lookup firstFree (memory s) beqAddr) eqn:HlookupFirst; try(simpl in *; intuition; congruence).
unfold isPADDR in *. destruct v; try(simpl in *; intuition; congruence).
- destruct (Index.pred nidx); try(simpl in *; intuition; congruence). simpl in HblockIn.
  destruct HblockIn as [HblockIsFirst | HblockInRec].
  + injection HblockIsFirst as HblockIsFirst. subst firstFree. subst block. rewrite HlookupFirst in *. congruence.
  + apply IHn in HblockInRec. congruence.
- destruct (beqAddr firstFree nullAddr); simpl in *; intuition; congruence.
Qed.

Lemma getFreeSlotsListRecN n1 n2 blockBase s (nidx1 nidx2: index) addr:
n1 <= n2
-> nidx1 <= nidx2
-> In (SomePaddr addr) (getFreeSlotsListRec n1 blockBase s nidx1)
-> In (SomePaddr addr) (getFreeSlotsListRec n2 blockBase s nidx2).
Proof.
revert n2 blockBase nidx1 nidx2. induction n1; simpl; intros n2 blockBase nidx1 nidx2 HlebN HlebIdx HaddrIn;
  try(destruct HaddrIn; exfalso; congruence).
assert(Hn2: n2 = S(n2-1)) by lia. rewrite Hn2 in *. simpl.
destruct (lookup blockBase (memory s) beqAddr); try(congruence). destruct v; try(congruence).
destruct (Index.pred nidx1) eqn:Hpred1; try(exfalso; simpl in HaddrIn; destruct HaddrIn; congruence).
unfold Index.pred in *. destruct (gt_dec nidx1 0); try(exfalso; congruence). injection Hpred1 as Hpred1.
destruct (gt_dec nidx2 0); try(lia). simpl in *.
destruct HaddrIn as [HaddrIsBase | HaddrInRec]; try(left; assumption). right.
set(newNidx2 := {| i := nidx2 - 1; Hi := StateLib.Index.pred_obligation_1 nidx2 g0 |}).
assert(HlebNRec: n1 <= n2-1) by lia. assert(HlebIdxRec: i <= newNidx2) by (subst; simpl; lia).
specialize(IHn1 (n2-1) (endAddr (blockrange b)) i newNidx2 HlebNRec HlebIdxRec HaddrInRec). assumption.
Qed.

Lemma getFreeSlotsListRecNBound n1 n2 blockBase s (nidx: index):
n1 <= n2
-> n1 > nidx
-> getFreeSlotsListRec n1 blockBase s nidx = getFreeSlotsListRec n2 blockBase s nidx.
Proof.
revert n2 blockBase nidx. induction n1; simpl; intros n2 blockBase nidx HlebN HgtIdx; try(lia).
assert(Hn2: n2 = S(n2-1)) by lia. rewrite Hn2 in *. simpl.
destruct (lookup blockBase (memory s) beqAddr); try(congruence). destruct v; try(congruence).
destruct (Index.pred nidx) eqn:Hpred; trivial. f_equal. apply IHn1; try(lia). unfold Index.pred in *.
destruct (gt_dec nidx 0); try(exfalso; congruence). injection Hpred as Hpred. rewrite <-Hpred. simpl. lia.
Qed.

Lemma wellFormedFreeSlotsListSplit list1 list2:
wellFormedFreeSlotsList list1 <> False
-> wellFormedFreeSlotsList list2 <> False
-> wellFormedFreeSlotsList (list1 ++ list2) <> False.
Proof.
revert list2. induction list1 as [ | el list1]; simpl; intros list2 HwellFormed1 HwellFormed2; trivial.
destruct el; auto.
Qed.

Lemma getKSEntriesAuxEqPDTNewStruct n kernel partition newPDentry s:
nextKernelIsValid s
-> nullAddrExists s
-> isPDT partition s
-> isKS kernel s
-> getKSEntriesAux n kernel {|
                              currentPartition := currentPartition s;
                              memory := add partition (PDT newPDentry) (memory s) beqAddr
                            |} = getKSEntriesAux n kernel s.
Proof.
intros HnextValid Hnull HpartIsPDT. revert kernel. unfold nullAddrExists in *. unfold isPADDR in *.
induction n; simpl; intros kernel HkernIsKS; trivial.
unfold Paddr.addPaddrIdx in *. specialize(HnextValid kernel HkernIsKS). unfold isPDT in *.
destruct HnextValid as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]).
destruct (le_dec (kernel + nextoffset) maxAddr); trivial.
destruct (beqAddr partition
  {| p := kernel+nextoffset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 kernel nextoffset l |}) eqn:HbeqPartNext.
{
  rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst partition. rewrite HlookupNext in *. exfalso; congruence.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupNext in *.
destruct (beqAddr partition nextAddr) eqn:HbeqPartNextKS.
{
  rewrite <-DTL.beqAddrTrue in HbeqPartNextKS. subst partition.
  destruct (lookup nextAddr (memory s) beqAddr); trivial. destruct v; try(exfalso; congruence); trivial.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
assert(HeqStruct: getKSEntriesInStructAux (maxIdx + 1) kernel
  {|
    currentPartition := currentPartition s; memory := add partition (PDT newPDentry) (memory s) beqAddr
  |} (CIndex 7) = getKSEntriesInStructAux (maxIdx + 1) kernel s (CIndex 7)).
{
  apply getKSEntriesInStructAuxEqPDT.
  - intro Hcontra. subst kernel. unfold isKS in *. destruct (lookup partition (memory s) beqAddr); try(congruence).
    destruct v; congruence.
  - unfold isBE. destruct (lookup partition (memory s) beqAddr); try(congruence).
    destruct v; congruence.
}
destruct (lookup nextAddr (memory s) beqAddr) eqn:HlookupNextKS; trivial. destruct v; trivial.
- assert(HnextIsKS: isKS nextAddr s).
  {
    destruct Hnext as [Hres | Hcontra]; trivial. exfalso. subst nextAddr. rewrite HlookupNextKS in *. congruence.
  }
  specialize(IHn nextAddr HnextIsKS). rewrite IHn. rewrite HeqStruct. f_equal.
- unfold isKS in Hnext. rewrite HlookupNextKS in *. destruct Hnext as [Hcontra | Hnext]; try(exfalso; congruence).
  subst nextAddr. rewrite beqAddrTrue. assumption.
Qed.

Lemma getKSEntriesEqPDTNewStructNotInPart partition changedPart newPDentry s:
nextKernelIsValid s
-> nullAddrExists s
-> StructurePointerIsKS s
-> isPDT changedPart s
-> beqAddr changedPart partition = false
-> getKSEntries partition {|
                            currentPartition := currentPartition s;
                            memory := add changedPart (PDT newPDentry) (memory s) beqAddr
                          |} = getKSEntries partition s.
Proof.
intros HnextValid Hnull Hstruct HchangedIsPDT HbeqChangedPart. unfold getKSEntries. simpl lookup.
rewrite HbeqChangedPart. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull; trivial. rewrite <-beqAddrFalse in *.
specialize(Hstruct partition p HlookupPart HbeqStructNull). apply getKSEntriesAuxEqPDTNewStruct; trivial.
Qed.

Lemma getKSEntriesEqPDTNewStruct partition pdentry newKern newPDentry s:
nextKernelIsValid s
-> nullAddrExists s
-> structure newPDentry = newKern
-> beqAddr newKern nullAddr = false
-> lookup partition (memory s) beqAddr = Some(PDT pdentry)
-> isKS newKern s
-> lookup (CPaddr (newKern + nextoffset)) (memory s) beqAddr = Some(PADDR (structure pdentry))
-> (structure pdentry = nullAddr
    \/ (isKS (structure pdentry) s
        /\ (forall kernList, isListOfKernelsAux kernList (structure pdentry) s
            -> length kernList <= maxNbPrepare - 1)))
-> getKSEntries partition {|
                            currentPartition := currentPartition s;
                            memory := add partition (PDT newPDentry) (memory s) beqAddr
                          |}
    = (getKSEntriesInStructAux (maxIdx+1) newKern s (CIndex (kernelStructureEntriesNb-1)))
        ++ getKSEntries partition s.
Proof.
intros HnextValid Hnull HnewStruct HbeqNewNull HlookupPart HnewIsKS HlookupNext HlenKernList. unfold getKSEntries.
simpl lookup. rewrite beqAddrTrue. rewrite HnewStruct. rewrite HbeqNewNull. rewrite HlookupPart.
pose proof maxNbPrepareNotZero. replace maxNbPrepare with (S (maxNbPrepare-1)) at 1; try(lia).
cbn -[maxNbPrepare nullAddr]. unfold CPaddr in HlookupNext. unfold Paddr.addPaddrIdx.
assert(HnextValidCopy: nextKernelIsValid s) by assumption. specialize(HnextValid newKern HnewIsKS).
destruct HnextValid as (HlebNextMax & [nextAddr (HlookupNextAnc & Hnext)]).
destruct (le_dec (newKern + nextoffset) maxAddr); try(lia).
destruct (beqAddr partition
  {| p := newKern+nextoffset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 newKern nextoffset l |}) eqn:HbeqPartNext.
{ rewrite <-DTL.beqAddrTrue in HbeqPartNext. subst partition. exfalso; congruence. }
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
replace (StateLib.Paddr.addPaddrIdx_obligation_1 newKern nextoffset l) with
  (ADT.CPaddr_obligation_1 (newKern + nextoffset) l); try(apply proof_irrelevance). rewrite HlookupNext.
specialize(HlookupNextAnc (ADT.CPaddr_obligation_1 (newKern + nextoffset) l)). rewrite HlookupNext in HlookupNextAnc.
injection HlookupNextAnc as HlookupNextAnc. subst nextAddr. unfold nullAddrExists in *.
destruct (beqAddr partition (structure pdentry)) eqn:HbeqPartStruct.
{
  rewrite <-DTL.beqAddrTrue in HbeqPartStruct. subst partition. unfold isKS in Hnext. rewrite HlookupPart in *.
  exfalso. destruct Hnext as [Hcontra | HcontraNull]; try(congruence). unfold isPADDR in *. rewrite HcontraNull in *.
  rewrite HlookupPart in *. congruence.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
assert(HeqStruct: getKSEntriesInStructAux (maxIdx + 1) newKern
  {|
    currentPartition := currentPartition s; memory := add partition (PDT newPDentry) (memory s) beqAddr
  |} (CIndex 7) = getKSEntriesInStructAux (maxIdx + 1) newKern s (CIndex 7)).
{
  apply getKSEntriesInStructAuxEqPDT.
  - intro Hcontra. rewrite Hcontra in *. unfold isKS in *. rewrite HlookupPart in *. congruence.
  - unfold isBE. rewrite HlookupPart. intuition.
}
destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
- rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  rewrite HeqStruct. apply eq_sym. apply app_nil_r.
- rewrite <-beqAddrFalse in *. destruct Hnext as [HnextIsKS | Hcontra]; try(exfalso; congruence). unfold isKS in *.
  destruct (lookup (structure pdentry) (memory s) beqAddr) eqn:HlookupNextAnc; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HeqStruct. f_equal. rewrite Nat.sub_add; try(lia).
  assert(HeqRest: getKSEntriesAux maxNbPrepare (structure pdentry)
    {|
      currentPartition := currentPartition s; memory := add partition (PDT newPDentry) (memory s) beqAddr
    |} = getKSEntriesAux maxNbPrepare (structure pdentry) s).
  {
    apply getKSEntriesAuxEqPDTNewStruct; trivial.
    - unfold isPDT. rewrite HlookupPart. trivial.
    - unfold isKS. rewrite HlookupNextAnc. assumption.
  }
  rewrite HeqRest. apply eq_sym. apply getKSEntriesAuxRemoveExtraFuelEq; trivial. unfold isKS. rewrite HlookupNextAnc.
  assumption. intros kernList HkernList. destruct HlenKernList as [Hcontra | HlenKernList]; try(exfalso; congruence).
  destruct HlenKernList as (_ & HlenKernList). specialize(HlenKernList kernList HkernList). lia.
Qed.

Lemma indexEqRefl idx: indexEq idx idx = true.
Proof.
apply beqIdxTrue. reflexivity.
Qed.

Lemma index_neq_i (idx1 idx2: index): idx1 <> idx2 <-> i idx1 <> i idx2.
Proof.
split.
- intro HbeqIdxs. contradict HbeqIdxs. destruct idx1. destruct idx2. simpl in *. subst i0. f_equal.
  apply proof_irrelevance.
- intro HbeqIdxsI. contradict HbeqIdxsI. destruct idx1. destruct idx2. simpl. injection HbeqIdxsI as HbeqIdxsI.
  assumption.
Qed.

Lemma nbKernInStructEq n kernel s (idx:index):
BlocksRangeFromKernelStartIsBE s
-> nullAddrExists s
-> isKS kernel s
-> n > idx
-> idx < kernelStructureEntriesNb
-> length (filterOptionPaddr (getKSEntriesInStructAux n kernel s idx)) = idx+1.
Proof.
intros HblockRange Hnull HkernIsKS. revert idx. induction n; simpl; intros idx HgtNIdx HltIdxKernEntries; try(lia).
specialize(HblockRange kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *. unfold CPaddr in HblockRange.
unfold Paddr.addPaddrIdx. unfold nullAddrExists in *. destruct (le_dec (kernel + idx) maxAddr).
- replace (StateLib.Paddr.addPaddrIdx_obligation_1 kernel idx l) with (ADT.CPaddr_obligation_1 (kernel + idx) l);
    try(apply proof_irrelevance).
  destruct (lookup {| p := kernel + idx; Hp := ADT.CPaddr_obligation_1 (kernel + idx) l |} (memory s) beqAddr);
    try(exfalso; congruence). destruct v; try(exfalso; congruence).
  destruct (indexEq idx zero) eqn:HbeqIdxZero.
  + simpl. apply beqIdxTrue in HbeqIdxZero. subst idx. unfold zero. cbn. reflexivity.
  + unfold Index.pred. apply beqIdxFalse in HbeqIdxZero. apply index_neq_i in HbeqIdxZero. unfold zero in HbeqIdxZero.
    cbn in HbeqIdxZero. destruct (gt_dec idx 0); try(lia). simpl. rewrite IHn; simpl; lia.
- unfold isPADDR in *. replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (kernel + idx) n0 |} with nullAddr in *;
    try(unfold nullAddr; unfold CPaddr; cbn; f_equal; apply proof_irrelevance). exfalso.
  destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
Qed.

Lemma nbKernEqAux n kern s:
nullAddrExists s
-> nextKernelIsValid s
-> BlocksRangeFromKernelStartIsBE s
-> isKS kern s
-> n > length (completeListOfKernelsAux n kern s)
-> length (filterOptionPaddr (getKSEntriesAux n kern s))
    = length (completeListOfKernelsAux n kern s) * kernelStructureEntriesNb + kernelStructureEntriesNb.
Proof.
intros Hnull HnextValid HblockRange. revert kern. induction n; intros kern HkernIsKS HgtNZero; try(simpl; lia).
cbn -[kernelStructureEntriesNb nullAddr].
assert(HnextValidCopy: nextKernelIsValid s) by assumption. simpl in HgtNZero. unfold CPaddr in HgtNZero.
specialize(HnextValid kern HkernIsKS). destruct HnextValid as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]).
unfold Paddr.addPaddrIdx. unfold CPaddr. destruct (le_dec (kern + nextoffset) maxAddr); try(lia). rewrite HlookupNext.
rewrite HlookupNext in *. unfold nullAddrExists in *. unfold isPADDR in *. pose proof KSEntriesNbLessThanMaxIdx.
assert(HidxEq: kernelStructureEntriesNb-1 = CIndex (kernelStructureEntriesNb-1)).
{
  unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). simpl. reflexivity.
}
assert(HgtMaxKernEntries: maxIdx + 1 > CIndex (kernelStructureEntriesNb - 1)) by (rewrite <-HidxEq; lia).
assert(HltIdxKernEntries: CIndex (kernelStructureEntriesNb-1) < kernelStructureEntriesNb)
  by (rewrite <-HidxEq; cbn; lia).
pose proof (nbKernInStructEq (maxIdx+1) kern s (CIndex (kernelStructureEntriesNb-1)) HblockRange Hnull HkernIsKS
  HgtMaxKernEntries HltIdxKernEntries) as HlentStruct. rewrite <-HidxEq in HlentStruct.
rewrite Nat.sub_add in HlentStruct; try(lia).
destruct Hnext as [HnextIsKS | HnextIsNull].
- specialize(IHn nextAddr HnextIsKS). unfold isKS in *. specialize(HnextValidCopy nextAddr HnextIsKS).
  destruct (lookup nextAddr (memory s) beqAddr) eqn:HlookupNextAddr; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). destruct (beqAddr nextAddr nullAddr) eqn:HbeqNextNull.
  {
    rewrite <-DTL.beqAddrTrue in HbeqNextNull. subst nextAddr. rewrite HlookupNextAddr in *. exfalso; congruence.
  }
  destruct (Nat.eqb n 0) eqn:HbeqNZero.
  { apply Nat.eqb_eq in HbeqNZero. subst n. simpl in HgtNZero. lia. }
  apply Nat.eqb_neq in HbeqNZero. assert(HgtNZeroRec: n > length (completeListOfKernelsAux n nextAddr s)).
  { simpl in HgtNZero. lia. }
  rewrite filterOptionPaddrSplit. rewrite length_app. rewrite HlentStruct. specialize(IHn HgtNZeroRec).
  rewrite IHn. simpl. lia.
- subst nextAddr. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite beqAddrTrue. rewrite HlentStruct. simpl. reflexivity.
Qed.

Lemma nbKernEq partition pdentry s:
StructurePointerIsKS s
-> FirstFreeSlotPointerIsBEAndFreeSlot s
-> nullAddrExists s
-> nextKernelIsValid s
-> BlocksRangeFromKernelStartIsBE s
-> maxNbPrepareIsMaxNbKernels s
-> lookup partition (memory s) beqAddr = Some(PDT pdentry)
-> length (filterOptionPaddr (getKSEntries partition s))
    = length (completeListOfKernels (structure pdentry) s)*kernelStructureEntriesNb.
Proof.
intros Hstruct HfirstIsBE Hnull HnextValid HblockRange HmaxNbPrep HlookupPart.
pose proof (completeKernListIsListOfKern partition pdentry s Hnull HnextValid HlookupPart) as HcompleteIsKernList.
assert(HmaxNbPrepCopy: maxNbPrepareIsMaxNbKernels s) by assumption.
specialize(HmaxNbPrep partition (completeListOfKernels (structure pdentry) s) HcompleteIsKernList) as Hlen.
unfold getKSEntries. rewrite HlookupPart. unfold nullAddrExists in *. unfold isPADDR in *.
destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
- simpl. rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. unfold completeListOfKernels.
  destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  simpl. reflexivity.
- rewrite <-beqAddrFalse in *. specialize(Hstruct partition pdentry HlookupPart HbeqStructNull).
  rewrite Nat.add_1_r. cbn -[maxNbPrepare kernelStructureEntriesNb nullAddr]. unfold completeListOfKernels in *.
  assert(HnextValidBis: nextKernelIsValid s) by assumption.
  specialize(HnextValid (structure pdentry) Hstruct).
  destruct HnextValid as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]). unfold Paddr.addPaddrIdx in *.
  destruct (le_dec (structure pdentry + nextoffset) maxAddr); try(lia). rewrite HlookupNext in *.
  assert(HstructBis: isKS (structure pdentry) s) by assumption. unfold isKS in Hstruct.
  destruct (lookup (structure pdentry) (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite Hstruct in *. unfold zero in *. rewrite indexEqRefl in *.
  cbn -[maxNbPrepare kernelStructureEntriesNb nullAddr] in *. pose proof maxIdxBiggerThanNbOfKernels.
  assert(HidxEq: kernelStructureEntriesNb-1 = CIndex (kernelStructureEntriesNb-1)).
  {
    unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). cbn -[kernelStructureEntriesNb].
    reflexivity.
  }
  assert(HgtMaxKernIdx: maxIdx+1 > CIndex (kernelStructureEntriesNb-1)).
  { rewrite <-HidxEq. lia. }
  assert(HltIdx: CIndex (kernelStructureEntriesNb-1) < kernelStructureEntriesNb).
  { rewrite <-HidxEq. cbn. lia. }
  pose proof (nbKernInStructEq (maxIdx+1) (structure pdentry) s (CIndex (kernelStructureEntriesNb-1)) HblockRange
    Hnull HstructBis HgtMaxKernIdx HltIdx) as HlenStruct. destruct Hnext as [HnextIsKS | HnextIsNull].
  + assert(HnextIsKSCopy: isKS nextAddr s) by assumption.
    unfold isKS in HnextIsKSCopy. destruct (lookup nextAddr (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite filterOptionPaddrSplit. rewrite length_app. rewrite HlenStruct.
    rewrite <-HidxEq. assert(HeqN: completeListOfKernelsAux maxNbPrepare (structure pdentry) s
      = completeListOfKernelsAux (S (maxNbPrepare-1)) (structure pdentry) s).
    { replace (S (maxNbPrepare-1)) with maxNbPrepare; try(cbn; lia). reflexivity. }
    rewrite HeqN in *. cbn -[maxNbPrepare kernelStructureEntriesNb nullAddr] in *. unfold CPaddr.
    unfold CPaddr in Hlen. destruct (le_dec (structure pdentry + nextoffset) maxAddr); try(lia).
    rewrite HlookupNext in *. destruct (beqAddr nextAddr nullAddr) eqn:HbeqNextNull.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqNextNull. subst nextAddr. unfold isKS in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
    }
    cbn -[kernelStructureEntriesNb maxNbPrepare nullAddr] in *.
    assert(HgtMaxLen: maxNbPrepare-1 > length (completeListOfKernelsAux (maxNbPrepare - 1) nextAddr s)) by lia.
    pose proof (nbKernEqAux (maxNbPrepare-1) nextAddr s Hnull HnextValidBis HblockRange HnextIsKS HgtMaxLen) as Hres.
    assert(HeqListNext: getKSEntriesAux maxNbPrepare nextAddr s = getKSEntriesAux (maxNbPrepare-1) nextAddr s).
    {
      replace maxNbPrepare with (S (maxNbPrepare-1)) at 1; try(cbn; lia).
      apply getKSEntriesAuxRemoveExtraFuelEq; trivial. intros kernList HkernList.
      assert(HkernListFull: isListOfKernels ((structure pdentry)::(nextAddr::kernList)) partition s).
      {
        simpl. exists pdentry. rewrite <-beqAddrFalse in *. intuition. unfold CPaddr.
        destruct (le_dec (structure pdentry + nextoffset) maxAddr); try(lia). apply HlookupNext.
      }
      specialize(HmaxNbPrepCopy partition ((structure pdentry)::(nextAddr::kernList)) HkernListFull).
      simpl in HmaxNbPrepCopy. lia.
    }
    rewrite HeqListNext. rewrite Hres. lia.
  + subst nextAddr. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite beqAddrTrue. rewrite HlenStruct.
    replace maxNbPrepare with (S (maxNbPrepare-1)); try(cbn; lia).
    cbn -[kernelStructureEntriesNb maxNbPrepare nullAddr]. unfold CPaddr.
    destruct (le_dec (structure pdentry + nextoffset) maxAddr); try(lia). rewrite HlookupNext. rewrite beqAddrTrue.
    cbn -[kernelStructureEntriesNb]. lia.
Qed.

Lemma lenWellFormed l:
wellFormedFreeSlotsList l <> False -> length l = length (filterOptionPaddr l).
Proof.
induction l; simpl; intro HwellFormed; try(reflexivity). destruct a; try(exfalso; congruence). simpl.
rewrite IHl; trivial.
Qed.

Lemma sh1offsetVal: i sh1offset = kernelStructureEntriesNb.
Proof.
unfold sh1offset. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl.
reflexivity.
Qed.

Lemma scoffsetVal: i scoffset = kernelStructureEntriesNb + kernelStructureEntriesNb.
Proof.
unfold scoffset. rewrite sh1offsetVal. unfold CIndex. cbn. pose proof Constants.maxIdxBiggerThanMinBlock.
destruct (le_dec 16 maxIdx); try(lia). simpl. reflexivity.
Qed.

Lemma nextoffsetVal: i nextoffset = kernelStructureEntriesNb + kernelStructureEntriesNb + kernelStructureEntriesNb.
Proof.
unfold nextoffset. rewrite scoffsetVal. unfold CIndex. cbn. pose proof Constants.maxIdxBiggerThanMinBlock.
destruct (le_dec 24 maxIdx); try(lia). simpl. reflexivity.
Qed.

Lemma kernelStructureTotalLengthVal: i Constants.kernelStructureTotalLength = 3*kernelStructureEntriesNb+1.
Proof.
unfold Constants.kernelStructureTotalLength. rewrite nextoffsetVal. unfold CIndex. cbn.
pose proof Constants.maxIdxBiggerThanMinBlock. destruct (le_dec 25 maxIdx); try(lia). simpl. reflexivity.
Qed.

Lemma wellFormedGivesSomePaddr addr l: wellFormedFreeSlotsList l <> False
-> In addr l
-> exists someAddr, addr = SomePaddr someAddr /\ In someAddr (filterOptionPaddr l).
Proof.
induction l; simpl ; intros HwellFormed HaddrIn; try(exfalso; congruence). destruct a; try(exfalso; congruence).
destruct HaddrIn as [HisAddr | HaddrInRec].
- exists p. simpl. auto.
- specialize(IHl HwellFormed HaddrInRec). destruct IHl as [someAddr (Haddr & HaddrInFilt)]. exists someAddr. simpl.
  auto.
Qed.

Lemma blockInRangeInStructLight block kernel (idx:index) n s:
wellFormedFstShadowIfBlockEntry s
-> nullAddrExists s
-> BlocksRangeFromKernelStartIsBE s
-> isKS kernel s
-> isBE block s
-> kernel <= block
-> i idx < n
-> idx < kernelStructureEntriesNb
-> block <= kernel+idx
-> In block (filterOptionPaddr (getKSEntriesInStructAux n kernel s idx)).
Proof.
intros HwellFormed Hnull HblockRange HkernIsKS HblockIsBE HlebKernBlock. revert idx. induction n; simpl; intros idx
  HltIdxN HltIdxKernEntries HlebBlockMaxIdx; try(lia). unfold Paddr.addPaddrIdx.
assert(HBE: isBE kernel s).
{
  unfold isBE. unfold isKS in *. destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). trivial.
}
specialize (HwellFormed kernel HBE). unfold isSHE in *. unfold CPaddr in HwellFormed. unfold sh1offset in *.
unfold blkoffset in *. simpl in *. unfold nullAddrExists in *. unfold isPADDR in *.
assert(HidxEq: kernelStructureEntriesNb = CIndex kernelStructureEntriesNb).
{
  unfold CIndex. pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
  reflexivity.
}
rewrite <-HidxEq in *. assert(HblockrangeLtMax: kernel + kernelStructureEntriesNb <= maxAddr).
{
  pose proof KSEntriesNbLessThanMaxIdx. destruct (le_dec (kernel + kernelStructureEntriesNb) maxAddr); try(lia).
  assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (kernel + kernelStructureEntriesNb) n0 |} = nullAddr).
  { unfold nullAddr. unfold CPaddr. cbn. f_equal. apply proof_irrelevance. }
  rewrite HnullEq in *. exfalso. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
  destruct v; congruence.
}
destruct (le_dec (kernel + kernelStructureEntriesNb) maxAddr); try(lia).
specialize (HblockRange kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *. unfold CPaddr in *.
destruct (le_dec (kernel + idx) maxAddr); try(lia). replace (StateLib.Paddr.addPaddrIdx_obligation_1 kernel idx l0)
  with (ADT.CPaddr_obligation_1 (kernel + idx) l0); try(apply proof_irrelevance).
destruct (lookup {| p := kernel + idx; Hp := ADT.CPaddr_obligation_1 (kernel + idx) l0 |} (memory s) beqAddr);
  try(exfalso; congruence). destruct v; try(exfalso; congruence).
destruct (beqIdx idx zero) eqn:HbeqIdxZero.
- (* idx = zero *)
  rewrite <-DTL.beqIdxTrue in HbeqIdxZero. rewrite HbeqIdxZero in *. simpl. left. unfold zero in *. subst idx. cbn.
  cbn in HlebBlockMaxIdx. apply paddrEqNatEqEquiv. simpl. lia.
- (* idx <> zero *)
  rewrite <-beqIdxFalse in *. apply index_neq_i in HbeqIdxZero. cbn in HbeqIdxZero. unfold Index.pred.
  destruct (gt_dec idx 0); try(lia). simpl.
  assert(HltIdxNRec: {| i := idx - 1; Hi := StateLib.Index.pred_obligation_1 idx g |} < n) by (simpl; lia).
  assert(HltIdxKernEntriesRec: {| i := idx-1; Hi := StateLib.Index.pred_obligation_1 idx g |}
    < kernelStructureEntriesNb) by (simpl; lia).
  destruct (Nat.eqb (kernel+idx) block) eqn:HbeqIdxBlock.
  + left. apply Nat.eqb_eq in HbeqIdxBlock. apply paddrEqNatEqEquiv. simpl.
    assumption.
  + right. apply Nat.eqb_neq in HbeqIdxBlock. apply IHn; trivial. simpl. lia.
Qed.

Lemma getKSEntriesInStructAuxIsRangeAux n (kernel:paddr) s (nidx:index) off:
(forall kernIdx:index, kernIdx <= nidx -> isBE (CPaddr (kernel+off+kernIdx)) s)
-> n > nidx
-> kernel+off+nidx < maxAddr-1
-> filterOptionPaddr (getKSEntriesInStructAux n (CPaddr (kernel+off)) s nidx)
    = rev (getAllPaddrBlockAux off kernel (S nidx)).
Proof.
revert nidx. induction n; simpl; intros nidx HidxsAreBE HgtNIdx HlebIdxMax; try(lia).
assert(HidxsAreBECopy: forall kernIdx : index, kernIdx <= nidx -> isBE (CPaddr (kernel+off+kernIdx)) s) by assumption.
assert(HlebTriv: nidx <= nidx) by lia. specialize(HidxsAreBECopy nidx HlebTriv). unfold Paddr.addPaddrIdx.
unfold CPaddr in HidxsAreBECopy. unfold CPaddr. destruct (le_dec (kernel + off) maxAddr); try(lia). simpl.
destruct (le_dec (kernel+off+nidx) maxAddr); try(lia). unfold isBE in HidxsAreBECopy.
replace (StateLib.Paddr.addPaddrIdx_obligation_1 {| p:=kernel+off; Hp := ADT.CPaddr_obligation_1 (kernel+off) l |}
    nidx l0) with (ADT.CPaddr_obligation_1 (kernel + off + nidx) l0);
  try(apply proof_irrelevance).
destruct (lookup {| p := kernel+off+nidx; Hp := ADT.CPaddr_obligation_1 (kernel+off+nidx) l0 |} (memory s) beqAddr);
  try(exfalso; congruence). destruct v; try(exfalso; congruence). unfold zero. cbn.
destruct (indexEq nidx {| i := 0; Hi := ADT.CIndex_obligation_1 0 (Nat.le_0_l maxIdx) |}) eqn:HbeqIdxZero.
- apply beqIdxTrue in HbeqIdxZero. subst nidx. simpl. destruct (le_dec (off + kernel) maxAddr); try(lia). simpl.
  f_equal. apply paddrEqNatEqEquiv. simpl. lia.
- apply beqIdxFalse in HbeqIdxZero. apply index_neq_i in HbeqIdxZero. simpl in HbeqIdxZero. unfold Index.pred.
  destruct (gt_dec nidx 0); try(lia). destruct (le_dec (off + kernel) maxAddr); try(lia). simpl.
  assert(HidxsAreBERec: forall kernIdx:index,
    kernIdx <= {| i := nidx - 1; Hi := StateLib.Index.pred_obligation_1 nidx g |}
    -> isBE (CPaddr (kernel+off+kernIdx)) s).
  {
    intros kernIdx HltIdxPred. simpl in HltIdxPred. assert(HltIdxNidx: kernIdx <= nidx) by lia.
    apply HidxsAreBE; trivial.
  }
  assert(HgtNIdxRec: n > {| i := nidx-1; Hi := StateLib.Index.pred_obligation_1 nidx g |}) by (simpl; lia).
  assert(HlebIdxMaxRec: kernel+off+{| i := nidx-1; Hi := StateLib.Index.pred_obligation_1 nidx g |} < maxAddr-1)
    by (simpl; lia).
  assert(Hoff: {| p := kernel + off; Hp := ADT.CPaddr_obligation_1 (kernel + off) l |} = CPaddr (kernel+off)).
  {
    unfold CPaddr. destruct (le_dec (kernel + off) maxAddr); try(lia). apply paddrEqNatEqEquiv. reflexivity.
  }
  specialize(IHn {| i := nidx-1; Hi := StateLib.Index.pred_obligation_1 nidx g |} HidxsAreBERec HgtNIdxRec
    HlebIdxMaxRec). rewrite Hoff. rewrite IHn. simpl. destruct (le_dec (off + kernel) maxAddr); try(lia). simpl.
  assert(Hcut: getAllPaddrBlockAux (S off) kernel nidx
    = getAllPaddrBlockAux (S off) kernel (nidx-1) ++ getAllPaddrBlockAux (S off) (kernel+nidx-1) 1).
  {
    assert(Hres: getAllPaddrBlockAux (S off) kernel ((kernel+nidx-1)-kernel)
        ++ getAllPaddrBlockAux (S off) (kernel+nidx-1) ((kernel+nidx)-(kernel+nidx-1))
      = getAllPaddrBlockAux (S off) kernel ((kernel+nidx)-kernel)).
    { apply getAllPaddrBlockAuxCut; lia. }
    replace (kernel + nidx - kernel) with (i nidx) in Hres; try(lia).
    replace (kernel + nidx - (kernel + nidx-1)) with 1 in Hres; try(lia).
    replace (kernel + nidx -1 - kernel) with (nidx-1) in Hres; try(lia). auto.
  }
  assert(Hlast: getAllPaddrBlockAux (S off) (kernel + nidx - 1) 1 = [CPaddr(kernel+off + nidx)]).
  {
    simpl. unfold CPaddr. replace (S (off + (kernel + nidx - 1))) with (kernel + off + nidx); try(lia).
    destruct (le_dec (kernel + off + nidx) maxAddr); try(lia). f_equal.
  }
  rewrite Hcut. rewrite Hlast. rewrite rev_unit. rewrite <-app_comm_cons. f_equal.
  + unfold CPaddr. destruct (le_dec (kernel + off + nidx) maxAddr); try(lia). f_equal. apply proof_irrelevance.
  + f_equal. f_equal. f_equal. apply proof_irrelevance.
Qed.

Lemma getKSEntriesInStructAuxIsRange n (kernel:paddr) s (nidx:index):
(forall kernIdx:index, kernIdx <= nidx -> isBE (CPaddr (kernel+kernIdx)) s)
-> n > nidx
-> kernel+nidx < maxAddr-1
-> filterOptionPaddr (getKSEntriesInStructAux n kernel s nidx)
    = rev (getAllPaddrBlock kernel (CPaddr (kernel+nidx+1))).
Proof.
intros HidxsAreBE HgtNIdx HlebIdxMax. unfold getAllPaddrBlock.
assert(HkernEq: kernel = CPaddr (kernel+0)).
{
  unfold CPaddr. destruct (le_dec (kernel + 0) maxAddr); try(lia). apply paddrEqNatEqEquiv. simpl. lia.
}
assert(HnidxEq: (CPaddr (kernel + nidx + 1) - kernel) = S nidx).
{
  unfold CPaddr. destruct (le_dec (kernel + nidx + 1) maxAddr); try(lia). simpl. lia.
}
rewrite HnidxEq. rewrite HkernEq at 1. apply getKSEntriesInStructAuxIsRangeAux; try(lia). rewrite Nat.add_0_r.
assumption.
Qed.

Lemma isListOfKernelsEqPDTNotInPart partition newPart newEntry kernList s0:
beqAddr newPart partition = false
-> isListOfKernels kernList partition {|
                                        currentPartition := currentPartition s0;
                                        memory := add newPart (PDT newEntry) (memory s0) beqAddr
                                      |}
-> isListOfKernels kernList partition s0.
Proof.
intros HbeqParts HisKernLists. destruct kernList.
- intuition.
- simpl in *. rewrite HbeqParts in *. destruct HisKernLists as [newPdentry HisKernLists]. exists newPdentry.
  rewrite <-beqAddrFalse in HbeqParts. rewrite removeDupIdentity in *; intuition.
  apply isListOfKernelsAuxEqPDT with newPart newEntry; assumption.
Qed.

Lemma completeListOfKernelsAuxN n1 n2 kern s:
n1 <= n2
-> length (completeListOfKernelsAux n1 kern s) < n1
-> completeListOfKernelsAux n1 kern s = completeListOfKernelsAux n2 kern s.
Proof.
revert n2 kern. induction n1; simpl; intros n2 kern HlebN Hlen; try(lia). replace n2 with (S (n2-1)) in *; try(lia).
simpl. destruct (lookup (CPaddr (kern + nextoffset)) (memory s) beqAddr); trivial. destruct v; trivial.
destruct (beqAddr p nullAddr); trivial. f_equal. simpl in Hlen. apply IHn1; lia.
Qed.

Lemma lowerLenLowerBoundCompleteAux n1 n2 kern s:
n1 <= n2
-> length (completeListOfKernelsAux n1 kern s) <= length (completeListOfKernelsAux n2 kern s).
Proof.
revert n2 kern. induction n1; simpl; intros n2 kern HlebN; try(lia). replace n2 with (S (n2-1)); try(lia). simpl.
destruct (lookup (CPaddr (kern + nextoffset)) (memory s) beqAddr); trivial. destruct v; trivial.
destruct (beqAddr p nullAddr); trivial. simpl. assert(HlebNRec: n1 <= n2-1) by lia.
specialize(IHn1 (n2-1) p HlebNRec). lia.
Qed.

Lemma getAllPaddrAuxEqPADDR addr newEntry blocklist s0:
isPADDR addr s0
-> getAllPaddrAux blocklist {|
                              currentPartition := currentPartition s0;
                              memory := add addr (PADDR newEntry) (memory s0) beqAddr |}
= getAllPaddrAux blocklist s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}). intros HPDTs0.
induction blocklist as [ | el blocklist]; simpl; trivial.
destruct (beqAddr addr el) eqn:HbeqAddrEl.
- rewrite <-DTL.beqAddrTrue in HbeqAddrEl. subst el. unfold isPADDR in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). assumption.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup el (memory s0) beqAddr); trivial. destruct v; trivial. f_equal. assumption.
Qed.

Lemma getAllPaddrConfigAuxEqPADDR addr newEntry kslist s0:
isPADDR addr s0
-> getAllPaddrConfigAux kslist {|
                                 currentPartition := currentPartition s0;
                                 memory := add addr (PADDR newEntry) (memory s0) beqAddr |}
= getAllPaddrConfigAux kslist s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}). intros HSPADDRs0.
induction kslist as [ | el kslist]; simpl; trivial.
destruct (beqAddr addr el) eqn:HbeqAddrEl.
- rewrite <-DTL.beqAddrTrue in HbeqAddrEl. subst el. unfold isPADDR in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). assumption.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup el (memory s0) beqAddr); trivial. destruct v; trivial. f_equal. assumption.
Qed.

Lemma getConfigBlocksAuxEqPADDR struct addr newEntry s0 n entriesleft:
nextKernelIsValid s0
-> nullAddrExists s0
-> isPADDR addr s0
-> beqAddr addr nullAddr = false
-> isKS struct s0
-> (forall kern, In kern (filterOptionPaddr (getConfigBlocksAux n struct s0 entriesleft))
    -> kern+nextoffset <> addr)
-> getConfigBlocksAux n struct {|
                              currentPartition := currentPartition s0;
                              memory := add addr (PADDR newEntry) (memory s0) beqAddr |} entriesleft
= getConfigBlocksAux n struct s0 entriesleft.
Proof.
intros HnextValid Hnull HaddrIsPADDR HbeqAddrNull. unfold nullAddrExists in *. revert struct entriesleft.
set (s := {| currentPartition := currentPartition s0; memory := _ |}).
induction n; simpl; intros struct entriesleft HstructIsKS HaddrNotIn; trivial. unfold isPADDR in *. unfold isKS in *.
specialize(HnextValid struct HstructIsKS). destruct HnextValid as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]).
destruct (beqAddr addr struct) eqn:HbeqAddrStruct.
{
  rewrite <-DTL.beqAddrTrue in HbeqAddrStruct. subst addr. exfalso.
  destruct (lookup struct (memory s0) beqAddr); try(congruence). destruct v; congruence.
}
rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup struct (memory s0) beqAddr) eqn:HlookupStruct; trivial. destruct v; trivial.
unfold Paddr.addPaddrIdx in *. destruct (le_dec (struct + nextoffset) maxAddr); try(lia).
set(nextPADDRAddr:= {| p := struct+nextoffset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 struct nextoffset l |}).
fold nextPADDRAddr in HaddrNotIn. destruct (beqAddr addr nextPADDRAddr) eqn:HbeqAddrP.
- rewrite <-DTL.beqAddrTrue in HbeqAddrP. rewrite <-HbeqAddrP in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  destruct (Index.pred entriesleft); trivial. simpl in HaddrNotIn. exfalso.
  assert(HpropsOr: struct = struct \/ In struct (filterOptionPaddr (getConfigBlocksAux n p s0 i))) by auto.
  specialize(HaddrNotIn struct HpropsOr). rewrite HbeqAddrP in HaddrNotIn. simpl in HaddrNotIn. congruence.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. unfold nextPADDRAddr in *.
  rewrite HlookupNext in *. destruct (Index.pred entriesleft); trivial. f_equal.
  destruct Hnext as [HnextIsKS | HnextIsNull].
  + specialize (IHn nextAddr i HnextIsKS). apply IHn. intros kern HkernIn. apply HaddrNotIn. simpl. auto.
  + subst nextAddr. destruct n; simpl; trivial. rewrite beqAddrFalse in HbeqAddrNull.
    rewrite HbeqAddrNull. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    destruct (lookup nullAddr (memory s0) beqAddr); trivial. destruct v; try(exfalso; congruence). reflexivity.
Qed.

Lemma getConfigBlocksEqPADDR addr newEntry part s0:
nextKernelIsValid s0
-> nullAddrExists s0
-> StructurePointerIsKS s0
-> isPADDR addr s0
-> beqAddr addr nullAddr = false
-> (forall kern, In kern (getConfigBlocks part s0) -> kern+nextoffset <> addr)
-> getConfigBlocks part {|
                          currentPartition := currentPartition s0;
                          memory := add addr (PADDR newEntry) (memory s0) beqAddr |}
= getConfigBlocks part s0.
Proof.
intros HnextValid Hnull Hstruct HaddrIsPADDR HbeqAddrNull HaddrNotIn. unfold getConfigBlocks in *. simpl lookup.
destruct (beqAddr addr part) eqn:HbeqAddrPart.
{
  rewrite <-DTL.beqAddrTrue in HbeqAddrPart. rewrite HbeqAddrPart in *. unfold isPADDR in *.
  destruct (lookup part (memory s0) beqAddr); trivial. destruct v; trivial. exfalso; congruence.
}
rewrite <-beqAddrFalse in HbeqAddrPart. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull.
- rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. rewrite MaxIdxNextEq. simpl.
  rewrite HbeqAddrNull. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  unfold nullAddrExists in *. unfold isPADDR in *.
  destruct (lookup nullAddr (memory s0) beqAddr); trivial. destruct v; try(exfalso; congruence). reflexivity.
- rewrite <-beqAddrFalse in HbeqStructNull. specialize(Hstruct part p HlookupPart HbeqStructNull). f_equal.
  apply getConfigBlocksAuxEqPADDR; trivial.
Qed.

Lemma getConfigPaddrEqPADDR partition addr newEntry s0:
nextKernelIsValid s0
-> nullAddrExists s0
-> StructurePointerIsKS s0
-> isPADDR addr s0
-> beqAddr addr nullAddr = false
-> (forall kern, In kern (getConfigBlocks partition s0) -> kern+nextoffset <> addr)
-> getConfigPaddr partition {|
                              currentPartition := currentPartition s0;
                              memory := add addr (PADDR newEntry) (memory s0) beqAddr |}
= getConfigPaddr partition s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}).
intros HnextValid Hnull Hstruct HaddrIsPADDR HbeqAddrNull HaddrNotIn. unfold getConfigPaddr.
assert(HconfBlockEq: getConfigBlocks partition s = getConfigBlocks partition s0).
{ apply getConfigBlocksEqPADDR; trivial. }
assert(HpaddrConfEq: getAllPaddrConfigAux (getConfigBlocks partition s0) s
  = getAllPaddrConfigAux (getConfigBlocks partition s0) s0).
{ apply getAllPaddrConfigAuxEqPADDR; trivial. }
rewrite HconfBlockEq. rewrite HpaddrConfEq. simpl. destruct (beqAddr addr partition) eqn:HbeqAddrPart.
- rewrite <-DTL.beqAddrTrue in HbeqAddrPart. subst addr. unfold isPADDR in *.
  destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
Qed.

Lemma completeKernListIsConfigAux n kern (nidx:index) s:
nullAddrExists s
-> nextKernelIsValid s
-> isKS kern s
-> n > nidx
-> nidx >= length(kern::completeListOfKernelsAux nidx kern s)
-> filterOptionPaddr (getConfigBlocksAux n kern s nidx) = kern::completeListOfKernelsAux nidx kern s.
Proof.
intros Hnull HnextValid. revert kern nidx. unfold nullAddrExists in *. unfold isPADDR in *.
induction n; simpl; intros kern nidx HkernIsKS HgtNIdx HgebIdxLen; try(lia).
specialize(HnextValid kern HkernIsKS). destruct HnextValid as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]).
assert(nidx > 0) by lia. replace (i nidx) with (S (nidx -1)) in HgebIdxLen; try(lia).
replace (i nidx) with (S (nidx -1)); try(lia). simpl in *.
unfold isKS in *. destruct (lookup kern (memory s) beqAddr); try(exfalso; congruence).
destruct v; try(exfalso; congruence). unfold Paddr.addPaddrIdx. unfold CPaddr in *.
destruct (le_dec (kern + nextoffset) maxAddr); try(lia). repeat rewrite HlookupNext in *. unfold Index.pred.
destruct (gt_dec nidx 0); try(lia). simpl. f_equal.
destruct (beqAddr nextAddr nullAddr) eqn:HbeqNextNull.
- rewrite <-DTL.beqAddrTrue in HbeqNextNull. subst nextAddr. replace n with (S (n-1)); try(lia). simpl.
  destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  destruct (beqAddr p nullAddr); reflexivity.
- rewrite <-beqAddrFalse in *. destruct Hnext as [HnextIsKS | Hcontra]; try(exfalso; congruence).
  apply IHn; trivial. 1,2: simpl in *; lia.
Qed.

Lemma completeKernListIsConfig part pdentry s:
nullAddrExists s
-> nextKernelIsValid s
-> StructurePointerIsKS s
-> maxNbPrepareIsMaxNbKernels s
-> lookup part (memory s) beqAddr = Some(PDT pdentry)
-> getConfigBlocks part s = completeListOfKernels (structure pdentry) s.
Proof.
intros Hnull HnextValid Hstruct HmaxPrep HlookupPart.
assert(HcomplIsKlist: isListOfKernels (completeListOfKernels (structure pdentry) s) part s).
{ apply completeKernListIsListOfKern; assumption. }
specialize(HmaxPrep part (completeListOfKernels (structure pdentry) s) HcomplIsKlist). clear HcomplIsKlist.
unfold getConfigBlocks. unfold completeListOfKernels in *.
rewrite HlookupPart. destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
- rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. rewrite MaxIdxNextEq.
  unfold nullAddrExists in *. unfold isPADDR in *. simpl.
  destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  destruct (beqAddr p nullAddr); reflexivity.
- rewrite <-beqAddrFalse in *. specialize(Hstruct part pdentry HlookupPart HbeqStructNull). unfold isKS in *.
  assert(HstructIsKS: isKS (structure pdentry) s) by assumption.
  destruct (lookup (structure pdentry) (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite Hstruct in *. unfold zero in *. rewrite indexEqRefl in *.
  assert(HmaxPrepEq: maxNbPrepare = CIndex maxNbPrepare).
  {
    unfold CIndex. pose proof maxNbPrepareNbLessThanMaxIdx. destruct (le_dec maxNbPrepare maxIdx); try(lia).
    reflexivity.
  }
  apply eq_sym. rewrite HmaxPrepEq at 1. apply eq_sym. apply completeKernListIsConfigAux; trivial.
  + pose proof maxNbPrepareNbLessThanMaxIdx. rewrite <-HmaxPrepEq. lia.
  + rewrite <-HmaxPrepEq. lia.
Qed.

Lemma configBlocksAreKSAux n kernel currKern s nidx:
nextKernelIsValid s
-> nullAddrExists s
-> isKS currKern s
-> In kernel (filterOptionPaddr (getConfigBlocksAux n currKern s nidx))
-> isKS kernel s.
Proof.
intros HnextValid Hnull. revert currKern nidx. induction n; simpl; intros currKern nidx HcurrIsKS HkernInConf;
  try(exfalso; congruence). specialize(HnextValid currKern HcurrIsKS). unfold nullAddrExists in *.
destruct HnextValid as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]). unfold isKS in HcurrIsKS.
destruct (lookup currKern (memory s) beqAddr) eqn:HlookupCurr; try(exfalso; congruence).
destruct v; try(exfalso; congruence). unfold Paddr.addPaddrIdx in *.
destruct (le_dec (currKern + nextoffset) maxAddr); try(lia). rewrite HlookupNext in *.
destruct (Index.pred nidx) eqn:Hpred; simpl in HkernInConf; try(exfalso; congruence).
destruct HkernInConf as [HkernIsCurr | HkernInConfRec].
- subst kernel. unfold isKS. rewrite HlookupCurr. assumption.
- destruct Hnext as [HnextIsKS | HnextIsNull].
  + revert HkernInConfRec. apply IHn. assumption.
  + subst nextAddr. exfalso. destruct n; simpl in HkernInConfRec; try(congruence). unfold isPADDR in *.
    destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
    destruct (beqAddr p nullAddr); simpl in HkernInConfRec; congruence.
Qed.

Lemma configBlocksAreKS kernel partition s: nextKernelIsValid s -> StructurePointerIsKS s -> nullAddrExists s
-> In kernel (getConfigBlocks partition s) -> isKS kernel s.
Proof.
intros HnextValid Hstruct Hnull HkernInConf. unfold getConfigBlocks in *. unfold nullAddrExists in *.
destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(simpl in HkernInConf; exfalso; congruence).
destruct v; try(simpl in HkernInConf; exfalso; congruence).
destruct (beqAddr (structure p) nullAddr) eqn:HbeqStructNull.
{
  rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull in *. exfalso. rewrite MaxIdxNextEq in *.
  simpl in *. unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
  destruct v; try(congruence). destruct (beqAddr p0 nullAddr); simpl in HkernInConf; congruence.
}
rewrite <-beqAddrFalse in *. specialize(Hstruct partition p HlookupPart HbeqStructNull). revert HkernInConf.
apply configBlocksAreKSAux; assumption.
Qed.

Lemma getAllPaddrConfigAuxIncl kernList s:
(forall addr, In addr kernList -> isBE addr s)
-> incl kernList (getAllPaddrConfigAux kernList s).
Proof.
induction kernList; simpl; intros HelsAreBE addr HaddrInList; trivial.
assert(HelsAreBERec: forall addr, In addr kernList -> isBE addr s).
{
  intros addrBis HaddrBisInList. apply HelsAreBE. simpl. auto.
}
assert(HaInList: a = a \/ In a kernList) by auto. specialize(HelsAreBE a HaInList). unfold isBE in *.
destruct (lookup a (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
apply in_or_app. simpl in HaddrInList.
destruct HaddrInList as [HaIsAddr | HaddrInListRec]; try(right; apply IHkernList; assumption). left. subst a.
rewrite kernelStructureTotalLengthVal. apply getAllPaddrBlockAuxIncl; lia.
Qed.

Lemma filterAccessibleEqPADDR addr newEntry s0 blocklist:
isPADDR addr s0
-> filterAccessible blocklist {|
                                currentPartition := currentPartition s0;
                                memory := add addr (PADDR newEntry) (memory s0) beqAddr |}
    = filterAccessible blocklist s0.
Proof.
set (s := {| currentPartition := currentPartition s0; memory := _ |}).
intro HPDTaddrs0. induction blocklist; simpl; trivial.
destruct (beqAddr addr a) eqn:HbeqAddrA.
- rewrite <-DTL.beqAddrTrue in HbeqAddrA. subst a. unfold isPADDR in *.
  destruct (lookup addr (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  trivial.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup a (memory s0) beqAddr); trivial. destruct v; trivial.
  destruct (accessible b); trivial. f_equal. assumption.
Qed.

Lemma CPaddrAddEq (addr1 addr2: paddr) (cst: index):
CPaddr (addr1 + cst) <> nullAddr
-> CPaddr (addr1 + cst) = CPaddr (addr2 + cst)
-> addr1 = addr2.
Proof.
intros HbeqAdd1Null HbeqAdds. unfold nullAddr in *. unfold CPaddr in *. simpl in *.
destruct (le_dec (addr1 + cst) maxAddr).
- destruct (le_dec (addr2 + cst) maxAddr).
  + injection HbeqAdds as HbeqAdds. apply Nat.add_cancel_r in HbeqAdds. apply paddrEqNatEqEquiv. assumption.
  + contradict HbeqAdd1Null. rewrite HbeqAdds. f_equal. apply proof_irrelevance.
- contradict HbeqAdd1Null. f_equal. apply proof_irrelevance.
Qed.

Lemma getMappedBlocksEqBEPresentChangeFalse block part changedBlock newBentry s0 bentry:
isPDT part s0
-> lookup changedBlock (memory s0) beqAddr = Some (BE bentry)
-> present newBentry <> present bentry
-> present newBentry = false
-> In changedBlock (getMappedBlocks part s0)
-> noDupKSEntriesList s0
-> (In block (getMappedBlocks part s0)
    -> changedBlock = block
        \/ In block (getMappedBlocks part {|
                                            currentPartition := currentPartition s0;
                                            memory := add changedBlock (BE newBentry) (memory s0) beqAddr
                                          |}))
    /\ (In block (getMappedBlocks part {|
                                        currentPartition := currentPartition s0;
                                        memory := add changedBlock (BE newBentry) (memory s0) beqAddr
                                      |})
        -> In block (getMappedBlocks part s0))
    /\ (NoDup (getMappedBlocks part s0)
          -> NoDup (getMappedBlocks part {|
                                           currentPartition := currentPartition s0;
                                           memory := add changedBlock (BE newBentry) (memory s0) beqAddr
                                         |})).
Proof.
intros HpartIsPDT HlookupBlock HpresEq HnewPres HblockMapped HnoDup. unfold getMappedBlocks in *.
set(s := {|
            currentPartition := currentPartition s0;
            memory := add changedBlock (BE newBentry) (memory s0) beqAddr
          |}).
specialize(HnoDup part HpartIsPDT).
assert(isBE changedBlock s0) by (unfold isBE; rewrite HlookupBlock; trivial).
assert(HKSEq: getKSEntries part s = getKSEntries part s0) by (apply getKSEntriesEqBE; assumption).
rewrite HKSEq. revert block. induction ((filterOptionPaddr (getKSEntries part s0))); simpl in *.
- intuition.
- intro block. apply NoDup_cons_iff in HnoDup. destruct HnoDup as (HaNotInL & HnoDupRec).
  destruct (lookup a (memory s0) beqAddr) eqn:HlookupA.
  + destruct v; try(destruct (beqAddr changedBlock a) eqn:HbeqBlockA;
      try(rewrite <-DTL.beqAddrTrue in HbeqBlockA; subst a; exfalso; congruence); rewrite <-beqAddrFalse in *;
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial; rewrite HlookupA;
      apply IHl; assumption).
    destruct (present b) eqn:HpresA.
    * simpl in *. destruct (beqAddr changedBlock a) eqn:HbeqBlockA.
      --- rewrite <-DTL.beqAddrTrue in HbeqBlockA. subst a. rewrite HnewPres.
          assert(HfiltPresEq: filterPresent l s = filterPresent l s0).
          { apply filterPresentEqBENotInListNoChange; assumption. }
          rewrite HfiltPresEq. split. intuition. split. intuition. intro HnoDupFilt.
          apply NoDup_cons_iff in HnoDupFilt. intuition.
      --- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          destruct HblockMapped as [HaIsBlock | HblockMappedRec]; try(exfalso; congruence). rewrite HlookupA.
          rewrite HpresA. simpl. specialize(IHl HblockMappedRec HnoDupRec).
          assert(IHlCopy: forall block,
            (In block (filterPresent l s0) -> changedBlock = block \/ In block (filterPresent l s))
            /\ (In block (filterPresent l s) -> In block (filterPresent l s0))
            /\ (NoDup (filterPresent l s0) -> NoDup (filterPresent l s))) by assumption. specialize(IHl block).
          destruct IHl as (Himpls0s & Himplss0 & HnoDupImpl). split. intuition. split. intuition.
          intro HnoDupFilt. apply NoDup_cons_iff in HnoDupFilt. apply NoDup_cons_iff.
          destruct HnoDupFilt as (HaNotInFilt & HnoDupFiltRec). split; try(apply HnoDupImpl; assumption).
          contradict HaNotInFilt. specialize(IHlCopy a). destruct IHlCopy as (_ & Hres & _). apply Hres. assumption.
    * destruct (beqAddr changedBlock a) eqn:HbeqBlockA.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockA. subst a. rewrite HlookupBlock in HlookupA.
        injection HlookupA as HbentriesEq. subst b. rewrite HpresA in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupA.
      rewrite HpresA. apply IHl; assumption.
  + destruct (beqAddr changedBlock a) eqn:HbeqBlockA.
    { rewrite <-DTL.beqAddrTrue in HbeqBlockA. subst a. exfalso; congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupA.
    apply IHl; assumption.
Qed.

Lemma inclFilterOption l1 l2: incl l1 l2 -> incl (filterOptionPaddr l1) (filterOptionPaddr l2).
Proof.
intros Hincl addr HaddrInL1. apply optionIsInFilter in HaddrInL1. apply optionIsInFilter. apply Hincl; assumption.
Qed.

(*DUP*)
Lemma getAccessibleMappedBlocksEqBEPresentFalseNoChangeLight partition addr' newEntry bentry0 s0:
isPDT partition s0 ->
lookup addr' (memory s0) beqAddr = Some (BE bentry0) ->
(present newEntry) = (present bentry0) ->
(present newEntry) = false ->
getAccessibleMappedBlocks partition {|
						currentPartition := currentPartition s0;
						memory := add addr' (BE newEntry)
            (memory s0) beqAddr |} =
getAccessibleMappedBlocks partition s0.
Proof.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
intros HPDTs0 Hlookupaddr's0 HpresentEq HpresentFalse.
unfold getAccessibleMappedPaddr.
unfold s'. simpl.

unfold getAccessibleMappedBlocks.
assert(HpartEq : lookup partition (memory s') beqAddr = lookup partition (memory s0) beqAddr).
{
	unfold s'. simpl.
	destruct (beqAddr addr' partition) eqn:beqblockpart.
	- rewrite <- DTL.beqAddrTrue in beqblockpart.
		subst addr'. unfold isPDT in *.
		rewrite Hlookupaddr's0 in *.
		exfalso ; congruence.
	- rewrite <- beqAddrFalse in *.
		rewrite removeDupIdentity in * ; intuition.
}
fold s'.
rewrite HpartEq.
destruct (lookup partition (memory s0) beqAddr) ; try (intuition ; exfalso ; congruence).
destruct v ; intuition.
assert(HEq :  getMappedBlocks partition s' = getMappedBlocks partition s0).
{ 
	eapply getMappedBlocksEqBENoChange with bentry0; intuition.
}
rewrite HEq.
apply filterAccessibleEqBENotInListNoChange ; intuition.
assert(present bentry0 = false) by (rewrite HpresentEq in * ; intuition).
eapply BlockPresentFalseNotMapped with partition addr' bentry0 s0 in H0 ; intuition.
Qed.

(* DUP *)
Lemma getAllPaddrAuxEqBEStartEndNoChangeLight addr' newEntry bentry0 blocklist s0:
lookup addr' (memory s0) beqAddr = Some (BE bentry0) ->
~In addr' blocklist ->
getAllPaddrAux blocklist {|
						currentPartition := currentPartition s0;
						memory := add addr' (BE newEntry)
            (memory s0) beqAddr |} =
getAllPaddrAux blocklist s0.
Proof.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
intros Hlookupaddr's0 HnewNotInList.
induction blocklist; simpl in *; trivial.
simpl.
destruct (beqAddr addr' a) eqn:Hf.
--- rewrite <- DTL.beqAddrTrue in Hf.
	subst a. apply not_or_and in HnewNotInList. destruct HnewNotInList as (Hcontra & _).
	exfalso ; congruence.
---
rewrite <- beqAddrFalse in *.
		repeat rewrite removeDupIdentity ; intuition.
		destruct (lookup a (memory s0) beqAddr) ; intuition.
		destruct v ; intuition.
		f_equal. intuition.
Qed.

(* DUP *)
Lemma getAccessibleMappedPaddrEqBEPresentFalseNoChangeLight partition addr' newEntry bentry0 s0:
isPDT partition s0 ->
lookup addr' (memory s0) beqAddr = Some (BE bentry0) ->
(present newEntry) = (present bentry0) ->
(present newEntry) = false ->
getAccessibleMappedPaddr partition {|
						currentPartition := currentPartition s0;
						memory := add addr' (BE newEntry)
            (memory s0) beqAddr |} =
getAccessibleMappedPaddr partition s0.
Proof.
set (s' :=   {|
currentPartition := currentPartition s0;
memory := _ |}).
intros HPDTs0 Hlookupaddr's0 HpresentEq HpresentFalse.
unfold getAccessibleMappedPaddr.
unfold s'. simpl.

destruct (beqAddr addr' partition) eqn:beqpartaddr ; try(exfalso ; congruence).
- (* addr' = partition *)
	rewrite <- DTL.beqAddrTrue in beqpartaddr.
	fold s'.
	subst addr'.
	unfold isPDT in *.
	destruct (lookup partition (memory s0) beqAddr) ; try(exfalso ; congruence).
	destruct v ; try(exfalso ; congruence).

- (* addr' <> partition *)
	rewrite <- beqAddrFalse in *.
	repeat rewrite removeDupIdentity ; intuition.
	fold s'.
	assert(HEq :  getAccessibleMappedBlocks partition s' = getAccessibleMappedBlocks partition s0).
	{ eapply getAccessibleMappedBlocksEqBEPresentFalseNoChangeLight with bentry0 ; intuition.
	}
	rewrite HEq.
	apply getAllPaddrAuxEqBEStartEndNoChangeLight with bentry0 ; trivial. apply BlockNotMappedNotAccessible.
  intro Hcontra. apply mappedBlockIsBE in Hcontra. destruct Hcontra as [bentry (Hlookup & Hcontra)].
  rewrite Hlookup in *. injection Hlookupaddr's0 as HbentriesEq. subst bentry. congruence.
Qed.

Lemma accessibleMappedBlockIsAccessible block part s:
In block (getAccessibleMappedBlocks part s)
-> bentryAFlag block true s.
Proof.
intro HblockAccMapped. unfold getAccessibleMappedBlocks in *.
destruct (lookup part (memory s) beqAddr); try(simpl in *; exfalso; congruence).
destruct v; try(simpl in *; exfalso; congruence).
induction (getMappedBlocks part s); simpl in *; try(exfalso; congruence).
destruct (lookup a (memory s) beqAddr) eqn:HlookupA; try(apply IHl; assumption).
destruct v; try(apply IHl; assumption). destruct (accessible b) eqn:Hacc; try(apply IHl; assumption). simpl in *.
destruct HblockAccMapped as [HaIsBlock | HblockAccMappedRec]; try(apply IHl; assumption). subst a.
unfold bentryAFlag. rewrite HlookupA. auto.
Qed.

Lemma filterAccessibleSplit l1 l2 s: filterAccessible (l1++l2) s = filterAccessible l1 s ++ filterAccessible l2 s.
Proof.
induction l1; simpl; trivial. rewrite IHl1. destruct (lookup a (memory s) beqAddr); trivial. destruct v; trivial.
destruct (accessible b); trivial.
Qed.

Lemma getAllPaddrBlockSplit l (start1 end1: paddr) startaddr endaddr:
start1 < end1
-> getAllPaddrBlock startaddr endaddr = getAllPaddrBlock start1 end1 ++ l
-> startaddr = start1.
Proof.
intro HltStartEnd. unfold getAllPaddrBlock. assert(end1-start1 > 0) by lia. destruct (end1-start1); try(lia).
simpl. assert(start1 <= maxAddr) by (apply Hp). destruct (le_dec start1 maxAddr); try(lia). intro Heq.
destruct (endaddr-startaddr); simpl in *; try(exfalso; congruence). assert(startaddr <= maxAddr) by (apply Hp).
destruct (le_dec startaddr maxAddr); try(lia). injection Heq as Heq. apply paddrEqNatEqEquiv. assumption.
Qed.

Lemma notEmptyListHasLast (A:Type) (firstEl:A) l:
exists lastEl lBis, firstEl::l = lBis++[lastEl].
Proof.
revert firstEl. induction l; simpl; intro firstEl.
- exists firstEl. exists []. rewrite app_nil_l. reflexivity.
- specialize(IHl a). destruct IHl as [lastEl [lBis IHl]]. exists lastEl. exists (firstEl::lBis). rewrite IHl. auto.
Qed.

Lemma lastElNotElDef (A:Type) l (lastEl:A) defaultEl:
defaultEl <> lastEl
-> lastEl = last l defaultEl
-> exists lBis, l = lBis++[lastEl].
Proof.
intro HbeqEls. destruct l; intro Hlast; simpl; try(simpl in *; exfalso; congruence).
pose proof (notEmptyListHasLast A a l) as HlRec. destruct HlRec as [lastElBis [lBis HlEq]]. rewrite HlEq in *.
rewrite last_last in Hlast. subst lastElBis. exists lBis. reflexivity.
Qed.

Lemma getAllPaddrBlockEqAux n1 n2 pos (startaddr: paddr):
pos+startaddr+n1 <= maxAddr
-> n1 > 0
-> getAllPaddrBlockAux pos startaddr n1 = getAllPaddrBlockAux pos startaddr n2
-> n1 = n2.
Proof.
revert pos n2. induction n1; simpl; intros pos n2 HlebMax Hgt1 Heq; try(lia).
destruct (le_dec (pos + startaddr) maxAddr) eqn:HlePMax; try(lia). destruct n2; simpl in *; try(exfalso; congruence).
f_equal. rewrite HlePMax in *. injection Heq as Heq. destruct n1.
- simpl in *. destruct n2; trivial. exfalso. simpl in *. destruct (le_dec (S (pos + startaddr)) maxAddr); try(lia).
  congruence.
- assert(Hn1: S n1 > 0) by lia. assert(HlebPosPMax: (S pos) + startaddr + S n1 <= maxAddr) by lia.
  specialize(IHn1 (S pos) n2 HlebPosPMax Hn1). apply IHn1; assumption.
Qed.

Lemma getAllPaddrBlockEq (start1 end1 start2 end2: paddr):
start1 < end1
-> getAllPaddrBlock start1 end1 = getAllPaddrBlock start2 end2
-> start1 = start2 /\ end1 = end2.
Proof.
unfold getAllPaddrBlock. intros Hlt Heq. assert(start1 = start2).
{
  destruct (beqAddr start1 start2) eqn:HbeqStart; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
  rewrite <-beqAddrFalse in *. assert(end1-start1 > 0) by lia. destruct (end1-start1); simpl in *; try(lia).
  assert(start1 <= maxAddr) by (apply Hp). destruct (le_dec start1 maxAddr); try(lia).
  destruct (end2-start2); simpl in *; try(congruence). assert(start2 <= maxAddr) by (apply Hp).
  destruct (le_dec start2 maxAddr); try(lia). injection Heq as Hcontra. apply paddrNeqNatNeqEquiv in HbeqStart.
  congruence.
}
subst start2. split; trivial. assert(HltBis: end1-start1 > 0) by lia.
assert(HlebMax: 0+start1+(end1-start1) <= maxAddr).
{ assert(end1 <= maxAddr) by (apply Hp). lia. }
pose proof (getAllPaddrBlockEqAux (end1-start1) (end2-start1) 0 start1 HlebMax HltBis Heq) as Hres.
destruct (Nat.leb end2 start1) eqn:Hle.
{
  apply Nat.leb_le in Hle. exfalso. assert(Hcontra: end2-start1 = 0) by lia. rewrite Hcontra in Heq. simpl in *.
  destruct (end1 - start1); lia.
}
apply Nat.leb_gt in Hle. apply paddrEqNatEqEquiv. lia.
Qed.

Lemma getAllPaddrBlockSplitLEqAux pos l start1 endaddr n:
pos+n+start1 <= maxAddr
-> getAllPaddrBlockAux pos start1 endaddr = getAllPaddrBlockAux pos start1 n ++ l
-> l = getAllPaddrBlockAux (n+pos) start1 (endaddr-n).
Proof.
revert pos endaddr. induction n; simpl; intros pos endaddr HlebMax Heq.
- rewrite Nat.sub_0_r. auto.
- destruct (le_dec (pos + start1) maxAddr) eqn:Hleb; try(lia). destruct endaddr; simpl in *; try(exfalso; congruence).
  rewrite Hleb in *. injection Heq as Heq. apply IHn in Heq; try(lia). replace (S (n+pos)) with (n+S pos); try(lia).
  assumption.
Qed.

Lemma getAllPaddrBlockAuxEqPos pos startaddr endaddr:
getAllPaddrBlockAux pos startaddr endaddr = getAllPaddrBlockAux 0 (startaddr+pos) endaddr.
Proof.
revert pos startaddr. induction endaddr; intros; simpl; trivial.
replace (pos+startaddr) with (startaddr+pos); try(lia). destruct (le_dec (startaddr + pos) maxAddr); trivial. f_equal.
assert(Heq: getAllPaddrBlockAux 1 (startaddr + pos) endaddr = getAllPaddrBlockAux 0 (startaddr+pos+1) endaddr).
{ apply IHendaddr. }
rewrite IHendaddr. rewrite Heq. replace (startaddr + S pos) with (startaddr + pos + 1); try(lia). reflexivity.
Qed.

Lemma getAllPaddrBlockSplitLEq l (start1 end1: paddr) endaddr:
start1 < end1
-> getAllPaddrBlock start1 endaddr = getAllPaddrBlock start1 end1 ++ l
-> l = getAllPaddrBlock end1 endaddr.
Proof.
unfold getAllPaddrBlock. intros Hlt Heq.
assert(Hend1: end1-start1+start1 = end1) by lia. rewrite <-Hend1. clear Hend1.
replace (endaddr - (end1 - start1 + start1)) with (endaddr - start1 - (end1 - start1)); try(lia).
assert(end1 <= maxAddr) by (apply Hp). apply getAllPaddrBlockSplitLEqAux in Heq; try(lia).
rewrite Nat.sub_add; try(lia). rewrite Nat.add_0_r in *. rewrite getAllPaddrBlockAuxEqPos in Heq.
replace (start1 + (end1 - start1)) with (p end1) in Heq; try(lia). assumption.
Qed.

Lemma getPDsEqSHEPDflagNoChangeFalse addr newSh1entry s pdlist sh1entry sh1entry1 sh1entry0:
lookup addr (memory s) beqAddr = Some (SHE sh1entry)
-> PDflag newSh1entry = PDflag sh1entry
-> PDflag sh1entry = false
-> getPDs pdlist {|
                    currentPartition := currentPartition s;
                    memory := add addr (SHE newSh1entry) (add addr (SHE sh1entry1)
                        (add addr (SHE sh1entry0) (memory s) beqAddr) beqAddr) beqAddr
                  |} = getPDs pdlist s.
Proof.
intros HlookupAddr HPDflagEq HPDflagFalse. unfold getPDs.
assert(HchildFiltEq: childFilter
        {|
          currentPartition := currentPartition s;
          memory :=
            add addr (SHE newSh1entry)
              (add addr (SHE sh1entry1) (add addr (SHE sh1entry0) (memory s) beqAddr) beqAddr) beqAddr
        |} = childFilter s).
{
  extensionality block. unfold childFilter. simpl. rewrite beqAddrTrue.
  destruct (beqAddr addr block) eqn:HbeqAddrBlock.
  - rewrite <-DTL.beqAddrTrue in HbeqAddrBlock. subst addr. rewrite HlookupAddr. reflexivity.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; trivial. destruct v; trivial.
    destruct (Paddr.addPaddrIdx block sh1offset); trivial. destruct (beqAddr addr p) eqn:HbeqAddrP.
    + rewrite <-DTL.beqAddrTrue in HbeqAddrP. subst p. rewrite HlookupAddr. assumption.
    + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
}
rewrite HchildFiltEq. induction (filter (childFilter s) pdlist); simpl; trivial. rewrite beqAddrTrue.
destruct (beqAddr addr a) eqn:HbeqAddrA.
- rewrite <-DTL.beqAddrTrue in HbeqAddrA. subst a. rewrite HlookupAddr. f_equal. assumption.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup a (memory s) beqAddr); f_equal; assumption.
Qed.

Lemma getChildrenEqSHEFalse part addr newSh1entry s sh1entry sh1entry1 sh1entry0:
lookup addr (memory s) beqAddr = Some (SHE sh1entry)
-> PDflag newSh1entry = PDflag sh1entry
-> PDflag sh1entry = false
-> getChildren part {|
                      currentPartition := currentPartition s;
                      memory := add addr (SHE newSh1entry) (add addr (SHE sh1entry1)
                          (add addr (SHE sh1entry0) (memory s) beqAddr) beqAddr) beqAddr
                    |} = getChildren part s.
Proof.
intros HlookupAddr HPDflagsEq HPDflagFalse. unfold getChildren. simpl lookup. rewrite beqAddrTrue.
destruct (beqAddr addr part) eqn:HbeqAddrPart.
- rewrite <-DTL.beqAddrTrue in HbeqAddrPart. subst addr. rewrite HlookupAddr. reflexivity.
- rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
  assert(HaddrIsSHE: isSHE addr s) by (unfold isSHE; rewrite HlookupAddr; trivial).
  assert(HpartIsPDT: isPDT part s) by (unfold isPDT; rewrite HlookupPart; trivial).
  set(s1 := {|
              currentPartition := currentPartition s;
              memory := add addr (SHE sh1entry0) (memory s) beqAddr
            |}).
  set(s2 := {|
              currentPartition := currentPartition s1;
              memory := add addr (SHE sh1entry1) (memory s1) beqAddr
            |}).
  set(s3 := {|
              currentPartition := currentPartition s2;
              memory := add addr (SHE newSh1entry) (memory s2) beqAddr
            |}).
  assert(Hs: s3 = {|
                    currentPartition := currentPartition s;
                     memory := add addr (SHE newSh1entry)
                         (add addr (SHE sh1entry1) (add addr (SHE sh1entry0) (memory s) beqAddr) beqAddr) beqAddr
                  |}) by reflexivity.
  rewrite <-Hs. assert(HgetMappedEqs1: getMappedBlocks part s1 = getMappedBlocks part s).
  { apply getMappedBlocksEqSHE; assumption. }
  assert(isPDT part s1).
  {
    unfold isPDT in *. simpl. rewrite beqAddrFalse in *. rewrite HbeqAddrPart.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HgetMappedEqs2: getMappedBlocks part s2 = getMappedBlocks part s).
  {
    rewrite <-HgetMappedEqs1. apply getMappedBlocksEqSHE; trivial. unfold isSHE. simpl. rewrite beqAddrTrue. trivial.
  }
  assert(isPDT part s2).
  {
    unfold isPDT in *. cbn -[s1]. rewrite beqAddrFalse in *. rewrite HbeqAddrPart.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HgetMappedEqs3: getMappedBlocks part s3 = getMappedBlocks part s).
  {
    rewrite <-HgetMappedEqs2. apply getMappedBlocksEqSHE; trivial. unfold isSHE. simpl. rewrite beqAddrTrue. trivial.
  }
  rewrite HgetMappedEqs3. rewrite Hs. apply getPDsEqSHEPDflagNoChangeFalse with sh1entry; trivial.
Qed.

Lemma getPartitionsAuxEqSHEFalse part addr newSh1entry sh1entry sh1entry0 sh1entry1 s n :
lookup addr (memory s) beqAddr = Some (SHE sh1entry)
-> PDflag newSh1entry = PDflag sh1entry
-> PDflag sh1entry = false
-> getPartitionsAux n part {|
                             currentPartition := currentPartition s;
                             memory := add addr (SHE newSh1entry) (add addr (SHE sh1entry1)
                                 (add addr (SHE sh1entry0) (memory s) beqAddr) beqAddr) beqAddr
                           |} = getPartitionsAux n part s.
Proof.
intros HlookupAddr HPDflagsEq HPDflagFalse. revert part. induction n; simpl; intro part; f_equal.
rewrite getChildrenEqSHEFalse with (sh1entry:=sh1entry); trivial. f_equal. extensionality p. apply IHn.
Qed.

Lemma getPartitionsEqSHEFalse part addr newSh1entry sh1entry sh1entry0 sh1entry1 s:
lookup addr (memory s) beqAddr = Some (SHE sh1entry)
-> PDflag newSh1entry = PDflag sh1entry
-> PDflag sh1entry = false
-> getPartitions part {|
                        currentPartition := currentPartition s;
                        memory := add addr (SHE newSh1entry) (add addr (SHE sh1entry1)
                            (add addr (SHE sh1entry0) (memory s) beqAddr) beqAddr) beqAddr
                      |} = getPartitions part s.
Proof.
intros HlookupAddr HPDflagsEq HPDflagFalse. unfold getPartitions.
apply getPartitionsAuxEqSHEFalse with sh1entry; trivial.
Qed.

Lemma isParentsListEqSHERevCompl part addr newSh1entry sh1entry0 sh1entry1 parentsList s:
(exists pdentry, lookup part (memory s) beqAddr = Some (PDT pdentry))
-> isSHE addr s
-> parentOfPartitionIsPartition s
-> isParentsList {|
						       currentPartition := currentPartition s;
						       memory := add addr (SHE newSh1entry) (add addr (SHE sh1entry1)
                        (add addr (SHE sh1entry0) (memory s) beqAddr) beqAddr) beqAddr
                 |} parentsList part
-> isParentsList s parentsList part.
Proof.
set (s':= {|
            currentPartition := currentPartition s;
            memory := _
          |}).
intros HpartIsPDTs0 HaddrIsSHEs0 HparentOfPart0. revert HpartIsPDTs0. revert part. induction parentsList; auto.
(* parentsList = a::l *)
simpl. intros part HpartIsPDTs0 HparentsLists1. rewrite beqAddrTrue in *.
destruct (beqAddr addr a) eqn:HbeqAddrA; try(exfalso; congruence).
rewrite <-beqAddrFalse in HbeqAddrA. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
destruct (lookup a (memory s) beqAddr); try(congruence). destruct v; try(congruence).
destruct HparentsLists1 as [HpartNotRoot (HlookupParts & HparentsLists1)]. split; trivial.
destruct (beqAddr addr part) eqn:HbeqAddrPart.
{ (* addr = part *)
  rewrite <-DTL.beqAddrTrue in HbeqAddrPart. rewrite HbeqAddrPart in *. unfold isSHE in *.
  destruct HpartIsPDTs0 as [pdentry0 HlookupPart]. rewrite HlookupPart in *. exfalso; congruence.
}
(* addr <> part *)
rewrite <-beqAddrFalse in HbeqAddrPart. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
destruct HlookupParts as [pdentry0 (HlookupParts0 & HpartIsParent)]. subst a.
assert(HparentIsPDT: exists parentEntry, lookup (parent pdentry0) (memory s) beqAddr
                                          = Some (PDT parentEntry)).
{
  unfold parentOfPartitionIsPartition in *. specialize(HparentOfPart0 part pdentry0 HlookupParts0).
  destruct HparentOfPart0 as [HparentOfPart HparentOfRoot]. specialize(HparentOfPart HpartNotRoot).
  intuition.
}
split. exists pdentry0. auto.
specialize(IHparentsList (parent pdentry0) HparentIsPDT HparentsLists1). assumption.
Qed.

Lemma partitionsFromChildListAreParentsList s childrenList blockBase part:
nullAddrExists s
-> isParent s
-> parentOfPartitionIsPartition s
-> noDupPartitionTree s
-> pdchildIsPDT s
-> childLocMappedInChild s
-> In part (getPartitions multiplexer s)
-> In blockBase (getMappedBlocks part s)
-> partitionsFromChildList s childrenList blockBase <> []
-> isChildBlocksList s childrenList blockBase
-> isParentsList s (tl (partitionsFromChildList s childrenList blockBase)++[part])
    (hd nullAddr (partitionsFromChildList s childrenList blockBase ++ [part])).
Proof.
intros Hnull HisParent HparentOfPart HnoDupTree HPDchildIsPDT HchildLocProps. revert blockBase part.
induction childrenList; simpl; intros blockBase part HpartIsPart HbaseMapped HchildrenListNotNull HchildrenList;
  try(exfalso; congruence).
destruct (lookup blockBase (memory s) beqAddr) eqn:HlookupBase; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct (lookup (CPaddr (blockBase+sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
destruct v; try(exfalso; congruence). destruct HchildrenList as (HchildLocVal & HlocIsBE & HchildrenList).
destruct (beqAddr (PDchild s0) nullAddr) eqn:HbeqChildNull; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
assert(Hsh1: sh1entryAddr blockBase (CPaddr (blockBase+sh1offset)) s).
{ unfold sh1entryAddr. rewrite HlookupBase. reflexivity. }
assert(HPDchild: sh1entryPDchild (CPaddr (blockBase+sh1offset)) (PDchild s0) s).
{ unfold sh1entryPDchild. rewrite HlookupSh1. reflexivity. }
specialize(HPDchildIsPDT part blockBase (CPaddr (blockBase+sh1offset)) (PDchild s0) HpartIsPart HbaseMapped Hsh1
  HPDchild HbeqChildNull). specialize(HisParent (PDchild s0) part HpartIsPart HPDchildIsPDT).
unfold pdentryParent in *.
destruct (lookup (PDchild s0) (memory s) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
destruct v; try(exfalso; congruence). assert(isPDT part s).
{
  unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
  destruct (lookup part (memory s) beqAddr); try(simpl in *; congruence). destruct v; try(simpl in *; congruence).
  trivial.
}
unfold isPDT in *. destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
destruct v; try(exfalso; congruence). assert(HbeqChildRoot: PDchild s0 <> constantRootPartM).
{
  intro Hcontra. specialize(HparentOfPart (PDchild s0) p HlookupChild).
  destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *.
  subst part. unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupPart in *. congruence.
}
destruct (partitionsFromChildList s childrenList a) eqn:HeqList.
- simpl. rewrite HlookupPart. split; trivial. split; trivial. exists p. split; trivial.
- assert(HchildrenListRecNotNull: partitionsFromChildList s childrenList a <> []).
  { rewrite HeqList. intro. congruence. }
  assert(HchildIsPart: In (PDchild s0) (getPartitions multiplexer s)).
  { apply childrenPartitionInPartitionList with part; trivial. }
  assert(HchildLoc: sh1entryInChildLocation (CPaddr (blockBase+sh1offset)) a s).
  { unfold sh1entryInChildLocation. rewrite HlookupSh1. split; auto. }
  specialize(HchildLocProps part blockBase (CPaddr (blockBase+sh1offset)) a (PDchild s0) HpartIsPart HbaseMapped
    Hsh1 HPDchild HchildLoc HbeqChildNull).
  destruct HchildLocProps as (HbeqANull & HAMapped & HstartsEq).
  specialize(IHchildrenList a (PDchild s0) HchildIsPart HAMapped HchildrenListRecNotNull HchildrenList).
  assert(HhdEq: hd nullAddr ((partitionsFromChildList s childrenList a ++ [PDchild s0])++[part])
    = hd nullAddr (partitionsFromChildList s childrenList a ++ [PDchild s0])).
  { rewrite HeqList. reflexivity. }
  assert(HtlEq: tl (partitionsFromChildList s childrenList a) ++ [PDchild s0]
    = tl (partitionsFromChildList s childrenList a ++ [PDchild s0])).
  { rewrite HeqList. reflexivity. }
  rewrite <-HeqList. rewrite HhdEq. rewrite HtlEq in *. apply isParentsListRec with (PDchild s0) p0 p; trivial.
  rewrite <-HtlEq. apply eq_sym. apply last_last.
Qed.

Lemma hdtl (A:Type) (l: list A) def: l<>[] -> l = (hd def l)::(tl l).
Proof.
destruct l; intro HlNotNull; try(exfalso; congruence). reflexivity.
Qed.

Lemma tlSplit (A:Type) (l1 l2: list A): l1<>[] -> tl (l1++l2) = tl l1 ++ l2.
Proof.
intro Hl1NotNull. destruct l1; try(exfalso; congruence). simpl. reflexivity.
Qed.

Lemma partNotInParentsListMeansBlockNotInChildrenList block part s childrenList blockBase partBase:
nullAddrExists s
-> DisjointKSEntries s
-> noDupPartitionTree s
-> pdchildIsPDT s
-> childBlockNullIfChildNull s
-> childLocMappedInChild s
-> isPDT part s
-> In block (getMappedBlocks part s)
-> In partBase (getPartitions multiplexer s)
-> In blockBase (getMappedBlocks partBase s)
-> isChildBlocksList s childrenList blockBase
-> ~ In part (partitionsFromChildList s childrenList blockBase)
-> ~ In block childrenList.
Proof.
intros Hnull Hdisjoint HnoDupTree HPDchildIsPDT Hsh1NullImpl HlocProps HpartIsPDT HblockMapped.
revert blockBase partBase. induction childrenList; simpl; intros blockBase partBase HbaseIsPart HblockBMapped
  HchildrenList HpartNotInList; trivial.
destruct (lookup blockBase (memory s) beqAddr) eqn:HlookupBlockB; try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct (lookup (CPaddr (blockBase + sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
destruct v; try(exfalso; congruence). destruct HchildrenList as (HchildLocVal & HlocIsBE & HchildrenList).
assert(Hsh1: sh1entryAddr blockBase (CPaddr (blockBase+sh1offset)) s).
{ unfold sh1entryAddr. rewrite HlookupBlockB. reflexivity. }
assert(HPDchild: sh1entryPDchild (CPaddr (blockBase + sh1offset)) (PDchild s0) s).
{ unfold sh1entryPDchild. rewrite HlookupSh1. reflexivity. }
specialize(Hsh1NullImpl partBase blockBase (CPaddr (blockBase+sh1offset)) HbaseIsPart HblockBMapped Hsh1).
assert(HchildLoc: sh1entryInChildLocation (CPaddr (blockBase+sh1offset)) a s).
{ unfold sh1entryInChildLocation. rewrite HlookupSh1. auto. }
specialize(HlocProps partBase blockBase (CPaddr (blockBase+sh1offset)) a (PDchild s0) HbaseIsPart HblockBMapped Hsh1
  HPDchild HchildLoc). apply and_not_or. unfold nullAddrExists in *. unfold isPADDR in *.
specialize(HPDchildIsPDT partBase blockBase (CPaddr (blockBase+sh1offset)) (PDchild s0) HbaseIsPart HblockBMapped Hsh1
  HPDchild).
destruct (beqAddr (PDchild s0) nullAddr) eqn:HbeqChildNull.
- rewrite <-DTL.beqAddrTrue in HbeqChildNull. rewrite HbeqChildNull in *. specialize(Hsh1NullImpl HPDchild).
  unfold sh1entryInChildLocation in *. rewrite HlookupSh1 in *. destruct Hsh1NullImpl as (Hsh1NullImpl & _).
  rewrite <-Hsh1NullImpl in *. subst a. assert(childrenList = []).
  {
    destruct childrenList; trivial. simpl in *. exfalso.
    destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  subst childrenList. simpl. split; auto. apply mappedBlockIsBE in HblockMapped.
  destruct HblockMapped as [bentry (Hlookup & _)]. intro. subst block. rewrite Hlookup in *. congruence.
- rewrite <-beqAddrFalse in *. specialize(HlocProps HbeqChildNull). destruct HlocProps as (HbeqANull & HAMapped & _).
  apply Lib.in_app_or_neg in HpartNotInList. destruct HpartNotInList as (HpartNotInList & HpartNotChild).
  simpl in HpartNotChild. apply not_or_and in HpartNotChild. destruct HpartNotChild as (HbeqChildPart & _).
  specialize(HPDchildIsPDT HbeqChildNull). assert(HchildIsPart: In (PDchild s0) (getPartitions multiplexer s)).
  { apply childrenPartitionInPartitionList with partBase; trivial. }
  split.
  + intro Hcontra. rewrite Hcontra in *. assert(HchildIsPDT: isPDT (PDchild s0) s).
    {
      unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
      destruct (lookup (PDchild s0) (memory s) beqAddr); try(simpl in *; congruence).
      destruct v; try(simpl in *; congruence). trivial.
    }
    specialize(Hdisjoint (PDchild s0) part HchildIsPDT HpartIsPDT HbeqChildPart).
    destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
    unfold getMappedBlocks in *. apply InFilterPresentInList in HAMapped. apply InFilterPresentInList in HblockMapped.
    specialize(Hdisjoint block HAMapped). congruence.
  + revert HpartNotInList. apply IHchildrenList with (PDchild s0); trivial.
Qed.

Lemma noDupChildrenList s childrenList blockBase:
nullAddrExists s
-> DisjointKSEntries s
-> isParent s
-> parentOfPartitionIsPartition s
-> noDupPartitionTree s
-> partitionTreeIsTree s
-> pdchildIsPDT s
-> childBlockNullIfChildNull s
-> childLocMappedInChild s
-> (exists part, In part (getPartitions multiplexer s) /\ In blockBase (getMappedBlocks part s))
-> isChildBlocksList s childrenList blockBase
-> NoDup (blockBase::childrenList).
Proof.
intros Hnull Hdisjoint HisParent HparentOfPart HnoDupTree Htree HPDchildIsPDT HPDnullEquiv HlocProps.
revert blockBase. induction childrenList; intros blockBase HbaseMapped HchildrenList.
- apply NoDup_cons; try(apply NoDup_nil). auto.
- destruct HbaseMapped as [part (HpartIsPart & HbaseMapped)].
  assert(HchildrenListCopy: isChildBlocksList s (a :: childrenList) blockBase) by assumption.
  simpl in HchildrenList. destruct (lookup blockBase (memory s) beqAddr) eqn:HlookupBase; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  destruct (lookup (CPaddr (blockBase + sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). destruct HchildrenList as (HlocVal & HlocIsBE & HchildrenList).
  assert(Hsh1: sh1entryAddr blockBase (CPaddr (blockBase+sh1offset)) s).
  {
    apply mappedBlockIsBE in HbaseMapped. destruct HbaseMapped as [bentry (Hlookup & _)]. unfold sh1entryAddr.
    rewrite Hlookup. reflexivity.
  }
  assert(HPDchild: sh1entryPDchild (CPaddr (blockBase+sh1offset)) (PDchild s0) s).
  { unfold sh1entryPDchild. rewrite HlookupSh1. reflexivity. }
  assert(HchildLoc: sh1entryInChildLocation (CPaddr (blockBase+sh1offset)) a s).
  { unfold sh1entryInChildLocation. rewrite HlookupSh1. split; auto. }
  destruct (beqAddr (PDchild s0) nullAddr) eqn:HbeqChildNull.
  + rewrite <-DTL.beqAddrTrue in HbeqChildNull. rewrite HbeqChildNull in *.
    specialize(HPDnullEquiv part blockBase (CPaddr (blockBase+sh1offset)) HpartIsPart
      HbaseMapped Hsh1 HPDchild). unfold sh1entryInChildLocation in *. rewrite HlookupSh1 in *.
    destruct HPDnullEquiv as (HchildLocIsNull & _). rewrite <-HchildLocIsNull in *. subst a.
    destruct childrenList.
    * apply NoDup_cons; try(apply NoDup_cons); try(apply NoDup_nil); auto. simpl. apply and_not_or. split; auto.
      intro. subst blockBase. unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupBase in *. congruence.
    * simpl in *. exfalso. unfold nullAddrExists in *. unfold isPADDR in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
  + rewrite <-beqAddrFalse in *.
    assert(HlocPropsCopy: childLocMappedInChild s) by assumption.
    assert(HPDchildIsPDTCopy: pdchildIsPDT s) by assumption.
    specialize(HlocProps part blockBase (CPaddr (blockBase + sh1offset)) a (PDchild s0) HpartIsPart HbaseMapped
      Hsh1 HPDchild HchildLoc HbeqChildNull). destruct HlocProps as (HbeqANull & HAMapped & HstartsEq).
    specialize(HPDchildIsPDT part blockBase (CPaddr (blockBase+sh1offset)) (PDchild s0) HpartIsPart HbaseMapped Hsh1
      HPDchild HbeqChildNull). assert(HchildIsPart: In (PDchild s0) (getPartitions multiplexer s)).
    { apply childrenPartitionInPartitionList with part; trivial. }
    assert(HaMapped: exists child, In child (getPartitions multiplexer s) /\ In a (getMappedBlocks child s)).
    { exists (PDchild s0). auto. }
    specialize(IHchildrenList a HaMapped HchildrenList). apply NoDup_cons; trivial.
    assert(HbeqListNull: partitionsFromChildList s (a::childrenList) blockBase <> []).
    {
      simpl. rewrite HlookupBase. rewrite HlookupSh1. rewrite beqAddrFalse in *. rewrite HbeqChildNull. intro Hcontra.
      apply app_eq_nil in Hcontra. destruct Hcontra. congruence.
    }
    pose proof (partitionsFromChildListAreParentsList s (a::childrenList) blockBase part Hnull HisParent HparentOfPart
      HnoDupTree HPDchildIsPDTCopy HlocPropsCopy HpartIsPart HbaseMapped HbeqListNull HchildrenListCopy)
      as HparentsList.
    (*assert(HhdEq: hd nullAddr (partitionsFromChildList s (a :: childrenList) blockBase)
      = hd (PDchild s0) (partitionsFromChildList s childrenList a)).
    {
      simpl. rewrite HlookupBase. rewrite HlookupSh1. rewrite beqAddrFalse in *. rewrite HbeqChildNull.
      destruct (partitionsFromChildList s childrenList a); reflexivity.
    }
    rewrite HhdEq in *.*)
    pose proof (parentOfPartNotInParentsListsTail
      (hd nullAddr (partitionsFromChildList s (a :: childrenList) blockBase ++ [part]))
      (tl (partitionsFromChildList s (a::childrenList) blockBase)++[part]) s Htree HparentOfPart HparentsList)
      as HnoDupTail.
    assert(HlistNotNull: (partitionsFromChildList s (a :: childrenList) blockBase) ++ [part] <> []).
    { intro Hcontra. apply app_eq_nil in Hcontra. destruct Hcontra. congruence. }
    pose proof (hdtl paddr ((partitionsFromChildList s (a :: childrenList) blockBase) ++ [part]) nullAddr
      HlistNotNull) as HparentsListEq.
    assert(HnoDup: NoDup (partitionsFromChildList s (a :: childrenList) blockBase ++ [part])).
    {
      rewrite HparentsListEq. apply NoDup_cons; try(rewrite tlSplit); trivial.
      assert(isPDT (hd nullAddr (partitionsFromChildList s (a :: childrenList) blockBase ++ [part])) s).
      {
        assert(HtlEq: exists firstPart tlList, tl (partitionsFromChildList s (a :: childrenList) blockBase) ++ [part]
          = firstPart::tlList).
        {
          destruct (tl (partitionsFromChildList s (a :: childrenList) blockBase)); simpl.
          - exists part. exists []. reflexivity.
          - exists p. exists (l++[part]). reflexivity.
        }
        destruct HtlEq as [firstPart [tlList HtlEq]]. rewrite HtlEq in HparentsList. simpl in *.
        rewrite HlookupBase in *. rewrite HlookupSh1 in *. rewrite beqAddrFalse in *. rewrite HbeqChildNull in *.
        destruct (lookup firstPart (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). destruct HparentsList as (_ & [pdentry (Hlookup & _)] & _).
        unfold isPDT. rewrite Hlookup. trivial.
      }
      unfold isPDT in *.
      destruct (lookup (hd nullAddr (partitionsFromChildList s (a::childrenList) blockBase++[part]))
        (memory s) beqAddr) eqn:HlookupHd; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      apply basePartNotInParentsLists with p s; trivial.
    }
    apply Lib.NoDupSplitInclIff in HnoDup. destruct HnoDup as ((HnoDup & _) & HdisjointParts).
    assert(HchildNotInList: ~In part (partitionsFromChildList s (a::childrenList) blockBase)).
    {
      intro Hcontra. apply HdisjointParts in Hcontra. simpl in Hcontra. contradict Hcontra. auto.
    }
    revert HchildNotInList. apply partNotInParentsListMeansBlockNotInChildrenList with part; trivial.
    unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
    destruct (lookup part (memory s) beqAddr); try(simpl in *; congruence).
    destruct v; try(simpl in *; congruence). trivial.
Qed.

Lemma isChildBlocksListRec s blockBase blockParent childrenList:
isChildBlocksList s childrenList blockBase
-> isBE blockParent s
-> sh1entryInChildLocation (CPaddr (blockParent+sh1offset)) blockBase s
-> isChildBlocksList s (blockBase::childrenList) blockParent.
Proof.
simpl. intros HchildrenList HblockPIsBE HchildLocP. unfold isBE in *. unfold sh1entryInChildLocation in *.
destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; try(congruence).
destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s) beqAddr); try(congruence). destruct v; try(congruence).
destruct HchildLocP as (HchildLocVal & HbaseIsBE). auto.
Qed.

(*Lemma lastOfChildListIfNoLoc s block blockBase childrenList:
isPADDR nullAddr s
-> isBE block s
-> sh1entryInChildLocation (CPaddr (block+sh1offset)) nullAddr s
-> isChildBlocksList s childrenList blockBase
-> In block childrenList
-> block = last childrenList blockBase
    \/ exists childrenListRec, childrenList = childrenListRec++[nullAddr] /\ block = last childrenListRec blockBase.
Proof.
intros Hnull HblockIsBE HchildLoc. revert blockBase. induction childrenList; intros blockBase HchildList HblockIn;
  try(simpl in *; exfalso; congruence). simpl in HchildList. simpl in HblockIn.
destruct (lookup blockBase (memory s) beqAddr); try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct (lookup (CPaddr (blockBase+sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
destruct v; try(exfalso; congruence). destruct HchildList as (HchildLocBase & HlocBaseProp & HchildList).
destruct HblockIn as [Heq | HblockIn].
- rewrite Heq in *. destruct childrenList.
  + left. reflexivity.
  + right. simpl in *. unfold isBE in *. destruct (lookup block (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). unfold sh1entryInChildLocation in *.
    destruct (lookup (CPaddr (block+sh1offset)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). destruct HchildLoc as (HchildLoc & _). rewrite <-HchildLoc in *.
    destruct HchildList as (HeqNull & _ & HchildList). subst p. destruct childrenList.
    * exists [block]. split; reflexivity.
    * exfalso. simpl in *. unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
      destruct v; congruence.
- specialize(IHchildrenList a HchildList HblockIn). destruct IHchildrenList as [Hlast | Hpen].
  + left. apply lastRecInc. assumption.
  + right. destruct Hpen as [childrenListRec (Hpen & Hlast)]. exists (a::childrenListRec). rewrite Hpen.
    split; trivial. apply lastRecInc. assumption.
Qed.

Lemma lastOfChildListIfNoLocBis s block blockBase childrenList:
isPADDR nullAddr s
-> isBE block s
-> sh1entryInChildLocation (CPaddr (block+sh1offset)) nullAddr s
-> isChildBlocksList s childrenList blockBase
-> In block childrenList
-> exists childrenListRec lastEl, childrenList = childrenListRec++[lastEl]
    /\ (lastEl = block /\ ~In block childrenListRec
        \/ lastEl = nullAddr
          /\ exists childrenListRecRec, childrenListRec = childrenListRecRec++[block]
              /\ ~In block childrenListRecRec).
Proof.
intros Hnull HblockIsBE HchildLoc. revert blockBase. induction childrenList; intros blockBase HchildList HblockIn;
  try(simpl in *; exfalso; congruence). simpl in *.
destruct (lookup blockBase (memory s) beqAddr); try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct (lookup (CPaddr (blockBase+sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
destruct v; try(exfalso; congruence). destruct HchildList as (HchildLocBase & HlocBaseProp & HchildList).
destruct (beqAddr a block) eqn:HbeqBlockA.
- rewrite <-DTL.beqAddrTrue in HbeqBlockA. rewrite HbeqBlockA in *. destruct childrenList.
  + exists []. exists block. split; trivial. left. split; auto.
  + exists [block]. exists p. simpl in *. unfold isBE in *.
    destruct (lookup block (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). unfold sh1entryInChildLocation in *.
    destruct (lookup (CPaddr (block+sh1offset)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). destruct HchildLoc as (HchildLoc & _). rewrite <-HchildLoc in *.
    destruct HchildList as (HeqNull & _ & HchildList). subst p. destruct childrenList.
    * split; trivial. right. split; trivial. exists []. split; auto.
    * exfalso. simpl in *. unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
      destruct v; congruence.
- rewrite <-beqAddrFalse in *. destruct HblockIn as [Heq | HblockIn]; try(exfalso; congruence).
  specialize(IHchildrenList a HchildList HblockIn).
  destruct IHchildrenList as [childrenListRec [lastEl (HchildListEq & IHchildrenList)]].
  exists (a::childrenListRec). exists lastEl. rewrite HchildListEq. split; auto.
  destruct IHchildrenList as [(Hlast & HblockNotIn) | (Hlast & [childrenListRecRec (Hpen & HblockNotIn)])].
  + left. simpl. split; trivial. apply and_not_or. split; assumption.
  + right. split; trivial. rewrite Hpen. exists (a::childrenListRecRec). split; trivial. simpl. apply and_not_or.
    split; assumption.
Qed.*)

Lemma lastOfChildListIfNoLoc s block blockBase childrenList:
isPADDR nullAddr s
-> isBE block s
-> sh1entryInChildLocation (CPaddr (block+sh1offset)) nullAddr s
-> isChildBlocksList s childrenList blockBase
-> In block childrenList
-> exists childrenListRec lastEl, childrenList = childrenListRec++[lastEl]
    /\ ~In nullAddr childrenListRec
    /\ (lastEl = block /\ ~In block childrenListRec
        \/ lastEl = nullAddr
          /\ exists childrenListRecRec, childrenListRec = childrenListRecRec++[block]
              /\ ~In block childrenListRecRec).
Proof.
intros Hnull HblockIsBE HchildLoc. revert blockBase. induction childrenList; intros blockBase HchildList HblockIn;
  try(simpl in *; exfalso; congruence). simpl in *.
destruct (lookup blockBase (memory s) beqAddr); try(exfalso; congruence).
destruct v; try(exfalso; congruence).
destruct (lookup (CPaddr (blockBase+sh1offset)) (memory s) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
destruct v; try(exfalso; congruence). destruct HchildList as (HchildLocBase & HlocBaseProp & HchildList).
destruct (beqAddr a block) eqn:HbeqBlockA.
- rewrite <-DTL.beqAddrTrue in HbeqBlockA. rewrite HbeqBlockA in *. destruct childrenList.
  + exists []. exists block. split; trivial. split; auto.
  + exists [block]. exists p. simpl in *. unfold isBE in *.
    destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). unfold sh1entryInChildLocation in *.
    destruct (lookup (CPaddr (block+sh1offset)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). destruct HchildLoc as (HchildLoc & _). assert(block <> nullAddr).
    {
      intro Hcontra. rewrite Hcontra in *. unfold isPADDR in *. rewrite HlookupBlock in *. congruence.
    }
    rewrite <-HchildLoc in *. destruct HchildList as (HeqNull & _ & HchildList). subst p. destruct childrenList.
    * split; trivial. split.
      --- intro Hcontra. destruct Hcontra; congruence.
      --- right. split; trivial. exists []. split; auto.
    * exfalso. simpl in *. unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
      destruct v; congruence.
- rewrite <-beqAddrFalse in *. destruct HblockIn as [Heq | HblockIn]; try(exfalso; congruence).
  specialize(IHchildrenList a HchildList HblockIn).
  destruct IHchildrenList as [childrenListRec [lastEl (HchildListEq & HnullNotIn & IHchildrenList)]].
  exists (a::childrenListRec). exists lastEl. rewrite HchildListEq. split; auto. split.
  + simpl. intro Hcontra. destruct Hcontra as [HeqA | HnullIn]; try(congruence). rewrite HeqA in *.
    destruct childrenList; simpl in *; try(congruence). unfold isPADDR in *.
    destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
  + destruct IHchildrenList as [(Hlast & HblockNotIn) | (Hlast & [childrenListRecRec (Hpen & HblockNotIn)])].
    * left. simpl. split; trivial. apply and_not_or. split; assumption.
    * right. split; trivial. rewrite Hpen. exists (a::childrenListRecRec). split; trivial. simpl. apply and_not_or.
      split; assumption.
Qed.

(*Lemma nbFreeLowerThanPrepared partition nbPrepare nbFreeSlots s:
maxNbPrepareIsMaxNbKernels s
-> NbFreeSlotsISNbFreeSlotsInList s
-> inclFreeSlotsBlockEntries s
-> pdentryNbPrepare partition nbPrepare s
-> pdentryNbFreeSlots partition nbFreeSlots s
-> nbFreeSlots <= nbPrepare*kernelStructureEntriesNb.
Proof.
intros HmaxNbPrep HnbFreeList HinclFreeKS HnbPrep HnbFree.
assert(HpartIsPDT: isPDT partition s).
{
  unfold isPDT. unfold pdentryNbPrepare in *. destruct (lookup partition (memory s) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
specialize(HnbFreeList partition nbFreeSlots HpartIsPDT HnbFree).
destruct HnbFreeList as [optFreeSlots (Hlist & HwellFormedList & HnbFreeList)].

inclFreeSlotsBlockEntries
KernelStructureStartFromBlockEntryAddrIsKS
Qed.

Lemma freeSlotsAreBlocks partition optFreeSlots s:
inclFreeSlotsBlockEntries s
-> optFreeSlots = getFreeSlotsList partition s
-> exists kernList, isListOfKernels kernList partition s
    /\ length optFreeSlots <= length kernList*kernelStructureEntriesNb.
Proof.

Qed.*)
