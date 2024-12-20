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
-> noDupUsedPaddrList s0
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
-> noDupUsedPaddrList s0
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
-> noDupUsedPaddrList s
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
-> noDupUsedPaddrList s
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
-> noDupUsedPaddrList s
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
