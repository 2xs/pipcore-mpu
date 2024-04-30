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

Require Import Model.ADT Model.Monad Model.Lib Model.MALInternal.
Require Import Core.Internal.
Require Import Proof.WeakestPreconditions Proof.Consistency Proof.StateLib Proof.DependentTypeLemmas
              Proof.InternalLemmas.
Require Import Hoare Invariants findBlockInKS.
Require Import FunctionalExtensionality List Lia Coq.Logic.ProofIrrelevance Coq.Bool.Bool Coq.Bool.BoolEq.
Import List.ListNotations.

Module WP := WeakestPreconditions.
Module DTL := DependentTypeLemmas.

Global Set Primitive Projections.
Global Set Printing Primitive Projection Parameters.


Lemma accessibleIfInFilterAcc elem belem l s:
In elem l
-> lookup elem (memory s) beqAddr = Some (BE belem)
-> accessible belem = true
-> In elem (filterAccessible l s).
Proof.
induction l.
- intros HinList Hlookup Haccessible. assert(Hcontra: ~In elem []) by (apply in_nil). congruence.
- intros HinList Hlookup Haccessible. assert(HcasesMapped: a = elem \/ In elem l) by (apply in_inv; assumption).
  destruct HcasesMapped as [HisElem | Hrec].
  + subst a. simpl. rewrite Hlookup. rewrite Haccessible. apply in_eq.
  + specialize(IHl Hrec Hlookup Haccessible). simpl. destruct (lookup a (memory s) beqAddr); try assumption.
    destruct v; try assumption. destruct (accessible b); try assumption. simpl. right. assumption.
Qed.


(*TODO move the two fixpoints elsewhere (to StateLib ?)*)
Fixpoint isParentsList (s: state) (parentsList: list paddr) (pdBase: paddr) :=
match parentsList with
| nil => True (*pdBase = constantRootPartM*)
| pdparent::newParentsList => (match (lookup pdparent (memory s) beqAddr) with
                            | Some (PDT pdentry) => pdBase <> constantRootPartM
                                                    /\ (exists pdentry0, lookup pdBase (memory s) beqAddr
                                                                        = Some (PDT pdentry0)
                                                        /\ pdparent = parent pdentry0)
                                                    /\ isParentsList s newParentsList pdparent
                            | _ => False
                            end)
end.


Lemma isParentsListEqBE partition addr' newEntry bentry0 parentsList s0:
(exists pdentry, lookup partition (memory s0) beqAddr = Some (PDT pdentry)) ->
lookup addr' (memory s0) beqAddr = Some (BE bentry0) ->
consistency1 s0 ->
isParentsList {|
						    currentPartition := currentPartition s0;
						    memory := add addr' (BE newEntry) (memory s0) beqAddr
              |} parentsList partition
-> isParentsList s0 parentsList partition.
Proof.
set (s':= {|
            currentPartition := currentPartition s0;
            memory := _
          |}).
intros HpartIsPDTs0 HaddrIsBEs0 Hconsists0. revert HpartIsPDTs0. revert partition.
induction parentsList.
- (* parentsList = [] *)
  simpl. intros. trivial.
- (* parentsList = a::l *)
  simpl. intros partition HpartIsPDTs0 HparentsLists1.
  destruct (beqAddr addr' a) eqn:HbeqAddrA; try(exfalso; congruence).
  rewrite <-beqAddrFalse in HbeqAddrA. rewrite removeDupIdentity in HparentsLists1; intuition.
  destruct (lookup a (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
  destruct HparentsLists1 as [HpartNotRoot (HlookupParts0 & HparentsLists1)]. split. assumption.
  destruct (beqAddr addr' partition) eqn:HbeqAddrPart.
  { (* addr' = partition *)
    rewrite <-DTL.beqAddrTrue in HbeqAddrPart. rewrite HbeqAddrPart in *. rewrite HaddrIsBEs0 in HpartIsPDTs0.
    destruct HpartIsPDTs0 as [pdentry0 HpartIsPDTs0]. exfalso; congruence.
  }
  (* addr' <> partition *)
  rewrite <-beqAddrFalse in HbeqAddrPart. rewrite removeDupIdentity in HlookupParts0; intuition.
  destruct HlookupParts0 as [pdentry0 (HlookupParts0 & HpartIsParent)]. subst a.
  assert(HparentIsPDT: exists parentEntry, lookup (parent pdentry0) (memory s0) beqAddr
                                            = Some (PDT parentEntry)).
  {
    assert(HparentIsPart: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
    unfold parentOfPartitionIsPartition in HparentIsPart.
    specialize(HparentIsPart partition pdentry0 HlookupParts0).
    destruct HparentIsPart as [HparentOfPart HparentOfRoot]. specialize(HparentOfPart HpartNotRoot).
    assumption.
  }
  specialize(IHparentsList (parent pdentry0) HparentIsPDT HparentsLists1). assumption.
Qed.

Lemma isParentsListEqPDTSameParent partition addr newEntry parentsList s0 s1:
s1 = {|
       currentPartition := currentPartition s0;
       memory := add addr (PDT newEntry) (memory s0) beqAddr
     |} ->
(exists pdentry pdentry1,
                lookup partition (memory s0) beqAddr = Some (PDT pdentry)
                /\ lookup partition (memory s1) beqAddr = Some (PDT pdentry1)
                /\ (partition <> addr -> pdentry1 = pdentry)
                /\ (partition = addr -> pdentry1 = newEntry /\ parent newEntry = parent pdentry)
                /\ (forall parentsList, isParentsList s0 parentsList partition -> ~ In addr parentsList)
                    (*addr <> parent pdentry*)) ->
parentOfPartitionIsPartition s0 ->
isParentsList s1 parentsList partition
-> isParentsList s0 parentsList partition.
Proof.
(*intros Hs1 HpartIsPDT. revert HpartIsPDTs0. revert HaddrIsNotPart.*)
revert partition. induction parentsList.
- (* parentsList = [] *)
  simpl. intros. trivial.
- (* parentsList = a::l *)
  simpl. intros partition Hs1 HpartIsPDT HparentIsPart HparentsLists1.
  destruct HpartIsPDT as [pdentry (pdentry1 & (HlookupParts0 & HlookupParts1 & HentriessEq & HparentsEq &
                            HaddNotParent))]. rewrite Hs1 in HparentsLists1.
  simpl in HparentsLists1.
  destruct (beqAddr addr a) eqn:HbeqAddrA.
  + (* addr = a *)
    destruct HparentsLists1 as [HpartNotRoot ((pdentry0 & (HpdentryEq & Ha)) & HparentsLists1)].
    rewrite <-DTL.beqAddrTrue in HbeqAddrA. rewrite HbeqAddrA in *.
    destruct (beqAddr a partition) eqn:HbeqAPart.
    * (* a = partition *)
      rewrite <-DTL.beqAddrTrue in HbeqAPart. rewrite HbeqAPart in *. rewrite HlookupParts0.
      split. assumption. injection HpdentryEq as HnewEntry. subst pdentry0. split. exists pdentry. split.
      reflexivity. assert(Htriv: partition = partition) by reflexivity.
      specialize(HparentsEq Htriv). destruct HparentsEq as [HnewEntriessEq HparentsEq]. rewrite HparentsEq in Ha.
      assumption. rewrite <-Hs1 in HparentsLists1.
      assert(HpartIsPDT: exists pdentry0 pdentry1,
                                    lookup partition (memory s0) beqAddr = Some (PDT pdentry0)
                                    /\ lookup partition (memory s1) beqAddr = Some (PDT pdentry1)
                                    /\ (partition <> partition -> pdentry1 = pdentry0)
                                    /\ (partition = partition -> pdentry1 = newEntry
                                                                /\ parent newEntry = parent pdentry0)
                                    /\ (forall parentsList : list paddr, isParentsList s0 parentsList partition
                                                                        -> ~ In partition parentsList)
                                       (*partition <> parent pdentry0*)).
      { exists pdentry. exists pdentry1. intuition. }
      specialize(IHparentsList partition Hs1 HpartIsPDT HparentIsPart HparentsLists1). assumption.
    * (* a <> partition *)
      rewrite <-beqAddrFalse in HbeqAPart. rewrite removeDupIdentity in HpdentryEq; intuition.
      assert(pdentry0 = pdentry).
      {
        rewrite HpdentryEq in HlookupParts0. injection HlookupParts0 as Heq. assumption.
      }
      subst pdentry0.
      unfold parentOfPartitionIsPartition in HparentIsPart.
      specialize(HparentIsPart partition pdentry HlookupParts0).
      destruct HparentIsPart as [HparentOfPart HparentOfRoot]. specialize(HparentOfPart HpartNotRoot).
      destruct HparentOfPart as [parentEntry HparentOfPart]. rewrite Ha. rewrite HparentOfPart.
      split. assumption. subst a. set(shortParentsList := [parent pdentry]).
      assert(HshortIsParentsList: isParentsList s0 shortParentsList partition).
      {
        subst shortParentsList. simpl. rewrite HparentOfPart. split. assumption. split. exists pdentry.
        split. assumption. reflexivity. trivial.
      }
      specialize(HaddNotParent shortParentsList HshortIsParentsList). subst shortParentsList.
      simpl in HaddNotParent. exfalso. apply HaddNotParent. left. apply eq_sym. assumption.
  + (* addr <> a *)
    rewrite <-beqAddrFalse in HbeqAddrA. rewrite removeDupIdentity in HparentsLists1; intuition.
    destruct (lookup a (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    destruct (beqAddr addr partition) eqn:HbeqAddrPart.
    * (* addr = partition *)
      rewrite <-DTL.beqAddrTrue in HbeqAddrPart. rewrite HbeqAddrPart in *.
      destruct HparentsLists1 as [HpartNotRoot ((pdentry0 & (HpdentryEq & Ha)) & HparentsLists1)].
      injection HpdentryEq as Hentry. subst pdentry0. split. assumption. split. exists pdentry.
      split. assumption. assert(Htriv: partition = partition) by intuition.
      specialize(HparentsEq Htriv). destruct HparentsEq as [HnewEntriessEq HparentsEq]. rewrite HparentsEq in Ha.
      assumption. rewrite Ha in *.
      assert(Htriv: partition = partition) by intuition. specialize(HparentsEq Htriv).
      destruct HparentsEq as [HnewEntriessEq HparentsEq]. rewrite HparentsEq in *.
      assert(HparentIsPDT: exists parentEntry, lookup (parent pdentry) (memory s0) beqAddr
                                                = Some (PDT parentEntry)).
      {
        unfold parentOfPartitionIsPartition in HparentIsPart.
        specialize(HparentIsPart partition pdentry HlookupParts0).
        destruct HparentIsPart as [HparentOfPart HparentOfRoot]. specialize(HparentOfPart HpartNotRoot).
        assumption.
      }
      destruct HparentIsPDT as [parentEntry HlookupParents0].
      assert(HlookupParents1: lookup (parent pdentry) (memory s1) beqAddr = Some (PDT parentEntry)).
      {
        rewrite Hs1. simpl.
        assert(HbeqPartParent: beqAddr partition (parent pdentry) = false)
                by (rewrite <-beqAddrFalse; intuition).
        rewrite HbeqPartParent. rewrite removeDupIdentity; intuition.
      }
      assert(HparentIsPDT: exists pdentry0 pdentry1 : PDTable,
                   lookup (parent pdentry) (memory s0) beqAddr = Some (PDT pdentry0)
                   /\ lookup (parent pdentry) (memory s1) beqAddr = Some (PDT pdentry1)
                   /\ (((parent pdentry) <> partition) -> pdentry1 = pdentry0)
                   /\ ((parent pdentry) = partition -> pdentry1 = newEntry /\ parent pdentry = parent pdentry0)
                   /\ (forall parentsList : list paddr, isParentsList s0 parentsList (parent pdentry)
                                                        -> In partition parentsList -> False)
                      (*(partition <> parent pdentry0)*)).
      {
        exists parentEntry. exists parentEntry. split. assumption. split. assumption. split. intro. reflexivity.
        split. intro. exfalso; congruence. intros parentsList0 HisParentsList0 HpartIsParent.
        assert(HisParentsList0Add: isParentsList s0 (parent pdentry::parentsList0) partition).
        {
          simpl. rewrite HlookupParents0. split. assumption. split. exists pdentry. split. assumption.
          reflexivity. assumption.
        }
        specialize(HaddNotParent (parent pdentry::parentsList0) HisParentsList0Add). simpl in HaddNotParent.
        apply HaddNotParent. right. assumption.
      }
      rewrite <-Hs1 in HparentsLists1.
      specialize(IHparentsList (parent pdentry) Hs1 HparentIsPDT HparentIsPart HparentsLists1). assumption.
    * (* addr <> partition *)
      destruct HparentsLists1 as [HpartNotRoot ((pdentry0 & (HpdentryEq & Ha)) & HparentsLists1)].
      rewrite <-beqAddrFalse in HbeqAddrPart.
      rewrite removeDupIdentity in HpdentryEq; try(intuition; congruence).
      rewrite HlookupParts0 in HpdentryEq. injection HpdentryEq as Hentry. subst pdentry0. split. assumption.
      split. exists pdentry. split. assumption. assumption. subst a.
      assert(HparentIsPDT: exists parentEntry, lookup (parent pdentry) (memory s0) beqAddr
                                                = Some (PDT parentEntry)).
      {
        unfold parentOfPartitionIsPartition in HparentIsPart.
        specialize(HparentIsPart partition pdentry HlookupParts0).
        destruct HparentIsPart as [HparentOfPart HparentOfRoot]. specialize(HparentOfPart HpartNotRoot).
        assumption.
      }
      destruct HparentIsPDT as [parentEntry HlookupParents0].
      assert(HlookupParents1: lookup (parent pdentry) (memory s1) beqAddr = Some (PDT parentEntry)).
      {
        rewrite Hs1. simpl.
        assert(HbeqPartParent: beqAddr addr (parent pdentry) = false) by (rewrite <-beqAddrFalse; intuition).
        rewrite HbeqPartParent. rewrite removeDupIdentity; intuition.
      }
      assert(HparentIsPDT: exists pdentry0 pdentry1 : PDTable,
                   lookup (parent pdentry) (memory s0) beqAddr = Some (PDT pdentry0)
                   /\ lookup (parent pdentry) (memory s1) beqAddr = Some (PDT pdentry1)
                   /\ (((parent pdentry) <> addr) -> pdentry1 = pdentry0)
                   /\ ((parent pdentry) = addr -> pdentry1 = newEntry /\ parent newEntry = parent pdentry0)
                   /\ (forall parentsList : list paddr, isParentsList s0 parentsList (parent pdentry)
                                                        -> In addr parentsList -> False)
                      (*(addr <> parent pdentry0)*)).
      {
        exists parentEntry. exists parentEntry. split. assumption. split. assumption. split. intro. reflexivity.
        split. intro Hcontra. exfalso; congruence. intros parentsList0 HisParentsList0 HaddrIsParent.
        assert(HisParentsList0Add: isParentsList s0 (parent pdentry::parentsList0) partition).
        {
          simpl. rewrite HlookupParents0. split. assumption. split. exists pdentry. split. assumption.
          reflexivity. assumption.
        }
        specialize(HaddNotParent (parent pdentry::parentsList0) HisParentsList0Add). simpl in HaddNotParent.
        apply HaddNotParent. right. assumption.
      }
      rewrite <-Hs1 in HparentsLists1.
      specialize(IHparentsList (parent pdentry) Hs1 HparentIsPDT HparentIsPart HparentsLists1). assumption.
Qed.


Fixpoint isBuiltFromWriteAccessibleRec (s0 s: state) (statesList: list state) (pdEntriesList: list paddr)
(pdbasepartition: paddr) (flag: bool) :=
match statesList with
| nil => pdEntriesList = nil /\ s = s0
| s2::newStatesList =>
        (*(s = s0 -> False) /\ (s <> s0 ->*)
        exists pdAddr newPdEntriesList,
            pdEntriesList = pdAddr::newPdEntriesList
            /\ exists (realMPU : list paddr) (pdentry0 pdentry1 : PDTable) (blockInParentPartitionAddr: paddr)
                  (bentry newBentry: BlockEntry) (s1: state),
                 s1 =
                  {|
                    currentPartition := currentPartition s0;
                    memory :=
                      add blockInParentPartitionAddr
                        (BE
                           (CBlockEntry (read bentry) (write bentry) (exec bentry)
                              (present bentry) flag (blockindex bentry) (blockrange bentry)))
                        (memory s0) beqAddr
                  |}
                 (*/\ lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry0)*)
                 /\ ((s2 = s1) \/ (s2 = (*TODO verify that*)
                     {|
                       currentPartition := currentPartition s0;
                       memory :=
                         add pdAddr
                           (PDT
                              {|
                                structure := structure pdentry1;
                                firstfreeslot := firstfreeslot pdentry1;
                                nbfreeslots := nbfreeslots pdentry1;
                                nbprepare := nbprepare pdentry1;
                                parent := parent pdentry1;
                                MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                                vidtAddr := vidtAddr pdentry1
                              |}) (memory s1) beqAddr
                     |}
                     /\ pdentryMPU pdAddr realMPU s1))
                  /\ (s0 = s2 -> newStatesList = [])
                  /\ newBentry =
                           CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                             (blockindex bentry) (blockrange bentry)
                  /\ lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
                  /\ lookup blockInParentPartitionAddr (memory s1) beqAddr = Some (BE newBentry)
                  /\ bentryPFlag blockInParentPartitionAddr true s0
                  /\ In blockInParentPartitionAddr (getMappedBlocks pdAddr s0)
                  /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentry0)
                  /\ lookup pdbasepartition (memory s1) beqAddr = Some (PDT pdentry0)
                  /\ lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
                  /\ lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)
                  /\ pdAddr = parent pdentry0
                  /\ isBuiltFromWriteAccessibleRec s2 s newStatesList newPdEntriesList pdAddr flag(*)*)
end.

(*Lemma lookupPDTEqWriteAccess partition cutStatesList initState parentsList parent flag s:
isPDT partition initState
-> parentOfPartitionIsPartition initState
-> isBuiltFromWriteAccessibleRec initState s cutStatesList parentsList parent flag
-> lookup partition (memory s) beqAddr = lookup partition (memory initState) beqAddr.
Proof.
revert parent. revert parentsList. revert initState. induction cutStatesList.
- (* cutStatesList = [] *)
  simpl. intros initState parentsList parent HpartIsPDT HparentOfPart Hprops.
  destruct Hprops as [HparentsList HssInitEq]. subst s. reflexivity.
- (* cutStatesList = a::l *)
  simpl. intros initState parentsList parent HpartIsPDT HparentOfPart Hprops.
  destruct Hprops as [Hinit Hrec]. destruct Hrec as [pdAddr Hprops]. intro Hcontra. apply Hinit. assumption.
  destruct Hprops as [newPdEntriesList (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr & (HlastCase &
                       (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockIsMapped & HlookupParentsInit
                        & HlookupParents1 & HlookupAncestorsInit & HlookupAncestors1 & Hancestor &
                         HisBuilt))))))))))))].
  destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
  { (* blockInParentPartitionAddr = partition *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *. unfold isPDT in HpartIsPDT.
    rewrite HlookupBlocks0 in HpartIsPDT. exfalso; congruence.
  }
  (* blockInParentPartitionAddr <> partition *)
  assert(HpartIsPDTa: isPDT partition a
                      /\ lookup partition (memory a) beqAddr = lookup partition (memory initState) beqAddr).
  {
    unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
    + (* a = s1 *)
      subst a. rewrite Hs1. simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in HbeqBlockPart.
      rewrite removeDupIdentity; intuition.
    + (* a <> s1 *)
      destruct Ha as [Ha HMPU]. rewrite Ha. rewrite Hs1. simpl.
      destruct (beqAddr pdAddr partition) eqn:HbeqAncestorPart.
      { (* pdAddr = partition *)
        rewrite <-DTL.beqAddrTrue in HbeqAncestorPart. rewrite HbeqAncestorPart in *. admit.
      }
      (* pdAddr <> partition *)
      destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockAncestor.
      { (* blockInParentPartitionAddr = pdAddr *)
        rewrite <-DTL.beqAddrTrue in HbeqBlockAncestor. rewrite HbeqBlockAncestor in *.
        rewrite HlookupBlocks0 in HlookupAncestorsInit. exfalso; congruence.
      }
      (* blockInParentPartitionAddr <> pdAddr *)
      simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in *. repeat rewrite removeDupIdentity; intuition.
  }
  destruct HpartIsPDTa as [HpartIsPDTa HlookupPartEqA].
  specialize(IHcutStatesList a newPdEntriesList pdAddr HpartIsPDTa HisBuilt). rewrite IHcutStatesList.
  assumption.
Admitted.*)

Lemma DisjointKSEntriesPreserved s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag:
DisjointKSEntries s0
-> StructurePointerIsKS s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> (StructurePointerIsKS s /\ DisjointKSEntries s /\ StructurePointerIsKS s1).
Proof.
intros Hdisjoint Hstruct HlookupPdAddr HlookupBlock HpropsOr Hs1.
assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
assert(Hstructs1: StructurePointerIsKS s1).
{
  unfold StructurePointerIsKS in *. intros entryaddr pdentry HlookupEntry HstructNotNull.
  assert(HlookupEntrysInit: lookup entryaddr (memory s0) beqAddr = Some (PDT pdentry)).
  {
    rewrite Hs1 in HlookupEntry. simpl in HlookupEntry.
    destruct (beqAddr blockInParentPartitionAddr entryaddr) eqn:HbeqBlockEntry; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HlookupEntry; intuition.
  }
  specialize(Hstruct entryaddr pdentry HlookupEntrysInit HstructNotNull). rewrite Hs1. unfold isKS in *. simpl.
  destruct (beqAddr blockInParentPartitionAddr (structure pdentry)) eqn:HbeqBlockStruct.
  - rewrite <-DTL.beqAddrTrue in HbeqBlockStruct. rewrite HbeqBlockStruct in *.
    rewrite HlookupBlock in Hstruct. rewrite <-Hstruct. unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
  - rewrite <-beqAddrFalse in HbeqBlockStruct. rewrite removeDupIdentity; intuition.
}
destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdAddr.
{
  rewrite <-DTL.beqAddrTrue in HbeqBlockPdAddr. rewrite HbeqBlockPdAddr in *.
  rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
}
assert(HlookupPdAddrs1: lookup pdAddr (memory s1) beqAddr = Some (PDT pdentry1)).
{
  rewrite Hs1. simpl. rewrite HbeqBlockPdAddr. rewrite <-beqAddrFalse in HbeqBlockPdAddr.
  rewrite removeDupIdentity; intuition.
}
split.
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. assumption.
  - unfold StructurePointerIsKS in *.
    intros entryaddr pdentry HlookupEntry HstructNotNull.
    assert(HlookupEntrys1: exists pdentrys1, lookup entryaddr (memory s1) beqAddr = Some (PDT pdentrys1)
                                             /\ structure pdentrys1 = structure pdentry).
    {
      rewrite Hs in HlookupEntry. simpl in HlookupEntry.
      destruct (beqAddr pdAddr entryaddr) eqn:HbeqPdaddrEntry.
      + rewrite <-DTL.beqAddrTrue in HbeqPdaddrEntry. rewrite HbeqPdaddrEntry in *.
        rewrite HlookupPdAddrs1. exists pdentry1. injection HlookupEntry as HpdentriesEq.
        rewrite <-HpdentriesEq. simpl. split. reflexivity. reflexivity.
      + rewrite <-beqAddrFalse in HbeqPdaddrEntry. exists pdentry.
        rewrite removeDupIdentity in HlookupEntry; intuition.
    }
    destruct HlookupEntrys1 as [pdentrys1 (HlookupEntrys1 & HstructEq)].
    rewrite <-HstructEq in HstructNotNull.
    specialize(Hstructs1 entryaddr pdentrys1 HlookupEntrys1 HstructNotNull).
    rewrite <-HstructEq. unfold isKS in *. rewrite Hs. simpl.
    destruct (beqAddr pdAddr (structure pdentrys1)) eqn:HbeqPdaddrStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqPdaddrStruct. rewrite HbeqPdaddrStruct in *.
      rewrite HlookupPdAddrs1 in Hstructs1. congruence.
    }
    rewrite <-beqAddrFalse in HbeqPdaddrStruct. rewrite removeDupIdentity; intuition.
}
(**) split.
unfold DisjointKSEntries in *. intros pd1 pd2 HisPDT1 HisPDT2 Hpd1NotPd2.
assert(HisPDT1A: isPDT pd1 s0).
{
  unfold isPDT in *. destruct HpropsOr as [Has1Eq | Hs].
  - subst s. rewrite Hs1 in HisPDT1. simpl in HisPDT1.
    destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity in HisPDT1; intuition.
  - rewrite Hs in HisPDT1. rewrite Hs1 in HisPDT1. simpl in HisPDT1.
    destruct (beqAddr pdAddr pd1) eqn:HbeqPdaddrPd1.
    + rewrite <-DTL.beqAddrTrue in HbeqPdaddrPd1. rewrite HbeqPdaddrPd1 in *. rewrite HlookupPdAddr.
      trivial.
    + rewrite HbeqBlockPdAddr in HisPDT1. simpl in HisPDT1.
      destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HisPDT1; intuition.
      rewrite removeDupIdentity in HisPDT1; intuition.
}
assert(HisPDT2A: isPDT pd2 s0).
{
  unfold isPDT in *. destruct HpropsOr as [Has1Eq | Hs].
  - subst s. rewrite Hs1 in HisPDT2. simpl in HisPDT2.
    destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity in HisPDT2; intuition.
  - rewrite Hs in HisPDT2. rewrite Hs1 in HisPDT2. simpl in HisPDT2.
    destruct (beqAddr pdAddr pd2) eqn:HbeqPdaddrPd2.
    + rewrite <-DTL.beqAddrTrue in HbeqPdaddrPd2. rewrite HbeqPdaddrPd2 in *. rewrite HlookupPdAddr.
      trivial.
    + rewrite HbeqBlockPdAddr in HisPDT2. simpl in HisPDT2.
      destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HisPDT2; intuition.
      rewrite removeDupIdentity in HisPDT2; intuition.
}
specialize(Hdisjoint pd1 pd2 HisPDT1A HisPDT2A Hpd1NotPd2).
destruct Hdisjoint as [optionEntriesList1 (optionEntriesList2 & (Hlist1 & Hlist2 & Hdisjoint))].
exists optionEntriesList1. exists optionEntriesList2.
split. subst optionEntriesList1. destruct HpropsOr as [Hss1Eq | Hs].
{
  subst s. apply eq_sym. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock. trivial.
}
{
  assert(HgetKSEq: getKSEntries pd1 s = getKSEntries pd1 s1).
  {
    rewrite Hs. apply getKSEntriesEqPDT with pdentry1; try(assumption). unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
  }
  rewrite HgetKSEq. apply eq_sym. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock.
  trivial.
}
split. subst optionEntriesList2. destruct HpropsOr as [Hss1Eq | Hs].
{
  subst s. apply eq_sym. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock. trivial.
}
{
  assert(HgetKSEq: getKSEntries pd2 s = getKSEntries pd2 s1).
  {
    rewrite Hs.
    apply getKSEntriesEqPDT with pdentry1; try(assumption). unfold CBlockEntry.
    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
  }
  rewrite HgetKSEq. apply eq_sym. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlock.
  trivial.
}
assumption. assumption.
Qed.

Lemma ParentsPreserved s s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry newMPU flag:
parentOfPartitionIsPartition s0
-> lookup pdAddr (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdAddr
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := newMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> parentOfPartitionIsPartition s.
Proof.
intros Hparent HlookupPdAddr HlookupBlock HpropsOr Hs1 partition entryPart HlookupPart.
set(newBentry:= CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry)).
assert(HlookupBlocks1: lookup blockInParentPartitionAddr (memory s1) beqAddr = Some (BE newBentry)).
{
  rewrite Hs1. simpl. rewrite beqAddrTrue. subst newBentry. reflexivity.
}
assert(HlookupBlocks: lookup blockInParentPartitionAddr (memory s) beqAddr = Some (BE newBentry)).
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. assumption.
  - rewrite Hs. simpl.
    destruct (beqAddr pdAddr blockInParentPartitionAddr) eqn:HbeqParentBlock.
    {
      rewrite <-DTL.beqAddrTrue in HbeqParentBlock. rewrite HbeqParentBlock in *.
      rewrite HlookupBlock in HlookupPdAddr. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
}
assert(HlookupPartEqs1: lookup partition (memory s1) beqAddr = lookup partition (memory s0) beqAddr).
{
  rewrite Hs1. simpl.
  destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *.
    rewrite HlookupPart in HlookupBlocks. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; intuition.
}
assert(HlookupParts0: exists entryParts0, lookup partition (memory s0) beqAddr = Some (PDT entryParts0)
                                          /\ parent entryParts0 = parent entryPart).
{
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. rewrite <-HlookupPartEqs1. exists entryPart. intuition.
  - rewrite Hs in HlookupPart. simpl in HlookupPart.
    destruct (beqAddr pdAddr partition) eqn:HbeqPdAddrPart.
    + injection HlookupPart as HentriesEq. rewrite <-DTL.beqAddrTrue in HbeqPdAddrPart.
      rewrite HbeqPdAddrPart in *. exists pdentry1. rewrite <-HentriesEq. simpl. intuition.
    + rewrite <-beqAddrFalse in HbeqPdAddrPart. rewrite removeDupIdentity in HlookupPart; intuition.
      exists entryPart. rewrite HlookupPartEqs1 in HlookupPart. intuition.
}
destruct HlookupParts0 as [entryParts0 (HlookupParts0 & HparentsEq)].
specialize(Hparent partition entryParts0 HlookupParts0). rewrite HparentsEq in *.
destruct Hparent as (HparentOfPart & HparentOfRoot & HparentNotPart). split.
{
  intro HpartNotRoot. specialize(HparentOfPart HpartNotRoot).
  destruct HparentOfPart as [parentEntry HlookupParent].
  assert(HlookupParents1: lookup (parent entryPart) (memory s1) beqAddr = Some (PDT parentEntry)).
  {
    rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr (parent entryPart)) eqn:HbeqBlockParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *.
      rewrite HlookupBlock in HlookupParent. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
  }
  destruct HpropsOr as [Hss1Eq | Hs].
  - subst s. exists parentEntry. assumption.
  - rewrite Hs. simpl. destruct (beqAddr pdAddr (parent entryPart)) eqn:HbeqPdAddrParent.
    + exists ({|
               structure := structure pdentry1;
               firstfreeslot := firstfreeslot pdentry1;
               nbfreeslots := nbfreeslots pdentry1;
               nbprepare := nbprepare pdentry1;
               parent := parent pdentry1;
               MPU := newMPU;
               vidtAddr := vidtAddr pdentry1
             |}). reflexivity.
    + exists parentEntry. rewrite <-beqAddrFalse in HbeqPdAddrParent. rewrite removeDupIdentity; intuition.
}
split.
{
  intro HpartIsRoot. specialize(HparentOfRoot HpartIsRoot). assumption.
}
assumption.
Qed.
(*TODO P*)
(*Lemma isBuiltRec s s1 s0 initState partition pdparent pdentry1 pdentryBase blockInParentPartitionAddr bentry
    realMPU flag cutStatesList parentsList:
pdentryMPU pdparent realMPU s1
-> (s = s1
    \/
     s =
     {|
       currentPartition := currentPartition s1;
       memory :=
         add pdparent
           (PDT
              {|
                structure := structure pdentry1;
                firstfreeslot := firstfreeslot pdentry1;
                nbfreeslots := nbfreeslots pdentry1;
                nbprepare := nbprepare pdentry1;
                parent := ADT.parent pdentry1;
                MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                vidtAddr := vidtAddr pdentry1
              |}) (memory s1) beqAddr
     |})
-> pdparent = parent pdentryBase
-> lookup pdparent (memory s0) beqAddr = Some (PDT pdentry1)
-> lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
-> bentryPFlag blockInParentPartitionAddr true s0
-> In blockInParentPartitionAddr (getMappedBlocks pdparent s0)
-> s1 =
      {|
        currentPartition := currentPartition s0;
        memory :=
          add blockInParentPartitionAddr
            (BE
               (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                  (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
      |}
-> lookup partition (memory s0) beqAddr = Some (PDT pdentryBase)
-> isBuiltFromWriteAccessibleRec initState s0 cutStatesList parentsList partition flag
-> isBuiltFromWriteAccessibleRec initState s (cutStatesList++[s]) (parentsList++[pdparent]) partition flag.
Proof.
intros HMPU HpropsOr Hparent HlookupParent HlookupBlock HPFlag HblockIsMapped Hs1.
revert initState. revert partition. induction cutStatesList.
- (* cutStatesList = [] *)
  simpl.
  intros partition initState HlookupBase HisBuilt.
  destruct HisBuilt as [HparentsList Hs0sInEq]. subst parentsList. subst s0. simpl.
  exists pdparent. exists []. split. reflexivity. exists realMPU. exists pdentryBase. exists pdentry1.
  exists blockInParentPartitionAddr. exists bentry. exists (CBlockEntry (read bentry) (write bentry)
    (exec bentry) (present bentry) flag (blockindex bentry) (blockrange bentry)). exists s1. split. assumption.
  assert(HcurrPartEq: currentPartition s1 = currentPartition initState).
  { rewrite Hs1. simpl. reflexivity. }
  rewrite <-HcurrPartEq. split.
  {
    destruct HpropsOr as [Hss1Eq | Hs].
    + left. assumption.
    + right. split. assumption. assumption.
  }
  split. intro. reflexivity. split. reflexivity. split. assumption. split. rewrite Hs1. simpl.
  rewrite beqAddrTrue. reflexivity. split. assumption. split. assumption. split. assumption. split. rewrite Hs1.
  simpl. destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst blockInParentPartitionAddr.
    rewrite HlookupBase in HlookupBlock. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; intuition. split. assumption.
  split. rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
    rewrite HlookupParent in HlookupBlock. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition. intuition.
- (* cutStatesList = a::l *)
  simpl.
  intros partition initState HlookupBase HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsListRec & (realMPULast & (pdentryBaseBis &
                        (pdentryParent & (blockInParentPartitionAddrLast & (bentryLast & (newBentryLast &
                        (s1' & HisBuilt)))))))))].
  destruct HisBuilt as [].
  exists pdAddr. exists (newPdEntriesList++[pdparent]). split. rewrite HparentsListRec. reflexivity.
  exists realMPULast. exists pdentryBaseBis. exists pdentryParent. exists blockInParentPartitionAddrLast.
  exists bentryLast. exists newBentryLast. exists s1'.
  specialize(IHcutStatesList a ).
Qed.*)

Lemma lookupBEEqWriteAccess addr cutStatesList initState parentsList parent flag s partition:
isPDT partition initState
-> isBE addr initState
-> DisjointKSEntries initState
-> StructurePointerIsKS initState
-> ~In partition parentsList
-> In addr (getMappedBlocks partition initState)
-> isBuiltFromWriteAccessibleRec initState s cutStatesList parentsList parent flag
-> lookup addr (memory s) beqAddr = lookup addr (memory initState) beqAddr.
Proof.
revert parent. revert parentsList. revert initState. revert partition. induction cutStatesList.
- (* cutStatesList = [] *)
  simpl.
  intros partition initState parentsList parent HpartIsPDT HaddrIsBE Hdisjoint Hstruct HpartNotParent
      HaddrIsMapped Hprops.
  destruct Hprops as [HparentsList HssInitEq]. subst s. reflexivity.
- (* cutStatesList = a::l *)
  simpl.
  intros partition initState parentsList parent HpartIsPDT HaddrIsBE Hdisjoint Hstruct HpartNotParent
      HaddrIsMapped Hprops.
  destruct Hprops as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr & (HlastCase &
                       (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockIsMapped & HlookupParentsInit
                        & HlookupParents1 & HlookupAncestorsInit & HlookupAncestors1 & Hancestor &
                         HisBuilt)))))))))))))].
  assert(HpartNotPdaddr: partition <> pdAddr).
  {
    rewrite HparentsList in HpartNotParent. simpl in HpartNotParent. apply Decidable.not_or in HpartNotParent.
    intuition.
  }
  destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockOldBlock.
  { (* blockInParentPartitionAddr = addr *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockOldBlock. rewrite HbeqBlockOldBlock in *. unfold getMappedBlocks in *.
    unfold DisjointKSEntries in Hdisjoint.
    assert(HpdaddrIsPDT: isPDT pdAddr initState) by (unfold isPDT; rewrite HlookupAncestorsInit; trivial).
    specialize(Hdisjoint partition pdAddr HpartIsPDT HpdaddrIsPDT HpartNotPdaddr).
    destruct Hdisjoint as [optionEntriesList1 (optionEntriesList2 & (Hlist1 & Hlist2 & Hdisjoint))].
    subst optionEntriesList1. subst optionEntriesList2. unfold Lib.disjoint in Hdisjoint.
    assert(HaddrIsKS: In addr (filterOptionPaddr (getKSEntries partition initState))).
    {
      clear HblockIsMapped. clear Hdisjoint. induction (filterOptionPaddr (getKSEntries partition initState));
                try(simpl in HaddrIsMapped; exfalso; congruence).
      simpl. simpl in HaddrIsMapped.
      destruct (lookup a0 (memory initState) beqAddr); try(right; apply IHl; intuition; congruence).
      destruct v; try(right; apply IHl; intuition; congruence).
      destruct (present b); try(right; apply IHl; intuition; congruence). simpl in HaddrIsMapped.
      destruct HaddrIsMapped. left. assumption. right. apply IHl. assumption.
    }
    assert(HblockIsKS: In addr (filterOptionPaddr (getKSEntries pdAddr initState))).
    {
      clear HaddrIsMapped. clear Hdisjoint. induction (filterOptionPaddr (getKSEntries pdAddr initState));
                try(simpl in HblockIsMapped; exfalso; congruence).
      simpl. simpl in HblockIsMapped.
      destruct (lookup a0 (memory initState) beqAddr); try(right; apply IHl; intuition; congruence).
      destruct v; try(right; apply IHl; intuition; congruence).
      destruct (present b); try(right; apply IHl; intuition; congruence). simpl in HblockIsMapped.
      destruct HblockIsMapped. left. assumption. right. apply IHl. assumption.
    }
    specialize(Hdisjoint addr HaddrIsKS). exfalso; congruence.
  }
  (* blockInParentPartitionAddr <> addr *)
  destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
  { (* blockInParentPartitionAddr = partition *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *. unfold isPDT in HpartIsPDT.
    rewrite HlookupBlocks0 in HpartIsPDT. exfalso; congruence.
  }
  (* blockInParentPartitionAddr <> partition *)
  destruct (beqAddr pdAddr partition) eqn:HbeqAncestorPart.
  { (* pdAddr = partition *)
    rewrite <-DTL.beqAddrTrue in HbeqAncestorPart. subst partition. exfalso; congruence.
  }
  (* pdAddr <> partition *)
  destruct (beqAddr blockInParentPartitionAddr pdAddr) eqn:HbeqBlockPdaddr.
  { (* blockInParentPartitionAddr = pdAddr *)
    rewrite <-DTL.beqAddrTrue in HbeqBlockPdaddr. rewrite HbeqBlockPdaddr in *.
    rewrite HlookupBlocks0 in HlookupAncestorsInit. exfalso; congruence.
  }
  (* blockInParentPartitionAddr <> pdAddr *)
  assert(HpartIsPDTa: isPDT partition a).
  {
    unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite Hs1. simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in HbeqBlockPart.
      rewrite removeDupIdentity; intuition.
    - destruct Ha as [Ha HMPU]. rewrite Ha. rewrite Hs1. simpl. rewrite HbeqAncestorPart.
      rewrite HbeqBlockPdaddr. simpl. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in *.
      repeat rewrite removeDupIdentity; intuition.
  }
  assert(HcurPartEq: currentPartition initState = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPartEq in HpropsOr.
  assert(HpartConsist: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  { apply DisjointKSEntriesPreserved with initState pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition. }
  destruct HpartConsist as [HstructA (HdisjointA & Hstructs1)].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HpartNotParentRec: ~ In partition newPdEntriesList).
  {
    rewrite HparentsList in HpartNotParent. simpl in HpartNotParent. apply Decidable.not_or in HpartNotParent.
    destruct HpartNotParent. assumption.
  }
  assert(HaddrIsMappedA: In addr (getMappedBlocks partition a)).
  {
    assert(HgetMappedEqs1: getMappedBlocks partition s1 = getMappedBlocks partition initState).
    {
      rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    assert(HgetMappedEq: getMappedBlocks partition a = getMappedBlocks partition initState).
    {
      rewrite <-HgetMappedEqs1. destruct HpropsOr as [Has1Eq | Ha].
      - subst a. reflexivity.
      - destruct Ha as [Ha HMPU]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1.
        assumption. assumption. unfold CBlockEntry.
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
    }
    rewrite HgetMappedEq. assumption.
  }
  assert(HlookupAddrEq: lookup addr (memory a) beqAddr = lookup addr (memory initState) beqAddr).
  {
    assert(HlookupEq: lookup addr (memory s1) beqAddr = lookup addr (memory initState) beqAddr).
    {
      rewrite Hs1. simpl. rewrite HbeqBlockOldBlock. rewrite <-beqAddrFalse in HbeqBlockOldBlock.
      rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupEq. destruct HpropsOr as [Has1Eq | Ha].
    + subst a. reflexivity.
    + destruct Ha as [Ha HMPU]. rewrite Ha. simpl. destruct (beqAddr pdAddr addr) eqn:HbeqPdaddrAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqPdaddrAddr. rewrite HbeqPdaddrAddr in *. unfold isBE in HaddrIsBE.
        rewrite HlookupAncestorsInit in HaddrIsBE. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in HbeqPdaddrAddr. rewrite removeDupIdentity; intuition.
  }
  assert(HaddrIsBEa: isBE addr a).
  {
    unfold isBE in *. rewrite HlookupAddrEq. assumption.
  }
  specialize(IHcutStatesList partition a newPdEntriesList pdAddr HpartIsPDTa HaddrIsBEa HdisjointA HstructA
               HpartNotParentRec HaddrIsMappedA HisBuilt).
  rewrite IHcutStatesList. assumption.
Qed.

(*Lemma lookupPDTEqWriteAccess cutStatesList initState parentsList pdparent flag s partition:
isPDT partition initState
(*-> DisjointKSEntries initState
-> StructurePointerIsKS initState*)
-> ~In pdparent parentsList
-> isBuiltFromWriteAccessibleRec initState s cutStatesList parentsList partition flag
-> lookup pdparent (memory s) beqAddr = lookup pdparent (memory initState) beqAddr.
Proof.
revert parentsList. revert initState. revert partition. induction cutStatesList.
- (* cutStatesList = [] *)
  simpl.
  intros partition initState parentsList HlookupPartsInit HpartNotParent Hprops.
  destruct Hprops as [HparentsList HssInitEq]. subst s. reflexivity.
- (* cutStatesList = a::l *)
  simpl.
  intros partition initState parentsList HlookupPartsInit HpartNotParent Hprops.
  destruct Hprops as [Hinit Hrec]. destruct Hrec as [pdAddr Hprops]. intro Hcontra. apply Hinit. assumption.
  destruct Hprops as [newPdEntriesList (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr & (HlastCase &
                       (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockIsMapped & HlookupParentsInit
                        & HlookupParents1 & HlookupAncestorsInit & HlookupAncestors1 & Hancestor &
                         HisBuilt))))))))))))].
  assert(HpdAddrIsPDTA: isPDT pdAddr a).
  {
    unfold isPDT. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite HlookupAncestors1. trivial.
    - destruct Ha as [Ha HMPU]. rewrite Ha. simpl. rewrite beqAddrTrue. trivial.
  }
  rewrite HparentsList in HpartNotParent. simpl in HpartNotParent. apply Decidable.not_or in HpartNotParent.
  destruct HpartNotParent as [HpdAddrNotParent HpartNotParent].
  specialize(IHcutStatesList pdAddr a newPdEntriesList HpdAddrIsPDTA HpartNotParent HisBuilt).
  rewrite IHcutStatesList.
  assert(HlookupEqs1: lookup pdparent (memory s1) beqAddr = lookup pdparent (memory initState) beqAddr).
  {
    rewrite Hs1. simpl.
  }
Qed.*)


Lemma isListOfKernelsEqBE kernList partition addr newEntry s0:
isListOfKernels kernList partition {|
					                           currentPartition := currentPartition s0;
					                           memory := add addr (BE newEntry) (memory s0) beqAddr
                                   |}
-> isListOfKernels kernList partition s0.
Proof.
destruct kernList as [ | kern nextKernList]; simpl.
- (* kernList = [] *)
  simpl. intuition.
- (* kernList = a::l *)
  simpl. intros HisKernLists1.
  destruct HisKernLists1 as [pdentry (HlookupPart & HstructNotNull & Hstruct & HindProp)].
  destruct (beqAddr addr partition) eqn:HbeqAddrPart; try(exfalso; congruence).
  rewrite <-beqAddrFalse in HbeqAddrPart. rewrite removeDupIdentity in HlookupPart; intuition.
  exists pdentry. intuition. clear Hstruct. clear HbeqAddrPart. revert HindProp. revert kern.
  induction nextKernList.
  + (* nextKernList = [] *)
    simpl. intuition.
  + (* nextKernList = a::l *)
    simpl. intros kern HpropsInd.
    destruct HpropsInd as [HlookupNextOffset (HaNotNull & HpropsInd)].
    destruct (beqAddr addr (CPaddr (kern + nextoffset))) eqn:HbeqAddNextKern; try(exfalso; congruence).
    rewrite <-beqAddrFalse in HbeqAddNextKern. rewrite removeDupIdentity in HlookupNextOffset; intuition.
Qed.

Lemma removeBlockFromPhysicalMPUAuxIncl block removedBlock MPU:
In block (MAL.removeBlockFromPhysicalMPUAux removedBlock MPU)
-> In block MPU.
Proof.
induction MPU.
- (* MPU = [] *)
  simpl. intuition.
- (* MPU = a::l *)
  intro HblockInNewMPU. simpl in HblockInNewMPU. destruct (beqAddr a removedBlock) eqn:HbeqElRemoved.
  + (* a = removedBlock *)
    simpl. right. assumption.
  + (* a <> removedBlock *)
    simpl in *. destruct HblockInNewMPU as [HaIsBlock | HblockInMPU].
    * left. assumption.
    * right. apply IHMPU. assumption.
Qed.

Lemma filterPresentIncl addr addrList s:
In addr (filterPresent addrList s)
-> In addr addrList.
Proof.
induction addrList.
- intro Hcontra. simpl in Hcontra. exfalso; congruence.
- intro HaddrInFiltr. simpl in HaddrInFiltr. simpl.
  destruct (lookup a (memory s) beqAddr); try(right; apply IHaddrList; assumption).
  destruct v; try(right; apply IHaddrList; assumption).
  destruct (present b).
  + simpl in HaddrInFiltr. destruct HaddrInFiltr as [HaIsAddr | Hind].
    * left. assumption.
    * right. apply IHaddrList. assumption.
  + right. apply IHaddrList. assumption.
Qed.


Lemma getMappedBlocksEqBuiltWithWriteAcc s0 s statesList parentsList pdbasepartition buildPart flag:
DisjointKSEntries s0
-> StructurePointerIsKS s0
-> parentOfPartitionIsPartition s0
-> isPDT pdbasepartition s0
-> isBuiltFromWriteAccessibleRec s0 s statesList parentsList buildPart flag
-> getMappedBlocks pdbasepartition s = getMappedBlocks pdbasepartition s0.
Proof.
revert buildPart. revert parentsList. revert s0. induction statesList.
- (* statesList = [] *)
  intros s0 parentsList buildPart Hdisjoint Hstruct Hparent HbaseIsPDT HisBuilt.
  simpl in HisBuilt. destruct HisBuilt as [HparentsList Hss0Eq]. subst s. reflexivity.
- (* statesList = a::l *)
  intros s0 parentsList buildPart Hdisjoint Hstruct Hparent HbaseIsPDT HisBuilt.
  simpl in HisBuilt.
  destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentry0 & pdentry1 &
                      (blockInParentPartitionAddr & (bentry & (newBentry & (s1 & (Hs1 & (HpropsOr & (HlastCase
                       & (HnewB & (HlookupBlocks0 & HlookupBlocks1 & HPFlag & HblockIsMapped &
                        HlookupParentsInit & HlookupParents1 & HlookupAncestorsInit & HlookupAncestors1 &
                         Hancestor & HisBuilt)))))))))))))].
  assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  assert(HcurPart: currentPartition s0 = currentPartition s1) by (rewrite Hs1; simpl; reflexivity).
  rewrite HcurPart in HpropsOr.
  assert(HpartConsist: StructurePointerIsKS a /\ DisjointKSEntries a /\ StructurePointerIsKS s1).
  {
    apply DisjointKSEntriesPreserved with s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
          (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  destruct HpartConsist as [HstructA (HdisjointA & Hstructs1)].
  assert(HbaseAndParentArePDT: isPDT pdbasepartition s0 /\ isPDT pdAddr s0).
  {
    unfold isPDT in *. rewrite HlookupAncestorsInit. intuition.
  }
  destruct HbaseAndParentArePDT as [HbaseIsPDTs0 HpdAddrIsPDTs0].
  assert(HbaseIsPDTs1: isPDT pdbasepartition s1).
  {
    unfold isPDT. rewrite Hs1. simpl.
    destruct (beqAddr blockInParentPartitionAddr pdbasepartition) eqn:HbeqBlockBase.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBase. rewrite HbeqBlockBase in *. unfold isPDT in HbaseIsPDT.
      rewrite HlookupBlocks0 in HbaseIsPDT. congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBase. rewrite removeDupIdentity; intuition.
  }
  assert(HbaseAndParentArePDT: isPDT pdbasepartition a /\ isPDT pdAddr a).
  {
    unfold isPDT in *. destruct HpropsOr as [Has1Eq | Ha].
    - subst a. rewrite HlookupAncestors1. intuition.
    - destruct Ha as [Ha HMPU]. rewrite Ha. simpl. rewrite beqAddrTrue.
      destruct (beqAddr pdAddr pdbasepartition) eqn:HbeqPdAddrBase; try(intuition; congruence).
      rewrite <-beqAddrFalse in HbeqPdAddrBase. rewrite removeDupIdentity; intuition.
  }
  destruct HbaseAndParentArePDT as [HbaseIsPDTA HpdAddrIsPDTA].
  assert(HparentA: parentOfPartitionIsPartition a).
  {
    apply ParentsPreserved with s1 s0 pdAddr pdentry1 blockInParentPartitionAddr bentry
        (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
  }
  specialize(IHstatesList a newPdEntriesList pdAddr HdisjointA HstructA HparentA HbaseIsPDTA HisBuilt).
  rewrite IHstatesList.
  assert(HgetMappedEqs1: getMappedBlocks pdbasepartition s1 = getMappedBlocks pdbasepartition s0).
  {
    rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
    unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    simpl. reflexivity.
  }
  rewrite <-HgetMappedEqs1.
  destruct HpropsOr as [Has1Eq | Ha].
  + (* a = s1 *)
    rewrite Has1Eq. reflexivity.
  + (* a <> s1 *)
    destruct Ha as [Ha HMPU]. rewrite Ha. apply getMappedBlocksEqPDT with pdentry1; intuition.
Qed.



Lemma removeBlockFromPhysicalMPU (pd : paddr) (blockentryaddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT pd s	}}
MAL.removeBlockFromPhysicalMPU pd blockentryaddr
{{fun (_ : unit) (s : state) =>
      exists s0 pdentry realMPU,
          pdentryMPU pd realMPU s0
          /\ P s0
          /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
          /\ s = {|
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
                             MPU := MAL.removeBlockFromPhysicalMPUAux blockentryaddr realMPU;
                             vidtAddr := vidtAddr pdentry
                           |}) (memory s0) beqAddr
                  |}
}}.
Proof.
unfold MAL.removeBlockFromPhysicalMPU. eapply bindRev.
{
  eapply weaken. apply readPDMPU. intros s Hprops. simpl. split. apply Hprops. intuition.
}
intro realMPU. eapply bindRev.
- eapply weaken. apply writePDMPU.
  intros s Hprops. simpl. destruct Hprops as [(HPs & HPDT) Hpdentry]. unfold isPDT in HPDT.
  destruct (lookup pd (memory s) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists p. split. reflexivity.
  instantiate(1:= fun (_:unit) (s:state) =>
              exists s0 pdentry,
                pdentryMPU pd realMPU s0
                /\ P s0
                /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
                /\ s = {|
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
                                   MPU := MAL.removeBlockFromPhysicalMPUAux blockentryaddr realMPU;
                                   vidtAddr := vidtAddr pdentry
                                 |}) (memory s0) beqAddr
                        |}
  ).
  simpl. exists s. exists p. intuition.
- intro. simpl. eapply weaken. apply WP.ret.
  simpl. intros s Hprops. destruct Hprops as [s0 (pdentry & Hprops)].
  exists s0. exists pdentry. exists realMPU. intuition.
Qed.

Lemma writeAccessibleRecAux (timeout : nat) (partition entryaddr : paddr) (flag : bool)
                          (P : state -> Prop):
{{fun s => consistency1 s
           /\ noDupUsedPaddrList s
           /\ sharedBlockPointsToChild s
           /\ (exists s0, (*exists statesList parentsList pdbasepartition,*) (*TODO verify that*)
                  P s0
                  /\ consistency s0
                  (*/\ isParentsList s0 parentsList pdbasepartition*)
                  (*/\ s = last statesList s0*)
                  (*/\ (exists entry, lookup pdbasepartition (memory s) beqAddr = Some (PDT entry))*)
                  /\ (exists ancestorEntry, lookup partition (memory s) beqAddr = Some (PDT ancestorEntry))
                  /\ (exists blockaddr bentry, (*changed the order to put the exists out of the OR*)
                        lookup blockaddr (memory s) beqAddr = Some (BE bentry)
                        /\ bentryPFlag blockaddr true s
                        /\ bentryAFlag blockaddr flag s
                        /\ In blockaddr (getMappedBlocks partition s)
                        /\ bentryStartAddr blockaddr entryaddr s
                        /\ (s = s0 \/
                            ((*s <> s0
                            /\*) (forall parent child addr,
                                        (child <> partition \/ ~ In addr (getAllPaddrAux [blockaddr] s))
                                        -> In parent (getPartitions multiplexer s)
                                        -> In child (getChildren parent s)
                                        -> In addr (getAccessibleMappedPaddr parent s)
                                        -> In addr (getMappedPaddr child s)
                                        -> In addr (getAccessibleMappedPaddr child s)))))
                  (*/\ isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition flag*)
                  /\ accessibleParentPaddrIsAccessibleIntoChild s0)
}}
writeAccessibleRecAux timeout partition entryaddr flag
{{fun writeSucceded s =>
      exists s0 (*pdentryBase*),
        (* Common properties *)
        P s0
        /\ accessibleParentPaddrIsAccessibleIntoChild s0
        (*/\ lookup partition (memory s) beqAddr = Some (PDT pdentryBase)*)
        /\ consistency1 s
        /\ noDupUsedPaddrList s
        /\ sharedBlockPointsToChild s
        (*/\ (timeout > maxAddr -> writeSucceded = true)*) (*probably true, but impossible to prove*)
        /\ (writeSucceded = true -> accessibleParentPaddrIsAccessibleIntoChild s)
        (*/\ ((* Base case: starting at the root *)
            (s0 = s /\ parentsList = [] /\ statesList = []
                    /\ ((*flag = false \/*) pdbasepartition = constantRootPartM \/ writeSucceded = false))
            \/
            (* Induction case *)
            (isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition flag))*)}}.
Proof.
revert partition. revert P. induction timeout.
{
  simpl. intros P pdbasepartition. eapply weaken. eapply WP.ret.
  intros s Hprops. simpl.
  destruct Hprops as [Hconsist (HnoDup & Hshared & Hprops)].
  destruct Hprops as [s0 (HPs0 & Hconsists0 (*& HisParentsList*) & HisPDT & HpartialAccessChild & Haccesss0)].
  exists s0.
  (*destruct HisPDT as [pdentryBase Hlookup].
  exists pdentryBase.*) unfold consistency in *. unfold consistency2 in *.
  intuition.
}
(* N <> 0 *)
intros P pdbasepartition. simpl. destruct (beqAddr pdbasepartition constantRootPartM) eqn:HbeqBaseRoot.
- rewrite <-DTL.beqAddrTrue in HbeqBaseRoot. rewrite HbeqBaseRoot in *. eapply weaken. apply WP.ret.
  intros s Hprops. simpl.
  destruct Hprops as [Hconsist (HnoDup & Hshared & Hprops)].
  destruct Hprops as [s0 (HPs0 & Hconsists0 (*& HisParentsList*) & HisPDT & HpartialAccessChild & Haccesss0)].
  exists s0.
  (*destruct HisPDT as [pdentryBase Hlookup].
  exists pdentryBase.*) intuition.
  destruct HpartialAccessChild as [blockaddr (bentryAddr & (HlookupBlock & HPFlag & HAFlag & HblockIsMapped &
                    HstartAddr & HpartialAccessChild))].
  destruct HpartialAccessChild as [Hss0Eq | HpartialAccess].
  + subst s. assumption.
  + intros parent child addr HparentIsPart HchildIsChild HaddrIsMappedAccInParent HaddrIsMappedInChild.
    assert(HnotSpecialCase: (child <> constantRootPartM) \/ ~ In addr (getAllPaddrAux [blockaddr] s)).
    {
      left. intro Hcontra. subst child.
      assert(HparentIsParent: isParent s) by (unfold consistency1 in *; intuition).
      specialize(HparentIsParent constantRootPartM parent HparentIsPart HchildIsChild).
      unfold pdentryParent in HparentIsParent.
      destruct (lookup constantRootPartM (memory s) beqAddr) eqn:HlookupRoot; try(congruence).
      destruct v; try(congruence).
      assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
      specialize(HparentOfPart constantRootPartM p HlookupRoot).
      destruct HparentOfPart as (HparentOfPart & HparentOfRoot & HparentNotPart).
      assert(Htriv: constantRootPartM = constantRootPartM) by reflexivity.
      specialize(HparentOfRoot Htriv). rewrite HparentOfRoot in *. subst parent.
      assert(HnullIsPDT: isPDT nullAddr s).
      {
        unfold consistency1 in *; apply partitionsArePDT; intuition.
      }
      assert(HnullIsPADDR: isPADDR nullAddr s).
      {
        assert(Hcons: nullAddrExists s) by (unfold consistency1; intuition).
        unfold nullAddrExists in Hcons. assumption.
      }
      unfold isPDT in HnullIsPDT. unfold isPADDR in HnullIsPADDR.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
      destruct v; congruence.
    }
    specialize(HpartialAccess parent child addr HnotSpecialCase HparentIsPart HchildIsChild
                HaddrIsMappedAccInParent HaddrIsMappedInChild).
    assumption.
- eapply bindRev.
  { (** MAL.readPDParent and MAL.getPDTRecordField **)
    unfold MAL.readPDParent. eapply weaken. eapply getPDTRecordField.
    intros s Hprops. simpl.
    destruct Hprops as [Hconsist1 (HnoDup & Hshared & (s0 & (HPs0 & Hconsists0 (*&
                         HisParentsList*) & HPDBase & HpartialAccess & Haccess)))].
    destruct HPDBase as [entry HPDBase]. exists entry.
    split. assumption.
    instantiate(1:= fun (parentEntry: paddr) (s: state) =>
                    consistency1 s
                    /\ noDupUsedPaddrList s
                    /\ sharedBlockPointsToChild s
                    /\ exists s0 pdentryBase (*lastPdentryBase*),
                          P s0
                          /\ consistency s0
                          (*/\ isParentsList s0 parentsList pdbasepartition*)
                          (*/\ lookup pdbasepartition (memory s) beqAddr = Some (PDT lastPdentryBase)*)
                          /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase)
                          /\ accessibleParentPaddrIsAccessibleIntoChild s0
                          (*/\ bentryAFlag entryaddr true s0*)
                          (*/\ parent lastPdentryBase = parent pdentryBase*)
                          /\ parentEntry = pdentryBase.(parent)
                          /\ (exists blockaddr bentry,
                                    lookup blockaddr (memory s) beqAddr = Some (BE bentry)
                                    /\ bentryPFlag blockaddr true s
                                    /\ bentryAFlag blockaddr flag s
                                    /\ In blockaddr (getMappedBlocks pdbasepartition s)
                                    /\ bentryStartAddr blockaddr entryaddr s
                                    /\ (s = s0 \/
                                        ((*s <> s0
                                        /\*) (forall parent child addr,
                                                (child <> pdbasepartition
                                                    \/ ~ In addr (getAllPaddrAux [blockaddr] s))
                                                -> In parent (getPartitions multiplexer s)
                                                -> In child (getChildren parent s)
                                                -> In addr (getAccessibleMappedPaddr parent s)
                                                -> In addr (getMappedPaddr child s)
                                                -> In addr (getAccessibleMappedPaddr child s)))))).
    simpl. split. assumption. split. assumption. split. assumption. exists s0.
    exists entry. split. assumption. split. assumption. split.
    assumption. split. assumption. (*split. assumption.*) split.
    reflexivity. assumption.
  }
  intro pdparent. eapply bindRev.
  { (** Internal.findBlockInKS **)
    eapply weaken. eapply findBlockInKS.
    simpl. intros s Hprops. split. eapply Hprops.
    destruct Hprops as [Hconsist1 (HnoDup & Hshared & (s0 & (pdentryBase &
                        (HPs0 & Hconsists0 (*& HisParentsList*) & HlookupBases
                        & Haccesss0 & Hparent & Hprops))))].
    split. apply Hconsist1. unfold isPDT. rewrite Hparent.
    assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    unfold parentOfPartitionIsPartition in HparentOfPart.
    rewrite <-beqAddrFalse in HbeqBaseRoot.
    specialize(HparentOfPart pdbasepartition pdentryBase HlookupBases).
    destruct HparentOfPart as [HparentOfPart HparentRoot].
    specialize(HparentOfPart HbeqBaseRoot).
    destruct HparentOfPart as [childEntry HlookupParent].
    rewrite HlookupParent. trivial.
  }
  intro blockInParentPartitionAddr. simpl. eapply bindRev.
  { apply compareAddrToNull. }
  intro addrIsNull. destruct addrIsNull eqn:HaddrIsNull.
  * (* addrIsNull = true *)
    eapply weaken. eapply WP.ret.
    simpl. intros s Hprops.
    destruct Hprops as [((Hconsist1Copy & HnoDup & Hshared & Hpropss0) & Hconsist1 & HblockProps) HbeqNullBlock].
    destruct Hpropss0 as [s0 (pdentryBase & (HPs0 & Hconsists0
                           (*& HisParentsList*) & HlookupBases & Haccess & Hparent & HpartialAccess))].
    exists s0. (*exists pdentryBase.*) split.
    assumption. (*split. assumption.*) split. assumption. split. assumption. split. assumption. split. assumption.
    intuition.
  * (* addrIsNull = false *)
    eapply bindRev.
    { (** MAL.writeBlockAccessibleFromBlockEntryAddr **)
      eapply weaken. eapply writeBlockAccessibleFromBlockEntryAddr.
      simpl. intros s Hprops.
      destruct Hprops as [((Hconsist1Copy & HnoDup & Hshared & Hpropss0) & Hconsis1 & HblockProps)
                            HbeqNullBlock].
      destruct Hpropss0 as [s0 (pdentryBase & (HPs0 & Hconsists0
                             (*& HisParentsList*) & HlookupBases & Haccess & Hparent & HpartialAccess))].
      rewrite <-beqAddrFalse in HbeqNullBlock. apply not_eq_sym in HbeqNullBlock.
      destruct HblockProps as [Hcontra | HblockProps]; try(exfalso; congruence).
      destruct HblockProps as [bentry HblockProps]. exists bentry. split. intuition.
      (* see insertNewEntry, l.4 686 *)
      instantiate(1:= fun _ s =>
          exists sInit s0, exists pdentry: PDTable, (*exists pdentry0: PDTable,*)
            exists bentry newBentry: BlockEntry,
              s = {|
                    currentPartition := currentPartition s0;
                    memory :=
                      add blockInParentPartitionAddr
                        (BE
                           (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                              (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
                  |}
              /\ pdparent = parent pdentry
              /\ lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
              /\ lookup blockInParentPartitionAddr (memory s) beqAddr = Some (BE newBentry)
              /\ bentryPFlag blockInParentPartitionAddr true s
              /\ bentryAFlag blockInParentPartitionAddr flag s
              /\ In blockInParentPartitionAddr (getMappedBlocks pdparent s)
              /\ bentryStartAddr blockInParentPartitionAddr entryaddr s
              /\ newBentry = CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                              (blockindex bentry) (blockrange bentry)
              /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentry)
              /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentry)
              /\ consistency1 s0
              /\ noDupUsedPaddrList s0
              /\ sharedBlockPointsToChild s0
              /\ (exists (blockaddr : paddr) (bentry : BlockEntry),
                      lookup blockaddr (memory s) beqAddr = Some (BE bentry) /\
                      bentryPFlag blockaddr true s /\
                      bentryAFlag blockaddr flag s /\
                      In blockaddr (getMappedBlocks pdparent s) /\
                      bentryStartAddr blockaddr entryaddr s /\
                      (forall parent child addr : paddr,
                         (child <> pdparent \/ ~ In addr (getAllPaddrAux [blockaddr] s))
                         -> In parent (getPartitions multiplexer s)
                         -> In child (getChildren parent s)
                         -> In addr (getAccessibleMappedPaddr parent s)
                         -> In addr (getMappedPaddr child s)
                         -> In addr (getAccessibleMappedPaddr child s)))
              /\ P sInit
              /\ consistency sInit
              /\ accessibleParentPaddrIsAccessibleIntoChild sInit
      ).
      simpl. set (s' := {| currentPartition :=  _|}).
      destruct HblockProps as [HlookupBlock (HpresentBlock & (HblockIsMapped & (blockstart & (Hblockstart &
              HblockEq))))].
      exists s0. exists s. exists pdentryBase. exists bentry.
      set(newBentry := CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                            (blockindex bentry) (blockrange bentry)).
      exists newBentry. rewrite InternalLemmas.beqAddrTrue.
      destruct (beqAddr blockInParentPartitionAddr pdbasepartition) eqn:HbeqBlockBase.
      {
        rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqBlockBase. rewrite HbeqBlockBase in *.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqBlockBase. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      assert(HlookupBlocks': lookup blockInParentPartitionAddr (memory s') beqAddr = Some (BE newBentry)).
      { simpl. rewrite beqAddrTrue. subst newBentry. reflexivity. }
      assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
      assert(HgetMappedEq: getMappedBlocks pdparent s' = getMappedBlocks pdparent s).
      {
        subst s'. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
        reflexivity.
      }
      rewrite HgetMappedEq. rewrite <-DTL.beqAddrTrue in HblockEq. subst blockstart.
      intuition.
      unfold bentryPFlag in *. rewrite HlookupBlocks'. rewrite HlookupBlock in HpresentBlock.
      subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption.
      unfold bentryAFlag in *. rewrite HlookupBlocks'. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      reflexivity.
      unfold bentryStartAddr in *. rewrite HlookupBlocks'. rewrite HlookupBlock in Hblockstart. subst newBentry.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. intuition.
      exists blockInParentPartitionAddr. exists newBentry.
      rewrite beqAddrTrue. split. reflexivity. split. unfold bentryPFlag in *. rewrite HlookupBlocks'.
      rewrite HlookupBlock in HpresentBlock. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption. split. unfold bentryAFlag in *. rewrite HlookupBlocks'. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      reflexivity. split. assumption. split. unfold bentryStartAddr in *. rewrite HlookupBlocks'.
      rewrite HlookupBlock in Hblockstart. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption.
      intros parent child addr HnotEdgeCase HparentIsPart HchildIsChild HaddrIsMappedAccInParent
            HaddrIsMappedInChild.
      assert(HgetPartitionsEq: getPartitions multiplexer s' = getPartitions multiplexer s).
      {
        subst s'. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
                      with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
                    try(unfold consistency1 in Hconsis1; intuition; congruence).
        - unfold sh1entryAddr. rewrite HlookupBlock. reflexivity.
        - simpl.
          destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
                   eqn:HbeqBlocBlockSh1.
          {
            assert(HwellFormed: wellFormedFstShadowIfBlockEntry s) by (unfold consistency1 in *; intuition).
            unfold wellFormedFstShadowIfBlockEntry in HwellFormed.
            assert(Hsh1IsSHE: isSHE (CPaddr (blockInParentPartitionAddr + sh1offset)) s).
            { apply HwellFormed. unfold isBE. rewrite HlookupBlock. trivial. }
            rewrite <-DTL.beqAddrTrue in HbeqBlocBlockSh1. rewrite <-HbeqBlocBlockSh1 in *.
            unfold isSHE in Hsh1IsSHE. rewrite HlookupBlock in Hsh1IsSHE. exfalso; congruence.
           }
          rewrite <-beqAddrFalse in HbeqBlocBlockSh1. rewrite removeDupIdentity; intuition.
        - unfold CBlockEntry.
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
          reflexivity.
        - unfold CBlockEntry.
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
          reflexivity.
      }
      rewrite HgetPartitionsEq in HparentIsPart.
      assert(HgetChildrenEq: getChildren parent s' = getChildren parent s).
      {
        subst s'. apply getChildrenEqBENoStartNoPresentChange with bentry;
                   try(assumption);
                   try(unfold CBlockEntry;
                       destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                       simpl; reflexivity).
        apply partitionsArePDT; try(unfold consistency1 in *; intuition; congruence).
      }
      rewrite HgetChildrenEq in HchildIsChild.
      assert(HpdparentIsPDT: isPDT pdparent s).
      {
        unfold getMappedBlocks in HblockIsMapped. unfold getKSEntries in HblockIsMapped.
        unfold isPDT.
        destruct (lookup pdparent (memory s) beqAddr); try(simpl in HblockIsMapped; congruence).
        destruct v; try(simpl in HblockIsMapped; congruence).
        trivial.
      }
      assert(HnewB: exists l,
                    newBentry = {|
                                  read := read bentry;
                                  write := write bentry;
                                  exec := exec bentry;
                                  present := present bentry;
                                  accessible := flag;
                                  blockindex := blockindex bentry;
                                  blockrange := blockrange bentry;
                                  Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                                |}).
      {
        simpl in HlookupBlocks'. rewrite beqAddrTrue in HlookupBlocks'. unfold CBlockEntry in HlookupBlocks'.
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
        injection HlookupBlocks' as HbentriesEq. exists l. apply eq_sym. assumption.
      }
      destruct HnewB as [l HnewB].
      assert(HgetAccEq: forall partition, partition <> pdparent
                            -> isPDT partition s
                            -> getAccessibleMappedPaddr partition s' = getAccessibleMappedPaddr partition s).
      {
        intros partition HpartNotParent HpartIsPDT. subst s'. apply getAccessibleMappedPaddrEqBENotInPart.
        - assumption.
        - unfold isBE. rewrite HlookupBlock. trivial.
        - intro Hcontra. assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
          unfold DisjointKSEntries in Hdisjoint.
          specialize(Hdisjoint partition pdparent HpartIsPDT HpdparentIsPDT HpartNotParent).
          destruct Hdisjoint as [optionEntriesList1 (optionEntriesList2 & (Hlist1 & Hlist2 & Hdisjoint))].
          subst optionEntriesList1. subst optionEntriesList2. unfold Lib.disjoint in Hdisjoint.
          specialize(Hdisjoint blockInParentPartitionAddr Hcontra). unfold getMappedBlocks in HblockIsMapped.
          induction (filterOptionPaddr (getKSEntries pdparent s)); try( simpl in HblockIsMapped; congruence).
          simpl in HblockIsMapped. simpl in Hdisjoint. apply Decidable.not_or in Hdisjoint.
          destruct Hdisjoint as [HbeqABlock HdisjointRec]. apply IHl0; try(assumption).
          destruct (lookup a (memory s) beqAddr); try(assumption). destruct v; try(assumption).
          destruct (present b); try(assumption). simpl in HblockIsMapped.
          destruct HblockIsMapped as [HaIsBlock | Hgoal]; try(exfalso; congruence).
          assumption.
      }
      assert(HchildIsPDT: isPDT child s).
      { apply childrenArePDT with parent; try(unfold consistency1 in *; intuition; congruence). }
      assert(HgetMappedChild: getMappedPaddr child s' = getMappedPaddr child s).
      {
        subst s'. apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
              try(assumption); unfold CBlockEntry;
              destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia); simpl;
              reflexivity.
      }
      rewrite HgetMappedChild in HaddrIsMappedInChild.
      assert(HgetAccMappedParentEq: In addr (getAccessibleMappedPaddr pdparent s') ->
                In addr (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry))
                          ++ (getAccessibleMappedPaddr pdparent s))
                /\ (flag = accessible bentry -> In addr (getAccessibleMappedPaddr pdparent s))
                /\ (flag = false -> ~ In addr (getAllPaddrBlock (startAddr (blockrange bentry))
                                                                (endAddr (blockrange bentry))))).
      {
        intro HaddrIsMapped.
        assert(Heq: forall l flag,
              getAccessibleMappedPaddr pdparent
                 {|
                   currentPartition := currentPartition s;
                   memory :=
                     add blockInParentPartitionAddr
                       (BE
                          (CBlockEntry (read bentry) (write bentry) 
                             (exec bentry) (present bentry) flag (blockindex bentry)
                             (blockrange bentry))) (memory s) beqAddr
                 |} = getAccessibleMappedPaddr pdparent
                         {|
                           currentPartition := currentPartition s;
                           memory :=
                             add blockInParentPartitionAddr
                               (BE
                                  {|
                                    read := read bentry;
                                    write := write bentry;
                                    exec := exec bentry;
                                    present := present bentry;
                                    accessible := flag;
                                    blockindex := blockindex bentry;
                                    blockrange := blockrange bentry;
                                    Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                                  |}) (memory s) beqAddr
                         |}).
        {
          intros l0 flag'. unfold CBlockEntry.
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
          f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. apply proof_irrelevance.
        }
        destruct (eqb flag (accessible bentry)) eqn:HbeqFlagOldAcc.
        - (* flag = accessible bentry *)
          apply eqb_prop in HbeqFlagOldAcc. subst flag.
          assert(HgetAccMappedEq: getAccessibleMappedPaddr pdparent s' = getAccessibleMappedPaddr pdparent s).
          {
            subst s'. apply getAccessibleMappedPaddrEqBEPresentAccessibleNoChange with bentry;
                  try(assumption);
                  try(unfold CBlockEntry;
                      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                      simpl; reflexivity).
          }
          rewrite HgetAccMappedEq in HaddrIsMapped. split. apply in_or_app. right. assumption. split. intro.
          assumption. intros HaccessFalse Hcontra.
          assert(HaccessTrue: bentryAFlag blockInParentPartitionAddr true s).
          {
            apply addrInAccessibleMappedIsAccessible with pdparent addr; try(assumption).
            simpl. rewrite HlookupBlock. rewrite app_nil_r. assumption.
          }
          unfold bentryAFlag in HaccessTrue. rewrite HlookupBlock in HaccessTrue. congruence.
        - (* flag <> accessible bentry *)
          apply eqb_false_iff in HbeqFlagOldAcc. split. destruct flag.
          + (* flag = true *)
            subst s'. apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence
                          with blockInParentPartitionAddr newBentry;
                      try(subst newBentry; unfold CBlockEntry;
                        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                        simpl);
                    try(unfold consistency1 in *; intuition; congruence).
            { unfold bentryPFlag in HpresentBlock. rewrite HlookupBlock in HpresentBlock. intuition. }
            {
              unfold getMappedBlocks in HblockIsMapped. apply DTL.InFilterPresentInList in HblockIsMapped.
              assumption.
            }
          + (* flag = false *)
            apply in_or_app. right.
            apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleFalseChangeInclusion with
                    blockInParentPartitionAddr newBentry bentry;
                      try(subst newBentry; unfold CBlockEntry;
                        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                        simpl);
                  try(unfold consistency1 in *; intuition; congruence).
            { unfold bentryPFlag in HpresentBlock. rewrite HlookupBlock in HpresentBlock. intuition. }
            {
              unfold getMappedBlocks in HblockIsMapped. apply DTL.InFilterPresentInList in HblockIsMapped.
              assumption.
            }
            subst s'. rewrite Heq with l0 false in HaddrIsMapped. assumption.
          + split; try(intro; exfalso; congruence). intro HflagFalse. subst flag.
            intro Hcontra. rewrite <-HgetMappedEq in *.
            assert(HaccessTrue: bentryAFlag blockInParentPartitionAddr true s').
            {
              apply addrInAccessibleMappedIsAccessible with pdparent addr; try(assumption).
              {
                unfold noDupUsedPaddrList in *. intros part HpartIsPDT.
                destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart.
                {
                  rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst part.
                  unfold isPDT in HpartIsPDT. rewrite HlookupBlocks' in HpartIsPDT. exfalso; congruence.
                }
                assert(HpartIsPDTs: isPDT part s).
                {
                  unfold isPDT in *. subst s'. simpl in HpartIsPDT. rewrite HbeqBlockPart in HpartIsPDT.
                  rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
                }
                specialize(HnoDup part HpartIsPDTs).
                assert(HgetUsedEq: getUsedPaddr part s' = getUsedPaddr part s).
                {
                  unfold getUsedPaddr.
                  assert(Hconfig: getConfigPaddr part s' = getConfigPaddr part s).
                  {
                    subst s'. apply getConfigPaddrEqBE; try(assumption).
                    unfold isBE. rewrite HlookupBlock. trivial.
                  }
                  assert(Hmapped: getMappedPaddr part s' = getMappedPaddr part s).
                  {
                    subst s'.
                    apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
                          try(assumption);
                          unfold CBlockEntry;
                            destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
                            try(lia); simpl; reflexivity.
                  }
                  rewrite Hconfig. rewrite Hmapped. reflexivity.
                }
                rewrite HgetUsedEq. assumption.
              }
              simpl. rewrite beqAddrTrue. rewrite app_nil_r. unfold CBlockEntry.
              destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
              simpl. assumption.
            }
            unfold bentryAFlag in HaccessTrue. rewrite HlookupBlocks' in HaccessTrue.
            rewrite HnewB in HaccessTrue. simpl in HaccessTrue. congruence.
      }
      destruct (beqAddr parent pdparent) eqn:HbeqParentPdParent.
      - (* parent = pdparent *)
        rewrite <-DTL.beqAddrTrue in HbeqParentPdParent. subst parent.
        assert(HaddrIsMappedAccInParents: In addr 
                        (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry))
                        ++ getAccessibleMappedPaddr pdparent s)) by intuition.
        apply in_app_or in HaddrIsMappedAccInParents.
        assert(HchildNotPdparent: pdparent <> child).
        {
          unfold consistency1 in *; apply childparentNotEq with s; intuition.
        }
        apply not_eq_sym in HchildNotPdparent.
        rewrite HgetAccEq; try(assumption).
        specialize(HgetAccMappedParentEq HaddrIsMappedAccInParent).
        destruct HgetAccMappedParentEq as (HgetAccMappedParentEq & HgetAccMappedParentEqFlagEq &
                                            HnotEdgeCaseIfNotFlag).
        destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                  HAFlagBlockAddr & HblockAddrMappedBase & HstartBlockAddr & HpartialAccess))].
        destruct (beqAddr child pdbasepartition) eqn:HbeqChildBase.
        + (* child = pdbasepartition *)
          rewrite <-DTL.beqAddrTrue in HbeqChildBase. subst child. unfold bentryStartAddr in *.
          rewrite HlookupBlockAddr in HstartBlockAddr. rewrite HlookupBlock in Hblockstart.
          rewrite HstartBlockAddr in Hblockstart. specialize(HnoDup pdbasepartition HchildIsPDT).
          unfold getUsedPaddr in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
          destruct HnoDup as [(Hconf & HnoDupMapped) Hdis]. unfold getMappedPaddr in HnoDupMapped.
          destruct HaddrIsMappedAccInParents as [HedgeCase | HaddrAccMappedParents].
          * (* addr is in the block, so flag = true *)
            destruct flag; try(intuition; exfalso; congruence). admit.
            (*TODO - property missing on the fact that the block is not cut*)
          * (* addr is not in the block, we can use the induction property *)
            admit.
        + (* child <> pdbasepartition *)
          rewrite <-beqAddrFalse in HbeqChildBase. destruct HpartialAccess as [Hss0Eq | HpartialAccess].
          * (* s = s0 *)
            subst s. destruct HaddrIsMappedAccInParents as [HedgeCase | HaddrAccMappedParents].
            {
              admit. (*still depends on blockaddr's properties*)
            }
            {
              specialize(Haccess pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParents
                      HaddrIsMappedInChild). assumption.
            }
          * (* s <> s0 *)
            destruct HaddrIsMappedAccInParents as [HedgeCase | HaddrAccMappedParents].
            {
              admit. (*still depends on blockaddr's properties*)
            }
            { apply HpartialAccess with pdparent; intuition. }
      - (* parent <> pdparent *)
        assert(HchildNotBase: child <> pdbasepartition).
        {
          rewrite <-beqAddrFalse in HbeqParentPdParent.
          intro Hcontra. subst child.
          assert(HpdparentParentEq: parent = pdparent).
          {
            (*assert(HparentIsPart: In parent (getPartitions multiplexer s)).
            {}

            assert(HisParents: isParent s) by (unfold consistency1 in *; intuition).
            specialize(HisParents pdbasepartition ).

            apply uniqueParent with pdbasepartition s; try(unfold consistency1 in *; intuition; congruence).
            {}
            { apply childrenPartitionInPartitionList; try(unfold consistency1 in *; intuition; congruence). }*)
            admit. (*TODO probably needs a consistency prop. Again.*)
          }
          congruence.
        }
        assert(HparentIsPDT: isPDT parent s).
        {
          unfold consistency1 in *; apply partitionsArePDT; intuition.
        }
        destruct (beqAddr child pdparent) eqn:HbeqChildPdParent.
        + (* child = pdparent *)
          rewrite <-DTL.beqAddrTrue in HbeqChildPdParent. subst child.
          assert(HaddrInAccMappedIf: In addr (getAllPaddrBlock (startAddr (blockrange bentry))
                                      (endAddr (blockrange bentry)) ++ getAccessibleMappedPaddr pdparent s)
                                    -> In addr (getAccessibleMappedPaddr pdparent s')).
          {
            intro Haddr. apply in_app_or in Haddr.
            assert(Heq: forall l flag,
                  getAccessibleMappedPaddr pdparent
                     {|
                       currentPartition := currentPartition s;
                       memory :=
                         add blockInParentPartitionAddr
                           (BE
                              (CBlockEntry (read bentry) (write bentry) 
                                 (exec bentry) (present bentry) flag (blockindex bentry)
                                 (blockrange bentry))) (memory s) beqAddr
                     |} = getAccessibleMappedPaddr pdparent
                             {|
                               currentPartition := currentPartition s;
                               memory :=
                                 add blockInParentPartitionAddr
                                   (BE
                                      {|
                                        read := read bentry;
                                        write := write bentry;
                                        exec := exec bentry;
                                        present := present bentry;
                                        accessible := flag;
                                        blockindex := blockindex bentry;
                                        blockrange := blockrange bentry;
                                        Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                                      |}) (memory s) beqAddr
                             |}).
            {
              intros l0 flag'. unfold CBlockEntry.
              destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
              f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. apply proof_irrelevance.
            }
            destruct Haddr as [HaddrInBentry | HaddrInAccMappeds].
            { (* addr is in the mofified entry *)
              rewrite app_nil_r in HnotEdgeCase. destruct HnotEdgeCase as [Hfalse | Hcontra].
              exfalso; congruence.
              contradict Hcontra. rewrite HnewB; simpl; assumption.
            }
            (* addr is not in the mofified entry *)
            destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                      HAFlagBlockAddr & HblockAddrMappedBase & HstartBlockAddr & HpartialAccess))].
            destruct (eqb flag (accessible bentry)) eqn:HbeqFlagOldAcc.
            - (* flag = accessible bentry *)
              apply eqb_prop in HbeqFlagOldAcc. subst flag.
              assert(HgetAccMappedEq: getAccessibleMappedPaddr pdparent s'
                                      = getAccessibleMappedPaddr pdparent s).
              {
                subst s'. apply getAccessibleMappedPaddrEqBEPresentAccessibleNoChange with bentry;
                      try(assumption);
                      try(unfold CBlockEntry;
                          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                          simpl; reflexivity).
              }
              rewrite HgetAccMappedEq. assumption.
            - (* flag <> accessible bentry *)
              apply eqb_false_iff in HbeqFlagOldAcc. destruct flag.
              + (* flag = true *)
                subst s'. apply <-getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence;
                          try(subst newBentry; unfold CBlockEntry;
                            destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                            simpl);
                        try(unfold consistency1 in *; intuition; congruence).
                {
                  unfold getMappedBlocks in HblockIsMapped. apply DTL.InFilterPresentInList in HblockIsMapped.
                  assumption.
                }
                { unfold bentryPFlag in HpresentBlock. rewrite HlookupBlock in HpresentBlock. intuition. }
              + (* flag = false *)
                assert(HaddrAccMappedOrInBlock:
                        In addr (getAccessibleMappedPaddr pdparent s')
                        \/ In addr (getAllPaddrBlock (startAddr (blockrange newBentry))
                                                     (endAddr (blockrange newBentry)))).
                {
                  subst s'.
                  apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleFalseChangeInclusionRev with
                          bentry;
                            try(rewrite HnewB; simpl);
                        try(unfold consistency1 in *; intuition; congruence).
                  unfold bentryPFlag in HpresentBlock. rewrite HlookupBlock in HpresentBlock. intuition.
                  unfold getMappedBlocks in HblockIsMapped. apply InFilterPresentInList with s. assumption.
                }
                destruct HaddrAccMappedOrInBlock as [HaddrAccMapped | Hcontra].
                assumption.
                destruct HnotEdgeCase as [Hfalse | HaddrNotInBlock]; try(rewrite app_nil_r in HaddrNotInBlock);
                    exfalso; congruence.
          }
          apply HaddrInAccMappedIf. apply in_or_app. right. rewrite <-beqAddrFalse in HbeqParentPdParent.
          specialize(HgetAccEq parent HbeqParentPdParent HparentIsPDT).
          rewrite HgetAccEq in HaddrIsMappedAccInParent.
          destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                      HAFlagBlockAddr & HblockAddrMappedBase & HstartBlockAddr & HpartialAccess))].
          destruct HpartialAccess as [Hss0Eq | HpartialAccess].
          { (* s = s0 *)
            subst s. specialize(Haccess parent pdparent addr HparentIsPart HchildIsChild HaddrIsMappedAccInParent
                  HaddrIsMappedInChild). assumption.
          }
          (* s <> s0 *)
          rewrite HlookupBlockAddr in HpartialAccess.
          assert(HnotPrevEdgeCase: pdparent <> pdbasepartition
                                   \/ ~ In addr (getAllPaddrBlock (startAddr (blockrange bentryBlockAddr))
                                                                  (endAddr (blockrange bentryBlockAddr)) ++ [])).
          { left. assumption. }
          specialize(HpartialAccess parent pdparent addr HnotPrevEdgeCase HparentIsPart HchildIsChild
                  HaddrIsMappedAccInParent HaddrIsMappedInChild). assumption.
        + (* child <> pdparent *)
          rewrite <-beqAddrFalse in *.
          assert(HgetAccParentEq: getAccessibleMappedPaddr parent s' = getAccessibleMappedPaddr parent s).
          { apply HgetAccEq; intuition. }
          assert(HgetAccChildEq: getAccessibleMappedPaddr child s' = getAccessibleMappedPaddr child s).
          { apply HgetAccEq; intuition. }
          rewrite HgetAccParentEq in HaddrIsMappedAccInParent. rewrite HgetAccChildEq.
          destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                      HAFlagBlockAddr & HblockAddrMappedBase & HstartBlockAddr & HpartialAccess))].
          destruct HpartialAccess as [Hss0Eq | HpartialAccess].
          { (* s = s0 *)
            subst s. specialize(Haccess parent child addr HparentIsPart HchildIsChild HaddrIsMappedAccInParent
                  HaddrIsMappedInChild). assumption.
          }
          (* s <> s0 *)
          rewrite HlookupBlockAddr in HpartialAccess.
          assert(HnotPrevEdgeCase: child <> pdbasepartition
                                   \/ ~ In addr (getAllPaddrBlock (startAddr (blockrange bentryBlockAddr))
                                                                  (endAddr (blockrange bentryBlockAddr)) ++ [])).
          { left. assumption. }
          specialize(HpartialAccess parent child addr HnotPrevEdgeCase HparentIsPart HchildIsChild
                  HaddrIsMappedAccInParent HaddrIsMappedInChild). assumption.
    }
    intro a. simpl. eapply bindRev.
    { (** MAL.removeBlockFromPhysicalMPUIfNotAccessible and MAL.removeBlockFromPhysicalMPU **)
      unfold MAL.removeBlockFromPhysicalMPUIfNotAccessible.
      destruct (negb flag) eqn:HflagFalse.
      - apply Bool.negb_true_iff in HflagFalse. rewrite HflagFalse in *.
        eapply bindRev.
        {
          eapply weaken. apply removeBlockFromPhysicalMPU.
          intros s Hprops. simpl. split. apply Hprops.
          destruct Hprops as [sInit (s0 & (pdentry & (bentry & (newBentry & (Hs & (Hparent & (HlookupBlocks0 &
                                (HlookupBlocks & (HPFlag &
                                  (HAFlag & (HblockInMappedBlocks & (HstartAddr & (HnewB & (HlookupBases0 &
                                   (HlookupBases & (Hconsists0 & HnoDup &
                                     Hshared & HpartialAccess & HPinit & HconsistInit &
                                      Haccess))))))))))))))))].
          assert(HparentIsPart: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
          unfold parentOfPartitionIsPartition in HparentIsPart.
          rewrite <-beqAddrFalse in HbeqBaseRoot.
          specialize(HparentIsPart pdbasepartition pdentry HlookupBases0).
          destruct HparentIsPart as [HparentIsPart HparentOfRoot].
          specialize(HparentIsPart HbeqBaseRoot).
          destruct HparentIsPart as [parentEntry HlookupParent].
          unfold isPDT. rewrite Hs. simpl.
          destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *.
            rewrite <- Hparent in HlookupParent. rewrite HlookupParent in *. congruence.
          }
          rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
          subst pdparent. rewrite HlookupParent. trivial.
        }
        intro. eapply weaken. apply WP.ret. intros s Hprops.
        instantiate(1:= fun _ s =>
          exists (sInit s0 s1: state) (realMPU : list paddr) (pdentryParent pdentryBase: PDTable)
                  (bentry newBentry: BlockEntry),
            s1 =
                {|
                  currentPartition := currentPartition s0;
                  memory :=
                    add blockInParentPartitionAddr
                      (BE
                         (CBlockEntry (read bentry) (write bentry) (exec bentry)
                            (present bentry) flag (blockindex bentry) (blockrange bentry)))
                      (memory s0) beqAddr
                |}
            /\ newBentry =
                         CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                           (blockindex bentry) (blockrange bentry)
            /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase)
            /\ lookup pdbasepartition (memory s1) beqAddr = Some (PDT pdentryBase)
            /\ lookup pdparent (memory s1) beqAddr = Some (PDT pdentryParent)
            /\ bentryAFlag blockInParentPartitionAddr flag s1
            /\ bentryPFlag blockInParentPartitionAddr true s1
            /\ In blockInParentPartitionAddr (getMappedBlocks pdparent s1)
            /\ bentryStartAddr blockInParentPartitionAddr entryaddr s1
            /\ lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
            /\ lookup blockInParentPartitionAddr (memory s1) beqAddr = Some (BE newBentry)
            /\ P sInit
            /\ consistency1 s0
            /\ pdentryMPU pdparent realMPU s1
            /\ pdparent = parent pdentryBase
            /\ noDupUsedPaddrList s0
            /\ sharedBlockPointsToChild s0
            /\ P sInit
            /\ consistency sInit
            /\ (exists (blockaddr : paddr) (bentry0 : BlockEntry),
                       lookup blockaddr (memory s1) beqAddr = Some (BE bentry0) /\
                       bentryPFlag blockaddr true s1 /\
                       bentryAFlag blockaddr flag s1 /\
                       In blockaddr (getMappedBlocks pdparent s1) /\
                       bentryStartAddr blockaddr entryaddr s1 /\
                       (forall parent child addr : paddr,
                          child <> pdparent
                          \/ ~In addr (getAllPaddrBlock (startAddr (blockrange bentry0))
                                                        (endAddr (blockrange bentry0)))
                          -> In parent (getPartitions multiplexer s1)
                          -> In child (getChildren parent s1)
                          -> In addr (getAccessibleMappedPaddr parent s1)
                          -> In addr (getMappedPaddr child s1)
                          -> In addr (getAccessibleMappedPaddr child s1)))
              /\ (s = s1 \/
                    s =
                     {|
                       currentPartition := currentPartition s1;
                       memory :=
                         add pdparent
                           (PDT
                              {|
                                structure := structure pdentryParent;
                                firstfreeslot := firstfreeslot pdentryParent;
                                nbfreeslots := nbfreeslots pdentryParent;
                                nbprepare := nbprepare pdentryParent;
                                parent := parent pdentryParent;
                                MPU :=
                                  MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                                vidtAddr := vidtAddr pdentryParent
                              |}) (memory s1) beqAddr
                     |})). (*?*)
        simpl. destruct Hprops as [s1 (pdentryParent & (realMPU & (HpdentryMPU & (Hprops &
                                      (HlookupParent & Hs)))))].
        destruct Hprops as [sInit (s0 & (pdentryBase & (bentry & (newBentry & (Hs1 & (Hparent & (HlookupBlocks0
                              & (HlookupBlocks1 & (HPFlag &
                               (HAFlag & (HblockInMappedBlocks1 & (HstartAddr & (HnewB &
                                 (HlookupBases0 & (HlookupBases1 & (Hconsists0 & HnoDup &
                                  Hshared & HpartialAccess & HPinit & HconsistInit &
                                   Haccess))))))))))))))))].
        exists sInit. exists s0. exists s1. exists realMPU. exists pdentryParent.
        exists pdentryBase. exists bentry. exists newBentry. intuition.
        destruct HpartialAccess as [blockaddr (bentryAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                                    HAFlagBlockAddr & HblockAddrMappedParent & HstartBlockAddr &
                                    HpartialAccess))].
        exists blockaddr. exists bentryAddr. rewrite HlookupBlockAddr in HpartialAccess.
        rewrite app_nil_r in HpartialAccess. intuition.
      - eapply weaken. apply WP.ret. intros s Hprops. simpl.
        destruct Hprops as [sInit (s0 & (pdentryBase & (bentry & (newBentry & (Hs1 & (Hparent & (HlookupBlocks0
                              & (HlookupBlocks1 & (HPFlag &
                                (HAFlag & (HblockInMappedBlocks1 & (HstartAddr & (HnewB &
                                  (HlookupBases0 & (HlookupBases1 &
                                   (Hconsists0 & HnoDup & Hshared & HpartialAccess & HPinit &
                                    HconsistInit & Haccess))))))))))))))))].
        assert(HparentIsPart: parentOfPartitionIsPartition s0) by (unfold consistency1 in Hconsists0; intuition).
        specialize(HparentIsPart pdbasepartition pdentryBase HlookupBases0).
        destruct HparentIsPart as [HparentOfPart (HparentOfRoot & HparentPartNotEq)].
        rewrite <-beqAddrFalse in HbeqBaseRoot. specialize(HparentOfPart HbeqBaseRoot).
        destruct HparentOfPart as [parentEntry HlookupPdparent]. rewrite <-Hparent in *.
        destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
          rewrite HlookupPdparent in HlookupBlocks0. exfalso; congruence.
        }
        assert(HlookupPdparents: lookup pdparent (memory s) beqAddr = Some (PDT parentEntry)).
        {
          rewrite Hs1. simpl. rewrite HbeqBlockParent. rewrite <-beqAddrFalse in HbeqBlockParent.
          rewrite removeDupIdentity; intuition.
        }
        exists sInit. exists s0. exists s. exists (MPU parentEntry). exists parentEntry.
        exists pdentryBase. exists bentry. exists newBentry.
        apply Bool.negb_false_iff in HflagFalse. rewrite HflagFalse in *. intuition.
        unfold pdentryMPU. rewrite HlookupPdparents. reflexivity.
        destruct HpartialAccess as [blockaddr (bentryAddr & (HlookupBlockAddr & HPFlagBlockAddr & HAFlagBlockAddr
                                    & HblockAddrMappedParent & HstartBlockAddr & HpartialAccess))].
        exists blockaddr. exists bentryAddr. rewrite HlookupBlockAddr in HpartialAccess.
        rewrite app_nil_r in HpartialAccess. intuition.
    }
    intro. simpl. eapply strengthen. eapply weaken. apply IHtimeout.
    -- intros s Hprops. simpl.
       destruct Hprops as [sInit (s0 & (s1 & realMPU & pdentryParent & pdentryBase & (bentry &
                            (newBentry & (Hs1 & HnewB &
                              HlookupBases0 & HlookupBases1 & HlookupParent & HAFlag & HPFlag &
                               HblockInMappedBlocks & HstartAddr & HlookupBlocks0 & HlookupBlocks1 & HPsInit &
                                Hconsists0 & HMPU & HparentEq & HnoDup & Hshared & HPsInitCopy &
                                 HconsistInit & HpartialAccess & HpropsOr)))))].
       destruct (beqAddr blockInParentPartitionAddr nullAddr) eqn:HbeqBlockNull.
       {
         assert(HnullExists: nullAddrExists s0) by (unfold consistency1 in Hconsists0; intuition).
         unfold nullAddrExists in HnullExists. unfold isPADDR in HnullExists.
         rewrite <-DTL.beqAddrTrue in HbeqBlockNull. rewrite HbeqBlockNull in *.
         destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
         destruct v; try(exfalso; congruence).
       }
       assert(HblockInMappedBlocksEqs1: getMappedBlocks pdparent s1 = getMappedBlocks pdparent s0).
       {
         rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. intuition. unfold CBlockEntry.
         assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
         destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
         reflexivity.
       }
       assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
       assert(HnewBentry: exists l, newBentry =
                      {|
                        read := read bentry;
                        write := write bentry;
                        exec := exec bentry;
                        present := present bentry;
                        accessible := flag;
                        blockindex := blockindex bentry;
                        blockrange := blockrange bentry;
                        Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                      |}).
       {
         rewrite HnewB. unfold CBlockEntry.
         destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
         exists l. reflexivity.
       }
       destruct HnewBentry as [lbentry HnewBentry].
       assert(HblockIsNotFree: ~isFreeSlot blockInParentPartitionAddr s0).
       {
         unfold isFreeSlot. rewrite HlookupBlocks0.
         assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
               by (unfold consistency in *; unfold consistency1 in *; intuition).
         unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
         assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
         { unfold isBE. rewrite HlookupBlocks0. trivial. }
         specialize(HwellFormeds0 blockInParentPartitionAddr HblockIsBE).
         unfold isSHE in HwellFormeds0.
         destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr);
               try(exfalso; congruence).
         destruct v; try(exfalso; congruence).
         assert(HwellFormedCuts0: wellFormedShadowCutIfBlockEntry s0)
               by (unfold consistency in *; unfold consistency1 in *; intuition).
         unfold wellFormedShadowCutIfBlockEntry in HwellFormedCuts0.
         specialize(HwellFormedCuts0 blockInParentPartitionAddr HblockIsBE).
         destruct HwellFormedCuts0 as [scentryaddr (HwellFormedCuts0 & HsceValue)].
         subst scentryaddr. unfold isSCE in HwellFormedCuts0.
         destruct (lookup (CPaddr (blockInParentPartitionAddr + scoffset)) (memory s0) beqAddr);
               try(exfalso; congruence).
         destruct v; try(exfalso; congruence).
         unfold bentryPFlag in HPFlag. rewrite HlookupBlocks1 in HPFlag.
         rewrite HnewBentry in HPFlag. simpl in HPFlag. rewrite <-HPFlag. intuition.
       }
       assert(HgetFreeSlotsListEq: forall pd, isPDT pd s0
                                             -> lookup pd (memory s1) beqAddr = lookup pd (memory s0) beqAddr
                                               -> getFreeSlotsList pd s1 = getFreeSlotsList pd s0).
       {
         intros pd HisPDT HlookupPdEq. unfold isPDT in HisPDT. unfold getFreeSlotsList in *.
         rewrite HlookupPdEq in *.
         destruct (lookup pd (memory s0) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
         destruct v; try(exfalso; congruence).
         destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull.
         + (* firstfreeslot p = nullAddr *)
           reflexivity.
         + (* firstfreeslot p <> nullAddr *)
           assert(HbeqFirstFreeBlock: firstfreeslot p <> blockInParentPartitionAddr).
           {
             assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold FirstFreeSlotPointerIsBEAndFreeSlot in HfirstFree.
             rewrite <-beqAddrFalse in HbeqFirstFreeNull.
             specialize(HfirstFree pd p HlookupPd HbeqFirstFreeNull).
             destruct HfirstFree as [HfirstIsBE HfirstIsFree].
             intro Hcontra. rewrite Hcontra in HfirstIsFree. congruence.
           }
           assert(HnoDups0: NoDupInFreeSlotsList s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NoDupInFreeSlotsList in HnoDups0.
           specialize(HnoDups0 pd p HlookupPd).
           destruct HnoDups0 as [optionFreeSlotsList (HoptionList & (HwellFormedList & HnoDupList))].
           unfold getFreeSlotsList in HoptionList. rewrite HlookupPd in HoptionList.
           rewrite HbeqFirstFreeNull in HoptionList. subst optionFreeSlotsList.
           rewrite Hs1. apply getFreeSlotsListRecEqBE; try(intuition; congruence).
           * unfold isBE. rewrite HlookupBlocks0. trivial.
           * intro Hcontra.
             set(optionFreeSlotsList:= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
             assert(HisInGetFree: optionFreeSlotsList = getFreeSlotsList pd s0
                                   /\ wellFormedFreeSlotsList optionFreeSlotsList <> False).
             {
               split.
               - unfold getFreeSlotsList. rewrite HlookupPd. rewrite HbeqFirstFreeNull. intuition.
               - intuition.
             }
             assert(HfreeSlotsAreFree: freeSlotsListIsFreeSlot s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold freeSlotsListIsFreeSlot in HfreeSlotsAreFree.
             assert(HisPDTCopy: isPDT pd s0) by (unfold isPDT; rewrite HlookupPd; trivial).
             assert(HinList: filterOptionPaddr optionFreeSlotsList = filterOptionPaddr optionFreeSlotsList
                     /\ In blockInParentPartitionAddr (filterOptionPaddr optionFreeSlotsList)).
             { intuition. }
             rewrite <-beqAddrFalse in HbeqBlockNull.
             specialize(HfreeSlotsAreFree pd blockInParentPartitionAddr optionFreeSlotsList
                       (filterOptionPaddr optionFreeSlotsList) HisPDTCopy HisInGetFree HinList HbeqBlockNull).
             congruence.
       }

       assert(Hconss1: consistency1 s1).
       {
         assert(HnullExists: nullAddrExists s1).
         { (* BEGIN nullAddrExists s1 *)
           assert(Hcons0: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold nullAddrExists in *. unfold isPADDR in *.
           rewrite Hs1. simpl. rewrite HbeqBlockNull.
           rewrite <-beqAddrFalse in HbeqBlockNull. rewrite removeDupIdentity; intuition.
           (* END nullAddrExists *)
         }

         assert(HwellFormed: wellFormedFstShadowIfBlockEntry s1).
         { (* BEGIN wellFormedFstShadowIfBlockEntry s1 *)
           assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold wellFormedFstShadowIfBlockEntry in *. intros pa HBE.
           assert(HBEs0: isBE pa s0).
           {
             rewrite Hs1 in HBE. unfold isBE in *. simpl in HBE.
             destruct (beqAddr blockInParentPartitionAddr pa) eqn:HbeqBlockPa.
             - rewrite <-DTL.beqAddrTrue in HbeqBlockPa. rewrite HbeqBlockPa in *. rewrite HlookupBlocks0.
               trivial.
             - rewrite <-beqAddrFalse in HbeqBlockPa. rewrite removeDupIdentity in HBE; intuition.
           }
           specialize(Hcons0 pa HBEs0). unfold isSHE in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (pa + sh1offset))) eqn:HbeqBlockPaSh1.
           {
             rewrite <-DTL.beqAddrTrue in HbeqBlockPaSh1. rewrite HbeqBlockPaSh1 in *.
             destruct (lookup (CPaddr (pa + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence).
           }
           rewrite <-beqAddrFalse in HbeqBlockPaSh1. rewrite removeDupIdentity; intuition.
           (* END wellFormedFstShadowIfBlockEntry*)
         }

         assert(Haccessible: AccessibleNoPDFlag s1).
         { (* BEGIN AccessibleNoPDFlag s1 *)
           assert(Hcons0: AccessibleNoPDFlag s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold AccessibleNoPDFlag in *. intros block sh1entryaddr HBEblock Hsh1entry Haccessible.
           assert(HBEblockEq: isBE block s1 = isBE block s0).
           {
             rewrite Hs1. unfold isBE. simpl.
              destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockParentBlock.
             - (* blockInParentPartitionAddr = block *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlock. rewrite HbeqBlockParentBlock in *.
               rewrite HlookupBlocks0. reflexivity.
             - (* blockInParentPartitionAddr <> block *)
               rewrite <-beqAddrFalse in HbeqBlockParentBlock. rewrite removeDupIdentity; intuition.
           }
           assert(Hsh1entryEq: sh1entryAddr block sh1entryaddr s1 = sh1entryAddr block sh1entryaddr s0).
           {
             rewrite Hs1. unfold sh1entryAddr. simpl.
             destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockParentBlock.
             - (* blockInParentPartitionAddr = block *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlock. rewrite HbeqBlockParentBlock in *.
               rewrite HlookupBlocks0. reflexivity.
             - (* blockInParentPartitionAddr <> block *)
               rewrite <-beqAddrFalse in HbeqBlockParentBlock. rewrite removeDupIdentity; intuition.
           }
           assert(HSH1: isSHE sh1entryaddr s1).
           {
             unfold wellFormedFstShadowIfBlockEntry in HwellFormed. specialize(HwellFormed block HBEblock).
             unfold sh1entryAddr in Hsh1entry.
             unfold isBE in HBEblock. destruct (lookup block (memory s1) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence).
             rewrite Hsh1entry in *. assumption.
           }
           assert(HlookupSh1Eq: lookup sh1entryaddr (memory s1) beqAddr
                                = lookup sh1entryaddr (memory s0) beqAddr).
           {
             rewrite Hs1. simpl. unfold sh1entryAddr in Hsh1entry.
             unfold isBE in HBEblock. destruct (lookup block (memory s1) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence).
             destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockParentSh1.
             - (* blockInParentPartitionAddr = sh1entryaddr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockParentSh1. rewrite HbeqBlockParentSh1 in *.
               unfold isSHE in HSH1. rewrite HlookupBlocks1 in HSH1. exfalso; congruence.
             - (* blockInParentPartitionAddr <> sh1entryaddr *)
               rewrite <-beqAddrFalse in HbeqBlockParentSh1. rewrite removeDupIdentity; intuition.
           }
           rewrite HBEblockEq in *. rewrite Hsh1entryEq in *.
           destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
           ++ (* blockInParentPartitionAddr = block *)
              rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block. admit.
              (*TODO: if accessible bentry = true, it's ok, but otherwise how do we know that the PDFlag isn't
                set?*)
              (*probably because the modified entries all belong to ancestors, so the block is shared, and I
                guess this results in the blocks necessarily not having the flag set - ask Damien*)
              (*probably linked to the new consistency prop on PDchild*)
           ++ (* blockInParentPartitionAddr <> block *)
              assert(HaccessibleEq: bentryAFlag block true s1 = bentryAFlag block true s0).
              {
                rewrite Hs1. unfold bentryAFlag. simpl. rewrite HbeqBlockBlock.
                - (* blockInParentPartitionAddr = block *)
                  rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
              }
              rewrite HaccessibleEq in Haccessible.
              specialize(Hcons0 block sh1entryaddr HBEblock Hsh1entry Haccessible).
              unfold sh1entryPDflag in *. rewrite Hs1. simpl. unfold isSHE in HSH1. rewrite Hs1 in HSH1.
              simpl in HSH1.
              destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1; try(congruence).
              rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition.
           (* END AccessibleNoPDFlag *)
         }

         assert(HPDTI: PDTIfPDFlag s1).
         { (* BEGIN PDTIfPDFlag s1 *)
           assert(Hcons0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold PDTIfPDFlag in *. intros idPDchild sh1entryaddr Hprops.
           destruct (beqAddr blockInParentPartitionAddr idPDchild) eqn:HbeqBlockIdPD.
           - (* blockInParentPartitionAddr = idPDchild *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockIdPD. rewrite HbeqBlockIdPD in *.
             (*unfold bentryStartAddr in HstartAddr. rewrite HlookupBlocks0 in HstartAddr.
             specialize(Hcons0 idPDchild sh1entryaddr Hpropss0).*)
             unfold checkChild in Hprops. destruct Hprops as [HPDflag Hsh1Eq].
             assert(Hsh1EqCopy: sh1entryAddr idPDchild sh1entryaddr s1) by assumption.
             unfold sh1entryAddr in Hsh1Eq. rewrite HlookupBlocks1 in *.
             assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
             assert(HBEidPDs0: isBE idPDchild s0).
             { unfold isBE. rewrite HlookupBlocks0. trivial. }
             specialize(HwellFormeds0 idPDchild HBEidPDs0). subst sh1entryaddr. unfold isSHE in HwellFormeds0.
             assert(HlookupSh1Eq: lookup (CPaddr (idPDchild + sh1offset)) (memory s1) beqAddr
                                  = lookup (CPaddr (idPDchild + sh1offset)) (memory s0) beqAddr).
             {
               rewrite Hs1. simpl.
               destruct (beqAddr idPDchild (CPaddr (idPDchild + sh1offset))) eqn:HbeqIdIdSh1.
               + (* idPDchild = CPaddr (idPDchild + sh1offset)) *)
                 rewrite <-DTL.beqAddrTrue in HbeqIdIdSh1. rewrite <-HbeqIdIdSh1 in *.
                 destruct (lookup idPDchild (memory s0) beqAddr); try(exfalso; congruence).
                 destruct v; try(exfalso; congruence).
               + (* idPDchild <> CPaddr (idPDchild + sh1offset)) *)
                 rewrite <-beqAddrFalse in HbeqIdIdSh1. rewrite removeDupIdentity; intuition.
             }
             rewrite <-HlookupSh1Eq in HwellFormeds0.
             destruct (lookup (CPaddr (idPDchild + sh1offset)) (memory s1) beqAddr) eqn:HlookupSh1;
                      try(exfalso; congruence).
             destruct v; try(exfalso; congruence).
             (*unfold AccessibleNoPDFlag in Haccessible.
             assert(HBEidPD: isBE idPDchild s1).
             { unfold isBE. rewrite HlookupBlocks1. trivial. }*)
             admit. (*TODO must be a congruence - the PDflag probably cannot be set for some reason
                - the same as for AccessibleNoPDFlag*)
           - (* blockInParentPartitionAddr <> idPDchild *)
             assert(Hpropss0: true = checkChild idPDchild s0 sh1entryaddr
                                    /\ sh1entryAddr idPDchild sh1entryaddr s0).
             {
               (*destruct Hprops as [Hcheck HPDT]. split.*)
               rewrite Hs1 in Hprops. unfold checkChild in *. unfold sh1entryAddr in *. simpl in Hprops.
               rewrite HbeqBlockIdPD in *. rewrite <-beqAddrFalse in *.
               rewrite removeDupIdentity in Hprops; try(intuition; congruence).
               destruct Hprops as [Hcheck Hsh1]. split; try(intuition; congruence).
               destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1.
               {
                 destruct (lookup idPDchild (memory s0) beqAddr) eqn:HlookupIdPD; try(exfalso; congruence).
                 destruct v; try(exfalso; congruence).
               }
               destruct (lookup idPDchild (memory s0) beqAddr) eqn:HlookupIdPD; try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hcheck; try(intuition; congruence).
             }
             specialize(Hcons0 idPDchild sh1entryaddr Hpropss0).
             destruct Hcons0 as [HbentryA (HbentryP & Hstart)].
             assert(HlookupChildEq: lookup idPDchild (memory s1) beqAddr
                                    = lookup idPDchild (memory s0) beqAddr).
             {
               rewrite Hs1. simpl. rewrite HbeqBlockIdPD. rewrite <-beqAddrFalse in HbeqBlockIdPD.
               rewrite removeDupIdentity; intuition.
             }
             unfold bentryAFlag in *. unfold bentryPFlag in *. unfold bentryStartAddr  in *.
             unfold entryPDT in *. rewrite HlookupChildEq. split. intuition. split. intuition.
             destruct Hstart as [startaddr Hstart]. exists startaddr. split. intuition.
             destruct (lookup idPDchild (memory s0) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence). rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr (startAddr (blockrange b))) eqn:HbeqBlockStart.
             + (* blockInParentPartitionAddr = startAddr (blockrange b) *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite HbeqBlockStart in *.
               destruct (lookup (startAddr (blockrange b)) (memory s0) beqAddr);
                   try(exfalso; intuition; congruence).
               destruct v; try(exfalso; intuition; congruence).
             + (* blockInParentPartitionAddr <> startAddr (blockrange b) *)
               rewrite <-beqAddrFalse in HbeqBlockStart. rewrite removeDupIdentity; intuition.
           (* END PDTIfPDFlag *)
         }

         assert(HfirstFreeSlotIsBEFree: FirstFreeSlotPointerIsBEAndFreeSlot s1).
         { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s1 *)
           assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
           intros pdentryaddr pdentry HlookupPdentryAddr HfirstFreeNotNull.
           assert(HlookupPdEq: lookup pdentryaddr (memory s1) beqAddr
                                = lookup pdentryaddr (memory s0) beqAddr).
           {
             rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr pdentryaddr) eqn:HbeqBlockPdentry.
             - (* blockInParentPartitionAddr = pdentryaddr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPdentry. rewrite HbeqBlockPdentry in *.
               rewrite HlookupPdentryAddr in *. exfalso; congruence.
             - (* blockInParentPartitionAddr <> pdentryaddr *)
               rewrite <-beqAddrFalse in HbeqBlockPdentry. rewrite removeDupIdentity; intuition.
           }
           rewrite HlookupPdEq in *.
           specialize(Hcons0 pdentryaddr pdentry HlookupPdentryAddr HfirstFreeNotNull).
           assert(HBEfirsts: isBE (firstfreeslot pdentry) s1).
           {
             unfold isBE in *. rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr (firstfreeslot pdentry)) eqn:HbeqBlockFirstFree.
             - (* blockInParentPartitionAddr = firstfreeslot pdentry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockFirstFree. rewrite HbeqBlockFirstFree in *. trivial.
             - (* blockInParentPartitionAddr <> firstfreeslot pdentry *)
               rewrite <-beqAddrFalse in HbeqBlockFirstFree. rewrite removeDupIdentity; intuition.
           }
           split. assumption. destruct Hcons0 as [HBE Hfree]. unfold isFreeSlot in *. rewrite Hs1. simpl.
           assert(HSHE: isSHE (CPaddr (firstfreeslot pdentry + sh1offset)) s0).
           {
             assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
             specialize(HwellFormeds0 (firstfreeslot pdentry) HBE). assumption.
           }
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (firstfreeslot pdentry + sh1offset)))
                      eqn:HbeqFirstFreeFirstPlusSh1.
           { (* firstfreeslot pdentry = CPaddr (firstfreeslot pdentry + sh1offset) *)
             rewrite <-DTL.beqAddrTrue in HbeqFirstFreeFirstPlusSh1.
             rewrite <-HbeqFirstFreeFirstPlusSh1 in *. unfold isSHE in HSHE. rewrite HlookupBlocks0 in HSHE.
             exfalso; congruence.
           }
           (* firstfreeslot pdentry <> CPaddr (firstfreeslot pdentry + sh1offset) *)
           assert(HSCE: isSCE (CPaddr (firstfreeslot pdentry + scoffset)) s0).
           {
             assert(HwellFormedCuts0: wellFormedShadowCutIfBlockEntry s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold wellFormedShadowCutIfBlockEntry in HwellFormedCuts0.
             specialize(HwellFormedCuts0 (firstfreeslot pdentry) HBE).
             destruct HwellFormedCuts0 as [scentryaddr (HSCE & Hvalue)]. subst scentryaddr. assumption.
           }
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (firstfreeslot pdentry + scoffset)))
                      eqn:HbeqFirstFreeFirstPlusSco.
           { (* firstfreeslot pdentry = CPaddr (firstfreeslot pdentry + scoffset) *)
             rewrite <-DTL.beqAddrTrue in HbeqFirstFreeFirstPlusSco.
             rewrite <-HbeqFirstFreeFirstPlusSco in *. unfold isSCE in HSCE. rewrite HlookupBlocks0 in HSCE.
             exfalso; congruence.
           }
           (* firstfreeslot pdentry <> CPaddr (firstfreeslot pdentry + scoffset) *)
           destruct (beqAddr blockInParentPartitionAddr (firstfreeslot pdentry)) eqn:HbeqBlockFirstFree.
           - (* blockInParentPartitionAddr = firstfreeslot pdentry *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockFirstFree. rewrite HbeqBlockFirstFree in *.
             rewrite <-beqAddrFalse in HbeqFirstFreeFirstPlusSh1.
             rewrite removeDupIdentity; try(intuition; congruence).
           - (* blockInParentPartitionAddr <> firstfreeslot pdentry *)
             rewrite <-beqAddrFalse in HbeqBlockFirstFree.
             rewrite removeDupIdentity; try(intuition; congruence).
             destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqFirstFreeFirstPlusSh1.
             rewrite removeDupIdentity; try(intuition; congruence).
             destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr);
                   try(intuition; congruence).
             destruct v; try(intuition; congruence).
             rewrite <-beqAddrFalse in HbeqFirstFreeFirstPlusSco.
             rewrite removeDupIdentity; try(intuition; congruence).
           (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
         }

         assert(multiplexerIsPDT s1).
         { (* BEGIN multiplexerIsPDT s1 *)
           assert(Hcons0: multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold multiplexerIsPDT in *.
           unfold isPDT in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr multiplexer) eqn:HbeqBlockMultip.
           - (* blockInParentPartitionAddr = multiplexer *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockMultip. rewrite HbeqBlockMultip in *.
             rewrite HlookupBlocks0 in Hcons0. congruence.
           - (* blockInParentPartitionAddr <> multiplexer *)
             rewrite <-beqAddrFalse in HbeqBlockMultip. rewrite removeDupIdentity; intuition.
          (* END multiplexerIsPDT *)
         }

         assert(currentPartitionInPartitionsList s1).
         { (* BEGIN currentPartitionInPartitionsList s1 *)
           assert(Hcons0: currentPartitionInPartitionsList s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold currentPartitionInPartitionsList in *.
           assert(HcurrPartEq: currentPartition s1 = currentPartition s0)
                 by (rewrite Hs1; simpl; reflexivity).
           assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
           {
             rewrite Hs1.
             assert(Hsh1: sh1entryAddr blockInParentPartitionAddr 
                           (CPaddr (blockInParentPartitionAddr + sh1offset)) s0)
                 by (apply DTL.lookupSh1EntryAddr with bentry; intuition).
             assert(HPDT: isPDT multiplexer s0).
             {
               assert(HisPDT: multiplexerIsPDT s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold multiplexerIsPDT in HisPDT. assumption.
             }
             assert(HPDTIfPDFlag: PDTIfPDFlag s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
             assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
             assert(HlookupEq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                              = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
             {
               rewrite Hs1. simpl.
               destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr+sh1offset)))
                   eqn:HbeqBlockBlockSh1.
               { (* blockInParentPartitionAddr = CPaddr (blockInParentPartitionAddr + sh1offset) *)
                 assert(HSHE: isSHE (CPaddr (blockInParentPartitionAddr + sh1offset)) s0).
                 {
                   unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
                   specialize(HwellFormeds0 blockInParentPartitionAddr). apply HwellFormeds0.
                   unfold isBE. rewrite HlookupBlocks0. trivial.
                 }
                 rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
                 unfold isSHE in HSHE. rewrite HlookupBlocks0 in HSHE. exfalso; congruence.
               }
               (* blockInParentPartitionAddr <> CPaddr (blockInParentPartitionAddr + sh1offset) *)
               rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
             }
             rewrite Hs1 in HlookupEq.
             apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
                   (CPaddr (blockInParentPartitionAddr + sh1offset)); try(intuition; congruence).
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
               reflexivity.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
               reflexivity.
           }
           rewrite HcurrPartEq. rewrite HgetPartEq. assumption.
           (* END currentPartitionInPartitionsList *)
         }

         assert(wellFormedShadowCutIfBlockEntry s1).
         { (* BEGIN wellFormedShadowCutIfBlockEntry s1 *)
           assert(Hcons0: wellFormedShadowCutIfBlockEntry s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold wellFormedShadowCutIfBlockEntry in *.
           intros pa HisBEpa.
           assert(HisBEs0: isBE pa s0).
           {
             unfold isBE in *. rewrite Hs1 in HisBEpa. simpl in HisBEpa.
             destruct (beqAddr blockInParentPartitionAddr pa) eqn:HbeqBlockPa.
             - (* blockInParentPartitionAddr = pa *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPa. rewrite HbeqBlockPa in *.
               rewrite HlookupBlocks0. trivial.
             - (* blockInParentPartitionAddr <> pa *)
               rewrite <-beqAddrFalse in HbeqBlockPa. rewrite removeDupIdentity in HisBEpa; intuition.
           }
           specialize(Hcons0 pa HisBEs0). destruct Hcons0 as [scentryaddr (HisSCE & HvalueSCE)].
           exists scentryaddr. split; try(assumption). unfold isSCE in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr scentryaddr) eqn:HbeqBlockSce.
           { (* blockInParentPartitionAddr = scentryaddr *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *.
             rewrite HlookupBlocks0 in HisSCE. congruence.
           }
           (* blockInParentPartitionAddr <> scentryaddr *)
           rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity; intuition.
           (* END wellFormedShadowCutIfBlockEntry *)
         }

         assert(BlocksRangeFromKernelStartIsBE s1).
         { (* BEGIN BlocksRangeFromKernelStartIsBE s1 *)
           assert(Hcons0: BlocksRangeFromKernelStartIsBE s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold BlocksRangeFromKernelStartIsBE in *.
           intros kernelEntry blockIdx HisKS HblockInfNbEntries.
           assert(HisKSs0: isKS kernelEntry s0).
           {
             unfold isKS in *. rewrite Hs1 in HisKS. simpl in HisKS.
             destruct (beqAddr blockInParentPartitionAddr kernelEntry) eqn:HbeqBlockKernEntry.
             { (* blockInParentPartitionAddr = kernelEntry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockKernEntry. rewrite HbeqBlockKernEntry in *.
               rewrite HlookupBlocks0. unfold CBlockEntry in HisKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HisKS. assumption.
             }
             (* blockInParentPartitionAddr <> kernelEntry *)
             rewrite <-beqAddrFalse in HbeqBlockKernEntry. rewrite removeDupIdentity in HisKS; intuition.
           }
           specialize(Hcons0 kernelEntry blockIdx HisKSs0 HblockInfNbEntries).
           unfold isBE in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (kernelEntry + blockIdx))) eqn:HbeqBlockKern.
           trivial.
           rewrite <-beqAddrFalse in HbeqBlockKern. rewrite removeDupIdentity; intuition.
           (* END BlocksRangeFromKernelStartIsBE *)
         }

         assert(KernelStructureStartFromBlockEntryAddrIsKS s1).
         { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s1 *)
           assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0)
                 by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold KernelStructureStartFromBlockEntryAddrIsKS in *.
           intros blockEntry blockIdx HisBE HblockIndex.
           assert(HisBEs0: isBE blockEntry s0).
           {
             unfold isBE in *. rewrite Hs1 in HisBE. simpl in HisBE.
             destruct (beqAddr blockInParentPartitionAddr blockEntry) eqn:HbeqBlockEntry.
             - (* blockInParentPartitionAddr = blockEntry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockEntry. rewrite HbeqBlockEntry in *.
               rewrite HlookupBlocks0. trivial.
             - (* blockInParentPartitionAddr <> blockEntry *)
               rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HisBE; intuition.
           }
           assert(HblockIndexs0: bentryBlockIndex blockEntry blockIdx s0).
           {
             unfold bentryBlockIndex in *. rewrite Hs1 in HblockIndex. simpl in HblockIndex.
             destruct (beqAddr blockInParentPartitionAddr blockEntry) eqn:HbeqBlockEntry.
             - (* blockInParentPartitionAddr = blockEntry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockEntry. rewrite HbeqBlockEntry in *.
               rewrite HlookupBlocks0. unfold CBlockEntry in HblockIndex.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HblockIndex. assumption.
             - (* blockInParentPartitionAddr <> blockEntry *)
               rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HblockIndex; intuition.
           }
           specialize(Hcons0 blockEntry blockIdx HisBEs0 HblockIndexs0). unfold isKS in *.
           rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockEntry-blockIdx)))
                   eqn: HbeqBlockBlockIdx.
           - (* blockInParentPartitionAddr = CPaddr (blockEntry-blockIdx) *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockBlockIdx. rewrite <-HbeqBlockBlockIdx in *.
             rewrite HlookupBlocks0 in Hcons0. unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
             assumption.
           - (* blockInParentPartitionAddr <> CPaddr (blockEntry-blockIdx) *)
             rewrite <- beqAddrFalse in HbeqBlockBlockIdx. rewrite removeDupIdentity; intuition.
            (* END KernelStructureStartFromBlockEntryAddrIsKS *)
         }

         assert(sh1InChildLocationIsBE s1).
         { (* BEGIN sh1InChildLocationIsBE s1 *)
           assert(Hcons0: sh1InChildLocationIsBE s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold sh1InChildLocationIsBE in *.
           intros sh1entryaddr sh1entry Hlookupsh1 HinChildLocNotNull.
           assert(Hlookupsh1s0: lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)).
           {
             rewrite Hs1 in Hlookupsh1. simpl in Hlookupsh1.
             destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1;
                   try(exfalso; congruence).
             (* blockInParentPartitionAddr <> sh1entryaddr *)
             rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity in Hlookupsh1; intuition.
           }
           specialize(Hcons0 sh1entryaddr sh1entry Hlookupsh1s0 HinChildLocNotNull).
           unfold isBE in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (inChildLocation sh1entry)) eqn:HbeqBlockInChild.
           - (* blockInParentPartitionAddr = inChildLocation sh1entry *)
             trivial.
           - (* blockInParentPartitionAddr <> inChildLocation sh1entry *)
             rewrite <-beqAddrFalse in HbeqBlockInChild. rewrite removeDupIdentity; intuition.
             (* END sh1InChildLocationIsBE *)
         }

         assert(StructurePointerIsKS s1).
         { (* BEGIN StructurePointerIsKS s1 *)
           assert(Hcons0: StructurePointerIsKS s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold StructurePointerIsKS in *.
           intros entryaddr0 pdentry HlookupEntry HstructNotNull.
           assert(HlookupEntrys0: lookup entryaddr0 (memory s0) beqAddr = Some (PDT pdentry)).
           {
             rewrite Hs1 in HlookupEntry. simpl in HlookupEntry.
             destruct (beqAddr blockInParentPartitionAddr entryaddr0) eqn:HbeqBlockEntry;
                   try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HlookupEntry; intuition.
           }
           specialize(Hcons0 entryaddr0 pdentry HlookupEntrys0 HstructNotNull). unfold isKS in *.
           rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (structure pdentry)) eqn:HbeqBlockStruct.
           - (* blockInParentPartitionAddr = structure pdentry *)
             unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
             rewrite <-DTL.beqAddrTrue in HbeqBlockStruct. rewrite HbeqBlockStruct in *.
             rewrite HlookupBlocks0 in Hcons0. assumption.
           - (* blockInParentPartitionAddr <> structure pdentry *)
             rewrite <-beqAddrFalse in HbeqBlockStruct. rewrite removeDupIdentity; intuition.
             (* END StructurePointerIsKS *)
         }

         assert(NextKSIsKS s1).
         { (* BEGIN NextKSIsKS s1 *)
           assert(Hcons0: NextKSIsKS s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NextKSIsKS in *.
           intros addr nextKSAddr nextKS HisKS HnextKSAddr HnextKSentry HnextKSNotNull.
           assert(HisKSs0: isKS addr s0).
           {
             unfold isKS in *. rewrite Hs1 in HisKS. simpl in HisKS.
             destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockAddr.
             - (* blockInParentPartitionAddr = addr *)
               unfold CBlockEntry in HisKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HisKS. rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. rewrite HbeqBlockAddr in *.
               rewrite HlookupBlocks0. assumption.
             - (* blockInParentPartitionAddr <> addr *)
               rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HisKS; intuition.
           }
           assert(HnextKSAddrs0: StateLib.nextKSAddr addr nextKSAddr s0).
           {
             unfold StateLib.nextKSAddr in *. rewrite Hs1 in HnextKSAddr. simpl in HnextKSAddr.
             destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockAddr.
             - (* blockInParentPartitionAddr = addr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. rewrite HbeqBlockAddr in *.
               rewrite HlookupBlocks0. assumption.
             - (* blockInParentPartitionAddr <> addr *)
               rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HnextKSAddr; intuition.
           }
           assert(HnextKSentrys0: nextKSentry nextKSAddr nextKS s0).
           {
             unfold nextKSentry in *. rewrite Hs1 in HnextKSentry. simpl in HnextKSentry.
             destruct (beqAddr blockInParentPartitionAddr nextKSAddr) eqn:HbeqBlockNextAddr;
                   try(exfalso; congruence).
             (* blockInParentPartitionAddr <> nextKSAddr *)
             rewrite <-beqAddrFalse in HbeqBlockNextAddr.
             rewrite removeDupIdentity in HnextKSentry; intuition.
           }
           specialize(Hcons0 addr nextKSAddr nextKS HisKSs0 HnextKSAddrs0 HnextKSentrys0 HnextKSNotNull).
           unfold isKS in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr nextKS) eqn:HbeqBlockNextKS.
           - (* blockInParentPartitionAddr = nextKS *)
             unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
             rewrite <-DTL.beqAddrTrue in HbeqBlockNextKS. rewrite HbeqBlockNextKS in *.
             rewrite HlookupBlocks0 in Hcons0. assumption.
           - (* blockInParentPartitionAddr <> nextKS *)
             rewrite <-beqAddrFalse in HbeqBlockNextKS. rewrite removeDupIdentity; intuition.
           (* END NextKSIsKS *)
         }

         assert(NextKSOffsetIsPADDR s1).
         { (* BEGIN NextKSOffsetIsPADDR s1 *)
           assert(Hcons0: NextKSOffsetIsPADDR s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NextKSOffsetIsPADDR in *.
           intros addr nextKSaddr HisKS HnextKSAddr.
           assert(HisKSs0: isKS addr s0).
           {
             unfold isKS in *. rewrite Hs1 in HisKS. simpl in HisKS.
             destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockAddr.
             - (* blockInParentPartitionAddr = addr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. rewrite HbeqBlockAddr in *.
               unfold CBlockEntry in HisKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HisKS. rewrite HlookupBlocks0. assumption.
             - (* blockInParentPartitionAddr <> addr *)
               rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HisKS; intuition.
           }
           assert(HnextKSAddrs0: nextKSAddr addr nextKSaddr s0).
           {
             unfold nextKSAddr in *. rewrite Hs1 in HnextKSAddr. simpl in HnextKSAddr.
             destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockAddr.
             - (* blockInParentPartitionAddr = addr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. rewrite HbeqBlockAddr in *.
               unfold CBlockEntry in HisKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HisKS. rewrite HlookupBlocks0. assumption.
             - (* blockInParentPartitionAddr <> addr *)
               rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HnextKSAddr; intuition.
           }
           specialize(Hcons0 addr nextKSaddr HisKSs0 HnextKSAddrs0). unfold isPADDR in *.
           rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr nextKSaddr) eqn:HbeqBlockNextKS.
           { (* blockInParentPartitionAddr = nextKSaddr *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockNextKS. rewrite HbeqBlockNextKS in *.
             destruct (lookup nextKSaddr (memory s0) beqAddr); try(exfalso; intuition; congruence).
             destruct v; try(exfalso; intuition; congruence).
           }
           (* blockInParentPartitionAddr <> nextKSaddr *)
           rewrite <-beqAddrFalse in HbeqBlockNextKS. rewrite removeDupIdentity; intuition.
           (* END NextKSOffsetIsPADDR *)
         }

         assert(NoDupInFreeSlotsList s1).
         { (* BEGIN NoDupInFreeSlotsList s1 *)
           assert(Hcons0: NoDupInFreeSlotsList s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NoDupInFreeSlotsList in *.
           intros pd pdentry HlookupPd.
           assert(HlookupPds0: lookup pd (memory s0) beqAddr = Some (PDT pdentry)).
           {
             rewrite Hs1 in HlookupPd. simpl in HlookupPd.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity in HlookupPd; intuition.
           }
           specialize(Hcons0 pd pdentry HlookupPds0). destruct Hcons0 as [optionFreeSlotsList Hcons0].
           exists optionFreeSlotsList. split.
           - destruct Hcons0 as [HgetFree Hcons0]. subst optionFreeSlotsList. apply eq_sym.
             apply HgetFreeSlotsListEq.
             + unfold isPDT. rewrite HlookupPds0. trivial.
             + rewrite HlookupPd. rewrite HlookupPds0. reflexivity.
           - intuition.
           (* END NoDupInFreeSlotsList *)
         }

         assert(freeSlotsListIsFreeSlot s1).
         { (* BEGIN freeSlotsListIsFreeSlot s1 *)
           assert(Hcons0: freeSlotsListIsFreeSlot s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold freeSlotsListIsFreeSlot in *.
           intros pd freeSlotAddr optionFreeSlotsList freeSlotsList HisPDT HoptionList HfreeSlotsList
               HaddNotNull.
           assert(HlookupPdEq: lookup pd (memory s1) beqAddr = lookup pd (memory s0) beqAddr).
           {
             unfold isPDT in HisPDT. rewrite Hs1 in *. simpl in *.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd.
             { (* blockInParentPartitionAddr = pd *)
               exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> pd *)
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; intuition.
           }
           assert(HisPDTs0: isPDT pd s0).
           {
             unfold isPDT in *. rewrite HlookupPdEq in HisPDT. assumption.
           }
           assert(HoptionLists0: optionFreeSlotsList = getFreeSlotsList pd s0
                                 /\ wellFormedFreeSlotsList optionFreeSlotsList <> False).
           {
             split.
             - destruct HoptionList as [HoptionList HwellFormedList]. subst optionFreeSlotsList.
               apply HgetFreeSlotsListEq; assumption.
             - intuition.
           }
           specialize(Hcons0 pd freeSlotAddr optionFreeSlotsList freeSlotsList HisPDTs0 HoptionLists0
                       HfreeSlotsList HaddNotNull).
           unfold isFreeSlot in *. rewrite Hs1. simpl.
           assert(HisBE: isBE freeSlotAddr s0).
           {
             unfold isBE. destruct (lookup freeSlotAddr (memory s0) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence). trivial.
           }
           assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
           specialize(HwellFormeds0 freeSlotAddr HisBE).
           assert(HwellFormedCuts0: wellFormedShadowCutIfBlockEntry s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold wellFormedShadowCutIfBlockEntry in HwellFormedCuts0.
           specialize(HwellFormedCuts0 freeSlotAddr HisBE).
           destruct HwellFormedCuts0 as [scentryaddr (HwellFormedCuts0 & HsceValue)].
           subst scentryaddr.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (freeSlotAddr + sh1offset))) eqn:HbeqBlockSh1.
           { (* blockInParentPartitionAddr = CPaddr (freeSlotAddr + sh1offset) *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *.
             unfold isSHE in HwellFormeds0. rewrite HlookupBlocks0 in HwellFormeds0.
             exfalso; congruence.
           }
           (* blockInParentPartitionAddr = CPaddr (freeSlotAddr + sh1offset) *)
           destruct (beqAddr blockInParentPartitionAddr freeSlotAddr) eqn:HbeqBlockFreeSlot.
           - (* blockInParentPartitionAddr = freeSlotAddr *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockFreeSlot. rewrite HbeqBlockFreeSlot in *.
             rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition; congruence.
           - (* blockInParentPartitionAddr <> freeSlotAddr *)
             rewrite <-beqAddrFalse in HbeqBlockFreeSlot.
             rewrite removeDupIdentity; try(intuition;congruence).
             destruct (lookup freeSlotAddr (memory s0) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSh1.
             rewrite removeDupIdentity; try(intuition; congruence).
             unfold isSHE in HwellFormeds0.
             destruct (lookup (CPaddr (freeSlotAddr + sh1offset)) (memory s0) beqAddr);
                 try(exfalso; congruence).
             destruct v; try(exfalso; congruence).
             destruct (beqAddr blockInParentPartitionAddr (CPaddr (freeSlotAddr + scoffset)))
                 eqn:HbeqBlockFreeSco.
             { (* blockInParentPartitionAddr = CPaddr (freeSlotAddr + scoffset) *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockFreeSco. rewrite <-HbeqBlockFreeSco in *.
               unfold isSCE in HwellFormedCuts0. rewrite HlookupBlocks0 in HwellFormedCuts0. congruence.
             }
             (* blockInParentPartitionAddr <> CPaddr (freeSlotAddr + scoffset) *)
             rewrite <-beqAddrFalse in HbeqBlockFreeSco. rewrite removeDupIdentity; intuition.
           (* END freeSlotsListIsFreeSlot *)
         }

         assert(DisjointFreeSlotsLists s1).
         { (* BEGIN DisjointFreeSlotsLists s1 *)
           assert(Hcons0: DisjointFreeSlotsLists s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold DisjointFreeSlotsLists in *.
           intros pd1 pd2 HisPDTpd1 HisPDTpd2 HpdNotEq.
           assert(HisPDTpd1s0: isPDT pd1 s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDTpd1. simpl in HisPDTpd1.
             destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity in HisPDTpd1; intuition.
           }
           assert(HisPDTpd2s0: isPDT pd2 s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDTpd2. simpl in HisPDTpd2.
             destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity in HisPDTpd2; intuition.
           }
           specialize(Hcons0 pd1 pd2 HisPDTpd1s0 HisPDTpd2s0 HpdNotEq).
           destruct Hcons0 as [optionFreeSlotsList1 (optionFreeSlotsList2 & (HoptionFreeSlotsList1 &
                     (HwellFormed1 & (HoptionFreeSlotsList2 & (HwellFormed2 & Hdisjoint)))))].
           exists optionFreeSlotsList1. exists optionFreeSlotsList2.
           assert(HgetFrees1: optionFreeSlotsList1 = getFreeSlotsList pd1 s1).
           {
             subst optionFreeSlotsList1. apply eq_sym. apply HgetFreeSlotsListEq. assumption.
             rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1.
             - (* blockInParentPartitionAddr = pd1 *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPd1. rewrite HbeqBlockPd1 in *.
               unfold isPDT in HisPDTpd1s0. rewrite HlookupBlocks0 in HisPDTpd1s0. exfalso;congruence.
             - (* blockInParentPartitionAddr <> pd1 *)
               rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity; intuition.
           }
           assert(HgetFrees2: optionFreeSlotsList2 = getFreeSlotsList pd2 s1).
           {
             subst optionFreeSlotsList2. apply eq_sym. apply HgetFreeSlotsListEq. assumption.
             rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2.
             - (* blockInParentPartitionAddr = pd2 *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPd2. rewrite HbeqBlockPd2 in *.
               unfold isPDT in HisPDTpd2s0. rewrite HlookupBlocks0 in HisPDTpd2s0. exfalso; congruence.
             - (* blockInParentPartitionAddr <> pd2 *)
               rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity; intuition.
           }
           intuition.
           (* END DisjointFreeSlotsLists *)
         }

         assert(inclFreeSlotsBlockEntries s1).
         { (* BEGIN inclFreeSlotsBlockEntries s1 *)
           assert(Hcons0: inclFreeSlotsBlockEntries s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold inclFreeSlotsBlockEntries in *.
           intros pd HisPDT.
           assert(HlookupPdEq: lookup pd (memory s1) beqAddr = lookup pd (memory s0) beqAddr).
           {
             rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd.
             { (* blockInParentPartitionAddr = pd *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPd. rewrite HbeqBlockPd in *. unfold isPDT in HisPDT.
               rewrite HlookupBlocks1 in HisPDT. exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> pd *)
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; intuition.
           }
           assert(HisPDTs0: isPDT pd s0).
           {
             unfold isPDT in *. rewrite HlookupPdEq in HisPDT. assumption.
           }
           specialize(Hcons0 pd HisPDTs0).
           assert(HgetFreeEq: getFreeSlotsList pd s1 = getFreeSlotsList pd s0).
           { apply HgetFreeSlotsListEq; assumption. }
           rewrite HgetFreeEq.
           assert(HgetKSEq: getKSEntries pd s1 = getKSEntries pd s0).
           {
             rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           rewrite HgetKSEq. assumption.
           (* END inclFreeSlotsBlockEntries *)
         }

         assert(DisjointKSEntries s1).
         { (* BEGIN DisjointKSEntries s1 *)
           assert(Hcons0: DisjointKSEntries s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold DisjointKSEntries in *.
           intros pd1 pd2 HisPDTpd1 HisPDTpd2 HpdNotEq.
           assert(HisPDTpd1s0: isPDT pd1 s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDTpd1. simpl in HisPDTpd1.
             destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity in HisPDTpd1; intuition.
           }
           assert(HisPDTpd2s0: isPDT pd2 s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDTpd2. simpl in HisPDTpd2.
             destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity in HisPDTpd2; intuition.
           }
           specialize(Hcons0 pd1 pd2 HisPDTpd1s0 HisPDTpd2s0 HpdNotEq).
           assert(HgetKS1Eq: getKSEntries pd1 s1 = getKSEntries pd1 s0).
           {
             rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           assert(HgetKS2Eq: getKSEntries pd2 s1 = getKSEntries pd2 s0).
           {
             rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           rewrite HgetKS1Eq. rewrite HgetKS2Eq. assumption.
           (* END DisjointKSEntries *)
         }

         assert(noDupPartitionTree s1).
         { (* BEGIN noDupPartitionTree s1 *)
           assert(Hcons0: noDupPartitionTree s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold noDupPartitionTree in *.
           assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
           {
             rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
                               (CPaddr (blockInParentPartitionAddr + sh1offset)).
             - assert(multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold multiplexerIsPDT in *. assumption.
             - assumption.
             - unfold consistency in *; unfold consistency1 in *; intuition.
             - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
             - simpl.
               assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
                       by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
               assert(HisBEBlock: isBE blockInParentPartitionAddr s0).
               { unfold isBE. rewrite HlookupBlocks0. trivial. }
               specialize(HwellFormeds0 blockInParentPartitionAddr HisBEBlock).
               destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
                   eqn:HbeqBlockSh1.
               { (* blockInParentPartitionAddr = CPaddr (blockInParentPartitionAddr + sh1offset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *.
                 unfold isSHE in HwellFormeds0. rewrite HlookupBlocks0 in HwellFormeds0. exfalso; congruence.
               }
               (* blockInParentPartitionAddr <> CPaddr (blockInParentPartitionAddr + sh1offset) *)
               rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
             - unfold consistency in *; unfold consistency1 in *; intuition.
           }
           rewrite HgetPartEq. assumption.
           (* END noDupPartitionTree *)
         }

         assert(HgetPartEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
         {
           rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
                             (CPaddr (blockInParentPartitionAddr + sh1offset)).
           - assert(multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold multiplexerIsPDT in *. assumption.
           - assumption.
           - unfold consistency in *; unfold consistency1 in *; intuition.
           - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
           - simpl.
             assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
                     by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
             assert(HisBEBlock: isBE blockInParentPartitionAddr s0).
             { unfold isBE. rewrite HlookupBlocks0. trivial. }
             specialize(HwellFormeds0 blockInParentPartitionAddr HisBEBlock).
             destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
                 eqn:HbeqBlockSh1.
             { (* blockInParentPartitionAddr = CPaddr (blockInParentPartitionAddr + sh1offset) *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *.
               unfold isSHE in HwellFormeds0. rewrite HlookupBlocks0 in HwellFormeds0. exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> CPaddr (blockInParentPartitionAddr + sh1offset) *)
             rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition.
           - unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
             simpl. reflexivity.
           - unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
             simpl. reflexivity.
           - unfold consistency in *; unfold consistency1 in *; intuition.
         }

         assert(isParent s1).
         { (* BEGIN isParent s1 *)
           assert(Hcons0: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold isParent in *.
           intros partition parent HparentIsPart HpartitionIsChild.
           rewrite HgetPartEq in HparentIsPart.
           assert(HgetChildrenEq: getChildren parent s1 = getChildren parent s0).
           {
             rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry.
             - apply partitionsArePDT; try(unfold consistency in *; unfold consistency1 in *; intuition).
             - assumption.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
           }
           rewrite HgetChildrenEq in HpartitionIsChild.
           specialize(Hcons0 partition parent HparentIsPart HpartitionIsChild).
           unfold StateLib.pdentryParent in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
           { (* blockInParentPartitionAddr = partition *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *.
             rewrite HlookupBlocks0 in Hcons0. congruence.
           }
           (* blockInParentPartitionAddr <> partition *)
           rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; intuition.
           (* END isParent *)
         }

         assert(isChild s1).
         { (* BEGIN isChild s1 *)
           assert(Hcons0: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold isChild in *.
           intros partition parent HpartIsPart HparentIsParent.
           rewrite HgetPartEq in HpartIsPart.
           assert(HparentIsParents0: StateLib.pdentryParent partition parent s0).
           {
             unfold StateLib.pdentryParent in *. rewrite Hs1 in HparentIsParent. simpl in HparentIsParent.
             destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
             { (* blockInParentPartitionAddr = partition *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *.
               exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> partition *)
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HparentIsParent; intuition.
           }
           specialize(Hcons0 partition parent HpartIsPart HparentIsParents0).
           assert(HgetChildrenEq: getChildren parent s1 = getChildren parent s0).
           {
             rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry.
             - unfold isPDT. unfold StateLib.pdentryParent in HparentIsParents0.
               destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               assert(HparentIsPart: parentOfPartitionIsPartition s0)
                     by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold parentOfPartitionIsPartition in HparentIsPart.
               specialize(HparentIsPart partition p HlookupPart).
               destruct HparentIsPart as [HparentIsPart (HparentOfRoot & HparentPartNotEq)].
               destruct (beqAddr partition constantRootPartM) eqn:HbeqPartRoot.
               { (* partition = constantRootPartM *)
                 rewrite <-DTL.beqAddrTrue in HbeqPartRoot. specialize(HparentOfRoot HbeqPartRoot).
                 rewrite HparentOfRoot in *. subst parent.
                 assert(Hnull: nullAddrExists s0)
                      by (unfold consistency in *; unfold consistency1 in *; intuition).
                 unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
                 unfold getChildren in Hcons0.
                 assert(Hcontra: ~In partition []) by (apply in_nil).
                 destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
                 destruct v; try(exfalso; congruence).
               }
               (* partition <> constantRootPartM *)
               rewrite <-beqAddrFalse in HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
               destruct HparentIsPart as [parentEntry HparentIsPart]. subst parent.
               rewrite HparentIsPart. trivial.
             - assumption.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
           }
           rewrite HgetChildrenEq. assumption.
           (* END isChild *)
         }

         assert(noDupKSEntriesList s1).
         { (* BEGIN noDupKSEntriesList s1 *)
           assert(Hcons0: noDupKSEntriesList s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold noDupKSEntriesList in *.
           intros partition HisPDT.
           assert(HisPDTs0: isPDT partition s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDT. simpl in HisPDT.
             destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart;
                   try(exfalso; congruence).
             (* blockInParentPartitionAddr <> partition *)
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HisPDT; intuition.
           }
           specialize(Hcons0 partition HisPDTs0).
           assert(HgetKSEq: getKSEntries partition s1 = getKSEntries partition s0).
           {
             rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           rewrite HgetKSEq. assumption.
           (* END noDupKSEntriesList *)
         }

         assert(noDupMappedBlocksList s1).
         { (* BEGIN noDupMappedBlocksList s1 *)
           assert(Hcons0: noDupMappedBlocksList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold noDupMappedBlocksList in *.
           intros partition HisPDT.
           assert(HisPDTs0: isPDT partition s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDT. simpl in HisPDT.
             destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart;
                   try(exfalso; congruence).
             (* blockInParentPartitionAddr <> partition *)
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HisPDT; intuition.
           }
           specialize(Hcons0 partition HisPDTs0).
           assert(HgetMappedEq: getMappedBlocks partition s1 = getMappedBlocks partition s0).
           {
             rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
             unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
             simpl. reflexivity.
           }
           rewrite HgetMappedEq. assumption.
           (* END noDupMappedBlocksList *)
         }

         assert(wellFormedBlock s1).
         { (* BEGIN wellFormedBlock s1 *)
           assert(Hcons0: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold wellFormedBlock in *.
           intros block startaddr endaddr HbPFlag HbStartAddr HbEndAddr.
           assert(HbPFlags0: bentryPFlag block true s0).
           {
             unfold bentryPFlag in *. rewrite Hs1 in HbPFlag. simpl in HbPFlag.
             destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
             - (* blockInParentPartitionAddr = block *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *.
               rewrite HlookupBlocks0. unfold CBlockEntry in HbPFlag.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HbPFlag. assumption.
             - (* blockInParentPartitionAddr <> block *)
               rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HbPFlag; intuition.
           }
           assert(HbStartAddrs0: bentryStartAddr block startaddr s0).
           {
             unfold bentryStartAddr in *. rewrite Hs1 in HbStartAddr. simpl in HbStartAddr.
             destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
             - (* blockInParentPartitionAddr = block *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *.
               rewrite HlookupBlocks0. unfold CBlockEntry in HbStartAddr.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HbStartAddr. assumption.
             - (* blockInParentPartitionAddr <> block *)
               rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HbStartAddr; intuition.
           }
           assert(HbEndAddrs0: bentryEndAddr block endaddr s0).
           {
             unfold bentryEndAddr in *. rewrite Hs1 in HbEndAddr. simpl in HbEndAddr.
             destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
             - (* blockInParentPartitionAddr = block *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *.
               rewrite HlookupBlocks0. unfold CBlockEntry in HbEndAddr.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HbEndAddr. assumption.
             - (* blockInParentPartitionAddr <> block *)
               rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HbEndAddr; intuition.
           }
           specialize(Hcons0 block startaddr endaddr HbPFlags0 HbStartAddrs0 HbEndAddrs0). assumption.
           (* END wellFormedBlock *)
         }

         assert(MPUFromAccessibleBlocks s1).
         { (* BEGIN MPUFromAccessibleBlocks s1 *)
           assert(Hcons0: MPUFromAccessibleBlocks s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold MPUFromAccessibleBlocks in *.
           intros partition block blocksInMPU HMPUpart HblockInMPU HblockNotNull.
           assert(HMPUparts0: pdentryMPU partition blocksInMPU s0).
           {
             unfold pdentryMPU in *. rewrite Hs1 in HMPUpart. simpl in HMPUpart.
             destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
             { (* blockInParentPartitionAddr = partition *)
               exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> partition *)
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HMPUpart; intuition.
           }
           destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
           { (* blockInParentPartitionAddr = block *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block. admit.
             (*TODO contra, blockInParentPartitionAddr probably shouldn't be in the MPU*)
           }
           (* blockInParentPartitionAddr <> block *)
           rewrite <-beqAddrFalse in HbeqBlockBlock.
           specialize(Hcons0 partition block blocksInMPU HMPUparts0 HblockInMPU HblockNotNull).
           destruct (beqAddr pdparent partition) eqn:HbeqParentPart.
           - (* pdparent = partition *)
             rewrite <-DTL.beqAddrTrue in HbeqParentPart. subst partition.
             destruct (eqb flag (accessible bentry)) eqn:HbeqFlagAccess.
             + (* flag = accessible bentry *)
               apply eqb_prop in HbeqFlagAccess. subst flag.
               assert(HgetAccMappedEq: getAccessibleMappedBlocks pdparent s1
                                        = getAccessibleMappedBlocks pdparent s0).
               {
                 rewrite HnewB in HnewBentry. rewrite HnewBentry in Hs1. rewrite Hs1.
                 apply getAccessibleMappedBlocksEqBEAccessiblePresentNoChange with bentry;
                        try(assumption); simpl; reflexivity.
               }
               rewrite HgetAccMappedEq. assumption.
             + (* flag <> accessible bentry *)
               assert(HparentIsPDTs0: isPDT pdparent s0).
               {
                 unfold isPDT. rewrite Hs1 in HlookupParent. simpl in HlookupParent.
                 destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent;
                     try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqBlockParent.
                 rewrite removeDupIdentity in HlookupParent; try(intuition; congruence).
                 rewrite HlookupParent. trivial.
               }
               apply eqb_false_iff in HbeqFlagAccess. destruct flag.
               * (* flag = true *)
                 rewrite HnewB in HnewBentry. rewrite HnewBentry in Hs1. rewrite Hs1.
                 apply <-getAccessibleMappedBlocksEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence; simpl;
                        try(instantiate(1:= bentry)); try(unfold consistency1 in Hconsists0; intuition;
                        congruence).
                 -- unfold getMappedBlocks in HblockInMappedBlocks.
                    apply InFilterPresentInList in HblockInMappedBlocks.
                    assert(HgetKSentriesEq: getKSEntries pdparent s1 = getKSEntries pdparent s0).
                    { rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks0. trivial. }
                    rewrite HgetKSentriesEq in HblockInMappedBlocks. assumption.
                 -- unfold bentryPFlag in HPFlag. rewrite HlookupBlocks1 in HPFlag.
                    rewrite <-HnewB in HnewBentry. rewrite HnewBentry in HPFlag. simpl in HPFlag. intuition.
               * (* flag = false *)
                 rewrite Hs1.
                 apply getAccessibleMappedBlocksEqBEPresentTrueNoChangeAccessibleFalseChangeInclusion with
                       bentry;
                      try(rewrite <-HnewB; rewrite HnewBentry; simpl);
                      try(intuition; congruence).
                 unfold bentryPFlag in HPFlag. rewrite HlookupBlocks1 in HPFlag.
                 rewrite HnewBentry in HPFlag. simpl in HPFlag. intuition.
           - (* pdparent <> partition *)
             assert(HpartIsPDTs0: isPDT partition s0).
             {
               unfold pdentryMPU in HMPUparts0.
               unfold isPDT. destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence).
               destruct v; try(exfalso; congruence). trivial.
             }
             assert(HparentIsPDTs0: isPDT pdparent s0).
             {
               unfold isPDT. rewrite Hs1 in HlookupParent. simpl in HlookupParent.
               destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent;
                   try(exfalso; congruence).
               rewrite <-beqAddrFalse in HbeqBlockParent.
               rewrite removeDupIdentity in HlookupParent; try(intuition; congruence).
               rewrite HlookupParent. trivial.
             }
             assert(HgetAccMappedEq: getAccessibleMappedBlocks partition s1
                                     = getAccessibleMappedBlocks partition s0).
             {
               rewrite Hs1. apply getAccessibleMappedBlocksEqBENotInPart.
               assumption.
               unfold isBE. rewrite HlookupBlocks0. trivial.
               assert(Hdisjoints0: DisjointKSEntries s0) by (unfold consistency1 in Hconsists0; intuition).
               rewrite <-beqAddrFalse in HbeqParentPart.
               specialize(Hdisjoints0 pdparent partition HparentIsPDTs0 HpartIsPDTs0 HbeqParentPart).
               destruct Hdisjoints0 as [listKS1 (listKS2 & (Hlist1 & Hlist2 & Hdisjoints0))].
               subst listKS1. subst listKS2.
               assert(HblockInKS: In blockInParentPartitionAddr (filterOptionPaddr (getKSEntries pdparent s0))).
               {
                 rewrite HblockInMappedBlocksEqs1 in HblockInMappedBlocks.
                 unfold getMappedBlocks in HblockInMappedBlocks. apply InFilterPresentInList with s0; assumption.
               }
               specialize(Hdisjoints0 blockInParentPartitionAddr HblockInKS). assumption.
             }
             rewrite HgetAccMappedEq. assumption.
           (* END MPUFromAccessibleBlocks *)
         }

         assert(parentOfPartitionIsPartition s1).
         { (* BEGIN parentOfPartitionIsPartition s1 *)
           assert(Hcons0: parentOfPartitionIsPartition s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold parentOfPartitionIsPartition in *.
           intros partition entry HlookupPart.
           assert(HlookupParts0: lookup partition (memory s0) beqAddr = Some (PDT entry)).
           {
             rewrite Hs1 in HlookupPart. simpl in HlookupPart.
             destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart;
                   try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPart; intuition.
           }
           specialize(Hcons0 partition entry HlookupParts0).
           destruct Hcons0 as [HparentIsPart (HparentOfRoot & HparentPartNotEq)]. split.
           - intro HpartNotRoot. specialize(HparentIsPart HpartNotRoot).
             destruct HparentIsPart as [parentEntry HparentIsPart]. exists parentEntry.
             rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr (parent entry)) eqn:HbeqBlockParent.
             { (* blockInParentPartitionAddr = parent entry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *.
               rewrite HlookupBlocks0 in HparentIsPart. exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> parent entry *)
             rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
           - split. intro HpartIsRoot. specialize(HparentOfRoot HpartIsRoot). assumption. assumption.
           (* END parentOfPartitionIsPartition *)
         }

         assert(NbFreeSlotsISNbFreeSlotsInList s1).
         { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s1 *)
           assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NbFreeSlotsISNbFreeSlotsInList in *.
           intros pd nbfreeslots HisPDT HnbFreeSlots.
           assert(HisPDTs0: isPDT pd s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDT. simpl in HisPDT.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity in HisPDT; intuition.
           }
           assert(HnbFreeSlotss0: pdentryNbFreeSlots pd nbfreeslots s0).
           {
             unfold pdentryNbFreeSlots in *. rewrite Hs1 in HnbFreeSlots. simpl in HnbFreeSlots.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity in HnbFreeSlots; intuition.
           }
           specialize(Hcons0 pd nbfreeslots HisPDTs0 HnbFreeSlotss0).
           destruct Hcons0 as [optionFreeSlotsList (HgetFreeSlots & (HwellFormedList &
                   HnbFreeSlotsIsLength))].
           exists optionFreeSlotsList. split.
           - unfold getFreeSlotsList in *. rewrite Hs1. simpl. unfold isPDT in HisPDT. rewrite Hs1 in HisPDT.
             simpl in HisPDT.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; try(intuition; congruence).
             destruct (lookup pd (memory s0) beqAddr) eqn:HlookupPds0; try(assumption).
             destruct v; try(assumption).
             destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; try(assumption).
             assert(HbeqFirstFreeBlock: firstfreeslot p <> blockInParentPartitionAddr).
             {
               assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
                     by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold FirstFreeSlotPointerIsBEAndFreeSlot in HfirstFree.
               rewrite <-beqAddrFalse in HbeqFirstFreeNull.
               specialize(HfirstFree pd p HlookupPds0 HbeqFirstFreeNull).
               destruct HfirstFree as [HfirstIsBE HfirstIsFree].
               intro Hcontra. rewrite Hcontra in HfirstIsFree. congruence.
             }
             assert(HnoDups0: NoDupInFreeSlotsList s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold NoDupInFreeSlotsList in HnoDups0.
             specialize(HnoDups0 pd p HlookupPds0).
             destruct HnoDups0 as [optionFreeSlotsListCopy (HoptionListCopy & (HwellFormedListCopy &
                                                 HnoDupListCopy))].
             unfold getFreeSlotsList in HoptionListCopy. rewrite HlookupPds0 in HoptionListCopy.
             rewrite HbeqFirstFreeNull in HoptionListCopy. subst optionFreeSlotsListCopy.
             subst optionFreeSlotsList. apply eq_sym.
             apply getFreeSlotsListRecEqBE; try(intuition; congruence).
             + unfold isBE. rewrite HlookupBlocks0. trivial.
             + intro Hcontra.
               set(optionFreeSlotsList:=
                         getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (ADT.nbfreeslots p)).
               assert(HisInGetFree: optionFreeSlotsList = getFreeSlotsList pd s0
                                     /\ wellFormedFreeSlotsList optionFreeSlotsList <> False).
               {
                 split.
                 - unfold getFreeSlotsList. rewrite HlookupPds0. rewrite HbeqFirstFreeNull. intuition.
                 - intuition.
               }
               assert(HfreeSlotsAreFree: freeSlotsListIsFreeSlot s0)
                     by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold freeSlotsListIsFreeSlot in HfreeSlotsAreFree.
               assert(HisPDTCopy: isPDT pd s0) by (unfold isPDT; rewrite HlookupPds0; trivial).
               assert(HinList: filterOptionPaddr optionFreeSlotsList = filterOptionPaddr optionFreeSlotsList
                       /\ In blockInParentPartitionAddr (filterOptionPaddr optionFreeSlotsList)).
               { intuition. }
               rewrite <-beqAddrFalse in HbeqBlockNull.
               specialize(HfreeSlotsAreFree pd blockInParentPartitionAddr optionFreeSlotsList
                         (filterOptionPaddr optionFreeSlotsList) HisPDTCopy HisInGetFree HinList 
                         HbeqBlockNull).
               congruence.
           - intuition.
           (* END NbFreeSlotsISNbFreeSlotsInList *)
         }

         assert(maxNbPrepareIsMaxNbKernels s1).
         { (* BEGIN maxNbPrepareIsMaxNbKernels s1 *)
           assert(Hcons0: maxNbPrepareIsMaxNbKernels s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold maxNbPrepareIsMaxNbKernels in *.
           intros partition kernList HisKernList.
           assert(HisKernLists0: isListOfKernels kernList partition s0).
           {
             apply isListOfKernelsEqBE with blockInParentPartitionAddr newBentry; try(intuition; congruence).
           }
           specialize(Hcons0 partition kernList HisKernLists0). assumption.
           (* END maxNbPrepareIsMaxNbKernels *)
         }
         unfold consistency1. intuition.
       }

       assert(HnoDups1: noDupUsedPaddrList s1).
       { (* BEGIN noDupUsedPaddrList s1 *)
         assert(Hcons0: noDupUsedPaddrList s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
         unfold noDupUsedPaddrList in *.
         intros partition HisPDTs1.
         assert(HisPDTs0: isPDT partition s0).
         {
           unfold isPDT in *. rewrite Hs1 in HisPDTs1. simpl in HisPDTs1.
           destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
           rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HisPDTs1; intuition.
         }
         specialize(Hcons0 partition HisPDTs0).
         assert(HusedPaddrEq: getUsedPaddr partition s1 = getUsedPaddr partition s0).
         {
           unfold getUsedPaddr in *.
           assert(HgetConfigEq: getConfigPaddr partition s1 = getConfigPaddr partition s0).
           {
             rewrite Hs1. apply getConfigPaddrEqBE; try(assumption).
             unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           assert(HgetMappedEq: getMappedPaddr partition s1 = getMappedPaddr partition s0).
           {
             rewrite Hs1.
             apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
                   try(assumption);
                   try(unfold CBlockEntry;
                       destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                       simpl; reflexivity).
           }
           rewrite HgetConfigEq. rewrite HgetMappedEq. reflexivity.
         }
         rewrite HusedPaddrEq. assumption.
         (* END noDupUsedPaddrList *)
       }

       assert(Hshareds1: sharedBlockPointsToChild s1).
       { (* BEGIN sharedBlockPointsToChild s1 *)
         assert(Hcons0: sharedBlockPointsToChild s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
         unfold sharedBlockPointsToChild in *.
         intros parent child addr parentblock sh1entryaddr HparentIsPart HchildIsChild HaddrIsInChild
             HaddrIsInParentBlock HparentBlockIsMappedInParent Hsh1ParentBlock.
         assert(HgetPartMultEq: getPartitions multiplexer s1 = getPartitions multiplexer s0).
         {
           rewrite Hs1.
           apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
                 with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
               try(unfold consistency in *; unfold consistency1 in *; intuition; congruence);
               try(unfold CBlockEntry;
                   destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                   simpl; reflexivity).
           - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
           - simpl.
             destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
                 eqn:HbeqBlockBlockSh1.
             { (* beqAddr blockInParentPartitionAddr = CPaddr (blockInParentPartitionAddr + sh1offset) *)
               assert(HwellFormed: wellFormedFstShadowIfBlockEntry s0)
                       by (unfold consistency in *; unfold consistency1 in *; intuition).
               assert(HblockIsBE: isBE blockInParentPartitionAddr s0)
                       by (unfold isBE; rewrite HlookupBlocks0; trivial).
               specialize(HwellFormed blockInParentPartitionAddr HblockIsBE).
               rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
               unfold isSHE in HwellFormed. rewrite HlookupBlocks0 in HwellFormed. exfalso; congruence.
             }
             (* beqAddr blockInParentPartitionAddr <> CPaddr (blockInParentPartitionAddr + sh1offset) *)
             rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
         }
         rewrite HgetPartMultEq in HparentIsPart.
         assert(HgetChildrenEq: getChildren parent s1 = getChildren parent s0).
         {
           rewrite Hs1.
           apply getChildrenEqBENoStartNoPresentChange with bentry;
                 try(assumption);
                 try(unfold CBlockEntry;
                     destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                     simpl; reflexivity).
           apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
         }
         rewrite HgetChildrenEq in HchildIsChild.
         assert(HgetUsedPaddrEq: getUsedPaddr child s1 = getUsedPaddr child s0).
         {
           unfold getUsedPaddr.
           assert(isPDT child s0).
           {
             apply childrenArePDT with parent; unfold consistency in *; unfold consistency1 in *; intuition.
           }
           assert(HgetConfigEq: getConfigPaddr child s1 = getConfigPaddr child s0).
           {
             rewrite Hs1. apply getConfigPaddrEqBE; try(assumption).
             unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           assert(HgetMappedPaddrEq: getMappedPaddr child s1 = getMappedPaddr child s0).
           {
             rewrite Hs1.
             apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
                 try(assumption);
                 try(unfold CBlockEntry;
                     destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                     simpl; reflexivity).
           }
           rewrite HgetConfigEq. rewrite HgetMappedPaddrEq. reflexivity.
         }
         rewrite HgetUsedPaddrEq in HaddrIsInChild.
         assert(HgetPaddrEq: getAllPaddrAux [parentblock] s1 = getAllPaddrAux [parentblock] s0).
         {
           rewrite Hs1. apply getAllPaddrAuxEqBEStartEndNoChange with bentry;
                 try(assumption);
                 try(unfold CBlockEntry;
                     destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                     simpl; reflexivity).
         }
         rewrite HgetPaddrEq in HaddrIsInParentBlock.
         assert(HgetMappedEq: getMappedBlocks parent s1 = getMappedBlocks parent s0).
         {
           rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry;
                 try(assumption);
                 try(unfold CBlockEntry;
                     destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                     simpl; reflexivity).
         }
         rewrite HgetMappedEq in HparentBlockIsMappedInParent.
         assert(Hsh1ParentBlocks0: sh1entryAddr parentblock sh1entryaddr s0).
         {
           unfold sh1entryAddr in *. rewrite Hs1 in Hsh1ParentBlock. simpl in Hsh1ParentBlock.
           destruct (beqAddr blockInParentPartitionAddr parentblock) eqn:HbeqBlockParentBlock.
           - (* blockInParentPartitionAddr = parentblock *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlock. rewrite HbeqBlockParentBlock in *.
             rewrite HlookupBlocks0. assumption.
           - (* blockInParentPartitionAddr <> parentblock *)
             rewrite <-beqAddrFalse in HbeqBlockParentBlock.
             rewrite removeDupIdentity in Hsh1ParentBlock; intuition.
         }
         specialize(Hcons0 parent child addr parentblock sh1entryaddr HparentIsPart HchildIsChild HaddrIsInChild
                      HaddrIsInParentBlock HparentBlockIsMappedInParent Hsh1ParentBlocks0).
         destruct Hcons0 as [HPDchild | HPDflag].
         - left. unfold sh1entryPDchild in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (parentblock + sh1offset)))
                   eqn:HbeqBlockParentBlocksh1.
           { (* blockInParentPartitionAddr = CPaddr (parentblock + sh1offset) *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlocksh1. rewrite <-HbeqBlockParentBlocksh1 in *.
             rewrite HlookupBlocks0 in HPDchild. congruence.
           }
           (* blockInParentPartitionAddr <> CPaddr (parentblock + sh1offset) *)
           rewrite <-beqAddrFalse in HbeqBlockParentBlocksh1. rewrite removeDupIdentity; intuition.
         - right. unfold sh1entryPDflag in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (parentblock + sh1offset)))
                   eqn:HbeqBlockParentBlocksh1.
           { (* blockInParentPartitionAddr = CPaddr (parentblock + sh1offset) *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlocksh1. rewrite <-HbeqBlockParentBlocksh1 in *.
             rewrite HlookupBlocks0 in HPDflag. congruence.
           }
           (* blockInParentPartitionAddr <> CPaddr (parentblock + sh1offset) *)
           rewrite <-beqAddrFalse in HbeqBlockParentBlocksh1. rewrite removeDupIdentity; intuition.
         (* END sharedBlockPointsToChild *)
       }

       split.
       ++ (* consistency1 s *)
          (* Disjunction on the value of s *)
          destruct HpropsOr as [Hs1sEq | Hs].
          ** (* s = s1 *)
             rewrite Hs1sEq. assumption.
          ** (* s <> s1 *)
             destruct (beqAddr pdparent nullAddr) eqn:HbeqParentNull.
             {
               assert(HnullExists: nullAddrExists s1) by (unfold consistency1 in *; intuition).
               unfold nullAddrExists in HnullExists. unfold isPADDR in HnullExists.
               rewrite <-DTL.beqAddrTrue in HbeqParentNull. rewrite HbeqParentNull in *.
               rewrite HlookupParent in HnullExists. exfalso; congruence.
             }
             assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
             {
               rewrite Hs1. simpl. reflexivity.
             }
             rewrite HcurrPartEq in *.
             assert(HblockInMappedBlocksEqs: getMappedBlocks pdparent s = getMappedBlocks pdparent s1).
             {
               rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent. assumption.
               unfold consistency1 in *; intuition. simpl. reflexivity.
             }
             assert(HlowerThanMaxs: blockindex newBentry < kernelStructureEntriesNb) by (apply Hidx).
             assert(HblockIsNotFrees1: ~isFreeSlot blockInParentPartitionAddr s1).
             {
               unfold isFreeSlot. rewrite HlookupBlocks1.
               assert(HwellFormeds1: wellFormedFstShadowIfBlockEntry s1)
                     by (unfold consistency1 in *; intuition).
               unfold wellFormedFstShadowIfBlockEntry in HwellFormeds1.
               assert(HblockIsBE: isBE blockInParentPartitionAddr s1).
               { unfold isBE. rewrite HlookupBlocks1. trivial. }
               specialize(HwellFormeds1 blockInParentPartitionAddr HblockIsBE).
               unfold isSHE in HwellFormeds1.
               destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr);
                     try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               assert(HwellFormedCuts1: wellFormedShadowCutIfBlockEntry s1)
                     by (unfold consistency1 in *; intuition).
               unfold wellFormedShadowCutIfBlockEntry in HwellFormedCuts1.
               specialize(HwellFormedCuts1 blockInParentPartitionAddr HblockIsBE).
               destruct HwellFormedCuts1 as [scentryaddr (HwellFormedCuts1 & HsceValue)].
               subst scentryaddr. unfold isSCE in HwellFormedCuts1.
               destruct (lookup (CPaddr (blockInParentPartitionAddr + scoffset)) (memory s1) beqAddr);
                     try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               unfold bentryPFlag in HPFlag. rewrite HlookupBlocks1 in HPFlag.
               rewrite <-HPFlag. intuition.
             }
             assert(HgetFreeSlotsListEqs: forall pd, isPDT pd s1
                                                -> lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr
                                                  -> getFreeSlotsList pd s = getFreeSlotsList pd s1).
             {
               intros pd HisPDT HlookupPdEq. unfold isPDT in HisPDT. unfold getFreeSlotsList in *.
               rewrite HlookupPdEq in *.
               destruct (lookup pd (memory s1) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull.
               + (* firstfreeslot p = nullAddr *)
                 reflexivity.
               + (* firstfreeslot p <> nullAddr *)
                 assert(HbeqFirstFreeParent: firstfreeslot p <> pdparent).
                 {
                   assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s1)
                         by (unfold consistency1 in *; intuition).
                   unfold FirstFreeSlotPointerIsBEAndFreeSlot in HfirstFree.
                   rewrite <-beqAddrFalse in HbeqFirstFreeNull.
                   specialize(HfirstFree pd p HlookupPd HbeqFirstFreeNull).
                   destruct HfirstFree as [HfirstIsBE HfirstIsFree].
                   intro Hcontra. rewrite Hcontra in HfirstIsBE. unfold isBE in HfirstIsBE.
                   rewrite HlookupParent in HfirstIsBE. congruence.
                 }
                 rewrite Hs. apply getFreeSlotsListRecEqPDT; try(intuition; congruence).
                 * unfold isBE. rewrite HlookupParent. intro. trivial.
                 * unfold isPADDR. rewrite HlookupParent. intro. trivial.
             }

             assert(HnullExists: nullAddrExists s).
             { (* BEGIN nullAddrExists s *)
               assert(Hcons0: nullAddrExists s1) by (unfold consistency1 in *; intuition).
               unfold nullAddrExists in *. unfold isPADDR in *.
               rewrite Hs. simpl. rewrite HbeqParentNull.
               rewrite <-beqAddrFalse in HbeqParentNull. rewrite removeDupIdentity; intuition.
               (* END nullAddrExists *)
             }

             assert(HwellFormed: wellFormedFstShadowIfBlockEntry s).
             { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
               assert(Hcons0: wellFormedFstShadowIfBlockEntry s1) by (unfold consistency1 in *; intuition).
               unfold wellFormedFstShadowIfBlockEntry in *.
               intros pa HisBE.
               assert(HisBEs1: isBE pa s1).
               {
                 unfold isBE in HisBE. rewrite Hs in HisBE. simpl in HisBE.
                 destruct (beqAddr pdparent pa) eqn:HbeqParentPa; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentPa. rewrite removeDupIdentity in HisBE; intuition.
               }
               specialize(Hcons0 pa HisBEs1). unfold isSHE in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (CPaddr (pa + sh1offset))) eqn:HbeqParentSh1.
               { (* pdparent = CPaddr (pa + sh1offset) *)
                 rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqParentSh1. rewrite <-HbeqParentSh1 in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent = CPaddr (pa + sh1offset) *)
               rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity; intuition.
               (* END wellFormedFstShadowIfBlockEntry *)
             }

             assert(HPDTI: PDTIfPDFlag s).
             { (* BEGIN PDTIfPDFlag s *)
               assert(Hcons0: PDTIfPDFlag s1) by (unfold consistency1 in *; intuition).
               unfold PDTIfPDFlag in *. intros idPDchild sh1entryaddr Hsh1entry.
               assert(Hpropss1: (true = checkChild idPDchild s1 sh1entryaddr
                                /\ sh1entryAddr idPDchild sh1entryaddr s1)
                                /\ lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s1) beqAddr).
               {
                 unfold checkChild in *. unfold sh1entryAddr in *.
                 rewrite Hs in Hsh1entry. simpl in Hsh1entry. rewrite Hs. simpl.
                 destruct (beqAddr pdparent idPDchild) eqn:HbeqParentChild; try(exfalso; intuition; congruence).
                 rewrite <-beqAddrFalse in HbeqParentChild.
                 rewrite removeDupIdentity in Hsh1entry; try(apply not_eq_sym; assumption).
                 destruct (lookup idPDchild (memory s1) beqAddr) eqn:HlookupChilds1;
                         try(exfalso; intuition; congruence).
                 destruct v; try(exfalso; intuition; congruence).
                 destruct (beqAddr pdparent sh1entryaddr) eqn:HbeqParentSh1; try(exfalso; intuition; congruence).
                 rewrite <-beqAddrFalse in HbeqParentSh1.
                 rewrite removeDupIdentity in Hsh1entry; try(apply not_eq_sym; assumption). split. assumption.
                 rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
               }
               destruct Hpropss1 as [Hsh1entrys1 HlookupChildEq].
               specialize(Hcons0 idPDchild sh1entryaddr Hsh1entrys1).
               unfold bentryAFlag in *. unfold bentryPFlag in *. unfold bentryStartAddr in *.
               unfold entryPDT in *.
               rewrite HlookupChildEq. destruct Hcons0 as [Haccess (Hpresent & Hstartaddr)]. intuition.
               destruct Hstartaddr as [startaddr Hstartaddr]. exists startaddr.
               destruct (lookup idPDchild (memory s1) beqAddr) eqn:HlookupChilds1;
                        try(exfalso; intuition; congruence).
               destruct v; try(exfalso; intuition; congruence).
               destruct Hstartaddr as [HstartVal HlookupStart].
               split. assumption. rewrite Hs. simpl.
               destruct (beqAddr pdparent (startAddr (blockrange b))) eqn:HbeqParentStart.
               - (* pdparent = startAddr (blockrange b) *)
                 assumption.
               - (* pdparent <> startAddr (blockrange b) *)
                 rewrite <-beqAddrFalse in HbeqParentStart. rewrite removeDupIdentity; intuition.
               (* END PDTIfPDFlag *)
             }

             assert(Haccessible: AccessibleNoPDFlag s).
             { (* BEGIN AccessibleNoPDFlag s *)
               assert(Hcons0: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
               unfold AccessibleNoPDFlag in *.
               intros block sh1entryaddr HblockIsBE Hsh1IsSh1 HAFlagBlock.
               assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. destruct (beqAddr pdparent block) eqn:HbeqParentBlock.
                 {
                   (* pdparent = block *)
                   unfold isBE in HblockIsBE. rewrite Hs in HblockIsBE. simpl in HblockIsBE.
                   rewrite HbeqParentBlock in HblockIsBE. exfalso; congruence.
                 }
                 (* pdparent <> block *)
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
               }
               assert(HblockIsBEs1: isBE block s1).
               {
                 unfold isBE in *. rewrite HlookupBlockEq in HblockIsBE. assumption.
               }
               assert(Hsh1IsSh1s1: sh1entryAddr block sh1entryaddr s1).
               {
                 unfold sh1entryAddr in *. rewrite HlookupBlockEq in Hsh1IsSh1. assumption.
               }
               assert(HAFlags1: bentryAFlag block true s1).
               {
                 unfold bentryAFlag in *. rewrite HlookupBlockEq in HAFlagBlock. assumption.
               }
               specialize(Hcons0 block sh1entryaddr HblockIsBEs1 Hsh1IsSh1s1 HAFlags1).
               unfold sh1entryPDflag in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent sh1entryaddr) eqn:HbeqParentSh1.
               { (* pdparent = sh1entryaddr *)
                 rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqParentSh1. rewrite HbeqParentSh1 in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> sh1entryaddr *)
               rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity; intuition.
               (* END AccessibleNoPDFlag *)
             }

             assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
             { (* BEGIN multiplexerIsPDT s *)
               assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
               unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
               intros pdentryaddr pdentry HlookupPdaddr HfirstFreeNotNull.
               assert(HlookupPdaddrs1: exists pdentrys1, lookup pdentryaddr (memory s1) beqAddr
                                                          = Some (PDT pdentrys1)
                                                         /\ firstfreeslot pdentrys1 <> nullAddr
                                                         /\ firstfreeslot pdentrys1 = firstfreeslot pdentry).
               {
                 rewrite Hs in HlookupPdaddr. simpl in HlookupPdaddr.
                 destruct (beqAddr pdparent pdentryaddr) eqn:HbeqParentPdaddr.
                 - (* pdparent = pdentryaddr *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPdaddr. rewrite HbeqParentPdaddr in *.
                   rewrite HlookupParent. exists pdentryParent. split. reflexivity.
                   injection HlookupPdaddr as Hpdentry. rewrite <-Hpdentry in *.
                   simpl in HfirstFreeNotNull. split. assumption. simpl. reflexivity.
                 - (* pdparent <> pdentryaddr *)
                   rewrite <-beqAddrFalse in HbeqParentPdaddr. exists pdentry.
                   rewrite removeDupIdentity in HlookupPdaddr; intuition.
               }
               destruct HlookupPdaddrs1 as [pdentrys1 (HlookupPdaddrs1 & (HfirstFreeNotNulls1 & HfirstFreeEq))].
               specialize(Hcons0 pdentryaddr pdentrys1 HlookupPdaddrs1 HfirstFreeNotNulls1).
               rewrite HfirstFreeEq in *. destruct Hcons0 as [HfirstFreeIsBE HfirstFreeIsFree].
               unfold isBE in *. unfold isFreeSlot in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (firstfreeslot pdentry)) eqn:HbeqParentFirst.
               { (* pdparent = firstfreeslot pdentry *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFirst. rewrite HbeqParentFirst in *.
                 rewrite HlookupParent in HfirstFreeIsBE. exfalso; congruence.
               }
               (* pdparent <> firstfreeslot pdentry *)
               rewrite <-beqAddrFalse in HbeqParentFirst. rewrite removeDupIdentity; intuition.
               destruct (lookup (firstfreeslot pdentry) (memory s1) beqAddr) eqn:HlookupFirst; try(congruence).
               destruct v; try(congruence).
               destruct(beqAddr pdparent (CPaddr (firstfreeslot pdentry + sh1offset))) eqn:HbeqParentFirstSh1.
               { (* pdparent = CPaddr (firstfreeslot pdentry + sh1offset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFirstSh1. rewrite <-HbeqParentFirstSh1 in *.
                 rewrite HlookupParent in HfirstFreeIsFree. congruence.
               }
               (* pdparent <> CPaddr (firstfreeslot pdentry + sh1offset) *)
               rewrite <-beqAddrFalse in HbeqParentFirstSh1. rewrite removeDupIdentity; intuition.
               destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s1) beqAddr);
                      try(congruence).
               destruct v; try(congruence).
               destruct (beqAddr pdparent (CPaddr (firstfreeslot pdentry + scoffset))) eqn:HbeqParentFirstSce.
               { (* pdparent = CPaddr (firstfreeslot pdentry + scoffset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFirstSce. rewrite <-HbeqParentFirstSce in *.
                 rewrite HlookupParent in HfirstFreeIsFree. congruence.
               }
               (* pdparent <> CPaddr (firstfreeslot pdentry + scoffset) *)
               rewrite <-beqAddrFalse in HbeqParentFirstSce. rewrite removeDupIdentity; intuition.
               (* END multiplexerIsPDT *)
             }

             assert(multiplexerIsPDT s).
             { (* BEGIN multiplexerIsPDT s *)
               assert(Hcons0: multiplexerIsPDT s1) by (unfold consistency1 in *; intuition).
               unfold multiplexerIsPDT in *.
               unfold isPDT in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent multiplexer) eqn:HbeqParentMultip.
               - (* pdparent = multiplexer *)
                 trivial.
               - (* pdparent <> multiplexer *)
                 rewrite <-beqAddrFalse in HbeqParentMultip. rewrite removeDupIdentity; intuition.
               (* END multiplexerIsPDT *)
             }

             assert(HgetPartitionsEq: getPartitions multiplexer s = getPartitions multiplexer s1).
             {
               rewrite Hs. apply getPartitionsEqPDT with pdentryParent; try(unfold consistency1 in *; intuition).
             }

             assert(currentPartitionInPartitionsList s).
             { (* BEGIN currentPartitionInPartitionsList s *)
               assert(Hcons0: currentPartitionInPartitionsList s1) by (unfold consistency1 in *; intuition).
               unfold currentPartitionInPartitionsList in *.
               rewrite HgetPartitionsEq. rewrite Hs. simpl. assumption.
               (* END currentPartitionInPartitionsList *)
             }

             assert(wellFormedShadowCutIfBlockEntry s).
             { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
               assert(Hcons0: wellFormedShadowCutIfBlockEntry s1) by (unfold consistency1 in *; intuition).
               unfold wellFormedShadowCutIfBlockEntry in *. intros pa HpaIsBE.
               assert(HlookupPaEq: lookup pa (memory s) beqAddr = lookup pa (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. unfold isBE in HpaIsBE. rewrite Hs in HpaIsBE. simpl in HpaIsBE.
                 destruct (beqAddr pdparent pa) eqn:HbeqParentPa; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentPa. rewrite removeDupIdentity; intuition.
               }
               assert(HpaIsBEs1: isBE pa s1).
               {
                 unfold isBE in *. rewrite HlookupPaEq in HpaIsBE. assumption.
               }
               specialize(Hcons0 pa HpaIsBEs1). destruct Hcons0 as [scentryaddr (HsceIsSce & HsceVal)].
               exists scentryaddr. split. unfold isSCE in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent scentryaddr) eqn:HbeqParentSce.
               { (* pdparent = scentryaddr *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentSce. rewrite HbeqParentSce in *.
                 rewrite HlookupParent in HsceIsSce. congruence.
               }
               (* pdparent <> scentryaddr *)
               rewrite <-beqAddrFalse in HbeqParentSce. rewrite removeDupIdentity; intuition.
               assumption.
               (* END wellFormedShadowCutIfBlockEntry *)
             }

             assert(BlocksRangeFromKernelStartIsBE s).
             { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
               assert(Hcons0: BlocksRangeFromKernelStartIsBE s1) by (unfold consistency1 in *; intuition).
               unfold BlocksRangeFromKernelStartIsBE in *.
               intros kernelentryaddr blockidx HkernIsKS HidxIsValid.
               assert(HkernIsKSs1: isKS kernelentryaddr s1).
               {
                 unfold isKS in *. rewrite Hs in HkernIsKS. simpl in HkernIsKS.
                 destruct (beqAddr pdparent kernelentryaddr) eqn:HbeqParentKern; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentKern. rewrite removeDupIdentity in HkernIsKS; intuition.
               }
               specialize(Hcons0 kernelentryaddr blockidx HkernIsKSs1 HidxIsValid).
               unfold isBE in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (CPaddr (kernelentryaddr + blockidx))) eqn:HbeqParentKernIdx.
               { (* pdparent = CPaddr (kernelentryaddr + blockidx) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentKernIdx. rewrite <-HbeqParentKernIdx in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> CPaddr (kernelentryaddr + blockidx) *)
               rewrite <-beqAddrFalse in HbeqParentKernIdx. rewrite removeDupIdentity; intuition.
               (* END BlocksRangeFromKernelStartIsBE *)
             }

             assert(KernelStructureStartFromBlockEntryAddrIsKS s).
             { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
               assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s1)
                      by (unfold consistency1 in *; intuition).
               unfold KernelStructureStartFromBlockEntryAddrIsKS in *.
               intros blockentryaddr blockidx HblockIsBE HidxIsBlockIdx.
               assert(HlookupBlockEq: lookup blockentryaddr (memory s) beqAddr
                                      = lookup blockentryaddr (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. unfold isBE in HblockIsBE. rewrite Hs in HblockIsBE. simpl in HblockIsBE.
                 destruct (beqAddr pdparent blockentryaddr) eqn:HbeqParentBlock; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
               }
               assert(HblockIsBEs1: isBE blockentryaddr s1).
               {
                 unfold isBE in *. rewrite HlookupBlockEq in HblockIsBE. assumption.
               }
               assert(HidxIsBlockIdxs1: bentryBlockIndex blockentryaddr blockidx s1).
               {
                 unfold bentryBlockIndex in *. rewrite HlookupBlockEq in HidxIsBlockIdx. assumption.
               }
               specialize(Hcons0 blockentryaddr blockidx HblockIsBEs1 HidxIsBlockIdxs1).
               unfold isKS in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (CPaddr (blockentryaddr - blockidx))) eqn:HbeqParentBlockMinus.
               { (* pdparent = CPaddr (blockentryaddr - blockidx) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentBlockMinus. rewrite <-HbeqParentBlockMinus in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> CPaddr (blockentryaddr - blockidx) *)
               rewrite <-beqAddrFalse in HbeqParentBlockMinus. rewrite removeDupIdentity; intuition.
               (* END KernelStructureStartFromBlockEntryAddrIsKS *)
             }

             assert(sh1InChildLocationIsBE s).
             { (* BEGIN sh1InChildLocationIsBE s *)
               assert(Hcons0: sh1InChildLocationIsBE s1) by (unfold consistency1 in *; intuition).
               unfold sh1InChildLocationIsBE in *.
               intros sh1entryaddr sh1entry HlookupSh1 HinChild.
               assert(HlookupSh1s1: lookup sh1entryaddr (memory s1) beqAddr = Some (SHE sh1entry)).
               {
                 rewrite Hs in HlookupSh1. simpl in HlookupSh1.
                 destruct (beqAddr pdparent sh1entryaddr) eqn:HbeqParentSh1; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity in HlookupSh1; intuition.
               }
               specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1s1 HinChild).
               unfold isBE in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (inChildLocation sh1entry)) eqn:HbeqParentInChild.
               { (* pdparent = inChildLocation sh1entry *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentInChild. rewrite HbeqParentInChild in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> inChildLocation sh1entry *)
               rewrite <-beqAddrFalse in HbeqParentInChild. rewrite removeDupIdentity; intuition.
               (* END sh1InChildLocationIsBE *)
             }

             assert(StructurePointerIsKS s).
             { (* BEGIN StructurePointerIsKS s *)
               assert(Hcons0: StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               unfold StructurePointerIsKS in *.
               intros pd pdentry HlookupPd HstructureNotNull.
               assert(HlookupPds1: exists pdentrys1, lookup pd (memory s1) beqAddr = Some (PDT pdentrys1)
                                                     /\ structure pdentrys1 = structure pdentry).
               {
                 rewrite Hs in HlookupPd. simpl in HlookupPd.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   exists pdentryParent. rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   split. assumption. injection HlookupPd as Hpdentry. rewrite <-Hpdentry. simpl. reflexivity.
                 - (* pdparent <> pd *)
                   exists pdentry; rewrite <-beqAddrFalse in HbeqParentPd.
                   rewrite removeDupIdentity in HlookupPd; intuition.
               }
               destruct HlookupPds1 as [pdentrys1 (HlookupPds1 & HstructEq)].
               rewrite <-HstructEq in HstructureNotNull.
               specialize(Hcons0 pd pdentrys1 HlookupPds1 HstructureNotNull).
               rewrite HstructEq in Hcons0. unfold isKS in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (structure pdentry)) eqn:HbeqParentStruct.
               { (* pdparent = structure pdentry *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentStruct. rewrite <-HbeqParentStruct in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> structure pdentry *)
               rewrite <-beqAddrFalse in HbeqParentStruct. rewrite removeDupIdentity; intuition.
               (* END StructurePointerIsKS *)
             }

             assert(NextKSIsKS s).
             { (* BEGIN NextKSIsKS s *)
               assert(Hcons0: NextKSIsKS s1) by (unfold consistency1 in *; intuition).
               unfold NextKSIsKS in *. intros addr nextKSaddr nextKS HaddrIsKS HnextKS HnextEntry HnextKSnotNull.
               assert(HaddrIsKSs1: isKS addr s1).
               {
                 unfold isKS in *. rewrite Hs in HaddrIsKS. simpl in HaddrIsKS.
                 destruct (beqAddr pdparent addr) eqn:HbeqParentAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentAddr. rewrite removeDupIdentity in HaddrIsKS; intuition.
               }
               assert(HnextKSs1: nextKSAddr addr nextKSaddr s1).
               {
                 unfold nextKSAddr in *. rewrite Hs in HnextKS. simpl in HnextKS.
                 destruct (beqAddr pdparent addr) eqn:HbeqParentAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentAddr. rewrite removeDupIdentity in HnextKS; intuition.
               }
               assert(HnextEntrys1: nextKSentry nextKSaddr nextKS s1).
               {
                 unfold nextKSentry in *. rewrite Hs in HnextEntry. simpl in HnextEntry.
                 destruct (beqAddr pdparent nextKSaddr) eqn:HbeqParentNextAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentNextAddr.
                 rewrite removeDupIdentity in HnextEntry; intuition.
               }
               specialize(Hcons0 addr nextKSaddr nextKS HaddrIsKSs1 HnextKSs1 HnextEntrys1 HnextKSnotNull).
               unfold isKS in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent nextKS) eqn:HbeqParentNext; try(exfalso; congruence).
               { (* pdparent = nextKS *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentNext. rewrite HbeqParentNext in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> nextKS *)
               rewrite <-beqAddrFalse in HbeqParentNext. rewrite removeDupIdentity; intuition.
               (* END NextKSIsKS *)
             }

             assert(NextKSOffsetIsPADDR s).
             { (* BEGIN NextKSOffsetIsPADDR s *)
               assert(Hcons0: NextKSOffsetIsPADDR s1) by (unfold consistency1 in *; intuition).
               unfold NextKSOffsetIsPADDR in *. intros addr nextksaddr HaddrIsKS HnextKS.
               assert(HaddrIsKSs1: isKS addr s1).
               {
                 unfold isKS in *. rewrite Hs in HaddrIsKS. simpl in HaddrIsKS.
                 destruct (beqAddr pdparent addr) eqn:HbeqParentAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentAddr. rewrite removeDupIdentity in HaddrIsKS; intuition.
               }
               assert(HnextKSs1: nextKSAddr addr nextksaddr s1).
               {
                 unfold nextKSAddr in *. rewrite Hs in HnextKS. simpl in HnextKS.
                 destruct (beqAddr pdparent addr) eqn:HbeqParentAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentAddr. rewrite removeDupIdentity in HnextKS; intuition.
               }
               specialize(Hcons0 addr nextksaddr HaddrIsKSs1 HnextKSs1).
               destruct Hcons0 as [HnextIsPADDR HnextNotNull]. split. unfold isPADDR in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent nextksaddr) eqn:HbeqParentNext.
               { (* pdparent = nextksaddr *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentNext. rewrite HbeqParentNext in *.
                 rewrite HlookupParent in HnextIsPADDR. congruence.
               }
               (* pdparent <> nextksaddr *)
               rewrite <-beqAddrFalse in HbeqParentNext. rewrite removeDupIdentity; intuition. assumption.
               (* END NextKSOffsetIsPADDR *)
             }

             assert(HlookupParents: lookup pdparent (memory s) beqAddr
                        = Some (PDT
                                  ({|
                                    structure := structure pdentryParent;
                                    firstfreeslot := firstfreeslot pdentryParent;
                                    nbfreeslots := nbfreeslots pdentryParent;
                                    nbprepare := nbprepare pdentryParent;
                                    parent := parent pdentryParent;
                                    MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                                    vidtAddr := vidtAddr pdentryParent
                                  |}))).
             {
               rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity.
             }

             assert(HgetFreeSlotsParent: getFreeSlotsList pdparent s = getFreeSlotsList pdparent s1).
             {
               unfold getFreeSlotsList. rewrite HlookupParent. rewrite HlookupParents. simpl.
               destruct (beqAddr (firstfreeslot pdentryParent) nullAddr) eqn:HbeqFirstFreeNull; try(reflexivity).
               rewrite Hs. apply getFreeSlotsListRecEqPDT.
               + apply firstBlockPDNotEq with pdentryParent s1. assumption. unfold pdentryFirstFreeSlot.
                 rewrite HlookupParent. reflexivity. exists (firstfreeslot pdentryParent).
                 rewrite <-beqAddrFalse in HbeqFirstFreeNull. unfold pdentryFirstFreeSlot.
                 rewrite HlookupParent. split. reflexivity. assumption. assumption.
               + unfold isBE. rewrite HlookupParent. intuition.
               + unfold isPADDR. rewrite HlookupParent. intuition.
             }

             assert(NoDupInFreeSlotsList s).
             { (* BEGIN NoDupInFreeSlotsList s *)
               assert(Hcons0: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
               unfold NoDupInFreeSlotsList in *. intros pd pdentry HlookupPd.
               destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
               - (* pdparent = pd *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                 specialize(Hcons0 pd pdentryParent HlookupParent).
                 destruct Hcons0 as [optionFreeSlotsList (HgetFreeList & (HwellFormedList & HnoDupList))].
                 exists optionFreeSlotsList. split; try(split; assumption; assumption).
                 subst optionFreeSlotsList.
                 apply eq_sym. assumption.
               - (* pdparent <> pd *)
                 assert(HlookupPds1: lookup pd (memory s1) beqAddr = Some (PDT pdentry)).
                 {
                   rewrite Hs in HlookupPd. simpl in HlookupPd. rewrite HbeqParentPd in HlookupPd.
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in HlookupPd; intuition.
                 }
                 specialize(Hcons0 pd pdentry HlookupPds1).
                 destruct Hcons0 as [optionFreeSlotsList (HgetFreeList & (HwellFormedList & HnoDupList))].
                 exists optionFreeSlotsList. split; try(split; assumption; assumption).
                 subst optionFreeSlotsList.
                 assert(HlookupPdsEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
                 {
                   rewrite HlookupPds1. assumption.
                 }
                 apply eq_sym. apply HgetFreeSlotsListEqs.
                 unfold isPDT. rewrite HlookupPds1. trivial. assumption.
               (* END NoDupInFreeSlotsList *)
             }

             assert(freeSlotsListIsFreeSlot s).
             { (* BEGIN freeSlotsListIsFreeSlot s *)
               assert(Hcons0: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
               unfold freeSlotsListIsFreeSlot in *.
               intros pd freeslotaddr optionFreeSlotsList freeSlotsList HpdIsPDT HoptionList HfreeSlotsList
                      HfreeSlotNotNull.
               assert(HpdIsPDTs1: isPDT pd s1).
               {
                 unfold isPDT in *. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *. rewrite HlookupParent.
                   trivial.
                 - (* pdparent <> pd *)
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in HpdIsPDT; intuition.
               }
               assert(HoptionLists1: optionFreeSlotsList = getFreeSlotsList pd s1
                                     /\ wellFormedFreeSlotsList optionFreeSlotsList <> False).
               {
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite <-HgetFreeSlotsParent. assumption.
                 - (* pdparent <> pd *)
                   assert(HlookupPdEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
                   {
                     rewrite Hs. simpl. rewrite HbeqParentPd. rewrite <-beqAddrFalse in HbeqParentPd.
                     rewrite removeDupIdentity; intuition.
                   }
                   specialize(HgetFreeSlotsListEqs pd HpdIsPDTs1 HlookupPdEq).
                   rewrite <-HgetFreeSlotsListEqs. assumption.
               }
               specialize(Hcons0 pd freeslotaddr optionFreeSlotsList freeSlotsList HpdIsPDTs1 HoptionLists1
                          HfreeSlotsList HfreeSlotNotNull).
               unfold isFreeSlot in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent freeslotaddr) eqn:HbeqParentFree.
               { (* pdparent = freeslotaddr *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFree. rewrite HbeqParentFree in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> freeslotaddr *)
               rewrite <-beqAddrFalse in HbeqParentFree. rewrite removeDupIdentity; intuition.
               destruct (lookup freeslotaddr (memory s1) beqAddr); try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               destruct (beqAddr pdparent (CPaddr (freeslotaddr + sh1offset))) eqn:HbeqParentFreeSh1.
               { (* pdparent = CPaddr (freeslotaddr + sh1offset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFreeSh1. rewrite HbeqParentFreeSh1 in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> CPaddr (freeslotaddr + sh1offset) *)
               rewrite <-beqAddrFalse in HbeqParentFreeSh1. rewrite removeDupIdentity; intuition.
               destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s1) beqAddr); try(congruence).
               destruct v; try(congruence).
               destruct (beqAddr pdparent (CPaddr (freeslotaddr + scoffset))) eqn:HbeqParentFreeSce.
               { (* pdparent = CPaddr (freeslotaddr + scoffset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFreeSce. rewrite <-HbeqParentFreeSce in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> CPaddr (freeslotaddr + scoffset) *)
               rewrite <-beqAddrFalse in HbeqParentFreeSce. rewrite removeDupIdentity; intuition.
               (* END freeSlotsListIsFreeSlot *)
             }

             assert(DisjointFreeSlotsLists s).
             { (* BEGIN DisjointFreeSlotsLists s *)
               assert(Hcons0: DisjointFreeSlotsLists s1) by (unfold consistency1 in *; intuition).
               unfold DisjointFreeSlotsLists in *. intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT Hpd1pd2Diff.
               assert(Hpd1IsPDTs1: isPDT pd1 s1).
               {
                 unfold isPDT in *. rewrite Hs in Hpd1IsPDT. simpl in Hpd1IsPDT.
                 destruct (beqAddr pdparent pd1) eqn:HbeqParentPd1.
                 - (* pdparent = pd1 *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd1. rewrite HbeqParentPd1 in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent <> pd1 *)
                   rewrite <-beqAddrFalse in HbeqParentPd1. rewrite removeDupIdentity in Hpd1IsPDT; intuition.
               }
               assert(Hpd2IsPDTs1: isPDT pd2 s1).
               {
                 unfold isPDT in *. rewrite Hs in Hpd2IsPDT. simpl in Hpd2IsPDT.
                 destruct (beqAddr pdparent pd2) eqn:HbeqParentPd2.
                 - (* pdparent = pd2 *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd2. rewrite HbeqParentPd2 in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent <> pd2 *)
                   rewrite <-beqAddrFalse in HbeqParentPd2. rewrite removeDupIdentity in Hpd2IsPDT; intuition.
               }
               specialize(Hcons0 pd1 pd2 Hpd1IsPDTs1 Hpd2IsPDTs1 Hpd1pd2Diff).
               destruct Hcons0 as [optionFreeSlotsList1 (optionFreeSlotsList2 & (Hlist1 & (HwellFormedList1 &
                                  (Hlist2 & (HwellFormedList2 & Hdisjoint)))))].
               exists optionFreeSlotsList1. exists optionFreeSlotsList2. subst optionFreeSlotsList1.
               subst optionFreeSlotsList2. split. destruct (beqAddr pdparent pd1) eqn:HbeqParentPd1.
               { (* pdparent = pd1 *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd1. rewrite HbeqParentPd1 in *.
                 rewrite <-HgetFreeSlotsParent. reflexivity.
               }
               (* pdparent <> pd1 *)
               assert(HlookupPd1Eq: lookup pd1 (memory s) beqAddr = lookup pd1 (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. rewrite HbeqParentPd1. rewrite <-beqAddrFalse in HbeqParentPd1.
                 rewrite removeDupIdentity; intuition.
               }
               specialize(HgetFreeSlotsListEqs pd1 Hpd1IsPDTs1 HlookupPd1Eq).
               rewrite <-HgetFreeSlotsListEqs. reflexivity. split. assumption. split.
               destruct (beqAddr pdparent pd2) eqn:HbeqParentPd2.
               { (* pdparent = pd2 *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd2. rewrite HbeqParentPd2 in *.
                 rewrite <-HgetFreeSlotsParent. reflexivity.
               }
               (* pdparent <> pd2 *)
               assert(HlookupPd2Eq: lookup pd2 (memory s) beqAddr = lookup pd2 (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. rewrite HbeqParentPd2. rewrite <-beqAddrFalse in HbeqParentPd2.
                 rewrite removeDupIdentity; intuition.
               }
               specialize(HgetFreeSlotsListEqs pd2 Hpd2IsPDTs1 HlookupPd2Eq).
               rewrite <-HgetFreeSlotsListEqs. reflexivity. split. assumption. assumption.
               (* END DisjointFreeSlotsLists *)
             }

             assert(HgetKSEq: forall pd, getKSEntries pd s = getKSEntries pd s1).
             {
               intro pd. assert(StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               rewrite Hs. apply getKSEntriesEqPDT with pdentryParent; try(assumption). simpl. reflexivity.
             }

             assert(inclFreeSlotsBlockEntries s).
             { (* BEGIN inclFreeSlotsBlockEntries s *)
               assert(Hcons0: inclFreeSlotsBlockEntries s1) by (unfold consistency1 in *; intuition).
               unfold inclFreeSlotsBlockEntries in *. intros pd HpdIsPDT.
               assert(HpdIsPDTs1: isPDT pd s1).
               {
                 unfold isPDT in *. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent <> pd *)
                   rewrite <-DTL.beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in HpdIsPDT; intuition.
               }
               specialize(Hcons0 pd HpdIsPDTs1).
               destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
               - (* pdparent = pd *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                 rewrite HgetFreeSlotsParent. rewrite HgetKSEq. assumption.
               - (* pdparent = pd *)
                 assert(HlookupPdEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
                 {
                   rewrite Hs. simpl. rewrite HbeqParentPd. rewrite <-beqAddrFalse in HbeqParentPd.
                   rewrite removeDupIdentity; intuition.
                 }
                 specialize(HgetFreeSlotsListEqs pd HpdIsPDTs1 HlookupPdEq).
                 rewrite HgetFreeSlotsListEqs. rewrite HgetKSEq. assumption.
               (* END inclFreeSlotsBlockEntries *)
             }

             assert(DisjointKSEntries s).
             { (* BEGIN DisjointKSEntries s *)
               assert(Hcons0: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
               unfold DisjointKSEntries in *. intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT Hpd1pd2NotEq.
               assert(Hpd1IsPDTs1: isPDT pd1 s1).
               {
                 unfold isPDT in *. rewrite Hs in Hpd1IsPDT. simpl in Hpd1IsPDT.
                 destruct (beqAddr pdparent pd1) eqn:HbeqParentPd.
                 - (* pdparent = pd1 *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent = pd1 *)
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in Hpd1IsPDT; intuition.
               }
               assert(Hpd2IsPDTs1: isPDT pd2 s1).
               {
                 unfold isPDT in *. rewrite Hs in Hpd2IsPDT. simpl in Hpd2IsPDT.
                 destruct (beqAddr pdparent pd2) eqn:HbeqParentPd.
                 - (* pdparent = pd2 *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent = pd2 *)
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in Hpd2IsPDT; intuition.
               }
               specialize(Hcons0 pd1 pd2 Hpd1IsPDTs1 Hpd2IsPDTs1 Hpd1pd2NotEq).
               destruct Hcons0 as [optionEntriesList1 (optionEntriesList2 & (Hlist1 & (Hlist2 & Hdisjoint)))].
               exists optionEntriesList1. exists optionEntriesList2.
               subst optionEntriesList1. subst optionEntriesList2. split. apply eq_sym. apply HgetKSEq.
               split. apply eq_sym. apply HgetKSEq. assumption.
               (* END DisjointKSEntries *)
             }

             assert(noDupPartitionTree s).
             { (* BEGIN noDupPartitionTree s *)
               assert(Hcons0: noDupPartitionTree s1) by (unfold consistency1 in *; intuition).
               unfold noDupPartitionTree in *. rewrite HgetPartitionsEq. assumption.
               (* END noDupPartitionTree *)
             }

             assert(HgetChildrenEq: forall pd, getChildren pd s = getChildren pd s1).
             {
               intro pd. assert(StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               rewrite Hs. apply getChildrenEqPDT with pdentryParent; try(assumption). simpl. reflexivity.
             }

             assert(HpdentryParentEq: forall pd parent, StateLib.pdentryParent pd parent s
                                                        = StateLib.pdentryParent pd parent s1).
             {
               intros pd parent. unfold StateLib.pdentryParent. rewrite Hs. simpl.
               destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
               - (* pdparent = pd *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                 rewrite HlookupParent. simpl. reflexivity.
               - (* pdparent = pd *)
                 rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity; intuition.
             }

             assert(isParent s).
             { (* BEGIN isParent s *)
               assert(Hcons0: isParent s1) by (unfold consistency1 in *; intuition).
               unfold isParent in *. intros partition parent HparentIsPart HpartIsChild.
               rewrite HgetPartitionsEq in HparentIsPart. rewrite HgetChildrenEq in HpartIsChild.
               specialize(Hcons0 partition parent HparentIsPart HpartIsChild). rewrite HpdentryParentEq.
               assumption.
               (* END isParent *)
             }

             assert(isChild s).
             { (* BEGIN isChild s *)
               assert(Hcons0: isChild s1) by (unfold consistency1 in *; intuition).
               unfold isChild in *. intros partition parent HpartIsPart HparentIsParent.
               rewrite HgetPartitionsEq in HpartIsPart. rewrite HpdentryParentEq in HparentIsParent.
               specialize(Hcons0 partition parent HpartIsPart HparentIsParent).
               rewrite HgetChildrenEq. assumption.
               (* END isChild *)
             }

             assert(noDupKSEntriesList s).
             { (* BEGIN noDupKSEntriesList s *)
               assert(Hcons0: noDupKSEntriesList s1) by (unfold consistency1 in *; intuition).
               unfold noDupKSEntriesList in *. intros partition HpartIsPDT.
               assert(HpartIsPDTs1: isPDT partition s1).
               {
                 unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
                 destruct (beqAddr pdparent partition) eqn:HbeqParentPart.
                 - (* pdparent = partition *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent = partition *)
                   rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
               }
               specialize(Hcons0 partition HpartIsPDTs1). rewrite HgetKSEq. assumption.
               (* END noDupKSEntriesList *)
             }

             assert(HmappedBlocksEq: forall pd, getMappedBlocks pd s = getMappedBlocks pd s1).
             {
               intro pd. assert(StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent; try(assumption). simpl. reflexivity.
             }

             assert(noDupMappedBlocksList s).
             { (* BEGIN noDupMappedBlocksList s *)
               assert(Hcons0: noDupMappedBlocksList s1) by (unfold consistency1 in *; intuition).
               unfold noDupMappedBlocksList in *. intros partition HpartIsPDT.
               assert(HpartIsPDTs1: isPDT partition s1).
               {
                 unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
                 destruct (beqAddr pdparent partition) eqn:HbeqParentPart.
                 - (* pdparent = partition *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent = partition *)
                   rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
               }
               specialize(Hcons0 partition HpartIsPDTs1). rewrite HmappedBlocksEq. assumption.
               (* END noDupMappedBlocksList *)
             }

             assert(wellFormedBlock s).
             { (* BEGIN wellFormedBlock s *)
               assert(Hcons0: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
               unfold wellFormedBlock in *. intros block startaddr endaddr HPFlagBlock Hstart Hend.
               assert(HPFlags1: bentryPFlag block true s1).
               {
                 unfold bentryPFlag in *. rewrite Hs in HPFlagBlock; simpl in HPFlagBlock.
                 destruct (beqAddr pdparent block) eqn:HbeqParentBlock; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in HPFlagBlock; intuition.
               }
               assert(Hstarts1: bentryStartAddr block startaddr s1).
               {
                 unfold bentryStartAddr in *. rewrite Hs in Hstart. simpl in Hstart.
                 destruct (beqAddr pdparent block) eqn:HbeqParentBlock; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in Hstart; intuition.
               }
               assert(Hends1: bentryEndAddr block endaddr s1).
               {
                 unfold bentryEndAddr in *. rewrite Hs in Hend. simpl in Hend.
                 destruct (beqAddr pdparent block) eqn:HbeqParentBlock; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in Hend; intuition.
               }
               specialize(Hcons0 block startaddr endaddr HPFlags1 Hstarts1 Hends1). assumption.
               (* END wellFormedBlock *)
             }

             assert(HaccessMappedBlocksEq: forall pd, getAccessibleMappedBlocks pd s
                                                       = getAccessibleMappedBlocks pd s1).
             {
               intro pd. assert(StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               rewrite Hs. apply getAccessibleMappedBlocksEqPDT with pdentryParent; try(assumption). simpl.
               reflexivity.
             }

             assert(MPUFromAccessibleBlocks s).
             { (* BEGIN MPUFromAccessibleBlocks s *)
               assert(Hcons0: MPUFromAccessibleBlocks s1) by (unfold consistency1 in *; intuition).
               unfold MPUFromAccessibleBlocks in *.
               intros partition block blocksInMPU HpartMPU HblockInMPU HblockNotNull.
               destruct (beqAddr pdparent partition) eqn:HbeqParentPart.
               - (* pdparent = partition *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
                 assert(HpartMPUs1: pdentryMPU partition realMPU s1 /\ In block realMPU).
                 {
                   unfold pdentryMPU in *. rewrite Hs in HpartMPU. simpl in HpartMPU.
                   rewrite beqAddrTrue in HpartMPU.
                   simpl  in HpartMPU. rewrite HlookupParent in *. simpl. simpl in HMPU. split. assumption.
                   subst blocksInMPU. apply removeBlockFromPhysicalMPUAuxIncl with blockInParentPartitionAddr.
                   assumption.
                 }
                 destruct HpartMPUs1 as [HpartMPUs1 HblockInMPUs1].
                 specialize(Hcons0 partition block realMPU HpartMPUs1 HblockInMPUs1 HblockNotNull).
                 rewrite HaccessMappedBlocksEq. assumption.
               - (* pdparent <> partition *)
                 assert(HpartMPUs1: pdentryMPU partition blocksInMPU s1).
                 {
                   unfold pdentryMPU in *. rewrite Hs in HpartMPU. simpl in HpartMPU.
                   rewrite HbeqParentPart in HpartMPU.
                   rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HpartMPU; intuition.
                 }
                 specialize(Hcons0 partition block blocksInMPU HpartMPUs1 HblockInMPU HblockNotNull).
                 rewrite HaccessMappedBlocksEq. assumption.
               (* END MPUFromAccessibleBlocks *)
             }

             assert(parentOfPartitionIsPartition s).
             { (* BEGIN parentOfPartitionIsPartition s *)
               assert(Hcons0: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
               unfold parentOfPartitionIsPartition in *. intros partition pdentry HlookupPart.
               assert(HlookupParts1: exists pdentrys1,
                                         lookup partition (memory s1) beqAddr = Some (PDT pdentrys1)
                                         /\ parent pdentrys1 = parent pdentry).
               {
                 rewrite Hs in HlookupPart. simpl in HlookupPart.
                 destruct (beqAddr pdparent partition) eqn:HbeqParentPart.
                 - (* pdparent = partition *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
                   exists pdentryParent. split. assumption. injection HlookupPart as Hpdentry. rewrite <-Hpdentry.
                   simpl. reflexivity.
                 - (* pdparent <> partition *)
                   rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HlookupPart; intuition.
                   exists pdentry. split. assumption. reflexivity.
               }
               destruct HlookupParts1 as [pdentrys1 (HlookupParts1 & HparentPartEq)].
               specialize(Hcons0 partition pdentrys1 HlookupParts1).
               destruct Hcons0 as [HparentOfPart (HparentOfRoot & HparentPartNotEq)].
               split.
               - intro HpartNotRoot. specialize(HparentOfPart HpartNotRoot). rewrite Hs. simpl.
                 destruct (beqAddr pdparent (parent pdentry)) eqn:HbeqParentEntryParent.
                 + (* pdparent = parent pdentry *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentEntryParent. rewrite HbeqParentEntryParent in *.
                   exists ({|
                             structure := structure pdentryParent;
                             firstfreeslot := firstfreeslot pdentryParent;
                             nbfreeslots := nbfreeslots pdentryParent;
                             nbprepare := nbprepare pdentryParent;
                             parent := parent pdentryParent;
                             MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                             vidtAddr := vidtAddr pdentryParent
                           |}). reflexivity.
                 + (* pdparent <> parent pdentry *)
                   rewrite <-beqAddrFalse in HbeqParentEntryParent. rewrite removeDupIdentity; intuition.
                   rewrite HparentPartEq in *. assumption.
               - split. intro HpartIsRoot. specialize(HparentOfRoot HpartIsRoot). rewrite HparentPartEq in *.
                 assumption. rewrite <-HparentPartEq. assumption.
               (* END parentOfPartitionIsPartition *)
             }

             assert(NbFreeSlotsISNbFreeSlotsInList s).
             { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
               assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s1) by (unfold consistency1 in *; intuition).
               unfold NbFreeSlotsISNbFreeSlotsInList in *. intros pd nbfreeslots HpdIsPDT Hnbfreeslots.
               assert(HpdIsPDTs1: isPDT pd s1).
               {
                 unfold isPDT in *. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent = pd *)
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in HpdIsPDT; intuition.
               }
               assert(Hnbfreeslotss1: pdentryNbFreeSlots pd nbfreeslots s1).
               {
                 unfold pdentryNbFreeSlots in *. rewrite Hs in Hnbfreeslots. simpl in Hnbfreeslots.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite HlookupParent. rewrite Hnbfreeslots. simpl. reflexivity.
                 - (* pdparent = pd *)
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in Hnbfreeslots; intuition.
               }
               specialize(Hcons0 pd nbfreeslots HpdIsPDTs1 Hnbfreeslotss1).
               destruct Hcons0 as [optionFreeSlotsList (Hlist & (HwellFormedList & HnbfreeslotsList))].
               exists optionFreeSlotsList. destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
               - (* pdparent = pd *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                 rewrite HgetFreeSlotsParent. intuition.
               - (* pdparent = pd *)
                 assert(HlookupEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
                 {
                   rewrite Hs. simpl. rewrite HbeqParentPd. rewrite <-beqAddrFalse in HbeqParentPd.
                   rewrite removeDupIdentity; intuition.
                 }
                 specialize(HgetFreeSlotsListEqs pd HpdIsPDTs1 HlookupEq). rewrite HgetFreeSlotsListEqs.
                 intuition.
               (* END NbFreeSlotsISNbFreeSlotsInList *)
             }

             assert(maxNbPrepareIsMaxNbKernels s).
             { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
               assert(Hcons0: maxNbPrepareIsMaxNbKernels s1) by (unfold consistency1 in Hconss1; intuition).
               unfold maxNbPrepareIsMaxNbKernels in *.
               intros partition kernList HisLisOfKern.
               assert(HisLisOfKerns1: isListOfKernels kernList partition s1).
               {
                 apply isListOfKernelsEqPDT with pdparent
                                                 {|
                                                   structure := structure pdentryParent;
                                                   firstfreeslot := firstfreeslot pdentryParent;
                                                   nbfreeslots := nbfreeslots pdentryParent;
                                                   nbprepare := nbprepare pdentryParent;
                                                   parent := parent pdentryParent;
                                                   MPU := MAL.removeBlockFromPhysicalMPUAux
                                                               blockInParentPartitionAddr realMPU;
                                                   vidtAddr := vidtAddr pdentryParent
                                                 |} pdentryParent; simpl; intuition; congruence.
               }
               specialize(Hcons0 partition kernList HisLisOfKerns1). assumption.
               (* END maxNbPrepareIsMaxNbKernels *)
             }

             unfold consistency1. intuition.
       ++ split.
          { (* noDupUsedPaddrList s *)
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            unfold noDupUsedPaddrList in *. intros partition HpartIsPSTs.
            assert(HpartIsPSTs1: isPDT partition s1).
            {
              unfold isPDT in *. rewrite Hs in HpartIsPSTs. simpl in HpartIsPSTs.
              destruct (beqAddr pdparent partition) eqn:HbeqParentPart.
              - (* pdparent = partition *)
                rewrite <-DTL.beqAddrTrue in HbeqParentPart. subst partition. rewrite HlookupParent. trivial.
              - (* pdparent <> partition *)
                rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HpartIsPSTs; intuition.
            }
            specialize(HnoDups1 partition HpartIsPSTs1).
            assert(HgetUsedEq: getUsedPaddr partition s = getUsedPaddr partition s1).
            {
              assert(HgetMappedEq: getMappedPaddr partition s = getMappedPaddr partition s1).
              {
                rewrite Hs. apply getMappedPaddrEqPDT with pdentryParent; simpl; intuition.
                unfold consistency1 in Hconss1; intuition.
              }
              assert(HgetConfigEq: getConfigPaddr partition s = getConfigPaddr partition s1).
              {
                rewrite Hs. apply getConfigPaddrEqPDT with pdentryParent; simpl; intuition.
              }
              unfold getUsedPaddr. rewrite HgetConfigEq. rewrite HgetMappedEq. reflexivity.
            }
            rewrite HgetUsedEq. assumption.
          }
          split.
          { (* sharedBlockPointsToChild s *)
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            unfold sharedBlockPointsToChild in *.
            intros parent child addr parentblock sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
                  HaddrInParentBlock HparentBlockMappedParent Hsh1.
            assert(HgetPartEq: getPartitions multiplexer s = getPartitions multiplexer s1).
            {
              rewrite Hs.
              unfold consistency1 in Hconss1; apply getPartitionsEqPDT with pdentryParent; simpl; intuition.
            }
            assert(HgetChildrenEq: getChildren parent s = getChildren parent s1).
            {
              rewrite Hs.
              unfold consistency1 in Hconss1; apply getChildrenEqPDT with pdentryParent; simpl; intuition.
            }
            rewrite HgetPartEq in HparentIsPart. rewrite HgetChildrenEq in HchildIsChild.
            assert(HgetUsedEq: getUsedPaddr child s = getUsedPaddr child s1).
            {
              assert(HgetMappedEq: getMappedPaddr child s = getMappedPaddr child s1).
              {
                rewrite Hs. apply getMappedPaddrEqPDT with pdentryParent; simpl; intuition.
                unfold consistency1 in Hconss1; intuition.
              }
              assert(HgetConfigEq: getConfigPaddr child s = getConfigPaddr child s1).
              {
                rewrite Hs. apply getConfigPaddrEqPDT with pdentryParent; simpl; intuition.
                unfold consistency1 in Hconss1; apply childrenArePDT with parent; intuition.
              }
              unfold getUsedPaddr. rewrite HgetConfigEq. rewrite HgetMappedEq. reflexivity.
            }
            assert(HgetAllPaddrEq: getAllPaddrAux [parentblock] s = getAllPaddrAux [parentblock] s1).
            {
              rewrite Hs. apply getAllPaddrAuxEqPDT.
              unfold consistency1 in Hconss1; apply partitionsArePDT ; intuition.
              admit. (*TODO we know that pdparent is PDT, that should suffice, right?*)
            }
            rewrite HgetUsedEq in HaddrUsedChild. rewrite HgetAllPaddrEq in HaddrInParentBlock.
            assert(HgetMappedEq: getMappedBlocks parent s = getMappedBlocks parent s1).
            {
              rewrite Hs.
              unfold consistency1 in Hconss1; apply getMappedBlocksEqPDT with pdentryParent; intuition.
            }
            assert(Hsh1s1: sh1entryAddr parentblock sh1entryaddr s1).
            {
              rewrite Hs in Hsh1. unfold sh1entryAddr in *. simpl in Hsh1.
              destruct (beqAddr pdparent parentblock) eqn:HbeqParentParentBlock; try(exfalso; congruence).
              rewrite <-beqAddrFalse in HbeqParentParentBlock. rewrite removeDupIdentity in Hsh1; intuition.
            }
            rewrite HgetMappedEq in HparentBlockMappedParent.
            specialize(Hshareds1 parent child addr parentblock sh1entryaddr HparentIsPart HchildIsChild
                  HaddrUsedChild HaddrInParentBlock HparentBlockMappedParent Hsh1s1).
            destruct Hshareds1 as [HPDchild | HPDflag].
            - left. unfold sh1entryPDchild in *. rewrite Hs. simpl.
              destruct (beqAddr pdparent (CPaddr (parentblock + sh1offset))) eqn:HbeqParentSh1.
              {
                rewrite <-DTL.beqAddrTrue in HbeqParentSh1. rewrite HbeqParentSh1 in *.
                rewrite HlookupParent in HPDchild; congruence.
              }
              rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity; intuition.
            - right. unfold sh1entryPDflag in *. rewrite Hs. simpl.
              destruct (beqAddr pdparent (CPaddr (parentblock + sh1offset))) eqn:HbeqParentSh1.
              {
                rewrite <-DTL.beqAddrTrue in HbeqParentSh1. rewrite HbeqParentSh1 in *.
                rewrite HlookupParent in HPDflag; congruence.
              }
              rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity; intuition.
          }
          exists sInit. split.
          instantiate(1:= fun sIn => P sIn). simpl. assumption.
          split. assumption. split.
          destruct HpropsOr as [Hss1Eq | Hs].
          {
            subst s. exists pdentryParent. assumption.
          }
          {
            rewrite Hs. exists {|
                                  structure := structure pdentryParent;
                                  firstfreeslot := firstfreeslot pdentryParent;
                                  nbfreeslots := nbfreeslots pdentryParent;
                                  nbprepare := nbprepare pdentryParent;
                                  parent := parent pdentryParent;
                                  MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                                  vidtAddr := vidtAddr pdentryParent
                                |}. simpl. rewrite beqAddrTrue. reflexivity.
          }
          split; try(unfold consistency in *; unfold consistency2 in *; intuition; congruence).
          destruct HpropsOr as [Hss1Eq | Hs].
          ** (* s = s1 *)
             subst s.
             destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                                           HAFlagBlockAddr & HblockAddrMappedParent & HstartBlockAddr &
                                           HpartialAccess))].
             exists blockaddr. exists bentryBlockAddr. intuition. right.
             intros parent child addr HnotEdgeCase HparentIsPart HchildIsChild HaddrAccMappedParent
                    HaddrMappedChild.
             apply HpartialAccess with parent; intuition. right. rewrite HlookupBlockAddr in H.
             rewrite app_nil_r in H. assumption.
          ** (* s <> s1 *)
             destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                                           HAFlagBlockAddr & HblockAddrMappedParent & HstartBlockAddr &
                                           HpartialAccess))].
             exists blockaddr. exists bentryBlockAddr.
             assert(HlookupBlockAddrs: lookup blockaddr (memory s) beqAddr = Some (BE bentryBlockAddr)).
             {
               rewrite Hs. simpl.
               destruct (beqAddr pdparent blockaddr) eqn:HbeqParentBlock.
               {
                 rewrite <-DTL.beqAddrTrue in HbeqParentBlock. rewrite HbeqParentBlock in *.
                 rewrite HlookupParent in HlookupBlockAddr. exfalso; congruence.
               }
               rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
             }
             split. assumption. split. unfold bentryPFlag in *. rewrite HlookupBlockAddrs.
             rewrite HlookupBlockAddr in HPFlagBlockAddr. assumption. split. unfold bentryAFlag in *.
             rewrite HlookupBlockAddrs. rewrite HlookupBlockAddr in HAFlagBlockAddr. assumption.
             assert(HblockInMappedBlocksEqs: getMappedBlocks pdparent s = getMappedBlocks pdparent s1).
             {
               rewrite Hs. unfold consistency1 in Hconss1; apply getMappedBlocksEqPDT with pdentryParent;
                  intuition.
             }
             rewrite HblockInMappedBlocksEqs. split. assumption. split. unfold bentryStartAddr in *.
             rewrite HlookupBlockAddrs. rewrite HlookupBlockAddr in HstartBlockAddr. assumption. right.
             intros parent child addr HnotEdgeCase HparentIsPart HchildIsChild HaddrAccMappedParent
                   HaddrMappedChild. rewrite HlookupBlockAddrs in HnotEdgeCase.
             rewrite app_nil_r in HnotEdgeCase.
             assert(HgetPartEq: getPartitions multiplexer s = getPartitions multiplexer s1).
             {
               rewrite Hs. unfold consistency1 in Hconss1; apply getPartitionsEqPDT with pdentryParent;
                  intuition.
             }
             assert(HgetChildrenEq: getChildren parent s = getChildren parent s1).
             {
               rewrite Hs. unfold consistency1 in Hconss1; apply getChildrenEqPDT with pdentryParent;
                  intuition.
             }
             assert(HgetAccMappedEq: getAccessibleMappedPaddr parent s = getAccessibleMappedPaddr parent s1).
             {
               rewrite Hs.
               unfold consistency1 in Hconss1; apply getAccessibleMappedPaddrEqPDT with pdentryParent;
                  intuition.
             }
             assert(HgetMappedEq: getMappedPaddr child s = getMappedPaddr child s1).
             {
               rewrite Hs. unfold consistency1 in Hconss1; apply getMappedPaddrEqPDT with pdentryParent;
                  intuition.
             }
             rewrite HgetPartEq in HparentIsPart. rewrite HgetChildrenEq in HchildIsChild.
             rewrite HgetAccMappedEq in HaddrAccMappedParent. rewrite HgetMappedEq in HaddrMappedChild.
             specialize(HpartialAccess parent child addr HnotEdgeCase HparentIsPart HchildIsChild
                   HaddrAccMappedParent HaddrMappedChild).
             assert(HgetAccMappedEqChild: getAccessibleMappedPaddr child s = getAccessibleMappedPaddr child s1).
             {
               rewrite Hs.
               unfold consistency1 in Hconss1; apply getAccessibleMappedPaddrEqPDT with pdentryParent;
                  intuition.
             }
             rewrite HgetAccMappedEqChild. assumption.
    -- simpl. intros s writeSucc Hprops. assumption.
Admitted.

(*Lemma writeAccessibleRec (pdbasepartition entryaddr : paddr) (flag : bool)
                          (P : state -> Prop):
{{fun s => consistency1 s
           /\ noDupUsedPaddrList s
           /\ sharedBlockPointsToChild s
           /\ (forall parent child addr, child <> pdbasepartition
                                         -> In parent (getPartitions multiplexer s)
                                         -> In child (getChildren parent s)
                                         -> In addr (getAccessibleMappedPaddr child s)
                                         -> In addr (getAccessibleMappedPaddr parent s))
           /\ (exists s0, exists statesList parentsList, (*TODO verify that*)
                  P s0
                  /\ consistency s0
                  /\ isParentsList s0 parentsList pdbasepartition
                  (*/\ s = last statesList s0*)
                  /\ (exists entry blockaddr bentry,
                          lookup pdbasepartition (memory s) beqAddr = Some (PDT entry)
                          /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT entry)
                          /\ lookup blockaddr s.(memory) beqAddr = Some (BE bentry)
                          /\ bentryPFlag blockaddr true s
                          /\ bentryAFlag blockaddr flag s
                          /\ In blockaddr (getMappedBlocks pdbasepartition s)
                          /\ bentryStartAddr blockaddr entryaddr s) (*maybe only if s <> s0*)
                  /\ bentryAFlag entryaddr true s0
                  /\ isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition flag
                  /\ accessibleChildPaddrIsAccessibleIntoParent s0
                  (*/\ ((forall child childEntry, parent childEntry = pdbasepartition
                                    -> lookup child (memory s) beqAddr = Some (PDT childEntry)
                                    -> exists blockaddr entry blockstart,
                                          lookup blockaddr s.(memory) beqAddr = Some (BE entry)
					                                /\ bentryPFlag blockaddr true s
					                                /\ bentryAFlag blockaddr flag s
					                                /\ In blockaddr (getMappedBlocks child s)
                                          /\ bentryStartAddr blockaddr blockstart s
                                          /\ beqAddr blockstart entryaddr = true)))*))
}}
writeAccessibleRec pdbasepartition entryaddr flag
{{fun writeSucceded s =>
      exists parentsList statesList s0 pdentryBase,
        (* Common properties *)
        isParentsList s0 parentsList pdbasepartition
        /\ P s0
        /\ accessibleChildPaddrIsAccessibleIntoParent s0
        /\ consistency1 s
        /\ noDupUsedPaddrList s
        /\ sharedBlockPointsToChild s
        /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase)
        /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase)
        (*/\ bentryAFlag entryaddr true s0*)
        /\ ((* Base case: starting at the root *)
            (s0 = s /\ parentsList = [] /\ statesList = []
                    /\ (pdbasepartition = constantRootPartM \/ writeSucceded = false))
            \/
            (* Induction case *)
            (isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition flag
             /\ (writeSucceded = true -> last parentsList nullAddr = constantRootPartM)
             /\ (exists nextParentsList, parentsList = (parent pdentryBase)::nextParentsList)
             /\ (exists blockaddr entry,
                        lookup blockaddr s.(memory) beqAddr = Some (BE entry)
                        /\ bentryPFlag blockaddr true s
                        /\ bentryAFlag blockaddr flag s
                        /\ In blockaddr (getMappedBlocks (parent pdentryBase) s)
                        /\ bentryStartAddr blockaddr entryaddr s
                        /\ (writeSucceded = true
                            -> (forall parent child addr, (child <> last parentsList constantRootPartM
                                                            \/ addr <> blockaddr)
                                                          -> In parent (getPartitions multiplexer s)
                                                          -> In child (getChildren parent s)
                                                          -> In addr (getAccessibleMappedPaddr child s)
                                                          -> In addr (getAccessibleMappedPaddr parent s))))))
}}.
Proof.
unfold writeAccessibleRec. eapply strengthen. eapply weaken. apply writeAccessibleRecAux.
{
  simpl. intros s Hprops.
  destruct Hprops as [Hconsist1 (HnoDup & (Hshared & (HpartialAcc & Hprops)))].
  split. assumption. split. assumption. split. assumption.
  destruct Hprops as [s0 (statesList & (parentsList & (HPs0 & Hprops)))].
  exists s0. exists statesList. exists parentsList. split. apply HPs0. (*TODO modify if necessary*)
  destruct Hprops as [Hconsists0 (HisParentsList & Hprops & HAFlag & HisBuilt & Haccess)].
  destruct Hprops as [pdentry (blockaddr & (bentry & Hprops))].
  intuition.
  - exists pdentry. intuition.
  - exists blockaddr. exists bentry. split. assumption. split. assumption. split. assumption. split. assumption.
    split. assumption.
    intros parent child addr Hhyp HparentIsPart HchildIsChild HaddrIsMapped.
    (*TODO THERE*)
    (*at s0, all is true, so what does that mean for this lemma?*)
}
{
  simpl. intros s writeSucceded Hprops.
  destruct Hprops as [parentsList (statesList & (s0 & (pdentryBase & Hprops)))].
}
Admitted.*)

Lemma writeAccessibleRec (pdbasepartition entryaddr : paddr) (flag : bool)
                          (P : state -> Prop):
{{fun s => consistency1 s
           /\ noDupUsedPaddrList s
           /\ sharedBlockPointsToChild s
           /\ (exists s0, (*exists statesList parentsList pdbasepartition,*) (*TODO verify that*)
                  P s0
                  /\ consistency s0
                  (*/\ isParentsList s0 parentsList pdbasepartition*)
                  (*/\ s = last statesList s0*)
                  (*/\ (exists entry, lookup pdbasepartition (memory s) beqAddr = Some (PDT entry))*)
                  /\ (exists ancestorEntry, lookup pdbasepartition (memory s) beqAddr = Some (PDT ancestorEntry))
                  /\ (exists blockaddr bentry, (*changed the order to put the exists out of the OR*)
                        lookup blockaddr (memory s) beqAddr = Some (BE bentry)
                        /\ bentryPFlag blockaddr true s
                        /\ bentryAFlag blockaddr flag s
                        /\ In blockaddr (getMappedBlocks pdbasepartition s)
                        /\ bentryStartAddr blockaddr entryaddr s
                        /\ (s = s0 \/
                            ((*s <> s0
                            /\*) (forall parent child addr,
                                        (child <> pdbasepartition \/ ~ In addr (getAllPaddrAux [blockaddr] s))
                                        -> In parent (getPartitions multiplexer s)
                                        -> In child (getChildren parent s)
                                        -> In addr (getAccessibleMappedPaddr parent s)
                                        -> In addr (getMappedPaddr child s)
                                        -> In addr (getAccessibleMappedPaddr child s)))))
                  (*/\ isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition flag*)
                  /\ accessibleParentPaddrIsAccessibleIntoChild s0)
}}
writeAccessibleRec pdbasepartition entryaddr flag
{{fun writeSucceded s =>
      exists s0 (*pdentryBase*),
        (* Common properties *)
        P s0
        /\ accessibleParentPaddrIsAccessibleIntoChild s0
        (*/\ lookup partition (memory s) beqAddr = Some (PDT pdentryBase)*)
        /\ consistency1 s
        /\ noDupUsedPaddrList s
        /\ sharedBlockPointsToChild s
        (*/\ (timeout > maxAddr -> writeSucceded = true)*) (*probably true, but impossible to prove*)
        /\ (writeSucceded = true -> accessibleParentPaddrIsAccessibleIntoChild s)
        (*/\ ((* Base case: starting at the root *)
            (s0 = s /\ parentsList = [] /\ statesList = []
                    /\ ((*flag = false \/*) pdbasepartition = constantRootPartM \/ writeSucceded = false))
            \/
            (* Induction case *)
            (isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition flag))*)}}.
Proof.
unfold writeAccessibleRec. apply writeAccessibleRecAux.
Qed.

(* Used in collect too *) (*MAL.readSCOriginFromBlockEntryAddr, MAL.readBlockStartFromBlockEntryAddr,
                           MAL.readSCNextFromBlockEntryAddr*)
Lemma writeAccessibleToAncestorsIfNotCutRec (pdbasepartition entryaddr : paddr) (flag : bool)
                                            (P : state -> Prop):
{{fun  s => P s /\ consistency s
          /\ (exists pdentry, lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentry))
          /\ (exists bentry : BlockEntry, lookup entryaddr s.(memory) beqAddr = Some (BE bentry))
          /\ bentryPFlag entryaddr true s
          /\ bentryAFlag entryaddr flag s
          /\ In entryaddr (getMappedBlocks pdbasepartition s)
}}
writeAccessibleToAncestorsIfNotCutRec pdbasepartition entryaddr flag 
{{fun writeSucceded s => 
    exists (s0 : state) (pdentry : PDTable)
          (blockOrigin blockStart blockNext globalIdBlock:paddr),
      (* properties common to both cases *)
      lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentry)
      /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentry)
      /\ P s0
      /\ consistency s0
      /\ (writeSucceded = true -> consistency s)
      /\ (exists (scentry : SCEntry) (scentryaddr : paddr),
            lookup scentryaddr (memory s0) beqAddr = Some (SCE scentry)
            /\ scentryNext scentryaddr blockNext s0)
      /\ (exists (scentry : SCEntry) (scentryaddr : paddr),
            lookup scentryaddr (memory s0) beqAddr = Some (SCE scentry)
            /\ scentryOrigin scentryaddr blockOrigin s0)
      /\ bentryStartAddr entryaddr globalIdBlock s0
      /\ bentryStartAddr entryaddr blockStart s0
      (* the two possible cases *)
      /\ ((s0 = s
           (*/\ ((beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr)%bool = false
               \/ flag = false \/ pdbasepartition = constantRootPartM \/ writeSucceded = false)*))
         \/ ((*exists statesList, exists parentsList,
             isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition flag
            /\*) blockStart = blockOrigin
            /\ blockNext = nullAddr))
}}.
Proof.
unfold writeAccessibleToAncestorsIfNotCutRec.
eapply bindRev.
{ (** MAL.readSCOriginFromBlockEntryAddr **)
  eapply weaken. eapply readSCOriginFromBlockEntryAddr.
  simpl. intros s Hprops.
  split. eapply Hprops. intuition.
}
intro blockOrigin. eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr **)
  eapply weaken. eapply readBlockStartFromBlockEntryAddr.
  intros s Hprops. simpl.
  split. eapply Hprops. unfold StateLib.isBE.
  destruct Hprops as [Hprops1 HpropsSCE].
  destruct Hprops1 as [HP (Hconst & (Hlookup & (HBE & HbentryA)))]. destruct HBE as [bentry HBE]. rewrite HBE.
  trivial.
}
intro blockStart. eapply bindRev.
{ (** MAL.readSCNextFromBlockEntryAddr **)
  eapply weaken. eapply readSCNextFromBlockEntryAddr.
  simpl. intros s Hprops. split. eapply Hprops. intuition.
}
intro blockNext. eapply bindRev.
{ (** readBlockStartFromBlockEntryAddr **)
  eapply weaken. eapply readBlockStartFromBlockEntryAddr.
  simpl. intros s Hprops.
  destruct Hprops as [Hprops1 HpropsSCENext]. destruct Hprops1 as [Hprops1 Hstart].
  destruct Hprops1 as [Hprops1 HSCEOrigin]. destruct Hprops1 as [HP (Hconst & (Hlookup & (HBE & HbentryA)))].
  assert(Hres : P s /\ consistency s
                /\ (exists pdentry, lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentry))
                /\ (exists bentry : BlockEntry, lookup entryaddr (memory s) beqAddr = Some (BE bentry))
                /\ bentryPFlag entryaddr true s
                /\ bentryAFlag entryaddr flag s
                /\ In entryaddr (getMappedBlocks pdbasepartition s)
                /\ (exists (scentry : SCEntry) (scentryaddr : paddr),
                     lookup scentryaddr (memory s) beqAddr = Some (SCE scentry) /\
                     StateLib.scentryOrigin scentryaddr blockOrigin s)
                /\ StateLib.bentryStartAddr entryaddr blockStart s
                /\ (exists (scentry : SCEntry) (scentryaddr : paddr),
                      lookup scentryaddr (memory s) beqAddr = Some (SCE scentry) /\
                      StateLib.scentryNext scentryaddr blockNext s)) by intuition.
  split. eapply Hres. unfold StateLib.isBE.
  destruct HBE as [bentry HBE]. rewrite HBE. trivial.
}
intro globalIdBlock. simpl.
destruct (beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr)%bool eqn:HnotCutYet.
- (* beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr = true -> block hasn't been cut *)
  assert(HblocksEq: blockStart = blockOrigin /\ blockNext = nullAddr).
  {
    apply Bool.andb_true_iff in HnotCutYet. destruct HnotCutYet as [Hstart Hnext].
    rewrite <-DTL.beqAddrTrue in *. intuition.
  }
  destruct HblocksEq as [Hstart Hnext]. subst blockStart. subst blockNext.
  eapply bindRev.
  { (** Internal.writeAccessibleRec **)
    eapply weaken. apply writeAccessibleRec.
    simpl. intros s Hprops. assert(Hconss: consistency s) by intuition.
    unfold consistency in Hconss. unfold consistency2 in Hconss. split. intuition. split. intuition. split.
    intuition. exists s. split. eapply Hprops. split. intuition. split. intuition.
    split; try(intuition; congruence). clear Hconss.
    destruct Hprops as [(HP & Hconsist & HlookupBase & HlookupEntryAddr & HAFlagEntryAddr & HscentryOrigin &
                          HstartEntryOrigin & HscentryNext) HstartEntry].
    destruct HlookupEntryAddr as [bentryAddr HlookupEntryAddr].
    exists entryaddr. exists bentryAddr. intuition.
  }
  intro recWriteEnded. simpl.
  destruct (negb recWriteEnded) eqn:HpbWrite.
  + (* recWriteEnded = false *)
    eapply weaken. eapply WP.ret. simpl. intros s Hprops.
    destruct Hprops as [s0 (Hprops & Haccesss0 & Hconsist1s & HnoDup & Hshared & Haccess)].
    destruct Hprops as [(HPs0 & Hconsists0 & HbaseIsPDT & HentryAddrIsBE & HPFlag & HAFlag & HentryMapped &
                        HsceOrigin & HentryStartOrigin & HsceNext) HentryStartGlob].
    destruct HbaseIsPDT as [pdentryBase HlookupBase].
    exists s0. exists pdentryBase. exists blockOrigin. exists blockOrigin. exists nullAddr.
    exists globalIdBlock. intuition. admit. (*TODO find a way to prove that*)
  + (* recWriteEnded = true *)
    eapply weaken. eapply WP.ret. simpl. intros s Hprops.
    destruct Hprops as [s0 (Hprops & Haccesss0 & Hconsist1s & HnoDup & Hshared & Haccess)].
    destruct Hprops as [(HPs0 & Hconsists0 & HbaseIsPDT & HentryAddrIsBE & HPFlag & HAFlag & HentryMapped &
                        HsceOrigin & HentryStartOrigin & HsceNext) HentryStartGlob].
    destruct HbaseIsPDT as [pdentryBase HlookupBase].
    exists s0. exists pdentryBase. exists blockOrigin. exists blockOrigin. exists nullAddr.
    exists globalIdBlock. apply negb_false_iff in HpbWrite. subst recWriteEnded. intuition.
    admit. (*TODO find a way to prove that*)
    unfold consistency. unfold consistency2. intuition.
- (* beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr = false -> block has been cut *)
  eapply weaken. eapply WP.ret. simpl. intros s Hprops.
  destruct Hprops as [(HPs & Hconsist & (pdentry & HlookupBase) & HentryAddrIsBE & HPFlag & HAFlag & HentryMapped
                      & HsceOrigin & HentryStartBlock & HsceNext) HentryStartGlob].
  exists s. exists pdentry. exists blockOrigin. exists blockStart. exists blockNext. exists globalIdBlock.
  intuition.
Admitted.

