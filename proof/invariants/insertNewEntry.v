(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2023)                *)
(*  Copyright (C) 2020-2023 Orange                                             *)
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
Require Import Model.ADT (*Pip.Model.Hardware Pip.Model.IAL*) Model.Monad Model.Lib
               Model.MAL.
Require Import Core.Internal Core.Services.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare Proof.InternalLemmas
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec (*EqNat*) List Bool.

Module WP := WeakestPreconditions.

(* Couper le code de preuve -> ici que faire une propagation des propriétés initiale
+ propager nouvelles propriétés *)
Lemma insertNewEntry 	(pdinsertion startaddr endaddr origin: paddr)
											(r w e : bool) (currnbfreeslots : index) idBlockToShare :
{{ fun s => (*P s /\*) partitionsIsolation s   (*/\ kernelDataIsolation s*) /\ verticalSharing s
/\ exists pdentry, lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)
								(*/\ exists entry, lookup startaddr (memory s) beqAddr = Some (entry)*)
								/\ currnbfreeslots > 0
/\ consistency s (*/\ exists nullAddr,  lookup nullAddr (memory s) beqAddr = Some (PADDR nullAddr)*)
(*/\ exists entry , lookup (CPaddr (entryaddr + scoffset)) s.(memory) beqAddr = Some (SCE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add (CPaddr (entryaddr + scoffset))
              (SCE {| origin := neworigin ; next := entry.(next) |})
              (memory s) beqAddr |}*)
(*/\ (*exists newFirstFreeSlotAddr,*)
exists newBlockEntryAddr newFirstFreeSlotAddr,
     entryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s
/\
Q tt
    {|
    currentPartition := currentPartition s;
    memory := add pdinsertion
                (PDT
                   {|
                   structure := structure pdentry;
                   firstfreeslot := newFirstFreeSlotAddr;
                   nbfreeslots := nbfreeslots pdentry;
                   nbprepare := nbprepare pdentry;
                   parent := parent pdentry;
                   MPU := MPU pdentry |}) (memory s) beqAddr |}*)
/\ (*(exists entry : BlockEntry, exists blockToShareInCurrPartAddr : paddr,
                 lookup blockToShareInCurrPartAddr (memory s) beqAddr =
                 Some (BE bentry)*) isBE idBlockToShare s

}}

Internal.insertNewEntry pdinsertion startaddr endaddr origin r w e currnbfreeslots
{{fun newentryaddr s => partitionsIsolation s   (*/\ kernelDataIsolation s*) /\ verticalSharing s /\ consistency s (*Q s /\ consistency s*)
(*{{ fun entryaddr s => Q tt s /\ P entryaddr s*)
(*/\ exists sh1entryaddr, isChild = StateLib.checkChild idPDchild s sh1entryaddr
/\ if isChild then (exists entry, lookup idPDchild s.(memory) beqAddr = Some (BE entry)
										/\ exists sh1entry, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry))
		else isChild = false*)
(*/\ exists globalIdPDChild : paddr,
	exists pdtentry : PDTable, lookup (beentry.(blockrange).(startAddr)) s.(memory) beqAddr = Some (PDT pdtentry)
-> pas cette condition car on retourne ensuite dans le code principal et si on termine
en faux on peut pas prouver ctte partie *)
/\ isBE idBlockToShare s
}}.
Proof.
(*unfold Internal.insertNewEntry.
eapply bind. intro newBlockEntryAddr.
eapply bind. intro newFirstFreeSlotAddr.
eapply bind. intro currentNbFreeSlots.
eapply bind. intro predCurrentNbFreeSlots.
eapply bind. intro ttwritePDFirstFreeSlotPointer.
eapply bind. intro ttwritePDNbFreeSlots.
eapply bind. intro ttwriteBlockStartFromBlockEntryAddr.
eapply bind. intro ttwriteBlockEndFromBlockEntryAddr.
eapply bind. intro ttwriteBlockAccessibleFromBlockEntryAddr.
eapply bind. intro ttwriteBlockPresentFromBlockEntryAddr.
eapply bind. intro ttwriteBlockRFromBlockEntryAddr.
eapply bind. intro ttwriteBlockWFromBlockEntryAddr.
eapply bind. intro ttwriteBlockXFromBlockEntryAddr.
eapply bind. intro ttwriteSCOriginFromBlockEntryAddr.
eapply weaken. apply ret.
intros. simpl. apply H.
eapply weaken. apply WP.writeSCOriginFromBlockEntryAddr.
(* Peux pas avancer en bind car s'applique avec des WP, or on en a pas pour certains write
car sont des opérations monadiques -> ne change rien si on réordonne les instructions
pour que les write soient tous ensemble*)
intros. simpl. apply H.
eapply weaken. apply WP.writeBlockXFromBlockEntryAddr.
intros. simpl. apply H.
eapply weaken. apply WP.writeBlockWFromBlockEntryAddr.
intros. simpl. apply H.
eapply weaken. apply WP.writeBlockRFromBlockEntryAddr.
intros. simpl. apply H.
eapply weaken. apply WP.writeBlockPresentFromBlockEntryAddr .
intros. simpl. apply H.
eapply weaken. apply WP.writeBlockAccessibleFromBlockEntryAddr.
intros. simpl. apply H.
eapply weaken. apply WP.writeBlockEndFromBlockEntryAddr.
intros. simpl. apply H.
eapply weaken. apply WP.writeBlockStartFromBlockEntryAddr.
intros. simpl. apply H.
eapply weaken. apply WP.writePDNbFreeSlots.
intros. simpl. apply H.
eapply weaken. apply WP.writePDFirstFreeSlotPointer .
intros. simpl. apply H.
eapply weaken. apply WP.Index.pred.
eapply weaken. apply WP.readPDNbFreeSlots.
intros. simpl. apply H.
eapply weaken. apply WP.readBlockEndFromBlockEntryAddr.
intros. simpl. apply H.
eapply weaken. apply WP.readPDFirstFreeSlot.
intros. simpl. apply H.

destruct H.
destruct H0. destruct H0.
exists x. split. assumption.
cbn.
unfold consistency in *. unfold FirstFreeSlotPointerIsBE in *.
intuition. destruct H1. destruct H1. intuition.
specialize (H5 pdinsertion x).
rewrite H0 in H5.
destruct H5. reflexivity.
exists x1. split. assumption.
exists x. split. assumption.
exists x.
unfold beqAddr. simpl. cbn. intuition.
rewrite PeanoNat.Nat.eqb_refl.
Search (PeanoNat.Nat.eqb).


destruct H5.
destruct H6.
specialize (H6 pdinsertion).
eexists. split. admit. eexists. split. exact H0.
split.
2 : { unfold isPDT. unfold add. cbn. admit. }
cbn. simpl.
instantiate (1:= fun _ => True).

unfold beqAddr.
intro newBlockEntryAddr.

eapply bind.
intro newFirstFreeSlotAddr.

eapply bind.
intros.
*)


(*
unfold Internal.insertNewEntry.
eapply WP.bindRev.
{ eapply weaken. apply readPDFirstFreeSlotPointer.
	intros. simpl. split. apply H.
	unfold isPDT. intuition. destruct H. destruct H. rewrite -> H. trivial.
}
	intro newBlockEntryAddr.
	eapply bindRev.
{ eapply weaken. apply readBlockEndFromBlockEntryAddr.
	intros. simpl. split. apply H.
	unfold isBE. intuition. destruct H0. intuition.
 	unfold consistency in *. intuition.
	unfold FirstFreeSlotPointerIsBE in *.
	destruct H5 with pdinsertion x. apply H0.
	unfold entryFirstFreeSlot in H1.
	rewrite H0 in H1. subst. rewrite H10. trivial.
}
	intro newFirstFreeSlotAddr.
	eapply bindRev.
{	eapply weaken. apply Index.pred.
	intros. simpl. split. apply H.
	intuition. destruct H. intuition.
}
	intro predCurrentNbFreeSlots. simpl.
	eapply bindRev.
{ eapply weaken.
	apply WP.writePDFirstFreeSlotPointer.
	intros. simpl.
	(* assert(exists x, lookup pdinsertion (memory s) beqAddr = Some (PDT x) ).
	{ intuition. destruct H4. destruct H0. exists x. assumption. }
	destruct H0. exists x. split. assumption.*)
	intuition.
	destruct H0. intuition.
	destruct H6. destruct H5. destruct H5.
	assert (newFirstFreeSlotAddr = x1).
	{ unfold entryEndAddr in *. unfold entryFirstFreeSlot in *.
	rewrite H0 in *. unfold consistency in *. intuition. unfold FirstFreeSlotPointerIsBE in *.
	specialize (H9 pdinsertion x H0). destruct H9. subst.
	rewrite H9 in *. subst.
	instantiate (1: newFirstFreeSlotAddr = x1
exact H6.

	destruct H6. destruct H5.
	generalize dependent x1.
	intros.

destruct H6. destruct H5. destruct H5. exact H6. H7.
	unfold entryEndAddr in *.
	unfold entryFirstFreeSlot in *.
	rewrite H0 in H4.
	subst. unfold consistency in *. unfold FirstFreeSlotPointerIsBE in *. intuition.
	specialize (H9 pdinsertion x H0).
	destruct H9 as [slotentry].
	rewrite H9 in H3. subst.
	destruct H8. eapply H3.

	specialize (H8 (endAddr (blockrange slotentry))).


 apply H8. destruct H8. apply H7.

	intuition.
	destruct H4. destruct H0. exists x. intuition.

}
	intros.
	eapply bindRev.
{ eapply weaken. apply WP.writePDNbFreeSlots.
	intros. simpl. exact H.
}
	intros.
	eapply bindRev.
{ eapply weaken. apply WP.writeBlockStartFromBlockEntryAddr.
	intros. simpl. exact H.
}
	intros.
	eapply bindRev.
{ eapply weaken. apply WP.writeBlockEndFromBlockEntryAddr.
	intros. simpl. exact H.
}
	intros.
	eapply bindRev.
{ eapply weaken. apply WP.writeBlockAccessibleFromBlockEntryAddr.
	intros. simpl. exact H.
}
	intros.
	eapply bindRev.
{ eapply weaken. apply WP.writeBlockPresentFromBlockEntryAddr.
	intros. simpl. exact H.
}
	intros.
	eapply bindRev.
{ eapply weaken. apply WP.writeBlockRFromBlockEntryAddr.
	intros. simpl. exact H.
}
	intros.
	eapply bindRev.
{ eapply weaken. apply WP.writeBlockWFromBlockEntryAddr.
	intros. simpl. exact H.
}
	intros.
	eapply bindRev.
{ eapply weaken. apply WP.writeBlockXFromBlockEntryAddr.
	intros. simpl. exact H.
}
	intros.
	eapply bindRev.
{ eapply weaken. apply writeSCOriginFromBlockEntryAddr.
	intros. simpl. exact H.
}
	intros.
	eapply weaken. apply ret.
	intros. simpl. exact H.
Qed.*)
	eapply bind. intros.
	eapply bind. intros.
	eapply bind. intros.
	eapply bind. intros.
	eapply bind. intros.
	(*eapply bind. intros.
	eapply bind. intros.
	eapply bind. intros.
	eapply bind. intros.
	eapply bind. intros.*)
	eapply weaken. apply ret.
	intros. apply H.
	(*apply writeSCOriginFromBlockEntryAddr.
	apply writeBlockXFromBlockEntryAddr.
	apply writeBlockWFromBlockEntryAddr.
	apply writeBlockRFromBlockEntryAddr.
	apply writeBlockPresentFromBlockEntryAddr.
	apply writeBlockAccessibleFromBlockEntryAddr.
	apply writeBlockEndFromBlockEntryAddr.
	apply writeBlockStartFromBlockEntryAddr.*)
	apply writePDNbFreeSlots. simpl.
	apply WP.writePDFirstFreeSlotPointer. simpl.
	intros.
	apply WP.Index.pred.
	apply WP.readBlockEndFromBlockEntryAddr.
	eapply weaken. apply WP.readPDFirstFreeSlotPointer.
	intros. simpl. intuition.
	destruct H2.  exists x. split. apply H1.
	intuition. unfold consistency in *. unfold FirstFreeSlotPointerIsBE in *.
	intuition. specialize (H7 pdinsertion x H2).
	destruct H7. exists x0. split. intuition.
	split. assumption.
	intros. simpl. exists x. split. apply H2.
	rewrite beqAddrTrue. simpl.
	eexists. split.
	f_equal.
	split. intros parent child1 child2 Hparent Hchild1 Hchild2 Hneq.
	intros paddr1 Hpaddr1 Hpaddr1'.
cbn in *. unfold partitionsIsolation, Lib.disjoint, not in H0.
	apply H0 with parent child1 child2 paddr1 ; trivial.


unfold partitionsIsolation. intros. simpl.
	unfold getUsedBlocks. unfold getConfigBlocks.
	unfold getMappedBlocks. set (s' := {|
       currentPartition := currentPartition s;
       memory := _ |}).
	congruence.
	split.
- unfold verticalSharing. intros. simpl.
	unfold getUsedBlocks. unfold getConfigBlocks.
	unfold getMappedBlocks.
	set (s' := {|
       currentPartition := currentPartition s;
       memory := _ |}) in *.
	destruct (lookup child (memory s') beqAddr) ; congruence.
- split. split. unfold wellFormedFstShadowIfBlockEntry. intros. simpl.
	unfold isSHE. intros.
	destruct (  lookup (CPaddr (pa + sh1offset))
    (memory
       {|
       currentPartition := currentPartition s;
       memory := add pdinsertion
                   (PDT
                      {|
                      structure := structure x;
                      firstfreeslot := endAddr (blockrange x0);
                      nbfreeslots := {| i := currnbfreeslots - 1; Hi := Hi |};
                      nbprepare := nbprepare x;
                      parent := parent x;
                      MPU := MPU x |})
                   (add pdinsertion
                      (PDT
                         {|
                         structure := structure x;
                         firstfreeslot := endAddr (blockrange x0);
                         nbfreeslots := nbfreeslots x;
                         nbprepare := nbprepare x;
                         parent := parent x;
                         MPU := MPU x |}) (memory s) beqAddr) beqAddr |}) beqAddr).
	destruct v. congruence. intuition. congruence. congruence. congruence. congruence.
	split. unfold PDTIfPDFlag. intros. exists x0. split.
	destruct x0. simpl in *. rewrite beqAddrTrue. subst. rewrite removeDupIdentity.
	destruct (beqAddr pdinsertion idPDchild).
	simpl. congruence. congruence. congruence.
	unfold entryPDT. destruct (lookup idPDchild
    (memory
       {|
       currentPartition := currentPartition s;
       memory := add pdinsertion
                   (PDT
                      {|
                      structure := structure
                                     {|
                                     structure := structure x;
                                     firstfreeslot := endAddr (blockrange x0);
                                     nbfreeslots := nbfreeslots x;
                                     nbprepare := nbprepare x;
                                     parent := parent x;
                                     MPU := MPU x |};
                      firstfreeslot := firstfreeslot
                                         {|
                                         structure := structure x;
                                         firstfreeslot := endAddr (blockrange x0);
                                         nbfreeslots := nbfreeslots x;
                                         nbprepare := nbprepare x;
                                         parent := parent x;
                                         MPU := MPU x |};
                      nbfreeslots := {| i := currnbfreeslots - 1; Hi := Hi |};
                      nbprepare := nbprepare
                                     {|
                                     structure := structure x;
                                     firstfreeslot := endAddr (blockrange x0);
                                     nbfreeslots := nbfreeslots x;
                                     nbprepare := nbprepare x;
                                     parent := parent x;
                                     MPU := MPU x |};
                      parent := parent
                                  {|
                                  structure := structure x;
                                  firstfreeslot := endAddr (blockrange x0);
                                  nbfreeslots := nbfreeslots x;
                                  nbprepare := nbprepare x;
                                  parent := parent x;
                                  MPU := MPU x |};
                      MPU := MPU
                               {|
                               structure := structure x;
                               firstfreeslot := endAddr (blockrange x0);
                               nbfreeslots := nbfreeslots x;
                               nbprepare := nbprepare x;
                               parent := parent x;
                               MPU := MPU x |} |})
                   (add pdinsertion
                      (PDT
                         {|
                         structure := structure x;
                         firstfreeslot := endAddr (blockrange x0);
                         nbfreeslots := nbfreeslots x;
                         nbprepare := nbprepare x;
                         parent := parent x;
                         MPU := MPU x |}) (memory s) beqAddr) beqAddr |}) beqAddr).
	destruct v ; congruence. congruence.
	split. unfold nullAddrExists. simpl. intros. unfold getNullAddr.
	destruct (lookup nullAddr
  (memory
     {|
     currentPartition := currentPartition s;
     memory := add pdinsertion
                 (PDT
                    {|
                    structure := structure x;
                    firstfreeslot := endAddr (blockrange x0);
                    nbfreeslots := {| i := currnbfreeslots - 1; Hi := Hi |};
                    nbprepare := nbprepare x;
                    parent := parent x;
                    MPU := MPU x |})
                 (add pdinsertion
                    (PDT
                       {|
                       structure := structure x;
                       firstfreeslot := endAddr (blockrange x0);
                       nbfreeslots := nbfreeslots x;
                       nbprepare := nbprepare x;
                       parent := parent x;
                       MPU := MPU x |}) (memory s) beqAddr) beqAddr |}) beqAddr).
	congruence. congruence.
split. intros. simpl.
	exists x0. rewrite removeDupDupIdentity. rewrite removeDupIdentity.
	destruct (beqAddr pdinsertion (firstfreeslot entry)) eqn:Hbeq ; congruence.
	congruence. congruence. congruence.
	unfold isBE.
	destruct (lookup idBlockToShare
    (memory
       {|
       currentPartition := currentPartition s;
       memory := add pdinsertion
                   (PDT
                      {|
                      structure := structure
                                     {|
                                     structure := structure x;
                                     firstfreeslot := endAddr
                                              (blockrange x0);
                                     nbfreeslots := nbfreeslots x;
                                     nbprepare := nbprepare x;
                                     parent := parent x;
                                     MPU := MPU x |};
                      firstfreeslot := firstfreeslot
                                         {|
                                         structure := structure x;
                                         firstfreeslot := endAddr
                                              (blockrange x0);
                                         nbfreeslots := nbfreeslots x;
                                         nbprepare := nbprepare x;
                                         parent := parent x;
                                         MPU := MPU x |};
                      nbfreeslots := {|
                                     i := currnbfreeslots - 1;
                                     Hi := Hi |};
                      nbprepare := nbprepare
                                     {|
                                     structure := structure x;
                                     firstfreeslot := endAddr
                                              (blockrange x0);
                                     nbfreeslots := nbfreeslots x;
                                     nbprepare := nbprepare x;
                                     parent := parent x;
                                     MPU := MPU x |};
                      parent := parent
                                  {|
                                  structure := structure x;
                                  firstfreeslot := endAddr
                                              (blockrange x0);
                                  nbfreeslots := nbfreeslots x;
                                  nbprepare := nbprepare x;
                                  parent := parent x;
                                  MPU := MPU x |};
                      MPU := MPU
                               {|
                               structure := structure x;
                               firstfreeslot := endAddr (blockrange x0);
                               nbfreeslots := nbfreeslots x;
                               nbprepare := nbprepare x;
                               parent := parent x;
                               MPU := MPU x |} |})
                   (add pdinsertion
                      (PDT
                         {|
                         structure := structure x;
                         firstfreeslot := endAddr (blockrange x0);
                         nbfreeslots := nbfreeslots x;
                         nbprepare := nbprepare x;
                         parent := parent x;
                         MPU := MPU x |}) (memory s) beqAddr) beqAddr |})
    beqAddr) ; congruence.

Qed.




(*
unfold add. simpl. rewrite beqAddrTrue. simpl.
	assert (
forall addr pe1 pointer, lookup addr (memory s) beqAddr = Some (PDT pe1) ->
exists pe2,
          lookup addr  (add addr
       (PDT
          {|
          structure := structure pe1;
              firstfreeslot := pointer;
              nbfreeslots := nbfreeslots pe1;
              nbprepare := nbprepare pe1;
              parent := parent pe1;
              MPU := MPU pe1 |}) (memory s) beqAddr) beqAddr  = Some (PDT pe2)

).
{
	intros . cbn. rewrite beqAddrTrue.
	eexists. f_equal.
}
	specialize (H9 pdinsertion x (endAddr (blockrange x0)) H0).
	exact H9.
  rewrite  Hmemory. eassumption.}
	rewrite removeDupDupIdentity.
 apply removeDupIdentity.


(*simpl. intuition.
destruct H4. exists x. intuition.
eexists. simpl.
unfold beqAddr.
rewrite PeanoNat.Nat.eqb_refl.
simpl.
split.
- f_equal.
- eexists. split.
	assert (PeanoNat.Nat.eqb pdinsertion newBlockEntryAddr = false).
	unfold entryEndAddr in *. unfold entryFirstFreeSlot in *.
	rewrite H4 in H3. subst.
	rewrite PeanoNat.Nat.eqb_neq.
	Search (lookup).
	destruct (lookup (firstfreeslot x) (memory s) beqAddr) eqn:Hfalse.
	destruct v eqn:Hv.
	unfold not. intro. subst. rewrite H0 in Hfalse. Set Printing All.
	(* Prouver que lookup addr = Some PDT et lookup addr = Some BE -> False*)
Search ( PeanoNat.Nat.eqb ?x ?y = false).*)
	intuition. destruct H4. exists x. rewrite beqAddrTrue. split.	apply H0.
	eexists. split. simpl. f_equal.
	(*eexists. split.*)
	simpl. rewrite beqAddrTrue. simpl.
	(* newblockEntryAddr is the free slot pointer in PDT, we know it's a BE from consistency*)
	assert (beqAddr pdinsertion newBlockEntryAddr = false).
	{ apply beqAddrFalse. unfold not.
		intros.
		unfold entryEndAddr in *. unfold entryFirstFreeSlot in *.
		destruct H0.
		rewrite H0 in H3. subst.
		destruct H5. unfold consistency in *. unfold FirstFreeSlotPointerIsBE in *.
		intuition. specialize (H7 (firstfreeslot x) x).
		rewrite H0 in H7. destruct H7. reflexivity. congruence.
	}
		rewrite H4. simpl.
		rewrite removeDupDupIdentity. rewrite removeDupIdentity.
		unfold entryFirstFreeSlot in *.
		destruct H0. rewrite H0 in H3.
		unfold consistency in *. unfold FirstFreeSlotPointerIsBE in *.
		destruct H5.
		intuition.
		specialize (H9 pdinsertion x H0).
		destruct H9.
		subst. exists x0. split.	rewrite H9. reflexivity.
		eexists ?[newentry]. split. f_equal. simpl.

		(*simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
			destruct (lt_dec blockindex kernelStructureEntriesNb) ; simpl.
			destruct (lt_dec blockindex kernelStructureEntriesNb) ; simpl.
			unfold CBlock. simpl. destruct (lt_dec startaddr (endAddr blockrange) ) ; simpl.
			destruct (lt_dec startaddr endaddr) ; simpl.

			eexists. split. f_equal. simpl.*)

		assert (forall x0 : BlockEntry, read
             (CBlockEntry (read x0) (write x0) (exec x0)
                (present x0) (accessible x0) (blockindex x0)
                (CBlock startaddr (endAddr (blockrange x0)))) = read x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
			simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity.
			congruence.
		}
assert (forall x0 : BlockEntry, write
             (CBlockEntry (read x0) (write x0) (exec x0)
                (present x0) (accessible x0) (blockindex x0)
                (CBlock startaddr (endAddr (blockrange x0)))) = write x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity.
			congruence.
		}
assert (forall x0 : BlockEntry, exec
             (CBlockEntry (read x0) (write x0) (exec x0)
                (present x0) (accessible x0) (blockindex x0)
                (CBlock startaddr (endAddr (blockrange x0)))) = exec x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity.
			congruence.
		}
assert (forall x0 : BlockEntry, accessible
             (CBlockEntry (read x0) (write x0) (exec x0)
                (present x0) (accessible x0) (blockindex x0)
                (CBlock startaddr (endAddr (blockrange x0)))) = accessible x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity.
			congruence.
		}
assert (forall x0 : BlockEntry, present
             (CBlockEntry (read x0) (write x0) (exec x0)
                (present x0) (accessible x0) (blockindex x0)
                (CBlock startaddr (endAddr (blockrange x0)))) = present x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity.
			congruence.
		}
		rewrite H3. rewrite H14. rewrite H16. rewrite H17. rewrite H18.

assert (forall x0 : BlockEntry, (blockindex
             (CBlockEntry (read x0) (write x0) (exec x0)
                (present x0) (accessible x0) (blockindex x0)
                (CBlock startaddr (endAddr (blockrange x0))))) = blockindex x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity.
			congruence.
		}
		rewrite H19.
		assert(forall x0 : BlockEntry, startAddr
                (blockrange
                   (CBlockEntry (read x0) (write x0) (exec x0)
                      (present x0) (accessible x0) (blockindex x0)
                      (CBlock startaddr (endAddr (blockrange x0))))) = startaddr).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. unfold CBlock.  destruct (lt_dec startaddr (endAddr (ADT.blockrange x0))).
			simpl. reflexivity.
			congruence.
			simpl. congruence.
}
	rewrite H20.

		eexists. split. f_equal.
		eexists. split. simpl.
		assert (forall x0 : BlockEntry, (read
           (CBlockEntry (read x0) (write x0) (exec x0) (present x0)
              (accessible x0) (blockindex x0) (CBlock startaddr endaddr))) = read x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity. congruence.
}
			assert (forall x0 : BlockEntry, (write
           (CBlockEntry (read x0) (write x0) (exec x0) (present x0)
              (accessible x0) (blockindex x0) (CBlock startaddr endaddr))) = write x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity. congruence.
}
			assert (forall x0 : BlockEntry, (exec
           (CBlockEntry (read x0) (write x0) (exec x0) (present x0)
              (accessible x0) (blockindex x0) (CBlock startaddr endaddr))) = exec x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity. congruence.
}
			assert (forall x0 : BlockEntry, (present
           (CBlockEntry (read x0) (write x0) (exec x0) (present x0)
              (accessible x0) (blockindex x0) (CBlock startaddr endaddr))) = present x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity. congruence.
}
			assert (forall x0 : BlockEntry, (accessible
           (CBlockEntry (read x0) (write x0) (exec x0) (present x0)
              (accessible x0) (blockindex x0) (CBlock startaddr endaddr))) = accessible x0).
		{ simpl. induction x0. simpl.
			intuition. cbn. unfold CBlockEntry.
						simpl. destruct (lt_dec (ADT.blockindex x0) kernelStructureEntriesNb).
			simpl. reflexivity. congruence.
}

rewrite H21, H22, H23, H24. f_equal.


			unfold CBlockEntry.
						simpl. destruct (lt_dec (blockindex x0) kernelStructureEntriesNb).
			simpl. destruct (lt_dec (blockindex x0) kernelStructureEntriesNb).
			simpl.


unfold CBlock.  destruct (lt_dec startaddr (endAddr (ADT.blockrange x0))).
			simpl. reflexivity.
			congruence.
			simpl. congruence.


			destruct CBlockEntry. simpl.
		exists entry.

		assert (exists entry1 : BlockEntry, CBlockEntry (read x1) (write x1) (exec x1) (present x1)
          (accessible x1) (blockindex x1)
          (CBlock startaddr (endAddr (blockrange x1))) = Some (entry)).

                   {|
                   currentPartition := currentPartition s;
                   memory := add newBlockEntryAddr
                                              (BE
                                                 (CBlockEntry
                                                    (read entry)
                                                    (write entry)
                                                    (exec entry)
                                                    (present entry)
                                                    (accessible entry)
                                                    (blockindex entry)
                                                    (CBlock
                                                       (startAddr (blockrange entry))
                                                       endaddr)))
		eexists. split. f_equal.
		eexists. split. f_equal.
		2 : { apply beqAddrFalse in H4. intuition. }
		2 :{ apply beqAddrFalse in H4. intuition. }
		eexists. split. f_equal.
		eexists. split. f_equal.
		Definition foo (x : nat) : nat := ltac:(exact x).
		exists foo.
		set (s' := add newBlockEntryAddr
                         (BE
                            (CBlockEntry (read entry2) (write entry2) e
                               (present entry2) (accessible entry2)
                               (blockindex entry2) (blockrange entry2)))
                         (add newBlockEntryAddr
                            (BE
                               (CBlockEntry (read entry1) w
                                  (exec entry1) (present entry1)
                                  (accessible entry1) (blockindex entry1)
                                  (blockrange entry1)))
                            (add newBlockEntryAddr
                               (BE
                                  (CBlockEntry r (write entry0)
                                     (exec entry0) (present entry0)
                                     (accessible entry0)
                                     (blockindex entry0)
                                     (blockrange entry0)))
                               (add newBlockEntryAddr
                                  (BE
                                     (CBlockEntry (read entry)
                                        (write entry) (exec entry) true
                                        (accessible entry)
                                        (blockindex entry)
                                        (blockrange entry)))
                                  (add newBlockEntryAddr
                                     (BE
                                        (CBlockEntry
                                           (read
                                              (CBlockEntry
                                                 (read
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (write
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (exec
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (present
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (accessible
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (blockindex
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (CBlock
                                                    (startAddr
                                                       (blockrange
                                                        (CBlockEntry
                                                        (read x1)
                                                        (write x1)
                                                        (exec x1)
                                                        (present x1)
                                                        (accessible x1)
                                                        (blockindex x1)
                                                        (CBlock startaddr
                                                        (endAddr (blockrange x1))))))
                                                    endaddr)))
                                           (write
                                              (CBlockEntry
                                                 (read
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (write
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (exec
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (present
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (accessible
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (blockindex
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (CBlock
                                                    (startAddr
                                                       (blockrange
                                                        (CBlockEntry
                                                        (read x1)
                                                        (write x1)
                                                        (exec x1)
                                                        (present x1)
                                                        (accessible x1)
                                                        (blockindex x1)
                                                        (CBlock startaddr
                                                        (endAddr (blockrange x1))))))
                                                    endaddr)))
                                           (exec
                                              (CBlockEntry
                                                 (read
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (write
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (exec
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (present
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (accessible
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (blockindex
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (CBlock
                                                    (startAddr
                                                       (blockrange
                                                        (CBlockEntry
                                                        (read x1)
                                                        (write x1)
                                                        (exec x1)
                                                        (present x1)
                                                        (accessible x1)
                                                        (blockindex x1)
                                                        (CBlock startaddr
                                                        (endAddr (blockrange x1))))))
                                                    endaddr)))
                                           (present
                                              (CBlockEntry
                                                 (read
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (write
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (exec
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (present
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (accessible
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (blockindex
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (CBlock
                                                    (startAddr
                                                       (blockrange
                                                        (CBlockEntry
                                                        (read x1)
                                                        (write x1)
                                                        (exec x1)
                                                        (present x1)
                                                        (accessible x1)
                                                        (blockindex x1)
                                                        (CBlock startaddr
                                                        (endAddr (blockrange x1))))))
                                                    endaddr))) true
                                           (blockindex
                                              (CBlockEntry
                                                 (read
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (write
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (exec
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (present
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (accessible
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (blockindex
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (CBlock
                                                    (startAddr
                                                       (blockrange
                                                        (CBlockEntry
                                                        (read x1)
                                                        (write x1)
                                                        (exec x1)
                                                        (present x1)
                                                        (accessible x1)
                                                        (blockindex x1)
                                                        (CBlock startaddr
                                                        (endAddr (blockrange x1))))))
                                                    endaddr)))
                                           (blockrange
                                              (CBlockEntry
                                                 (read
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (write
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (exec
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (present
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (accessible
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (blockindex
                                                    (CBlockEntry
                                                       (read x1)
                                                       (write x1)
                                                       (exec x1)
                                                       (present x1)
                                                       (accessible x1)
                                                       (blockindex x1)
                                                       (CBlock startaddr
                                                        (endAddr (blockrange x1)))))
                                                 (CBlock
                                                    (startAddr
                                                       (blockrange
                                                        (CBlockEntry
                                                        (read x1)
                                                        (write x1)
                                                        (exec x1)
                                                        (present x1)
                                                        (accessible x1)
                                                        (blockindex x1)
                                                        (CBlock startaddr
                                                        (endAddr (blockrange x1))))))
                                                    endaddr)))))
                                     (add newBlockEntryAddr
                                        (BE
                                           (CBlockEntry
                                              (read
                                                 (CBlockEntry
                                                    (read x1)
                                                    (write x1)
                                                    (exec x1)
                                                    (present x1)
                                                    (accessible x1)
                                                    (blockindex x1)
                                                    (CBlock startaddr
                                                       (endAddr (blockrange x1)))))
                                              (write
                                                 (CBlockEntry
                                                    (read x1)
                                                    (write x1)
                                                    (exec x1)
                                                    (present x1)
                                                    (accessible x1)
                                                    (blockindex x1)
                                                    (CBlock startaddr
                                                       (endAddr (blockrange x1)))))
                                              (exec
                                                 (CBlockEntry
                                                    (read x1)
                                                    (write x1)
                                                    (exec x1)
                                                    (present x1)
                                                    (accessible x1)
                                                    (blockindex x1)
                                                    (CBlock startaddr
                                                       (endAddr (blockrange x1)))))
                                              (present
                                                 (CBlockEntry
                                                    (read x1)
                                                    (write x1)
                                                    (exec x1)
                                                    (present x1)
                                                    (accessible x1)
                                                    (blockindex x1)
                                                    (CBlock startaddr
                                                       (endAddr (blockrange x1)))))
                                              (accessible
                                                 (CBlockEntry
                                                    (read x1)
                                                    (write x1)
                                                    (exec x1)
                                                    (present x1)
                                                    (accessible x1)
                                                    (blockindex x1)
                                                    (CBlock startaddr
                                                       (endAddr (blockrange x1)))))
                                              (blockindex
                                                 (CBlockEntry
                                                    (read x1)
                                                    (write x1)
                                                    (exec x1)
                                                    (present x1)
                                                    (accessible x1)
                                                    (blockindex x1)
                                                    (CBlock startaddr
                                                       (endAddr (blockrange x1)))))
                                              (CBlock
                                                 (startAddr
                                                    (blockrange
                                                       (CBlockEntry
                                                        (read x1)
                                                        (write x1)
                                                        (exec x1)
                                                        (present x1)
                                                        (accessible x1)
                                                        (blockindex x1)
                                                        (CBlock startaddr
                                                        (endAddr (blockrange x1))))))
                                                 endaddr)))
                                        (add newBlockEntryAddr
                                           (BE
                                              (CBlockEntry
                                                 (read x1)
                                                 (write x1)
                                                 (exec x1)
                                                 (present x1)
                                                 (accessible x1)
                                                 (blockindex x1)
                                                 (CBlock startaddr
                                                    (endAddr (blockrange x1)))))
                                           (add pdinsertion
                                              (PDT
                                                 {|
                                                 structure := structure x;
                                                 firstfreeslot := newFirstFreeSlotAddr;
                                                 nbfreeslots := predCurrentNbFreeSlots;
                                                 nbprepare := nbprepare x;
                                                 parent := parent x;
                                                 MPU := MPU x |})
                                              (add pdinsertion
                                                 (PDT
                                                    {|
                                                    structure := structure x;
                                                    firstfreeslot := newFirstFreeSlotAddr;
                                                    nbfreeslots := nbfreeslots x;
                                                    nbprepare := nbprepare x;
                                                    parent := parent x;
                                                    MPU := MPU x |})
                                                 (memory s) beqAddr) beqAddr) beqAddr)
                                        beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                         beqAddr) .
		destruct entry as (_).
		eexists. split. f_equal.
		eexists. split. f_equal.
		eexists. split. f_equal.
		eexists. split. f_equal.
		destruct entry.
		eexists. split. f_equal.
		eexists. split. f_equal.
		eexists. split. f_equal.
		assert (add newBlockEntryAddr
              (BE
                 (CBlockEntry (read x1) (write x1) (exec x1)
                    true true
                    (blockindex x2) (CBlock ((startAddr (blockrange x0) (endAddr (blockrange x))))
              (add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read ?entry2) w (exec ?entry2)
                       (present ?entry2) (accessible ?entry2)
                       (blockindex ?entry2) (blockrange ?entry2)))
                 (add newBlockEntryAddr
                    (BE
                       (CBlockEntry r (write ?entry1) (exec ?entry1)
                          (present ?entry1) (accessible ?entry1)
                          (blockindex ?entry1) (blockrange ?entry1)))
                    (add newBlockEntryAddr
                       (BE
                          (CBlockEntry (read ?entry0) (write ?entry0)
                             (exec ?entry0) true (accessible ?entry0)
                             (blockindex ?entry0) (blockrange ?entry0)))
                       (add newBlockEntryAddr
                          (BE
                             (CBlockEntry (read ?entry)
                                (write ?entry) (exec ?entry)
                                (present ?entry) true (blockindex ?entry)
                                (blockrange ?entry)))
                          (add newBlockEntryAddr
                             (BE
                                (CBlockEntry (read x2) (write x2)
                                   (exec x2) (present x2)
                                   (accessible x2) (blockindex x2)
                                   (CBlock (startAddr (blockrange x2)) endaddr)))
                             (add newBlockEntryAddr
                                (BE
                                   (CBlockEntry (read x1)
                                      (write x1) (exec x1)
                                      (present x1) (accessible x1)
                                      (blockindex x1)
                                      (CBlock startaddr (endAddr (blockrange x1))))))))))) =
add newBlockEntryAddr
              (BE
                 (CBlockEntry r w e
                    true true
                    (blockindex x2)
(CBlock (startAddr endaddr))))).

set (s' :=   {|
currentPartition := _ |}).
{
	unfold isBE. destruct (lookup newBlockEntryAddr (memory s') beqAddr) eqn:Hlookup.
	destruct v eqn:Hv ; trivial.





{|
                      (CBlockEntry
                         (read
                            (CBlockEntry
                               (read
                                  (CBlockEntry r (write ?entry)
                                     (exec ?entry) (present ?entry)
                                     (accessible ?entry)
                                     (blockindex ?entry)
                                     (blockrange ?entry))) w
		eexists. split. subst. f_equal.
		eexists. split. subst. f_equal.
		eexists. split. subst. f_equal.
		eexists. split.
2 : {	eexists. split. f_equal.
			eexists. split. simpl. f_equal.
		unfold isBE. simpl. split.



}
		eexists. split. subst. f_equal.
		eexists. split. subst. f_equal.
		eexists. split. subst. f_equal.



		unfold entryEndAddr in *.
		destruct (lookup newBlockEntryAddr (memory s) beqAddr) eqn:Hlookup.
		f_equal.
		destruct v eqn:Hv.
		specialize (entry = b).

rewrite H5. simpl.
		assert (lookup newBlockEntryAddr
  (removeDup pdinsertion (removeDup pdinsertion (memory s) beqAddr) beqAddr)
  beqAddr = lookup newBlockEntryAddr (memory s) beqAddr).
		{ apply removeDupIdentity. intuition. }
		unfold removeDup. simpl.


	eapply bindRev.
{	eapply weaken. apply WP.writePDFirstFreeSlotPointer.
	intros. simpl. intuition.
	destruct H4. exists x. split. destruct H0. assumption.
	unfold add.
	set (s' :=  {|
     currentPartition := _ |}).
	subst.
	exact (P s').

writeAccessible
split. apply H.
	intuition. destruct H3. destruct H. destruct H3. intuition.
}
	intro predCurrentNbFreeSlots.


set (s' :=  {|
     currentPartition := _ |}).
   simpl in *.
	pattern s in H.
   instantiate (1 := fun tt s => H /\
             StateLib.entryFirstFreeSlot pdinsertion s.(memory) = Some newFirstFreeSlotAddr ).

assert( Hlemma : forall addr1 addr2 x pointer,
addr2 <> addr1 ->
entryFirstFreeSlot addr1 pointer s ->
entryFirstFreeSlot addr1 pointer
  {|
  currentPartition := currentPartition s;
  memory := add addr2 x (memory s) beqAddr |}).
{
intros.
unfold entryFirstFreeSlot in *.
cbn.
case_eq (beqAddr addr2 addr1).
intros. simpl. unfold beqAddr in H5. unfold not in H3. contradict H5.
	unfold not. intro. apply H3. Search(PeanoNat.Nat.eqb).
	rewrite -> PeanoNat.Nat.eqb_eq in H5.
	destruct addr2 in *. destruct addr1 in *. apply H5.

unfold not in H0.
unfold beqAddr.
rewrite <- H0.
assert (Hpairs : beqPairs (table2, idx2) (table1, idx1) beqAddr = false).
apply beqPairsFalse.
left; trivial.
rewrite Hpairs.
assert (lookup  table1 idx1 (removeDup table2 idx2 (memory s) beqPage beqIndex)
          beqPage beqIndex = lookup  table1 idx1 (memory s) beqPage beqIndex) as Hmemory.
{ apply removeDupIdentity. subst.  intuition. }
rewrite  Hmemory. assumption.
Qed.

destruct H. destruct H. destruct H. destruct H2.
	exists x. split. destruct H2. assumption.
	pose (H' : H&H2&H1).
	pose (H'' := conj H1 H0).
	pose (H''' := conj H' H'').
	pattern s in H'''.
  match type of H with
  | ?HT s => instantiate (1 := fun tt s => HT s /\
             StateLib.entryFirstFreeSlot pdinsertion s.(memory) = Some newFirstFreeSlotAddr )
  end.

	  intros. simpl.
     (*set (s' := {| currentPartition := _ |}). *)


admit. (*
 (** add the propeties about writeAccessible post conditions **)
match type of H2 with
  | ?HT s => instantiate (1 := fun tt s => HT s /\
              entryUserFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) false s /\
              isEntryPage ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) phypage s /\
              entryPresentFlag ptvaInAncestor (StateLib.getIndexOfAddr vaInAncestor fstLevel) true s  )
  end.
  rewrite and_assoc.
   split. *)
}	intros.

	eapply bindRev.
{ eapply weaken. apply readPDNbFreeSlots.
	intros. simpl.

}
	intro currentNbFreeSlots.

Require Import Model.Test.

Lemma addMemoryBlockTest  (currentPartition idPDchild : paddr) :
{{fun s => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
checkChildOfCurrPart3 currentPartition idPDchild
{{fun _ s  => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold checkChildOfCurrPart3.
eapply bindRev.
eapply weaken. apply checkChildOfCurrPart. simpl. intros. split. apply H. apply H.
intro b. simpl. destruct b. simpl.
eapply bindRev.
	eapply weaken. apply readBlockStartFromBlockEntryAddr. intros. simpl. split.
	apply H.
	unfold isBE.

	unfold checkChild in *.
Admitted.*)

