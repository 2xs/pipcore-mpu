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
											(r w e : bool) (currnbfreeslots : index) (P : state -> Prop):
{{ fun s => (*P s /\*) partitionsIsolation s   (*/\ kernelDataIsolation s*) /\ verticalSharing s
/\ consistency s
(* to retrieve the fields in pdinsertion *)
/\ (exists pdentry, lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry))
(* to show the first free slot pointer is not NULL *)
/\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s /\ currnbfreeslots > 0)
/\ P s
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
(*/\ (*(exists entry : BlockEntry, exists blockToShareInCurrPartAddr : paddr,
                 lookup blockToShareInCurrPartAddr (memory s) beqAddr =
                 Some (BE bentry)*) isBE idBlockToShare s*)

}}

Internal.insertNewEntry pdinsertion startaddr endaddr origin r w e currnbfreeslots
{{fun newentryaddr s => (*partitionsIsolation s   (*/\ kernelDataIsolation s*) /\ verticalSharing s /\ consistency s*)
(*/\ exists globalIdPDChild : paddr, 
	exists pdtentry : PDTable, lookup (beentry.(blockrange).(startAddr)) s.(memory) beqAddr = Some (PDT pdtentry)
-> pas cette condition car on retourne ensuite dans le code principal et si on termine 
en faux on peut pas prouver ctte partie *)
(exists s0, P s0) /\ isBE newentryaddr s /\ consistency s /\
(*
exists sceaddr scentry pdentry bentry newBlockEntryAddr newFirstFreeSlotAddr predCurrentNbFreeSlots,
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r w e
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))


				(add sceaddr (SCE {| origin := origin; next := next scentry |})
 (memory s) beqAddr) beqAddr) beqAddr |})
*)

(exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5: BlockEntry,
		exists sceaddr, exists scentry : SCEntry,
		exists newBlockEntryAddr newFirstFreeSlotAddr predCurrentNbFreeSlots,
  s = {|
     currentPartition := currentPartition s0;
     memory := add sceaddr
									(SCE {| origin := origin; next := next scentry |})
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry5) (write bentry5) e (present bentry5) 
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
  
)
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
eapply weaken. apply ret.
intros. simpl. apply H.
admit.
(*eapply weaken. eapply WP.writeSCOriginFromBlockEntryAddr.*)
(* Peux pas avancer en bind car s'applique avec des WP, or on en a pas pour certains write
car sont des opérations monadiques -> ne change rien si on réordonne les instructions
pour que les write soient tous ensemble*)
*)

unfold Internal.insertNewEntry.
eapply WP.bindRev.
{ (** readPDFirstFreeSlotPointer **)
	eapply weaken. apply readPDFirstFreeSlotPointer.
	intros. simpl. split. apply H.
	unfold isPDT. intuition. destruct H2. intuition. rewrite -> H2. trivial.
}
	intro newBlockEntryAddr.
	eapply bindRev.
{ (** readBlockEndFromBlockEntryAddr **)
	eapply weaken. apply readBlockEndFromBlockEntryAddr.
	intros. simpl. split. apply H.
	unfold isBE. intuition. destruct H3. intuition.
 	unfold consistency in *. intuition. 
	unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
	destruct H9 with pdinsertion x. intuition.
	- unfold FirstFreeSlotPointerNotNullEq in *.
		pose (H_slotnotnull := H23 pdinsertion currnbfreeslots).
		destruct H_slotnotnull. pose (H_conj := conj H5 H7).
		destruct H22. assumption. unfold pdentryFirstFreeSlot in *.
		rewrite H3 in H22. destruct H22. subst. assumption.
	-	unfold pdentryFirstFreeSlot in *.
		rewrite H3 in H1. subst. rewrite isBELookupEq in H22. destruct H22.
		rewrite H1. trivial.
}
	intro newFirstFreeSlotAddr.
	eapply bindRev.
{	(** Index.pred **)
	eapply weaken. apply Index.pred.
	intros. simpl. split. apply H. intuition.
}
	intro predCurrentNbFreeSlots. simpl.
		eapply bindRev.
	{ (** MAL.writePDFirstFreeSlotPointer **)
		eapply weaken. apply WP.writePDFirstFreeSlotPointer.
		intros. simpl. intuition. destruct H5. exists x. split. assumption.
		assert(isBE newBlockEntryAddr s).
		{
			unfold isBE.
		 	unfold consistency in *. intuition. 
			unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
			destruct H11 with pdinsertion x. intuition.
			- unfold FirstFreeSlotPointerNotNullEq in *.
				pose (H_slotnotnull := H25 pdinsertion currnbfreeslots).
				destruct H_slotnotnull. pose (H_conj := conj H7 H9).
				destruct H24. assumption. unfold pdentryFirstFreeSlot in *.
				rewrite H5 in H24. destruct H24. subst. assumption.
			-	unfold pdentryFirstFreeSlot in *.
				rewrite H5 in H3. subst. rewrite isBELookupEq in H24. destruct H24.
				rewrite H3. trivial.
	}
instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     (*pdentryNbFreeSlots pdinsertion currnbfreeslots s /\ currnbfreeslots > 0 /\*)
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
isBE newBlockEntryAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, (*lookup pdinsertion (memory s0) beqAddr = Some (PDT pdentry)
/\*) s = {|
     currentPartition := currentPartition s0;
     memory := add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr |}
(*consistency s /\*)
	(*  /\  (exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 /\ isBE newBlockEntryAddr s0
		/\ isPDT pdinsertion s0)
). intros. simpl. intuition.
	eexists. rewrite beqAddrTrue.
			split. f_equal. f_equal. intuition.
			- unfold isBE. cbn.
				(* show pdinsertion <> newBlockEntryAddr *)
				unfold pdentryFirstFreeSlot in *. rewrite H5 in H3.
				apply isBELookupEq in H6. destruct H6.
				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeq.
				+ rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. rewrite H6. trivial.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			(*unfold pdentryFirstFreeSlot in *. cbn. rewrite beqAddrTrue. cbn.
			unfold bentryEndAddr in *. repeat rewrite H5 in *. intuition. subst. *)
			- exists s. exists x. intuition.
				unfold isPDT. rewrite H5. trivial.
			(*- exists s. intuition.*)
}	intros. simpl.
(*
		2 : { intros. exact H. }
		unfold MAL.writePDFirstFreeSlotPointer.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
((((*partitionsIsolation s /\
       verticalSharing s /\*)
				P s0 /\
       (exists pdentry : PDTable,
          lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)) /\
          (pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
          currnbfreeslots > 0) (*/\ consistency s *)/\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
     bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s) /\
    StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots)). intuition.
	}
		intro s0. intuition.
		destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		4 : {
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     (*pdentryNbFreeSlots pdinsertion currnbfreeslots s /\ currnbfreeslots > 0 /\*)
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, (*lookup pdinsertion (memory s0) beqAddr = Some (PDT pdentry)
/\*) s = {|
     currentPartition := currentPartition s0;
     memory := add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr |}
  ) /\
	(exists olds : state, P olds)
).
			unfold Monad.modify.
			eapply bindRev. eapply weaken. apply get. intros. simpl.
			pattern s in H. apply H.
			intro ss.
			eapply weaken. apply put.
			intros. simpl. set (s' := {|
      currentPartition :=  _|}).
			eexists. split. rewrite beqAddrTrue. f_equal.
			split. assumption. 
			split. exists ss. exists p. intuition.
			unfold pdentryNbFreeSlots in *. destruct H. destruct H.
			destruct H. destruct H. rewrite Hlookup in H2.
			cbn. rewrite beqAddrTrue. cbn. intuition. intuition.
			(*admit. admit.*)
			exists ss. exists p. intuition.

} }			eapply weaken. apply undefined. intros. intuition. destruct H. congruence.
eapply weaken. apply undefined. intros. intuition. destruct H. congruence.
eapply weaken. apply undefined. intros. intuition. destruct H. congruence.
eapply weaken. apply undefined. intros. intuition. destruct H. congruence.
eapply weaken. apply undefined. intros. intuition. destruct H. congruence. }
		intros. simpl.*)

eapply bindRev.
	{ (**  MAL.writePDNbFreeSlots **)
		eapply weaken. apply WP.writePDNbFreeSlots.
		intros. intuition.
		destruct H. exists x. split. intuition.
instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
isBE newBlockEntryAddr s /\
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
    (* pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, (*lookup pdinsertion (memory s0) beqAddr = Some (PDT pdentry)
/\*)  exists pdentry0 : PDTable, s = {|
     currentPartition := currentPartition s0;
     memory := add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr |}
(*/\
(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)

/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 /\ isBE newBlockEntryAddr s0
/\ isPDT pdinsertion s0
  
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			eexists. split. rewrite beqAddrTrue. f_equal.
			split.
			- unfold isBE. cbn. intuition.
			(* DUP: show pdinsertion <> newBlockEntryAddr *)
				apply isBELookupEq in H. destruct H.
				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeq.
				+ rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. rewrite H. trivial.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- intuition.
			unfold pdentryNbFreeSlots in *. cbn. rewrite beqAddrTrue. cbn. reflexivity.
			destruct H3.
			destruct H2.
			exists x0. exists x1. exists x. subst. intuition.
			unfold s'. f_equal. rewrite H3. intuition. cbn. f_equal.
			rewrite H3. cbn. f_equal.
}	intros. simpl.

(*
		2 : { intros. exact H. }
		unfold MAL.writePDNbFreeSlots.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
exists pd : PDTable,
      lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\
      (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
      bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
      StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
      (exists (s0 : state) (pdentry : PDTable),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add pdinsertion
                     (PDT
                        {|
                        structure := structure pdentry;
                        firstfreeslot := newFirstFreeSlotAddr;
                        nbfreeslots := nbfreeslots pdentry;
                        nbprepare := nbprepare pdentry;
                        parent := parent pdentry;
                        MPU := MPU pdentry |}) (memory s0) beqAddr |})). intuition.
	}
		intro s0. intuition.
		destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		4 : {
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, (*lookup pdinsertion (memory s0) beqAddr = Some (PDT pdentry)
/\*)  exists pdentry0 : PDTable, s = {|
     currentPartition := currentPartition s0;
     memory := add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr |}
  
)).
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			eexists. split. rewrite beqAddrTrue. f_equal.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H.
			destruct H0. destruct H. rewrite Hlookup in H0.
			cbn. rewrite beqAddrTrue. cbn. intuition. intuition.
			destruct H1. intuition.
			destruct H1. intuition. destruct H5. destruct H4.
			exists x0. exists x1. exists p. subst. intuition. }
}
			eapply weaken. apply undefined. intros. intuition. destruct H1. intuition. congruence.
eapply weaken. apply undefined. intros. intuition. destruct H1. intuition. congruence.
eapply weaken. apply undefined. intros. intuition. destruct H1. intuition. congruence.
eapply weaken. apply undefined. intros. intuition. destruct H1. intuition. congruence.
eapply weaken. apply undefined. intros. intuition. destruct H1. intuition. congruence. }
intros. simpl.*)

eapply bindRev.
	{ (**  MAL.writeBlockStartFromBlockEntryAddr **)
		eapply weaken. apply WP.writeBlockStartFromBlockEntryAddr.
		intros. intuition.
		destruct H. intuition. destruct H4. destruct H3. destruct H3.
		assert(HBE : isBE newBlockEntryAddr x0) by intuition.
		apply isBELookupEq in HBE.
		destruct HBE. exists x3. 
		assert(HblockNotPD : beqAddr newBlockEntryAddr pdinsertion = false).
		{		destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
					* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
						rewrite Hbeq in *. unfold isPDT in *. unfold isBE in *.
						destruct (lookup pdinsertion (memory x0) beqAddr) eqn:Hfalse ; try(exfalso ; congruence).
						destruct v eqn:Hvfalse ; try(exfalso ; congruence). intuition.
					* reflexivity.
		}
		split.
		-- 	intuition. rewrite H5. cbn. rewrite beqAddrTrue.
				rewrite beqAddrSym. rewrite HblockNotPD.
						rewrite <- beqAddrFalse in HblockNotPD.
						repeat rewrite removeDupIdentity ; intuition.
				(*destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
					* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
						rewrite Hbeq in *. unfold isPDT in *. unfold isBE in *.
						destruct (lookup pdinsertion (memory x0) beqAddr) eqn:Hfalse ; try(exfalso ; congruence).
						destruct v eqn:Hvfalse ; try(exfalso ; congruence).
					* rewrite beqAddrSym. rewrite Hbeq.
						rewrite <- beqAddrFalse in Hbeq.
						repeat rewrite removeDupIdentity ; intuition.*)
		-- instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
(*isBE newBlockEntryAddr s /\*)
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry newEntry: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry) 
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr |}
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE newEntry) /\
newEntry = (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry))))

(*  /\
(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 /\
(*isBE newBlockEntryAddr s0*)
isPDT pdinsertion s0
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			exists x. split.
			- destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
				+ f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- split.
			(*unfold isBE. cbn. intuition.
			rewrite beqAddrTrue. trivial.
			intuition.*)
			unfold pdentryNbFreeSlots in *. cbn.
			destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
				+ rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
					(*destruct H4. destruct H3. destruct H3.*)
					exists x0. exists x1. exists x2. exists x3. eexists.
					rewrite beqAddrTrue. subst. intuition.
					(*unfold s'. subst. f_equal.*)
					

}	intros. simpl.

(*
		2 : { intros. exact H. }
		unfold MAL.writeBlockStartFromBlockEntryAddr.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
exists pd : PDTable,
      lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
      pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\
      (*predCurrentNbFreeSlots > 0 /\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
      bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
      StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
      (exists (s0 : state) (pdentry pdentry0 : PDTable),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add pdinsertion
                     (PDT
                        {|
                        structure := structure pdentry0;
                        firstfreeslot := firstfreeslot pdentry0;
                        nbfreeslots := predCurrentNbFreeSlots;
                        nbprepare := nbprepare pdentry0;
                        parent := parent pdentry0;
                        MPU := MPU pdentry0 |})
                     (add pdinsertion
                        (PDT
                           {|
                           structure := structure pdentry;
                           firstfreeslot := newFirstFreeSlotAddr;
                           nbfreeslots := nbfreeslots pdentry;
                           nbprepare := nbprepare pdentry;
                           parent := parent pdentry;
                           MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr |})). intuition.
	}
		intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		4 : {
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\ predCurrentNbFreeSlots > 0 /\
     pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry : BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry) 
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr |}
  
)). admit. } }
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}). destruct H. destruct H0. exists x.
			
			split. cbn. admit.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H0.
			destruct H0. rewrite H in H0. admit. intuition. intuition.
			admit. admit. destruct H7. destruct H6. destruct H6.
			exists x0. exists x1. exists x2. exists b. subst. intuition.
			admit. admit. admit. admit. }
intros. simpl.*)

eapply bindRev.
	{ (**  MAL.writeBlockEndFromBlockEntryAddr **)
		eapply weaken. apply WP.writeBlockEndFromBlockEntryAddr.
		intros. intuition.
		destruct H. intuition.
		destruct H3. destruct H2. destruct H2. destruct H2. destruct H2.
		exists x4. intuition.
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
(*isBE newBlockEntryAddr s /\*)
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 newEntry: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE newEntry) /\
newEntry = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry))))

(*  /\
(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 (*/\ isBE newBlockEntryAddr s0*)
/\ isPDT pdinsertion s0
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			intuition. exists x. split.
			- destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
				+ f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- split.
				(*+ unfold isBE. cbn. rewrite beqAddrTrue. trivial.*)
				+ intuition.
					unfold pdentryNbFreeSlots in *. cbn.
					destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
						* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
							subst. congruence.
						* rewrite removeDupIdentity. assumption.
							rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
							exists x0. exists x1. exists x2. exists x3. exists x4.
							rewrite beqAddrTrue. eexists. subst. intuition.
}	intros. simpl.

(*
		2 : { intros. exact H. }
		unfold MAL.writeBlockEndFromBlockEntryAddr.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
exists pd : PDTable,
      lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
      pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\
      predCurrentNbFreeSlots > 0 /\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
      bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
      StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
      (exists (s0 : state) (pdentry pdentry0 : PDTable) (bentry : BlockEntry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) 
                           (accessible bentry) (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
                     (add pdinsertion
                        (PDT
                           {|
                           structure := structure pdentry0;
                           firstfreeslot := firstfreeslot pdentry0;
                           nbfreeslots := predCurrentNbFreeSlots;
                           nbprepare := nbprepare pdentry0;
                           parent := parent pdentry0;
                           MPU := MPU pdentry0 |})
                        (add pdinsertion
                           (PDT
                              {|
                              structure := structure pdentry;
                              firstfreeslot := newFirstFreeSlotAddr;
                              nbfreeslots := nbfreeslots pdentry;
                              nbprepare := nbprepare pdentry;
                              parent := parent pdentry;
                              MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr)
                     beqAddr |})). intuition.
	}
		intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\ predCurrentNbFreeSlots > 0 /\
     pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr |}
  
)).
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}). destruct H. destruct H0. exists x.
			
			split. cbn. admit.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H0.
			destruct H0. rewrite H in H0. admit. intuition. intuition.
			admit. admit. destruct H7. destruct H6. destruct H6. destruct H6.
			exists x0. exists x1. exists x2. exists x3. exists b. subst. intuition.
}
			admit. admit. admit. admit. admit. }
intros. simpl.*)



eapply bindRev.
	{ (**  MAL.writeBlockAccessibleFromBlockEntryAddr **)
		eapply weaken. apply WP.writeBlockAccessibleFromBlockEntryAddr.
		intros. intuition.
		destruct H. intuition.
		destruct H3. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
		 exists x5. intuition.
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
(*isBE newBlockEntryAddr s /\*)
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 newEntry: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE newEntry) /\
newEntry = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1))
/\
bentry1 = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry))))
(*  /\
(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 (*/\ isBE newBlockEntryAddr s0*)
/\ isPDT pdinsertion s0
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			exists x. split.
			- (* DUP *)
				destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
				+ f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- split.
				(*+ unfold isBE. cbn. rewrite beqAddrTrue. trivial.*)
				+ intuition.
					unfold pdentryNbFreeSlots in *. cbn.
					destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
						* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
							subst. congruence.
						* rewrite removeDupIdentity. assumption.
							rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
							exists x0. exists x1. exists x2. exists x3. exists x4. exists x5.
							rewrite beqAddrTrue. eexists. subst. intuition.
}	intros. simpl.

(*
		2 : { intros. exact H. }
		unfold MAL.writeBlockAccessibleFromBlockEntryAddr.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
exists pd : PDTable,
      lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
      pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\
      predCurrentNbFreeSlots > 0 /\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
      bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
      StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
      (exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 : BlockEntry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry0) (write bentry0) 
                           (exec bentry0) (present bentry0) 
                           (accessible bentry0) (blockindex bentry0)
                           (CBlock (startAddr (blockrange bentry0)) endaddr)))
                     (add newBlockEntryAddr
                        (BE
                           (CBlockEntry (read bentry) (write bentry) 
                              (exec bentry) (present bentry) 
                              (accessible bentry) (blockindex bentry)
                              (CBlock startaddr (endAddr (blockrange bentry)))))
                        (add pdinsertion
                           (PDT
                              {|
                              structure := structure pdentry0;
                              firstfreeslot := firstfreeslot pdentry0;
                              nbfreeslots := predCurrentNbFreeSlots;
                              nbprepare := nbprepare pdentry0;
                              parent := parent pdentry0;
                              MPU := MPU pdentry0 |})
                           (add pdinsertion
                              (PDT
                                 {|
                                 structure := structure pdentry;
                                 firstfreeslot := newFirstFreeSlotAddr;
                                 nbfreeslots := nbfreeslots pdentry;
                                 nbprepare := nbprepare pdentry;
                                 parent := parent pdentry;
                                 MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr)
                        beqAddr) beqAddr |})). intuition.
	}
		intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\ predCurrentNbFreeSlots > 0 /\
     pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
  
)).
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}). destruct H. destruct H0. exists x.
			
			split. cbn. admit.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H0.
			destruct H0. rewrite H in H0. admit. intuition. intuition.
			admit. admit. destruct H7. destruct H6. destruct H6. destruct H6. destruct H6.
			exists x0. exists x1. exists x2. exists x3. exists x4. exists b. subst. intuition.
}
			admit. admit. admit. admit. admit. }
intros. simpl.*)

eapply bindRev.
	{ (**  MAL.writeBlockPresentFromBlockEntryAddr **)
		eapply weaken. apply WP.writeBlockPresentFromBlockEntryAddr.
		intros. intuition.
		destruct H. intuition.
		destruct H3. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
		destruct H2.
		 exists x6. intuition.
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
(*isBE newBlockEntryAddr s /\*)
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 newEntry: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE newEntry) /\
newEntry = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1))
/\
bentry1 = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry))))

(*    /\
(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 (*/\ isBE newBlockEntryAddr s0*)
/\ isPDT pdinsertion s0
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			exists x. split.
			- (* DUP *)
				destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
				+ f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- split.
				(*+ unfold isBE. cbn. rewrite beqAddrTrue. trivial.*)
				+ intuition.
					unfold pdentryNbFreeSlots in *. cbn.
					destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
						* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
							subst. congruence.
						* rewrite removeDupIdentity. assumption.
							rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
							exists x0. exists x1. exists x2. exists x3. exists x4. exists x5.
							exists x6.
							rewrite beqAddrTrue. eexists. subst. intuition.
}	intros. simpl.

(*
		2 : { intros. exact H. }
		unfold MAL.writeBlockPresentFromBlockEntryAddr.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
exists pd : PDTable,
      lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
      pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\
      predCurrentNbFreeSlots > 0 /\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
      bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
      StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
      (exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0
                                                    bentry1 : BlockEntry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry1) (write bentry1) 
                           (exec bentry1) (present bentry1) true 
                           (blockindex bentry1) (blockrange bentry1)))
                     (add newBlockEntryAddr
                        (BE
                           (CBlockEntry (read bentry0) (write bentry0) 
                              (exec bentry0) (present bentry0) 
                              (accessible bentry0) (blockindex bentry0)
                              (CBlock (startAddr (blockrange bentry0)) endaddr)))
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry) 
                                 (write bentry) (exec bentry) 
                                 (present bentry) (accessible bentry)
                                 (blockindex bentry)
                                 (CBlock startaddr (endAddr (blockrange bentry)))))
                           (add pdinsertion
                              (PDT
                                 {|
                                 structure := structure pdentry0;
                                 firstfreeslot := firstfreeslot pdentry0;
                                 nbfreeslots := predCurrentNbFreeSlots;
                                 nbprepare := nbprepare pdentry0;
                                 parent := parent pdentry0;
                                 MPU := MPU pdentry0 |})
                              (add pdinsertion
                                 (PDT
                                    {|
                                    structure := structure pdentry;
                                    firstfreeslot := newFirstFreeSlotAddr;
                                    nbfreeslots := nbfreeslots pdentry;
                                    nbprepare := nbprepare pdentry;
                                    parent := parent pdentry;
                                    MPU := MPU pdentry |}) 
                                 (memory s0) beqAddr) beqAddr) beqAddr) beqAddr)
                     beqAddr |})). intuition.
	}
		intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\ predCurrentNbFreeSlots > 0 /\
     pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
  
)).
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}). destruct H. destruct H0. exists x.
			
			split. cbn. admit.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H0.
			destruct H0. rewrite H in H0. admit. intuition. intuition.
			admit. admit. destruct H7. destruct H6. destruct H6. destruct H6. destruct H6.
			destruct H6.
			exists x0. exists x1. exists x2. exists x3. exists x4. exists x5.
			exists b. subst. intuition.
}
			admit. admit. admit. admit. admit. }
intros. simpl. *)

eapply bindRev.
	{ (**  MAL.writeBlockRFromBlockEntryAddr **)
		eapply weaken. apply WP.writeBlockRFromBlockEntryAddr.
		intros. intuition.
		destruct H. intuition.
		destruct H3. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
		destruct H2. destruct H2.
		 exists x7. intuition.
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
(*isBE newBlockEntryAddr s /\*)
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 newEntry: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE newEntry) /\
newEntry = (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))
/\
bentry3 = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1))
/\
bentry1 = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry))))
(*      /\
(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 (*/\ isBE newBlockEntryAddr s0*)
/\ isPDT pdinsertion s0
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			exists x. split.
			- (* DUP *)
				destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
				+ f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- split.
				(*+ unfold isBE. cbn. rewrite beqAddrTrue. trivial.*)
				+ intuition.
					unfold pdentryNbFreeSlots in *. cbn.
					destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
						* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
							subst. congruence.
						* rewrite removeDupIdentity. assumption.
							rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
							exists x0. exists x1. exists x2. exists x3. exists x4. exists x5.
							exists x6. exists x7.
							rewrite beqAddrTrue. eexists. subst. intuition.
}	intros. simpl.


(*
		2 : { intros. exact H. }
		unfold MAL.writeBlockRFromBlockEntryAddr.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
exists pd : PDTable,
      lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
      pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\
      predCurrentNbFreeSlots > 0 /\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
      bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
      StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
      (exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1
                                                    bentry2 : BlockEntry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry2) (write bentry2) 
                           (exec bentry2) true (accessible bentry2)
                           (blockindex bentry2) (blockrange bentry2)))
                     (add newBlockEntryAddr
                        (BE
                           (CBlockEntry (read bentry1) (write bentry1) 
                              (exec bentry1) (present bentry1) true
                              (blockindex bentry1) (blockrange bentry1)))
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry0) 
                                 (write bentry0) (exec bentry0) 
                                 (present bentry0) (accessible bentry0)
                                 (blockindex bentry0)
                                 (CBlock (startAddr (blockrange bentry0)) endaddr)))
                           (add newBlockEntryAddr
                              (BE
                                 (CBlockEntry (read bentry) 
                                    (write bentry) (exec bentry) 
                                    (present bentry) (accessible bentry)
                                    (blockindex bentry)
                                    (CBlock startaddr (endAddr (blockrange bentry)))))
                              (add pdinsertion
                                 (PDT
                                    {|
                                    structure := structure pdentry0;
                                    firstfreeslot := firstfreeslot pdentry0;
                                    nbfreeslots := predCurrentNbFreeSlots;
                                    nbprepare := nbprepare pdentry0;
                                    parent := parent pdentry0;
                                    MPU := MPU pdentry0 |})
                                 (add pdinsertion
                                    (PDT
                                       {|
                                       structure := structure pdentry;
                                       firstfreeslot := newFirstFreeSlotAddr;
                                       nbfreeslots := nbfreeslots pdentry;
                                       nbprepare := nbprepare pdentry;
                                       parent := parent pdentry;
                                       MPU := MPU pdentry |}) 
                                    (memory s0) beqAddr) beqAddr) beqAddr) beqAddr)
                        beqAddr) beqAddr |})). intuition.
	}
		intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\ predCurrentNbFreeSlots > 0 /\
     pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
  
)).
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}). destruct H. destruct H0. exists x.
			
			split. cbn. admit.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H0.
			destruct H0. rewrite H in H0. admit. intuition. intuition.
			admit. admit. destruct H7. destruct H6. destruct H6. destruct H6. destruct H6.
			destruct H6. destruct H6.
			exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
			exists b. subst. intuition.
}
			admit. admit. admit. admit. admit. }
intros. simpl.*)

eapply bindRev.
	{ (**  MAL.writeBlockWFromBlockEntryAddr **)
		eapply weaken. apply WP.writeBlockWFromBlockEntryAddr.
		intros. intuition.
		destruct H. intuition.
		destruct H3. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
		destruct H2. destruct H2. destruct H2.
		 exists x8. intuition.
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
(*isBE newBlockEntryAddr s /\*)
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 newEntry: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE newEntry) /\
newEntry = (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4))
/\
bentry4 = (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))
/\
bentry3 = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1))
/\
bentry1 = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry))))
(*        /\
(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 (*/\ isBE newBlockEntryAddr s0*)
/\ isPDT pdinsertion s0
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			exists x. split.
			- (* DUP *)
				destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
				+ f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- split.
				(*+ unfold isBE. cbn. rewrite beqAddrTrue. trivial.*)
				+ intuition.
					unfold pdentryNbFreeSlots in *. cbn.
					destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
						* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
							subst. congruence.
						* rewrite removeDupIdentity. assumption.
							rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
							exists x0. exists x1. exists x2. exists x3. exists x4. exists x5.
							exists x6. exists x7. exists x8.
							rewrite beqAddrTrue. eexists. subst. intuition.
}	intros. simpl.

(*
		2 : { intros. exact H. }
		unfold MAL.writeBlockWFromBlockEntryAddr.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
exists pd : PDTable,
      lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
      pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\
      predCurrentNbFreeSlots > 0 /\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
      bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
      StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
      (exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 : BlockEntry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add newBlockEntryAddr
                     (BE
                        (CBlockEntry r (write bentry3) (exec bentry3)
                           (present bentry3) (accessible bentry3)
                           (blockindex bentry3) (blockrange bentry3)))
                     (add newBlockEntryAddr
                        (BE
                           (CBlockEntry (read bentry2) (write bentry2) 
                              (exec bentry2) true (accessible bentry2)
                              (blockindex bentry2) (blockrange bentry2)))
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry1) 
                                 (write bentry1) (exec bentry1) 
                                 (present bentry1) true (blockindex bentry1)
                                 (blockrange bentry1)))
                           (add newBlockEntryAddr
                              (BE
                                 (CBlockEntry (read bentry0) 
                                    (write bentry0) (exec bentry0) 
                                    (present bentry0) (accessible bentry0)
                                    (blockindex bentry0)
                                    (CBlock (startAddr (blockrange bentry0)) endaddr)))
                              (add newBlockEntryAddr
                                 (BE
                                    (CBlockEntry (read bentry) 
                                       (write bentry) (exec bentry) 
                                       (present bentry) (accessible bentry)
                                       (blockindex bentry)
                                       (CBlock startaddr
                                          (endAddr (blockrange bentry)))))
                                 (add pdinsertion
                                    (PDT
                                       {|
                                       structure := structure pdentry0;
                                       firstfreeslot := firstfreeslot pdentry0;
                                       nbfreeslots := predCurrentNbFreeSlots;
                                       nbprepare := nbprepare pdentry0;
                                       parent := parent pdentry0;
                                       MPU := MPU pdentry0 |})
                                    (add pdinsertion
                                       (PDT
                                          {|
                                          structure := structure pdentry;
                                          firstfreeslot := newFirstFreeSlotAddr;
                                          nbfreeslots := nbfreeslots pdentry;
                                          nbprepare := nbprepare pdentry;
                                          parent := parent pdentry;
                                          MPU := MPU pdentry |}) 
                                       (memory s0) beqAddr) beqAddr) beqAddr) beqAddr)
                           beqAddr) beqAddr) beqAddr |})). intuition.
	}
		intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\ predCurrentNbFreeSlots > 0 /\
     pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
  
)).
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}). destruct H. destruct H0. exists x.
			
			split. cbn. admit.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H0.
			destruct H0. rewrite H in H0. admit. intuition. intuition.
			admit. admit. destruct H7. destruct H6. destruct H6. destruct H6. destruct H6.
			destruct H6. destruct H6. destruct H6.
			exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
			exists x7.
			exists b. subst. intuition.
}
			admit. admit. admit. admit. admit. }
intros. simpl.*)

eapply bindRev.
	{ (**  MAL.writeBlockXFromBlockEntryAddr **)
		eapply weaken. apply WP.writeBlockXFromBlockEntryAddr.
		intros. intuition.
		destruct H. intuition.
		(*apply isBELookupEq in H.
		destruct H. exists x0. split. assumption.*)
							destruct H3. destruct H2. destruct H2. destruct H2.
							destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
						exists x9. intuition.

			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
(*isBE newBlockEntryAddr s /\*)

pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, ( exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 newEntry : BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry5) (write bentry5) e (present bentry5) 
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5))
											(*newEntry*)
) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE newEntry) /\
newEntry = (CBlockEntry (read bentry5) (write bentry5) e (present bentry5) 
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5))
/\
bentry5 = (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4))
/\
bentry4 = (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))
/\
bentry3 = (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))
/\
bentry2 = (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1))
/\
bentry1 = (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr))
/\
bentry0 = (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry))))
(*/\ (*exists newEntry : BlockEntry,*)
(*lookup newBlockEntryAddr (memory s) beqAddr = (*Some (BE newEntry)*)*)
bentry5 = 
(CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
    (accessible bentry4) (blockindex bentry4) (blockrange bentry4))*)
)          /\
(*(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 (*/\ isBE newBlockEntryAddr s0*)
/\ isPDT pdinsertion s0

)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			exists x. split.
			- (* DUP *)
				destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
				+ f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- split.
				(*+ unfold isBE. cbn. rewrite beqAddrTrue. trivial.*)
				+ intuition.
					unfold pdentryNbFreeSlots in *. cbn.
					destruct (beqAddr newBlockEntryAddr pdinsertion) eqn:Hbeq.
						* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
							subst. congruence.
						* rewrite removeDupIdentity. assumption.
							rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
							exists x0. intuition. exists x1. exists x2. exists x3. exists x4. exists x5.
							exists x6. exists x7. exists x8. exists x9.
							rewrite beqAddrTrue. eexists.
							intuition. unfold s'. rewrite H3. f_equal.

(*
							cbn in H. repeat rewrite beqAddrTrue in H.
							lia. rewrite f_equal in H.
							contradict H. rewrite H4.
							unfold not. f_equal. contradict H4.
							destruct H4 as [HHH].
							pose (HHHHH := f_equal None H4).

apply (f_equal option) in H4. reflexivity.
About f_equal.
							apply Some in H.
							assert(blockindex x0 = blockindex x5).
							apply (f_equal Some) in H.
							destruct x0. unfold CBlockEntry in H.
							destruct (lt_dec (ADT.blockindex x9) kernelStructureEntriesNb) eqn:Htest ; try(exfalso ; congruence).
							simpl in H.

							Search (Some ?x = Some ?y). destruct Some eqn:HSome in H .
							destruct v eqn:Hvv in H.

rewrite f_equal in H.
							(*unfold s'. subst. f_equal.*)*)
}	intros. simpl.


(*
		2 : { intros. exact H. }
		unfold MAL.writeBlockXFromBlockEntryAddr.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
exists pd : PDTable,
      lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
      pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\
      predCurrentNbFreeSlots > 0 /\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
      bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
      StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
      (exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 bentry4 : BlockEntry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry4) w (exec bentry4)
                           (present bentry4) (accessible bentry4)
                           (blockindex bentry4) (blockrange bentry4)))
                     (add newBlockEntryAddr
                        (BE
                           (CBlockEntry r (write bentry3) 
                              (exec bentry3) (present bentry3) 
                              (accessible bentry3) (blockindex bentry3)
                              (blockrange bentry3)))
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry2) 
                                 (write bentry2) (exec bentry2) true
                                 (accessible bentry2) (blockindex bentry2)
                                 (blockrange bentry2)))
                           (add newBlockEntryAddr
                              (BE
                                 (CBlockEntry (read bentry1) 
                                    (write bentry1) (exec bentry1) 
                                    (present bentry1) true 
                                    (blockindex bentry1) 
                                    (blockrange bentry1)))
                              (add newBlockEntryAddr
                                 (BE
                                    (CBlockEntry (read bentry0) 
                                       (write bentry0) (exec bentry0)
                                       (present bentry0) 
                                       (accessible bentry0) 
                                       (blockindex bentry0)
                                       (CBlock (startAddr (blockrange bentry0))
                                          endaddr)))
                                 (add newBlockEntryAddr
                                    (BE
                                       (CBlockEntry (read bentry) 
                                          (write bentry) 
                                          (exec bentry) (present bentry)
                                          (accessible bentry) 
                                          (blockindex bentry)
                                          (CBlock startaddr
                                             (endAddr (blockrange bentry)))))
                                    (add pdinsertion
                                       (PDT
                                          {|
                                          structure := structure pdentry0;
                                          firstfreeslot := firstfreeslot pdentry0;
                                          nbfreeslots := predCurrentNbFreeSlots;
                                          nbprepare := nbprepare pdentry0;
                                          parent := parent pdentry0;
                                          MPU := MPU pdentry0 |})
                                       (add pdinsertion
                                          (PDT
                                             {|
                                             structure := structure pdentry;
                                             firstfreeslot := newFirstFreeSlotAddr;
                                             nbfreeslots := nbfreeslots pdentry;
                                             nbprepare := nbprepare pdentry;
                                             parent := parent pdentry;
                                             MPU := MPU pdentry |}) 
                                          (memory s0) beqAddr) beqAddr) beqAddr)
                                 beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |})). intuition.
	}
		intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		{ (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\ predCurrentNbFreeSlots > 0 /\
     pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5: BlockEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry5) (write bentry5) e (present bentry5) 
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
  
)).
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}). destruct H. destruct H0. exists x.
			
			split. cbn. admit.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H0.
			destruct H0. rewrite H in H0. admit. intuition. intuition.
			admit. admit. destruct H7. destruct H6. destruct H6. destruct H6. destruct H6.
			destruct H6. destruct H6. destruct H6. destruct H6.
			exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
			exists x7. exists x8.
			exists b. subst. intuition.
}
			admit. admit. admit. admit. admit. }
intros. simpl.*)

eapply bindRev.
	{ (**  MAL.writeSCOriginFromBlockEntryAddr **)
		eapply weaken. apply writeSCOriginFromBlockEntryAddr.
		intros. simpl. destruct H. destruct H.
		assert(HSCE : wellFormedShadowCutIfBlockEntry s).
		{ unfold wellFormedShadowCutIfBlockEntry. intros. simpl.
			exists (CPaddr (pa + scoffset)). intuition.

			intuition. destruct H4 as [s0].
		destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3.
		destruct H3. destruct H3. destruct H3. destruct H3. destruct H3.
			assert(HSCEEq : isSCE (CPaddr (pa + scoffset)) s = isSCE (CPaddr (pa + scoffset)) s0).
			{
				intuition. rewrite H5. unfold isSCE. cbn.
				destruct (beqAddr newBlockEntryAddr (CPaddr (pa + scoffset))) eqn:Hbeq.
			rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
			rewrite <- Hbeq.
			assert (HBE : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE x2)) by intuition.
			rewrite HBE.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
			destruct v eqn:Hv ; try congruence. intuition.
		
			repeat rewrite beqAddrTrue.
			destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			unfold isPDT in *. unfold isBE in *. rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
			rewrite Hbeqpdblock in *.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.
			rewrite Hbeqpdblock in *.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
			cbn.

			destruct (beqAddr pdinsertion (CPaddr (pa + scoffset))) eqn:Hbeqpdpa ; try congruence.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			rewrite <- Hbeqpdpa. assert(HPDT : isPDT pdinsertion s0) by intuition.
			apply isPDTLookupEq in HPDT. destruct HPDT.
			rewrite H19. trivial.

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			}
			rewrite HSCEEq.
			assert(Hcons : wellFormedShadowCutIfBlockEntry s0) by
			(unfold consistency in * ; intuition).
			unfold wellFormedShadowCutIfBlockEntry in Hcons.
			assert(HBEEq : isBE pa s = isBE pa s0).
			{
				intuition. rewrite H5. unfold isBE. cbn. repeat rewrite beqAddrTrue.

				destruct (beqAddr newBlockEntryAddr pa) eqn:Hbeq.
				rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
				rewrite <- Hbeq.
				assert (HBE : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE x2)) by intuition.
			rewrite HBE. trivial.

				rewrite <- beqAddrFalse in *.

				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				unfold isPDT in *. unfold isBE in *. (* subst.*)
				destruct (lookup pa (memory s) beqAddr) eqn:Hpa ; try(exfalso ; congruence).
				repeat rewrite removeDupIdentity ; intuition.
				
				cbn.
				(*rewrite Hbeqpdblock.
				repeat rewrite removeDupIdentity ; intuition.
				cbn.*)

				destruct (beqAddr pdinsertion pa) eqn:Hbeqpdpa.
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				rewrite <- Hbeqpdpa.
				assert(HPDT : isPDT pdinsertion s0) by intuition.
				apply isPDTLookupEq in HPDT. destruct HPDT.
				rewrite H19. trivial.
				

				rewrite <- beqAddrFalse in *.

				repeat rewrite removeDupIdentity ; intuition.
			}
			rewrite HBEEq in *.
			specialize (Hcons pa H1).
			destruct Hcons. intuition.
			rewrite H9 in *. intuition.
}
intuition.
- 	destruct H3 as [s0].
		destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
		destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
		apply isBELookupEq.
		assert(Hnewblocks : lookup newBlockEntryAddr (memory s) beqAddr = Some (BE x9)) by intuition.
		exists x9. intuition.
(*- 		assert(Hcons2 : forall blockentryaddr : paddr, forall entry : BlockEntry,
lookup blockentryaddr (memory s) beqAddr = Some (BE entry) ->
bentryBlockIndex blockentryaddr entry.(blockindex) s ->
isBE (CPaddr (blockentryaddr - entry.(blockindex))) s).
{ 
intros. simpl.*)

	- unfold KernelStructureStartFromBlockEntryAddrIsBE. intros. simpl.
		destruct H3 as [s0].
		destruct H3. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3.
		destruct H3. destruct H3. destruct H3. destruct H3. destruct H3.



		assert(isBE (CPaddr (blockentryaddr - blockindex entry)) s = isBE (CPaddr (blockentryaddr - blockindex entry)) s0).
		{ intuition. rewrite H6. unfold isBE. cbn.
		
			destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeq.
			rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
			rewrite <- Hbeq.
			assert (HBE :  lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE x2)) by intuition.
			rewrite HBE ; trivial.
			(*destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
			destruct v eqn:Hv ; try congruence ; intuition.*)

			repeat rewrite beqAddrTrue.
			destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			unfold isPDT in *. unfold isBE in *. rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
			rewrite Hbeqpdblock in *.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.
			rewrite Hbeqpdblock in *.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
			cbn.

			destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdpa ; try congruence.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			rewrite <- Hbeqpdpa.
			assert(HPDT : isPDT pdinsertion s0) by intuition.
			apply isPDTLookupEq in HPDT. destruct HPDT.
			rewrite H20. trivial.

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
		}
			(*rewrite H6.*)
			(*assert(HHcons : forall blockentryaddr : paddr, 
isBE blockentryaddr s0 ->
exists entry : BlockEntry, isBE (CPaddr (blockentryaddr - entry.(blockindex))) s0).
			admit.*)
	
			rewrite H6.
			




		(*	assert(Hcons2 : forall blockentryaddr : paddr, forall entry : BlockEntry,
lookup blockentryaddr (memory s0) beqAddr = Some (BE entry)->
exists entry' : BlockEntry,
lookup (CPaddr (blockentryaddr - entry.(blockindex))) (memory s0) beqAddr = Some (BE entry')).
admit.

			assert (exists entry' : BlockEntry,
lookup (CPaddr (blockentryaddr - entry.(blockindex))) (memory s) beqAddr = Some (BE entry')).
			(*eexists.*)
{*)

			(*destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry)) ) eqn:Hbeq ; try intuition.*)
			(*+ (* newBlockEntryAddr = (CPaddr (blockentryaddr - blockindex x9)) *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				rewrite <- Hbeq in *. assumption.*)
			(* pdinsertion <> newBlockEntryAddr *)
				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock ; try (exfalso ; congruence).
				++ (* pdinsertion = newBlockEntryAddr *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in *.
						(*assert(HBE : isBE newBlockEntryAddr s0) by intuition.
						apply isBELookupEq in HBE. destruct HBE as [HBEx HBE'].*)
						assert(HBE : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE x2)) by intuition.
						unfold isPDT in *. rewrite Hbeqpdblock in *. rewrite HBE in *. intuition.
				++ (* pdinsertion <> newBlockEntryAddr *)
						
						(*rewrite H4. cbn. repeat rewrite beqAddrTrue.*)
					destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdblock' ; try (exfalso ; congruence).
					+++ (* newBlockEntryAddr = (CPaddr (blockentryaddr - blockindex entry)) *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in *.
							rewrite <- Hbeqpdblock' in *. intuition.
							unfold isBE.
							assert(HBE : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE x2)) by intuition.
							rewrite HBE. trivial.
					+++ (* newBlockEntryAddr <> (CPaddr (blockentryaddr - blockindex entry)) *)
							destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdblock'' ; try (exfalso ; congruence).
							++++ (* pdinsertion = (CPaddr (blockentryaddr - blockindex entry)) *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in *.
									(* prove false by exploring the values of blockentryaddr *)
									destruct (beqAddr pdinsertion blockentryaddr) eqn:Hbeqpdpa ; try (exfalso ; congruence) ; trivial.
								+ (* pdinsertion = blockentryaddr *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in *.
									rewrite Hbeqpdpa in *.
									congruence.
								+ (* pdinsertion <> blockentryaddr *)
									destruct (beqAddr blockentryaddr newBlockEntryAddr) eqn:Hbeqblocknew ; try(exfalso ;congruence).
									* (* blockentryaddr = newBlockEntryAddr *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in *.
										unfold bentryBlockIndex in *.
										rewrite Hbeqblocknew in *. intuition.
										rewrite H9 in *. intuition.
										rewrite H21.
										assert(blockindex x9 = blockindex x7).
										{ rewrite H11. rewrite H13.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x7) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x7) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. reflexivity. destruct blockentry_d. destruct x7.
										intuition.
										}
										assert(blockindex x7 = blockindex x5).
										{ rewrite H15. rewrite H17.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x5) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x5) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. reflexivity. destruct blockentry_d. destruct x5.
										intuition.
										}
										assert(blockindex x5 = blockindex x3).
										{ rewrite H18. rewrite H20.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x3) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x3) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. reflexivity. destruct blockentry_d. destruct x3.
										intuition.
										}
										assert(blockindex x3 = blockindex x2).
										{ rewrite H22.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x2) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x2) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. destruct blockentry_d. destruct x2.
										intuition.
										}
										(*rewrite H8 in *. intuition.*)
										assert(Hblockindex : blockindex entry = blockindex x9) by intuition.
										(*rewrite Hblockindex.*)
										(*assert(Hcons2 : forall blockentryaddr : paddr, forall entry : BlockEntry,
lookup blockentryaddr (memory s0) beqAddr = Some (BE entry) ->
bentryBlockIndex blockentryaddr entry.(blockindex) s0 ->
isBE (CPaddr (blockentryaddr - entry.(blockindex))) s0).*)
											assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0) by
											(unfold consistency in * ; intuition).
										assert(Hblocks0 : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE x2)) by intuition.
										specialize (Hcons newBlockEntryAddr x2 Hblocks0).
										rewrite <- H26 in *. rewrite <- H25 in *. rewrite <- H24 in *.
										rewrite <- H4 in *.
										apply Hcons.
										unfold bentryBlockIndex. rewrite Hblocks0. intuition.
										rewrite <- H21. intuition.
							* (*blockentryaddr <> newBlockEntryAddr *)
								(* prove entry didn't change from s0 to s, so we can prove s0 *)
								intuition. rewrite H7 in H2. cbn in H2. rewrite beqAddrTrue in H2.
								rewrite Hbeqpdblock in *.
								rewrite beqAddrSym in H2.
								rewrite Hbeqblocknew in *.
								rewrite <- beqAddrFalse in *.
								do 6 rewrite removeDupIdentity in H2; intuition.
								cbn in H2.
								destruct (beqAddr pdinsertion blockentryaddr) eqn:Hpdpa ; intuition ; try(exfalso ; congruence).
								rewrite beqAddrTrue in H2.
								rewrite <- beqAddrFalse in *.
								do 3 rewrite removeDupIdentity in H2; intuition.
								assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0) by
											(unfold consistency in * ; intuition).
								assert(Hblocks0 : lookup blockentryaddr (memory s0) beqAddr = Some (BE entry)) by intuition.
								specialize (Hcons blockentryaddr entry Hblocks0).
								apply Hcons.
								unfold bentryBlockIndex. rewrite Hblocks0. intuition.
								destruct entry. cbn. intuition.
				++++ (* pdinsertion <> (CPaddr (blockentryaddr - blockindex entry) *)
							(* it can be any values that hasn't been modified in the state,
									so if it is true at s0 then it should stay true with s *)
							(* DUP : redo the previous proof with blockentryaddr = newBlockEntryAddr,
									pdinsertion or none of them *)
									(* prove false by exploring the values of blockentryaddr *)
									destruct (beqAddr pdinsertion blockentryaddr) eqn:Hbeqpdpa ; try (exfalso ; congruence) ; trivial.
								+ (* pdinsertion = blockentryaddr *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in *.
									rewrite Hbeqpdpa in *.
									congruence.
								+ (* pdinsertion <> blockentryaddr *)
									destruct (beqAddr blockentryaddr newBlockEntryAddr) eqn:Hbeqblocknew ; try(exfalso ;congruence).
									* (* blockentryaddr = newBlockEntryAddr *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in *.
										unfold bentryBlockIndex in *.
										rewrite Hbeqblocknew in *. intuition.
										rewrite H9 in *. intuition.
										rewrite H21.
										assert(blockindex x9 = blockindex x7).
										{ rewrite H11. rewrite H13.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x7) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x7) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. reflexivity. destruct blockentry_d. destruct x7.
										intuition.
										}
										assert(blockindex x7 = blockindex x5).
										{ rewrite H15. rewrite H17.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x5) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x5) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. reflexivity. destruct blockentry_d. destruct x5.
										intuition.
										}
										assert(blockindex x5 = blockindex x3).
										{ rewrite H18. rewrite H20.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x3) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x3) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. reflexivity. destruct blockentry_d. destruct x3.
										intuition.
										}
										assert(blockindex x3 = blockindex x2).
										{ rewrite H22.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x2) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x2) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. destruct blockentry_d. destruct x2.
										intuition.
										}
										(*rewrite H8 in *. intuition.*)
										assert(Hblockindex : blockindex entry = blockindex x9) by intuition.
										(*rewrite Hblockindex.*)
										(*assert(Hcons2 : forall blockentryaddr : paddr, forall entry : BlockEntry,
lookup blockentryaddr (memory s0) beqAddr = Some (BE entry) ->
bentryBlockIndex blockentryaddr entry.(blockindex) s0 ->
isBE (CPaddr (blockentryaddr - entry.(blockindex))) s0).*)
											assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0) by
											(unfold consistency in * ; intuition).
										assert(Hblocks0 : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE x2)) by intuition.
										specialize (Hcons newBlockEntryAddr x2 Hblocks0).
										rewrite <- H26 in *. rewrite <- H25 in *. rewrite <- H24 in *.
										rewrite <- H4 in *.
										apply Hcons.
										unfold bentryBlockIndex. rewrite Hblocks0. intuition.
										rewrite <- H21. intuition.
							* (*blockentryaddr <> newBlockEntryAddr *)
								(* prove entry didn't change from s0 to s, so we can prove s0 *)
								intuition. rewrite H7 in H2. cbn in H2. rewrite beqAddrTrue in H2.
								rewrite Hbeqpdblock in *.
								rewrite beqAddrSym in H2.
								rewrite Hbeqblocknew in *.
								rewrite <- beqAddrFalse in *.
								do 6 rewrite removeDupIdentity in H2; intuition.
								cbn in H2.
								destruct (beqAddr pdinsertion blockentryaddr) eqn:Hpdpa ; intuition ; try(exfalso ; congruence).
								rewrite beqAddrTrue in H2.
								rewrite <- beqAddrFalse in *.
								do 3 rewrite removeDupIdentity in H2; intuition.
								assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0) by
											(unfold consistency in * ; intuition).
								assert(Hblocks0 : lookup blockentryaddr (memory s0) beqAddr = Some (BE entry)) by intuition.
								specialize (Hcons blockentryaddr entry Hblocks0).
								apply Hcons.
								unfold bentryBlockIndex. rewrite Hblocks0. intuition.
								destruct entry. cbn. intuition.
- (* we know newBlockEntryAddr is BE and that the ShadoCut is well formed, so we
			know SCE exists *)
		unfold wellFormedShadowCutIfBlockEntry in *.
		destruct H3 as [s0].
		destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
		destruct H2. destruct H2. destruct H2. destruct H2. destruct H2.
		intuition.
		assert(HBE : lookup newBlockEntryAddr (memory s) beqAddr = Some (BE x9)) by intuition.
		specialize (HSCE newBlockEntryAddr).
		unfold isBE in HSCE. rewrite HBE in *. destruct HSCE ; trivial.
		intuition. apply isSCELookupEq in H20. destruct H20. rewrite H21 in *.
		exists x11. intuition.
-
		


destruct ( beqAddr pdinsertion newBlockEntryAddr ) eqn:Hfalse ; try (intuition ; exfalso ; congruence). (* why need to do this ? since we checked it befre ? *)
							(* pdinsertion <> newBlockEntryAddr *)
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
							cbn.
							destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - 0))) eqn:Hbeqpdblock'' ; try (exfalso ; congruence).
							++++ (* pdinsertion = (CPaddr (blockentryaddr - blockindex entry)) *)
									(* prove false because can't be PDT and BE at the same time*)
									rewrite Haddr in *.	rewrite <- DependentTypeLemmas.beqAddrTrue in *.
									rewrite <- Hbeqpdblock'' in *.
									assert(HPDT : isPDT pdinsertion s0) by intuition.
									apply isPDTLookupEq in HPDT. destruct HPDT. congruence.
(*
									rewrite H4 in H5.
									cbn in H5.
									repeat rewrite beqAddrTrue in H3.
									rewrite <- DependentTypeLemmas.beqAddrTrue in *.
									rewrite <- beqAddrFalse in *.
									rewrite beqAddrSym in H3.
									cbn in H3.*)
							++++ 							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
										cbn.
									rewrite Haddr in *.
									
					
				* (* pdinsertion <> newBlockEntryAddr *)
					rewrite H4 in H3. cbn in H3. rewrite beqAddrTrue in *.
											rewrite <- beqAddrFalse in *.
							do 6 rewrite removeDupIdentity in H3; intuition.
					repeat rewrite beqAddrTrue in H3.
					rewrite beqAddrSym in H3.
					
					destruct (beqAddr blockentryaddr newBlockEntryAddr ) eqn:Hffalse  in H3 ; try (rewrite <- DependentTypeLemmas.beqAddrTrue in * ; exfalso ; congruence).
					destruct (beqAddr pdinsertion newBlockEntryAddr ) eqn:Hfffalse  in H3 ; try (rewrite <- DependentTypeLemmas.beqAddrTrue in * ; exfalso ; congruence).
					cbn in H3.
					destruct (beqAddr pdinsertion blockentryaddr ) eqn:Hffffalse  in H3 ; try (rewrite <- DependentTypeLemmas.beqAddrTrue in * ; exfalso ; congruence).
					rewrite <- beqAddrFalse in *.
					cbn in H3.
					do 3 rewrite removeDupIdentity in H3; intuition. exists entry. intuition.

	- simpl in *. cbn in *.
						rewrite H4. cbn. repeat rewrite beqAddrTrue.
					destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - 0))) eqn:Hbeqpdblock' ; try (exfalso ; congruence).
					+++ (* newBlockEntryAddr = (CPaddr (blockentryaddr - blockindex entry)) *)
							eexists. intuition. 
					+++ (* newBlockEntryAddr <> (CPaddr (blockentryaddr - blockindex entry)) *)
							destruct ( beqAddr pdinsertion newBlockEntryAddr ) eqn:Hfalse ; try (intuition ; exfalso ; congruence). (* why need to do this ? since we checked it befre ? *)
							(* pdinsertion <> newBlockEntryAddr *)
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
							cbn.
							destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - 0))) eqn:Hbeqpdblock'' ; try (exfalso ; congruence).
							++++ (* pdinsertion = (CPaddr (blockentryaddr - blockindex entry)) *)
									(* prove false because can't be PDT and BE at the same time*)
									rewrite Haddr in *.	rewrite <- DependentTypeLemmas.beqAddrTrue in *.
									rewrite <- Hbeqpdblock'' in *.
									assert(HPDT : isPDT pdinsertion s0) by intuition.
									apply isPDTLookupEq in HPDT. destruct HPDT. congruence.
(*
									rewrite H4 in H3.
									cbn in H3.
									repeat rewrite beqAddrTrue in H3.
									rewrite <- DependentTypeLemmas.beqAddrTrue in *.
									rewrite <- beqAddrFalse in *.
									rewrite beqAddrSym in H3.
									cbn in H3.*)
							++++ 							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
										cbn.
									rewrite Haddr in *.
									destruct (beqAddr pdinsertion blockentryaddr) eqn:Hbeqpdpa ; try (exfalso ; congruence) ; trivial.
			+ (* pdinsertion = blockentryaddr *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				rewrite Hbeqpdpa in *.
				congruence.
			+ (* pdinsertion <> blockentryaddr *)
				destruct (beqAddr blockentryaddr newBlockEntryAddr) eqn:Hbeqblocknew ; try(exfalso ;congruence).
				* (* blockentryaddr = newBlockEntryAddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in *. congruence.
					
				* (* pdinsertion <> newBlockEntryAddr *)
					rewrite H4 in H3. cbn in H3. rewrite beqAddrTrue in *.
											rewrite <- beqAddrFalse in *.
							do 6 rewrite removeDupIdentity in H3; intuition.
					repeat rewrite beqAddrTrue in H3.
					rewrite beqAddrSym in H3.
					
					destruct (beqAddr blockentryaddr newBlockEntryAddr ) eqn:Hffalse  in H3 ; try (rewrite <- DependentTypeLemmas.beqAddrTrue in * ; exfalso ; congruence).
					destruct (beqAddr pdinsertion newBlockEntryAddr ) eqn:Hfffalse  in H3 ; try (rewrite <- DependentTypeLemmas.beqAddrTrue in * ; exfalso ; congruence).
					cbn in H3.
					destruct (beqAddr pdinsertion blockentryaddr ) eqn:Hffffalse  in H3 ; try (rewrite <- DependentTypeLemmas.beqAddrTrue in * ; exfalso ; congruence).
					rewrite <- beqAddrFalse in *.
					cbn in H3.
					do 3 rewrite removeDupIdentity in H3; intuition. exists entry. intuition.



					intuition. admit.
					




							


 rewrite beqAddrTrue. exfalso. congruence. f_equal. congruence. contradict H0. congruence.
							 f_equal.
							unfold isPDT in *.  rewrite H7 in *.
rewrite H4 in H3.
							cbn in H3.
							repeat rewrite beqAddrTrue in H3.
							rewrite <- DependentTypeLemmas.beqAddrTrue in *.
							rewrite <- beqAddrFalse in *.
							rewrite beqAddrSym in H3.
							cbn in H3.


			
				destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdblock' ; try (exfalso ; congruence).
					+++ (* pdinsertion = (CPaddr (blockentryaddr - blockindex entry)) *)
							(* prove false because can't be PDT and BE at the same time*)
							rewrite H4 in H3.
							cbn in H3.
							repeat rewrite beqAddrTrue in H3.
							rewrite <- DependentTypeLemmas.beqAddrTrue in *.
							rewrite <- beqAddrFalse in *.
							rewrite beqAddrSym in H3.
							cbn in H3.

							destruct (beqAddr blockentryaddr newBlockEntryAddr) eqn:Hblocknew ; try(exfalso ; congruence).
							--- (* blockentryaddr = newBlockEntryAddr *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in *.
									rewrite Hblocknew in *.
									assert(HBE : isBE newBlockEntryAddr s0) by intuition.
									apply isBELookupEq in HBE. destruct HBE.
									specialize(Hcons2 newBlockEntryAddr entry H7).
									rewrite <- Hbeqpdblock' in *.
									destruct Hcons2. congruence.


							repeat rewrite removeDupIdentity in H3; intuition.

							specialize (Hcons2 blockentryaddr entry H7).
							destruct Hcons2. 
							rewrite <- DependentTypeLemmas.beqAddrTrue in *.
							rewrite <- Hbeqpdblock' in *.
							assert (HPDT : isPDT pdinsertion s0) by intuition.
							unfold isPDT in *. rewrite H8 in *. exfalso; congruence.
				+++

							rewrite <- Hbeqpdblock' in *.
							eexists. rewrite H4. cbn. 						
							rewrite <- beqAddrFalse in *.
							rewrite beqAddrSym.
							repeat rewrite removeDupIdentity ; intuition.
							repeat rewrite beqAddrTrue.
							destruct ( beqAddr pdinsertion newBlockEntryAddr ) eqn:Hfalse ; try (intuition). (* why need to do this ? since we checked it befre ? *)
							(* pdinsertion<> newBlockEntryAddr *)
														repeat rewrite removeDupIdentity ; intuition.
							cbn. rewrite beqAddrTrue. exfalso. congruence. f_equal. congruence. contradict H0. congruence.
							 f_equal.
							unfold isPDT in *.  rewrite H7 in *.
							intuition.
					++ (* pdinsertion<> (CPaddr (blockentryaddr - blockindex entry)) *)
							destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry)) ) eqn:Hbeq.
							2 : { cbn.
							rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity ; intuition.
										destruct (beqAddr pdinsert



						destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry)) ) eqn:Hbeq.
						2 : { cbn.
						rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hfalse ; try intuition.
								repeat rewrite removeDupIdentity ; intuition.
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								assert(HBE : isBE newBlockEntryAddr s0) by intuition.
						apply isBELookupEq in HBE. destruct HBE.
						unfold isPDT in *. rewrite Hfalse in *. rewrite H13 in *.
						intuition.
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								assert(HBE : isBE newBlockEntryAddr s0) by intuition.
						apply isBELookupEq in HBE. destruct HBE.
						unfold isPDT in *. rewrite Hfalse in *. rewrite H13 in *.
						intuition.
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								assert(HBE : isBE newBlockEntryAddr s0) by intuition.
						apply isBELookupEq in HBE. destruct HBE.
						unfold isPDT in *. rewrite Hfalse in *. rewrite H13 in *.
						intuition.

						cbn.
						destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hffalse ; try(exfalso ; congruence).
						intuition. f_equal.
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
					2 : {
								cbn.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
						(* by H3 *)
						assert(Hproof : lookup blockentryaddr (memory s0) beqAddr = Some (BE entry)).
						admit.
						specialize (Hcons2 blockentryaddr entry Hproof). intuition.
						destruct Hcons2.
						rewrite H13. f_equal. cbn. intuition. instantiate (1:= x9).
						destruct Hcons2. intuition. eapply H13.
								destruct Hcons2. rewrite Hffalse in *. congruence.


						apply Hcons2.


						assert(HPDT : isPDT pdinsertion s) by admit.
						apply isPDTLookupEq in HPDT. destruct HPDT.
						

						
						

								destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hffalse ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								unfold isPDT in *. unfold isBE in *. rewrite Hfalse in *.
								destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hffalse ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								unfold isPDT in *. unfold isBE in *. rewrite Hfalse in *.
								destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hffalse ; try(exfalso ; congruence).
						cbn.
									

					+++ (* newBlockEntryAddr = (CPaddr (blockentryaddr - blockindex x9)) *)
								cbn.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
						destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hfalse ; try intuition.
								repeat rewrite removeDupIdentity ; intuition.
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								unfold isPDT in *. unfold isBE in *. rewrite Hfalse in *.
								destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hffalse ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								unfold isPDT in *. unfold isBE in *. rewrite Hfalse in *.
								destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hffalse ; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								unfold isPDT in *. unfold isBE in *. rewrite Hfalse in *.
								destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hffalse ; try(exfalso ; congruence).
						cbn.
						destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:HbeqpdKS ; try intuition.
						+++ rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								specialize (Hcons2 blockentryaddr entry H3).
								destruct Hcons2. rewrite HbeqpdKS in *. congruence.
						+++ cbn.
						rewrite <- beqAddrFalse in *.
						repeat rewrite removeDupIdentity ; intuition.
								assert( lookup newBlockEntryAddr (memory s0) beqAddr =
Some
  (BE
     (CBlockEntry (read x8) (write x8) e (present x8) 
        (accessible x8) (blockindex x8) (blockrange x8)))

								repeat rewrite removeDupIdentity ; intuition.
								rewrite <- DependentTypeLemmas.beqAddrTrue in *.
								unfold isPDT in *. unfold isBE in *. rewrite Hfalse in *.
								rewrite Hbeqpdblock in *. 

						
						apply isPDTLookupEq in H16. destruct H16.
						do 9 rewrite removeDupIdentity in H5 ; try( rewrite H16 in *; rewrite removeDupIdentity in H5 ;intuition) ; intuition.
						rewrite H16 in *.
						rewrite removeDupIdentity in H5.
						*** rewrite H15 in *.
								intuition.
						*** rewrite removeDupIdentity in H5.
								rewrite H15 in *. exfalso ; intuition.
								destruct (lookup pdinsertion (removeDup pdinsertion (memory s0) beqAddr)
         beqAddr) eqn:Hfalse ; try (exfalso ; congruence). 
								destruct v eqn:Hvfalse ; try(exfalso ; intuition).
								contradict Hfalse.
								rewrite removeDupIdentity ; intuition. congruence.
								rewrite removeDupIdentity in Hfalse ; intuition. congruence.
								destruct (lookup pdinsertion (removeDup pdinsertion (memory s0) beqAddr)
           beqAddr) eqn:hffalse; try(exfalso ; congruence).
						destruct v0 eqn:Hvffalse ; try(exfalso ; congruence).
						cbn in hffalse.


						destruct(  lookup (CPaddr (blockentryaddr - blockindex x9))
         (removeDup newBlockEntryAddr
            (removeDup newBlockEntryAddr
               (removeDup newBlockEntryAddr
                  (removeDup newBlockEntryAddr
                     (removeDup newBlockEntryAddr
                        (if beqAddr pdinsertion newBlockEntryAddr
                         then
                          removeDup newBlockEntryAddr
                            (removeDup newBlockEntryAddr
                               (removeDup pdinsertion
                                  (removeDup pdinsertion (memory s0) beqAddr)
                                  beqAddr) beqAddr) beqAddr
                         else
                          (pdinsertion,
                          PDT
                            {|
                            structure := structure x1;
                            firstfreeslot := firstfreeslot x1;
                            nbfreeslots := predCurrentNbFreeSlots;
                            nbprepare := nbprepare x1;
                            parent := parent x1;
                            MPU := MPU x1 |})
                          :: removeDup newBlockEntryAddr
                               (removeDup newBlockEntryAddr
                                  (removeDup pdinsertion
                                     (removeDup pdinsertion 
                                        (memory s0) beqAddr) beqAddr)
                                  beqAddr) beqAddr) beqAddr) beqAddr)
                  beqAddr) beqAddr) beqAddr) beqAddr) eqn:HAll; try (exfalso ; congruence).
									destruct v eqn:Hv ; try (exfalso ; congruence).
									do 6 rewrite removeDupIdentity in HAll.



			assert(HBE : isBE newBlockEntryAddr s0) by intuition.
			apply isBELookupEq in HBE. destruct HBE as [entry'].
			assert (blockindex entry = blockindex entry'). admit.
			rewrite H8.
			assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
			by (unfold consistency in * ; intuition).
			unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
			specialize (Hcons blockentryaddr entry').
			apply Hcons.

			rewrite H4 in H3. cbn in H3. repeat rewrite beqAddrTrue in H3.

			destruct (beqAddr newBlockEntryAddr blockentryaddr ) eqn:Hbeq ; try intuition.
			+ (* newBlockEntryAddr = blockentryaddr *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				rewrite <- Hbeq in *. assumption.
			+ (* newBlockEntryAddr <> blockentryaddr *)
				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock ; try (exfalso ; congruence).
				++ (* pdinsertion = newBlockEntryAddr *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in *.
						unfold isBE in *. unfold isPDT in *. rewrite Hbeqpdblock in *.
						rewrite H7 in *. intuition.
				++ (* pdinsertion<> newBlockEntryAddr *)
						do 6 rewrite removeDupIdentity  in H3 ; intuition.


						destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdblockblock ; intuition.
								+++ (* pdinsertion = (CPaddr (newBlockEntryAddr - blockindex entry)) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in *.
										rewrite <- Hbeqpdblockblock in *.
										apply isPDTLookupEq in H14. destruct H14.
										unfold isBE. rewrite H13.
										rewrite H4 in H0. cbn in H0.
										contradict H0.
										repeat rewrite beqAddrTrue.
destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
				* (* pdinsertion = newBlockEntryAddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in *.
					unfold isPDT in *. unfold isBE in *. 
					rewrite Hbeqpdblock in *.
					destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; intuition).
					destruct v eqn:Hv ; try (exfalso ; intuition).
					congruence.
				* (* pdinsertion <> newBlockEntryAddr *)
							rewrite beqAddrSym in Hbeqpdblock. rewrite Hbeqpdblock.
							rewrite <- beqAddrFalse in *.
															repeat rewrite removeDupIdentity ; intuition.
							cbn in H0.
							repeat rewrite beqAddrTrue in H0. Search (x). contradict H0. congruence.
								+++ (* pdinsertion = (CPaddr (newBlockEntryAddr - blockindex entry)) *)
										contradict H13.
										cbn.
										rewrite Hbeqpdblockblock.
								repeat rewrite removeDupIdentity ; intuition.
										Search (Some (SHE ?x)).
										rewrite H4 in H3. cbn in H3. repeat rewrite beqAddrTrue in H3.
										rewrite Hbeqpdblock in H3.

										destruct (beqAddr newBlockEntryAddr blockentryaddr) ; intuition.
										Search (isSHE ?x).

 ; try (exfalso ; congruence).
				assert(blockindex entry = blockindex entry').

			destruct (beqAddr pdinsertion blockentryaddr) eqn:Hbeqpdpa ; try (exfalso ; congruence) ; trivial.
			+ (* pdinsertion = blockentryaddr *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				rewrite Hbeqpdpa in *.
				congruence.
			+ (* pdinsertion <> blockentryaddr *)
				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
				* (* pdinsertion = newBlockEntryAddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in *.
					unfold isPDT in *. unfold isBE in *. 
					rewrite Hbeqpdblock in *.
					destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; intuition).
					destruct v eqn:Hv ; try (exfalso ; intuition).
				* (* pdinsertion <> newBlockEntryAddr *)
					unfold isBE. rewrite H4. cbn.
							repeat rewrite beqAddrTrue.

					destruct ((if beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry))
   then
    Some
      (BE
         (CBlockEntry (read x8) (write x8) e (present x8) 
            (accessible x8) (blockindex x8) (blockrange x8)))
   else
    lookup (CPaddr (blockentryaddr - blockindex entry))
      (removeDup newBlockEntryAddr
         (removeDup newBlockEntryAddr
            (removeDup newBlockEntryAddr
               (removeDup newBlockEntryAddr
                  (removeDup newBlockEntryAddr
                     (removeDup newBlockEntryAddr
                        (if beqAddr pdinsertion newBlockEntryAddr
                         then
                          removeDup newBlockEntryAddr
                            (removeDup pdinsertion
                               (removeDup pdinsertion (memory s0) beqAddr)
                               beqAddr) beqAddr
                         else
                          (pdinsertion,
                          PDT
                            {|
                            structure := structure x1;
                            firstfreeslot := firstfreeslot x1;
                            nbfreeslots := predCurrentNbFreeSlots;
                            nbprepare := nbprepare x1;
                            parent := parent x1;
                            MPU := MPU x1 |})
                          :: removeDup newBlockEntryAddr
                               (removeDup pdinsertion
                                  (removeDup pdinsertion (memory s0) beqAddr)
                                  beqAddr) beqAddr) beqAddr) beqAddr)
                  beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)) eqn:Hremaining ; try (exfalso ; congruence).
					destruct v eqn:Hv ; trivial.

						rewrite Hbeqpdblock in Hremaining. cbn.
					destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeq ; trivial.
					++ (* newBlockEntryAddr <> CPaddr (blockentryaddr - blockindex entry)) *)
							intuition. congruence.
					++ (* newBlockEntryAddr = CPaddr (blockentryaddr - blockindex entry)) *)
							intuition. contradict Hremaining.

								repeat rewrite removeDupIdentity; intuition.

						destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdblockblock ; intuition.
								+++ (* pdinsertion = (CPaddr (newBlockEntryAddr - blockindex entry)) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in *.
										contradict H13.
										cbn.
										repeat rewrite beqAddrTrue.
										rewrite <- Hbeqpdblockblock in *.
										repeat rewrite beqAddrTrue. congruence.
								+++ (* pdinsertion = (CPaddr (newBlockEntryAddr - blockindex entry)) *)
										contradict H13.
										cbn.
										rewrite Hbeqpdblockblock.
								repeat rewrite removeDupIdentity ; intuition.
										Search (Some (SHE ?x)).
										rewrite H4 in H3. cbn in H3. repeat rewrite beqAddrTrue in H3.
										rewrite Hbeqpdblock in H3.

										destruct (beqAddr newBlockEntryAddr blockentryaddr) ; intuition.
										Search (isSHE ?x).

 ; try (exfalso ; congruence).
										

congruence.
 congruence.
										repeat rewrite beqAddrTrue. congruence.


										unfold isPDT in *.
										unfold isBE in H6.
										destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup ; try (congruence).
										destruct v eqn:Hv ; try congruence.
										assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
										by (unfold consistency in * ; intuition).
										unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
										specialize (Hcons newBlockEntryAddr entry).
										contradict Hcons.
										rewrite <- Hbeqpdblockblock.
										unfold isPDT in H14.
										unfold isBE.
										destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
										destruct v eqn:Hv ; try (exfalso ; congruence).


								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
							destruct (beqAddr pdinsertion newBlockEntryAddr) ; try intuition.
							cbn.
							* (* pdinsertion newBlockEntryAddr *)

							rewrite <- beqAddrFalse in *.

rewrite <- DependentTypeLemmas.beqAddrTrue in *.
						assert((BE
          (CBlockEntry (read x8) (write x8) e (present x8) 
             (accessible x8) (blockindex x8) (blockrange x8))) = (BE entry)).
						intuition. f_equal.
						assert (blockindex entry = blockindex x8). intuition. cbn.
						Search (f_equal).
						rewrite <- H3.
						rewrite <- Hbeq in *.
						unfold isBE.
						rewrite H4. cbn.
						repeat rewrite beqAddrTrue in *. simpl.
						rewrite Hbeq.
						destruct ( beqAddr blockentryaddr (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqnewblock.
						** (* blockentryaddr = (CPaddr (blockentryaddr - blockindex entry))*)
								trivial.
						**	(* blockentryaddr <> (CPaddr (blockentryaddr - blockindex entry)) *)

								rewrite <- beqAddrFalse in *.
								repeat rewrite removeDupIdentity ; intuition.
								rewrite <- Hbeq. cbn.


								destruct (beqAddr pdinsertion (CPaddr (newBlockEntryAddr - blockindex entry))) eqn:Hbeqpdblockblock.
								+++ (* pdinsertion = (CPaddr (newBlockEntryAddr - blockindex entry)) *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in *.
										rewrite <- Hbeqpdblockblock.
										cbn.
										repeat rewrite beqAddrTrue.
										rewrite <- Hbeqpdblockblock in *.
										unfold isPDT in *.
										unfold isBE in H6.
										destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup ; try (congruence).
										destruct v eqn:Hv ; try congruence.
										assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
										by (unfold consistency in * ; intuition).
										unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
										specialize (Hcons newBlockEntryAddr entry).
										contradict Hcons.
										rewrite <- Hbeqpdblockblock.
										unfold isPDT in H14.
										unfold isBE.
										destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
										destruct v eqn:Hv ; try (exfalso ; congruence).

										(*rewrite H4 in H3. cbn in H3. rewrite beqAddrTrue in H3.*)
										assert(HconsKS : FirstFreeSlotPointerIsBEAndFreeSlot s0)
										by (unfold consistency in * ; intuition).
										unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
										specialize (HconsKS pdinsertion p Hlookup).
										unfold pdentryFirstFreeSlot in *. rewrite Hlookup in *.
										rewrite <- H10 in *. intuition.
										destruct HconsKS. intuition. rewrite H15 in *.
										unfold isBE in H12.
										assert(HconsNULL : nullAddrExists s0)
										by (unfold consistency in * ; intuition).
										unfold nullAddrExists in *.
										unfold isPADDR in *.
										destruct (lookup nullAddr (memory s0) beqAddr ) ; try (exfalso ; congruence).
										destruct v0 ; try (exfalso ; congruence).
										contradict H13. intuition.
										rewrite <- H3. rewrite Hbeq.
										rewrite H4. cbn. repeat rewrite beqAddrTrue.
										rewrite Hbeq. intuition.
										auto.
										unfold isBE in H12.
										destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup' ; try (exfalso ; congruence).
										destruct v eqn:Hv' ; try (exfalso ; congruence).
										auto.
					
 admit.

								+++ (* pdinsertion <> (CPaddr (blockentryaddr - blockindex entry)) *)
										rewrite <- beqAddrFalse in *.
										repeat rewrite removeDupIdentity ; intuition.
										unfold isBE in H6.




								rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeqnewblock.

						
												assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
									by (unfold consistency in * ; intuition).
						unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
					specialize (Hcons newBlockEntryAddr entry).
					
					contradict Hcons.
					apply Hcons.


contradict Hbeqnewblock.
						induction entry. simpl. induction blockindex.
						simpl. induction i. simpl. cbn.
						destruct newBlockEntryAddr. simpl. induction p.
						simpl.
						
					repeat rewrite removeDupIdentity ; intuition.

						rewrite H6. intuition.
						cbn.


						assert (HPDT : isPDT pdinsertion s0) by intuition.

					++ (* newBlockEntryAddr <> (CPaddr (blockentryaddr - blockindex entry)) *)
						rewrite H4. unfold isBE. cbn.
						rewrite Hbeq.

					repeat rewrite beqAddrTrue in *. simpl.

			+ (* newBlockEntryAddr <> (CPaddr (blockentryaddr - blockindex entry)) *)
				rewrite H4. unfold isBE. cbn.
				rewrite Hbeq.

				repeat rewrite beqAddrTrue in *. simpl.



			destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeq ; trivial.
			+ (* newBlockEntryAddr = (CPaddr (blockentryaddr - blockindex entry)) *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				rewrite <- Hbeq in *.
				rewrite H6. intuition.

			+ (* newBlockEntryAddr <> (CPaddr (blockentryaddr - blockindex entry)) *)
				rewrite H4. unfold isBE. cbn.
				rewrite Hbeq.

				repeat rewrite beqAddrTrue in *. simpl.

				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
				* (* pdinsertion = newBlockEntryAddr *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in *.
					unfold isPDT in *. unfold isBE in *. 
					rewrite Hbeqpdblock in *.
					destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; intuition).
					destruct v eqn:Hv ; try (exfalso ; intuition).
				* (* pdinsertion <> newBlockEntryAddr *) 
					cbn.
					rewrite Hbeqpdblock.
					rewrite <- beqAddrFalse in *.
					repeat rewrite removeDupIdentity ; intuition.
					cbn.
					destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdpa ; try (exfalso ; congruence).
					-- (* pdinsertion = (CPaddr (blockentryaddr - blockindex entry)) *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in *. admit.

					-- (* pdinsertion <> (CPaddr (blockentryaddr - blockindex entry)) *)
							rewrite <- beqAddrFalse in *.
							repeat rewrite removeDupIdentity ; intuition.
							unfold isBE in H6.

							case_eq (lookup (CPaddr (blockentryaddr - blockindex entry)) (memory s0) beqAddr).
							intros. destruct v eqn:Hv ; try (intuition). intuition.
							rewrite H13 in *.
							case_eq (lookup (CPaddr (blockentryaddr - blockindex entry)) 
         (memory s) beqAddr). destruct v0 eqn:Hv0 ; try (intuition). intuition.
							intros. rewrite H15 in *. rewrite <- H6. intuition.
intros. rewrite H15 in *. rewrite <- H6. intuition.

							destruct ( lookup (CPaddr (blockentryaddr - blockindex entry)) (memory s0) beqAddr).
							destruct (lookup (CPaddr (blockentryaddr - blockindex entry)) 
         (memory s) beqAddr) eqn:Hlookup' ; try (exfalso ; congruence).
								destruct v eqn:Hv ; try (intuition). intuition.
							destruct v0 eqn:Hv' ; try (intuition ; rewrite <- H6 ; trivial). 



							rewrite Hbeqpdpa in *.


							rewrite <- Hbeqpdpa in *.
						assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
									by (unfold consistency in * ; intuition).
						unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
						assert (HPDT : isPDT pdinsertion s0) by intuition.


							rewrite <- DependentTypeLemmas.beqAddrTrue in *.
							assert (HPDT : isPDT pdinsertion s0) by intuition.
							unfold isPDT in HPDT.
							destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
							destruct v eqn:Hv ; try (exfalso ; congruence).
							rewrite <- Hbeqpdpa in *.
							unfold isBE in H6.
							rewrite Hlookup in *.
							rewrite Hbeqpdpa in *.
							destruct( lookup (CPaddr (blockentryaddr - blockindex entry)) 
         (memory s) beqAddr) eqn:Hfalse ; try (exfalso ; congruence).
							destruct v0 eqn:Hvfalse ; try (exfalso ; congruence).
							rewrite <- Hbeqpdpa in *.
						

				assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
							by (unfold consistency in * ; intuition).
							unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
							assert (HPDT : isPDT pdinsertion s0) by intuition.
							assert(isPDT pdinsertion s0 = isPDT pdinsertion s). admit.
							unfold isPDT in HPDT.
							destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup.
							destruct v eqn:Hv ; try (exfalso ; intuition).
							specialize (Hcons blockentryaddr entry).
							rewrite <- Hbeqpdpa in *.
							unfold isBE in Hcons.
							rewrite Hlookup in *.
							apply Hcons.
							rewrite <- H3.
							f_equal. f_equal. rewrite H4. cbn. f_equal.
							unfold add. intuition. cbn.
							repeat rewrite beqAddrTrue.
							rewrite Hbeqpdblock. cbn.
							destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hfalse ; try (intuition).
							destruct s0. f_equal. intuition. simpl.

							repeat rewrite removeDupIdentity ; intuition.
							rewrite <- beqAddrFalse in Hbeq.

							apply isPDTLookupEq in H14. destruct H14.


rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
			rewrite Hbeq. repeat rewrite beqAddrTrue.

			destruct( beqAddr (CPaddr (newBlockEntryAddr - blockindex entry))
      (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeq2 ; trivial.
			destruct (beqAddr pdinsertion (CPaddr (newBlockEntryAddr - blockindex entry))) eqn:Hbeqpdblock.
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				unfold isPDT in *. unfold isBE in *.
				rewrite <- Hbeqpdblock in *. rewrite <- Hbeq in *.
				destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; intuition).
				destruct v eqn:Hv ; try (exfalso ; intuition).

				cbn. rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.

				destruct (beqAddr pdinsertion (CPaddr (newBlockEntryAddr - blockindex entry))) eqn:HbeqF.
				rewrite <- DependentTypeLemmas.beqAddrTrue in *. intuition.

				cbn. rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.

				contradict Hbeq. admit.

rewrite <- beqAddrFalse in *.
				rewrite Hbeqpdblock in *.
								repeat rewrite removeDupIdentity ; intuition.


		assert (isBE (CPaddr (blockentryaddr - blockindex entry)) s0).
		{
			rewrite H4 in H3.
			cbn in *.
				repeat rewrite beqAddrTrue in *.
				destruct(beqAddr newBlockEntryAddr blockentryaddr) eqn:Hbeq ; try congruence.
				rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
				rewrite <- H6.
				rewrite <- Hbeq.
				rewrite H4. unfold isBE. cbn.

				destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr - blockindex entry))) eqn:Hbeq2 ; trivial.
				repeat rewrite beqAddrTrue.

				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
rewrite <- beqAddrFalse in *.
				rewrite Hbeqpdblock in *.
								repeat rewrite removeDupIdentity ; intuition.

				unfold isPDT in *. unfold isBE in *. rewrite <- Hbeqpdblock in *.
				destruct( lookup pdinsertion (memory s0) beqAddr) eqn:Hfalse ; try (exfalso ; congruence).
				destruct v eqn:Hvfalse ; try (exfalso ; congruence).

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
				cbn.

			destruct (beqAddr pdinsertion (CPaddr (newBlockEntryAddr - blockindex entry))) eqn:Hbeqpdpa ; try (exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			rewrite Hbeq in *.
assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
			by (unfold consistency in * ; intuition).
			unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
			assert (HPDT : isPDT pdinsertion s0) by intuition.
			rewrite Hbeqpdpa in *.
			apply isPDTLookupEq in H14. destruct H14.
			
			assert (HBE : isBE newBlockEntryAddr s0) by (rewrite Hbeq ; intuition).

			2 : { repeat rewrite removeDupIdentity ; intuition.
 						rewrite <- beqAddrFalse in *.
						assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
			by (unfold consistency in * ; intuition).
			unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
			specialize (Hcons newBlockEntryAddr entry).
				destruct (
			contradict Hcons.
			rewrite <- H3. unfold not. intros.
			rewrite <- Hbeqpdpa in *. destruct H14.
			unfold isBE. unfold isPDT in HPDT.
			destruct (lookup (CPaddr (blockentryaddr - blockindex entry)) (memory s0) beqAddr) ; try(exfalso ; congruence).
			destruct v ; try(exfalso ; congruence).
			rewrite <- Hbeq.
			unfold not. intros. contradict H14.
			
			

			apply isBELookupEq in H12. destruct H12.
			specialize (Hcons blockentryaddr x9 H12).








				destruct (lookup (CPaddr (newBlockEntryAddr - blockindex entry)) (memory s0) beqAddr) eqn:Hlookup.
				destruct v eqn:Hv ; trivial.

				unfold isPDT in *. unfold isBE in *. rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
				rewrite Hbeqpdblock in *.
				destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.
				rewrite Hbeqpdblock in *.
				destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.



				assert (HBE : isBE newBlockEntryAddr s0) by intuition.

				assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
			by (unfold consistency in * ; intuition).
			unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
			apply Hcons.
				apply isBELookupEq in HBE. destruct HBE. rewrite H7. trivial.

				
				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
				cbn.

				destruct (beqAddr pdinsertion blockentryaddr) eqn:Hbeqpdpa ; try congruence.
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				rewrite <- Hbeqpdpa.
				apply isPDTLookupEq in H14. destruct H14.
				rewrite H13. trivial.

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			unfold isBE.

		}
			
		rewrite H6. intuition.
		assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
			by (unfold consistency in * ; intuition).
			unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
			apply Hcons.

		unfold isBE. rewrite H4. cbn.
		destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeq.
			rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq. trivial.

			repeat rewrite beqAddrTrue.
			destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			unfold isPDT in *. unfold isBE in *. 
			rewrite Hbeqpdblock in *.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; intuition).
			destruct v eqn:Hv ; try (exfalso ; intuition).
			
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
			cbn.

			destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdpa ; try (exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
			by (unfold consistency in * ; intuition).
			unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
			specialize (Hcons blockentryaddr entry).
			contradict Hcons.
			rewrite <- Hbeqpdpa.
			unfold isBE. apply isPDTLookupEq in H13. destruct H13.
			rewrite H12. intuition. apply H13. intuition.
			rewrite <- H3.
			rewrite H4.
			cbn. simpl.
			repeat rewrite beqAddrTrue.


			destruct (beqAddr newBlockEntryAddr blockentryaddr) eqn:Hbeq2.
rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			unfold isBE in H11.
			rewrite <- Hbeq2.
			
			destruct (lookup blockentryaddr (memory s0) beqAddr) eqn:Hlookup'.
			destruct v eqn:Hv'  ;try (rewrite <- Hbeq2 in * ; rewrite Hlookup' in H11 ; congruence).
			cbn. rewrite <- Hbeq2 in Hlookup'. rewrite Hlookup' in H11 ; congruence.
			cbn. rewrite <- Hbeq2 in Hlookup'. rewrite Hlookup' in H11 ; congruence.
 			congruence. intuition.
			
			apply isBELookupEq in H11. destruct H11.
			rewrite <- Hbeq2. rewrite H11.
			

			repeat rewrite removeDupIdentity ; intuition.

			unfold not. intros.
			unfold isBE

			rewrite Hbeqpdpa in *.
			unfold isPDT in *.
			destruct (lookup (CPaddr (blockentryaddr - blockindex entry)) (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
			destruct v eqn:Hv ; try (exfalso ; congruence).

			rewrite <- Hbeqpdpa.
			apply isPDTLookupEq in H13. destruct H13.
			rewrite H12. trivial.

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.




		assert(isBE (CPaddr (blockentryaddr - blockindex entry)) s = isBE (CPaddr (blockentryaddr - blockindex entry)) s0).
		{ rewrite H4. unfold isBE. cbn.
		
			destruct (beqAddr newBlockEntryAddr (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeq.
			rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
			rewrite <- Hbeq.
			assert (HBE : isBE newBlockEntryAddr s0) by intuition.
			unfold isBE in HBE.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
			destruct v eqn:Hv ; try congruence ; intuition.

			repeat rewrite beqAddrTrue.
			destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			unfold isPDT in *. unfold isBE in *. rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
			rewrite Hbeqpdblock in *.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.
			rewrite Hbeqpdblock in *.
			destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.
			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
			cbn.

			destruct (beqAddr pdinsertion (CPaddr (blockentryaddr - blockindex entry))) eqn:Hbeqpdpa ; try congruence.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			rewrite <- Hbeqpdpa.
			apply isPDTLookupEq in H13. destruct H13.
			rewrite H12. trivial.

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
		}

			rewrite H6.
			assert(Hcons : KernelStructureStartFromBlockEntryAddrIsBE s0)
			by (unfold consistency in * ; intuition).
			unfold KernelStructureStartFromBlockEntryAddrIsBE in *.
			apply Hcons.
			assert(isBE blockentryaddr s = isBE blockentryaddr s0).
			{
				rewrite H4. unfold isBE. cbn.
				repeat rewrite beqAddrTrue in *.
				destruct(beqAddr newBlockEntryAddr blockentryaddr) eqn:Hbeq ; try congruence.
				rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
				rewrite <- Hbeq.
				assert (HBE : isBE newBlockEntryAddr s0) by intuition.
				apply isBELookupEq in HBE. destruct HBE. rewrite H7. trivial.

				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				unfold isPDT in *. unfold isBE in *. rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
				rewrite Hbeqpdblock in *.
				destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.
				rewrite Hbeqpdblock in *.
				destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup ; try congruence.

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
				cbn.

				destruct (beqAddr pdinsertion blockentryaddr) eqn:Hbeqpdpa ; try congruence.
				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
				rewrite <- Hbeqpdpa.
				apply isPDTLookupEq in H14. destruct H14.
				rewrite H13. trivial.

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.
			}


			unfold isBE in H7 at 1. (* unfold only first occurence *)
			rewrite H3 in H7.
			assert(isBE blockentryaddr s0).
			unfold isBE. unfold isBE in H7.
			destruct (lookup blockentryaddr (memory s0) beqAddr) eqn:Hlookup ; try (rewrite <- H7 ; trivial).
			
			apply isBELookupEq in H8. destruct H8.


 by intuition.
			Search (True = ?x).
			unfold isBE in H7.
			rewrite <- H3.
			destruct (lookup blockentryaddr (memory s) beqAddr) eqn:Hlookup.
			destruct v eqn:Hv.
			destruct H7.
			destruct (lookup blockentryaddr (memory s0) beqAddr) eqn:Hlookup'.
			destruct v0 eqn:Hv'.
			
	
rewrite H3 in *.
			rewrite <- H3.
			unfold isBE in H7.
			(* prove it is the same *)
			rewrite H4.
			cbn. repeat rewrite beqAddrTrue.
			(* DUP *)
			destruct(beqAddr newBlockEntryAddr blockentryaddr) eqn:Hbeq ; try congruence.
				rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
				rewrite <- Hbeq.
				assert (HBE : isBE newBlockEntryAddr s0) by intuition.
				apply isBELookupEq in HBE. destruct HBE. rewrite H8. trivial.
			destruct (beqAddr pdinsertion blockentryaddr) eqn:Hbeqpdpa ; try congruence.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			rewrite <- Hbeqpdpa.
			apply isPDTLookupEq in H14. destruct H14.
			rewrite H13. trivial.
			destruct (lookup blockentryaddr (memory s0) beqAddr ) eqn:Hlookup ; try congruence.
			destruct v eqn:Hv ; try congruence.
			rewrite H3 in *.


			rewrite <- Hbeqpdpa.
			apply isPDTLookupEq in H14. destruct H14.
			rewrite H13. trivial. f_equal.

				rewrite <- beqAddrFalse in *.
				repeat rewrite removeDupIdentity ; intuition.


			rewrite <- beqAddrFalse in *.
			repeat rewrite removeDupIdentity ; intuition.
			cbn.
			assert(isBE blockentryaddr s = isBE blockentryaddr s0). admit.
			
			unfold isBE in H7.
			rewrite H3 in H7.
destruct (lookup blockentryaddr (memory s0) beqAddr) eqn:Hlookup; try congruence.
			destruct v eqn:Hv.
			rewrite <- Hlookup. assumption.
			unfold isBE in H6. rewrite <- Hlookup in *.

 intuition. f_equal. f_equal.
			unfold isBE.
			rewrite H3.
			destruct (lookup blockentryaddr (memory s0) beqAddr) eqn:Hlookup.
			destruct v eqn:Hv. trivial.
			rewrite  
			trivial. simpl.

 f_equal. f_equal. f_equal.
			specialize (Hcons pa H3).
			destruct Hcons. intuition.
			rewrite H11 in *. intuition.

(*
			exists (CPaddr (newBlockEntryAddr + scoffset)). intuition.
			unfold isSCE.
destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. destruct H4.
			destruct H4. destruct H4. destruct H4. destruct H4. intuition.
			rewrite H5. cbn.
			destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr + scoffset))) eqn:Hbeq.
			rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
			unfold consistency in *. unfold wellFormedShadowCutIfBlockEntry in *. intuition.
			specialize (H18 newBlockEntryAddr H11).
			destruct H18. unfold isSCE in H18. intuition.
			rewrite H30 in *. rewrite <- Hbeq in *.
			unfold isBE in H11. 
			destruct (lookup newBlockEntryAddr (memory x0) beqAddr) eqn:Hlookup ; try congruence.
			destruct v eqn:Hv ; try congruence.
			
			rewrite beqAddrTrue. rewrite <- beqAddrFalse in *.

			destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpdblock.
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			unfold isPDT in *. unfold isBE in *.
			rewrite Hbeqpdblock in *.
			destruct (lookup newBlockEntryAddr (memory x0) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
			destruct v eqn:Hv ; try (exfalso ; congruence).

			repeat rewrite removeDupIdentity ; intuition. cbn.
			
			destruct (beqAddr pdinsertion (CPaddr (newBlockEntryAddr + scoffset))) eqn:Hlookup ; try (exfalso ; congruence).
			rewrite <- DependentTypeLemmas.beqAddrTrue in *.
			unfold consistency in *. unfold wellFormedShadowCutIfBlockEntry in *. intuition.
			specialize (H18 newBlockEntryAddr H11).
			destruct H18. unfold isSCE in H18. intuition.
			rewrite H30 in *. rewrite <- Hlookup in *.
			unfold isPDT in *.
			destruct (lookup pdinsertion (memory x0) beqAddr) eqn:Hlookup2 ; try (exfalso ; congruence).
			destruct v eqn:Hv2 ; try (exfalso ; congruence).
			rewrite beqAddrTrue.
			rewrite <- beqAddrFalse in *. (* to remove in the step after the consequence *)
			repeat rewrite removeDupIdentity ; intuition.

			unfold consistency in *. unfold wellFormedShadowCutIfBlockEntry in *. intuition.
			specialize (H18 newBlockEntryAddr H11).
			destruct H18. unfold isSCE in H18. intuition.
			rewrite H30 in *.

			destruct (lookup (CPaddr (newBlockEntryAddr + scoffset)) (memory x0) beqAddr) eqn:Hlookup' ; try (exfalso ; congruence).
			destruct v eqn:Hv ; try (exfalso ; congruence).
			trivial.
			f_equal. f_equal.*)
			
			
(*
			unfold CPaddr in *.
			destruct (le_dec (newBlockEntryAddr + scoffset) maxAddr). simpl in *.
			destruct newBlockEntryAddr. simpl in *.
			cbn in *. induction p. simpl in *. rewrite <- f_equal in Hbeq.
			
			induction newBlockEntryAddr. destruct scoffset.
			simpl in *.
			destruct newBlockEntryAddr. simpl in *. congruence.
			destruct (lookup (CPaddr (newBlockEntryAddr + scoffset)) (memory s) beqAddr) eqn:Hlookup.
			destruct v eqn:Hv. cbn in *.
		
			cbn in *. rewrite H5 in Hlookup. cbn in *.
			exists (CPaddr (pa + scoffset)). split.
			unfold isSCE.
			destruct H4. destruct H4. destruct H4. destruct H4. destruct H4. destruct H4.
			destruct H4. destruct H4. destruct H4. destruct H4. intuition.
			rewrite H5. cbn.
			destruct (beqAddr newBlockEntryAddr (CPaddr (pa + scoffset))) eqn:Hbeqblockpa.
			rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeqblockpa.
			unfold consistency in *. unfold wellFormedShadowCutIfBlockEntry in *. intuition.
			specialize (H18 newBlockEntryAddr H11).
			destruct H18. unfold isSCE in H18. intuition.
			destruct (lookup x10 (memory x0) beqAddr) eqn:Hlookup ; try congruence.
			destruct v eqn:Hv ; try congruence.
			apply isBELookupEq in H11. destruct H11.
			rewrite H30 in *. rewrite Hbeqblockpa in *. rewrite  congruence. *)

		- 
			pose (Hcons := H7).
		unfold consistency in Hcons. unfold wellFormedShadowCutIfBlockEntry in *. intuition.
			unfold isSCE. rewrite H4. cbn.
			repeat rewrite beqAddrTrue. eexists.
			destruct (beqAddr newBlockEntryAddr scentryaddr).
		specialize (H18 newBlockEntryAddr H10).
		destruct H18. admit. (*unfold isSCE in H18. intuition.
		destruct (lookup x10 (memory x0) beqAddr) eqn:HSCE ; try (exfalso ; congruence).
		destruct v eqn:HvSCE ; try (exfalso ; congruence).
		exists (CPaddr (newBlockEntryAddr + scoffset)).
		unfold isSCE. rewrite <- H31. rewrite <- HSCE. intuition. cbn. rewrite H4. cbn. simpl.
		rewrite beqAddrTrue.
		apply isBELookupEq in H10. destruct H10.
		destruct (beqAddr newBlockEntryAddr x10) eqn:beq.
		f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in beq. congruence.
		rewrite beqAddrTrue.
		destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpd.
		repeat rewrite removeDupIdentity ; intuition ;
		rewrite beqAddrSym in Hbeqpd ;
		rewrite <- H18 in Hbeqpd ; congruence.
		assert(x10 <> newBlockEntryAddr).
		rewrite <- beqAddrFalse in beq. intuition.
		repeat rewrite removeDupIdentity ; intuition.
		cbn.
		destruct (beqAddr pdinsertion x10) eqn:Hbeqpdx10.
		f_equal. rewrite <- beqAddrFalse in *.
		apply isPDTLookupEq in H12. destruct H12.
		rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeqpdx10. congruence.
		repeat rewrite removeDupIdentity ; (rewrite <- beqAddrFalse in Hbeqpdx10 ; subst; intuition).
*)
		- admit.
		- destruct H4. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3.
			destruct H3. destruct H3. destruct H3. destruct H3. intuition.
			pose (Hcons := H7).
		unfold consistency in Hcons. unfold wellFormedShadowCutIfBlockEntry in *. intuition.
		specialize (H18 newBlockEntryAddr H10).
		destruct H18. unfold isSCE in H18. intuition.
		destruct (lookup x10 (memory x0) beqAddr) eqn:HSCE ; try (exfalso ; congruence).
		destruct v eqn:HvSCE ; try (exfalso ; congruence).
		exists s0. rewrite <- H30. intuition. cbn. rewrite H4. cbn. simpl.
		rewrite beqAddrTrue.
		apply isBELookupEq in H10. destruct H10.
		destruct (beqAddr newBlockEntryAddr x10) eqn:beq.
		f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in beq. congruence.
		rewrite beqAddrTrue.
		destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hbeqpd.
		repeat rewrite removeDupIdentity ; intuition ;
		rewrite beqAddrSym in Hbeqpd ;
		rewrite <- H18 in Hbeqpd ; congruence.
		assert(x10 <> newBlockEntryAddr).
		rewrite <- beqAddrFalse in beq. intuition.
		repeat rewrite removeDupIdentity ; intuition.
		cbn.
		destruct (beqAddr pdinsertion x10) eqn:Hbeqpdx10.
		f_equal. rewrite <- beqAddrFalse in *.
		apply isPDTLookupEq in H12. destruct H12.
		rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeqpdx10. congruence.
		repeat rewrite removeDupIdentity ; (rewrite <- beqAddrFalse in Hbeqpdx10 ; subst; intuition).




		

		(*2 : { intros. exact H. }
		unfold MAL.writeSCOriginFromBlockEntryAddr.
		eapply bindRev. 
		{ (** MAL.getSCEntryAddrFromBlockEntryAddr **) 
			eapply weaken. apply getSCEntryAddrFromBlockEntryAddr.
			intros. split. apply H.
			destruct H. intuition.
			destruct H4. destruct H3. destruct H3. destruct H3. destruct H3. destruct H3.
			destruct H3. destruct H3. destruct H3. destruct H3. intuition.
			- unfold wellFormedShadowCutIfBlockEntry.
				intros. eexists.
				split. unfold isSCE.
				unfold consistency in *. unfold wellFormedShadowCutIfBlockEntry in *. intuition.
				specialize (H16 pa). simpl in *.
				apply isBELookupEq in H9. destruct H9.
				destruct (lookup pa (memory s) beqAddr)  eqn:Hlookup in * ; try(congruence).
				destruct v eqn:Hv ; try(congruence).
				rewrite H4 in Hlookup. cbn in *.
				destruct (beqAddr newBlockEntryAddr pa) eqn:Hbeq.
				cbn in *. instantiate(1:= CPaddr (pa + scoffset)).
				cbn.
				destruct (lookup (CPaddr (pa + scoffset)) (memory s) beqAddr) eqn:Hbeq2.
				destruct v0 eqn:hv2 ; try congruence.
				destruct H16.
				unfold isBE. cbn. apply beqAddrTrue in Hbeq.
				cbn in *. rewrite H4 in Hbeq2. cbn in *.

specialize (H16 H9). rewrite H4. cbn.
				+ intuition. cbn. case_eq (beqAddr). 
					* destruct (beqAddr) eqn:Hbeq.
					rewrite beqAddrTrue in Hbeq.
				
			admit.
			- admit.
			- apply isBELookupEq in H. destruct H. exists x0. assumption.*)
(*		}
		intro SCEAddr.
	{ (**  MAL.writeSCOriginFromBlockEntryAddr2 **)
		eapply weaken. apply WP.writeSCOriginFromBlockEntryAddr2.
		intros. intuition.
		destruct H1 as [scentry]. exists scentry. intuition.*)
instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
isBE newBlockEntryAddr s /\
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5: BlockEntry,
		exists sceaddr, exists scentry : SCEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add sceaddr
									(SCE {| origin := origin; next := next scentry |})
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry5) (write bentry5) e (present bentry5) 
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
            /\
(* (exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 /\ isBE newBlockEntryAddr s0
/\ isPDT pdinsertion s0
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			exists x. split.
			- destruct (beqAddr x10 pdinsertion) eqn:Hbeqpdx10.
				rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeqpdx10.
				unfold isPDT in *.
				rewrite Hbeqpdx10 in *. rewrite HSCE in *. exfalso. congruence.
				rewrite removeDupIdentity. intuition.
				rewrite beqAddrFalse in *. intuition.
				rewrite beqAddrSym. congruence.
			- split.
				+ unfold isBE. intuition. rewrite isBELookupEq in *. destruct H.
					cbn. destruct (beqAddr x10 newBlockEntryAddr) eqn:Hbeq.
					* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
						destruct H10. rewrite Hbeq in *. congruence.
					* rewrite removeDupIdentity. rewrite H. trivial.
						rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
					unfold pdentryNbFreeSlots in *. cbn.
					destruct (beqAddr x10 pdinsertion) eqn:Hbeq.
						* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
							apply isPDTLookupEq in H12. destruct H12.
							rewrite Hbeq in *. congruence.
						* rewrite removeDupIdentity. assumption.
							rewrite <- beqAddrFalse in Hbeq. intuition.
						* exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
							exists x7. exists x8. exists x9. exists x10. exists s0.
							split. unfold s'. subst. f_equal.
							intuition.
							
			(*- (* DUP *) intuition.
				destruct (beqAddr SCEAddr pdinsertion) eqn:Hbeq.
				+ f_equal. rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
				+ rewrite removeDupIdentity. assumption.
					rewrite <- beqAddrFalse in Hbeq. intuition.
			- split.
				+ unfold isBE. intuition. rewrite isBELookupEq in *. destruct H.
					cbn. destruct (beqAddr SCEAddr newBlockEntryAddr) eqn:Hbeq.
					* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
					subst. congruence.
					* rewrite removeDupIdentity. rewrite H. trivial.
						rewrite <- beqAddrFalse in Hbeq. intuition.
				+ intuition.
					unfold pdentryNbFreeSlots in *. cbn.
					destruct (beqAddr SCEAddr pdinsertion) eqn:Hbeq.
						* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
							subst. congruence.
						* rewrite removeDupIdentity. assumption.
							rewrite <- beqAddrFalse in Hbeq. intuition.
						* destruct H6. destruct H5. destruct H5. destruct H5. destruct H5.
							destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
							exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
							exists x7. exists x8. exists x9. exists SCEAddr. exists scentry.
							subst. intuition.
							unfold s'. subst. f_equal.
	}*)
}	intros. simpl.

(*
				unfold MAL.writeSCOriginFromBlockEntryAddr2.
			eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(exists pd : PDTable,
       lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
       pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\
       predCurrentNbFreeSlots > 0 /\
       pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
       bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
       StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
       (exists
          (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                     bentry3 bentry4
                                                     bentry5 : BlockEntry),
          s =
          {|
          currentPartition := currentPartition s0;
          memory := add newBlockEntryAddr
                      (BE
                         (CBlockEntry (read bentry5) (write bentry5) e
                            (present bentry5) (accessible bentry5)
                            (blockindex bentry5) (blockrange bentry5)))
                      (add newBlockEntryAddr
                         (BE
                            (CBlockEntry (read bentry4) w 
                               (exec bentry4) (present bentry4) 
                               (accessible bentry4) (blockindex bentry4)
                               (blockrange bentry4)))
                         (add newBlockEntryAddr
                            (BE
                               (CBlockEntry r (write bentry3) 
                                  (exec bentry3) (present bentry3)
                                  (accessible bentry3) (blockindex bentry3)
                                  (blockrange bentry3)))
                            (add newBlockEntryAddr
                               (BE
                                  (CBlockEntry (read bentry2) 
                                     (write bentry2) (exec bentry2) true
                                     (accessible bentry2) 
                                     (blockindex bentry2) 
                                     (blockrange bentry2)))
                               (add newBlockEntryAddr
                                  (BE
                                     (CBlockEntry (read bentry1) 
                                        (write bentry1) (exec bentry1)
                                        (present bentry1) true 
                                        (blockindex bentry1) 
                                        (blockrange bentry1)))
                                  (add newBlockEntryAddr
                                     (BE
                                        (CBlockEntry (read bentry0) 
                                           (write bentry0) 
                                           (exec bentry0) 
                                           (present bentry0) 
                                           (accessible bentry0) 
                                           (blockindex bentry0)
                                           (CBlock (startAddr (blockrange bentry0))
                                              endaddr)))
                                     (add newBlockEntryAddr
                                        (BE
                                           (CBlockEntry (read bentry) 
                                              (write bentry) 
                                              (exec bentry) 
                                              (present bentry) 
                                              (accessible bentry) 
                                              (blockindex bentry)
                                              (CBlock startaddr
                                                 (endAddr (blockrange bentry)))))
                                        (add pdinsertion
                                           (PDT
                                              {|
                                              structure := structure pdentry0;
                                              firstfreeslot := firstfreeslot pdentry0;
                                              nbfreeslots := predCurrentNbFreeSlots;
                                              nbprepare := nbprepare pdentry0;
                                              parent := parent pdentry0;
                                              MPU := MPU pdentry0 |})
                                           (add pdinsertion
                                              (PDT
                                                 {|
                                                 structure := structure pdentry;
                                                 firstfreeslot := newFirstFreeSlotAddr;
                                                 nbfreeslots := nbfreeslots pdentry;
                                                 nbprepare := nbprepare pdentry;
                                                 parent := parent pdentry;
                                                 MPU := MPU pdentry |}) 
                                              (memory s0) beqAddr) beqAddr) beqAddr)
                                     beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                      beqAddr |})) /\
    (exists entry : SCEntry,
       lookup SCEAddr (memory s) beqAddr = Some (SCE entry) /\
       scentryAddr newBlockEntryAddr SCEAddr s)). intuition.
		intro s0. intuition.
		destruct (lookup SCEAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		3: { (** modify **)
			instantiate (1:= fun _ s => exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
     pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s /\ predCurrentNbFreeSlots > 0 /\
     pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5: BlockEntry,
		exists sceaddr, exists scentry : SCEntry,
  s = {|
     currentPartition := currentPartition s0;
     memory := add sceaddr
									(SCE {| origin := origin; next := next scentry |})
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry5) (write bentry5) e (present bentry5) 
                       (accessible bentry5) (blockindex bentry5) (blockrange bentry5))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry4) w (exec bentry4) (present bentry4) 
                       (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry3) (exec bentry3) (present bentry3) 
                       (accessible bentry3) (blockindex bentry3) (blockrange bentry3))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry2) (write bentry2) (exec bentry2) true 
                       (accessible bentry2) (blockindex bentry2) (blockrange bentry2))) 
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry1) (write bentry1) (exec bentry1) 
                       (present bentry1) true (blockindex bentry1) (blockrange bentry1)))
							(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) 
                       (present bentry0) (accessible bentry0) (blockindex bentry0)
                       (CBlock (startAddr (blockrange bentry0)) endaddr)))
							(add newBlockEntryAddr
                     (BE
                        (CBlockEntry (read bentry) (write bentry) 
                           (exec bentry) (present bentry) (accessible bentry)
                           (blockindex bentry)
                           (CBlock startaddr (endAddr (blockrange bentry)))))
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry0;
                    firstfreeslot := firstfreeslot pdentry0;
                    nbfreeslots := predCurrentNbFreeSlots;
                    nbprepare := nbprepare pdentry0;
                    parent := parent pdentry0;
                    MPU := MPU pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
  
)).
			eapply weaken. apply modify.
			intros. simpl.  set (s' := {|
      currentPartition :=  _|}). destruct H. destruct H0. destruct H0. exists x.
			
			split. cbn. admit.
			split. unfold pdentryNbFreeSlots in *. destruct H. destruct H0.
			destruct H0. rewrite H in H0. admit. intuition. intuition.
			admit. admit. destruct H8. destruct H7. destruct H7. destruct H7. destruct H7.
			destruct H7. destruct H7. destruct H7. destruct H7. destruct H7.
			exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
			exists x7. exists x8. exists x9.
			exists SCEAddr. exists s. subst. intuition.
}
			admit. admit. admit. admit. admit. }
intros. simpl.*)

	eapply weaken. apply ret.
	intros. intuition. split.
	- destruct H. intuition. destruct H4. repeat destruct H3.
		destruct H4. exists x0. intuition.
	- split.
		(* DUP *)
		+ unfold isBE. destruct H. intuition.
		+ split.
			* unfold consistency. admit.
			* destruct H. intuition.
				destruct H4. destruct H3. destruct H3. destruct H3. destruct H3.
							destruct H3. destruct H3. destruct H3. destruct H3. destruct H3.
							destruct H3. destruct H3.
							exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
							exists x7. exists x8. exists x9. exists x10. exists x11.
						exists newBlockEntryAddr. exists newFirstFreeSlotAddr. exists predCurrentNbFreeSlots.
							subst. intuition.

(*
	destruct H. intuition.
	destruct H6. destruct H5. destruct H5. destruct H5.
			destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
			destruct H5. destruct H5. destruct H5.
			eexists. eexists. eexists. eexists. eexists. eexists. eexists. eexists.
			eexists. eexists. eexists. eexists. exists newBlockEntryAddr. exists newFirstFreeSlotAddr. exists predCurrentNbFreeSlots. 

			intuition. rewrite H5. f_equal.*)
			Admitted.
(*
			exists x10. exists x11.
			exists x2. exists x9. exists newBlockEntryAddr. exists newFirstFreeSlotAddr. exists predCurrentNbFreeSlots. 
			intuition. cbn. (* change postcondition or show equivalence *)
			simpl in *. unfold add in H5. simpl in H5.
			repeat rewrite beqAddrTrue in H5.
 exists s. subst. intuition.


-----------------------

			instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
				exists pdentry : PDTable,
				(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) 
				) /\  isPDT pdinsertion s
				(*/\ s = {|
					currentPartition := currentPartition s;
					memory := add pdinsertion
								      (PDT
								         {|
								         structure := structure pdentry;
								         firstfreeslot := newFirstFreeSlotAddr;
												(*structure := newFirstFreeSlotAddr;
								         firstfreeslot := newFirstFreeSlotAddr;*)
								         nbfreeslots := nbfreeslots pdentry;
								         nbprepare := nbprepare pdentry;
								         parent := parent pdentry;
								         MPU := MPU pdentry |}) (memory s) beqAddr |}
										(*s.(memory) |}*)*)

				). simpl. set (s' := {|
      currentPartition :=  _|}).
- eexists. split. rewrite beqAddrTrue. (*split.*)
			+ f_equal.
			+ (*split.*) unfold isPDT. cbn. rewrite beqAddrTrue. intuition.
			}
			} 	cbn. admit. admit. admit. admit. admit.
			}
			intros.
			eapply weaken. apply modify.
			intros. simpl.
			instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
				exists pdentry : PDTable,
				(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) 
				) /\  isPDT pdinsertion s
				/\ s = {|
					currentPartition := currentPartition s;
					memory := add pdinsertion
								      (PDT
								         {|
								         structure := structure pdentry;
								         firstfreeslot := newFirstFreeSlotAddr;
												(*structure := newFirstFreeSlotAddr;
								         firstfreeslot := newFirstFreeSlotAddr;*)
								         nbfreeslots := nbfreeslots pdentry;
								         nbprepare := nbprepare pdentry;
								         parent := parent pdentry;
								         MPU := MPU pdentry |}) (memory s) beqAddr |}
										(*s.(memory) |}*)  (*/\

				((*partitionsIsolation s /\
					 verticalSharing s /\*)
						
					pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
				 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
				StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

							pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
							currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
				/\ isPDT pdinsertion s*)
				(*/\ exists pdentry : PDTable,
				lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*)
				). simpl. set (s' := {|
      currentPartition :=  _|}).
		 (*split. 
		- admit.*)
		- eexists. split. rewrite beqAddrTrue. (*split.*)
			+ f_equal.
			+ (*split.*) unfold isPDT. cbn. rewrite beqAddrTrue. intuition.
				cbn. admit.
			
		}
}  eapply weaken. apply undefined. intros.
			simpl. intuition. destruct H. intuition. congruence.
eapply weaken. apply undefined. intros.
			simpl. intuition. destruct H. intuition. congruence.
eapply weaken. apply undefined. intros.
			simpl. intuition. destruct H. intuition. congruence.
eapply weaken. apply undefined. intros.
			simpl. intuition. destruct H. intuition. congruence.
eapply weaken. apply undefined. intros.
			simpl. intuition. destruct H. intuition. congruence.
} intros.
	eapply bindRev.
	{ (** MAL.writePDNbFreeSlots **)
		eapply weaken.
		2 : { intros. exact H. }
		unfold MAL.writePDNbFreeSlots.
		eapply bindRev.
		{ (** get **)
			eapply weaken. apply get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\
(*partitionsIsolation s /\*)
    exists pdentry : PDTable,
       (lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\
        isPDT pdinsertion s)  /\
        s =
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
                       MPU := MPU pdentry |}) (memory s1) beqAddr |} (*/\
       ((*partitionsIsolation s /\
        verticalSharing s /\*)
			pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
       bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
       StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
       pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
       currnbfreeslots > 0 (*/\
       consistency s*) (* /\ isBE idBlockToShare s *) /\ isPDT pdinsertion s)*)). intuition.
intuition. destruct H. exists x. intuition. }
intro s0. simpl. intuition. (*admit.*)
		destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		4 : {
unfold Monad.modify.
eapply bindRev.
		{ (** get **)
					eapply weaken. apply get.
			intro s. intros. simpl. pattern s in H. apply H.
	}
	intro s1.
	eapply weaken. apply put.
	intros. simpl.
(*
		eapply weaken. apply modify.
		intros.*)
instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
exists pdentry : PDTable,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)) /\ 
isPDT pdinsertion s /\

s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := nbfreeslots pdentry;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |}) (memory s) beqAddr |} (*/\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s
(*/\ exists pdentry : PDTable,
lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*) *)
). simpl. set (s' := {|
      currentPartition :=  _|}).
		 (*split. 
		- admit.*)
		- eexists. split. rewrite beqAddrTrue. (*split.*)
			+ f_equal. + split.
			 (*split.*) unfold isPDT. cbn. rewrite beqAddrTrue. intuition.
				cbn. intuition. destruct H1.  intuition. subst. cbn in *.
				rewrite H2 in s'. f_equal.


			 } admit. admit. admit. admit. admit. } intros.
	eapply bindRev.
	{ (** MAL.writeBlockStartFromBlockEntryAddr **)
		eapply weaken.
		2 : { intros. exact H. }
		unfold MAL.writeBlockStartFromBlockEntryAddr.
		eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*partitionsIsolation s /\*)
    (exists pdentry : PDTable,
       (lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\
        isPDT pdinsertion s (*/\
        s =
        {|
        currentPartition := currentPartition s;
        memory := add pdinsertion
                    (PDT
                       {|
                       structure := structure pdentry;
                       firstfreeslot := newFirstFreeSlotAddr;
                       nbfreeslots := predCurrentNbFreeSlots;
                       nbprepare := nbprepare pdentry;
                       parent := parent pdentry;
                       MPU := MPU pdentry |}) (memory s) beqAddr |} *) ) /\
       ((*partitionsIsolation s /\
        verticalSharing s /\*) pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
       bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
       StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\
       pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
       currnbfreeslots > 0 /\
       consistency s(*  /\ isBE idBlockToShare s *) /\ isPDT pdinsertion s)). intuition.
intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		eapply weaken. apply modify.
		intros. (*instantiate (1:= fun _ s => tt=tt /\ s =s ).*)
instantiate (1:= fun _ s => partitionsIsolation s /\ 
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                       (present bentry) (accessible bentry) (blockindex bentry)
                       (CBlock startaddr (endAddr (blockrange bentry)))))

 (memory s) beqAddr) beqAddr |} *) ) /\

(partitionsIsolation s /\
   verticalSharing s /\
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s
(*/\ exists pdentry : PDTable,
lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*)
). simpl. admit. admit. admit. admit. admit. admit. } intros.
	eapply bindRev.
	{ (** MAL.writeBlockEndFromBlockEntryAddr **)
		eapply weaken.
		2 : { intros. exact H. }
		unfold MAL.writeBlockEndFromBlockEntryAddr.
		eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                       (present bentry) (accessible bentry) (blockindex bentry)
                       (CBlock startaddr (endAddr (blockrange bentry)))))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s). intuition. admit.
intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		eapply weaken. apply modify.
		intros. (*instantiate (1:= fun _ s => tt=tt /\ s =s ).*)
instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                       (present bentry) (accessible bentry) (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s
(*/\ exists pdentry : PDTable,
lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*)
). simpl. admit. admit. admit. admit. admit. admit. } intros.

	eapply bindRev.
	{ (** MAL.writeBlockAccessibleFromBlockEntryAddr **)
		eapply weaken.
		2 : { intros. exact H. }
		unfold MAL.writeBlockAccessibleFromBlockEntryAddr.
		eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                       (present bentry) (accessible bentry) (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s). intuition.
intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		eapply weaken. apply modify.
		intros. (*instantiate (1:= fun _ s => tt=tt /\ s =s ).*)
instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                       (present bentry) true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s
(*/\ exists pdentry : PDTable,
lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*)
). simpl. admit. admit. admit. admit. admit. admit. } intros.

	eapply bindRev.
	{ (** MAL.writeBlockPresentFromBlockEntryAddr **)
		eapply weaken.
		2 : { intros. exact H. }
		unfold MAL.writeBlockAccessibleFromBlockEntryAddr.
		eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                       (present bentry) true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s). intuition.
intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		eapply weaken. apply modify.
		intros. (*instantiate (1:= fun _ s => tt=tt /\ s =s ).*)
instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s
(*/\ exists pdentry : PDTable,
lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*)
). simpl. admit. admit. admit. admit. admit. admit. } intros.

	eapply bindRev.
	{ (** MAL.writeBlockRFromBlockEntryAddr **)
		eapply weaken.
		2 : { intros. exact H. }
		unfold MAL.writeBlockRFromBlockEntryAddr.
		eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry (read bentry) (write bentry) (exec bentry) 
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s). intuition.
intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		eapply weaken. apply modify.
		intros. (*instantiate (1:= fun _ s => tt=tt /\ s =s ).*)
instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry) (exec bentry) 
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s(*  /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s
(*/\ exists pdentry : PDTable,
lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*)
). simpl. admit. admit. admit. admit. admit. admit. } intros.


	eapply bindRev.
	{ (** MAL.writeBlockWFromBlockEntryAddr **)
		eapply weaken.
		2 : { intros. exact H. }
		unfold MAL.writeBlockWFromBlockEntryAddr.
		eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r (write bentry) (exec bentry) 
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s). intuition.
intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		eapply weaken. apply modify.
		intros. (*instantiate (1:= fun _ s => tt=tt /\ s =s ).*)
instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r w (exec bentry) 
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s
(*/\ exists pdentry : PDTable,
lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*)
). simpl. admit. admit. admit. admit. admit. admit. } intros.



	eapply bindRev.
	{ (** MAL.writeBlockXFromBlockEntryAddr **)
		eapply weaken.
		2 : { intros. exact H. }
		unfold MAL.writeBlockXFromBlockEntryAddr.
		eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r w (exec bentry) 
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s). intuition.
intro s0. intuition.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
		eapply weaken. apply modify.
		intros. (*instantiate (1:= fun _ s => tt=tt /\ s =s ).*)
instantiate (1:= fun _ s => (*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r w e
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *) ) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s
(*/\ exists pdentry : PDTable,
lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry)*)
). simpl. admit. admit. admit. admit. admit. admit. } intros.

	eapply bindRev.
	{ (** MAL.writeSCOriginFromBlockEntryAddr **)
		unfold MAL.writeSCOriginFromBlockEntryAddr.
		eapply bindRev. 
		{ (** MAL.getSCEntryAddrFromBlockEntryAddr **) 
			eapply weaken. apply getSCEntryAddrFromBlockEntryAddr.
			intros. split. apply H. unfold consistency in *. intuition.
			admit. admit. admit.
		}
		intro SCEAddr.
				unfold MAL.writeSCOriginFromBlockEntryAddr2.
			eapply bindRev.
		eapply weaken. apply get.
		intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s (*/\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r w e
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory s) beqAddr) beqAddr |} *)) /\

((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s /\
(exists entry : SCEntry,
       lookup SCEAddr (memory s) beqAddr = Some (SCE entry) /\
       scentryAddr newBlockEntryAddr SCEAddr s)
). intuition. destruct H0. destruct H. exists x. exists x0.
intuition.
intro s0. intuition.
		destruct (lookup SCEAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
	3 : {
		eapply weaken. apply modify.
		intros. (*instantiate (1:= fun _ s => tt=tt /\ s =s ).*)
(*instantiate (1:= fun _ st => 
partitionsIsolation st /\ 
exists pdentry : PDTable, exists bentry : BlockEntry, exists scentry : SCEntry,
(lookup pdinsertion (memory st) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion st /\
lookup newBlockEntryAddr (memory st) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr st /\
st = {|
  currentPartition := currentPartition st;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r w e
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))

 (memory st) beqAddr) beqAddr |}) /\

(partitionsIsolation st /\
   verticalSharing st /\
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr st) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr st /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots st /\
      currnbfreeslots > 0 /\ consistency st /\ isBE idBlockToShare st /\
(exists sceaddr : paddr, isSCE sceaddr st /\ 
scentryAddr newBlockEntryAddr sceaddr st /\
lookup sceaddr (memory st) beqAddr = Some (SCE scentry))).*)

instantiate (1:= fun _ s => 
(*partitionsIsolation s /\ *)
exists pdentry : PDTable, exists bentry : BlockEntry,
exists scentry : SCEntry, exists sceaddr : paddr,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s /\
lookup sceaddr (memory s) beqAddr = Some (SCE scentry) /\
isSCE sceaddr s /\
scentryAddr newBlockEntryAddr sceaddr s /\
s = {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure pdentry;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := predCurrentNbFreeSlots;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MPU pdentry |})
					(add newBlockEntryAddr
                 (BE
                    (CBlockEntry r w e
                       true true (blockindex bentry)
                       (CBlock startaddr endaddr)))


				(add sceaddr (SCE {| origin := origin; next := next scentry |})
 (memory s) beqAddr) beqAddr) beqAddr |} ) /\
(*add SCEAddr (SCE {| origin := origin; next := next scentry |}) 
                 (memory s) beqAddr |})*)
((*partitionsIsolation s /\
   verticalSharing s /\*)
    
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots /\

      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s (* /\ isBE idBlockToShare s *)
/\ isPDT pdinsertion s

). intros. simpl. set (s' := {|
      currentPartition :=  _|}).
		 (*split. 
		- admit.*)
		- eexists. eexists. eexists. eexists. split. repeat rewrite beqAddrTrue. cbn. split.
			+ f_equal.
			+ (*split.*) unfold isPDT. cbn. rewrite beqAddrTrue. trivial.
				(*cbn. admit.*)
			+ admit.



admit. } admit. admit. admit. admit. admit. }
	intros. 
	{ (** ret **)
	eapply weaken. apply ret. intros. simpl. intuition.
	admit. admit. admit. 
Admitted.

(*
		

	intros. split. reflexivity. split.
	admit. intuition. 
	unfold bentryEndAddr. cbn.
	assert (pdinsertion <> newBlockEntryAddr). admit. 
	rewrite beqAddrFalse in *. cbn. simpl. rewrite H5. rewrite removeDupIdentity.
	unfold bentryEndAddr in H3. subst. destruct (lookup newBlockEntryAddr (memory s) beqAddr) eqn:Hlookup' ; try (exfalso ; congruence).
	destruct v eqn:Hv0 ; try (exfalso ; congruence). intuition. rewrite <- beqAddrFalse in *. intuition. 
admit. admit. admit. admit. admit. } admit. admit. admit. admit. admit. }
	intros. simpl.



(((partitionsIsolation s /\
   verticalSharing s /\
   (exists pdentry : PDTable,
      Some (PDT p) = Some (PDT pdentry) /\
      pdentryNbFreeSlots pdinsertion currnbfreeslots s /\
      currnbfreeslots > 0 /\ consistency s /\ isBE idBlockToShare s)) /\
  pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s) /\
 bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s) /\
StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots). intuition.



		

		instantiate (1:= forall s, s =  {|
  currentPartition := currentPartition s;
  memory := add pdinsertion
              (PDT
                 {|
                 structure := structure p;
                 firstfreeslot := newFirstFreeSlotAddr;
                 nbfreeslots := nbfreeslots p;
                 nbprepare := nbprepare p;
                 parent := parent p;
                 MPU := MPU p |}) (memory s) beqAddr |}). /\ 

    (((partitionsIsolation s0 /\
       verticalSharing s0 /\
       (exists pdentry : PDTable,
          Some (PDT p) = Some (PDT pdentry) /\
          pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\
          currnbfreeslots > 0 /\ consistency s0 /\ isBE idBlockToShare s0)) /\
      pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0) /\
     bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0) /\
    StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots
).
		apply H.
		try (apply undefined ; congruence).
		try (apply undefined ; congruence).
		intros.  simpl.
		unfold Monad.modify.
		eapply bindRev. apply get. intro s0.



eapply weaken. apply WP.writePDFirstFreeSlotPointer.
		intros. simpl.
		eexists. split.
		- intuition. destruct H5. Set Printing All. instantiate (1:= 
                 fun tt => {|
                 structure := structure x;
                 firstfreeslot := firstfreeslot x (*newFirstFreeSlotAddr*);
                 nbfreeslots := nbfreeslots x;
                 nbprepare := nbprepare x;
                 parent := parent x;
                 MPU := MPU x |}).
	}
(*{ (** writePDFirstFreeSlotPointer **)
	eapply weaken.
	apply Invariants.writePDFirstFreeSlotPointer.
	intros. simpl. intuition.
	- unfold isPDT. destruct H5. intuition. rewrite H5. trivial.
	- destruct H5. intuition.
}
	intros. simpl.
	eapply bindRev. (* ajouter propagation de props *)
	{ (** MAL.writePDNbFreeSlots **)
		eapply weaken. apply Invariants.writePDNbFreeSlots.
		intros. simpl. destruct H. intuition.
		- unfold isPDT. rewrite H0; trivial.
	}
	intros.
	eapply bindRev.
	{ (** MAL.writeBlockStartFromBlockEntryAddr **)
		eapply weaken. apply Invariants.writeBlockStartFromBlockEntryAddr.
		intros. simpl. destruct H. intuition.
		unfold isBE. admit.
	} intros.*)

	
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
*)
*)