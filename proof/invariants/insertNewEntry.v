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

exists pd : PDTable, lookup pdinsertion (memory s) beqAddr = Some (PDT pd) /\
(*pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots *)


(exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6: BlockEntry,
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
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}

/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6) /\
bentry6 = (CBlockEntry (read bentry5) (write bentry5) e (present bentry5) 
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
		/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0))
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
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry |}) (memory s0) beqAddr) beqAddr |}
(*/\
(exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)

/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 /\ isBE newBlockEntryAddr s0
/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)
  
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
isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)
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
/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)
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
/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)
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
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry|}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
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
/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)
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
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
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
/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)
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
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
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
/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)
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
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
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
/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)

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
			rewrite H20. trivial.

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
				rewrite H20. trivial.
				

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
			assert(HPDTs0 : isPDT pdinsertion s0) by intuition.
			apply isPDTLookupEq in HPDTs0. destruct HPDTs0 as [pds0 HPDTs0].
			rewrite HPDTs0. trivial.

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
										rewrite H22.
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
										{ rewrite H19. rewrite H21.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x3) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x3) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. reflexivity. destruct blockentry_d. destruct x3.
										intuition.
										}
										assert(blockindex x3 = blockindex x2).
										{ rewrite H24.
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
										rewrite <- H28 in *. rewrite <- H27 in *. rewrite <- H26 in *.
										rewrite <- H4 in *.
										apply Hcons.
										unfold bentryBlockIndex. rewrite Hblocks0. intuition.
										rewrite <- H22. intuition.
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
										rewrite H22.
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
										{ rewrite H19. rewrite H21.
										 unfold CBlockEntry.
										destruct(lt_dec (blockindex x3) kernelStructureEntriesNb) eqn:Hdec ; try(exfalso ; congruence).
										intuition. simpl. intuition.
										destruct(lt_dec (blockindex x3) kernelStructureEntriesNb) eqn:Hdec' ; try(exfalso ; congruence).
 										cbn. reflexivity. destruct blockentry_d. destruct x3.
										intuition.
										}
										assert(blockindex x3 = blockindex x2).
										{ rewrite H24.
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
										rewrite <- H28 in *. rewrite <- H27 in *. rewrite <- H26 in *.
										rewrite <- H4 in *.
										apply Hcons.
										unfold bentryBlockIndex. rewrite Hblocks0. intuition.
										rewrite <- H22. intuition.
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
		intuition. apply isSCELookupEq in H22. destruct H22. rewrite H23 in *.
		exists x11. intuition.
		

		

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
(*isBE newBlockEntryAddr s /\*)
pdentryNbFreeSlots pdinsertion predCurrentNbFreeSlots s (*/\ predCurrentNbFreeSlots > 0*) /\
     (*pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s /\*)
   StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots 

/\ (exists s0, exists pdentry : PDTable, exists pdentry0 : PDTable, 
		exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6: BlockEntry,
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
                    MPU := MPU pdentry0;
										vidtBlock := vidtBlock pdentry0 |})
								(add pdinsertion
                 (PDT
                    {|
                    structure := structure pdentry;
                    firstfreeslot := newFirstFreeSlotAddr;
                    nbfreeslots := nbfreeslots pdentry;
                    nbprepare := nbprepare pdentry;
                    parent := parent pdentry;
                    MPU := MPU pdentry;
										vidtBlock := vidtBlock pdentry |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}

/\ lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
/\ lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6) /\
bentry6 = (CBlockEntry (read bentry5) (write bentry5) e (present bentry5) 
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
/\ sceaddr = (CPaddr (newBlockEntryAddr + scoffset))
(* (exists olds : state, P olds /\ partitionsIsolation olds /\
       verticalSharing olds /\ consistency olds /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr olds /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr olds)*)
/\ P s0 /\ partitionsIsolation s0 /\
       verticalSharing s0 /\ consistency s0 /\ pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0 /\
    bentryEndAddr newBlockEntryAddr newFirstFreeSlotAddr s0 (*/\ isBE newBlockEntryAddr s0*)
/\ isPDT pdinsertion s0 /\ (pdentryNbFreeSlots pdinsertion currnbfreeslots s0 /\ currnbfreeslots > 0)
)). 	intros. simpl.  set (s' := {|
      currentPartition :=  _|}).
			exists x. split.
			+ destruct (beqAddr (CPaddr (newBlockEntryAddr + scoffset)) pdinsertion) eqn:Hbeqpdx10.
				rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeqpdx10.
				unfold isPDT in *.
				rewrite Hbeqpdx10 in *. rewrite H18 in *. exfalso. congruence.
				rewrite removeDupIdentity. intuition.
				rewrite beqAddrFalse in *. intuition.
				rewrite beqAddrSym. congruence.
			(*+ split.
				+ unfold isBE. intuition. rewrite isBELookupEq in *. destruct H.
					cbn. destruct (beqAddr x10 newBlockEntryAddr) eqn:Hbeq.
					* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
						destruct H10. rewrite Hbeq in *. congruence.
					* rewrite removeDupIdentity. rewrite H. trivial.
						rewrite <- beqAddrFalse in Hbeq. intuition.*)
				+ intuition.
					++ unfold pdentryNbFreeSlots in *. cbn. rewrite <- H23 in *.
						destruct (beqAddr x10 pdinsertion) eqn:Hbeq.
							* rewrite <- DependentTypeLemmas.beqAddrTrue in Hbeq.
								assert(HPDT : isPDT pdinsertion s0) by intuition.
								apply isPDTLookupEq in HPDT. destruct HPDT.
								rewrite Hbeq in *. congruence.
							* rewrite removeDupIdentity. assumption.
								rewrite <- beqAddrFalse in Hbeq. intuition.
					++ 	exists s0. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
							exists x7. exists x8. exists x9. exists x10. exists x11.
							intuition.
							unfold s'. rewrite H4. rewrite H23. intuition. f_equal.
							destruct (beqAddr (CPaddr (newBlockEntryAddr + scoffset)) newBlockEntryAddr) eqn:HnewSCEq ; try(exfalso ; congruence).
							* rewrite <- DependentTypeLemmas.beqAddrTrue in HnewSCEq.
								rewrite HnewSCEq in *. congruence.
							* rewrite <- beqAddrFalse in HnewSCEq.
								rewrite removeDupIdentity ; intuition.
							
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
			admit. admit. admit. admit. admit. }
intros. simpl.*)

	eapply weaken. apply ret.
	intros.
destruct H as [newpd]. destruct H. destruct H0.
destruct H1.
destruct H2 as [s0 [pdentry [pdentry0 [bentry [bentry0 [bentry1 [bentry2
               [bentry3 [bentry4 [bentry5 [bentry6 [sceaddr [scentry [Hs Hpropag]]]]]]]]]]]]]].
intuition.
	- exists s0. intuition.
	- (* DUP *)
		unfold isBE.
		assert(HBE : lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6))
									by intuition.
		rewrite HBE ; trivial.
	- unfold consistency. split.
		{ (* wellFormedFstShadowIfBlockEntry *)
			unfold wellFormedFstShadowIfBlockEntry.
			intros pa HBEs.

			(* 1) isBE pa s in hypothesis: eliminate impossible values for pa *)
			destruct (beqAddr pdinsertion pa) eqn:beqpdpa in HBEs ; try(exfalso ; congruence).
			* (* pdinsertion = pa *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpa.
				rewrite <- beqpdpa in *.
				unfold isPDT in *. unfold isBE in *. rewrite H in *.
				exfalso ; congruence.
			* (* pdinsertion <> pa *)
				apply isBELookupEq in HBEs. rewrite Hs in HBEs. cbn in HBEs. destruct HBEs as [entry HBEs].
				destruct (beqAddr sceaddr pa) eqn:beqpasce in HBEs ; try(exfalso ; congruence).
				(* sceaddr <> pa *)
				destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:beqpdnewblock in HBEs ; try(exfalso ; congruence).
				**	(* pdinsertion = newBlockEntryAddr *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdnewblock.
						rewrite beqpdnewblock in *.
						unfold isPDT in *. unfold isBE in *. rewrite H in *.
						congruence.
				** 	(* pdinsertion <> newBlockEntryAddr *)
						destruct (beqAddr newBlockEntryAddr sceaddr) eqn:beqnewblocksce in HBEs ; try(exfalso ; congruence).
						*** (* newBlockEntryAddr = sceaddr *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewblocksce.
								rewrite beqnewblocksce in *.
								rewrite Hs in H4. cbn in H4. repeat rewrite beqAddrTrue in H4.
								congruence.
						*** (* newBlockEntryAddr <> sceaddr *)
								repeat rewrite beqAddrTrue in HBEs.
								cbn in HBEs.
								destruct (beqAddr newBlockEntryAddr pa) eqn:beqnewblockpa in HBEs ; try(exfalso ; congruence).
							**** 	(* 2) treat special case where newBlockEntryAddr = pa *)
										rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewblockpa.
										rewrite <- beqnewblockpa in *.
										assert(Hcons : wellFormedFstShadowIfBlockEntry s0)
														by (unfold consistency in *; intuition).
										unfold wellFormedFstShadowIfBlockEntry in *.
										specialize (Hcons newBlockEntryAddr).
										unfold isBE in Hcons.
										assert(HBE : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry))
													by intuition.
										rewrite HBE in *.
										apply isSHELookupEq.
										rewrite Hs. cbn.
										(* 3) eliminate impossible values for (CPaddr (newBlockEntryAddr + sh1offset)) *)
										destruct (beqAddr sceaddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:beqsceoffset ; try(exfalso ; congruence).
										++++ (* sceaddr = (CPaddr (newBlockEntryAddr + sh1offset)) *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceoffset.
													assert(HSCE : wellFormedShadowCutIfBlockEntry s0)
																	by (unfold consistency in *; intuition).
													specialize(HSCE newBlockEntryAddr).
													unfold isBE in HSCE.
													rewrite HBE in *. destruct HSCE ; trivial.
													intuition. subst x.
													unfold isSCE in *. unfold isSHE in *.
													rewrite <- beqsceoffset in *.
													rewrite <- H11 in *.
													destruct (lookup sceaddr (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
													destruct v eqn:Hv ; try(exfalso ; congruence).
										++++ (*sceaddr <> (CPaddr (newBlockEntryAddr + sh1offset))*)
													repeat rewrite beqAddrTrue.
													rewrite <- beqAddrFalse in *. intuition.
													repeat rewrite removeDupIdentity; intuition.
													destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hfalse. (*proved before *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in Hfalse ; congruence.
													cbn.
													destruct (beqAddr newBlockEntryAddr (CPaddr (newBlockEntryAddr + sh1offset))) eqn:newblocksh1offset.
													+++++ (* newBlockEntryAddr = (CPaddr (newBlockEntryAddr + sh1offset))*)
																rewrite <- DependentTypeLemmas.beqAddrTrue in newblocksh1offset.
																rewrite <- newblocksh1offset in *.
																unfold isSHE in *. rewrite HBE in *.
																exfalso ; congruence.
													+++++ (* newBlockEntryAddr <> (CPaddr (newBlockEntryAddr + sh1offset))*)
																cbn.
																rewrite <- beqAddrFalse in *. intuition.
																repeat rewrite removeDupIdentity; intuition.
																destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hffalse. (*proved before *)
																rewrite <- DependentTypeLemmas.beqAddrTrue in Hffalse ; congruence.
																cbn.
																destruct (beqAddr pdinsertion (CPaddr (newBlockEntryAddr + sh1offset))) eqn:pdsh1offset.
																++++++ (* pdinsertion = (CPaddr (newBlockEntryAddr + sh1offset))*)
																				rewrite <- DependentTypeLemmas.beqAddrTrue in *.
																				rewrite <- pdsh1offset in *.
																				unfold isSHE in *. unfold isPDT in *.
																				destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
																				destruct v eqn:Hv ; try(exfalso ; congruence).
																++++++ (* pdinsertion <> (CPaddr (newBlockEntryAddr + sh1offset))*)
																				rewrite <- beqAddrFalse in *.
																				repeat rewrite removeDupIdentity; intuition.
																				assert(HSHEs0: isSHE (CPaddr (newBlockEntryAddr + sh1offset)) s0)
																					by intuition.
																				apply isSHELookupEq in HSHEs0. destruct HSHEs0 as [shentry HSHEs0].
																				(* 4) resolve the only true case *)
																				exists shentry. easy.

							**** (* 4) treat special case where pa is not equal to any modified entries*)
										(* newBlockEntryAddr <> pa *)
										cbn in HBEs.
										destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hfalse ; try(exfalso ; congruence).
										rewrite <- beqAddrFalse in *.
										do 6 rewrite removeDupIdentity in HBEs; intuition.
										cbn in HBEs.
										destruct (beqAddr pdinsertion pa) eqn:Hffalse ; try(exfalso ; congruence).
										do 4 rewrite removeDupIdentity in HBEs; intuition.
										(* no modifictions of SHE so what is true at s0 is still true at s *)
										assert(HSHEEq : isSHE (CPaddr (pa + sh1offset)) s = isSHE (CPaddr (pa + sh1offset)) s0).
										{
											assert(HSHE : wellFormedFstShadowIfBlockEntry s0)
																		by (unfold consistency in *; intuition).
											specialize(HSHE pa).
											unfold isBE in HSHE.
											assert(HSCE : wellFormedShadowCutIfBlockEntry s0)
																		by (unfold consistency in *; intuition).
											specialize(HSCE pa).
											unfold isBE in HSCE.
											rewrite HBEs in *. intuition.
											destruct H22 as [scentryaddr]. intuition. subst scentryaddr.
											rewrite Hs. unfold isSHE. cbn.
											repeat rewrite beqAddrTrue.
											rewrite <- beqAddrFalse in *. intuition.
											repeat rewrite removeDupIdentity; intuition.
											assert(HBE : lookup newBlockEntryAddr (memory s0) beqAddr = Some (BE bentry))
																		by intuition.
											(* eliminate impossible values for (CPaddr (pa + sh1offset)) *)
											destruct (beqAddr sceaddr (CPaddr (pa + sh1offset))) eqn:Hscesh1offset.
											 - 	(* sceaddr = (CPaddr (pa + sh1offset)) *)
													rewrite <- DependentTypeLemmas.beqAddrTrue in Hscesh1offset.
													rewrite <- Hscesh1offset in *.
													assert(HSCE : isSCE sceaddr s0).
													{ rewrite H11.
														assert(HSCE : wellFormedShadowCutIfBlockEntry s0)
																					by (unfold consistency in *; intuition).
														specialize(HSCE newBlockEntryAddr).
														unfold isBE in HSCE.
														rewrite HBE in *. intuition.
														destruct H22. intuition. subst x.
														rewrite <- H11 in *.
														unfold isSHE in *. unfold isSCE in *.
														congruence.
													}
													apply isSCELookupEq in HSCE. destruct HSCE.
													rewrite H22. trivial.
													(* almost DUP with previous step *)
												- (* sceaddr <> (CPaddr (pa + sh1offset))*)
														destruct(beqAddr newBlockEntryAddr sceaddr) eqn:Hnewblocksce. (* Proved before *)
														rewrite <- DependentTypeLemmas.beqAddrTrue in Hnewblocksce ; congruence.
														cbn.
														rewrite <- beqAddrFalse in *.
														destruct (beqAddr newBlockEntryAddr (CPaddr (pa + sh1offset))) eqn:newblocksh1offset.
														+ (* newBlockEntryAddr = (CPaddr (pa + sh1offset))*)
															rewrite <- DependentTypeLemmas.beqAddrTrue in newblocksh1offset.
															rewrite <- newblocksh1offset in *.
															unfold isSHE in *. rewrite HBE in *.
															exfalso ; congruence.
														+ (* newBlockEntryAddr <> (CPaddr (pa + sh1offset))*)
															cbn.
															rewrite <- beqAddrFalse in *.
															repeat rewrite removeDupIdentity; intuition.
															destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hfffalse. (*proved before *)
															rewrite <- DependentTypeLemmas.beqAddrTrue in Hfffalse ; congruence.
															cbn.
															destruct (beqAddr pdinsertion (CPaddr (pa + sh1offset))) eqn:pdsh1offset.
															* (* pdinsertion = (CPaddr (pa + sh1offset))*)
																rewrite <- DependentTypeLemmas.beqAddrTrue in *.
																rewrite <- pdsh1offset in *.
																unfold isSHE in *. unfold isPDT in *.
																destruct (lookup pdinsertion (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
																destruct v eqn:Hv ; try(exfalso ; congruence).
															* (* pdinsertion <> (CPaddr (pa + sh1offset))*)
																rewrite <- beqAddrFalse in *.
																(* resolve the only true case *)
																repeat rewrite removeDupIdentity; intuition.
									}
									rewrite HSHEEq.
									assert(HSHE : wellFormedFstShadowIfBlockEntry s0)
																by (unfold consistency in *; intuition).
									specialize(HSHE pa).
									unfold isBE in HSHE.
									rewrite HBEs in *. intuition.
			}
	assert(beqAddr pdinsertion newBlockEntryAddr = false).
	{
		destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:beqpdnewblock; try(exfalso ; congruence).
		*	(* pdinsertion = newBlockEntryAddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdnewblock.
			rewrite beqpdnewblock in *.
			unfold isPDT in *. unfold isBE in *. rewrite H in *.
			congruence.
		* (* pdinsertion <> newBlockEntryAddr *)
			reflexivity.
	}
	assert(beqAddr newBlockEntryAddr sceaddr = false).
	{
		destruct (beqAddr newBlockEntryAddr sceaddr) eqn:beqnewblocksce ; try(exfalso ; congruence).
		* (* newBlockEntryAddr = sceaddr *)
								rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewblocksce.
								rewrite beqnewblocksce in *.
								rewrite Hs in H4. cbn in H4. repeat rewrite beqAddrTrue in H4.
								congruence.
		* (* newBlockEntryAddr <> sceaddr *)
			reflexivity.
	}
	assert(HSCE : isSCE sceaddr s0).
	{ rewrite H11.
		assert(HSCE : wellFormedShadowCutIfBlockEntry s0)
									by (unfold consistency in *; intuition).
		specialize(HSCE newBlockEntryAddr).
		unfold isBE in HSCE.
		rewrite H2 in *. intuition.
		destruct H23. intuition. subst x.
		rewrite <- H11 in *.
		unfold isSHE in *. unfold isSCE in *.
		congruence.
	}
	assert(beqAddr pdinsertion sceaddr = false).
	{
		destruct (beqAddr pdinsertion sceaddr) eqn:beqpdsce; try(exfalso ; congruence).
		*	(* pdinsertion = sceaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdsce.
			rewrite beqpdsce in *.
			unfold isPDT in *.
			apply isSCELookupEq in HSCE. destruct HSCE.
			rewrite H23 in *. exfalso;congruence.
		* (* pdinsertion <> sceaddr *)
			reflexivity.
	}
	assert(isSCE sceaddr s).
	{
		unfold isSCE. rewrite Hs. cbn.
		rewrite beqAddrTrue. trivial.
	}
	split.
	{ (* PDTIfPDFlag s *)
		assert(Hcons0 : forall idPDchild sh1entryaddr,
true = StateLib.checkChild idPDchild s0 sh1entryaddr /\
sh1entryAddr idPDchild sh1entryaddr s0 ->
exists startaddr, bentryStartAddr idPDchild startaddr s0 /\
 entryPDT idPDchild startaddr s0). admit. (* replace consistency with next assertion *)

		assert(forall idPDchild sh1entryaddr,
true = StateLib.checkChild idPDchild s sh1entryaddr /\
sh1entryAddr idPDchild sh1entryaddr s ->
exists startaddr, bentryStartAddr idPDchild startaddr s /\
 entryPDT idPDchild startaddr s).
		{
		(*unfold PDTIfPDFlag.*)
		intros idPDchild sh1entryaddr HcheckChilds.
		destruct HcheckChilds as [HcheckChilds Hsh1entryaddr].
		(* develop idPDchild *)
		unfold checkChild in HcheckChilds.
		unfold entryPDT.
		unfold bentryStartAddr.

		destruct(lookup idPDchild (memory s) beqAddr) eqn:Hlookup in HcheckChilds ; try(exfalso ; congruence).
		destruct v eqn:Hv ; try(exfalso ; congruence).

		(*exists b. intuition.*)
		eexists. intuition. rewrite Hlookup. intuition.
		(* check all values of idPDchild -> only newBlock is OK -> get to s0 because is freeSlot at s0
				-> pdflag can't be set -> check PDTIfPDFlags0
			or nothing then
			1) idPdchild is not modified in s -> lookup idPDchild s == lookup idPDchild s0

			1) (startAddr (blockrange b)) (memory s) == (startAddr (blockrange b)) (memory s0)
			and pdFlag is true at s0 because PDTIfPDFlags0 so OK
			2) startAddr (blockrange b)) = pdisnertion so ok
			3) startAddr (blockrange b)) = newblock so at s0 PDTIfPDFlags0 with idPDchild 
					and so newblock isPDT -> contra*)
		destruct (beqAddr pdinsertion idPDchild) eqn:beqpdidpd; try(exfalso ; congruence).
		*	(* pdinsertion = idPDchild *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdidpd.
			rewrite beqpdidpd in *.
			congruence.
		* (* pdinsertion <> pdinsertion *)
			destruct (beqAddr sceaddr idPDchild) eqn:beqsceidpd; try(exfalso ; congruence).
			**	(* sceaddr = idPDchild *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqsceidpd.
				unfold isSCE in *.
				rewrite <- beqsceidpd in *.
				rewrite Hlookup in *.
				exfalso; congruence.
			** (* sceaddr <> idPDchild *)
					assert(HidPDs0 : isBE idPDchild s0).
					{ rewrite Hs in Hlookup. cbn in Hlookup.
						rewrite beqAddrTrue in Hlookup.
						rewrite beqsceidpd in Hlookup.
						rewrite H22 in Hlookup. (*newBlock <> sce *)
						rewrite H20 in Hlookup. (*pd <> newblock*)
						rewrite beqAddrTrue in Hlookup.
						cbn in Hlookup.
						destruct (beqAddr newBlockEntryAddr idPDchild) eqn:beqnewidpd; try(exfalso ; congruence).
						* (* newBlockEntryAddr = idPDchild *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewidpd.
							rewrite <- beqnewidpd.
							apply isBELookupEq. exists bentry. intuition.
						* (* newBlockEntryAddr <> idPDchild *)
							rewrite H20 in Hlookup. (*pd <> newblock*)
							rewrite <- beqAddrFalse in *.
							do 6 rewrite removeDupIdentity in Hlookup; intuition.
							cbn in Hlookup.
							destruct (beqAddr pdinsertion idPDchild) eqn:Hff ;try (exfalso;congruence).
							do 4 rewrite removeDupIdentity in Hlookup; intuition.
							unfold isBE. rewrite Hlookup ; trivial.
					}
					intuition.

					assert(HfreeSlot : FirstFreeSlotPointerIsBEAndFreeSlot s0)
													by (unfold consistency in *; intuition).
					unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. Search pdinsertion.
					assert(HPDTs0 : isPDT pdinsertion s0) by intuition.
					apply isPDTLookupEq in HPDTs0. destruct HPDTs0 as [pds0 HPDTs0].
					assert(HfreeSlots0 : pdentryFirstFreeSlot pdinsertion newBlockEntryAddr s0)
						 by intuition.
					specialize (HfreeSlot pdinsertion pds0 HPDTs0).
					unfold pdentryFirstFreeSlot in HfreeSlots0.
					rewrite HPDTs0 in HfreeSlots0.
					assert(HfreeSlotNotNull : FirstFreeSlotPointerNotNullEq s0)
													by (unfold consistency in *; intuition).
					unfold FirstFreeSlotPointerNotNullEq in *.
					specialize (HfreeSlotNotNull pdinsertion currnbfreeslots).
					intuition.

					assert(Hsh1s0 : isSHE sh1entryaddr s0).
					{

					destruct (lookup sh1entryaddr (memory s) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
					destruct v0 eqn:Hv0 ; try(exfalso ; congruence).
					(* prove flag didn't change *)
					rewrite Hs in Hsh1.
					cbn in Hsh1.
					rewrite beqAddrTrue in Hsh1.
					destruct (beqAddr sceaddr sh1entryaddr) eqn:beqscesh1; try(exfalso ; congruence).
					rewrite H22 in *. (* newblock <> sce *)
					cbn in Hsh1.
					destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:beqnewsh1; try(exfalso ; congruence).
					destruct (beqAddr pdinsertion sh1entryaddr) eqn:beqpdsh1; try(exfalso ; congruence).
					* (* pdinsertion = sh1entryaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdsh1.
							rewrite <- beqpdsh1 in *.
							rewrite beqAddrTrue in Hsh1.
							rewrite <- beqAddrFalse in *.
							do 7 rewrite removeDupIdentity in Hsh1; intuition.
							destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:beqnewpd; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewpd.
							congruence.
							cbn in Hsh1.
							rewrite beqAddrTrue in Hsh1.
							congruence.
					* (* pdinsertion <> sh1entryaddr *)
							cbn in Hsh1.
							(*rewrite H18 in Hsh1.*)
							rewrite beqAddrTrue in Hsh1.
							rewrite <- beqAddrFalse in *.
							do 7 rewrite removeDupIdentity in Hsh1; intuition.
							cbn in Hsh1.
							destruct (beqAddr pdinsertion sh1entryaddr) eqn:Hfff ; try (exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
							destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:beqnewpd; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewpd.
							congruence.
							cbn in Hsh1; intuition.
							destruct (beqAddr pdinsertion sh1entryaddr) eqn:Hffff; try(exfalso ; congruence).
							do 3 rewrite removeDupIdentity in Hsh1; intuition.
							unfold isSHE. rewrite Hsh1 in *. trivial.
					}
					 (*assert(Hsh1eq : isSHE sh1entryaddr s0 = isSHE sh1entryaddr s).
					{ (* Partial DUP *)
						rewrite Hs. unfold isSHE.
						cbn.
						rewrite beqAddrTrue.
						apply isSHELookupEq in Hsh1s0. destruct Hsh1s0 as [xsh1 Hsh1s0].
						rewrite Hsh1s0.
						destruct (beqAddr sceaddr sh1entryaddr) eqn:beqscesh1; try(exfalso ; congruence).
						* (* sceaddr = sh1entryaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1.
							rewrite <- beqscesh1 in *.
							apply isSCELookupEq in HSCE. destruct HSCE as [x HSCE].
							rewrite HSCE in *; congruence.
						*	(* sceaddr <> sh1entryaddr *)
							rewrite H20 in *. (* newblock <> sce *)
							cbn.
							destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:beqnewsh1; try(exfalso ; congruence).
							** (* newBlockEntryAddr = sh1entryaddr *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewsh1.
									rewrite <- beqnewsh1 in *.
									congruence.
							** (* newBlockEntryAddr <> sh1entryaddr *)
									rewrite H20. (*pd <> newblock *)
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity; intuition.
									cbn.
									destruct (beqAddr pdinsertion sh1entryaddr) eqn:beqpdsh1; try(exfalso ; congruence).
									*** (* pdinsertion = sh1entryaddr *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdsh1.
											rewrite <- beqpdsh1 in *.
											unfold isPDT in *.
											rewrite Hsh1s0 in *. exfalso ; congruence.
									*** (* pdinsertion <> sh1entryaddr *)
											cbn.
											rewrite <- beqAddrFalse in *.
											rewrite beqAddrTrue.
											destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:Hff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hfff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											destruct (beqAddr pdinsertion sh1entryaddr) eqn:Hffff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hffff. congruence.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											rewrite Hsh1s0. trivial.
					}
					assert(Hsh1s : isSHE sh1entryaddr s).
					{ (*DUP of eq*)
						destruct (lookup sh1entryaddr (memory s) beqAddr) eqn:Hsh1 ; try(exfalso ; congruence).
						destruct v0 eqn:Hv0 ; try(exfalso ; congruence).
						rewrite Hs. unfold isSHE.
						cbn.
						rewrite beqAddrTrue.
						destruct (beqAddr sceaddr sh1entryaddr) eqn:beqscesh1; try(exfalso ; congruence).
						* (* sceaddr = sh1entryaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1.
							rewrite <- beqscesh1 in *.
							assert(HSCEs : isSCE sceaddr s) by intuition.
							apply isSCELookupEq in HSCEs. destruct HSCEs as [x HSCEs].
							rewrite HSCEs in *; congruence.
						*	(* sceaddr <> sh1entryaddr *)
							rewrite H20 in *. (* newblock <> sce *)
							cbn.
							destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:beqnewsh1; try(exfalso ; congruence).
							** (* newBlockEntryAddr = sh1entryaddr *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewsh1.
									rewrite <- beqnewsh1 in *.
									congruence.
							** (* newBlockEntryAddr <> sh1entryaddr *)
									rewrite H20. (* pd <> newblock *)
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity; intuition.
									cbn.
									destruct (beqAddr pdinsertion sh1entryaddr) eqn:beqpdsh1; try(exfalso ; congruence).
									*** (* pdinsertion = sh1entryaddr *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdsh1.
											rewrite <- beqpdsh1 in *.
											unfold isPDT in *.
											exfalso ; congruence.
									*** (* pdinsertion <> sh1entryaddr *)
											cbn.
											rewrite <- beqAddrFalse in *.
											rewrite beqAddrTrue.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hf; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:Hff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hfff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											destruct (beqAddr pdinsertion sh1entryaddr) eqn:Hffff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hffff. congruence.
											repeat rewrite removeDupIdentity; intuition.
	}*)

					specialize(Hcons0 idPDchild sh1entryaddr).
					unfold checkChild in Hcons0.
					apply isBELookupEq in HidPDs0. destruct HidPDs0 as [x HidPDs0].
					rewrite HidPDs0 in Hcons0.
					apply isSHELookupEq in Hsh1s0. destruct Hsh1s0 as [y Hsh1s0].
					rewrite Hsh1s0 in *.
						destruct (beqAddr newBlockEntryAddr idPDchild) eqn:beqnewidpd; try(exfalso ; congruence).
						*** (* newBlockEntryAddr = idPDchild *)
								(* newBlockEntryAddr at s0 is firstfreeslot *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewidpd.
							rewrite <- beqnewidpd.
							rewrite <- HfreeSlots0 in HfreeSlot.
							destruct HfreeSlot as [isBEs0 isFreeSlots0].
							intuition.
							destruct H27 (*right part of FirstFreeSlotPointerNotNullEq*).
							unfold pdentryFirstFreeSlot in *. rewrite HPDTs0 in H27.
							intuition.
							congruence.
							unfold isFreeSlot in isFreeSlots0.
							rewrite H2 in isFreeSlots0.
							unfold sh1entryAddr in Hsh1entryaddr.
							rewrite Hlookup in Hsh1entryaddr.
							rewrite <- beqnewidpd in Hsh1entryaddr.
							rewrite <- Hsh1entryaddr in isFreeSlots0.
							rewrite Hsh1s0 in isFreeSlots0.
							rewrite <- H11 in isFreeSlots0.
							apply isSCELookupEq in HSCE. destruct HSCE as [scentrys0 HSCEs0].
							rewrite HSCEs0 in isFreeSlots0.
							
						exfalso.
						destruct (beqAddr sceaddr sh1entryaddr) eqn:beqscesh1; try(exfalso ; congruence).
						-- (* sceaddr = sh1entryaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1.
							rewrite <- beqscesh1 in *.
							assert(HSCEs : isSCE sceaddr s) by intuition.
							apply isSCELookupEq in HSCEs. destruct HSCEs as [scentrys HSCEs].
							rewrite HSCEs in *; congruence.
						--	(* sceaddr <> sh1entryaddr *)
							(*rewrite H20 in *. (* newblock <> sce *)
							cbn.*)
							destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:beqnewsh1; try(exfalso ; congruence).
							--- (* newBlockEntryAddr = sh1entryaddr *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewsh1.
									rewrite <- beqnewsh1 in *.
									congruence.
							--- (* newBlockEntryAddr <> sh1entryaddr *)
									(*rewrite H20. (* pd <> newblock *)*)
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity; intuition.
									cbn.
									destruct (beqAddr pdinsertion sh1entryaddr) eqn:beqpdsh1; try(exfalso ; congruence).
									---- (* pdinsertion = sh1entryaddr *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdsh1.
											rewrite <- beqpdsh1 in *.
											unfold isPDT in *.
											exfalso ; congruence.
									---- (* pdinsertion <> sh1entryaddr *)
											rewrite Hs in HcheckChilds.
											cbn in HcheckChilds.
											rewrite <- beqAddrFalse in *.
											rewrite beqAddrTrue in HcheckChilds.
											repeat rewrite removeDupIdentity in HcheckChilds; intuition.
											cbn in HcheckChilds.
											destruct (beqAddr sceaddr sh1entryaddr) eqn:Hf; try(exfalso ; congruence).
											destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:Hff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
											destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hfff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hfff. congruence.
											cbn in HcheckChilds.

											destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:Hfffff; try(exfalso ; congruence).
											do 7 rewrite removeDupIdentity in HcheckChilds; intuition.
											destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hffff; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hffff. congruence.
											cbn in HcheckChilds.
											destruct (beqAddr pdinsertion sh1entryaddr) eqn:Hffffff; try(exfalso ; congruence).
											rewrite beqAddrTrue in HcheckChilds.
											do 3 rewrite removeDupIdentity in HcheckChilds; intuition.
											rewrite Hsh1s0 in HcheckChilds.
											congruence.
						*** (* newBlockEntryAddr <> idPDchild *)
								assert(HidPDchildEq : lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s0) beqAddr).
								{ Search sceaddr.
									rewrite Hs.
									cbn.
									rewrite beqAddrTrue.
									rewrite beqsceidpd. rewrite H22.
									cbn.
									rewrite beqnewidpd. rewrite H20.
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity ; intuition.
									cbn. Search idPDchild.
									destruct (beqAddr pdinsertion idPDchild) eqn:Hf; try(exfalso ; congruence).
									rewrite <- DependentTypeLemmas.beqAddrTrue in Hf. congruence.
									rewrite beqAddrTrue.
									repeat rewrite removeDupIdentity ; intuition.
								}
									rewrite HidPDchildEq.
									rewrite HidPDs0.
									rewrite HidPDs0 in HidPDchildEq.
									rewrite Hlookup in HidPDchildEq.
									injection HidPDchildEq ; intro bentryEq.
									Search x.
									(* PDflag can only be true for anything except the modified state, because
											the only candidate is newBlockEntryAddr which was a free slot so
											flag is null -> contra*)
									destruct Hcons0.
								 { rewrite Hs in HcheckChilds.
								cbn in HcheckChilds.
								rewrite <- beqAddrFalse in *.
								rewrite beqAddrTrue in HcheckChilds.
								destruct (beqAddr sceaddr sh1entryaddr) eqn:Hf; try(exfalso ; congruence).
								rewrite <- beqAddrFalse in *.
								cbn in HcheckChilds.
								destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hff; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hff. congruence.
								cbn in HcheckChilds.
								destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:Hfff; try(exfalso ; congruence).
								cbn in HcheckChilds.
								rewrite <- beqAddrFalse in *.
								do 7 rewrite removeDupIdentity in HcheckChilds; intuition.
								destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hffff; try(exfalso ; congruence).
								rewrite <- DependentTypeLemmas.beqAddrTrue in Hffff. congruence.
								cbn in HcheckChilds.
								destruct (beqAddr pdinsertion sh1entryaddr) eqn:Hfffff; try(exfalso ; congruence).
								cbn in HcheckChilds.
								rewrite beqAddrTrue in HcheckChilds.
								rewrite <- beqAddrFalse in *.
								do 3 rewrite removeDupIdentity in HcheckChilds; intuition.
								rewrite Hsh1s0 in HcheckChilds.
								congruence.
								unfold sh1entryAddr.
								rewrite HidPDs0.
								unfold sh1entryAddr in Hsh1entryaddr.
								rewrite Hlookup in Hsh1entryaddr.
								assumption.
								}
								unfold bentryStartAddr in H25. unfold entryPDT in H25.
								rewrite HidPDs0 in H25. intuition.
								rewrite <- H29 in *.
								
						rewrite Hs. cbn.
						rewrite beqAddrTrue.
						destruct (beqAddr sceaddr x0) eqn:beqscex0; try(exfalso ; congruence).
						- (* sceaddr = x0 *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqscex0.
							rewrite <- beqscex0 in *.
							apply isSCELookupEq in HSCE. destruct HSCE as [sceaddr' HSCE].
							rewrite HSCE in *; congruence.
						-	(* sceaddr <> x0 *)
							rewrite <- beqscex0 in *. (* newblock <> sce *)
							cbn.
							destruct (beqAddr newBlockEntryAddr sceaddr) eqn:beqnewsce; try(exfalso ; congruence).
							cbn.
							destruct (beqAddr newBlockEntryAddr x0) eqn:beqnewx0; try(exfalso ; congruence).
							-- (* newBlockEntryAddr = x0 *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewx0.
									rewrite <- beqnewx0 in *. rewrite H2 in H30.
									congruence.
							-- (* newBlockEntryAddr <> x0 *)
									rewrite <- beqAddrFalse in *.
									repeat rewrite removeDupIdentity; intuition.
									cbn.
									destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:beqpdnew; try(exfalso ; congruence).
									cbn.
									destruct (beqAddr pdinsertion x0) eqn:beqpdx0; try(exfalso ; congruence).
									--- (* pdinsertion = x0 *)
											rewrite bentryEq. intuition.
									--- (* pdinsertion <> x0 *)
											rewrite beqAddrTrue.
											rewrite <- beqAddrFalse in *.
											repeat rewrite removeDupIdentity; intuition.
											destruct (lookup x0 (memory s0) beqAddr) eqn:Hlookupx0 ; try (exfalso ; congruence).
											destruct v0 eqn:Hv0 ; try (exfalso ; congruence).
											rewrite bentryEq. intuition.
				} (* end new PDTIfPDFlag*)


					unfold isSHE in Hsh1s.
					assert(HSh1eq : lookup sh1entryaddr (memory s0) beqAddr = lookup sh1entryaddr (memory s) beqAddr).
					{

						destruct (beqAddr sceaddr sh1entryaddr) eqn:beqscesh1; try(exfalso ; congruence).
						+ (* sceaddr = sh1entryaddr *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in beqscesh1.
							rewrite <- beqscesh1 in *.
							assert(HSCEs : isSCE sceaddr s) by intuition.
							apply isSCELookupEq in HSCEs. destruct HSCEs as [z HSCEs].
							rewrite HSCEs in *; congruence.
						+	(* sceaddr <> sh1entryaddr *)
							destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:beqnewsh1; try(exfalso ; congruence).
							++ (* newBlockEntryAddr = sh1entryaddr *)
									rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewsh1.
									rewrite <- beqnewsh1 in *.
									congruence.
							++ (* newBlockEntryAddr <> sh1entryaddr *)
									destruct (beqAddr pdinsertion sh1entryaddr) eqn:beqpdsh1; try(exfalso ; congruence).
									*** (* pdinsertion = sh1entryaddr *)
											rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdsh1.
											rewrite <- beqpdsh1 in *.
											unfold isPDT in *.
											rewrite H in *.
											exfalso ; congruence.
									*** (* pdinsertion <> sh1entryaddr *)
											rewrite Hs.
											cbn.
											repeat rewrite beqAddrTrue.
											destruct (beqAddr sceaddr sh1entryaddr) eqn:Hf ; try(exfalso ; congruence).
											destruct (beqAddr newBlockEntryAddr sceaddr) eqn:Hff ; try(exfalso ; congruence).
											cbn.
											destruct (beqAddr newBlockEntryAddr sh1entryaddr) eqn:Hfff ; try(exfalso ; congruence).
											destruct (beqAddr pdinsertion newBlockEntryAddr) eqn:Hffff ; try (exfalso ; congruence).
											rewrite <- beqAddrFalse in *.
											repeat rewrite removeDupIdentity; intuition.
											cbn.
											cbn.
											destruct (beqAddr pdinsertion sh1entryaddr) eqn:Hfffff ; try(exfalso ; congruence).
											rewrite <- DependentTypeLemmas.beqAddrTrue in Hfffff.
											congruence.
											repeat rewrite removeDupIdentity; intuition.
				}
					rewrite <- HSh1eq in HcheckChilds.
					rewrite Hsh1s0 in HcheckChilds. trivial.

					unfold bentryStartAddr in *. unfold entryPDT in *.
					rewrite HidPDs0 in *.
					intuition.



		destruct (beqAddr pdinsertion (startAddr (blockrange b))) eqn:beqpdstart; try(exfalso ; congruence).
		***	(* pdinsertion = startaddr *)
			rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdstart.
			rewrite <- beqpdstart.
			rewrite H. trivial.
		*** (* pdinsertion <> startaddr *)
			destruct (beqAddr sceaddr (startAddr (blockrange b))) eqn:beqscestart; try(exfalso ; congruence).
			****	(* sceaddr = startaddr *)
				rewrite <- DependentTypeLemmas.beqAddrTrue in beqscestart.
				rewrite <- beqscestart.
				apply isSCELookupEq in HSCE. destruct HSCE.
				unfold isSCE in *.
				specialize(Hcons0 idPDchild sh1entryaddr).
				unfold checkChild in Hcons0.
				rewrite 
				rewrite H23 in *. exfalso;congruence.
				rewrite H11.

				
			* (* pdinsertion <> startaddr *)

cbn.
		destruct (lookup (startAddr (blockrange b)) (memory s) beqAddr) eqn:Hlookup'' ; try(exfalso ; congruence).
		destruct v1 eqn:Hv'' ; try(exfalso ; congruence).

		assert(HPDTIfPDFlags0 : PDTIfPDFlag s0) by (unfold consistency in * ; intuition).
		unfold PDTIfPDFlag in HPDTIfPDFlags0.
		specialize(HPDTIfPDFlags0 idPDchild sh1entryaddr).
		unfold checkChild in HPDTIfPDFlags0.
		assert(exists entry, lookup idPDchild (memory s0) beqAddr = Some (BE entry)).
		admit.
		assert(exists entry', lookup sh1entryaddr (memory s0) beqAddr = Some (SHE entry')).
		admit.
		destruct H22, H23. rewrite H22 in *. rewrite H23 in *.
		destruct HPDTIfPDFlags0.

		destruct (beqAddr newBlockEntryAddr idPDchild) eqn:beqnewblockidPDchild in HcheckChilds ; try(exfalso ; congruence).
		* 	(* 2) treat special case where newBlockEntryAddr = idPDchild *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in beqnewblockidPDchild.
					rewrite <- beqnewblockidPDchild in *.
					assert(HBEs : lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry6))
								by intuition.
					rewrite HBEs in *.
					
}
	- (* Final state *)
		exists newpd. intuition. exists s0. exists pdentry. exists pdentry0.
		exists bentry. exists bentry0. exists bentry1. exists bentry2. exists bentry3.
		exists bentry4. exists bentry5. exists bentry6. exists sceaddr. exists scentry.
		exists newBlockEntryAddr. exists newFirstFreeSlotAddr. exists predCurrentNbFreeSlots.
		intuition.

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
}
			admit. admit. admit. admit. admit. }
intros. simpl.*)

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