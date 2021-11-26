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

Require Import Model.ADT Model.Lib Model.MAL.
Require Import Core.Services.

Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib (*Proof.InternalLemmas Proof.InternalLemmas2*) Proof.DependentTypeLemmas.

Require Import Invariants checkChildOfCurrPart insertNewEntry.

Require Import Bool List EqNat.

Require Import Model.Monad.

Module WP := WeakestPreconditions.

(** * Summary 
    This file contains the invariant of [addMemoryBlock].
    We prove that this PIP service preserves the isolation property *)

Lemma addMemoryBlock  (idPDchild idBlockToShare: paddr) (r w e : bool) :
{{fun s => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
Services.addMemoryBlock idPDchild idBlockToShare r w e 
{{fun _ s  => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold addMemoryBlock.
eapply WP.bindRev.
{ (** getCurPartition **)
	eapply WP.weaken. apply Invariants.getCurPartition.
	cbn. intros. split. exact H. intuition.
}
intro currentPart.
eapply WP.bindRev.
{ (** findBlockInKSWithAddr **)
	eapply weaken. eapply findBlockInKSWithAddr.findBlockInKSWithAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockToShareInCurrPartAddr.
eapply WP.bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H.
}
intro addrIsNull.
case_eq addrIsNull.
- (* case_eq addrIsNull = true *)
	intros.
	{ (** ret **)
		eapply WP.weaken. apply WP.ret.
  	simpl. intros. intuition.
}
- (* case_eq addrIsNull = false *)
	intros.
	eapply bindRev.
	{ (** checkRights **)
		eapply weaken. apply Invariants.checkRights.
		intros. simpl. split. apply H0. rewrite <- beqAddrFalse in *. intuition.
		destruct H8. exists x. apply H5.
	}
	intro rcheck.
	case_eq (negb rcheck).
	+ (* case_eq negb rcheck = true *)
		intros.
	{ (** ret **)
		eapply WP.weaken. apply WP.ret.
  	simpl. intros. intuition.
}
	+ (* case_eq negb rcheck = false *)
		intros.
		eapply WP.bindRev.
		{ (** checkChildOfCurrPart **)
			eapply weaken. apply checkChildOfCurrPart.checkChildOfCurrPart.
			intros. simpl. split. apply H1. intuition.
		}
		intro isChildCurrPart.
case_eq (negb isChildCurrPart).
* (* case_eq negb isChildCurrPart = true *)
	intros.
	{ (** ret **)
		eapply WP.weaken. apply WP.ret.
  	simpl. intros. intuition.
}
* (* case_eq negb isChildCurrPart = true *)
	intros.
	eapply WP.bindRev.
	{ (** readBlockStartFromBlockEntryAddr **)
		eapply weaken. apply Invariants.readBlockStartFromBlockEntryAddr.
		intros. simpl. split. apply H2.
		repeat rewrite <- beqAddrFalse in *. (* get rid of NULL conditions since we
		are in this branch *)
		rewrite negb_false_iff in *. (* get rif of trivial cases *)
		intuition.
		(* child has been checked, we know that idPDchild is valid and isBE *)
		destruct H9. destruct H4. destruct H9.
		unfold isBE. intuition. rewrite H15; trivial.
	}
	intro globalIdPDChild.
	eapply WP.bindRev.
	{ (** readPDNbFreeSlots **)
		eapply weaken. apply Invariants.readPDNbFreeSlots.
		intros. simpl. split. apply H2.
		repeat rewrite <- beqAddrFalse in *. rewrite negb_false_iff in *. intuition.
		(* globalIdPDChild is a PDT because it is the start address of idPDchild 
				who is a child *)
		unfold bentryStartAddr in *. destruct H10. destruct H5.
		destruct H10. destruct H10.
		unfold consistency in *.
		unfold PDTIfPDFlag in *. intuition.
		unfold entryPDT in *.
		destruct H19 with idPDchild x. subst. intuition.
		destruct H62.
		rewrite H10 in *. rewrite <- H4 in *.
		unfold isPDT.
		destruct (lookup globalIdPDChild (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
		destruct v eqn:Hv ; try (exfalso ; congruence).
		trivial.
	}
	intro nbfreeslots.
	eapply bindRev.
	{ (** zero **)
		eapply weaken. apply Invariants.Index.zero.
		intros. simpl. apply H2.
	}
	intro zero.
	eapply bindRev.
	{ (** MALInternal.Index.leb nbfreeslots zero **)
		eapply weaken. apply Invariants.Index.leb.
		intros. simpl. apply H2.
	}
	intro isFull.
	case_eq (isFull).
	-- (* case_eq isFull = false *)
			intros.
			{ (** ret **)
				eapply weaken. apply WP.ret.
				intros. simpl. apply H3.
			}
	-- (*case_eq isFull = true *)
			intros.
			eapply bindRev.
			{ (** readBlockAccessibleFromBlockEntryAddr *)
				eapply weaken. apply readBlockAccessibleFromBlockEntryAddr. 
				intros. simpl. split. apply H3.
				repeat rewrite beqAddrFalse in *. rewrite negb_false_iff in *. subst.
				intuition ; (unfold isBE ; destruct H6 ; rewrite -> H5 ; trivial).
			}
			intro addrIsAccessible.
			case_eq (negb addrIsAccessible).
			++ (*case_eq negb addrIsAccessible = true *)
				intros. simpl.
				{ (** ret **)
					eapply weaken. apply WP.ret.
					intros. simpl. intuition.
				}
			++ (*case_eq negb addrIsAccessible = false *)
					intros.
					eapply bindRev.
					{ (** readBlockPresentFromBlockEntryAddr **)
						eapply weaken. apply readBlockPresentFromBlockEntryAddr.
						intros. simpl. split. apply H4.
						repeat rewrite <- beqAddrFalse in *.
						unfold isBE. intuition.
						destruct H19. destruct H16. rewrite -> H16. trivial.
					}
					intro addrIsPresent.
					case_eq (negb addrIsPresent).
					** (*case_eq negb addrIsPresent = true *)
						intros. simpl.
						{ (** ret **)
							eapply weaken. apply WP.ret.
							intros. simpl. intuition.
						}
					** (*case_eq negb addrIsPresent = false *)
							intros.
							eapply bindRev.
						{	(** readBlockStartFromBlockEntryAddr **)
							eapply weaken. apply readBlockStartFromBlockEntryAddr.
							intros. simpl. split. apply H5.
							repeat rewrite <- beqAddrFalse in *.
							unfold isBE. intuition.
							destruct H21. destruct H18. rewrite -> H18. trivial.
						}
						intro blockstart.
						eapply bindRev.
						{	(** readBlockEndFromBlockEntryAddr **)
							eapply weaken. apply readBlockEndFromBlockEntryAddr.
							intros. simpl. split. apply H5.
							repeat rewrite <- beqAddrFalse in *.
							unfold isBE. intuition.
							destruct H22. destruct H19. rewrite -> H19. trivial.
						}
						intro blockend.

(* Start of structure modifications *)
	


(* 1) traiter les instructions de modifications en paquet *)
	eapply bindRev.
{ eapply weaken. apply insertNewEntry.insertNewEntry.
	intros. simpl.
	split. intuition. split. intuition. split. intuition.
	split.
	- repeat rewrite beqAddrFalse in *. rewrite negb_false_iff in *. subst.
		(* DUP : globalIdPDChild is a PDT because it is the start address of idPDchild 
				who is a child *)
		unfold bentryStartAddr in *. intuition .
		+ destruct H14. destruct H9.
			destruct H14. destruct H14.
			unfold consistency in *.
			unfold PDTIfPDFlag in *. intuition.
			unfold entryPDT in *.
			destruct H23 with idPDchild x. subst. intuition.
			destruct H66.
			rewrite H66 in *. rewrite <- H8 in *.
			unfold isPDT.
			destruct (lookup globalIdPDChild (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
			destruct v eqn:Hv ; try (exfalso ; congruence).
			exists p. trivial.

		(* DUP of before *)
		+ destruct H14. destruct H9.
			destruct H14. destruct H14.
			unfold consistency in *.
			unfold PDTIfPDFlag in *. intuition.
			unfold entryPDT in *.
			destruct H23 with idPDchild x. subst. intuition.
			destruct H66.
			rewrite H66 in *. rewrite <- H8 in *.
			unfold isPDT.
			destruct (lookup globalIdPDChild (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
			destruct v eqn:Hv ; try (exfalso ; congruence).
			exists p. trivial.
	- split. intuition. unfold StateLib.Index.leb in *.
		assert(PeanoNat.Nat.leb nbfreeslots zero = false) by intuition.
		apply PeanoNat.Nat.leb_gt. assert (zero = CIndex 0) by intuition.
		subst. simpl in H6. intuition.
 }
	intro blockToShareChildEntryAddr. simpl.


eapply bindRev.
	{ (** MAL.writeSh1PDChildFromBlockEntryAddr **)
		unfold MAL.writeSh1PDChildFromBlockEntryAddr.
		eapply bindRev. 
		{ (** MAL.getSh1EntryAddrFromBlockEntryAddr **) 
			eapply weaken. apply getSh1EntryAddrFromBlockEntryAddr.
			intros. split. apply H5.
			assert(consistency s). admit.
			unfold consistency in *. intuition.
			apply isBELookupEq. 
			unfold isBE. cbn. admit.
		}
		intro Sh1EAddr.
		{ (** MAL.writeSh1PDChildFromBlockEntryAddr **)

			eapply weaken. apply writeSh1PDChildFromBlockEntryAddr2.
			intros. intuition. destruct H7 as [oldsh1entry oldSh1H].
			exists oldsh1entry. intuition. Set Printing All. Check _ tt _.
instantiate (1:= fun _ s =>
((exists
         (originals0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 bentry4
                                                    bentry5 : BlockEntry) 
       (sceaddr : paddr) (scentry : SCEntry) (newBlockEntryAddr
                                              newFirstFreeSlotAddr : paddr) 
       (predCurrentNbFreeSlots : index) (sh1eaddr : paddr)
       (sh1entry : Sh1Entry),
         s =
         {|
         currentPartition := currentPartition originals0;
         memory := add sh1eaddr
                     (SHE
                        {|
                        PDchild := globalIdPDChild;
                        PDflag := PDflag sh1entry;
                        inChildLocation := inChildLocation sh1entry |})
                     (add sceaddr
                        (SCE {| origin := blockstart; next := next scentry |})
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry5) 
                                 (write bentry5) e (present bentry5)
                                 (accessible bentry5) (blockindex bentry5)
                                 (blockrange bentry5)))
                           (add newBlockEntryAddr
                              (BE
                                 (CBlockEntry (read bentry4) w 
                                    (exec bentry4) (present bentry4)
                                    (accessible bentry4) 
                                    (blockindex bentry4) 
                                    (blockrange bentry4)))
                              (add newBlockEntryAddr
                                 (BE
                                    (CBlockEntry r (write bentry3) 
                                       (exec bentry3) (present bentry3)
                                       (accessible bentry3) 
                                       (blockindex bentry3) 
                                       (blockrange bentry3)))
                                 (add newBlockEntryAddr
                                    (BE
                                       (CBlockEntry (read bentry2) 
                                          (write bentry2) 
                                          (exec bentry2) true 
                                          (accessible bentry2) 
                                          (blockindex bentry2) 
                                          (blockrange bentry2)))
                                    (add newBlockEntryAddr
                                       (BE
                                          (CBlockEntry (read bentry1) 
                                             (write bentry1) 
                                             (exec bentry1) 
                                             (present bentry1) true
                                             (blockindex bentry1)
                                             (blockrange bentry1)))
                                       (add newBlockEntryAddr
                                          (BE
                                             (CBlockEntry 
                                                (read bentry0) 
                                                (write bentry0) 
                                                (exec bentry0) 
                                                (present bentry0)
                                                (accessible bentry0)
                                                (blockindex bentry0)
                                                (CBlock
                                                   (startAddr (blockrange bentry0))
                                                   blockend)))
                                          (add newBlockEntryAddr
                                             (BE
                                                (CBlockEntry 
                                                   (read bentry) 
                                                   (write bentry) 
                                                   (exec bentry) 
                                                   (present bentry)
                                                   (accessible bentry)
                                                   (blockindex bentry)
                                                   (CBlock blockstart
                                                      (endAddr (blockrange bentry)))))
                                             (add globalIdPDChild
                                                (PDT
                                                   {|
                                                   structure := structure pdentry0;
                                                   firstfreeslot := firstfreeslot
                                                        pdentry0;
                                                   nbfreeslots := predCurrentNbFreeSlots;
                                                   nbprepare := nbprepare pdentry0;
                                                   parent := parent pdentry0;
                                                   MPU := MPU pdentry0 |})
                                                (add globalIdPDChild
                                                   (PDT
                                                      {|
                                                      structure := structure pdentry;
                                                      firstfreeslot := newFirstFreeSlotAddr;
                                                      nbfreeslots := ADT.nbfreeslots
                                                        pdentry;
                                                      nbprepare := nbprepare pdentry;
                                                      parent := parent pdentry;
                                                      MPU := MPU pdentry |})
                                                   (memory originals0) beqAddr) beqAddr)
                                             beqAddr) beqAddr) beqAddr) beqAddr)
                                 beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
(*/\ sh1eaddr = Sh1EAddr*) /\
       exists olds1, lookup sh1eaddr (memory olds1) beqAddr = Some (SHE sh1entry) /\
			isBE blockToShareChildEntryAddr olds1
) /\
      isBE blockToShareChildEntryAddr s)
     (*(exists sh1entry : Sh1Entry,
        lookup Sh1EAddr (memory s) beqAddr = Some (SHE sh1entry) /\
        sh1entryAddr blockToShareInCurrPartAddr Sh1EAddr s)*)
). intros. simpl. intuition. destruct H8. exists x.
	destruct H8. destruct H8. exists x0. exists x1. destruct H8. destruct H8. destruct H8.
	destruct H8. destruct H8. destruct H8. destruct H8.
	 exists x2. exists x3. exists x4. exists x5. exists x6.
	 exists x7. exists x8. destruct H8. destruct H8. exists x9. exists x10.
	destruct H8. destruct H8. destruct H8. exists x11. exists x12. exists x13.
exists Sh1EAddr. exists oldsh1entry.
	intuition. f_equal. rewrite H8. cbn. reflexivity. f_equal.
rewrite H8. cbn. reflexivity. exists s. intuition.

	apply isBELookupEq in H5. apply isBELookupEq.
	destruct H5 as[oldbentry]. exists oldbentry.
	cbn.
	destruct (beqAddr Sh1EAddr blockToShareChildEntryAddr) eqn:Hbeq.
	- rewrite <- beqAddrTrue in *. subst.
		contradict H6. unfold not. congruence.
	- rewrite removeDupIdentity. assumption.
		unfold not. intros. subst. congruence.
}
}
	intros.
eapply bindRev.
	{ (** MAL.writeSh1InChildLocationFromBlockEntryAddr **)
		unfold MAL.writeSh1InChildLocationFromBlockEntryAddr.
		eapply bindRev. 
		{ (** MAL.getSh1EntryAddrFromBlockEntryAddr **) 
			eapply weaken. apply getSh1EntryAddrFromBlockEntryAddr.
			intros. split. apply H5.
			assert(consistency s). admit.
			unfold consistency in *. intuition.
			apply isBELookupEq. admit.
		}
		intro Sh1EAddr. simpl.
		{ (** MAL.writeSh1InChildLocationFromBlockEntryAddr2 **)

			eapply weaken. apply writeSh1InChildLocationFromBlockEntryAddr2.
			intros. intuition.
(*			destruct H5. destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
			destruct H5. destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
			destruct H5. destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
			exists x15.
			destruct H6 as [oldSh1H]. intuition.*)

			destruct H7 as [previoussh1entry oldSh1H].
			exists previoussh1entry. intuition.
instantiate (1:= fun _ s =>
((exists
         (originals0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 bentry4
                                                    bentry5 : BlockEntry) 
       (sceaddr : paddr) (scentry : SCEntry) (newBlockEntryAddr
                                              newFirstFreeSlotAddr : paddr) 
       (predCurrentNbFreeSlots : index) (sh1eaddr : paddr)
       (sh1entry sh1entry1: Sh1Entry) (oldsh1eaddr : paddr),
         s =
         {|
         currentPartition := currentPartition originals0;
         memory := add sh1eaddr
              (SHE
                 {|
                 PDchild := PDchild sh1entry1;
                 PDflag := PDflag sh1entry1;
                 inChildLocation := blockToShareChildEntryAddr |}) 
									(add oldsh1eaddr
                     (SHE
                        {|
                        PDchild := globalIdPDChild;
                        PDflag := PDflag sh1entry;
                        inChildLocation := inChildLocation sh1entry |})
                     (add sceaddr
                        (SCE {| origin := blockstart; next := next scentry |})
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry5) 
                                 (write bentry5) e (present bentry5)
                                 (accessible bentry5) (blockindex bentry5)
                                 (blockrange bentry5)))
                           (add newBlockEntryAddr
                              (BE
                                 (CBlockEntry (read bentry4) w 
                                    (exec bentry4) (present bentry4)
                                    (accessible bentry4) 
                                    (blockindex bentry4) 
                                    (blockrange bentry4)))
                              (add newBlockEntryAddr
                                 (BE
                                    (CBlockEntry r (write bentry3) 
                                       (exec bentry3) (present bentry3)
                                       (accessible bentry3) 
                                       (blockindex bentry3) 
                                       (blockrange bentry3)))
                                 (add newBlockEntryAddr
                                    (BE
                                       (CBlockEntry (read bentry2) 
                                          (write bentry2) 
                                          (exec bentry2) true 
                                          (accessible bentry2) 
                                          (blockindex bentry2) 
                                          (blockrange bentry2)))
                                    (add newBlockEntryAddr
                                       (BE
                                          (CBlockEntry (read bentry1) 
                                             (write bentry1) 
                                             (exec bentry1) 
                                             (present bentry1) true
                                             (blockindex bentry1)
                                             (blockrange bentry1)))
                                       (add newBlockEntryAddr
                                          (BE
                                             (CBlockEntry 
                                                (read bentry0) 
                                                (write bentry0) 
                                                (exec bentry0) 
                                                (present bentry0)
                                                (accessible bentry0)
                                                (blockindex bentry0)
                                                (CBlock
                                                   (startAddr (blockrange bentry0))
                                                   blockend)))
                                          (add newBlockEntryAddr
                                             (BE
                                                (CBlockEntry 
                                                   (read bentry) 
                                                   (write bentry) 
                                                   (exec bentry) 
                                                   (present bentry)
                                                   (accessible bentry)
                                                   (blockindex bentry)
                                                   (CBlock blockstart
                                                      (endAddr (blockrange bentry)))))
                                             (add globalIdPDChild
                                                (PDT
                                                   {|
                                                   structure := structure pdentry0;
                                                   firstfreeslot := firstfreeslot
                                                        pdentry0;
                                                   nbfreeslots := predCurrentNbFreeSlots;
                                                   nbprepare := nbprepare pdentry0;
                                                   parent := parent pdentry0;
                                                   MPU := MPU pdentry0 |})
                                                (add globalIdPDChild
                                                   (PDT
                                                      {|
                                                      structure := structure pdentry;
                                                      firstfreeslot := newFirstFreeSlotAddr;
                                                      nbfreeslots := ADT.nbfreeslots
                                                        pdentry;
                                                      nbprepare := nbprepare pdentry;
                                                      parent := parent pdentry;
                                                      MPU := MPU pdentry |})
                                                   (memory originals0) beqAddr) beqAddr)
                                             beqAddr) beqAddr) beqAddr) beqAddr)
                                 beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
(*/\ sh1eaddr = Sh1EAddr*)
(* /\ exists olds1, lookup sh1eaddr (memory olds1) beqAddr = Some (SHE sh1entry1) /\
			isBE blockToShareChildEntryAddr olds1
			/\ exists oldolds1, lookup sh1eaddr (memory oldolds1) beqAddr = Some (SHE sh1entry) /\
			isBE blockToShareChildEntryAddr oldolds1 /\*)
     (*/\  lookup sh1eaddr (memory olds1) beqAddr = Some (SHE sh1entry1) /\
			isBE blockToShareChildEntryAddr olds1
			/\ lookup sh1eaddr (memory oldolds1) beqAddr = Some (SHE sh1entry) /\
			isBE blockToShareChildEntryAddr oldolds1 *)
) /\
      isBE blockToShareChildEntryAddr s)
     (*(exists sh1entry : Sh1Entry,
        lookup Sh1EAddr (memory s) beqAddr = Some (SHE sh1entry) /\
        sh1entryAddr blockToShareInCurrPartAddr Sh1EAddr s)*)
). intros. simpl. intuition. destruct H5. exists x.
	destruct H5. destruct H5. exists x0. exists x1. destruct H5. destruct H5. destruct H5.
	destruct H5. destruct H5. destruct H5. destruct H5.
	 exists x2. exists x3. exists x4. exists x5. exists x6.
	 exists x7. exists x8. destruct H5. destruct H5. exists x9. exists x10.
	destruct H5. destruct H5. destruct H5. exists x11. exists x12. exists x13.
	destruct H5.
	exists Sh1EAddr. destruct H5. destruct H5. exists x15. exists previoussh1entry.

	exists x14.
	intuition. rewrite H5. cbn. simpl.
	f_equal. f_equal. cbn. f_equal.
	apply isBELookupEq in H8. apply isBELookupEq.
	destruct H8 as[oldbentry]. exists oldbentry.
	cbn.
	destruct (beqAddr Sh1EAddr blockToShareChildEntryAddr) eqn:Hbeq.
	- rewrite <- beqAddrTrue in *. subst.
		contradict H6. unfold not. congruence.
	- rewrite removeDupIdentity. assumption.
		unfold not. intros. subst. congruence.
}
}
	intros.
	{ (** ret **)
		eapply weaken. apply WP.ret.
		intros. simpl. intuition.
		- (** partitionIsolation **)

}
				unfold MAL.writeSh1PDChildFromBlockEntryAddr2.
				eapply bindRev.
		{ (** get **)
			eapply weaken. apply WP.get.
			intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
((*partitionsIsolation s /\
      verticalSharing s /\
      consistency s /\*)
      isBE blockToShareChildEntryAddr s /\
      (exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 bentry4
                                                    bentry5 : BlockEntry) 
       (sceaddr : paddr) (scentry : SCEntry) (newBlockEntryAddr
                                              newFirstFreeSlotAddr : paddr) 
       (predCurrentNbFreeSlots : index),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add sceaddr (SCE {| origin := blockstart; next := next scentry |})
                     (add newBlockEntryAddr
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
                                    (accessible bentry3) 
                                    (blockindex bentry3) 
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
                                          (write bentry1) 
                                          (exec bentry1) 
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
                                                blockend)))
                                       (add newBlockEntryAddr
                                          (BE
                                             (CBlockEntry 
                                                (read bentry) 
                                                (write bentry) 
                                                (exec bentry) 
                                                (present bentry) 
                                                (accessible bentry)
                                                (blockindex bentry)
                                                (CBlock blockstart
                                                   (endAddr (blockrange bentry)))))
                                          (add globalIdPDChild
                                             (PDT
                                                {|
                                                structure := structure pdentry0;
                                                firstfreeslot := firstfreeslot
                                                        pdentry0;
                                                nbfreeslots := predCurrentNbFreeSlots;
                                                nbprepare := nbprepare pdentry0;
                                                parent := parent pdentry0;
                                                MPU := MPU pdentry0 |})
                                             (add globalIdPDChild
                                                (PDT
                                                   {|
                                                   structure := structure pdentry;
                                                   firstfreeslot := newFirstFreeSlotAddr;
                                                   nbfreeslots := ADT.nbfreeslots
                                                        pdentry;
                                                   nbprepare := nbprepare pdentry;
                                                   parent := parent pdentry;
                                                   MPU := MPU pdentry |}) 
                                                (memory s0) beqAddr) beqAddr) beqAddr)
                                       beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                        beqAddr) beqAddr |})) /\
     (exists sh1entry : Sh1Entry,
        lookup Sh1EAddr (memory s) beqAddr = Some (SHE sh1entry) /\
        sh1entryAddr blockToShareInCurrPartAddr Sh1EAddr s)
). intuition.
	}
intro s0. intuition.
		destruct (lookup Sh1EAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
	2: {
		
instantiate (1:= fun _ s =>
(*partitionsIsolation s /\
exists pdentry : PDTable, exists pdinsertion : paddr,
 exists bentry : BlockEntry, exists newBlockEntryAddr : paddr,
exists scentry : SCEntry, exists sceaddr : paddr,
exists sh1entry : Sh1Entry, exists sh1addr : paddr,
exists predCurrentNbFreeSlots : index, exists newFirstFreeSlotAddr : paddr,
exists startaddr endaddr origin : paddr,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s /\
lookup sceaddr (memory s) beqAddr = Some (SCE scentry) /\
isSCE sceaddr s /\
scentryAddr newBlockEntryAddr sceaddr s) /\
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
				(add sh1addr
                 (SHE
                    {|
                    PDchild := globalIdPDChild;
                    PDflag := PDflag sh1entry;
                    inChildLocation := inChildLocation sh1entry |}) 
 (memory s) beqAddr) beqAddr) beqAddr) beqAddr |} *)
(*add SCEAddr (SCE {| origin := origin; next := next scentry |}) 
                 (memory s) beqAddr |})*)
(exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 bentry4
                                                    bentry5 : BlockEntry) 
       (sceaddr : paddr) (scentry : SCEntry) (newBlockEntryAddr
                                              newFirstFreeSlotAddr : paddr) 
       (predCurrentNbFreeSlots : index) (sh1eaddr : paddr) (sh1entry : Sh1Entry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add sh1eaddr
                 (SHE
                    {|
                    PDchild := globalIdPDChild;
                    PDflag := PDflag sh1entry;
                    inChildLocation := inChildLocation sh1entry |})
									(add sceaddr (SCE {| origin := blockstart; next := next scentry |})
                     (add newBlockEntryAddr
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
                                    (accessible bentry3) 
                                    (blockindex bentry3) 
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
                                          (write bentry1) 
                                          (exec bentry1) 
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
                                                blockend)))
                                       (add newBlockEntryAddr
                                          (BE
                                             (CBlockEntry 
                                                (read bentry) 
                                                (write bentry) 
                                                (exec bentry) 
                                                (present bentry) 
                                                (accessible bentry)
                                                (blockindex bentry)
                                                (CBlock blockstart
                                                   (endAddr (blockrange bentry)))))
                                          (add globalIdPDChild
                                             (PDT
                                                {|
                                                structure := structure pdentry0;
                                                firstfreeslot := firstfreeslot
                                                        pdentry0;
                                                nbfreeslots := predCurrentNbFreeSlots;
                                                nbprepare := nbprepare pdentry0;
                                                parent := parent pdentry0;
                                                MPU := MPU pdentry0 |})
                                             (add globalIdPDChild
                                                (PDT
                                                   {|
                                                   structure := structure pdentry;
                                                   firstfreeslot := newFirstFreeSlotAddr;
                                                   nbfreeslots := ADT.nbfreeslots
                                                        pdentry;
                                                   nbprepare := nbprepare pdentry;
                                                   parent := parent pdentry;
                                                   MPU := MPU pdentry |}) 
                                                (memory s0) beqAddr) beqAddr) beqAddr)
                                       beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                        beqAddr) beqAddr) beqAddr |})
/\ isBE blockToShareChildEntryAddr s


). eapply weaken. apply WP.modify.
		intros. simpl. set (s' := {|
      currentPartition :=  _|}). 
intros. simpl.
	split.
	- intuition.
		destruct H9. destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
		 destruct H5. destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
		 destruct H5. destruct H5. destruct H5.
		exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5.
		exists x6. exists x7. exists x8. exists x9. exists x10. exists x11.
		exists x12. exists x13. destruct H8. exists Sh1EAddr. exists s.
		subst. intuition.
	- unfold isBE. admit.
}
	eapply weaken. apply WP.undefined. intros.
			simpl. intuition. destruct H8. intuition. congruence.
	eapply weaken. apply WP.undefined. intros.
			simpl. intuition. destruct H8. intuition. congruence.
	eapply weaken. apply WP.undefined. intros.
			simpl. intuition. destruct H8. intuition. congruence.
	eapply weaken. apply WP.undefined. intros.
			simpl. intuition. destruct H8. intuition. congruence.
	eapply weaken. apply WP.undefined. intros.
			simpl. intuition. destruct H8. intuition. congruence.
}
}
	intros.

eapply bindRev.
	{ (** MAL.writeSh1InChildLocationFromBlockEntryAddr **)
		unfold MAL.writeSh1InChildLocationFromBlockEntryAddr.
		eapply bindRev. 
		{ (** MAL.getSh1EntryAddrFromBlockEntryAddr **) 
			eapply weaken. apply getSh1EntryAddrFromBlockEntryAddr.
			intros. split. apply H5.
			assert(consistency s). admit.
			unfold consistency in *. intuition.
			apply isBELookupEq. admit.
		}
		intro Sh1EAddr.
		{ (** MAL.writeSh1InChildLocationFromBlockEntryAddr2 **)
			eapply weaken. apply writeSh1InChildLocationFromBlockEntryAddr2.
			intros. simpl. intuition. destruct H7. exists x. intuition.
			instantiate (1:= fun _ s =>
(*partitionsIsolation s /\
exists pdentry : PDTable, exists pdinsertion : paddr,
 exists bentry : BlockEntry, exists newBlockEntryAddr : paddr,
exists scentry : SCEntry, exists sceaddr : paddr,
exists sh1entry : Sh1Entry, exists sh1addr : paddr,
exists predCurrentNbFreeSlots : index, exists newFirstFreeSlotAddr : paddr,
exists startaddr endaddr origin : paddr,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s /\
lookup sceaddr (memory s) beqAddr = Some (SCE scentry) /\
isSCE sceaddr s /\
scentryAddr newBlockEntryAddr sceaddr s) /\
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
				(add sh1addr
                 (SHE
                    {|
                    PDchild := globalIdPDChild;
                    PDflag := PDflag sh1entry;
                    inChildLocation := blockToShareChildEntryAddr |}) 
 (memory s) beqAddr) beqAddr) beqAddr) beqAddr |} 
(*add SCEAddr (SCE {| origin := origin; next := next scentry |}) 
                 (memory s) beqAddr |})*)*)
((exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 bentry4
                                                    bentry5 : BlockEntry) 
       (sceaddr : paddr) (scentry : SCEntry) (newBlockEntryAddr
                                              newFirstFreeSlotAddr : paddr) 
       (predCurrentNbFreeSlots : index) (sh1eaddr : paddr)
       (sh1entry sh1entry1: Sh1Entry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add Sh1EAddr
                 (SHE
                    {|
                    PDchild := PDchild x;
                    PDflag := PDflag x;
                    inChildLocation := blockToShareChildEntryAddr |}) 
									(add Sh1EAddr
                     (SHE
                        {|
                        PDchild := globalIdPDChild;
                        PDflag := PDflag sh1entry;
                        inChildLocation := inChildLocation sh1entry |})
                     (add sceaddr
                        (SCE {| origin := blockstart; next := next scentry |})
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry5) 
                                 (write bentry5) e (present bentry5)
                                 (accessible bentry5) (blockindex bentry5)
                                 (blockrange bentry5)))
                           (add newBlockEntryAddr
                              (BE
                                 (CBlockEntry (read bentry4) w 
                                    (exec bentry4) (present bentry4)
                                    (accessible bentry4) 
                                    (blockindex bentry4) 
                                    (blockrange bentry4)))
                              (add newBlockEntryAddr
                                 (BE
                                    (CBlockEntry r (write bentry3) 
                                       (exec bentry3) (present bentry3)
                                       (accessible bentry3) 
                                       (blockindex bentry3) 
                                       (blockrange bentry3)))
                                 (add newBlockEntryAddr
                                    (BE
                                       (CBlockEntry (read bentry2) 
                                          (write bentry2) 
                                          (exec bentry2) true 
                                          (accessible bentry2) 
                                          (blockindex bentry2) 
                                          (blockrange bentry2)))
                                    (add newBlockEntryAddr
                                       (BE
                                          (CBlockEntry (read bentry1) 
                                             (write bentry1) 
                                             (exec bentry1) 
                                             (present bentry1) true
                                             (blockindex bentry1)
                                             (blockrange bentry1)))
                                       (add newBlockEntryAddr
                                          (BE
                                             (CBlockEntry 
                                                (read bentry0) 
                                                (write bentry0) 
                                                (exec bentry0) 
                                                (present bentry0)
                                                (accessible bentry0)
                                                (blockindex bentry0)
                                                (CBlock
                                                   (startAddr (blockrange bentry0))
                                                   blockend)))
                                          (add newBlockEntryAddr
                                             (BE
                                                (CBlockEntry 
                                                   (read bentry) 
                                                   (write bentry) 
                                                   (exec bentry) 
                                                   (present bentry)
                                                   (accessible bentry)
                                                   (blockindex bentry)
                                                   (CBlock blockstart
                                                      (endAddr (blockrange bentry)))))
                                             (add globalIdPDChild
                                                (PDT
                                                   {|
                                                   structure := structure pdentry0;
                                                   firstfreeslot := firstfreeslot
                                                        pdentry0;
                                                   nbfreeslots := predCurrentNbFreeSlots;
                                                   nbprepare := nbprepare pdentry0;
                                                   parent := parent pdentry0;
                                                   MPU := MPU pdentry0 |})
                                                (add globalIdPDChild
                                                   (PDT
                                                      {|
                                                      structure := structure pdentry;
                                                      firstfreeslot := newFirstFreeSlotAddr;
                                                      nbfreeslots := ADT.nbfreeslots
                                                        pdentry;
                                                      nbprepare := nbprepare pdentry;
                                                      parent := parent pdentry;
                                                      MPU := MPU pdentry |})
                                                   (memory s0) beqAddr) beqAddr)
                                             beqAddr) beqAddr) beqAddr) beqAddr)
                                 beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
(*/\ 
        lookup Sh1EAddr (memory s) beqAddr = Some (SHE x)*)
) /\
      isBE blockToShareChildEntryAddr s)
     (*(exists sh1entry : Sh1Entry,
        lookup Sh1EAddr (memory s) beqAddr = Some (SHE sh1entry) /\
        sh1entryAddr blockToShareInCurrPartAddr Sh1EAddr s)*)
). intros. simpl. intuition.
	destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
	destruct H5. destruct H5. destruct H5. destruct H5.
	destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
	destruct H5. destruct H5. destruct H5.

	exists x0. exists x1. exists x2. exists x3. exists x4. exists x5. exists x6.
	 exists x7. exists x8. exists x9. exists x10. exists x11. exists x12. exists x13.
 exists x14. exists Sh1EAddr. exists x. exists x.
	intuition. f_equal. rewrite H5. cbn. reflexivity. f_equal.
	rewrite H5. f_equal. cbn. f_equal. intuition.


unfold MAL.writeSh1InChildLocationFromBlockEntryAddr2.
				eapply bindRev.
				{ (** get **)
					eapply weaken. apply WP.get.
					intro s. intros. simpl. instantiate (1:= fun s s0 => s = s0 /\ 
(*(partitionsIsolation s /\
      (exists
         (pdentry : PDTable) (pdinsertion : paddr) (bentry : BlockEntry) 
       (newBlockEntryAddr : paddr) (scentry : SCEntry) (sceaddr : paddr) 
       (sh1entry : Sh1Entry) (sh1addr : paddr) (predCurrentNbFreeSlots : index) 
       (newFirstFreeSlotAddr startaddr endaddr origin : paddr),
         (lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\
          isPDT pdinsertion s /\
          lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\
          isBE newBlockEntryAddr s /\
          lookup sceaddr (memory s) beqAddr = Some (SCE scentry) /\
          isSCE sceaddr s /\ scentryAddr newBlockEntryAddr sceaddr s) /\
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
                        MPU := MPU pdentry |})
                     (add newBlockEntryAddr
                        (BE
                           (CBlockEntry r w e true true (blockindex bentry)
                              (CBlock startaddr endaddr)))
                        (add sceaddr
                           (SCE {| origin := origin; next := next scentry |})
                           (add sh1addr
                              (SHE
                                 {|
                                 PDchild := globalIdPDChild;
                                 PDflag := PDflag sh1entry;
                                 inChildLocation := inChildLocation sh1entry |})
                              (memory s) beqAddr) beqAddr) beqAddr) beqAddr |})) /\
     (exists sh1entry : Sh1Entry,
        lookup Sh1EAddr (memory s) beqAddr = Some (SHE sh1entry) /\
        sh1entryAddr blockToShareInCurrPartAddr Sh1EAddr s)*)
((*partitionsIsolation s /\
      (exists
         (pdentry : PDTable) (pdinsertion : paddr) (bentry : BlockEntry) 
       (newBlockEntryAddr : paddr) (scentry : SCEntry) (sceaddr : paddr) 
       (_ : Sh1Entry) (_ : paddr) (_ : index) (_ _ _ _ : paddr),
         (lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\
          isPDT pdinsertion s /\
          lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\
          isBE newBlockEntryAddr s /\
          lookup sceaddr (memory s) beqAddr = Some (SCE scentry) /\
          isSCE sceaddr s /\ scentryAddr newBlockEntryAddr sceaddr s) /\*)
         (exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 bentry4
                                                    bentry5 : BlockEntry) 
       (sceaddr : paddr) (scentry : SCEntry) (newBlockEntryAddr
                                              newFirstFreeSlotAddr : paddr) 
       (predCurrentNbFreeSlots : index) (sh1eaddr : paddr) 
       (sh1entry : Sh1Entry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add sh1eaddr
                     (SHE
                        {|
                        PDchild := globalIdPDChild;
                        PDflag := PDflag sh1entry;
                        inChildLocation := inChildLocation sh1entry |})
                     (add sceaddr
                        (SCE {| origin := blockstart; next := next scentry |})
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry5) 
                                 (write bentry5) e (present bentry5)
                                 (accessible bentry5) (blockindex bentry5)
                                 (blockrange bentry5)))
                           (add newBlockEntryAddr
                              (BE
                                 (CBlockEntry (read bentry4) w 
                                    (exec bentry4) (present bentry4)
                                    (accessible bentry4) 
                                    (blockindex bentry4) 
                                    (blockrange bentry4)))
                              (add newBlockEntryAddr
                                 (BE
                                    (CBlockEntry r (write bentry3) 
                                       (exec bentry3) (present bentry3)
                                       (accessible bentry3) 
                                       (blockindex bentry3) 
                                       (blockrange bentry3)))
                                 (add newBlockEntryAddr
                                    (BE
                                       (CBlockEntry (read bentry2) 
                                          (write bentry2) 
                                          (exec bentry2) true 
                                          (accessible bentry2) 
                                          (blockindex bentry2) 
                                          (blockrange bentry2)))
                                    (add newBlockEntryAddr
                                       (BE
                                          (CBlockEntry (read bentry1) 
                                             (write bentry1) 
                                             (exec bentry1) 
                                             (present bentry1) true
                                             (blockindex bentry1)
                                             (blockrange bentry1)))
                                       (add newBlockEntryAddr
                                          (BE
                                             (CBlockEntry 
                                                (read bentry0) 
                                                (write bentry0) 
                                                (exec bentry0) 
                                                (present bentry0)
                                                (accessible bentry0)
                                                (blockindex bentry0)
                                                (CBlock
                                                   (startAddr (blockrange bentry0))
                                                   blockend)))
                                          (add newBlockEntryAddr
                                             (BE
                                                (CBlockEntry 
                                                   (read bentry) 
                                                   (write bentry) 
                                                   (exec bentry) 
                                                   (present bentry)
                                                   (accessible bentry)
                                                   (blockindex bentry)
                                                   (CBlock blockstart
                                                      (endAddr (blockrange bentry)))))
                                             (add globalIdPDChild
                                                (PDT
                                                   {|
                                                   structure := structure pdentry0;
                                                   firstfreeslot := firstfreeslot
                                                        pdentry0;
                                                   nbfreeslots := predCurrentNbFreeSlots;
                                                   nbprepare := nbprepare pdentry0;
                                                   parent := parent pdentry0;
                                                   MPU := MPU pdentry0 |})
                                                (add globalIdPDChild
                                                   (PDT
                                                      {|
                                                      structure := structure pdentry;
                                                      firstfreeslot := newFirstFreeSlotAddr;
                                                      nbfreeslots := ADT.nbfreeslots
                                                        pdentry;
                                                      nbprepare := nbprepare pdentry;
                                                      parent := parent pdentry;
                                                      MPU := MPU pdentry |})
                                                   (memory s0) beqAddr) beqAddr)
                                             beqAddr) beqAddr) beqAddr) beqAddr)
                                 beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}) /\
      isBE blockToShareChildEntryAddr s) /\
     (exists sh1entry : Sh1Entry,
        lookup Sh1EAddr (memory s) beqAddr = Some (SHE sh1entry) /\
        sh1entryAddr blockToShareInCurrPartAddr Sh1EAddr s)
). intuition.
}
	intro s0. intuition.
		destruct (lookup Sh1EAddr (memory s0) beqAddr) eqn:Hlookup.
		destruct v eqn:Hv.
	2: {
instantiate (1:= fun _ s =>
(*partitionsIsolation s /\
exists pdentry : PDTable, exists pdinsertion : paddr,
 exists bentry : BlockEntry, exists newBlockEntryAddr : paddr,
exists scentry : SCEntry, exists sceaddr : paddr,
exists sh1entry : Sh1Entry, exists sh1addr : paddr,
exists predCurrentNbFreeSlots : index, exists newFirstFreeSlotAddr : paddr,
exists startaddr endaddr origin : paddr,
(lookup pdinsertion (memory s) beqAddr = Some (PDT pdentry) /\ 
isPDT pdinsertion s /\
lookup newBlockEntryAddr (memory s) beqAddr = Some (BE bentry) /\ 
isBE newBlockEntryAddr s /\
lookup sceaddr (memory s) beqAddr = Some (SCE scentry) /\
isSCE sceaddr s /\
scentryAddr newBlockEntryAddr sceaddr s) /\
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
				(add sh1addr
                 (SHE
                    {|
                    PDchild := globalIdPDChild;
                    PDflag := PDflag sh1entry;
                    inChildLocation := blockToShareChildEntryAddr |}) 
 (memory s) beqAddr) beqAddr) beqAddr) beqAddr |} 
(*add SCEAddr (SCE {| origin := origin; next := next scentry |}) 
                 (memory s) beqAddr |})*)*)
((exists
         (s0 : state) (pdentry pdentry0 : PDTable) (bentry bentry0 bentry1 bentry2
                                                    bentry3 bentry4
                                                    bentry5 : BlockEntry) 
       (sceaddr : paddr) (scentry : SCEntry) (newBlockEntryAddr
                                              newFirstFreeSlotAddr : paddr) 
       (predCurrentNbFreeSlots : index) (sh1eaddr : paddr)
       (sh1entry sh1entry1: Sh1Entry),
         s =
         {|
         currentPartition := currentPartition s0;
         memory := add sh1eaddr
                 (SHE
                    {|
                    PDchild := PDchild sh1entry1;
                    PDflag := PDflag sh1entry1;
                    inChildLocation := blockToShareChildEntryAddr |}) 
									(add sh1eaddr
                     (SHE
                        {|
                        PDchild := globalIdPDChild;
                        PDflag := PDflag sh1entry;
                        inChildLocation := inChildLocation sh1entry |})
                     (add sceaddr
                        (SCE {| origin := blockstart; next := next scentry |})
                        (add newBlockEntryAddr
                           (BE
                              (CBlockEntry (read bentry5) 
                                 (write bentry5) e (present bentry5)
                                 (accessible bentry5) (blockindex bentry5)
                                 (blockrange bentry5)))
                           (add newBlockEntryAddr
                              (BE
                                 (CBlockEntry (read bentry4) w 
                                    (exec bentry4) (present bentry4)
                                    (accessible bentry4) 
                                    (blockindex bentry4) 
                                    (blockrange bentry4)))
                              (add newBlockEntryAddr
                                 (BE
                                    (CBlockEntry r (write bentry3) 
                                       (exec bentry3) (present bentry3)
                                       (accessible bentry3) 
                                       (blockindex bentry3) 
                                       (blockrange bentry3)))
                                 (add newBlockEntryAddr
                                    (BE
                                       (CBlockEntry (read bentry2) 
                                          (write bentry2) 
                                          (exec bentry2) true 
                                          (accessible bentry2) 
                                          (blockindex bentry2) 
                                          (blockrange bentry2)))
                                    (add newBlockEntryAddr
                                       (BE
                                          (CBlockEntry (read bentry1) 
                                             (write bentry1) 
                                             (exec bentry1) 
                                             (present bentry1) true
                                             (blockindex bentry1)
                                             (blockrange bentry1)))
                                       (add newBlockEntryAddr
                                          (BE
                                             (CBlockEntry 
                                                (read bentry0) 
                                                (write bentry0) 
                                                (exec bentry0) 
                                                (present bentry0)
                                                (accessible bentry0)
                                                (blockindex bentry0)
                                                (CBlock
                                                   (startAddr (blockrange bentry0))
                                                   blockend)))
                                          (add newBlockEntryAddr
                                             (BE
                                                (CBlockEntry 
                                                   (read bentry) 
                                                   (write bentry) 
                                                   (exec bentry) 
                                                   (present bentry)
                                                   (accessible bentry)
                                                   (blockindex bentry)
                                                   (CBlock blockstart
                                                      (endAddr (blockrange bentry)))))
                                             (add globalIdPDChild
                                                (PDT
                                                   {|
                                                   structure := structure pdentry0;
                                                   firstfreeslot := firstfreeslot
                                                        pdentry0;
                                                   nbfreeslots := predCurrentNbFreeSlots;
                                                   nbprepare := nbprepare pdentry0;
                                                   parent := parent pdentry0;
                                                   MPU := MPU pdentry0 |})
                                                (add globalIdPDChild
                                                   (PDT
                                                      {|
                                                      structure := structure pdentry;
                                                      firstfreeslot := newFirstFreeSlotAddr;
                                                      nbfreeslots := ADT.nbfreeslots
                                                        pdentry;
                                                      nbprepare := nbprepare pdentry;
                                                      parent := parent pdentry;
                                                      MPU := MPU pdentry |})
                                                   (memory s0) beqAddr) beqAddr)
                                             beqAddr) beqAddr) beqAddr) beqAddr)
                                 beqAddr) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr |}
/\ 
        lookup sh1eaddr (memory s) beqAddr = Some (SHE sh1entry1)
) /\
      isBE blockToShareChildEntryAddr s)
     (*(exists sh1entry : Sh1Entry,
        lookup Sh1EAddr (memory s) beqAddr = Some (SHE sh1entry) /\
        sh1entryAddr blockToShareInCurrPartAddr Sh1EAddr s)*)
). eapply weaken. apply WP.modify.
		intros. simpl. set (s' := {|
      currentPartition :=  _|}). 
intros. simpl.
intuition.
		destruct H7. destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
		 destruct H5. destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
		 destruct H5. destruct H5. destruct H5. destruct H5. destruct H5.
		exists x. exists x0. exists x1. exists x2. exists x3. exists x4. exists x5.
		exists x6. exists x7. exists x8. exists x9. exists x10. exists x11.
		exists x12. exists x13. exists Sh1EAddr. exists x15. destruct H8. exists s. 
		subst. intuition. unfold s'. cbn. f_equal. f_equal. f_equal. 
(* y a un truc faux dans le instantiate juste avant*)
intuition.
	- unfold isBE. admit.


simpl. cbn. admit. } admit. admit. admit. admit. admit. }
	intros.

 
	{ (** ret **)
	eapply weaken. apply WP.ret. intros. simpl. intuition.
	admit. admit. admit. 

----------------------------------------------------------
2: { intros.
		eapply bindRev.
		2: { intros. eapply weaken. eapply WP.ret.
		intros. simpl. exact H3.
			}
	intros. eapply weaken. eapply writeSh1InChildLocationFromBlockEntryAddr.
	intros. simpl. exact H3.
	}
	eapply weaken. apply writeSh1PDChildFromBlockEntryAddr.
	intros. simpl.
	unfold consistency in *. intuition.
	unfold wellFormedFstShadowIfBlockEntry in *.
	specialize (H6 blockToShareInCurrPartAddr H7).
	apply isSHELookupEq in H6.
	destruct H6. exists x.
	split. assumption.
	intuition. simpl. set (blockToShareAddrInSh1 := (CPaddr (blockToShareInCurrPartAddr + sh1offset))).
	eexists. assert(beqAddr blockToShareAddrInSh1 blockToShareAddrInSh1 = true).
 	destruct blockToShareAddrInSh1. simpl.
	unfold beqAddr. apply PeanoNat.Nat.eqb_refl.
	rewrite H14. split.
	f_equal. intuition.
- (*partitionsIsolation*)
	unfold partitionsIsolation. intros. simpl.
	unfold getUsedBlocks. unfold getConfigBlocks.
	unfold getMappedBlocks. set (s' := {|
       currentPartition := currentPartition s;
       memory := _ |}) in *.
	admit.
- (* kernelDataIsolation*)
	admit.
- unfold verticalSharing. intros. simpl.
	unfold getUsedBlocks. unfold getConfigBlocks.
	unfold getMappedBlocks.
	set (s' := {|
       currentPartition := currentPartition s;
       memory := _ |}) in *.
	destruct (monadToValue (readPDStructurePointer child) s') eqn:Hstucturepointer.




 now exists a.  }
  rewrite assoc.
  eapply bindRev.
  (** getFstShadow **)
  eapply WP.weaken. 
  eapply Invariants.getFstShadow. cbn.
  intros s H.
  split.
  pattern s in H.
  eexact H.
  unfold consistency in *.
  unfold partitionDescriptorEntry in *.
  intuition.
  simpl.
  intros currentShadow1.
  rewrite assoc.
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
  intro idxDescChild. simpl.
  rewrite assoc.
  (** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eexact H. subst.
  split. 
  intuition.
  split. 
  instantiate (1:= currentPart).
  intuition. 
  subst.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *. 
  intuition.
  instantiate (1:= sh1idx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
  assert(Hcp : currentPart = currentPartition s) by intuition.
  assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
  exists currentShadow1.
  split. intuition.
  
  unfold consistency in *.
  destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
  unfold partitionDescriptorEntry in Hpd.
  assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
  \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
  by auto.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
  generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
  destruct Hpd as (Hidxpd & _& Hentry). 
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  split.
  unfold nextEntryIsPP in *.
  destruct (StateLib.Index.succ sh1idx); try now contradict H0.
  destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex);
  try now contradict H0.
  destruct v ; try now contradict H0.
  subst; assumption.
  subst. left. split;intuition.
  intro ptDescChild. simpl.
  (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptDescChild sh1idx currentPart descChild s /\ ptDescChild = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr descChild fstLevel = idx ->
  isVE ptDescChild idx s /\ getTableAddrRoot ptDescChild sh1idx currentPart descChild s  )).
  { destruct H1 as [H1 |(Hi & Hi1 & H1)].
    + left. trivial. 
    + right. intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
      - split; assumption.
      - contradict Hfalse. 
        symmetrynot. 
        apply idxSh2idxSh1notEq.
      - contradict Hfalse. 
        symmetrynot. apply idxPDidxSh1notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. }
  rewrite assoc.
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptDescChildIsnull. simpl.
  case_eq ptDescChildIsnull.
  { intros.
    eapply WP.weaken.
    eapply WP.ret .
    simpl. intros.
    intuition. }
  intros HptDescChildIsnull. 
  subst.
  (* readPDflag *)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readPDflag.
  simpl;intros.
  split.
  destruct H as (((Ha1 & Ha2) & Ha3) & Ha4).
  assert (Hnewget : isVE ptDescChild (StateLib.getIndexOfAddr descChild fstLevel) s /\
       getTableAddrRoot ptDescChild sh1idx currentPart descChild s /\ 
       (Nat.eqb defaultPage ptDescChild) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr descChild fstLevel);trivial.
      intuition. }
  assert (HP := conj (conj Ha1 Ha2) Hnewget).
  pattern s in HP.
  eexact HP.
  destruct H as (H & Htrue).
  destruct H as (H & Hor).
  destruct Hor as [(Hor & Hfalse) | Hor].
  subst.
  apply beq_nat_false in Htrue.
  now contradict Htrue.
  destruct H as (H & Hidx).
  subst.
  destruct Hor with (StateLib.getIndexOfAddr descChild fstLevel);
  trivial.
  intros ischild;simpl in *.
  intros.
  case_eq ischild; intros Hischild;[|intros;eapply weaken;[ eapply WP.ret;trivial|
  intros;simpl;intuition]].
  subst.
(** end checkChild *)
(** getFstShadow **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getFstShadow. cbn.
intros s H.
split.
pattern s in H.
eexact H.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
intros currentShadow.
(** getTableAddr **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
assert(Hsh1eq : currentShadow = currentShadow1).
apply getSh1NextEntryIsPPEq with currentPart s;trivial.
intuition.
apply nextEntryIsPPgetFstShadow;intuition.
subst currentShadow1.
destruct H as (H & _).
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= sh1idx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow s) by intuition.
exists currentShadow.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
\/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *.
destruct (StateLib.Index.succ sh1idx); try now contradict H0.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex);
try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaInCurPart. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaInCurPart sh1idx currentPart vaInCurrentPartition s /\ ptVaInCurPart = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isVE ptVaInCurPart idx s /\ getTableAddrRoot ptVaInCurPart sh1idx currentPart vaInCurrentPartition s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
    - split; assumption.
    - contradict Hfalse. 
      symmetrynot. 
      apply idxSh2idxSh1notEq.
    - contradict Hfalse. 
      symmetrynot. apply idxPDidxSh1notEq.  }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro childListSh1Isnull. simpl.
case_eq childListSh1Isnull.
{ intros. eapply WP.weaken.  eapply WP.ret . simpl. intros.
 pattern false, s in H0.
 eapply H0. }
intros HptVaInCurPartNotNull. clear HptVaInCurPartNotNull.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
    destruct H as ((Ha1  & Ha3) & Ha4).
  assert (Hnewget : isVE ptVaInCurPart (
  StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) s /\
       getTableAddrRoot ptVaInCurPart sh1idx currentPart vaInCurrentPartition s /\ 
       (Nat.eqb defaultPage ptVaInCurPart) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP.  }
intro idxvaInCurPart.
simpl. 
(** checkDerivation **)
unfold Internal.checkDerivation.
rewrite assoc.
(** readVirEntry **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.readVirEntry. 
{ simpl. intros.
  split.
  pattern s in H.
  eexact H.
  intuition. subst;trivial. }
intros vainve.
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.compareVAddrToNull.
intro isnotderiv. simpl.
(** getPd **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getPd.
cbn.
intros s H.
split.
pattern s in H.
eexact H.
split.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
intros currentPD.
(** getTableAddr **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
exists currentPD.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *.
destruct (StateLib.Index.succ PDidx); try now contradict H0.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex);
try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaInCurPartpd. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaInCurPartpd PDidx currentPart vaInCurrentPartition s /\ ptVaInCurPartpd = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\ getTableAddrRoot ptVaInCurPartpd PDidx currentPart vaInCurrentPartition s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptVaInCurPartpdIsnull. simpl.
case_eq ptVaInCurPartpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptVaInCurPartpdNotNull. subst.
(** readAccessible **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readAccessible. simpl.
  intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptVaInCurPartpd (
  StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) s /\
       getTableAddrRoot ptVaInCurPartpd PDidx currentPart
         vaInCurrentPartition s /\ 
       (Nat.eqb defaultPage ptVaInCurPartpd) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel);trivial.
      intuition. }
   subst.
 split.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. clear Ha3. 
  intuition. subst;trivial. }
intros accessiblesrc. simpl.
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros presentmap. simpl.
(** getTableAddr : to return the physical page of the descChild   **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
exists currentPD.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *.
destruct (StateLib.Index.succ PDidx); try now contradict H0.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex);
try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptDescChildpd. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptDescChildpd PDidx currentPart descChild s /\ ptDescChildpd = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptDescChildpd idx s /\ getTableAddrRoot ptDescChildpd PDidx currentPart descChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptDescChildpdIsnull. simpl.
case_eq ptDescChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptDescChildpdNotNull. subst.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptDescChildpd 
  (StateLib.getIndexOfAddr descChild fstLevel) s /\
       getTableAddrRoot ptDescChildpd PDidx currentPart descChild s /\ 
       (Nat.eqb defaultPage ptDescChildpd) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr descChild fstLevel);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. }
intro idxDescChild1.
simpl. 
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros presentDescPhy. simpl.
case_eq (negb presentDescPhy);intros Hlegit;subst.
eapply weaken. eapply WP.ret. 
simpl. intros;intuition.
(** readPhyEntry **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPhyEntry. simpl.
  intros.
  split.
  pattern s in H.
  eapply H. 
  subst.
  intuition;subst;trivial. }
intros phyDescChild. simpl.
(** getPd **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getPd.
cbn.
intros s H.
(** descChild is a child *)
assert(Hchildren : In phyDescChild (getChildren (currentPartition s) s)).
{ 
 apply inGetChildren with level currentPD ptDescChildpd ptDescChild currentShadow descChild;
  intuition;subst;trivial.
      apply negb_false_iff in Hlegit.
  subst;trivial.
   }
  

split. 
assert(Hnew := conj H Hchildren).  
pattern s in Hnew.
eexact Hnew.
split.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros pdChildphy.
simpl.
(** getTableAddr : to check if the virtual address is available to map a new page  **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
assert(Hchildpart : In phyDescChild (getPartitions multiplexer s)). 
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
split. 
instantiate (1:= phyDescChild );trivial.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by intuition.
exists pdChildphy.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
    generalize (Hpd  phyDescChild  Hchildpart); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx); [|now contradict H0];
destruct (lookup phyDescChild i (memory s) beqPage beqIndex) ; [|now contradict H0];
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaChildpd. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaChildpd PDidx phyDescChild vaChild s /\ ptVaChildpd = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr vaChild fstLevel = idx ->
isPE ptVaChildpd idx s /\ getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }

(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptVaChildpdIsnull. simpl.
case_eq ptVaChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptVaChildpdIsnull. subst.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptVaChildpd 
  (StateLib.getIndexOfAddr vaChild fstLevel) s /\
       getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s /\ 
       (Nat.eqb defaultPage ptVaChildpd) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaChild fstLevel);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. }
intro idxvaChild.
simpl. 
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros presentvaChild. simpl.
case_eq (isnotderiv && accessiblesrc && presentmap && negb presentvaChild);intros Hlegit1;subst;[|intros;eapply weaken;[ eapply WP.ret;trivial|
  intros;simpl;intuition]].
(** readPhyEntry **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPhyEntry. simpl.
  intros.
  split.
  pattern s in H.
  eapply H. 
  subst.
  intuition;subst;trivial. }
intros phyVaChild. simpl.
(** getSndShadow **)
eapply bindRev.
eapply weaken.
eapply Invariants.getSndShadow.
simpl;intros.
split. 

pattern s in H. 
exact H.
split. trivial.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros sh2Childphy.
simpl.
(** getTableAddr : to access to the second shadow page table  **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
assert(Hchildpart : In phyDescChild (getPartitions multiplexer s)). 
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
split. 
instantiate (1:= phyDescChild );trivial.
instantiate (1:= sh2idx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP phyDescChild sh2idx sh2Childphy s) by intuition.
exists sh2Childphy.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/  sh2idx  = sh3idx
\/  sh2idx  = PPRidx \/  sh2idx = PRidx) as Htmp 
by auto.
generalize (Hpd  phyDescChild  Hchildpart); clear Hpd; intros Hpd.
generalize (Hpd sh2idx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *;
destruct (StateLib.Index.succ sh2idx); [|now contradict H0];
destruct (lookup phyDescChild i (memory s) beqPage beqIndex); [|now contradict H0];
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaChildsh2. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaChildsh2 sh2idx phyDescChild vaChild s /\ ptVaChildsh2 = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr vaChild fstLevel = idx ->
isVA ptVaChildsh2 idx s /\ getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxSh2idxSh1notEq.
    - split;trivial.
    - contradict Hfalse.
      symmetrynot.
      apply idxPDidxSh2notEq. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptVaChildpdIsnull. simpl.
case_eq ptVaChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptVaChildpdIsnull. subst.
(** write virtual **)
eapply WP.bindRev.
eapply WP.weaken.
eapply writeVirtualInv.
intros.
exact Hlegit1.
exact Hlegit.
intros.
destruct H as ((Ha1 & Ha3) & Ha4).
try repeat rewrite and_assoc in Ha1.
unfold propagatedPropertiesAddVaddr.
split.
exact Ha1.
{ destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
  subst.
  apply beq_nat_false in Ha4.
  now contradict Ha4.
  destruct Ha3 with (StateLib.getIndexOfAddr vaChild fstLevel);trivial.
  intuition. } 
intros [].
(** writeVirEntry **)
eapply bindRev.
eapply weaken.
eapply writeVirEntryAddVaddr;trivial.
intros.
exact Hlegit1.
exact Hlegit.
intros.
simpl.
exact H.
intros [].
(** writeVirEntry **)
eapply bindRev.
eapply weaken.
apply writePhyEntryMapMMUPage.
instantiate (1:= presentDescPhy);trivial.
instantiate (1:= presentvaChild);trivial.
  try repeat rewrite andb_true_iff in *. 
  intuition.
  eapply Hlegit1.
  intros;simpl.
  eapply H.
  intros. eapply weaken.
  eapply WP.ret;trivial.
  intros;trivial.
Qed.