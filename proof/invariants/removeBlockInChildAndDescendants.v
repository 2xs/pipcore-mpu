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
Require Import (*Model.ADT*) Model.Monad Model.Lib
               Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants.
Require Import Proof.invariants.findBlockInKSWithAddr Proof.invariants.checkBlockCut.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec (*EqNat*) List Bool.

Lemma checkRemoveSubblocksRecAux n (subblockAddr : paddr) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency s
										/\ isBE subblockAddr s}}
Internal.checkRemoveSubblocksRecAux n subblockAddr
{{fun (isRemovePossible : bool) (s : state) => P s /\ consistency s }}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert subblockAddr.
	induction n.
- (* n = 0 *)
	intros;simpl.
	(** ret *)
	eapply weaken. apply ret.
	intros. simpl. intuition.
- (* n = S n*)
	intros. simpl.
	eapply bindRev.
	{ (** MAL.readBlockAccessibleFromBlockEntryAddr*)
		eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
	}
	intro isAccessible.
	eapply bindRev.
	{ (** MAL.readBlockPresentFromBlockEntryAddr*)
		eapply weaken. apply readBlockPresentFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
	}
	intro isPresent.
	eapply bindRev.
	{ (** MAL.readSh1PDChildFromBlockEntryAddr*)
		eapply weaken. apply readSh1PDChildFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
		apply isBELookupEq. assumption.
	}
	intro PDChildAddr.
	eapply bindRev.
	{ (** Internal.compareAddrToNull*)
		eapply weaken. apply compareAddrToNull.
		intros. simpl. apply H.
	}
	intro PDChildAddrIsNull.
	case_eq (isAccessible && isPresent && PDChildAddrIsNull).
	* (* case_eq isAccessible && isPresent && PDChildAddrIsNull = true *)
		intros. simpl.
		eapply bindRev.
		{ (** MAL.readSCNextFromBlockEntryAddr*)
			eapply weaken. apply readSCNextFromBlockEntryAddr.
			intros. simpl. split. apply H0. intuition.
			apply isBELookupEq. assumption.
		}
		intro nextsubblock.
		eapply bindRev.
		{ (** Internal.compareAddrToNull*)
			eapply weaken. apply compareAddrToNull.
			intros. simpl. apply H0.
		}
		intro isNull.
		case_eq isNull.
		+ (* case_eq isNull = true *)
			intros.
			{ (** ret *)
				eapply weaken. apply ret.
				intros. simpl. intuition.
			}
		+ (* case_eq isNull = false *)
			{ (** induction hypothesis *)
				intros. eapply weaken. apply IHn.
				intros. simpl. intuition. Search (nextsubblock).
				unfold consistency in *. intuition.
				destruct H4. destruct H4. intuition.
				unfold scentryNext in *. rewrite H24 in *. subst.
				unfold scNextIsBE in *. apply H25 with x0.
				assumption.
				(* Prove next x <> nullAddr *)
				apply beqAddrFalse in H3. intuition.
			}
	* (*case_eq isAccessible && isPresent && PDChildAddrIsNull = false *)
		intros. simpl.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition.
		}
Qed.

Lemma checkRemoveSubblocksRec (subblockAddr : paddr) P :
{{ fun s => P s /\ consistency s
						/\ isBE subblockAddr s }}
checkRemoveSubblocksRec subblockAddr
{{fun isRemovePossible s => P s /\ consistency s}}.
Proof.
unfold checkRemoveSubblocksRec.
eapply weaken. apply checkRemoveSubblocksRecAux.
intros. simpl. intuition.
Qed.

Lemma removeSubblocksRecAux n (idPDchild subblockAddr : paddr) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency s
										/\ isBE subblockAddr s}}
Internal.removeSubblocksRecAux n idPDchild subblockAddr
{{fun (recRemoveSubblocksEnded : bool) (s : state) => P s /\ consistency s }}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert idPDchild subblockAddr.
induction n.
- (* n = 0 *)
	intros;simpl.
	(** ret *)
	eapply weaken. apply ret.
	intros. simpl. intuition.
- (* n = S n*)
	intros. simpl.
	eapply bindRev.
	{ (** Internal.compareAddrToNull*)
		eapply weaken. apply compareAddrToNull.
		intros. simpl. apply H.
	}
	intro isNull.
	case_eq isNull.
	+ (* case_eq isNull = true *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition.
		}
	+ (* case_eq isNull = false *)
		intros.
		eapply bindRev.
		{ (** MAL.readSCNextFromBlockEntryAddr *)
			eapply weaken. apply readSCNextFromBlockEntryAddr.
			intros. simpl. split. apply H0. intuition.
			apply isBELookupEq. assumption.
		}
		intro nextsubblock.
		eapply bindRev.
		{ (** freeSlot *)
			admit.
		}
		intros.
		{ (** removeSubblocksRecAux *)
		admit. (*eapply weaken. apply removeSubblocksRecAux.*)
		}
Admitted.

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


Lemma removeBlockInChildAndDescendants (currentPart
																				blockToRemoveInCurrPartAddr
																				idPDchild
																				blockToRemoveInChildAddr : paddr) P :
{{ fun s => P s /\ consistency s
						/\ isBE blockToRemoveInCurrPartAddr s
						/\ beqAddr nullAddr blockToRemoveInChildAddr = false
						/\ beqAddr nullAddr idPDchild = false
						(*/\  (exists (sh1entryaddr : paddr),
       isSHE sh1entryaddr s /\
       sh1entryInChildLocation sh1entryaddr blockToRemoveInChildAddr s)*)
						/\ isBE blockToRemoveInChildAddr s }}
Internal.removeBlockInChildAndDescendants currentPart blockToRemoveInCurrPartAddr
																					idPDchild blockToRemoveInChildAddr
{{fun isBlockRemoved s => P s /\ consistency s
(*/\ exists sh1entryaddr, isChild = StateLib.checkChild idPDchild s sh1entryaddr
/\ if isChild then (exists entry, lookup idPDchild s.(memory) beqAddr = Some (BE entry)
										/\ exists sh1entry, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry))
		else isChild = false*)
}}.
Proof.
unfold Internal.removeBlockInChildAndDescendants.
eapply bindRev.
{ (** readBlockStartFromBlockEntryAddr *)
	eapply weaken. apply readBlockStartFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
}
	intro globalIdBlockToRemove.
	eapply bindRev.
{ (** checkBlockCut *)
	eapply weaken. apply checkBlockCut.
	intros. simpl. split. apply H. intuition.
	(*TODO : set in RemoveMemoryBlock *)
	(*unfold sh1entryInChildLocation in *.
	destruct H6. destruct H5.
	destruct (lookup x (memory s) beqAddr) eqn:Hlookup.
	destruct v eqn:Hv. exfalso ; congruence.
	destruct H6.
	apply H7. unfold not. intros. apply beqAddrFalse in H3. intuition.
	exfalso ; congruence. exfalso ; congruence. exfalso ; congruence.
	exfalso ; congruence.*)
}
intro isBlockCut.
case_eq isBlockCut.
- (* case_eq isBlockCut = true *)
	intros. simpl.
	eapply bindRev.
	{ (** Internal.checkRemoveSubblocksRec *)
		eapply weaken. apply checkRemoveSubblocksRec.
		intros. simpl. split. apply H0. intuition.
	}
	intro isRemovePossible.
	case_eq isRemovePossible.
		+ (* case_eq isRemovePossible = true *)
			intros. simpl.
			eapply bindRev.
			{ (** removeSubblocksRec *)
				eapply weaken. apply removeSubblocksRec.
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
	+ (* case_eq isRemovePossible = false *)
		intros.  simpl.
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
Qed.
