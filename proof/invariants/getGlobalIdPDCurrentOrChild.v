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

(** * Summary
    This file contains the invariant of [getGlobalIdPDCurrentOrChild].
*)

Require Import Model.ADT Core.Services Model.MALInternal Model.Lib.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas.
Require Import invariants.Invariants invariants.checkChildOfCurrPart.

Require Import Model.Monad (* for visibility *).

Module WP := WeakestPreconditions.

Lemma getGlobalIdPDCurrentOrChild (currentPartition idPDToCheck : paddr) (P : state -> Prop):
{{fun s => P s /\ consistency s
					/\ isPDT currentPartition s}}
Internal.getGlobalIdPDCurrentOrChild currentPartition idPDToCheck
{{fun idPDChild s  => P s /\ consistency s /\
										(idPDChild <> nullAddr -> isPDT idPDChild s) }}.
Proof.
unfold Internal.getGlobalIdPDCurrentOrChild.
eapply bindRev.
{ (** MALInternal.getBeqAddr **)
	eapply weaken. apply getBeqAddr.
	intros. simpl. apply H.
}
intro isCurrentPart.
case_eq isCurrentPart.
- (* case_eq isCurrentPart = true *)
	intros.
	{ (** ret *)
	eapply weaken. apply WP.ret.
  simpl. intros. intuition.
	}
- (* case_eq isCurrentPart = false *)
	intros.
	eapply bindRev.
	{ (** Internal.checkChildOfCurrPart *)
		eapply weaken. apply checkChildOfCurrPart.
		intros. simpl. split. apply H0. intuition.
	}
	intro isChildCurrPart.
	case_eq isChildCurrPart.
	+ (* case_eq isChildCurrPart = true *)
		intros.
		eapply bindRev.
		{ (** MAL.readBlockStartFromBlockEntryAddr *)
			eapply weaken. apply readBlockStartFromBlockEntryAddr.
			intros. simpl. split. apply H1. intuition.
			destruct H5. intuition. destruct H7.
			unfold isBE. intuition. rewrite H7 ; trivial.
		}
		intro idPDChild.
		{ (** ret *)
		eapply weaken. apply WP.ret.
		simpl. intros. intuition.
		destruct H6.
		assert(HPDTIfPDFlag : PDTIfPDFlag s) by
			(unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold PDTIfPDFlag in *.
		intuition. unfold entryPDT in *. destruct H9. intuition.
		destruct H10 as [Hsh1entry Hsh1entryaddr]. destruct Hsh1entryaddr.
		assert(Hconj := conj H8 H6).
		specialize (HPDTIfPDFlag idPDToCheck x Hconj).
		destruct HPDTIfPDFlag as [HAFlag (HPFlag & (startaddr & HPDTIfPDFlag))]. intuition.
		unfold bentryStartAddr in *. rewrite H9 in *. subst.
		unfold isPDT.
		destruct (lookup (startAddr (blockrange x0)) (memory s) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
		destruct v eqn:Hv ; try (exfalso ; congruence) ; trivial.
		}
	+ (* case_eq isChildCurrPart = false *)
		intros.
		{ (** ret *)
		eapply weaken. apply WP.ret.
		simpl. intros. intuition.
		}
Qed.



