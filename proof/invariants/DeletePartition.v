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
    This file contains the invariant of [deletePartition].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas.
Require Import Invariants getGlobalIdPDCurrentOrChild findBlockInKS.
Require Import Compare_dec.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Module WP := WeakestPreconditions.

Lemma deletePartition (idPDchildToDelete: paddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.deletePartition idPDchildToDelete
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold Services.deletePartition.
eapply bindRev.
{ (** getCurPartition **)
	eapply weaken. apply getCurPartition.
	intros. simpl. split. apply H. intuition.
}
intro currentPart.
eapply bindRev.
{ (** Internal.findBlockInKSWithAddr *)
	eapply weaken. apply findBlockInKSWithAddr.findBlockInKSWithAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockToDeleteInCurrPartAddr.
eapply bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H.
}
intro addrIsNull.
case_eq addrIsNull.
- (* case_eq addrIsNull = true *)
		intros.
		{ (** ret *)
		eapply weaken. apply WP.ret.
		simpl. intros. intuition.
		}
- (* case_eq addrIsNull = false *)
		intros.
		eapply bindRev.
		{ (** MAL.readSh1PDFlagFromBlockEntryAddr *)
			eapply weaken. apply readSh1PDFlagFromBlockEntryAddr.
			intros. simpl. split. apply H0.
			repeat rewrite <- beqAddrFalse in *. intuition.
			destruct H8. exists x. intuition.
		}
		intro isChild.
		case_eq (negb isChild).
		+ (* case_eq negb isChild = true *)
				intros.
				{ (** ret *)
				eapply weaken. apply WP.ret.
				simpl. intros. intuition.
				}
		+ (* case_eq negb isChild = false *)
				intros.
				eapply bindRev.
				{ (** MAL.readBlockStartFromBlockEntryAddr *)
					eapply weaken. apply readBlockStartFromBlockEntryAddr.
					intros. simpl. split. apply H1.
					repeat rewrite <- beqAddrFalse in *. intuition.
					apply isBELookupEq. destruct H10. exists x. intuition.
				}
				intro blockStartAddr.
				eapply bindRev.
				{ (** MAL.readBlockEndFromBlockEntryAddr *)
					eapply weaken. apply readBlockEndFromBlockEntryAddr.
					intros. simpl. split. apply H1.
					repeat rewrite <- beqAddrFalse in *. intuition.
					apply isBELookupEq. destruct H11. exists x. intuition.
				}
				intro blockEndAddr.


Qed.
