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
    This file contains the invariant of [findBlock].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas.
Require Import Invariants getGlobalIdPDCurrentOrChild findBlockInKS.
Require Import Compare_dec.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Module WP := WeakestPreconditions.

Lemma findBlock (idPD: paddr) (addrInBlock : paddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.findBlock idPD addrInBlock
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold Services.findBlock.
eapply bindRev.
{ (** getCurPartition **)
	eapply weaken. apply getCurPartition.
	intros. simpl. apply H.
}
intro currentPart.
eapply bindRev.
{ (** Internal.getGlobalIdPDCurrentOrChild **)
	eapply weaken. apply getGlobalIdPDCurrentOrChild.
	intros. simpl. split. apply H. intuition.
	subst currentPart.
	apply currentPartIsPDT ;
	unfold consistency in * ; unfold consistency1 in * ;
	intuition.
}
intro globalIdPD.
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
	{ (** Internal.findBelongingBlock *)
		eapply weaken. apply findBlockInKS.findBelongingBlock.
		intros. simpl. split. apply H0. intuition.
		apply H5. intros. apply beqAddrFalse in H2. congruence.
	}
	intro blockAddr.
	eapply bindRev.
	{ (** compareAddrToNull **)
		eapply weaken. apply Invariants.compareAddrToNull.
		intros. simpl. apply H0.
	}
	intro addrIsNull0.
	case_eq addrIsNull0.
	+ (* case_eq addrIsNull0 = true *)
		intros. simpl.
		{ (** ret *)
			eapply weaken. apply WP.ret.
			intros. intuition.
		}
	+ (* case_eq addrIsNull0 = false *)
		intros.
		eapply bindRev.
		{ (** MAL.readBlockEntryFromBlockEntryAddr *)
			eapply weaken. apply readBlockEntryFromBlockEntryAddr.
			intros. simpl. split. apply H1. intuition.
			- (* blockAddr = nullAddr, this is false since we are in the branch
						where we found the block *)
				contradict H11. apply beqAddrFalse in H3. congruence.
			- unfold isBE. destruct H11. rewrite H6;trivial.
		}
		intro blockentry.
		{ (** ret *)
			eapply weaken. apply WP.ret.
			intros. intuition.
		}
Qed.
