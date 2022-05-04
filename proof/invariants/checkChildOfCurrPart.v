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
    This file contains the invariant of [checkChildOfCurrPart].
*)
Require Import Model.Monad Model.Lib Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants
							 Proof.invariants.findBlockInKSWithAddr.

Lemma checkChildOfCurrPart (currentPartition idPDchild : paddr) P :
{{ fun s => P s /\ consistency s /\ isPDT currentPartition s}}
Internal.checkChildOfCurrPart  currentPartition idPDchild
{{fun isChild s => P s
/\ (isChild = true -> exists sh1entryaddr, isChild = StateLib.checkChild idPDchild s sh1entryaddr
										/\ exists entry, lookup idPDchild s.(memory) beqAddr = Some (BE entry)
										/\ exists sh1entry, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry))
}}.
Proof.
unfold Internal.checkChildOfCurrPart.
eapply WP.bindRev.
{
	(** findBlockInKSWithAddr *)
	eapply weaken. apply findBlockInKSWithAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockInParentPartAddr. simpl.
(** compareAddrToNull **)
eapply WP.bindRev.
{
	eapply weaken. eapply compareAddrToNull.
	intros. simpl. apply H.
}
intro addrIsNull0.
simpl.
case_eq addrIsNull0.
- (* case_eq addrIsNull0 = true*)
	{ (** ret *)
		intros. eapply WP.weaken. apply WP.ret.
		intros. simpl. intuition.
	}
- (* case_eq addrIsNull0 = false *)
	intros.
	eapply bindRev.
	{	(** Invariants.readSh1PDFlagFromBlockEntryAddr *)
		eapply weaken. apply Invariants.readSh1PDFlagFromBlockEntryAddr.
		intros. simpl. split. apply H0.
		intuition.
		intros. simpl.
		(* prove blockInParentPartAddr can't be NULL and not NULL at the same time *)
		apply beqAddrFalse in H2. exfalso ; congruence.
		destruct H4. exists x. apply H4.
	}
		intro isChild. simpl.
		case_eq isChild.
		+ (* ischild =  true *)
			intro childIsNotNull. simpl.
			{ (** ret *)
				eapply weaken. apply WP.ret.
				intros. simpl. intuition.
				(*blockInParentPartAddr can't be NULL and not NULL at the same time *)
				apply beqAddrFalse in H3. exfalso ; congruence.
				destruct H2. destruct H2. exists x0.
				split. unfold checkChild. destruct H5. intuition. subst. 
				rewrite H2. rewrite H8.
				unfold sh1entryPDflag in *. rewrite -> H8 in *. assumption.
				destruct H5. exists x1. split. intuition. subst. assumption.
				exists x. intuition.
			}
	 	+ (* ischild = false : sh1entry exists but PDflag = 0 *)
			simpl. intros.
			{ (** ret *)
				eapply weaken. apply WP.ret.
				intros. simpl. split. apply H1.
				intuition.
			}
Qed.

