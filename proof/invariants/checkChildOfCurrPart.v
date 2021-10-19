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
Require Import Proof.Consistency (*Pip.Proof.DependentTypeLemmas*) Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants
								Proof.invariants.findBlockInKSWithAddr.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec (*EqNat*) List Bool.

Module WP := WeakestPreconditions.

(* Couper le code de preuve -> ici que faire une propagation des propriétés initiale
+ propager nouvelles propriétés *) 
Lemma checkChildOfCurrPart (currentPartition idPDchild : paddr) P :
{{ fun s => P s /\ consistency s (*/\ exists nullAddr,  lookup nullAddr (memory s) beqAddr = Some (PADDR nullAddr)*)}}
Internal.checkChildOfCurrPart  currentPartition idPDchild
{{fun isChild s => P s /\ consistency s (*Q s /\ consistency s*)
												
/\ exists sh1entryaddr, isChild = StateLib.checkChild idPDchild s sh1entryaddr
(*/\ (exists entry, lookup idPDchild s.(memory) beqAddr = Some (BE entry)
												/\ entryPDT idPDchild entry.(blockrange).(startAddr) s)*)
/\ if isChild then (exists entry, lookup idPDchild s.(memory) beqAddr = Some (BE entry)
										/\ exists sh1entry, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry))
		else isChild = false
(*/\ exists globalIdPDChild : paddr, 
	exists pdtentry : PDTable, lookup (beentry.(blockrange).(startAddr)) s.(memory) beqAddr = Some (PDT pdtentry)
-> pas cette condition car on retourne ensuite dans le code principal et si on termine 
en faux on peut pas prouver ctte partie *)
}}.
Proof.
unfold Internal.checkChildOfCurrPart.
eapply WP.bindRev.
{
	(** findBlockInKSWithAddr *)
		
		apply findBlockInKSWithAddr.
}
		intro blockInParentPartAddr. simpl.
	(** compareAddrToNull **)
	eapply WP.bindRev.
	eapply Invariants.compareAddrToNull.
	intro addrIsNull0.
	simpl.
	destruct addrIsNull0 eqn:ischild.
	- { (*addrIsNull0 = true*)
		eapply WP.weaken. apply WP.ret. intros. simpl.
		destruct H. destruct H. split. apply H. split. apply H.
		unfold checkChild.
		
		exists blockInParentPartAddr. destruct H1. destruct H1. subst.
		rewrite -> H1. trivial. split ; trivial. (*

		assert(beqAddr nullAddr blockInParentPartAddr = true -> nullAddr = blockInParentPartAddr).
		{ admit. (*intros. Set Printing All. unfold beqAddr. Set Printing All.
			unfold beqAddr in *.
			unfold PeanoNat.Nat.eqb in *.
			Search (?x = ?y -> PeanoNat.Nat.eqb ?y ?x = true).

 apply EqNat.beq_nat_true in H4.
			Set Printing All.
			eapply H4.
			unfold nullAddr in *. Set Printing All. rewrite -> H.

apply H.*) }
		(*unfold beqAddr in H1. apply PeanoNat.Nat.eqb_eq in H1. Set Printing All. rewrite <- H1.
	apply H in H1.
	rewrite <- H1.*)

Set Printing All. unfold beqAddr in H1.
		unfold consistency in *.
		intuition.
		Set Printing All.
 unfold nullAddrExists in *. unfold getNullAddr in *.
		Search (PeanoNat.Nat.eqb ?x ?y = true).
		apply PeanoNat.Nat.eqb_eq in H1. subst.
		contradict H.
Set Printing All.
		rewrite <- H1.

 subst.

(* split. apply H. split. apply H. 
		destruct H. destruct H.
	destruct H1. destruct H1. (*destruct H0. split. apply H4.*) 
	unfold checkChild. subst. destruct H. destruct H2. destruct H3.
	
	exists idPDchild. rewrite -> H1.
	split. trivial. 
exists x. split. trivial. unfold beqAddr
	unfold entryPDT. rewrite -> H1.
	destruct (lookup (startAddr (blockrange x)) (memory s) beqAddr) eqn:Hlookup.
	destruct v eqn:Hv. congruence.*)
(*
		eapply weaken.
 apply H. 
		exists P. apply H.*)
		(*intros. destruct H. destruct H. destruct H. destruct H2.
		destruct x in H2. apply H2.
		apply H2.
eassumption. simpl. apply H. destruct H. destruct H. apply H. simpl. split.  apply H0.*) (*destruct H0. destruct H0.
	destruct H2. destruct H2. (*destruct H0. split. apply H4.*) exists x. rewrite <- H3. split. apply H2.
	unfold checkChild. subst. unfold beqAddr in H1. rewrite -> H1. trivial. *)
	(*3: { intros. simpl in *. apply H0. }*)
		(*simpl. eapply WP.weaken. apply WP.ret.
	intros. destruct H0. destruct H0. destruct H0. destruct H0. assumption.*)
*)}
	- { (*addrIsNull0 = true*)
			intros. 
(*	eapply bind. 2: { eapply weaken. apply Invariants.readSh1PDFlagFromBlockEntryAddr.
	intros. simpl.
		split. apply H0. destruct H0 ; destruct H0 . destruct H2 ; destruct H2.
		split. apply H0.
 exists x. apply H2.
*)
 		eapply bindRev.
		{	eapply weaken. apply Invariants.readSh1PDFlagFromBlockEntryAddr. intros. 
			intros. simpl. split. apply H. 
			intros. simpl.

			split. apply H. destruct H ; destruct H. destruct H1 ; destruct H1.

	 		exists x. apply H1.
 		}
			(*eapply weaken.
			
			
		(** readSh1PDFlagFromBlockEntryAddr.  *)
		+ simpl. (*eapply WP.weaken.
		2: { intros. apply H. } 
			eapply  weaken. *)eapply Invariants.readSh1PDFlagFromBlockEntryAddr.
			+ intros.
	(*eapply WP.readSh1PDFlagFromBlockEntryAddr.*) simpl. split. destruct H0 ; destruct H0. apply H0.


			destruct H0 ; destruct H0 . destruct H2 ; destruct H2. exists x. apply H2. (*split. apply H. (*split.*)
			unfold isBE. destruct (lookup blockInParentPartAddr (memory s) beqAddr) eqn:Hlookup.
			destruct v eqn:V ; destruct H ; destruct H ; destruct H1 ; destruct H1.
			trivial. congruence. congruence. congruence. congruence.
			destruct H ; destruct H ; destruct H1 ; destruct H1. congruence.*)
}*)

		 intro isChild. simpl.
			case_eq isChild.
			(* ischild =  true *)
			* intro childIsNotNull. simpl. eapply weaken. apply WP.ret.
			intros. simpl. split. apply H. split. apply H. (*apply H0.*) (*intuition.
			(*destruct H4. destruct H1. exists x. rewrite <- H4. split.
			apply H1.*) destruct H3. destruct H0. rewrite <- H3.*)
			unfold checkChild. destruct H. destruct H. destruct H0. destruct H.
		destruct H2. destruct H0. exists x1.
		destruct H0. destruct H2. subst. rewrite -> H2. rewrite -> H0. (*
 split. destruct H2. rewrite -> H3 in H2. assumption.

			destruct H0. exists x1. destruct H0. rewrite -> H0. (*unfold beqAddr in H0. destruct H. destruct H.
			destruct H3. destruct H0. rewrite -> H0.*)*)
			unfold sh1entryPDflag in *. rewrite -> H0 in *. split. assumption.
			exists x0. split. reflexivity.
			exists x. reflexivity.

		(* ischild = false : sh1entry exists but flag = 0 *)		
		 	* simpl. intros. eapply weaken.
			 apply WP.ret.
			intros. simpl. (*apply H1.*) split. apply H0. split. apply H0.


 destruct H0 ; destruct H0 ; destruct H0. destruct H1. repeat destruct H1. destruct H3.
		(* exists x0. destruct H1. split. rewrite H3 in *. assumption.*)

		exists x0. split. unfold sh1entryPDflag in H4. unfold checkChild. destruct H1. subst.
		rewrite -> H1.
		destruct (lookup x0 (memory s) beqAddr).
		destruct v ; trivial. trivial. trivial.
}
Qed.

Print checkChildOfCurrPart.
About checkChildOfCurrPart.
(*
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

