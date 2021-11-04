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
Require Import Model.Monad Model.Lib Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants.
Require Import Compare_dec Bool.

Lemma findBlockInKSWithAddrAux n (kernelstructurestart blockEntryAddr : paddr) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency s
										/\ isKS kernelstructurestart s}}
Internal.findBlockInKSWithAddrAux n kernelstructurestart blockEntryAddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency s /\
																				(blockaddr = nullAddr \/
																	(exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
																			/\ blockaddr = blockEntryAddr)) }}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert kernelstructurestart blockEntryAddr.
	induction n.
- (* n = 0 *)
	intros;simpl.
	(* MALInternal.getNullAddr *)
	eapply weaken. unfold MALInternal.getNullAddr.
	eapply WP.ret. intros. simpl. intuition.
- (* n = S n*)
	intros. simpl.
	eapply bindRev.
	{ (** leb *)
		eapply weaken. apply Paddr.leb.
		intros. simpl. apply H.
	}
	intro isEntryAddrAboveStart.
	eapply bindRev.
	{ (** zero *)
		eapply weaken. apply Index.zero.
		intros. simpl. apply H.
	}
	intro zero.
	eapply bindRev.
	{ (** getSh1EntryAddrFromKernelStructureStart *)
		eapply weaken. apply getSh1EntryAddrFromKernelStructureStart.
		intros. simpl. split. apply H. unfold consistency in *. intuition.
		unfold pdentryPDStructurePointer in *.
		unfold isPDT in *.
		cbn. subst. unfold CIndex. destruct (lt_dec 0 maxIdx) ; intuition.
	}
	intro maxEntryAddrInStructure.
	eapply bindRev.
	{ (** leb *)
		eapply weaken. apply Paddr.leb.
		intros. simpl. apply H.
	}
	intro isEntryAddrBelowEnd.
	case_eq (isEntryAddrAboveStart && isEntryAddrBelowEnd).
		+ (* case_eq isEntryAddrAboveStart && isEntryAddrBelowEnd = true *)
			intros.
			eapply bindRev.
			{ (** checkEntry *)
				eapply weaken. apply checkEntry.
				intros. simpl. apply H0.
			}
			intro entryExists.
			case_eq entryExists.
				* (* case_eq entryExists = true *)
					intros. simpl.
					eapply bindRev.
					{ (** MAL.readBlockPresentFromBlockEntryAddr *)
						eapply weaken. apply readBlockPresentFromBlockEntryAddr.
						intros. simpl. split. apply H1. intuition.
					}
					intro isPresent.
					case_eq isPresent.
						-- (* case_eq isPresent = true *)
							intros. simpl. eapply weaken. apply ret.
							intros. simpl. intuition.
							right. apply isBELookupEq in H10. destruct H10. exists x. intuition.
						-- (* case_eq isPresent = false *)
							intros. eapply weaken. apply ret.
							intros. simpl. intuition.
				* (* case_eq entryExists = false *)
					intros. simpl. eapply weaken. apply ret.
					intros. simpl. intuition.
		+	(* case_eq isEntryAddrAboveStart && isEntryAddrBelowEnd = false *)
			intros.
			eapply bindRev.
			{ (** readNextFromKernelStructureStart *)
				eapply weaken. apply readNextFromKernelStructureStart.
				intros. simpl. split. apply H0. intuition.
				unfold consistency in *. intuition.
			}
			intro nextKernelStructure.
			eapply bindRev.
			{ (** Internal.compareAddrToNull *)
				eapply weaken. apply compareAddrToNull.
				intros. simpl. apply H0.
			}
			intro isnull.
			case_eq isnull.
				* (* case_eq isnull = true *)
					intros.
					{ (** ret *)
						eapply weaken. apply ret.
						intros. simpl. intuition.
					}
				* (* case_eq isnull = false *)
					{ (** induction hypothesis *)
						intros. eapply weaken. apply IHn.
						intros. simpl. intuition.
						unfold consistency in *. intuition.
						unfold KSIsBE in *. eauto.
						unfold NextKSIsKS in *. 
						destruct H4.
						apply H22 with kernelstructurestart x ; intuition.
						(* Prove nextKernelStructure <> nullAddr *)
						apply beqAddrFalse in H3. intuition.
					}
Qed.



Lemma findBlockInKSWithAddr (idPD blockEntryAddr: paddr) (P : state -> Prop) :
{{ fun s => P s /\ consistency s /\ isPDT idPD s}} Internal.findBlockInKSWithAddr idPD blockEntryAddr 
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency s /\
																				(blockaddr = nullAddr \/
																	(exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)
																			/\ blockaddr = blockEntryAddr)) }}.
Proof.
unfold Internal.findBlockInKSWithAddr.
eapply bindRev.
{ (** readPDStructurePointer *)
	eapply weaken. apply readPDStructurePointer.
	intros. simpl. split. apply H. intuition.
}
	intro kernelstructurestart.
	(** findBlockInKSWithAddrAux *)
	eapply weaken. apply findBlockInKSWithAddrAux.
	intros. simpl. intuition.
	unfold consistency in *. unfold StructurePointerIsKS in *. intuition.
	unfold isPDT in *.
	destruct (lookup idPD (memory s) beqAddr) eqn:Hlookup ; try (exfalso; congruence).
	destruct v eqn:Hv ; try (exfalso; congruence).
	unfold pdentryPDStructurePointer in *.
	rewrite Hlookup in H1.
	subst.
	apply H13 with idPD.
	assumption.
Qed.


