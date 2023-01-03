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
    This file contains the invariants of [findBlockInKS, findBelongingBlock] and
		associated lemmas.
*)
Require Import Model.Monad Model.Lib Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants.
Require Import Compare_dec Bool.

Lemma findBlockComp  (entryaddr referenceaddr : paddr) (comparator : index) (P : state -> Prop)  :
{{fun s  =>  P s
						/\ isBE entryaddr s}}
Internal.findBlockComp entryaddr referenceaddr comparator
{{fun isMatch s => P s}}.
Proof.
unfold Internal.findBlockComp.
eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr *)
	eapply weaken. apply readBlockStartFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
}
intro blockstart.
eapply bindRev.
{ (** MALInternal.Index.zero *)
	eapply weaken. apply Index.zero.
	intros. simpl. apply H.
}
intro zero. simpl.
destruct beqIdx eqn:Hcomp.
- (* beqIdx comparator zero = true *)
	case_eq (beqAddr blockstart referenceaddr).
	+ (* case_eq beqAddr blockstart referenceaddr = true *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. apply H0.
		}
	+ (* case_eq beqAddr blockstart referenceaddr = false *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. apply H0.
		}
- (* beqIdx comparator zero = false *)
	eapply bindRev.
	{ (** MAL.readBlockEndFromBlockEntryAddr *)
		eapply weaken. apply readBlockEndFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
	}
	intro blockend.
	eapply bindRev.
	{ (** MALInternal.Paddr.leb *)
		eapply weaken. apply Paddr.leb.
		intros. simpl. apply H.
	}
	intro aboveStart.
	eapply bindRev.
	{ (** MALInternal.Paddr.leb *)
		eapply weaken. apply Paddr.leb.
		intros. simpl. apply H.
	}
	intro belowEnd.
	case_eq (aboveStart && belowEnd).
	+ (* case_eq aboveStart && belowEnd = true *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. apply H0.
		}
	+ (* case_eq aboveStart && belowEnd = false *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. apply H0.
		}
Qed.

Lemma findBlockInKSInStructAux n (currentidx : index)
																(currentkernelstructure referenceaddr : paddr)
																(compoption : index) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency s
										/\ isKS currentkernelstructure s
										/\ currentidx < kernelStructureEntriesNb
}}
Internal.findBlockInKSInStructAux n currentidx currentkernelstructure referenceaddr compoption
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency s /\
		(blockaddr = nullAddr
				\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)))
}}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert currentidx currentkernelstructure referenceaddr compoption.
induction n.
- (* n = 0 *)
	intros;simpl.
	{	(* MALInternal.getNullAddr *)
		eapply weaken. unfold MALInternal.getNullAddr.
		eapply WP.ret. intros. simpl. intuition.
	}
- (* n = S n*)
	(*unfold Internal.findBlockInKSInStructAux.*)
	intros.
	eapply bindRev.
	{ (** getBlockEntryAddrFromKernelStructureStart *)
		eapply weaken. apply getBlockEntryAddrFromKernelStructureStart.
		intros. split. apply H. unfold consistency in *. cbn. intuition.
	}
	intro entryaddr.
	eapply bindRev.
	{ (** MAL.readBlockPresentFromBlockEntryAddr *)
		eapply weaken. apply readBlockPresentFromBlockEntryAddr.
		intros. simpl. split. apply H. intuition.
	}
	intro ispresent.
	eapply bindRev.
	{ (** findBlockComp *)
		eapply weaken. apply findBlockComp.
		intros. simpl. split. apply H. intuition.
	}
	intro matchcomp.
	case_eq (ispresent && matchcomp).
	+ (* case_eq ispresent && matchcomp = true *)
		intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition. right. apply isBELookupEq. intuition.
		}
	+ (* case_eq ispresent && matchcomp = false *)
		intros.
		eapply bindRev.
		{ (** getKernelStructureEntriesNb *)
			eapply weaken. apply getKernelStructureEntriesNb.
			intros. simpl. apply H0.
		}
		intro maxentriesnb.
		eapply bindRev.
		{ (** succ *)
			eapply weaken. apply Index.succ.
			intros. simpl. split. apply H0. intuition.
			apply PeanoNat.Nat.lt_le_incl.
			rewrite KSEntriesNbLessThanMaxIdx in *.
			apply PeanoNat.Nat.lt_add_lt_sub_l in H8.
			rewrite PeanoNat.Nat.add_comm. assumption.
		}
		intro nextidx.
		eapply bindRev.
		{ (** Index.ltb *)
			eapply weaken. apply Index.ltb.
			intros. simpl. apply H0.
		}
		intro isnotlastidx.
		case_eq (isnotlastidx).
		* (* case_eq isnotlastidx = true *)
			intros.
			{ (** induction hypothesis *)
				eapply weaken. apply IHn.
				intros. intuition.
				- (* nextidx < kernelStructureEntriesNb checked before *)
					unfold StateLib.Index.ltb in *.
					apply eq_sym in H3.
					apply PeanoNat.Nat.ltb_lt in H3. subst.
					unfold CIndex in *. destruct (le_dec kernelStructureEntriesNb maxIdx).
					simpl in *. assumption.
					contradict n0. apply PeanoNat.Nat.lt_le_incl.
					apply NPeano.Nat.lt_pred_lt.
					rewrite Minus.pred_of_minus.
					apply KSEntriesNbLessThanMaxIdx.
		}
		* (* case_eq isnotlastidx = false *)
			intros.
			{ (** ret *)
				eapply weaken. apply ret.
				intros. simpl. intuition.
			}
Qed.

Lemma findBlockInKSAux n (currentkernelstructure idblock : paddr)
																(compoption : index) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency s
										/\ isKS currentkernelstructure s}}
Internal.findBlockInKSAux n currentkernelstructure idblock compoption
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency s /\
																				(blockaddr = nullAddr \/
																	(exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry))) }}.
Proof.
(* revert mandatory to generalize the induction hypothesis *)
revert currentkernelstructure idblock compoption.
induction n.
- (* n = 0 *)
	intros;simpl.
	(* MALInternal.getNullAddr *)
	eapply weaken. unfold MALInternal.getNullAddr.
	eapply WP.ret. intros. simpl. intuition.
- (* n = S n*)
	unfold Internal.findBlockInKSAux.
	intros.
	eapply bindRev.
	{ (** MALInternal.Index.zero *)
		eapply weaken. apply Index.zero.
		intros. simpl. apply H.
	}
	intro zero.
	eapply bindRev.
	{ (** Internal.findBlockInKSInStructAux *)
		eapply weaken. apply findBlockInKSInStructAux.
		intros. simpl. split. apply H. intuition.
		- (* zero < kernelStructureEntriesNb by axiom *)
			apply CIndex0ltKSEntriesNb. assumption.
		(*- (* zero < maxIdx - 1 by axiom *)
			apply CIndex0ltMaxIdx. assumption.*)
	}
	intro foundblock.
	eapply bindRev.
	{ (** Internal.compareAddrToNull *)
		eapply weaken. apply compareAddrToNull.
		intros. simpl. apply H.
	}
	intro foundblockisnull.
	case_eq foundblockisnull.
	+ (* case_eq foundblockisnull = true *)
		intros.
		eapply bindRev.
		{ (** MAL.readNextFromKernelStructureStart *)
			eapply weaken. apply readNextFromKernelStructureStart.
			intros. simpl. split. apply H0. unfold consistency in *. intuition.
		}
		intro nextkernelstructure.
		eapply bindRev.
		{ (** Internal.compareAddrToNull *)
			eapply weaken. apply compareAddrToNull.
			intros. simpl. apply H0.
		}
		intro nextKSisnull.
		case_eq nextKSisnull.
		* (* case_eq nextKSisnull = true *)
			intros.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition.
		}
		* (* case_eq nextKSisnull = false *)
			intros.
			{ (** induction hypothesis *)
				eapply weaken. apply IHn.
				intros. simpl. split. apply H1. split. apply H1. intuition.
				- destruct H4. unfold consistency in *. intuition.
				unfold NextKSIsKS in *.
				apply beqAddrFalse in H3.
				eauto.
				- (* impossible, foundblock is null *)
					contradict H9.
					apply beqAddrTrue in H5. subst.
					unfold consistency in *.
					unfold nullAddrExists in *.
					intuition. unfold isPADDR in *.
					destruct H.
					rewrite H in *. congruence.
			}
	+ (* case_eq foundblockisnull = false *)
		intros. simpl.
		{ (** ret *)
			eapply weaken. apply ret.
			intros. simpl. intuition.
		}
Qed.

Lemma findBelongingBlock (idPD referenceaddr: paddr) (P : state -> Prop) :
{{ fun s => P s /\ consistency s /\ isPDT idPD s}}
Internal.findBelongingBlock idPD referenceaddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency s /\
			(blockaddr = nullAddr
					\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)))
}}.
Proof.
unfold Internal.findBelongingBlock.
eapply bindRev.
{ (** MALInternal.Index.zero *)
	eapply weaken. apply Index.zero.
	intros. simpl. apply H.
}
intro zero.
eapply bindRev.
{ (** MALInternal.Index.succ *)
	eapply weaken. apply Index.succ.
	intros. simpl. split. apply H.
	intuition. rewrite H1. unfold CIndex. destruct (le_dec 0 maxIdx).
(*	simpl. rewrite <- PeanoNat.Nat.lt_add_lt_sub_l.*)
	simpl. apply PeanoNat.Nat.lt_le_incl. apply maxIdxBigEnough.
	contradict n. apply PeanoNat.Nat.lt_le_incl. apply maxIdxNotZero.
}
intro one.
eapply bindRev.
{ (** MAL.readPDStructurePointer *)
	eapply weaken. apply readPDStructurePointer.
	intros. simpl. split. apply H. intuition.
}
intro kernelstructurestart.
{ (** Internal.findBlockInKSAux *)
	eapply weaken. apply findBlockInKSAux.
	intros. simpl. intuition.
	unfold pdentryStructurePointer in *.
	unfold isPDT in *.
	destruct (lookup idPD (memory s) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
	destruct v eqn:Hv ; try (exfalso ; congruence).
	unfold consistency in *.
	unfold StructurePointerIsKS in *. intuition.
	subst.
	apply H16 with idPD. assumption.
}
Qed.

Lemma findBlockInKS (idPD blockEntryAddr: paddr) (P : state -> Prop) :
{{ fun s => P s /\ consistency s /\ isPDT idPD s}}
Internal.findBlockInKS idPD blockEntryAddr
{{fun (blockaddr : paddr) (s : state) => P s /\ consistency s /\
			(blockaddr = nullAddr
			\/ (exists entry, lookup blockaddr s.(memory) beqAddr = Some (BE entry)))
}}.
Proof.
unfold Internal.findBlockInKS.
eapply bindRev.
{ (** MALInternal.Index.zero *)
	eapply weaken. apply Index.zero.
	intros. simpl. apply H.
}
intro zero.
eapply bindRev.
{ (** MAL.readPDStructurePointer *)
	eapply weaken. apply readPDStructurePointer.
	intros. simpl. split. apply H. intuition.
}
intro kernelstructurestart.
{ (** Internal.findBlockInKSAux *)
	eapply weaken. apply findBlockInKSAux.
	intros. simpl. intuition.
	unfold pdentryStructurePointer in *.
	unfold isPDT in *.
	destruct (lookup idPD (memory s) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
	destruct v eqn:Hv ; try (exfalso ; congruence).
	unfold consistency in *.
	unfold StructurePointerIsKS in *. intuition.
	subst.
	apply H15 with idPD. assumption.
}
Qed.

