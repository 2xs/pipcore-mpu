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
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec (*EqNat*) List Bool.

Module WP := WeakestPreconditions.

Lemma findBlockInKSWithAddrAux n (kernelstructurestart blockEntryAddr : paddr) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency s
										/\ exists pdaddr, pdentryPDStructurePointer pdaddr kernelstructurestart s}}
Internal.findBlockInKSWithAddrAux n kernelstructurestart blockEntryAddr
{{ fun (BF : paddr) (s : state) => P s /\ consistency s /\ isBE BF s }}.
Proof.
(*unfold findBlockInKSWithAddrAux.*)
(*revert n kernelstructurestart blockEntryAddr.*)
induction n.
- (* n = 0 *)
	intros;simpl.
	eapply weaken.
	eapply WP.ret. simpl. intuition.
	unfold consistency in *. unfold nullAddrExists in*. intuition.
- (* n = S n*)
	unfold findBlockInKSWithAddrAux.
	eapply bindRev.
	{ (* leb *)
		eapply weaken. apply Paddr.leb.
		intros. simpl. apply H.
	}
		intro isEntryAddrAboveStart.
		eapply bindRev.
	{ (* zero *)
		eapply weaken. apply Index.zero.
		intros. simpl. apply H.
	}
		intro zero.
		eapply bindRev.
	{ (* getSh1EntryAddrFromKernelStructureStart *)
		eapply weaken. apply getSh1EntryAddrFromKernelStructureStart.
		intros. simpl. split. apply H. unfold consistency in *. intuition.
		unfold pdentryPDStructurePointer in *. destruct H4.
		destruct H4.
		unfold StructurePointerIsBE in *.
		
		unfold isBE.

	}
		intro maxEntryAddrInStructure.

Qed.



Lemma findBlockInKSWithAddr (idPD blockEntryAddr: paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT idPD s}} Internal.findBlockInKSWithAddr idPD blockEntryAddr 
{{fun (BF : paddr) (s : state) => P s /\ exists entry, lookup BF s.(memory) beqAddr = Some (BE entry)
																			/\ BF = blockEntryAddr }}.
(* What happend is not block found ? no entry found *)
Proof.
unfold Internal.findBlockInKSWithAddr.
eapply bindRev.
{ (** readPDStructurePointer *)
	eapply weaken. apply readPDStructurePointer.
	intros. simpl. split. apply H. intuition.
}
	intro kernelstructurestart.
