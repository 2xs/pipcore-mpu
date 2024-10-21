(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2024)                *)
(*  Copyright (C) 2020-2024 Orange                                             *)
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
Require Import Proof.Consistency (*Pip.Proof.DependentTypeLemmas*) Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants
								Proof.invariants.findBlockInKSWithAddr.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec (*EqNat*) List Bool.

Module WP := WeakestPreconditions.

(* Couper le code de preuve -> ici que faire une propagation des propriétés initiale
+ propager nouvelles propriétés *)
Lemma checkBlockCut (blockentryaddr : paddr) P :
{{ fun s => P s /\ wellFormedShadowCutIfBlockEntry s /\ KernelStructureStartFromBlockEntryAddrIsKS s
            /\ BlocksRangeFromKernelStartIsBE s /\ nullAddrExists s
						/\ isBE blockentryaddr s }}
Internal.checkBlockCut blockentryaddr
{{fun isBlockCut s => P s (*/\ consistency s*)
                      /\ exists blockStart blockOrigin blockNext,
                          scentryOrigin (CPaddr (blockentryaddr + scoffset)) blockOrigin s
                          /\ scentryNext (CPaddr (blockentryaddr + scoffset)) blockNext s
                          /\ bentryStartAddr blockentryaddr blockStart s
                          /\ beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr = negb isBlockCut
(*/\ exists sh1entryaddr, isChild = StateLib.checkChild idPDchild s sh1entryaddr
/\ if isChild then (exists entry, lookup idPDchild s.(memory) beqAddr = Some (BE entry)
										/\ exists sh1entry, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry))
		else isChild = false*)
}}.
Proof.
unfold Internal.checkBlockCut.
eapply WP.bindRev.
{ (** readSCOriginFromBlockEntryAddr *)
	eapply weaken. apply readSCOriginFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition. apply isBELookupEq. intuition.
}
	intro blockOrigin.
	eapply WP.bindRev.
{ (** readBlockStartFromBlockEntryAddr *)
	eapply weaken. apply readBlockStartFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
}
	intro blockStart.
	eapply WP.bindRev.
{ (** readSCNextFromBlockEntryAddr *)
	eapply weaken. apply readSCNextFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition. apply isBELookupEq. intuition.

}
	intro blockNext. simpl.
	case_eq (beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr).
{ (** case_eq beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr = true *)
	intros. eapply weaken. apply ret.
	intros. simpl. intuition. exists blockStart. exists blockOrigin. exists blockNext. intuition.
}
{ (** case_eq beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr = false *)
	intros. eapply weaken. apply ret.
	intros. simpl. intuition. exists blockStart. exists blockOrigin. exists blockNext. intuition.
}
Qed.
