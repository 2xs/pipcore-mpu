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
    This file contains the invariants of [sizeOfBlock].
*)
Require Import Model.Monad Model.Lib Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions
							 Proof.invariants.Invariants.
Require Import Compare_dec Bool Lia.
Require Import Model.ADT.

Lemma sizeOfBlock (blockentryaddr : paddr) (P :  state -> Prop) :
{{fun s => P s /\ consistency s /\ isBE blockentryaddr s }}
Internal.sizeOfBlock blockentryaddr
{{fun _ s => P s /\ consistency s}}.
Proof.
unfold sizeOfBlock.
eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr *)
	eapply weaken. apply readBlockStartFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
}
intro startAddr.
eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr *)
	eapply weaken. apply readBlockEndFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
}
intro endAddr.
eapply bindRev.
{ (** MALInternal.Paddr.subPaddr *)
	eapply weaken. apply Paddr.subPaddr.
	intros. simpl. split. apply H. split; try(split); try(lia).
  assert(endAddr <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp). lia.
}
intro size. eapply weaken. apply ret. intros s Hprops. simpl. intuition.
Qed.
