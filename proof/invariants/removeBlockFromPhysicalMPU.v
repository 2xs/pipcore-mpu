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
Require Import Model.Monad Model.Lib Model.MAL.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants.
Require Import Compare_dec Bool.
(*

Lemma removeBlockFromPhysicalMPUAux (blockentryaddr : paddr) (realMPU : list paddr) (P : state -> Prop) :
{{  fun s : state => P s /\ consistency s}}
MAL.removeBlockFromPhysicalMPUAux blockentryaddr realMPU
{{fun (realMPUentries : list paddr) (s : state) => P s /\ consistency s 
																				 }}.
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


Qed.*)

Lemma removeBlockFromPhysicalMPU (pd : paddr) (blockentryaddr : paddr) (P : state -> Prop) :
{{ fun s => partitionsIsolation s /\ verticalSharing s /\ kernelDataIsolation s /\ consistency s
						/\ isPDT pd s
						/\ isBE blockentryaddr s}}
MAL.removeBlockFromPhysicalMPU pd blockentryaddr
{{fun (_ : unit) (s : state) => partitionsIsolation s /\ verticalSharing s /\ kernelDataIsolation s  /\ consistency s}}.
Proof.
unfold MAL.removeBlockFromPhysicalMPU.
eapply bindRev.
{ (** MAL.readPDMPU *)
	eapply weaken. apply readPDMPU.
	intros. simpl. split. apply H. intuition.
}
intro realMPU.
eapply bind. intros. eapply weaken. apply ret. intros. simpl. apply H.
eapply weaken. apply writePDMPU.
intros. simpl.
unfold pdentryMPU in *.
destruct (lookup pd (memory s) beqAddr) eqn:Hlookup ; try (exfalso ; intuition ; congruence).
destruct v eqn:Hv ; try (exfalso ; intuition ; congruence).
exists p. set (s' := {|
       currentPartition := currentPartition s;
       memory := _ |}). intuition.
- unfold partitionsIsolation. intros. simpl.
	unfold Lib.disjoint. intros.
	unfold getUsedBlocks. unfold getConfigBlocks.
	unfold getMappedBlocks.
	destruct (lookup child2 (memory s') beqAddr) eqn:Hlookup' ; try (exfalso ; congruence).
	destruct v ; try (exfalso ; congruence). intuition. admit. admit.
- unfold verticalSharing. intros parent child.
	unfold verticalSharing in *.
	specialize (H0 parent child).
	apply H0 with parent child ; trivial.

eapply bindRev.
{ (** writePDMPU *)
	eapply weaken. apply writePDMPU.
	intros. simpl. intuition.
	unfold pdentryMPU in *.
	destruct (lookup pd (memory s) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
	destruct v eqn:Hv ; try (exfalso ; congruence).
	exists p. intuition.
