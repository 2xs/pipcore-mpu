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
Require Import Model.Monad Model.Lib Model.MAL Model.ADT.
Require Import Core.Internal.
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions Proof.invariants.Invariants.
Require Import Compare_dec Bool.

(* Whatever the pd, be it a child or the current partition, removing a block
	doesn't change the security properties *)
(* no lemma to use :
1) create a temporary lemma with the desired output properties
2) admit the lemma and see if this is enough to continue the principal proof
3) if yes, then prove the lemma *)
(*Definition defaultBlockEntry defaultentry s: Prop :=
let emptyblock := CBlock nullAddr nullAddr in
let entriesnb := getKernelStructureEntriesNb in
defaultentry = 
match defaultentry with 
|Some (CBlockEntry false false false false false entriesnb emptyblock) => True
|_ => False
end.
*)

Lemma getDefaultBlockEntry (P : state -> Prop) :
{{ fun s => P s	}}
MAL.getDefaultBlockEntry
{{fun (defaultentry : BlockEntry) (s : state) => P s}}.
Proof.
Admitted.


Lemma removeBlockFromPhysicalMPU (pd : paddr) (blockentryaddr : paddr) (P : state -> Prop) :
{{ fun s => P s	}}
MAL.removeBlockFromPhysicalMPU pd blockentryaddr
{{fun (_ : unit) (s : state) => P s}}.
Proof.
Admitted.


(* COPY *)
Lemma writeBlockEntryFromBlockEntryAddr  (entryaddr : paddr) (blockentry : BlockEntry)  (P : unit -> state -> Prop) :
{{fun  s => lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\ 
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
								(BE (CBlockEntry 	blockentry.(read) blockentry.(write) blockentry.(exec)
																	blockentry.(present) blockentry.(accessible)
																	blockentry.(blockindex) blockentry.(blockrange)))
              (memory s) beqAddr |} }}
writeBlockEntryFromBlockEntryAddr entryaddr blockentry
{{P}}.
Proof.
unfold writeBlockEntryFromBlockEntryAddr.
eapply bindRev.
{ (** MAL.writeBlockStartFromBlockEntryAddr *)
	eapply weaken. eapply writeBlockStartFromBlockEntryAddr.
	intros. simpl. destruct H. exists blockentry. split. apply H.
	assert ((CBlock (startAddr (blockrange blockentry))
                       (endAddr (blockrange blockentry))) = (blockrange blockentry)).
	{ destruct blockentry. simpl. cbn. destruct blockrange. simpl. intuition.
		unfold CBlock. simpl. destruct (lt_dec startAddr endAddr) eqn:Hltdec ; try (exfalso; congruence).
		destruct startAddr,endAddr. simpl in *. intuition.
simpl. trivial. f_equal. intuition.
	unfold ADT.CBlock_obligation_1. f_equal. destruct p, p0 ; intuition.
	destruct p0 ; intuition. simpl in *. (* 0 < 1 *)


eapply weaken. apply 
{ (** MAL.writeBlockStartFromBlockEntryAddr *)
	eapply weaken. apply writeBlockStartFromBlockEntryAddr.
	intros. simpl. destruct H. exists x. split. apply H.
	apply H.
intros.
eapply bind. intros.
eapply bind. intros.
eapply bind. intros.
eapply bind. intros.
eapply bind. intros.
eapply bind. intros.
eapply weaken. apply ret.
intros. exact H.
eapply weaken. apply writeBlockXFromBlockEntryAddr.
intros. simpl. eexists. apply H.
eapply weaken. apply writeBlockWFromBlockEntryAddr.
intros. simpl. unfold beqAddr. rewrite PeanoNat.Nat.eqb_refl. eexists. apply H.
eapply weaken. apply writeBlockRFromBlockEntryAddr.
intros. simpl. unfold beqAddr. rewrite PeanoNat.Nat.eqb_refl. eexists. apply H.
eapply weaken. apply writeBlockPresentFromBlockEntryAddr.
intros. simpl. unfold beqAddr. rewrite PeanoNat.Nat.eqb_refl. eexists. apply H.
eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr.
intros. simpl. unfold beqAddr. rewrite PeanoNat.Nat.eqb_refl. eexists. apply H.
eapply weaken. apply writeBlockEndFromBlockEntryAddr.
intros. simpl. unfold beqAddr. rewrite PeanoNat.Nat.eqb_refl. eexists. apply H.
eapply weaken. apply .
intros. simpl. unfold beqAddr. rewrite PeanoNat.Nat.eqb_refl. eexists. apply H.
Qed.



Lemma freeSlot (pd entrytofreeaddr: paddr) (P : state -> Prop) :
{{ fun s =>    partitionsIsolation s /\ verticalSharing s /\ kernelDataIsolation s /\ consistency s
						/\ isPDT pd s /\ pd = currentPartition s
						/\ isBE entrytofreeaddr s /\ beqAddr nullAddr entrytofreeaddr = false
						}}
Internal.freeSlot pd entrytofreeaddr
{{fun (freedblockaddr : paddr) (s : state) => partitionsIsolation s /\ verticalSharing s /\ kernelDataIsolation s /\ consistency s
																							(* /\ isBE freedblockaddr s*) }}.
Proof.
unfold Internal.freeSlot.
(*
eapply bind. intros.
eapply bind. intro defaultBlockEntry.
eapply bind. intros.
eapply bind. intro defaultSh1Entry.
eapply bind. intros.
eapply bind. intro defaultSCEntry.
eapply bind. intros.
eapply bind. intro currFirstFreeSlot.
eapply bind. intros.
eapply bind. intros.
eapply bind. intro nbfreeslots.
eapply bind. intro nbfreeslotssucc.
eapply bind. intros.
eapply weaken. apply ret.
intros. simpl. exact H.
eapply weaken. apply writePDNbFreeSlots.
intros. simpl. eexists. split. apply H.
set (s' := {| currentPartition := _ |}). intuition.
unfold partitionsIsolation. intuition.
unfold getUsedBlocks. unfold getConfigBlocks. unfold getMappedBlocks.
destruct (lookup child1 (memory s') beqAddr) eqn:Hlookup ; try (exfalso; congruence).
destruct v eqn:Hv ; try (exfalso; congruence).
Search (nil).
destruct (lookup child2 (memory s') beqAddr) eqn:Hlookup'' ; try (exfalso; congruence).
destruct v eqn:Hv' ; try (exfalso; congruence).
destruct (monadToValue (MAL.readPDStructurePointer child1) s') eqn:Hmonad' ; try (exfalso; congruence).
destruct v0 eqn:Hv0' ; try (exfalso; congruence).
destruct (monadToValue (MAL.readPDStructurePointer child2) s') eqn:Hmonad'' ; try (exfalso; congruence).
simpl.
destruct v eqn:Hv' ; try (exfalso; congruence).
simpl.


instantiate (1:= fun s nbfreeslotssucc => exists pd, isPDT pd s /\ pdentryNbFreeSlots pd nbfreeslotssucc s). apply writePDNbFreeSlots.
intros. simpl. exists pd.

*)





eapply bindRev.
{ (** removeBlockFromPhysicalMPU *)
	intros. apply removeBlockFromPhysicalMPU.
}
intros.
eapply bindRev.
{ (** getDefaultBlockEntry *)
	eapply weaken. apply getDefaultBlockEntry.
	intros. simpl. apply H.
}
intro defaultBlockEntry.
eapply bindRev.
{ (** writeBlockEntryFromBlockEntryAddr *)
	eapply weaken. apply writeBlockEntryFromBlockEntryAddr.
	intros. simpl. apply H.
}

