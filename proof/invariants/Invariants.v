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
Require Import Core.Internal. (*Core.Services.*)
Require Import Proof.Consistency Proof.DependentTypeLemmas Proof.Hoare
               Proof.Isolation Proof.StateLib Proof.WeakestPreconditions.
Require Import Coq.Logic.ProofIrrelevance Lia Setoid Compare_dec EqNat List Bool.

Module WP := WeakestPreconditions.


(* COPY *)
Lemma getCurPartition P :
{{fun s => P s}} MAL.getCurPartition
{{fun (pd : paddr) (s : state) => P s /\ pd = currentPartition s }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.getCurPartition .
cbn. intros . intuition.
Qed.

Module Index.
(* COPY*)
Lemma ltb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.ltb index1 index2
{{ fun b s => P s /\ b = StateLib.Index.ltb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.ltb.
intros. simpl. split;trivial.
Qed.

(*COPY *)
Lemma leb index1 index2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Index.leb index1 index2
{{ fun b s => P s /\ b = StateLib.Index.leb index1 index2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.leb.
intros. simpl. split;trivial.
Qed.

(* partial DUP *)
Lemma zero P :
{{fun s => P s }} MALInternal.Index.zero
{{fun (idx0 : index) (s : state) => P s  /\ idx0 = CIndex 0 }}.
Proof.
unfold MALInternal.Index.zero.
eapply WP.weaken.
eapply WP.ret .
intros. simpl.
intuition.
Qed.

(* COPY *)
Lemma succ (idx : index ) P :
{{fun s => P s  /\ idx + 1 <= maxIdx }} MALInternal.Index.succ idx
{{fun (idxsuc : index) (s : state) => P s  /\ StateLib.Index.succ idx = Some idxsuc }}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.succ.
cbn.
intros.
split.
intuition.
split. intuition.
unfold StateLib.Index.succ.
subst.
destruct (le_dec (idx + 1) maxIdx). assert (l=l0).
apply proof_irrelevance.
subst. reflexivity.
intuition.
Qed.

(* COPY *)
Lemma pred (idx : index ) P :
{{fun s => P s  /\ idx > 0}} MALInternal.Index.pred idx
{{fun (idxpred : index) (s : state) => P s  /\ StateLib.Index.pred idx = Some idxpred }}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Index.pred.
cbn.
intros.
split.
intuition.
intros.
split. intuition.
unfold StateLib.Index.pred.
subst.
destruct (gt_dec idx 0).
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition.
Qed.
End Index.

Module Paddr.
(* DUP *)
Lemma leb addr1 addr2 (P : state -> Prop):
{{ fun s : state => P s }} MALInternal.Paddr.leb addr1 addr2
{{ fun b s => P s /\ b = StateLib.Paddr.leb addr1 addr2}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Paddr.leb.
intros. simpl. split;trivial.
Qed.

(* DUP de pred *)
Lemma subPaddr  (addr1 addr2 : paddr ) P :
{{fun s => P s  /\ addr1 >= 0 /\ addr2 >= 0 /\ addr1 - addr2 < maxIdx}}
MALInternal.Paddr.subPaddr addr1 addr2
{{fun (idxsub : index) (s : state) => P s  /\ StateLib.Paddr.subPaddr addr1 addr2 = Some idxsub }}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Paddr.subPaddr.
cbn.
intros.
split.
intuition.
intros.
split. intuition.
unfold StateLib.Paddr.subPaddr.
subst.
destruct (le_dec (addr1 - addr2) maxIdx).
split. intuition. intuition.
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition.
Qed.

(* DUP*)
Lemma subPaddrIdx  (addr : paddr) (idx: index) (P: state -> Prop) :
{{ fun s : state => P s /\ addr >= 0 /\ idx >= 0 /\ addr - idx <= maxAddr (*/\ forall Hp : n - m < maxAddr,
                   P {| p := n -m; Hp := Hp |} s*) }}
MALInternal.Paddr.subPaddrIdx addr idx
{{fun (paddrsub : paddr) (s : state) => P s  (*/\ StateLib.Paddr.subPaddrIdx addr idx = Some paddrsub *)
/\ CPaddr (addr - idx) = paddrsub}}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.Paddr.subPaddrIdx.
cbn.
intros.
split.
intuition.
intros.
split. intuition.
intros. split. apply H.
unfold CPaddr.
destruct (le_dec (addr - idx) maxAddr). intuition.
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition.
Qed.

(* DUP *)
Lemma pred (addr : paddr ) P :
{{fun s => P s  /\ addr > 0}} MALInternal.Paddr.pred addr
{{fun (addrpred : paddr) (s : state) => P s  /\ StateLib.Paddr.pred addr = Some addrpred }}.
Proof.
eapply WP.weaken.
eapply WeakestPreconditions.Paddr.pred.
cbn.
intros.
split.
intuition.
intros.
split. intuition.
unfold StateLib.Paddr.pred.
subst.
destruct (gt_dec addr 0).
f_equal.
f_equal.
apply proof_irrelevance.
subst.
intuition.
Qed.

End Paddr.

Lemma check32Aligned (addr : paddr ) P :
{{fun s => P s  /\ addr >= 0}} MAL.check32Aligned addr
{{fun (is32aligned : bool) (s : state) => P s  /\ is32aligned = StateLib.is32Aligned addr }}.
Proof.
eapply WP.weaken.
eapply  WeakestPreconditions.check32Aligned.
cbn.
intros.
split.
intuition.
intros. reflexivity.
Qed.

(* DUP of getDefaultVaddr *)
Lemma getMinBlockSize P :
{{fun s => P s}} MALInternal.getMinBlockSize
{{fun minsize s => P s /\ minsize = Constants.minBlockSize }}.
Proof.
unfold MALInternal.getMinBlockSize.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.

(* DUP *)
Lemma getKernelStructureEntriesNb P :
{{fun s => P s}} MALInternal.getKernelStructureEntriesNb
{{fun entriesnb s => P s /\ entriesnb = (CIndex kernelStructureEntriesNb) }}.
Proof.
unfold MALInternal.getKernelStructureEntriesNb.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.

(* DUP *)
Lemma getMPURegionsNb P :
{{fun s => P s}} MALInternal.getMPURegionsNb
{{fun mpuregionsnb s => P s /\ mpuregionsnb = (CIndex MPURegionsNb) }}.
Proof.
unfold MALInternal.getMPURegionsNb.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.


(* DUP *)
Lemma getKernelStructureTotalLength P :
{{fun s => P s}} MALInternal.getKernelStructureTotalLength
{{fun totallength s => P s /\ totallength = Constants.kernelStructureTotalLength }}.
Proof.
unfold MALInternal.getKernelStructureTotalLength.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.


(* DUP *)
Lemma getPDStructurePointerAddrFromPD (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT paddr s  }} MAL.getPDStructurePointerAddrFromPD paddr
{{ fun (pointerToKS : ADT.paddr) (s : state) => P s /\ pointerToKS = CPaddr (paddr + Constants.kernelstructureidx) }}.
Proof.
unfold MAL.getPDStructurePointerAddrFromPD.
eapply WP.weaken.
eapply WP.ret .
intros.
simpl. intuition.
Qed.

(*
(* DUP *)
Lemma readBlockStartFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockStartFromBlockEntryAddr paddr
{{ fun (start : ADT.paddr) (s : state) => P s /\ bentryStartAddr paddr start s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryStartAddr;trivial.
Qed.


Lemma readBlockEndFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockEndFromBlockEntryAddr paddr
{{ fun (endaddr : ADT.paddr) (s : state) => P s /\ bentryEndAddr paddr endaddr s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryEndAddr;trivial.
Qed.*)

Lemma readBlockStartFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockStartFromBlockEntryAddr paddr
{{ fun (start : ADT.paddr) (s : state) => P s /\ bentryStartAddr paddr start s }}.
Proof.
eapply WP.weaken.
unfold readBlockStartFromBlockEntryAddr.
eapply bindRev.
apply WP.getBlockRecordField.
simpl.
intros.
eapply weaken. apply ret.
intros. simpl. apply H.
intros. simpl.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryStartAddr;trivial.
Qed.


Lemma readBlockEndFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockEndFromBlockEntryAddr paddr
{{ fun (endaddr : ADT.paddr) (s : state) => P s /\ bentryEndAddr paddr endaddr s }}.
Proof.
eapply WP.weaken.
unfold readBlockEndFromBlockEntryAddr.
eapply bindRev.
apply WP.getBlockRecordField.
simpl.
intros.
eapply weaken. apply ret.
intros. simpl. apply H.
intros. simpl.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryEndAddr;trivial.
Qed.


(* DUP *)
Lemma readBlockAccessibleFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockAccessibleFromBlockEntryAddr paddr
{{ fun (isA : bool) (s : state) => P s /\ bentryAFlag paddr isA s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryAccessibleFlag;trivial.
Qed.

Lemma readBlockPresentFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockPresentFromBlockEntryAddr paddr
{{ fun (isP : bool) (s : state) => P s /\ bentryPFlag paddr isP s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryPresentFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockRFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockRFromBlockEntryAddr paddr
{{ fun (isR : bool) (s : state) => P s /\ bentryRFlag paddr isR s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryReadFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockWFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockWFromBlockEntryAddr paddr
{{ fun (isW : bool) (s : state) => P s /\ bentryWFlag paddr isW s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryWriteFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockXFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockXFromBlockEntryAddr paddr
{{ fun (isX : bool) (s : state) => P s /\ bentryXFlag paddr isX s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupBEntryExecFlag;trivial.
Qed.

(* DUP *)
Lemma readBlockIndexFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockIndexFromBlockEntryAddr paddr
{{ fun (idx : index) (s : state) => P s /\ isBE paddr s /\ bentryBlockIndex paddr idx s }}.
Proof.
eapply WP.weaken.
apply WP.getBlockRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
unfold isBE. rewrite Hentry ; trivial.
apply lookupBEntryBlockIndex;trivial.
Qed.

(* DUP *)
Lemma readBlockEntryFromBlockEntryAddr (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isBE paddr s  }} MAL.readBlockEntryFromBlockEntryAddr paddr
{{ fun (be : BlockEntry) (s : state) => P s /\ isBE paddr s /\ entryBE paddr be s }}.
Proof.
eapply WP.weaken.
apply WP.readBlockEntryFromBlockEntryAddr.
simpl.
intros.
destruct H as (H & Hentry).
apply isBELookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
unfold isBE. rewrite Hentry ; trivial.
unfold entryBE. rewrite Hentry;trivial.
Qed.

(* DUP *)
Lemma readPDFirstFreeSlotPointer (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT paddr s  }} MAL.readPDFirstFreeSlotPointer paddr
{{ fun (firstfreeslotaddr : ADT.paddr) (s : state) => P s /\ pdentryFirstFreeSlot paddr firstfreeslotaddr s}}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupPDEntryFirstFreeSlot;trivial.
Qed.

(* DUP *)
Lemma readPDNbFreeSlots (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT paddr s  }} MAL.readPDNbFreeSlots paddr
{{ fun (nbfreeslots : index) (s : state) => P s /\ pdentryNbFreeSlots paddr nbfreeslots s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupPDEntryNbFreeSlots;trivial.
Qed.

(* DUP *)
Lemma readPDStructurePointer (pdpaddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT pdpaddr s  }} MAL.readPDStructurePointer pdpaddr
{{ fun (structurepointer : paddr) (s : state) => P s /\ pdentryStructurePointer pdpaddr structurepointer s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. intuition.
apply lookupPDEntryStructurePointer;trivial.
Qed.

(* DUP *)
Lemma readPDMPU (pdpaddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT pdpaddr s  }} MAL.readPDMPU pdpaddr
{{ fun (MPU : list paddr) (s : state) => P s /\ pdentryMPU pdpaddr MPU s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupPDEntryMPU;trivial.
Qed.

(* DUP *)
Lemma readPDNbPrepare (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT paddr s  }} MAL.readPDNbPrepare paddr
{{ fun (nbprepare : index) (s : state) => P s /\ pdentryNbPrepare paddr nbprepare s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupPDEntryNbPrepare;trivial.
Qed.

(* DUP *)
Lemma readPDVidt (paddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT paddr s  }} MAL.readPDVidt paddr
{{ fun (vidtBlock : ADT.paddr) (s : state) => P s /\ pdentryVidt paddr vidtBlock s }}.
Proof.
eapply WP.weaken.
apply WP.getPDTRecordField.
simpl.
intros.
destruct H as (H & Hentry).
apply isPDTLookupEq in Hentry ;trivial.
destruct Hentry as (entry & Hentry).
exists entry. repeat split;trivial.
apply lookupPDEntryVidt;trivial.
Qed.

(* DUP *)
Lemma readBlockFromPhysicalMPU (pd : paddr) (idx : index) (P : state -> Prop) :
{{ fun s => P s /\ isPDT pd s  }} MAL.readBlockFromPhysicalMPU pd idx
{{ fun (block: paddr) (s : state) => P s /\ pdentryMPUblock pd idx block s }}.
Proof.
unfold readBlockFromPhysicalMPU.
eapply bindRev.
{ (** readPDMPU *)
	eapply weaken. apply readPDMPU.
	intros. simpl. split. apply H. intuition.
}
intro realMPU.
{ (** ret *)
	eapply weaken. apply WeakestPreconditions.ret.
	intros. simpl. intuition.
	unfold pdentryMPUblock. unfold isPDT in *. 	unfold pdentryMPU in *.
	destruct (lookup pd (memory s) beqAddr) ; try (exfalso ; congruence).
	destruct v ; try (exfalso ; congruence).
	subst. reflexivity.
}
Qed.

(* Partial DUP *)
Lemma compareAddrToNull (pa : paddr) (P : state -> Prop):
{{fun s => P s }} compareAddrToNull pa
{{fun (isnull : bool) (s : state) => P s /\
                                       (beqAddr nullAddr pa) = isnull }}.
Proof.
unfold compareAddrToNull.
eapply WP.bindRev.
+ unfold MALInternal.getNullAddr.
  eapply WP.weaken.
  eapply WP.ret . intros.
  instantiate (1:= fun nullPa s => P s /\ beqAddr nullAddr nullPa = true ).
  simpl.
  intuition.
+ intro nullPa. simpl.
  unfold MALInternal.getBeqAddr.
  eapply WP.weaken. eapply WP.ret . intros.
  simpl. intuition.
  unfold beqAddr in *.
	destruct nullAddr, pa.
  simpl in *.
	case_eq p. intros. induction p0. subst. simpl. destruct H1.
	apply PeanoNat.Nat.eqb_sym.
	subst. apply PeanoNat.Nat.eqb_eq in H1.
	rewrite -> H1. trivial.
	intros. apply PeanoNat.Nat.eqb_eq in H1. rewrite <- H1. rewrite ->H. trivial.
Qed.

Lemma getBeqAddr (p1 : paddr)  (p2 : paddr) (P : state -> Prop):
{{fun s => P s }} getBeqAddr p1 p2
{{fun (isequal : bool) (s : state) => P s /\
                                       (beqAddr p1 p2) = isequal }}.
Proof.
	unfold MALInternal.getBeqAddr.
  eapply WP.weaken. eapply WP.ret . intros.
  simpl. intuition.
Qed.

Lemma getBeqIdx (i1 : index)  (i2 : index) (P : state -> Prop):
{{fun s => P s }} getBeqIdx i1 i2
{{fun (isequal : bool) (s : state) => P s /\
                                       (beqIdx i1 i2) = isequal }}.
Proof.
	unfold MALInternal.getBeqIdx.
  eapply WP.weaken. eapply WP.ret . intros.
  simpl. intuition.
Qed.

(* DUP *)
Lemma getMaxNbPrepare P :
{{fun s => P s}} MALInternal.getMaxNbPrepare
{{fun nbprepare s => P s (*/\ entriesnb = (CIndex kernelStructureEntriesNb)*) }}.
Proof.
unfold MALInternal.getMaxNbPrepare.
eapply WP.weaken.
eapply WP.ret.
intros.
simpl. intuition.
Qed.


Lemma compatibleRight (originalright newright : bool) (P : state -> Prop) :
{{fun s => P s}} Internal.compatibleRight originalright newright {{fun iscompatible s => P s}}.
Proof.
unfold Internal.compatibleRight.
case_eq newright.
	- intros.
		eapply WP.weaken.
		eapply WP.ret.
		intros.
 simpl; trivial.
	- intros.
		eapply WP.weaken.
		eapply WP.ret.
		intros.  simpl; trivial.
Qed.

Lemma getBlockEntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (blockidx : index) (P : state -> Prop) :
{{ fun s => P s /\ BlocksRangeFromKernelStartIsBE s
								/\ isKS kernelStartAddr s
								/\ blockidx < kernelStructureEntriesNb}}
MAL.getBlockEntryAddrFromKernelStructureStart kernelStartAddr blockidx
{{ fun (BEAddr : ADT.paddr) (s : state) => P s /\ BEAddr = CPaddr (kernelStartAddr + blkoffset + blockidx)
																						/\ isBE BEAddr s}}.
Proof.
unfold MAL.getBlockEntryAddrFromKernelStructureStart.
eapply weaken. apply ret.
intros. simpl. split. apply H. split. reflexivity.
(* entryaddr is a BE because it's a simple offset from KS start *)
rewrite PeanoNat.Nat.add_0_r.
unfold BlocksRangeFromKernelStartIsBE in *. intuition.
Qed.

Lemma getSh1EntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (blockidx : index) (P : state -> Prop) :
{{ fun s => P s }}
MAL.getSh1EntryAddrFromKernelStructureStart kernelStartAddr blockidx
{{ fun (SHEAddr : ADT.paddr) (s : state) => P s /\ SHEAddr = CPaddr (kernelStartAddr + sh1offset + blockidx) }}.
Proof.
	unfold MAL.getSh1EntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	intuition.
Qed.

Lemma getSCEntryAddrFromKernelStructureStart (kernelStartAddr : paddr) (blockidx : index) (P : state -> Prop) :
{{fun s => P s }}
MAL.getSCEntryAddrFromKernelStructureStart kernelStartAddr blockidx
{{ fun scentryaddr s => P s /\ scentryaddr = CPaddr (kernelStartAddr + scoffset + blockidx)
}}.
Proof.
unfold MAL.getSCEntryAddrFromKernelStructureStart.
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	reflexivity.
Qed.

Lemma getKernelStructureStartAddr  (blockentryaddr : paddr) (blockidx : index)  (P : state -> Prop) :
{{fun s => P s /\ 	KernelStructureStartFromBlockEntryAddrIsKS s
					/\	blockidx < kernelStructureEntriesNb
					/\ blockentryaddr <= maxAddr
					/\	exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)
					/\ bentryBlockIndex blockentryaddr blockidx s
}}

MAL.getKernelStructureStartAddr blockentryaddr blockidx
{{ fun KSstart s => P s
									/\ exists entry, lookup KSstart s.(memory) beqAddr = Some (BE entry)
									/\ KSstart = CPaddr (blockentryaddr - blockidx) (* need for getSCEntryAddrFromblockentryAddr *)}}.
Proof.
unfold MAL.getKernelStructureStartAddr.
eapply bindRev.
{ (** MALInternal.Paddr.subPaddrIdx *)
	eapply weaken. apply Paddr.subPaddrIdx.
	intros. simpl. split. apply H. intuition.
	lia.
}
intro kernelStartAddr. simpl.
{ (** ret *)
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	intuition. unfold KernelStructureStartFromBlockEntryAddrIsKS in *.
	destruct H5. destruct H4.
	assert(HBEs : isBE blockentryaddr s).
	{ unfold isBE. rewrite H4. trivial. }
	specialize(H0 blockentryaddr blockidx HBEs H5).
	replace kernelStartAddr with (CPaddr (blockentryaddr - blockidx)).
	apply KSIsBE in H0.
	apply isBELookupEq in H0. destruct H0. exists x0.
	intuition.
}
Qed.

Lemma getSh1EntryAddrFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop) :
{{fun s => Q s /\  wellFormedFstShadowIfBlockEntry s
					  	 /\ KernelStructureStartFromBlockEntryAddrIsKS s
							 /\ BlocksRangeFromKernelStartIsBE s
							 /\ nullAddrExists s
							 /\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.getSh1EntryAddrFromBlockEntryAddr blockentryaddr
{{ fun sh1entryaddr s => Q s /\ exists sh1entry : Sh1Entry,
lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
/\ sh1entryAddr blockentryaddr sh1entryaddr s}}.
Proof.
unfold MAL.getSh1EntryAddrFromBlockEntryAddr.
eapply bindRev.
{ (** MAL.readBlockIndexFromBlockEntryAddr *)
	eapply weaken. apply readBlockIndexFromBlockEntryAddr.
	intros. simpl. split. apply H.
	unfold isBE. intuition. destruct H5. rewrite H4; trivial.
}
intro BlockEntryIndex.
eapply bindRev.
{ (** getKernelStructureStartAddr *)
	eapply weaken. apply getKernelStructureStartAddr.
	intros. simpl. split. exact H.
	intuition.
	unfold bentryBlockIndex in *.
	destruct H7. rewrite H6 in *. subst BlockEntryIndex. apply Hidx.
	destruct blockentryaddr. simpl. trivial.
	destruct H7. exists x. intuition.
}
intro kernelStartAddr.
eapply bindRev.
{ (** MAL.getSh1EntryAddrFromKernelStructureStart *)
	eapply weaken. apply getSh1EntryAddrFromKernelStructureStart.
	intros. simpl. exact H.
}
(* Proof : kernelStartAddr + blockindex is BE, so +sh1offset is SHE *)
intro SHEAddr.
{ (** ret *)
	eapply weaken. apply ret.
	intros. simpl. split. apply H.
	intuition.
	assert(HwellFormedFstShadowIfBlockEntrys' : wellFormedFstShadowIfBlockEntry s)
		by assumption.
	unfold wellFormedFstShadowIfBlockEntry in *.
	assert(HKS : exists entry : BlockEntry,
       lookup kernelStartAddr (memory s) beqAddr = Some (BE entry) /\
       kernelStartAddr = CPaddr (blockentryaddr - BlockEntryIndex)) by trivial.
	destruct HKS as [ksentry (HKSEq & Hlookupks)].
	subst kernelStartAddr. unfold sh1entryAddr.
	assert(Hblock : exists entry : BlockEntry,
       lookup blockentryaddr (memory s) beqAddr = Some (BE entry)) by trivial.
	destruct Hblock as [blockentry Hlookupblocks]. rewrite Hlookupblocks.

	assert(HKSStartFromBlockEntryAddrIsKS : KernelStructureStartFromBlockEntryAddrIsKS s)
		by intuition.
	unfold KernelStructureStartFromBlockEntryAddrIsKS in *.
	assert(HBE : isBE blockentryaddr s) by trivial.
	assert(Hbentryidx : bentryBlockIndex blockentryaddr BlockEntryIndex s) by trivial.
	specialize (HKSStartFromBlockEntryAddrIsKS blockentryaddr BlockEntryIndex
																						HBE Hbentryidx).
	assert(HBlocksRangeFromKernelStartIsBEs : BlocksRangeFromKernelStartIsBE s)
		by trivial.
	unfold BlocksRangeFromKernelStartIsBE in *.
	assert(Hlt : BlockEntryIndex < kernelStructureEntriesNb)
		by (unfold bentryBlockIndex in * ; rewrite Hlookupblocks in * ;
					subst BlockEntryIndex ; eapply Hidx).
	specialize (HBlocksRangeFromKernelStartIsBEs (CPaddr (blockentryaddr - BlockEntryIndex))
																								BlockEntryIndex
																								HKSStartFromBlockEntryAddrIsKS
																								Hlt).
	specialize (HwellFormedFstShadowIfBlockEntrys' (CPaddr (CPaddr (blockentryaddr - BlockEntryIndex) + BlockEntryIndex))
								HBlocksRangeFromKernelStartIsBEs).
	assert(HSHEAddrEq : SHEAddr =
     CPaddr
       (CPaddr (blockentryaddr - BlockEntryIndex) + sh1offset + BlockEntryIndex))
			by trivial.
	unfold CPaddr in HKSEq. unfold CPaddr at 2 in HSHEAddrEq.
	unfold CPaddr at 3 in HwellFormedFstShadowIfBlockEntrys'.

	unfold CPaddr at 2 in HBlocksRangeFromKernelStartIsBEs.
	destruct (le_dec (blockentryaddr - BlockEntryIndex) maxAddr) ; intuition.
	- simpl in *.
		unfold CPaddr at 2 in HwellFormedFstShadowIfBlockEntrys'.
		unfold CPaddr in HBlocksRangeFromKernelStartIsBEs.
		destruct (le_dec (blockentryaddr - BlockEntryIndex + BlockEntryIndex) maxAddr) ; intuition.
		-- simpl in *.
			apply isSHELookupEq in  HwellFormedFstShadowIfBlockEntrys'.
			destruct HwellFormedFstShadowIfBlockEntrys' as [sh1entry Hsh1entry].
			exists sh1entry. subst SHEAddr. 
			assert(HEq : blockentryaddr - BlockEntryIndex + sh1offset + BlockEntryIndex =
										blockentryaddr - BlockEntryIndex + BlockEntryIndex + sh1offset).
			{ rewrite PeanoNat.Nat.add_shuffle0. reflexivity. }
			rewrite HEq in *. rewrite HSHEAddrEq in *. intuition.
			assert(HEq' : blockentryaddr - BlockEntryIndex + BlockEntryIndex + sh1offset = 
									blockentryaddr + sh1offset).
			{
				rewrite PeanoNat.Nat.sub_add. reflexivity.
				assert(blockentryaddr - BlockEntryIndex <= maxAddr) by lia.
				unfold isBE in *.
				destruct (blockentryaddr - BlockEntryIndex) eqn:diff ; intuition.
				- (* False cause BE NULL *)
					unfold nullAddrExists in *. unfold isPADDR in *.
					unfold nullAddr in *.
					unfold CPaddr in *.
					destruct (le_dec 0 maxAddr) ; intuition.
					assert(HpEq : ADT.CPaddr_obligation_1 0 l1 = ADT.CPaddr_obligation_1 0 l)
						by apply proof_irrelevance.
					rewrite HpEq in *.
					destruct (lookup {| p := 0; Hp := ADT.CPaddr_obligation_1 0 l |} (memory s) beqAddr) ;
						try (exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
				- lia.
			}
			rewrite HEq'. reflexivity.
			-- (* False cause BE NULL *)
					unfold isBE in *.
					(* DUP *)
					unfold nullAddrExists in *. unfold isPADDR in *.
					unfold nullAddr in *.
					unfold CPaddr in *.
					destruct (le_dec 0 maxAddr) ; intuition.
					assert(HpEq : ADT.CPaddr_obligation_1 0 l0 = ADT.CPaddr_obligation_2)
						by apply proof_irrelevance.
					rewrite HpEq in *.
					destruct (lookup {| p := 0; Hp := ADT.CPaddr_obligation_2|} (memory s) beqAddr) ;
						try (exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
	- (* False cause BE Null *)
		unfold isBE in *.
		(* DUP *)
		unfold nullAddrExists in *. unfold isPADDR in *.
		unfold nullAddr in *.
		unfold CPaddr in *.
		destruct (le_dec 0 maxAddr) ; intuition.
		assert(HpEq : ADT.CPaddr_obligation_1 0 l = ADT.CPaddr_obligation_2)
			by apply proof_irrelevance.
		rewrite HpEq in *.
		destruct (lookup {| p := 0; Hp := ADT.CPaddr_obligation_2|} (memory s) beqAddr) ;
			try (exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
}
Qed.

(* DUP *)
Lemma getNextAddrFromKernelStructureStart  (kernelStartAddr : paddr) (P : state -> Prop) :
{{fun s => P s (*/\ wellFormedNextKSAddrIfKernelStructureStart s *)
					/\ exists entry, lookup kernelStartAddr s.(memory) beqAddr = Some (BE entry)}}
MAL.getNextAddrFromKernelStructureStart kernelStartAddr
{{ fun nextaddr s => P s /\ nextaddr = CPaddr (kernelStartAddr + nextoffset) (*/\ exists entry, lookup nextaddr s.(memory) beqAddr = Some (PADDR entry)
/\ nextKSAddr nextksaddr nextksaddr s
/\ nextksaddr = CPaddr (kernelStartAddr + nextoffset)*)}}.
Proof.
unfold MAL.getNextAddrFromKernelStructureStart.
eapply weaken. apply ret.
intros. simpl. intuition.
Qed.

Lemma readSh1PDChildFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  :
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSh1PDChildFromBlockEntryAddr blockentryaddr
{{fun pdchild s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryPDchild sh1entryaddr pdchild s
										/\ sh1entryAddr blockentryaddr sh1entryaddr s}}.
Proof.
unfold MAL.readSh1PDChildFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. split. apply H. split. apply H. intuition.
+	intro sh1entryaddr. simpl.
	eapply bind.
	intros. apply ret.
	eapply weaken. apply getSh1RecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	split. apply lookupSh1EntryPDchild. apply H0.
	intuition.
Qed.

(* DUP *)
Lemma readSh1PDFlagFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  :
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSh1PDFlagFromBlockEntryAddr blockentryaddr
{{fun pdflag s => Q s
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryPDflag sh1entryaddr pdflag s
										/\ sh1entryAddr blockentryaddr sh1entryaddr s }}.
Proof.
unfold MAL.readSh1PDFlagFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. split. apply H. split. apply H. intuition.
+	intro sh1entryaddr. simpl.
	eapply bind.
	intros. apply ret.
	eapply weaken. apply getSh1RecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	split. apply lookupSh1EntryPDflag. apply H0.
	intuition.
Qed.

(* DUP with deeper changes because of lookupSh1EntryInChildLocation *)
Lemma readSh1InChildLocationFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  :
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSh1InChildLocationFromBlockEntryAddr blockentryaddr
{{fun inchildlocation s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists sh1entry : Sh1Entry, exists sh1entryaddr : paddr, lookup sh1entryaddr s.(memory) beqAddr = Some (SHE sh1entry)
										/\ sh1entryInChildLocation sh1entryaddr inchildlocation s}}.
Proof.
unfold readSh1InChildLocationFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. unfold consistency in H. unfold consistency1 in H.
	intuition.
+	intro sh1entryaddr. simpl.
	eapply bind.
	intros. apply ret.
	eapply weaken. apply getSh1RecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists sh1entryaddr. split. apply H0.
	apply lookupSh1EntryInChildLocation. apply H0. intuition.
Qed.


Lemma getSCEntryAddrFromBlockEntryAddr  (blockentryaddr : paddr) (P : state -> Prop) :
{{fun s => P s /\ wellFormedShadowCutIfBlockEntry s
							/\ KernelStructureStartFromBlockEntryAddrIsKS s
							/\ BlocksRangeFromKernelStartIsBE s
							/\ nullAddrExists s
					/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)
							 }}
MAL.getSCEntryAddrFromBlockEntryAddr blockentryaddr
{{ fun scentryaddr s => P s /\ exists entry, lookup scentryaddr s.(memory) beqAddr = Some (SCE entry)
																/\ scentryAddr blockentryaddr scentryaddr s
}}.
Proof.
unfold MAL.getSCEntryAddrFromBlockEntryAddr.
eapply bindRev.
{ eapply weaken.
- apply readBlockIndexFromBlockEntryAddr.
- intros. cbn. split. exact H. (* NOTE : Important to propagate the whole property *)
	unfold isBE. destruct H. destruct H0. destruct H1. destruct H2.
	destruct H3. destruct H4. rewrite H4. trivial.
}
intro BlockEntryIndex.
eapply bindRev.
{ (* getKernelStructureStartAddr *)
	eapply weaken. apply getKernelStructureStartAddr.
	intros. simpl. split. exact H. intuition.
	unfold bentryBlockIndex in *. destruct H7. rewrite H6 in *.
	subst BlockEntryIndex. apply Hidx.
	destruct blockentryaddr. simpl. trivial. (* already done in sh1entry *)
	apply isBELookupEq in H0.
	destruct H0. exists x. intuition.
}
intro kernelStartAddr. simpl.
eapply bindRev.
{ (* getSCEntryAddrFromKernelStructureStart *)
	eapply weaken.  apply getSCEntryAddrFromKernelStructureStart.
	intros. simpl. apply H.
}
intro SCEAddr.
{ (** ret *)
	eapply weaken. apply ret.
	intros. simpl.
	split. apply H.
	intuition.
	rewrite H1.
	assert(HKS : exists entry : BlockEntry,
       lookup kernelStartAddr (memory s) beqAddr = Some (BE entry) /\
       kernelStartAddr = CPaddr (blockentryaddr - BlockEntryIndex)) by trivial.
	destruct HKS as [ksentry (HKSEq & Hlookupks)].
	subst kernelStartAddr. unfold scentryAddr.

	assert(HwellFormedShadowCutIfBlockEntry : wellFormedShadowCutIfBlockEntry s)
		by assumption.
	unfold wellFormedFstShadowIfBlockEntry in *.

	assert(Hblock : exists entry : BlockEntry,
       lookup blockentryaddr (memory s) beqAddr = Some (BE entry)) by trivial.
	destruct Hblock as [blockentry Hlookupblocks]. rewrite Hlookupblocks.

	assert(HKSStartFromBlockEntryAddrIsKS : KernelStructureStartFromBlockEntryAddrIsKS s)
		by intuition.
	unfold KernelStructureStartFromBlockEntryAddrIsKS in *.
	assert(HBE : isBE blockentryaddr s) by trivial.
	assert(Hbentryidx : bentryBlockIndex blockentryaddr BlockEntryIndex s) by trivial.
	specialize (HKSStartFromBlockEntryAddrIsKS blockentryaddr BlockEntryIndex
																						HBE Hbentryidx).
	assert(HBlocksRangeFromKernelStartIsBEs : BlocksRangeFromKernelStartIsBE s)
		by trivial.
	unfold BlocksRangeFromKernelStartIsBE in *.
	assert(Hlt : BlockEntryIndex < kernelStructureEntriesNb)
		by (unfold bentryBlockIndex in * ; rewrite Hlookupblocks in * ;
					subst BlockEntryIndex ; eapply Hidx).
	specialize (HBlocksRangeFromKernelStartIsBEs (CPaddr (blockentryaddr - BlockEntryIndex))
																								BlockEntryIndex
																								HKSStartFromBlockEntryAddrIsKS
																								Hlt).
	specialize (HwellFormedShadowCutIfBlockEntry (CPaddr (CPaddr (blockentryaddr - BlockEntryIndex) + BlockEntryIndex))
								HBlocksRangeFromKernelStartIsBEs).
	assert(HSCEAddrEq : SCEAddr =
     CPaddr
       (CPaddr (blockentryaddr - BlockEntryIndex) + scoffset + BlockEntryIndex))
			by trivial.
	unfold CPaddr in HKSEq. unfold CPaddr at 2 in HSCEAddrEq.
	unfold CPaddr at 3 in HwellFormedShadowCutIfBlockEntry.

	unfold CPaddr at 2 in HBlocksRangeFromKernelStartIsBEs.
	destruct (le_dec (blockentryaddr - BlockEntryIndex) maxAddr) ; intuition.
	- simpl in *.
		unfold CPaddr at 2 in HwellFormedShadowCutIfBlockEntry.
		unfold CPaddr in HBlocksRangeFromKernelStartIsBEs.
		destruct (le_dec (blockentryaddr - BlockEntryIndex + BlockEntryIndex) maxAddr) ; intuition.
		-- simpl in *.
			destruct HwellFormedShadowCutIfBlockEntry as [scentryaddr (HSCE & HaddrEq) ].
			apply isSCELookupEq in HSCE. destruct HSCE as [scentry Hscentry].
			exists scentry. subst SCEAddr. subst scentryaddr.
			assert(HEq : blockentryaddr - BlockEntryIndex + scoffset + BlockEntryIndex =
										blockentryaddr - BlockEntryIndex + BlockEntryIndex + scoffset).
			{ rewrite PeanoNat.Nat.add_shuffle0. reflexivity. }
			rewrite HEq in *. rewrite HSCEAddrEq in *. intuition.
			assert(HEq' : blockentryaddr - BlockEntryIndex + BlockEntryIndex + scoffset = 
									blockentryaddr + scoffset).
			{
				rewrite PeanoNat.Nat.sub_add. reflexivity.
				assert(blockentryaddr - BlockEntryIndex <= maxAddr) by lia.
				unfold isBE in *.
				destruct (blockentryaddr - BlockEntryIndex) eqn:diff ; intuition.
				- (* False cause BE NULL *)
					unfold nullAddrExists in *. unfold isPADDR in *.
					unfold nullAddr in *.
					unfold CPaddr in *.
					destruct (le_dec 0 maxAddr) ; intuition.
					assert(HpEq : ADT.CPaddr_obligation_1 0 l1 = ADT.CPaddr_obligation_1 0 l)
						by apply proof_irrelevance.
					rewrite HpEq in *.
					destruct (lookup {| p := 0; Hp := ADT.CPaddr_obligation_1 0 l |} (memory s) beqAddr) ;
						try (exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
				- lia.
			}
			rewrite HEq'. reflexivity.
			-- (* False cause BE NULL *)
					unfold isBE in *.
					(* DUP *)
					unfold nullAddrExists in *. unfold isPADDR in *.
					unfold nullAddr in *.
					unfold CPaddr in *.
					destruct (le_dec 0 maxAddr) ; intuition.
					assert(HpEq : ADT.CPaddr_obligation_1 0 l0 = ADT.CPaddr_obligation_2)
						by apply proof_irrelevance.
					rewrite HpEq in *.
					destruct (lookup {| p := 0; Hp := ADT.CPaddr_obligation_2|} (memory s) beqAddr) ;
						try (exfalso ; congruence).
					destruct v ; try(exfalso ; congruence).
	- (* False cause BE Null *)
		unfold isBE in *.
		(* DUP *)
		unfold nullAddrExists in *. unfold isPADDR in *.
		unfold nullAddr in *.
		unfold CPaddr in *.
		destruct (le_dec 0 maxAddr) ; intuition.
		assert(HpEq : ADT.CPaddr_obligation_1 0 l = ADT.CPaddr_obligation_2)
			by apply proof_irrelevance.
		rewrite HpEq in *.
		destruct (lookup {| p := 0; Hp := ADT.CPaddr_obligation_2|} (memory s) beqAddr) ;
			try (exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
}
Qed.

(* DUP *)
Lemma readSCOriginFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  :
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSCOriginFromBlockEntryAddr blockentryaddr
{{fun origin s => Q s (*/\ consistency s*) (*/\ exists entry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)*)
										/\ exists scentry : SCEntry, exists scentryaddr : paddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry)
										/\ scentryOrigin scentryaddr origin s}}.
Proof.
unfold MAL.readSCOriginFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. split. apply H. split. apply H. intuition.
+	intro scentryaddr. simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply getSCRecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists scentryaddr. split. apply H0.
	apply lookupSCEntryOrigin. apply H0.
Qed.

(* DUP with changes in scentryNext + lookupSCEntryNext + changes of function names*)
Lemma readSCNextFromBlockEntryAddr  (blockentryaddr : paddr) (Q : state -> Prop)  :
{{fun s  =>  Q s /\ consistency s /\ exists entry : BlockEntry, lookup blockentryaddr s.(memory) beqAddr = Some (BE entry)}}
MAL.readSCNextFromBlockEntryAddr blockentryaddr
{{fun next s => Q s
										/\ exists scentry : SCEntry, exists scentryaddr : paddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE scentry)
										/\ scentryNext scentryaddr next s}}.
Proof.
unfold MAL.readSCNextFromBlockEntryAddr.
eapply WP.bindRev.
+   eapply WP.weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. unfold consistency in H. split. apply H. split. apply H.
	split. apply H. split. apply H. split. apply H. intuition.
+	intro scentryaddr. simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply getSCRecordField.
	intros. simpl. destruct H. destruct H0. exists x.
	split. intuition. split. apply H.
	exists x. exists scentryaddr. split. apply H0.
	apply lookupSCEntryNext. apply H0.
Qed.

Lemma readNextFromKernelStructureStart (structurepaddr : paddr) (P : state -> Prop)  :
{{fun s  =>  P s /\ NextKSOffsetIsPADDR s /\
						isKS structurepaddr s
             }}
MAL.readNextFromKernelStructureStart structurepaddr
{{fun nextkernelstructure s => P s
																/\ exists offset, (offset = CPaddr (structurepaddr + nextoffset)
																/\ nextKSAddr structurepaddr offset s)
																/\ nextKSentry offset nextkernelstructure s}}.
Proof.
unfold MAL.readNextFromKernelStructureStart.
eapply WP.bindRev.
+   eapply WP.weaken. apply getNextAddrFromKernelStructureStart.
	intros. simpl. split. apply H. intuition. apply isKSLookupEq in H2.
	destruct H2. exists x. intuition.
+ intro nextaddr.
	simpl. eapply bind.
	intros. apply ret.
	eapply weaken. apply WP.readNextFromKernelStructureStart2.
	intros. simpl. intuition. subst.
	unfold NextKSOffsetIsPADDR in H0.
	specialize (H0 structurepaddr (CPaddr (structurepaddr + nextoffset)) H3).
	unfold isKS in *. unfold nextKSAddr in H0.
	destruct(lookup structurepaddr (memory s) beqAddr) eqn:Hlookup ; intuition.
	destruct v eqn:Hv ; intuition.
	apply isPADDRLookupEq in H1. destruct H1.
	exists x. intuition.
	exists (CPaddr (structurepaddr + nextoffset)). intuition.
	unfold nextKSAddr. rewrite Hlookup ; trivial.
	unfold nextKSentry. subst. rewrite H0 ; trivial.
Qed.

Lemma checkRights p r w e P :
{{ fun s => P s /\ exists entry, lookup p s.(memory) beqAddr = Some (BE entry)}}
Internal.checkRights  p r w e
{{ fun rights s => P s /\ exists entry, lookup p s.(memory) beqAddr = Some (BE entry)  }}.
Proof.
unfold checkRights.
case_eq r.
2: {intros. simpl.
	eapply WP.weaken.
eapply WP.ret.
simpl; trivial. (* intuition.*)
}
 intros. simpl.
	eapply WP.bindRev.
{
	eapply WP.weaken.
	eapply readBlockXFromBlockEntryAddr.
	intuition. apply H1.

unfold isBE.
	destruct H2. destruct (lookup p (memory s) beqAddr). destruct v.
	trivial. repeat congruence. congruence. congruence. congruence. congruence.
}
	intro xoriginal.
 	eapply WP.bindRev.
{
		eapply WP.weaken.
	eapply readBlockWFromBlockEntryAddr.
	intuition. apply H1.

	unfold bentryXFlag in H2.

unfold isBE;
destruct (lookup p (memory s) beqAddr). destruct v.
destruct xoriginal.  destruct exec. try repeat trivial. repeat trivial. trivial. trivial. trivial.
trivial. trivial. trivial.
}
	intro woriginal.
 	eapply WP.bindRev.
{ case_eq e.
	intros.
	intros;	apply compatibleRight.
	intros; apply compatibleRight.
}
	intro isCompatibleWithX.
 	eapply WP.bindRev.
{ case_eq w.
	intros;	apply compatibleRight.
	intros; apply compatibleRight.
}
	intro isCompatibleWithW.
	simpl in *.
	destruct (isCompatibleWithX && isCompatibleWithW).
- (* Dup *)
	simpl.
	eapply WP.weaken.
	eapply WP.ret.
	intuition.
	unfold bentryWFlag in H2.
	destruct (lookup p (memory s) beqAddr) eqn:lookup.
	destruct v eqn:V.
	exists b. reflexivity. intuition. intuition. intuition. intuition. intuition.
- simpl.
	eapply WP.weaken.
	eapply WP.ret.
	intuition.
	unfold bentryWFlag in H2.
	destruct (lookup p (memory s) beqAddr) eqn:lookup.
	destruct v eqn:V.
	exists b. reflexivity. intuition. intuition. intuition. intuition. intuition.
Qed.

Lemma writeSh1PDChildFromBlockEntryAddr (blockentryaddr pdchild : paddr)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup (CPaddr (blockentryaddr + sh1offset)) s.(memory) beqAddr = Some (SHE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add (CPaddr (blockentryaddr + sh1offset))
              (SHE {|	PDchild := pdchild;
											PDflag := entry.(PDflag);
											inChildLocation := entry.(inChildLocation) |})
              (memory s) beqAddr |}
/\ isBE blockentryaddr s
/\ wellFormedFstShadowIfBlockEntry s
/\ KernelStructureStartFromBlockEntryAddrIsKS s
/\ BlocksRangeFromKernelStartIsBE s
/\ nullAddrExists s
 }}
MAL.writeSh1PDChildFromBlockEntryAddr blockentryaddr pdchild  {{P}}.
Proof.
eapply bindRev.
{ eapply weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. destruct H. intuition.
 apply isBELookupEq in H1 ;trivial.
}
	intro Sh1EAddr.
{ cbn. eapply weaken. eapply WP.writeSh1PDChildFromBlockEntryAddr2.	cbn.
	intros. simpl. destruct H. destruct H.
	intuition.
	unfold sh1entryAddr in *.
	apply isBELookupEq in H2. destruct H2.
	rewrite H2 in H0.
	destruct H0. destruct H0.
	subst. exists x. split.
	assumption. assumption.
}
Qed.


(* DUP*)
Lemma writeSh1InChildLocationFromBlockEntryAddr (blockentryaddr newinchildlocation : paddr)  (P : unit -> state -> Prop) :
{{fun  s => exists entry , lookup (CPaddr (blockentryaddr + sh1offset)) s.(memory) beqAddr = Some (SHE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add (CPaddr (blockentryaddr + sh1offset))
              (SHE {|	PDchild := entry.(PDchild);
											PDflag := entry.(PDflag);
											inChildLocation := newinchildlocation |})
              (memory s) beqAddr |}
/\ isBE blockentryaddr s
/\ wellFormedFstShadowIfBlockEntry s
/\ KernelStructureStartFromBlockEntryAddrIsKS s
/\ BlocksRangeFromKernelStartIsBE s
/\ nullAddrExists s
 }}
MAL.writeSh1InChildLocationFromBlockEntryAddr blockentryaddr newinchildlocation  {{P}}.
Proof.
eapply bindRev.
{ eapply weaken. apply getSh1EntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. destruct H. intuition.
 apply isBELookupEq in H1 ;trivial.
}
	intro Sh1EAddr.
{ cbn. eapply weaken. eapply WP.writeSh1InChildLocationFromBlockEntryAddr2.	cbn.
	intros. simpl. destruct H. destruct H.
	intuition.
	unfold sh1entryAddr in *.
	apply isBELookupEq in H2. destruct H2.
	rewrite H2 in H0.
	destruct H0. destruct H0.
	subst. exists x. split.
	assumption. assumption.
}
Qed.

Lemma writeSCOriginFromBlockEntryAddr  (entryaddr : paddr) (neworigin : ADT.paddr)  (P : unit -> state -> Prop) :
{{fun  s => (*exists blockentry , lookup entryaddr s.(memory) beqAddr = Some (BE blockentry) /\*)
						isBE entryaddr s
						/\ wellFormedShadowCutIfBlockEntry s
						/\ KernelStructureStartFromBlockEntryAddrIsKS s
						/\ BlocksRangeFromKernelStartIsBE s
						/\ nullAddrExists s
						(*exists entry , exists scentryaddr, lookup scentryaddr s.(memory) beqAddr = Some (SCE entry) /\ *)
/\ exists entry , lookup (CPaddr (entryaddr + scoffset)) s.(memory) beqAddr = Some (SCE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add (CPaddr (entryaddr + scoffset))
              (SCE {| origin := neworigin ; next := entry.(next) |})
              (memory s) beqAddr |} }}
writeSCOriginFromBlockEntryAddr entryaddr neworigin  {{P}}.
Proof.
unfold MAL.writeSCOriginFromBlockEntryAddr.
eapply bindRev.
{ eapply weaken. apply getSCEntryAddrFromBlockEntryAddr.
	intros. simpl. split. apply H. intuition.
 apply isBELookupEq in H0 ;trivial.
}
	intro SCEAddr.
{ cbn. eapply weaken. eapply WP.writeSCOriginFromBlockEntryAddr2.
	cbn.
	intros. simpl. destruct H.
	intuition.
	unfold scentryAddr in H0.
	apply isBELookupEq in H1. destruct H1.
	rewrite H1 in H0.
	destruct H0. destruct H0.
	subst.
	assumption.
}
Qed.

Lemma checkEntry  (kernelstructurestart blockentryaddr : paddr) (P :  state -> Prop) :
{{fun s => P s }}
MAL.checkEntry kernelstructurestart blockentryaddr
{{fun isValidentry s => P s /\ (isValidentry = true -> isBE blockentryaddr s)}}.
Proof.
eapply weaken. apply WeakestPreconditions.checkEntry.
intros.  simpl. intuition.
unfold entryExists in *. unfold isBE.
destruct (lookup blockentryaddr (memory s) beqAddr) eqn:Hlookup.
destruct v eqn:Hv ; trivial ; intuition. intuition.
Qed.

Lemma checkBlockInRAM  (blockentryaddr : paddr) (P :  state -> Prop) :
{{fun s => P s /\ isBE blockentryaddr s}}
MAL.checkBlockInRAM blockentryaddr
{{fun isblockinram s => P s /\ isBlockInRAM blockentryaddr isblockinram s}}.
Proof.
eapply weaken. apply checkBlockInRAM.
intros.  simpl. intuition.
apply isBELookupEq in H1. destruct H1. exists x. intuition.
unfold isBlockInRAM in *. rewrite H.
unfold blockInRAM in *. rewrite H.
reflexivity.
Qed.

Lemma writePDFirstFreeSlotPointer (pdtablepaddr firstfreeslotpaddr : paddr) (P : unit -> state -> Prop) :
{{fun s =>
exists entry , lookup pdtablepaddr s.(memory) beqAddr = Some (PDT entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add pdtablepaddr
              (PDT {| structure := entry.(structure);
											firstfreeslot := firstfreeslotpaddr;
											nbfreeslots := entry.(nbfreeslots);
                     	nbprepare := entry.(nbprepare);
											parent := entry.(parent);
											MPU := entry.(MPU) ; vidtBlock := entry.(vidtBlock) |})
              (memory s) beqAddr |} }}
MAL.writePDFirstFreeSlotPointer pdtablepaddr firstfreeslotpaddr {{P}}.
Proof.
eapply WP.writePDFirstFreeSlotPointer.
Qed.

Lemma writePDNbFreeSlots (pdtablepaddr : paddr) (nbfreeslots : index) (P : unit -> state -> Prop) :
{{fun s =>
exists entry , lookup pdtablepaddr s.(memory) beqAddr = Some (PDT entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add pdtablepaddr
              (PDT {| structure := entry.(structure);
											firstfreeslot := entry.(firstfreeslot);
											nbfreeslots := nbfreeslots;
                    	nbprepare := entry.(nbprepare);
											parent := entry.(parent);
											MPU := entry.(MPU) ; vidtBlock := entry.(vidtBlock) |})
              (memory s) beqAddr |}
}}
MAL.writePDNbFreeSlots pdtablepaddr nbfreeslots
{{ P }}.
Proof.
eapply WP.writePDNbFreeSlots.
Qed.

Lemma writeBlockStartFromBlockEntryAddr (entryaddr newstartaddr : paddr) (P : unit -> state -> Prop)  :
{{fun s => 
exists entry , lookup entryaddr s.(memory) beqAddr = Some (BE entry) /\
P tt {|
  currentPartition := currentPartition s;
  memory := add entryaddr
								(BE (CBlockEntry 	entry.(read) entry.(write) entry.(exec)
																	entry.(present) entry.(accessible)
																	entry.(blockindex) (CBlock newstartaddr entry.(blockrange).(endAddr))))
              (memory s) beqAddr |}
}}
MAL.writeBlockStartFromBlockEntryAddr entryaddr newstartaddr
{{P}}.
Proof.
eapply WP.writeBlockStartFromBlockEntryAddr.
Qed.