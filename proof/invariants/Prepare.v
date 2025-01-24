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

(** * Summary
    This file contains the invariant of [prepare].
    We prove that this PIP service preserves the isolation property *)
Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas.
Require Import Proof.invariants.Invariants getGlobalIdPDCurrentOrChild sizeOfBlock.
Require Import Compare_dec Bool List.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Module WP := WeakestPreconditions.

Lemma prepare (idPD : paddr)
							(idRequisitionedBlock : paddr) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.prepare idPD idRequisitionedBlock
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold Services.prepare.
eapply bindRev.
{ (** getCurPartition **)
	eapply weaken. apply getCurPartition.
	intros. simpl. apply H.
}
intro currentPart. eapply bindRev.
{ (** Internal.getGlobalIdPDCurrentOrChild **)
	eapply weaken. apply getGlobalIdPDCurrentOrChild.
	intros. simpl. split. apply H. intuition.
	subst currentPart.
	apply currentPartIsPDT ;
	unfold consistency in * ; unfold consistency1 in * ;
	intuition.
}
intro globalIdPD.
eapply bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H.
}
intro addrIsNull.
case_eq addrIsNull.
{ (* case_eq addrIsNull = true *)
  intros.
  { (** ret *)
  eapply weaken. apply WP.ret.
  simpl. intros. intuition.
  }
}
(* case_eq addrIsNull = false *)
intros HaddrNull.
eapply bindRev.
{ (** MAL.readPDNbPrepare *)
  eapply weaken. apply readPDNbPrepare.
  intros s Hprops. simpl. split. apply Hprops. intuition.
  apply H4. intros. apply beqAddrFalse in H0. congruence.
}
intro nbPrepare.
eapply bindRev.
{ (** MALInternal.getMaxNbPrepare *)
  eapply weaken. apply Invariants.getMaxNbPrepare.
  intros s Hprops. simpl. apply Hprops.
}
intro maxnbprepare.
eapply bindRev.
{ (** leb *)
  eapply weaken. apply Invariants.Index.leb.
  intros s Hprops. simpl. apply Hprops.
}
intro isMaxPrepare.
case_eq isMaxPrepare.
{ (* case_eq isMaxPrepare = true*)
  intros.
  { (** ret *)
    intros. eapply WP.weaken. apply WP.ret.
    intros. simpl. intuition.
  }
}
(* case_eq isMaxPrepare = false *)
intros HmaxPrepare.
eapply bindRev.
{ (** getKernelStructureEntriesNb *)
  eapply weaken. apply Invariants.getKernelStructureEntriesNb.
  intros s Hprops. simpl. apply Hprops.
}
intro kernelentriesnb.
eapply bindRev.
{ (** Internal.findBlockInKSWithAddr *)
  eapply weaken. apply findBlockInKSWithAddr.findBlockInKSWithAddr.
  intros s Hprops. simpl. split. apply Hprops. intuition. subst currentPart.
  apply currentPartIsPDT ;
  unfold consistency in * ; unfold consistency1 in * ;
  intuition.
}
intro requisitionedBlockInCurrPartAddr.
eapply bindRev.
{ (** compareAddrToNull **)
  eapply weaken. apply Invariants.compareAddrToNull.
  intros s Hprops. simpl. apply Hprops.
}
intro addrIsNull0.
case_eq addrIsNull0.
{ (* case_eq addrIsNull0 = true *)
  intros.
  { (** ret *)
    eapply weaken. apply WP.ret.
    simpl. intros. intuition.
  }
}
(* case_eq addrIsNull0 = false *)
intros Haddr0Null.
eapply bindRev.
{ (** MAL.checkBlockInRAM **)
  eapply weaken. apply Invariants.checkBlockInRAM.
  intros s Hprops. simpl.
  destruct Hprops as ((Hprops & Hconsist & HpropsOr) & HbeqNullReq). rewrite <-beqAddrFalse in HbeqNullReq.
  destruct HpropsOr as [Hcontra | [bentry (HlookupReq & HreqProps)]]; try(exfalso; congruence).
  split. instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ consistency s /\ currentPart = currentPartition s
    /\ isPDT globalIdPD s
    /\ beqAddr nullAddr globalIdPD = false
    /\ pdentryNbPrepare globalIdPD nbPrepare s
    /\ false = StateLib.Index.leb maxnbprepare nbPrepare
    /\ kernelentriesnb = CIndex kernelStructureEntriesNb
    /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
    /\ bentryPFlag requisitionedBlockInCurrPartAddr true s
    /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s)
    /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
    /\ exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry)).
  rewrite beqAddrFalse in *. intuition.
  - assert(Hres: beqAddr globalIdPD nullAddr = false -> isPDT globalIdPD s) by intuition. apply Hres.
    rewrite beqAddrSym. assumption.
  - exists bentry. assumption.
  - unfold isBE. rewrite HlookupReq. trivial.
}
intro isInRAM.
case_eq (negb isInRAM).
{ (* case_eq (negb isInRAM = true*)
  intros.
  { (** ret *)
    intros. eapply WP.weaken. apply WP.ret.
    intros. simpl. intuition.
  }
}
(* case_eq (negb isInRAM = false *)
intros HisInRAM.
eapply bindRev.
{ (** sizeOfBlock *)
  eapply weaken. apply sizeOfBlock.
  intros s Hprops. simpl. split. apply Hprops. intuition.
  assert(HlookupReq: exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    by assumption. unfold isBE. destruct HlookupReq as [bentry HlookupReq]. rewrite HlookupReq; trivial.
}
intro blockSize.
eapply bindRev.
{ (** getKernelStructureTotalLength *)
	eapply weaken. apply Invariants.getKernelStructureTotalLength.
	intros s Hprops. simpl. apply Hprops.
}
intro kStructureTotalLength.
eapply bindRev.
{ (** Index.ltb *)
  eapply weaken. apply Invariants.Index.ltb.
  intros s Hprops. simpl. apply Hprops.
}
intro isBlockTooSmall.
case_eq isBlockTooSmall.
{ (* case_eq isBlockTooSmall = true *)
  intros.
  { (** ret *)
    eapply weaken. apply WP.ret.
    simpl. intros. intuition.
  }
}
(* case_eq isBlockTooSmall = false *)
intros HblockTooSmall.
eapply bindRev.
{ (** MAL.readBlockAccessibleFromBlockEntryAddr *)
  eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
  intros s Hprops. simpl. split. apply Hprops. intuition.
  assert(HlookupReq: exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    by assumption. unfold isBE. destruct HlookupReq as [bentry HlookupReq]. rewrite HlookupReq; trivial.
}
intro addrIsAccessible.
case_eq (negb addrIsAccessible).
{ (* case_eq negb addrIsAccessible = true *)
  intros.
  { (** ret *)
    eapply weaken. apply WP.ret.
    simpl. intros. intuition.
  }
}
(* case_eq negb addrIsAccessible = false *)
intros HaddrAcc. apply negb_false_iff in HaddrAcc. apply negb_false_iff in HisInRAM.
eapply bindRev.
{ (** MAL.readBlockPresentFromBlockEntryAddr *)
  eapply weaken. apply readBlockPresentFromBlockEntryAddr.
  intros s Hprops. simpl. split. apply Hprops. intuition.
  assert(HlookupReq: exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    by assumption. unfold isBE. destruct HlookupReq as [bentry HlookupReq]. rewrite HlookupReq; trivial.
}
intro addrIsPresent.
case_eq (negb addrIsPresent).
{ (* case_eq negb addrIsPresent = true *)
  intros.
  { (** ret *)
    eapply weaken. apply WP.ret.
    simpl. intros. intuition.
  }
}
(* case_eq negb addrIsPresent = false *)
intros HaddrPresent. apply negb_false_iff in HaddrPresent. eapply bindRev.



eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr *)
  eapply weaken. apply readBlockStartFromBlockEntryAddr.
  intros. simpl. split. apply H8. intuition.
  - (* we know this case is impossible because we are in the branch
    where requisitionedBlockInCurrPartAddr is not NULL *)
    apply beqAddrFalse in H16. congruence.
  - destruct H33. intuition. subst.
    unfold isBE. rewrite H33 ; trivial.
}
intro requisitionedBlockStart.
eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr *)
  eapply weaken. apply readBlockEndFromBlockEntryAddr.
  intros. simpl. split. apply H8. intuition.
  - (* we know this case is impossible because we are in the branch
    where requisitionedBlockInCurrPartAddr is not NULL *)
    apply beqAddrFalse in H17. congruence.
  - destruct H34. intuition. subst.
    unfold isBE. rewrite H34 ; trivial.
}
intro requisitionedBlockEnd.
