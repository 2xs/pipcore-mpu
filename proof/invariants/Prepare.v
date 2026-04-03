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
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas Proof.InternalLemmas2.
Require Import Proof.invariants.Invariants getGlobalIdPDCurrentOrChild sizeOfBlock initStructure.
Require Import writeAccessibleToAncestorsIfNotCutRec. Import isBuiltFromWriteAccessibleRec.
From Stdlib Require Import Compare_dec Bool List Lia Logic.ProofIrrelevance.
Import List.ListNotations.

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
	eapply weaken. apply getGlobalIdPDCurrentOrChildPrecise.
	intros. simpl. split. apply H. intuition; subst currentPart.
  - unfold consistency in *; unfold consistency1 in *; intuition.
	- apply currentPartIsPDT ; unfold consistency in * ; unfold consistency1 in * ; intuition.
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
    /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s))
    /\ beqAddr nullAddr globalIdPD = false
    /\ pdentryNbPrepare globalIdPD nbPrepare s
    /\ false = StateLib.Index.leb maxnbprepare nbPrepare
    /\ kernelentriesnb = CIndex kernelStructureEntriesNb
    /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
    /\ bentryPFlag requisitionedBlockInCurrPartAddr true s
    /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s)
    /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
    /\ (exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    /\ i maxnbprepare = maxNbPrepare).
  rewrite beqAddrFalse in *. intuition.
  - assert(Hres: beqAddr globalIdPD nullAddr = false -> isPDT globalIdPD s) by intuition. apply Hres.
    rewrite beqAddrSym. assumption.
  - rewrite <-beqAddrFalse in *. intuition.
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
  intros s Hprops. simpl. split. apply Hprops. split. intuition.
  assert(HlookupReq: exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    by intuition. unfold isBE. destruct HlookupReq as [bentry HlookupReq]. rewrite HlookupReq; trivial.
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
  intros s Hprops. simpl. split. apply Hprops.
  assert(HlookupReq: exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    by intuition. unfold isBE. destruct HlookupReq as [bentry HlookupReq]. rewrite HlookupReq; trivial.
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
  intros s Hprops. simpl. split. apply Hprops.
  assert(HlookupReq: exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    by intuition. unfold isBE. destruct HlookupReq as [bentry HlookupReq]. rewrite HlookupReq; trivial.
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
{ (** MAL.readSh1PDChildFromBlockEntryAddr **)
  eapply weaken. apply readSh1PDChildFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
  unfold consistency in *; unfold consistency1 in *; intuition.
}
intro PDChildAddr. eapply bindRev.
{ (** Internal.compareAddrToNull **)
  eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
}
intro PDChildAddrIsNull. destruct (negb PDChildAddrIsNull) eqn:HchildNull.
{ (* case negb PDChildAddrIsNull = true *)
  eapply weaken. apply WP.ret. simpl. intros. intuition.
}
(* case negb PDChildAddrIsNull = false *)
apply negb_false_iff in HchildNull. eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr *)
  eapply weaken. apply readBlockStartFromBlockEntryAddr.
  intros s Hprops. simpl.
  assert(HpropsBis: ((((((((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ consistency s /\
    currentPart = currentPartition s /\
    isPDT globalIdPD s /\
    (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s)) /\
    beqAddr nullAddr globalIdPD = false /\
    pdentryNbPrepare globalIdPD nbPrepare s /\
    false = StateLib.Index.leb maxnbprepare nbPrepare /\
    kernelentriesnb = CIndex kernelStructureEntriesNb /\
    requisitionedBlockInCurrPartAddr = idRequisitionedBlock /\
    bentryPFlag requisitionedBlockInCurrPartAddr true s /\
    In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s) /\
    beqAddr nullAddr requisitionedBlockInCurrPartAddr = false /\
    (exists bentry : BlockEntry,
       lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry)) /\
    i maxnbprepare = maxNbPrepare) /\
    isBlockInRAM requisitionedBlockInCurrPartAddr isInRAM s) /\ consistency s /\
    (exists startaddr endaddr : paddr,
       bentryStartAddr requisitionedBlockInCurrPartAddr startaddr s /\
       bentryEndAddr requisitionedBlockInCurrPartAddr endaddr s /\ i blockSize = endaddr - startaddr)) /\
     kStructureTotalLength = Constants.kernelStructureTotalLength) /\
     false = StateLib.Index.ltb blockSize kStructureTotalLength) /\
     bentryAFlag requisitionedBlockInCurrPartAddr addrIsAccessible s) /\
     bentryPFlag requisitionedBlockInCurrPartAddr addrIsPresent s) /\
     (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
        lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) /\
        sh1entryPDchild sh1entryaddr PDChildAddr s /\
        sh1entryAddr requisitionedBlockInCurrPartAddr sh1entryaddr s)) /\
      beqAddr nullAddr PDChildAddr = PDChildAddrIsNull
      /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s).
  {
    split. apply Hprops. split. apply Hprops. destruct Hprops as ((_ & Hsh1) & HbeqNullChild).
    destruct Hsh1 as [_ [sh1entryaddr (_ & Hres & Hsh1)]]. unfold sh1entryAddr in *.
    destruct (lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst sh1entryaddr. subst PDChildAddrIsNull.
    rewrite <-DTL.beqAddrTrue in HbeqNullChild. subst PDChildAddr. assumption.
  }
  split. apply HpropsBis.
  assert(HlookupReq: exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    by intuition. unfold isBE. destruct HlookupReq as [bentry HlookupReq]. rewrite HlookupReq; trivial.
}
intro requisitionedBlockStart. eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr *)
  eapply weaken. apply readBlockEndFromBlockEntryAddr.
  intros s Hprops. simpl. split. apply Hprops.
  assert(HlookupReq: exists bentry, lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr = Some (BE bentry))
    by intuition. unfold isBE. destruct HlookupReq as [bentry HlookupReq]. rewrite HlookupReq; trivial.
}
intro requisitionedBlockEnd. eapply bindRev.
{ (** Internal.initStructure *)
  eapply weaken. apply initStructure.
  intros s Hprops. simpl.
  assert(HblockRMapped: In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s)) by intuition.
  assert(HcurrIsPart: In currentPart (getPartitions multiplexer s)).
  {
    assert(currentPart = currentPartition s) by intuition. subst currentPart.
    unfold consistency in *; unfold consistency1 in *; intuition.
  }
  assert(HlookupStart: lookup requisitionedBlockStart (memory s) beqAddr = None).
  {
    destruct Hprops as ((((((Hprops & HAflag) & HPflag) & Hsh1) & HbeqNullIDchild & _) & HstartBlock) &
      HendBlock).
    assert(Htypes: blocksAddressesTypes s) by (unfold consistency in *; unfold consistency1 in *; intuition).
    destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchild & Hsh1)]]. subst PDChildAddrIsNull.
    rewrite <-DTL.beqAddrTrue in HbeqNullIDchild. subst PDChildAddr. subst addrIsPresent.
    assert(~isKS requisitionedBlockStart s).
    {
      intro Hcontra. assert(HkernAcc: kernelsAreNotAccessible s)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      specialize(HkernAcc requisitionedBlockInCurrPartAddr requisitionedBlockStart currentPart HcurrIsPart
        HblockRMapped HstartBlock Hcontra).
      unfold bentryAFlag in *. destruct (lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr); try(congruence).
      destruct v; congruence.
    }
    assert(~isPDT requisitionedBlockStart s).
    {
      assert(HnotPDT: notPDTIfNotPDflag s) by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(HPDflag: sh1entryPDflag sh1entryaddr false s).
      {
        assert(HaccNoPD: AccessibleNoPDFlag s) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HblockIsBE: isBE requisitionedBlockInCurrPartAddr s).
        {
          unfold isBE. unfold bentryPFlag in *.
          destruct (lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr) eqn:HlookupBlock; try(congruence).
          destruct v; try(congruence). trivial.
        }
        specialize(HaccNoPD requisitionedBlockInCurrPartAddr sh1entryaddr).
        apply HaccNoPD; try(assumption). subst addrIsAccessible. assumption.
      }
      assert(Hsh1Copy: sh1entryAddr requisitionedBlockInCurrPartAddr sh1entryaddr s) by assumption.
      unfold sh1entryAddr in Hsh1Copy.
      destruct (lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      specialize(HnotPDT requisitionedBlockInCurrPartAddr requisitionedBlockStart sh1entryaddr currentPart HcurrIsPart
        HblockRMapped HstartBlock Hsh1 HPDflag HPDchild). assumption.
    }
    unfold sh1entryAddr in *.
    destruct (lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst sh1entryaddr.
    specialize(Htypes requisitionedBlockInCurrPartAddr requisitionedBlockStart requisitionedBlockEnd currentPart
      HcurrIsPart HblockRMapped HstartBlock HendBlock HPDchild).
    destruct Htypes as [(HKS & _) | [(HPDT & _) | Hnone]]; try(exfalso; congruence). apply Hnone.
    assert(HwellFormed: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HwellFormed requisitionedBlockInCurrPartAddr requisitionedBlockStart requisitionedBlockEnd HPflag
      HstartBlock HendBlock). destruct HwellFormed as (HltStartEnd & HsubstEndStart).
    apply getAllPaddrBlockIncl; lia.
  }
  split. apply (conj Hprops HlookupStart). destruct Hprops as ((((((Hprops & HAflag) & HPflag) & Hsh1) &
    HbeqNullIDchild & HPDchild) & HstartBlock) & HendBlock).
  assert(HwellFormed: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
  subst addrIsPresent. specialize(HwellFormed requisitionedBlockInCurrPartAddr requisitionedBlockStart
    requisitionedBlockEnd HPflag HstartBlock HendBlock). destruct HwellFormed as (HltStartEnd & HsubstEndStart).
  split.
  {
    unfold Constants.minBlockSize in HsubstEndStart. unfold Constants.kernelStructureTotalLength. unfold CIndex.
    unfold CIndex in HsubstEndStart. pose proof Constants.maxIdxBiggerThanMinBlock.
    destruct (le_dec 32 maxIdx); try(lia).
    assert(Hsh1offset: i sh1offset = kernelStructureEntriesNb).
    {
      unfold sh1offset. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
      pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl.
      reflexivity.
    }
    assert(Hscoffset: i scoffset = kernelStructureEntriesNb + kernelStructureEntriesNb).
    {
      unfold scoffset. rewrite Hsh1offset. unfold CIndex. cbn. pose proof Constants.maxIdxBiggerThanMinBlock.
      destruct (le_dec 16 maxIdx); try(lia). simpl. reflexivity.
    }
    assert(Hnextoffset: i nextoffset = kernelStructureEntriesNb+kernelStructureEntriesNb+kernelStructureEntriesNb).
    {
      unfold nextoffset. rewrite Hscoffset. unfold CIndex. cbn. destruct (le_dec 24 maxIdx); try(lia). simpl.
      reflexivity.
    }
    destruct (le_dec (nextoffset + 1) maxIdx); try(cbn in *; lia).
  }
  split. lia. split. intuition. split; try(intuition; congruence). intros addr (HlebStartAddr & HltAddrEnd).
  assert(Htypes: blocksAddressesTypes s) by (unfold consistency in *; unfold consistency1 in *; intuition).
  specialize(Htypes requisitionedBlockInCurrPartAddr requisitionedBlockStart requisitionedBlockEnd currentPart
    HcurrIsPart HblockRMapped HstartBlock HendBlock HPDchild).
  assert(~isKS requisitionedBlockStart s).
  {
    unfold isKS. rewrite HlookupStart. intuition.
  }
  assert(~isPDT requisitionedBlockStart s).
  {
    unfold isPDT. rewrite HlookupStart. intuition.
  }
  destruct Htypes as [(HKS & _) | [(HPDT & _) | Hnone]]; try(exfalso; congruence). apply Hnone.
  apply getAllPaddrBlockIncl; lia.
  split. intuition. split. intuition. split. intuition. exists requisitionedBlockInCurrPartAddr. exists currentPart.
  auto.
}
intro isStructureInitialised. destruct (negb isStructureInitialised) eqn:HnegInitStruct.
{
  eapply weaken. apply WP.ret. intros s Hprops. exfalso. apply negb_true_iff in HnegInitStruct.
  destruct Hprops as [s0 Hprops]. intuition. congruence.
}
apply negb_false_iff in HnegInitStruct. eapply bindRev.
{ (** getAddr **)
  unfold getAddr. eapply weaken. apply WP.ret. intros s Hprops.
  instantiate(1 := fun blockStart s => blockStart = requisitionedBlockStart
    /\ consistency1 s /\ noDupMappedPaddrList s /\ accessibleParentPaddrIsAccessibleIntoChild s
    /\ sharedBlockPointsToChild s /\ adressesRangePreservedIfOriginAndNextOk s /\ childsBlocksPropsInParent s
    /\ noChildImpliesAddressesNotShared s /\ blockAndNextAreSideBySide s /\ parentBlocksBoundsIfNoNext s
    /\ childLocMappedInChild s /\ childLocHasSameStart s
    /\ verticalSharing s /\ partitionsIsolation s /\ kernelDataIsolation s
    /\ (forall block startaddr part, startaddr <> requisitionedBlockStart -> In part (getPartitions multiplexer s)
        -> In block (getMappedBlocks part s) -> bentryStartAddr block startaddr s
        -> isKS startaddr s -> bentryAFlag block false s)
    /\ isPDT globalIdPD s
    /\ pdentryNbPrepare globalIdPD nbPrepare s
    /\ bentryPFlag requisitionedBlockInCurrPartAddr true s
    /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s
    /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s
    /\ bentryAFlag requisitionedBlockInCurrPartAddr addrIsAccessible s
    /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s)
    /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s
    /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
          (CIndex (kernelStructureEntriesNb-1)) s
    /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s
    /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s) beqAddr = Some (PADDR nullAddr)
    /\ (forall part kernList, isListOfKernels kernList part s -> ~ In requisitionedBlockStart kernList)
    /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
        -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s)
    /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
        -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s)
    /\ (forall partition, isPDT partition s
        -> Lib.disjoint
          (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
          (getFreeSlotsList partition s))
    /\ wellFormedFreeSlotsList
          (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb)) <> False
    /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
    /\ (forall block, In block
         (filterOptionPaddr
            (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb)))
          -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx) /\ kernIdx < kernelStructureEntriesNb)
    /\ (forall kernIdx kernel, kernIdx < kernelStructureEntriesNb
        -> kernel = CPaddr (requisitionedBlockStart+kernIdx)
        -> In kernel (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s
            (CIndex kernelStructureEntriesNb))))
    /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
        (SomePaddr requisitionedBlockStart) = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
    /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s
    /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
          -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1)) s)
    /\ (forall addr, In addr (filterOptionPaddr
            (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s (CIndex (kernelStructureEntriesNb-1))))
          -> forall part, isPDT part s -> ~In addr (filterOptionPaddr (getKSEntries part s)))
    /\ (forall part, Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
          (getAllPaddrConfigAux (getConfigBlocks part s) s))
    /\ beqAddr nullAddr globalIdPD = false
    /\ false = StateLib.Index.leb maxnbprepare nbPrepare
    /\ kernelentriesnb = CIndex kernelStructureEntriesNb
    /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
    /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
    /\ kStructureTotalLength = Constants.kernelStructureTotalLength
    /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
    /\ beqAddr nullAddr PDChildAddr = PDChildAddrIsNull
    /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
    /\ currentPart = currentPartition s
    /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s))
    /\ i maxnbprepare = maxNbPrepare). simpl.
  destruct Hprops as (Hconsist & HnoDupUsed & Haccess & Hshared & Hrange & HchildBlockProps & HnoChild &
    HnextBlockSide & HparentBounds & HlocProps & HsameStart & HVS & HPI &
    HKDI & _ & HkernAcc & HlookupNext & HidxKern & HidxLast & HPflagNew & HnewFree & HdisjointFree & HwellFormedNew &
    HnoDupNew & HnewFreeAreStartBlocks & HstartsBlocksAreNew & HlastNew & HendLast & HendNew & HnewStructAreNotEntries
    & HnewAreNotConf & [s0 Hpropss0]). split.
  reflexivity. split. assumption. split. assumption. split. assumption. split. assumption. split. assumption. split.
  assumption. split. assumption. split. assumption. split. assumption. split. assumption. split. assumption.
  split. assumption. split. assumption. split. assumption.
  destruct Hpropss0 as (((((((((((((HPIs0 & HKDIs0 & HVSs0 & _ & HcurrPart & HglobIsPDT & Hglob & HbeqGlobNull &
    HnbPrepare & HlebMaxNbPrep & HentriesNb & HblockEq & _ & HblockMapped & HbeqNullBlock & HlookupBlock & Hmax) & _)
    & Hconsists0 & Hbounds) & HkernSize) & HltSizeKernSize) & HAflag) & HPflag) & Hsh1) & HbeqNullIdChild & HPDchild)
    & HstartBlock) & HendBlock) & HlookupStarts0) & HlookupSomeEq & HgetMappedEq & HgetChildrenEq & HkernEq &
    HcurrPartEq & _).
  assert(HlookupGlobEq: lookup globalIdPD (memory s) beqAddr = lookup globalIdPD (memory s0) beqAddr).
  {
    unfold isPDT in HglobIsPDT. apply HlookupSomeEq.
    destruct (lookup globalIdPD (memory s0) beqAddr); try(exfalso; congruence). exists v. reflexivity.
  }
  unfold isPDT. unfold pdentryNbPrepare. rewrite HlookupGlobEq. split. assumption. split. assumption.
  assert(HlookupBlockEq: lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr
    = lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr).
  {
    destruct HlookupBlock as [bentry HlookupBlock]. apply HlookupSomeEq. exists (BE bentry). assumption.
  }
  unfold bentryPFlag. unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryPFlag. unfold bentryAFlag.
  rewrite HlookupBlockEq. split. assumption. split. subst addrIsPresent. assumption. split.
  assumption. split. assumption. split. assumption. split.
  {
    rewrite HgetMappedEq. assumption. unfold getMappedBlocks in HblockMapped; unfold getKSEntries in HblockMapped.
    unfold isPDT. destruct (lookup currentPart (memory s0) beqAddr); try(simpl in HblockMapped; congruence).
    destruct v; try(simpl in HblockMapped; congruence). trivial.
  }
  assert(HgetChildrenCurrEq: getChildren currentPart s = getChildren currentPart s0).
  {
    apply HgetChildrenEq. unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
    destruct (lookup currentPart (memory s0) beqAddr); try(simpl in HblockMapped; congruence).
    destruct v; try(simpl in HblockMapped; congruence). trivial.
  }
  rewrite HgetChildrenCurrEq.
  assert(sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s).
  {
    unfold sh1entryPDchild in *.
    assert(HlookupSh1Eq: lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s) beqAddr
      = lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s0) beqAddr).
    {
      apply HlookupSomeEq.
      destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s0) beqAddr);
        try(exfalso; congruence). destruct v; try(exfalso; congruence). exists (SHE s1). reflexivity.
    }
    rewrite HlookupSh1Eq. assumption.
  }
  assert(i blockSize = requisitionedBlockEnd - requisitionedBlockStart).
  {
    destruct Hbounds as [startBis [endBis (HstartBis & HendBis & Hres)]]. unfold bentryStartAddr in *.
    unfold bentryEndAddr in *.
    destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). subst startBis. subst endBis. subst requisitionedBlockStart.
    subst requisitionedBlockEnd. assumption.
  }
  assert(forall part kernList, isListOfKernels kernList part s -> ~ In requisitionedBlockStart kernList).
  {
    intros part kernList HkernList HstartInList. apply HkernEq in HkernList.
    destruct kernList as [ | kern kernList]; simpl in HstartInList; try(congruence). simpl in HkernList.
    destruct HkernList as [pdentry (HlookupPart & HbeqStructNull & Hkern & HkernList)].
    assert(Hstruct: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(Hstruct part pdentry HlookupPart HbeqStructNull).
    destruct HstartInList as [Hcontra | HstartInList].
    {
      subst kern. unfold isKS in *. subst requisitionedBlockStart. rewrite HlookupStarts0 in *. congruence.
    }
    rewrite Hkern in Hstruct. clear Hkern. revert kern Hstruct HkernList HstartInList.
    induction kernList; intros; simpl in HstartInList; try(congruence). simpl in HkernList.
    destruct HkernList as (HlookupKernNext & HlebNextMax & HbeqANull & HkernListRec).
    assert(HnextValid: nextKernelIsValid s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HnextValid kern Hstruct). destruct HnextValid as (_ & [nextAddr (HlookupKernNextBis & Hnext)]).
    unfold CPaddr in HlookupKernNext. destruct (le_dec (kern + nextoffset) maxAddr); try(lia).
    rewrite HlookupKernNextBis in HlookupKernNext. injection HlookupKernNext as HlookupKernNext. subst a.
    destruct Hnext as [HnextIsKS | Hcontra]; try(congruence).
    destruct HstartInList as [Hcontra | HstartInList].
    {
      subst nextAddr. unfold isKS in *. rewrite HlookupStarts0 in *. congruence.
    }
    apply IHkernList with nextAddr; assumption.
  }
  rewrite HcurrPartEq. intuition.
}
intro newKStructurePointer. eapply bindRev.
{ (** MAL.writeBlockAccessibleFromBlockEntryAddr **)
  eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr. intros s Hprops. simpl.
  instantiate(1 := fun _ s =>
    exists s0 bentry,
      s = {|
            currentPartition := currentPartition s0;
            memory :=
              add requisitionedBlockInCurrPartAddr
                (BE
                   (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) false
                      (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
          |}
      /\ lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr = Some (BE bentry)
      /\ consistency1 s0 /\ noDupMappedPaddrList s0 /\ accessibleParentPaddrIsAccessibleIntoChild s0
      /\ sharedBlockPointsToChild s0 /\ adressesRangePreservedIfOriginAndNextOk s0 /\ childsBlocksPropsInParent s0
      /\ noChildImpliesAddressesNotShared s0 /\ blockAndNextAreSideBySide s0 /\ parentBlocksBoundsIfNoNext s0
      /\ childLocMappedInChild s0 /\ childLocHasSameStart s0
      /\ verticalSharing s0 /\ partitionsIsolation s0 /\ kernelDataIsolation s0
      /\ (forall block startaddr part, startaddr <> requisitionedBlockStart -> In part (getPartitions multiplexer s0)
          -> In block (getMappedBlocks part s0) -> bentryStartAddr block startaddr s0
          -> isKS startaddr s0 -> bentryAFlag block false s0)
      /\ isPDT globalIdPD s0
      /\ pdentryNbPrepare globalIdPD nbPrepare s0
      /\ bentryPFlag requisitionedBlockInCurrPartAddr true s0
      /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s0
      /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s0
      /\ bentryAFlag requisitionedBlockInCurrPartAddr addrIsAccessible s0
      /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)
      /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s0
      /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
            (CIndex (kernelStructureEntriesNb-1)) s0
      /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s0
      /\ currentPart = currentPartition s
      /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s))
      /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s) beqAddr = Some (PADDR nullAddr)
      /\ (forall part kernList, isListOfKernels kernList part s0 -> ~ In requisitionedBlockStart kernList)
      /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
            -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0)
      /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
          -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s0)
      /\ (forall partition, isPDT partition s0
          -> Lib.disjoint
            (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
            (getFreeSlotsList partition s0))
      /\ wellFormedFreeSlotsList
            (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)) <> False
      /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
      /\ (forall block, In block
           (filterOptionPaddr
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)))
            -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                /\ kernIdx < kernelStructureEntriesNb)
      /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
          -> block = CPaddr (requisitionedBlockStart+kernIdx)
          -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0
              (CIndex kernelStructureEntriesNb))))
      /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
            (SomePaddr requisitionedBlockStart)
          = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
      /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s0
      /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
            -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1)) s0)
      /\ (forall addr, In addr (filterOptionPaddr
              (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0 (CIndex (kernelStructureEntriesNb-1))))
            -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
      /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s0
      /\ (forall part,
          Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
          (getAllPaddrConfigAux (getConfigBlocks part s0) s0))
      /\ beqAddr nullAddr globalIdPD = false
      /\ false = StateLib.Index.leb maxnbprepare nbPrepare
      /\ kernelentriesnb = CIndex kernelStructureEntriesNb
      /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
      /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
      /\ kStructureTotalLength = Constants.kernelStructureTotalLength
      /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
      /\ beqAddr nullAddr PDChildAddr = PDChildAddrIsNull
      /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
      /\ newKStructurePointer = requisitionedBlockStart
      /\ i maxnbprepare = maxNbPrepare). simpl.
  assert(HPflag: bentryPFlag requisitionedBlockInCurrPartAddr true s) by intuition.
  unfold bentryPFlag in HPflag.
  destruct (lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. split. reflexivity. exists s. exists b.
  set(s':= {|
             currentPartition := currentPartition s;
             memory :=
               add requisitionedBlockInCurrPartAddr
                 (BE
                    (CBlockEntry (read b) (write b) (exec b) (present b) false (blockindex b) (blockrange b)))
                 (memory s) beqAddr
            |}).
  assert(HgetChildrenEq: getChildren currentPart s' = getChildren currentPart s).
  {
    assert(blockindex b < kernelStructureEntriesNb) by (apply Hidx).
    apply getChildrenEqBENoStartNoPresentChange with b; unfold CBlockEntry;
      destruct (lt_dec (blockindex b) kernelStructureEntriesNb); try(lia); trivial.
    assert(Hcurr: currentPart = currentPartition s) by intuition.
    assert(HcurrIsPart: In currentPart (getPartitions multiplexer s)).
    { subst currentPart. unfold consistency1 in *; intuition. }
    apply partitionsArePDT; trivial; unfold consistency1 in *; intuition.
  }
  assert(sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s).
  {
    subst addrIsAccessible. assert(HAflag: bentryAFlag requisitionedBlockInCurrPartAddr true s) by intuition.
    assert(Hres: AccessibleNoPDFlag s) by (unfold consistency1 in *; intuition). unfold AccessibleNoPDFlag in *.
    apply Hres with requisitionedBlockInCurrPartAddr; trivial.
    - unfold isBE. rewrite HlookupBlock. trivial.
    - unfold sh1entryAddr. rewrite HlookupBlock. trivial.
  }
  rewrite HgetChildrenEq. assert(HlookupNext: lookup (CPaddr (requisitionedBlockStart+nextoffset)) (memory s) beqAddr
    = Some (PADDR nullAddr)) by intuition.
  destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockStart+nextoffset))) eqn:HbeqBlockNext.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite HbeqBlockNext in *. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). intuition.
}
intro. eapply bindRev.
{ (** MAL.removeBlockFromPhysicalMPU **)
  eapply weaken. apply removeBlockFromPhysicalMPU. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s0 [bentry (Hs & HlookupBlock & Hprops)]].
  assert(HblockMapped: In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)) by intuition.
  unfold getMappedBlocks in HblockMapped. unfold getKSEntries in HblockMapped. unfold isPDT.
  destruct (lookup currentPart (memory s0) beqAddr) eqn:HlookupCurr; try(exfalso; simpl in HblockMapped; congruence).
  destruct v; try(exfalso; simpl in HblockMapped; congruence). rewrite Hs. simpl.
  destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockCurr. subst currentPart. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupCurr.
  trivial.
}
intro. eapply bindRev.
{ (** Internal.writeAccessibleToAncestorsIfNotCutRec **)
  eapply weaken. apply writeBlockAccessibleFromBlockEntryAddrFalseKernels. intros s Hprops. simpl.
  destruct Hprops as [s1 [pdentry [realMPU (HMPU & [s0 [bentry (Hs1 & HlookupBlocks0 & Hconsists0 & HnoDups0 &
    Haccesss0 & Hshareds0 & Hranges0 & HchildBlockPropss0 & HnoChilds0 & HnextBlockSides0 & HparentBoundss0 &
    HlocProps & HsameStarts0 & HVSs0 & HPIs0 & HKDIs0 & HkernAccs0 & HglobIsPDTs0
    & HnbPrepare & HPflags0 & Hstarts0 & Hends0 & HAflags0 & HblockMappeds0 & HidxKern & HidxLast & HPDchild
    & Hcurr & Hglob & HlookupNext & HstartNotKern & HPflagNew & HnewFree & HdisjointFree & HwellFormedNew & HnoDupNew
    & HnewFreeAreStartBlocks & HstartsBlocksAreNew & HlastNew & HendLast & HendNew & HnewStructAreNotEntries &
    HPDflag & HnewNotConf & HbeqNullGlob & HlebMaxNbPrep & HentriesNb & Hblock & HbeqNullBlock & HmaxKSlen &
    HltSizeMax & HbeqNullChild & Hsize & HnewPtr & Hmax)]] & HlookupCurrs1 & Hs)]]]. subst addrIsAccessible.
  unfold CBlockEntry in Hs1. assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
  destruct (lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
  assert(HgetPartsEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
  {
    rewrite Hs1. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
      (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)); simpl; try(assumption); try(reflexivity);
      try(unfold consistency1 in *; intuition; congruence).
    - unfold sh1entryAddr. rewrite HlookupBlocks0. reflexivity.
    - destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)))
        eqn:HbeqBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. unfold sh1entryPDchild in *.
        rewrite HlookupBlocks0 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    - unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }
  assert(HcurrIsPDT: isPDT currentPart s0).
  {
    rewrite Hs1 in HlookupCurrs1. simpl in HlookupCurrs1.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    unfold isPDT. rewrite HlookupCurrs1. trivial.
  }

  assert(HgetKSEntriesEqs1: forall part, getKSEntries part s1 = getKSEntries part s0).
  {
    intro part. rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks0. trivial.
  }

  assert(HgetChildrenEqs1: forall pdparent, isPDT pdparent s0 -> getChildren pdparent s1 = getChildren pdparent s0).
  {
    intros pdparent HparentIsPDT. rewrite Hs1.
    apply getChildrenEqBENoStartNoPresentChange with bentry; simpl; trivial.
  }

  assert(HgetMappedEqs1: forall partition, getMappedBlocks partition s1 = getMappedBlocks partition s0).
  {
    intro partition. rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry; simpl; trivial.
  }

  assert(HPDchilds: sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s).
  {
    unfold sh1entryPDchild in *. rewrite Hs. simpl.
    destruct (beqAddr currentPart (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))) eqn:HbeqCurrSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite <-HbeqCurrSh1 in *. unfold isPDT in *.
      destruct (lookup currentPart (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
    destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)))
      eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
  }
  assert(HgetMappedPEqs1s0: forall partition, isPDT partition s0
    -> getMappedPaddr partition s1 = getMappedPaddr partition s0).
  {
    intros partition HpartIsPDT. rewrite Hs1.
    apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry; simpl; trivial.
  }
  assert(HgetConfigEqs1s0: forall partition, isPDT partition s0
    -> getConfigPaddr partition s1 = getConfigPaddr partition s0).
  {
    intros partition HpartIsPDT. rewrite Hs1. apply getConfigPaddrEqBE; trivial. unfold isBE. rewrite HlookupBlocks0.
    trivial.
  }
  assert(HgetConfigPaddrEq: forall partition, isPDT partition s0
    -> getConfigPaddr partition s = getConfigPaddr partition s0).
  {
    intros partition HpartIsPDT. assert(Heq: getConfigPaddr partition s1 = getConfigPaddr partition s0).
    {
      rewrite Hs1. apply getConfigPaddrEqBE; trivial. unfold isBE. rewrite HlookupBlocks0. trivial.
    }
    rewrite <-Heq. rewrite Hs. apply getConfigPaddrEqPDT with pdentry; simpl; trivial. unfold isPDT in *.
    rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart.
    { rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst partition. rewrite HlookupBlocks0 in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }

  assert(HgetConfigBEqs1: forall part, isPDT part s0 -> getConfigBlocks part s1 = getConfigBlocks part s0).
  {
    intros part HpartIsPDT. rewrite Hs1. apply getConfigBlocksEqBE; trivial. unfold isBE. rewrite HlookupBlocks0.
    trivial.
  }

  assert(Hconsists1: consistency1 s1).
  {
    assert(nullAddrExists s1).
    { (* BEGIN nullAddrExists s1 *)
      assert(Hcons0: nullAddrExists s0) by (unfold consistency1 in *; intuition).
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs1. simpl. rewrite beqAddrSym in HbeqNullBlock.
      rewrite HbeqNullBlock. rewrite <-beqAddrFalse in HbeqNullBlock.
      rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END nullAddrExists *)
    }

    assert(wellFormedFstShadowIfBlockEntry s1).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s1 *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
        by (unfold consistency1 in *; intuition). intros block HblockIsBE.
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE in *. rewrite Hs1 in HblockIsBE. simpl in HblockIsBE.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 block HblockIsBEs0). unfold isSHE in *. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(PDTIfPDFlag s1).
    { (* BEGIN PDTIfPDFlag s1 *)
      assert(Hcons0: PDTIfPDFlag s0) by (unfold consistency1 in *; intuition).
      intros idPDchild sh1entryaddr part HpartIsPart HblockMapped (HcheckChild & Hsh1). rewrite HgetPartsEqs1 in *.
      rewrite HgetMappedEqs1 in *. unfold checkChild in *. unfold sh1entryAddr in *.
      unfold bentryAFlag. unfold bentryPFlag. unfold bentryStartAddr. unfold entryPDT. rewrite Hs1 in HcheckChild.
      rewrite Hs1. rewrite Hs1 in Hsh1. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr idPDchild) eqn:HbeqBlockChild.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockChild. subst idPDchild. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        assert(HcheckChilds0: true = checkChild requisitionedBlockInCurrPartAddr s0 sh1entryaddr
          /\ sh1entryAddr requisitionedBlockInCurrPartAddr sh1entryaddr s0).
        {
          unfold checkChild. unfold sh1entryAddr. rewrite HlookupBlocks0. split; assumption.
        }
        specialize(Hcons0 requisitionedBlockInCurrPartAddr sh1entryaddr part HpartIsPart HblockMapped HcheckChilds0).
        destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HPDT)]). unfold bentryPFlag in *.
        unfold bentryStartAddr in *. unfold entryPDT in *. rewrite HlookupBlocks0 in *. split. reflexivity. split.
        assumption. exists startaddr. split. assumption.
        destruct (beqAddr requisitionedBlockInCurrPartAddr (startAddr (blockrange bentry))) eqn:HbeqBlockStart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite HbeqBlockStart in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
        destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1.
        {
          exfalso. destruct (lookup idPDchild (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
        assert(HcheckChilds0: true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0).
        { split; assumption. }
        specialize(Hcons0 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChilds0). unfold entryPDT in *.
        destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HPDT)]). split. assumption. split. assumption.
        exists startaddr. split. assumption. destruct (lookup idPDchild (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (beqAddr requisitionedBlockInCurrPartAddr (startAddr (blockrange b))) eqn:HbeqBlockStart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite HbeqBlockStart in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag s1).
    { (* BEGIN AccessibleNoPDFlag s1 *)
      assert(Hcons0: AccessibleNoPDFlag s0) by (unfold consistency1 in *; intuition).
      intros block sh1entryaddr HblockIsBE Hsh1 HAflag. unfold isBE in *. unfold sh1entryAddr in *.
      unfold bentryAFlag in *. unfold sh1entryPDflag. rewrite Hs1 in HblockIsBE. rewrite Hs1 in HAflag.
      rewrite Hs1 in Hsh1. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      { simpl in HAflag. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). rewrite Hs1.
      specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAflag). unfold sh1entryPDflag in *. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot s1).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s1 *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart HbeqFirstNull. rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition pdentryPart HlookupPart HbeqFirstNull). destruct Hcons0 as (_ & HfirstIsFree).
      unfold isFreeSlot in *. unfold isBE. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (firstfreeslot pdentryPart)) eqn:HbeqBlockFirst.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockFirst. rewrite <-HbeqBlockFirst in *. split; trivial.
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)))
          eqn:HbeqBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite HlookupBlocks0 in *.
        destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockInCurrPartAddr + scoffset)))
          eqn:HbeqBlockSce.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
        destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). intuition.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (lookup (firstfreeslot pdentryPart) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). split; trivial.
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (firstfreeslot pdentryPart + sh1offset)))
          eqn:HbeqBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (lookup (CPaddr (firstfreeslot pdentryPart+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (firstfreeslot pdentryPart + scoffset)))
          eqn:HbeqBlockSce.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite <-HbeqBlockSce in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT s1).
    { (* BEGIN multiplexerIsPDT s1 *)
      assert(Hcons0: multiplexerIsPDT s0) by (unfold consistency1 in *; intuition).
      unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr multiplexer) eqn:HbeqBlockMult.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockMult. rewrite HbeqBlockMult in *.
        rewrite HlookupBlocks0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END multiplexerIsPDT *)
    }

    assert(currentPartitionInPartitionsList s1).
    { (* BEGIN currentPartitionInPartitionsList s1 *)
      assert(Hcons0: currentPartitionInPartitionsList s0) by (unfold consistency1 in *; intuition).
      unfold currentPartitionInPartitionsList in *. rewrite HgetPartsEqs1. rewrite Hs1. simpl. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry s1).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s1 *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s0)
        by (unfold consistency1 in *; intuition). intros block HblockIsBE.
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE in *. rewrite Hs1 in HblockIsBE. simpl in HblockIsBE.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 block HblockIsBEs0). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)].
      exists scentryaddr. split; try(assumption). unfold isSCE in *. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr scentryaddr) eqn:HbeqBlockSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *. rewrite HlookupBlocks0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE s1).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s1 *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by (unfold consistency1 in *; intuition).
      intros kernel idx HkernIsKS HltIdxKernEntries.
      assert(HkernIsKSs0: isKS kernel s0).
      {
        unfold isKS in *. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr requisitionedBlockInCurrPartAddr kernel) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlocks0. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 kernel idx HkernIsKSs0 HltIdxKernEntries). unfold isBE. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (kernel + idx))) eqn:HbeqBlockIdx; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS s1).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s1 *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0)
        by (unfold consistency1 in *; intuition). intros block idx HblockIsBE Hidx.
      assert(Hblocks0: isBE block s0 /\ bentryBlockIndex block idx s0).
      {
        unfold isBE in *. unfold bentryBlockIndex in *. rewrite Hs1 in HblockIsBE. rewrite Hs1 in Hidx. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. split; assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); assumption.
      }
      destruct Hblocks0 as (HblockIsBEs0 & Hidxs0). specialize(Hcons0 block idx HblockIsBEs0 Hidxs0).
      unfold isKS in *. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (block - idx))) eqn:HbeqBlockKern.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. rewrite HbeqBlockKern in *. rewrite HlookupBlocks0 in *.
        simpl in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(sh1InChildLocationIsBE s1).
    { (* BEGIN sh1InChildLocationIsBE s1 *)
      assert(Hcons0: sh1InChildLocationIsBE s0) by (unfold consistency1 in *; intuition).
      intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull. rewrite Hs1 in HlookupSh1. simpl in HlookupSh1.
      destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). unfold isBE in *. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (inChildLocation sh1entry)) eqn:HbeqBlockLoc; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END sh1InChildLocationIsBE *)
    }

    assert(StructurePointerIsKS s1).
    { (* BEGIN StructurePointerIsKS s1 *)
      assert(Hcons0: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart HbeqStructNull. rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition pdentryPart HlookupPart HbeqStructNull). unfold isKS in *. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (structure pdentryPart)) eqn:HbeqBlockStruct.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockStruct. rewrite HbeqBlockStruct in *. rewrite HlookupBlocks0 in *.
        simpl. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END StructurePointerIsKS *)
    }

    assert(NextKSIsKS s1).
    { (* BEGIN NextKSIsKS s1 *)
      assert(Hcons0: NextKSIsKS s0) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull.
      assert(Hkerns0: isKS kernel s0 /\ nextKSAddr kernel nextKSaddr s0).
      {
        unfold isKS in *. unfold nextKSAddr in *. rewrite Hs1 in HkernIsKS. rewrite Hs1 in HnextAddr. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr kernel) eqn:HbeqBlockKern.
        - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0. simpl in *.
          split; assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); assumption.
      }
      destruct Hkerns0 as (HkernIsKSs0 & HnextAddrs0). unfold nextKSentry in *. rewrite Hs1 in HnextKSAddr.
      simpl in HnextKSAddr. destruct (beqAddr requisitionedBlockInCurrPartAddr nextKSaddr) eqn:HbeqBlockNext;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKSs0 HnextAddrs0 HnextKSAddr HbeqNextNull). unfold isKS in *.
      rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr nextKS) eqn:HbeqBlockNextKS.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockNextKS. rewrite HbeqBlockNextKS in *. rewrite HlookupBlocks0 in *.
        simpl. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR s1).
    { (* BEGIN NextKSOffsetIsPADDR s1 *)
      assert(Hcons0: NextKSOffsetIsPADDR s0) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr HkernIsKS HnextAddr.
      assert(Hkerns0: isKS kernel s0 /\ nextKSAddr kernel nextKSaddr s0).
      {
        unfold isKS in *. unfold nextKSAddr in *. rewrite Hs1 in HkernIsKS. rewrite Hs1 in HnextAddr. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr kernel) eqn:HbeqBlockKern.
        - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0. simpl in *.
          split; assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); assumption.
      }
      destruct Hkerns0 as (HkernIsKSs0 & HnextAddrs0). specialize(Hcons0 kernel nextKSaddr HkernIsKSs0 HnextAddrs0).
      destruct Hcons0 as (HnextKSAddr & HbeqNextNull). split; try(assumption). unfold isPADDR in *. rewrite Hs1.
      simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr nextKSaddr) eqn:HbeqBlockNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockNext. subst nextKSaddr. rewrite HlookupBlocks0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(HblockIsNotFree: ~isFreeSlot requisitionedBlockInCurrPartAddr s0).
    {
      unfold isFreeSlot. unfold bentryAFlag in *. rewrite HlookupBlocks0 in *. intro Hcontra.
      destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+scoffset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). destruct Hcontra as (_ & _ & _ & _ & _ & Hcontra & _). congruence.
    }

    assert(NoDupInFreeSlotsList s1).
    { (* BEGIN NoDupInFreeSlotsList s1 *)
      assert(Hcons0: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart. rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition pdentryPart HlookupPart).
      destruct Hcons0 as [optFreeList (Hlist & HwellFormedList & HnoDupList)]. exists optFreeList.
      split; try(split); try(assumption). rewrite Hs1. unfold getFreeSlotsList in *. simpl.
      rewrite beqAddrFalse in HbeqBlockPart. rewrite HbeqBlockPart.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      assert(~ In requisitionedBlockInCurrPartAddr (filterOptionPaddr optFreeList)).
      {
        assert(Hfree: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition). intro Hcontra.
        contradict HblockIsNotFree. unfold freeSlotsListIsFreeSlot in Hfree. apply Hfree with partition optFreeList
          (filterOptionPaddr optFreeList).
        - unfold isPDT. rewrite HlookupPart. trivial.
        - split; assumption.
        - split. reflexivity. assumption.
        - apply not_eq_sym. assumption.
      }
      rewrite HlookupPart in *.
      destruct (beqAddr (firstfreeslot pdentryPart) nullAddr) eqn:HbeqFirstNull; try(assumption).
      apply eq_sym. apply getFreeSlotsListRecEqBE; try(assumption).
      - intro Hcontra. rewrite <-beqAddrFalse in HbeqFirstNull.
        assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
        specialize(HfirstIsFree partition pdentryPart HlookupPart HbeqFirstNull). rewrite Hcontra in *.
        destruct HfirstIsFree as (_ & HfirstIsFree). congruence.
      - unfold isBE. rewrite HlookupBlocks0. trivial.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot s1).
    { (* BEGIN freeSlotsListIsFreeSlot s1 *)
      assert(Hcons0: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition).
      intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
      unfold isPDT in HpartIsPDT. rewrite Hs1 in HpartIsPDT. unfold getFreeSlotsList in HwellFormed.
      rewrite Hs1 in HwellFormed. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      rewrite <-Hs1 in HwellFormed.
      assert(HwellFormeds0: optionfreeslotslist = getFreeSlotsList partition s0
        /\ wellFormedFreeSlotsList optionfreeslotslist <> False).
      {
        destruct HwellFormed as (Hlist & HwellFormed). split; try(assumption). unfold getFreeSlotsList.
        destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(assumption).
        apply getFreeSlotsListRecEqBERev with requisitionedBlockInCurrPartAddr
         {|
           read := read bentry;
           write := write bentry;
           exec := exec bentry;
           present := present bentry;
           accessible := false;
           blockindex := blockindex bentry;
           blockrange := blockrange bentry;
           Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
         |}; try(rewrite <-Hs1); try(assumption).
        - unfold consistency1 in *; intuition.
        - intro Hcontra. rewrite <-beqAddrFalse in HbeqFirstNull.
          assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
          specialize(HfirstIsFree partition p HlookupPart HbeqFirstNull). rewrite Hcontra in *.
          destruct HfirstIsFree as (_ & HfirstIsFree). congruence.
        - unfold isBE. rewrite HlookupBlocks0. trivial.
        - assert(Hres: NoDupInFreeSlotsList s1) by assumption.
          assert(HlookupParts1: lookup partition (memory s1) beqAddr = Some (PDT p)).
          {
            rewrite Hs1. simpl. rewrite beqAddrFalse in HbeqBlockPart. rewrite HbeqBlockPart.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
          }
          specialize(Hres partition p HlookupParts1). destruct Hres as [listBis (HlistBis & _ & Hres)].
          unfold getFreeSlotsList in HlistBis. rewrite HlookupParts1 in *. rewrite HbeqFirstNull in *.
          rewrite <-Hlist in HlistBis. subst listBis. assumption.
        - assert(Hfree: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition). intro Hcontra.
          contradict HblockIsNotFree. unfold freeSlotsListIsFreeSlot in Hfree. apply Hfree with partition
            (getFreeSlotsList partition s0)
            (filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))).
          + unfold isPDT. rewrite HlookupPart. trivial.
          + split; try(reflexivity). assert(Hres: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
            specialize(Hres partition p HlookupPart). destruct Hres as [listBis (HlistBis & Hres & _)].
            subst listBis. assumption.
          + split; try(assumption). unfold getFreeSlotsList. rewrite HlookupPart. rewrite HbeqFirstNull.
            reflexivity.
          + apply not_eq_sym. assumption.
        }
        specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormeds0 HaddrInList
          HbeqAddrNull). unfold isFreeSlot in *. rewrite Hs1. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr addr) eqn:HbeqBlockAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. exfalso. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (addr + sh1offset))) eqn:HbeqBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (addr + scoffset))) eqn:HbeqBlockSce.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(HgetFreeSlotsListEq: forall partition, getFreeSlotsList partition s1 = getFreeSlotsList partition s0).
    {
      intro partition. unfold getFreeSlotsList. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *. rewrite HlookupBlocks0. trivial.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
      destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
      assert(HnoDupList: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
      specialize(HnoDupList partition p HlookupPart). unfold getFreeSlotsList in HnoDupList.
      destruct HnoDupList as [optFreeList (Hlist & HwellFormed & HnoDup)]. rewrite HlookupPart in *.
      rewrite HbeqFirstNull in *. rewrite <-Hlist. apply getFreeSlotsListRecEqBE; try(assumption).
      - assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in HbeqFirstNull. specialize(HfirstIsFree partition p HlookupPart HbeqFirstNull).
        destruct HfirstIsFree as (_ & HfirstIsFree). intro Hcontra. rewrite Hcontra in *. congruence.
      - unfold isBE. rewrite HlookupBlocks0. trivial.
      - assert(Hfree: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition).
        contradict HblockIsNotFree. specialize(Hfree partition).
        apply Hfree with optFreeList (filterOptionPaddr optFreeList).
        + unfold isPDT. rewrite HlookupPart. trivial.
        + split; try(assumption). unfold getFreeSlotsList. rewrite HlookupPart. rewrite HbeqFirstNull.
          assumption.
        + split. reflexivity. assumption.
        + apply not_eq_sym. assumption.
    }

    assert(DisjointFreeSlotsLists s1).
    { (* BEGIN DisjointFreeSlotsLists s1 *)
      assert(Hcons0: DisjointFreeSlotsLists s0) by (unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. rewrite Hs1 in Hpart1IsPDT.
      rewrite Hs1 in Hpart2IsPDT. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr part1) eqn:HbeqBlockPart1; try(exfalso; congruence).
      destruct (beqAddr requisitionedBlockInCurrPartAddr part2) eqn:HbeqBlockPart2; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts).
      destruct Hcons0 as [list1 [list2 (Hlist1 & HwellFormed1 & Hlist2 & HwellFormed2 & Hdisjoint)]].
      exists list1. exists list2.
      assert(HnoDupList: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
      split; try(split; try(split; try(split))); try(assumption).
      1,2: unfold getFreeSlotsList in *; rewrite Hs1; simpl; rewrite beqAddrFalse in *.
      - rewrite HbeqBlockPart1. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
        destruct (lookup part1 (memory s0) beqAddr) eqn:HlookupPart1; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). specialize(HnoDupList part1 p HlookupPart1).
        destruct HnoDupList as [listBis (HlistBis & _ & HnoDupList)]. unfold getFreeSlotsList in HlistBis.
        rewrite HlookupPart1 in *. rewrite <-Hlist1 in HlistBis. subst listBis.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(assumption). apply eq_sym.
        apply getFreeSlotsListRecEqBE; try(assumption).
        + assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in HbeqFirstNull. specialize(HfirstIsFree part1 p HlookupPart1 HbeqFirstNull).
          destruct HfirstIsFree as (_ & HfirstIsFree). intro Hcontra. rewrite Hcontra in *. congruence.
        + unfold isBE. rewrite HlookupBlocks0. trivial.
        + assert(Hfree: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition).
          contradict HblockIsNotFree. specialize(Hfree part1). apply Hfree with list1 (filterOptionPaddr list1).
          * unfold isPDT. rewrite HlookupPart1. trivial.
          * split; try(assumption). unfold getFreeSlotsList. rewrite HlookupPart1. rewrite HbeqFirstNull.
            assumption.
          * split. reflexivity. assumption.
          * apply not_eq_sym. assumption.
      - rewrite HbeqBlockPart2. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
        destruct (lookup part2 (memory s0) beqAddr) eqn:HlookupPart2; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). specialize(HnoDupList part2 p HlookupPart2).
        destruct HnoDupList as [listBis (HlistBis & _ & HnoDupList)]. unfold getFreeSlotsList in HlistBis.
        rewrite HlookupPart2 in *. rewrite <-Hlist2 in HlistBis. subst listBis.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(assumption). apply eq_sym.
        apply getFreeSlotsListRecEqBE; try(assumption).
        + assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in HbeqFirstNull. specialize(HfirstIsFree part2 p HlookupPart2 HbeqFirstNull).
          destruct HfirstIsFree as (_ & HfirstIsFree). intro Hcontra. rewrite Hcontra in *. congruence.
        + unfold isBE. rewrite HlookupBlocks0. trivial.
        + assert(Hfree: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition).
          contradict HblockIsNotFree. specialize(Hfree part2). apply Hfree with list2 (filterOptionPaddr list2).
          * unfold isPDT. rewrite HlookupPart2. trivial.
          * split; try(assumption). unfold getFreeSlotsList. rewrite HlookupPart2. rewrite HbeqFirstNull.
            assumption.
          * split. reflexivity. assumption.
          * apply not_eq_sym. assumption.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries s1).
    { (* BEGIN inclFreeSlotsBlockEntries s1 *)
      assert(Hcons0: inclFreeSlotsBlockEntries s0) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs1 in HpartIsPDT. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition HpartIsPDT). rewrite HgetKSEntriesEqs1. rewrite HgetFreeSlotsListEq. assumption.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries s1).
    { (* BEGIN DisjointKSEntries s1 *)
      assert(Hcons0: DisjointKSEntries s0) by (unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. rewrite Hs1 in Hpart1IsPDT.
      rewrite Hs1 in Hpart2IsPDT. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr part1) eqn:HbeqBlockPart1; try(exfalso; congruence).
      destruct (beqAddr requisitionedBlockInCurrPartAddr part2) eqn:HbeqBlockPart2; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts). rewrite HgetKSEntriesEqs1 in *.
      rewrite HgetKSEntriesEqs1 in *. assumption.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree s1).
    { (* BEGIN noDupPartitionTree s1 *)
      assert(Hcons0: noDupPartitionTree s0) by (unfold consistency1 in *; intuition). unfold noDupPartitionTree.
      rewrite HgetPartsEqs1. assumption.
      (* END noDupPartitionTree *)
    }

    assert(isParent s1).
    { (* BEGIN isParent s1 *)
      assert(Hcons0: isParent s0) by (unfold consistency1 in *; intuition).
      intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEqs1 in HparentIsPart.
      assert(HparentIsPDT: isPDT pdparent s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetChildrenEqs1 in HpartIsChild; trivial.
      specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent in *. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart.
      { rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst partition. rewrite HlookupBlocks0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      (* END isParent *)
    }

    assert(isChild s1).
    { (* BEGIN isChild s1 *)
      assert(Hcons0: isChild s0) by (unfold consistency1 in *; intuition).
      intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEqs1 in HpartIsPart.
      unfold pdentryParent in *. rewrite Hs1 in HparentIsParent. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
      rewrite HgetChildrenEqs1; trivial. unfold isPDT. unfold getChildren in Hcons0.
      destruct (lookup pdparent (memory s0) beqAddr); try(simpl in *; trivial). destruct v; simpl in *; trivial.
      (* END isChild *)
    }

    assert(noDupKSEntriesList s1).
    { (* BEGIN noDupKSEntriesList s1 *)
      assert(Hcons0: noDupKSEntriesList s0) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs1 in HpartIsPDT. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition HpartIsPDT). rewrite HgetKSEntriesEqs1. assumption.
      (* END noDupKSEntriesList *)
    }

    assert(noDupMappedBlocksList s1).
    { (* BEGIN noDupMappedBlocksList s1 *)
      assert(Hcons0: noDupMappedBlocksList s0) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs1 in HpartIsPDT. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition HpartIsPDT). rewrite HgetMappedEqs1. assumption.
      (* END noDupMappedBlocksList *)
    }

    assert(wellFormedBlock s1).
    { (* BEGIN wellFormedBlock s1 *)
      assert(Hcons0: wellFormedBlock s0) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr HPflag HstartBlock HendBlock. specialize(Hcons0 block). apply Hcons0.
      unfold bentryPFlag in *. rewrite Hs1 in HPflag.
      2: unfold bentryStartAddr in *; rewrite Hs1 in HstartBlock.
      3: unfold bentryEndAddr in *; rewrite Hs1 in HendBlock.
      1,2,3: simpl in *; destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks;
        try(rewrite <-DTL.beqAddrTrue in HbeqBlocks; subst block; rewrite HlookupBlocks0; simpl in *; assumption).
      1,2,3: rewrite <-beqAddrFalse in *; rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      (* END wellFormedBlock *)
    }

    assert(parentOfPartitionIsPartition s1).
    { (* BEGIN parentOfPartitionIsPartition s1 *)
      assert(Hcons0: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart. rewrite Hs1 in HlookupPart. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition pdentryPart HlookupPart).
      destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split.
      - intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot). rewrite HgetPartsEqs1.
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial. exists parentEntry.
        rewrite Hs1. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr (parent pdentryPart)) eqn:HbeqBlockParent.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      - split; trivial.
      (* END parentOfPartitionIsPartition *)
    }

    assert(NbFreeSlotsISNbFreeSlotsInList s1).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s1 *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0) by (unfold consistency1 in *; intuition).
      intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. unfold pdentryNbFreeSlots in *.
      rewrite Hs1 in HpartIsPDT. rewrite Hs1 in HnbFree. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree). rewrite HgetFreeSlotsListEq. trivial.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(maxNbPrepareIsMaxNbKernels s1).
    { (* BEGIN maxNbPrepareIsMaxNbKernels s1 *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by (unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. rewrite Hs1 in HlistOfKerns. apply isListOfKernelsEqBE in HlistOfKerns.
      specialize(Hcons0 partition kernList HlistOfKerns). trivial.
      (* END maxNbPrepareIsMaxNbKernels *)
    }

    assert(blockInChildHasAtLeastEquivalentBlockInParent s1).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s1 *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0)
        by (unfold consistency1 in *; intuition). intros pdparent child block startChild endChild
        HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild. rewrite HgetPartsEqs1 in *.
      assert(HparentIsPDT: isPDT pdparent s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetChildrenEqs1 in HchildIsChild; trivial. rewrite HgetMappedEqs1 in *.
      assert(Hblocks0: bentryStartAddr block startChild s0 /\ bentryEndAddr block endChild s0
        /\ bentryPFlag block true s0).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs1 in HstartChild.
        rewrite Hs1 in HendChild. rewrite Hs1 in HPflagChild. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. intuition.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). intuition.
      }
      destruct Hblocks0 as (HstartChilds0 & HendChilds0 & HPflagChilds0).
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        HstartChilds0 HendChilds0 HPflagChilds0). destruct Hcons0 as [blockParent [startParent [endParent
        (HparentMapped & HstartParent & HendParent & Hbounds)]]]. exists blockParent. exists startParent.
      exists endParent. split. assumption. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs1.
      simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0 in *. intuition.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). intuition.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(partitionTreeIsTree s1).
    { (* BEGIN partitionTreeIsTree s1 *)
      assert(Hcons0: partitionTreeIsTree s0) by (unfold consistency1 in *; intuition).
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
      unfold pdentryParent in *. rewrite Hs1 in HparentIsParent. simpl in *. rewrite HgetPartsEqs1 in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr child) eqn:HbeqBlockChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      destruct parentsList; try(simpl in *; intuition; congruence).
      assert(exists pdentry0, lookup pdparent (memory s0) beqAddr = Some (PDT pdentry0)).
      {
        simpl in HparentsList. destruct (lookup p (memory s1) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). destruct HparentsList as (_ & [parentEntry (Hlookup & _)] & _).
        exists parentEntry. rewrite Hs1 in Hlookup. simpl in Hlookup.
        destruct (beqAddr requisitionedBlockInCurrPartAddr pdparent) eqn:HbeqBlockParent; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      }
      rewrite Hs1 in HparentsList. apply isParentsListEqBERev with pdparent requisitionedBlockInCurrPartAddr
         {|
           read := read bentry;
           write := write bentry;
           exec := exec bentry;
           present := present bentry;
           accessible := false;
           blockindex := blockindex bentry;
           blockrange := blockrange bentry;
           Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
         |} bentry (p::parentsList) s0 in HparentsList; try(assumption);
        try(unfold consistency1 in *; intuition; congruence).
      specialize(Hcons0 child pdparent (p::parentsList) HbeqChildRoot HchildIsPart HparentIsParent HparentsList).
      assumption.
      (* END partitionTreeIsTree *)
    }

    assert(nextKernelIsValid s1).
    { (* BEGIN nextKernelIsValid s1 *)
      assert(Hcons0: nextKernelIsValid s0) by (unfold consistency1 in *; intuition).
      intros kernel HkernIsKS.
      assert(HkernIsKSs0: isKS kernel s0).
      {
        unfold isKS in *. rewrite Hs1 in HkernIsKS. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr kernel) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlocks0. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 kernel HkernIsKSs0). split. apply Hcons0.
      destruct Hcons0 as (HlebNextMax & [nextKSaddr (HlookupNextBis & HnextIsKS)]). exists nextKSaddr. split.
      - intro Hp. rewrite Hs1. simpl. specialize(HlookupNextBis Hp).
        destruct (beqAddr requisitionedBlockInCurrPartAddr {| p := kernel+nextoffset; Hp := Hp |}) eqn:HbeqBlockNext.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite HbeqBlockNext in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      - destruct HnextIsKS as [HnextIsKS | HnextIsNull]; try(right; assumption). left. unfold isKS in *. rewrite Hs1.
        simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr nextKSaddr) eqn:HbeqBlockNext.
        + rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite HbeqBlockNext in *. rewrite HlookupBlocks0 in *. simpl.
          assumption.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns s1).
    { (* BEGIN noDupListOfKerns s1 *)
      assert(Hcons0: noDupListOfKerns s0) by (unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. rewrite Hs1 in HlistOfKerns. apply isListOfKernelsEqBE in HlistOfKerns.
      specialize(Hcons0 partition kernList HlistOfKerns). assumption.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax s1).
    { (* BEGIN MPUsizeIsBelowMax s1 *)
      assert(Hcons0: MPUsizeIsBelowMax s0) by (unfold consistency1 in *; intuition).
      intros partition MPUlist HMPUPart. unfold pdentryMPU in *. rewrite Hs1 in HMPUPart. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition MPUlist HMPUPart). assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart s1).
    { (* BEGIN originIsParentBlocksStart s1 *)
      assert(Hcons0: originIsParentBlocksStart s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEqs1 in *. rewrite HgetMappedEqs1 in *. rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      unfold scentryOrigin in *. rewrite Hs1 in Horigin. simpl in Horigin.
      destruct (beqAddr requisitionedBlockInCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
        Horigin). destruct Hcons0 as (HinclParent & HlebStart). split.
      - intro HbeqPartRoot. specialize(HinclParent HbeqPartRoot).
        destruct HinclParent as [blockParent (HblockParentMapped & HstartParent & Hincl)]. exists blockParent.
        split. assumption. unfold bentryStartAddr in *. rewrite Hs1. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlockBlockP.
        + simpl in *. rewrite <-DTL.beqAddrTrue in HbeqBlockBlockP. subst blockParent. rewrite HlookupBlocks0 in *.
          split. assumption. intros addr HaddrInBlock.
          destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
          * simpl in *. assumption.
          * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
            specialize(Hincl addr HaddrInBlock). assumption.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). split.
          assumption. intros addr HaddrInBlock.
          destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
          * simpl in *. assert(HaddrInBlocks0: In addr (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)).
            { simpl. rewrite HlookupBlocks0. assumption. }
            rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. simpl in *. specialize(Hincl addr HaddrInBlocks0).
            assumption.
          * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
            specialize(Hincl addr HaddrInBlock). assumption.
      - intros startaddr HstartBlock. unfold bentryStartAddr in *. apply HlebStart. rewrite Hs1 in HstartBlock.
        simpl in *. destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. trivial.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut s1).
    { (* BEGIN nextImpliesBlockWasCut s1 *)
      assert(Hcons0: nextImpliesBlockWasCut s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
        Hsce HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEqs1 in *.
      rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      unfold scentryNext in Hnext. rewrite Hs1 in Hnext. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      assert(HendBlocks0: bentryEndAddr block endaddr s0).
      {
        unfold bentryEndAddr in *. rewrite Hs1 in HendBlock. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 partition pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
        HendBlocks0 Hsce HbeqNextNull Hnext HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & HltEnd & Hincl)]].
      exists blockParent. exists endParent. split. assumption. unfold bentryEndAddr in *. rewrite Hs1. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlockBlockP.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockBlockP. subst blockParent. rewrite HlookupBlocks0 in *. simpl.
        split; trivial. split; trivial. intros addr HaddrInBlock.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        + simpl in *. assumption.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
          specialize(Hincl addr HaddrInBlock). assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
        split; trivial. split; trivial. intros addr HaddrInBlock.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        + simpl in *. assert(HaddrInBlocks0: In addr (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)).
          { simpl. rewrite HlookupBlocks0. assumption. }
          rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. simpl in *. specialize(Hincl addr HaddrInBlocks0).
          assumption.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
          specialize(Hincl addr HaddrInBlock). assumption.
      (* END nextImpliesBlockWasCut *)
    }

    assert(blocksAddressesTypes s1).
    { (* BEGIN blocksAddressesTypes s1 *)
      assert(Hcons0: blocksAddressesTypes s0) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock.
      rewrite HgetPartsEqs1 in *. rewrite HgetMappedEqs1 in *. unfold sh1entryPDchild in *.
      rewrite Hs1 in HPDchildBlock. simpl in *. destruct (beqAddr requisitionedBlockInCurrPartAddr
        (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs1 in HstartBlock.
        rewrite Hs1 in HendBlock. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. intuition.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). intuition.
      }
      destruct Hblocks0 as (HstartBlocks0 & HendBlocks0).
      specialize(Hcons0 block startaddr endaddr part HpartIsPart HblockMapped HstartBlocks0 HendBlocks0
        HPDchildBlock).
      destruct Hcons0 as [(HKS & HblockRange) | [(HPDT & HblockRange) | Hnone]].
      - left. split.
        + unfold isKS in *. rewrite Hs1. simpl.
          destruct (beqAddr requisitionedBlockInCurrPartAddr startaddr) eqn:HbeqBlockStart.
          * rewrite <-DTL.beqAddrTrue in HbeqBlockStart. subst startaddr. rewrite HlookupBlocks0 in *. simpl. trivial.
          * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
        + intros addr HaddrInRange. specialize(HblockRange addr HaddrInRange).
          destruct HblockRange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
          * left. unfold isBE in *. rewrite Hs1. simpl.
            destruct (beqAddr requisitionedBlockInCurrPartAddr addr) eqn:HbeqBlockAddr; trivial.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
          * right. left. unfold isSHE in *. rewrite Hs1. simpl.
            destruct (beqAddr requisitionedBlockInCurrPartAddr addr) eqn:HbeqBlockAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks0 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
          * right. right. left. unfold isSCE in *. rewrite Hs1. simpl.
            destruct (beqAddr requisitionedBlockInCurrPartAddr addr) eqn:HbeqBlockAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks0 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
          * right. right. right. left. unfold isPADDR in *. rewrite Hs1. simpl.
            destruct (beqAddr requisitionedBlockInCurrPartAddr addr) eqn:HbeqBlockAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks0 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
          * right. right. right. right. rewrite Hs1. simpl.
            destruct (beqAddr requisitionedBlockInCurrPartAddr addr) eqn:HbeqBlockAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks0 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      - right. left. split.
        + unfold isPDT in *. rewrite Hs1. simpl.
          destruct (beqAddr requisitionedBlockInCurrPartAddr startaddr) eqn:HbeqBlockStart.
          { rewrite <-DTL.beqAddrTrue in HbeqBlockStart. subst startaddr. rewrite HlookupBlocks0 in *. congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
        + intros addr HaddrInRange. specialize(HblockRange addr HaddrInRange). rewrite Hs1. simpl.
          destruct (beqAddr requisitionedBlockInCurrPartAddr addr) eqn:HbeqBlockAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      - right. right. intros addr HaddrInRange. specialize(Hnone addr HaddrInRange). rewrite Hs1. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr addr) eqn:HbeqBlockAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks0 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END blocksAddressesTypes *)
    }

    assert(notPDTIfNotPDflag s1).
    { (* BEGIN notPDTIfNotPDflag s1 *)
      assert(Hcons0: notPDTIfNotPDflag s0) by (unfold consistency1 in *; intuition).
      intros block startaddr sh1entryaddr part HpartIsPart HblockMapped HstartBlock Hsh1 HPDflagBlock HPDchildBlock.
      rewrite HgetPartsEqs1 in *. rewrite HgetMappedEqs1 in *. unfold sh1entryPDflag in *.
      unfold sh1entryPDchild in *. rewrite Hs1 in HPDflagBlock. rewrite Hs1 in HPDchildBlock. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ sh1entryAddr block sh1entryaddr s0).
      {
        unfold bentryStartAddr in *. unfold sh1entryAddr in *. rewrite Hs1 in HstartBlock.
        rewrite Hs1 in Hsh1.
        simpl in *. destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct Hblocks0 as (HstartBlocks0 & Hsh1s0).
      specialize(Hcons0 block startaddr sh1entryaddr part HpartIsPart HblockMapped HstartBlocks0 Hsh1s0 HPDflagBlock
        HPDchildBlock).
      contradict Hcons0. unfold isPDT in *. rewrite Hs1 in Hcons0. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr startaddr) eqn:HbeqBlockStart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      (* END notPDTIfNotPDflag *)
    }

    assert(nextKernAddrIsInSameBlock s1).
    { (* BEGIN nextKernAddrIsInSameBlock s1 *)
      assert(Hcons0: nextKernAddrIsInSameBlock s0) by (unfold consistency1 in *; intuition).
      intros block kernel startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock
        HkernIsKS. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEqs1 in *.
      assert(HkernIsKSs0: isKS kernel s0).
      {
        unfold isKS in *. rewrite Hs1 in HkernIsKS. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr kernel) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst kernel. rewrite HlookupBlocks0. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym); assumption.
      }
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs1 in HstartBlock.
        rewrite Hs1 in HendBlock. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. intuition.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). intuition.
      }
      destruct Hblocks0 as (HstartBlocks0 & HendBlocks0). unfold sh1entryPDchild in *.
      rewrite Hs1 in HPDchildBlock. simpl in *. destruct (beqAddr requisitionedBlockInCurrPartAddr
        (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 block kernel startaddr endaddr part HpartIsPart HblockMapped HstartBlocks0 HendBlocks0
        HPDchildBlock HkernIsKSs0). assumption.
      (* END nextKernAddrIsInSameBlock *)
    }

    (*assert(blockBelongsToAPart s1).
    { (* BEGIN blockBelongsToAPart s1 *)
      assert(Hcons0: blockBelongsToAPart s0) by (unfold consistency1 in *; intuition).
      intros block HPflagBlock. assert(HPflagBlocks0: bentryPFlag block true s0).
      {
        unfold bentryPFlag in *. rewrite Hs1 in HPflagBlock. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 block HPflagBlocks0). rewrite HgetPartsEqs1. destruct Hcons0 as [part Hcons0]. exists part.
      rewrite HgetMappedEqs1. assumption.
      (* END blockBelongsToAPart *)
    }*)

    assert(PDflagMeansNoChild s1).
    { (* BEGIN PDflagMeansNoChild s1 *)
      assert(Hcons0: PDflagMeansNoChild s0) by (unfold consistency1 in *; intuition).
      intros block HblockIsBE HPDflagBlock. unfold sh1entryPDflag in *. unfold sh1entryPDchild. rewrite Hs1.
      rewrite Hs1 in HPDflagBlock. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1;
        try(congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE in *. rewrite Hs1 in HblockIsBE. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 block HblockIsBEs0 HPDflagBlock). assumption.
      (* END PDflagMeansNoChild *)
    }

    assert(nbPrepareIsNbKern s1).
    { (* BEGIN nbPrepareIsNbKern s1 *)
      assert(Hcons0: nbPrepareIsNbKern s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart. rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentryPart HlookupPart).
      assert(Heq: completeListOfKernels (structure pdentryPart) s1
        = completeListOfKernels (structure pdentryPart) s0).
      { rewrite Hs1. apply completeListOfKernelsEqBE with bentry; trivial. }
      rewrite Heq. assumption.
      (* END nbPrepareIsNbKern *)
    }

    assert(pdchildIsPDT s1).
    { (* BEGIN pdchildIsPDT s1 *)
      assert(Hcons0: pdchildIsPDT s0) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull.
      rewrite HgetPartsEqs1 in *. rewrite HgetMappedEqs1 in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      unfold sh1entryPDchild in *. rewrite Hs1 in HPDchildB. simpl in HPDchildB.
      destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(Hsh1s0: sh1entryAddr block sh1entryaddr s0).
      {
        unfold sh1entryAddr in *. rewrite Hs1 in Hsh1. simpl in Hsh1.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1s0 HPDchildB HbeqIdChildNull).
      rewrite HgetChildrenEqs1; trivial.
      (* END pdchildIsPDT *)
    }

    assert(childBlockNullIfChildNull s1).
    { (* BEGIN childBlockNullIfChildNull s1 *)
      assert(Hcons0: childBlockNullIfChildNull s0) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchildB.
      rewrite HgetPartsEqs1 in *. rewrite HgetMappedEqs1 in *. unfold sh1entryInChildLocation. rewrite Hs1.
      unfold sh1entryPDchild in *. rewrite Hs1 in HPDchildB. simpl in HPDchildB. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(Hsh1s0: sh1entryAddr block sh1entryaddr s0).
      {
        unfold sh1entryAddr in *. rewrite Hs1 in Hsh1. simpl in Hsh1.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part block sh1entryaddr HpartIsPart HblockMapped Hsh1s0 HPDchildB).
      unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). destruct Hcons0. split; trivial. intro. exfalso; congruence.
      (* END childBlockNullIfChildNull *)
    }

    assert(accessibleBlocksArePresent s1).
    { (* BEGIN accessibleBlocksArePresent s1 *)
      assert(Hcons0: accessibleBlocksArePresent s0) by (unfold consistency1 in *; intuition).
      intros block HAflag. unfold bentryAFlag in *. unfold bentryPFlag. rewrite Hs1 in HAflag. rewrite Hs1.
      simpl in *. destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      { simpl in *. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      apply Hcons0; assumption.
      (* END accessibleBlocksArePresent *)
    }

    assert(sharedBlockIsPresent s1).
    { (* BEGIN sharedBlockIsPresent s1 *)
      assert(Hcons0: sharedBlockIsPresent s0) by (unfold consistency1 in *; intuition).
      intros part block child HpartIsPart HblockIsEntry HPDchildB HbeqChildNull. rewrite HgetPartsEqs1 in *.
      rewrite HgetKSEntriesEqs1 in *. unfold sh1entryPDchild in *. rewrite Hs1 in HPDchildB. simpl in HPDchildB.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block child HpartIsPart HblockIsEntry HPDchildB HbeqChildNull). unfold bentryPFlag in *.
      rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0 in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      (* END sharedBlockIsPresent *)
    }

    assert(sharedBlockNoPDflagNoLocIsKern s1).
    { (* BEGIN sharedBlockNoPDflagNoLocIsKern s1 *)
      assert(Hcons0: sharedBlockNoPDflagNoLocIsKern s0) by (unfold consistency1 in *; intuition).
      intros part block child startaddr HpartIsPart HblockIsEntry HPDchildB HbeqChildNull HPDflagB Hloc Hstart.
      rewrite HgetPartsEqs1 in *. rewrite HgetKSEntriesEqs1 in *. unfold sh1entryPDchild in *.
      unfold sh1entryPDflag in *. unfold sh1entryInChildLocationWeak in *. rewrite Hs1 in HPDchildB.
      rewrite Hs1 in HPDflagB. rewrite Hs1 in Hloc. simpl in HPDchildB. simpl in HPDflagB. simpl in Hloc.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hstarts0B: bentryStartAddr block startaddr s0).
      {
        unfold bentryStartAddr in *. rewrite Hs1 in Hstart. simpl in Hstart.
        destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 part block child startaddr HpartIsPart HblockIsEntry HPDchildB HbeqChildNull HPDflagB Hloc
        Hstarts0B). rewrite HgetConfigBEqs1; trivial. unfold getConfigBlocks in *. unfold isPDT.
      destruct (lookup child (memory s0) beqAddr); try(simpl in Hcons0; congruence).
      destruct v; try(simpl in Hcons0; congruence). trivial.
      (* END sharedBlockNoPDflagNoLocIsKern *)
    }

    assert(HgetMappedPEq: forall part, isPDT part s0 -> getMappedPaddr part s1 = getMappedPaddr part s0).
    {
      intros part HpartIsPDT. rewrite Hs1.
      apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry; trivial.
    }

    assert(partitionNotAutoMapped s1).
    { (* BEGIN partitionNotAutoMapped s1 *)
      assert(Hcons0: partitionNotAutoMapped s0) by (unfold consistency1 in *; intuition).
      intros part HpartIsPart. rewrite HgetPartsEqs1 in *. specialize(Hcons0 part HpartIsPart).
      assert(isPDT part s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetMappedPEq; trivial.
      (* END partitionNotAutoMapped *)
    }

    assert(configAddrNotMappedInChild s1).
    { (* BEGIN configAddrNotMappedInChild s1 *)
      assert(Hcons0: configAddrNotMappedInChild s0) by (unfold consistency1 in *; intuition).
      intros part child addr HpartIsPart HchildIsChild HaddrIsConfig. rewrite HgetPartsEqs1 in *.
      assert(isPDT part s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEqs1 in *; trivial. rewrite HgetConfigEqs1s0 in *; trivial.
      specialize(Hcons0 part child addr HpartIsPart HchildIsChild HaddrIsConfig). rewrite HgetMappedPEqs1s0; trivial.
      apply childrenArePDT with part; trivial; unfold consistency1 in *; intuition.
     (* END configAddrNotMappedInChild *)
    }

    (* assert(configNotMappedRoot s1).
    { (* BEGIN configNotMappedRoot s1 *)
      assert(Hcons0: configNotMappedRoot s0) by (unfold consistency1 in *; intuition).
      intros addr HaddrIsConfig. assert(isPDT multiplexer s0) by (unfold consistency1 in *; intuition).
      rewrite HgetConfigEqs1s0 in *; trivial. specialize(Hcons0 addr HaddrIsConfig).
      rewrite HgetMappedPEqs1s0; trivial.
     (* END configNotMappedRoot *)
    } *)

    assert(fullKernelIsInOneBlock s1).
    { (* BEGIN fullKernelIsInOneBlock s1 *)
      assert(Hcons0: fullKernelIsInOneBlock s0) by (unfold consistency1 in *; intuition).
      intros part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKS. rewrite HgetPartsEqs1 in *.
      rewrite HgetMappedEqs1 in *. assert(HkernIsKSs0: isKS kernel s0).
      {
        unfold isKS in *. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr requisitionedBlockInCurrPartAddr kernel) eqn:HbeqBlockKern.
        - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      assert(HgetBlocksEq: getAllPaddrAux [block] s1 = getAllPaddrAux [block] s0).
      {
        rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      rewrite HgetBlocksEq in *.
      specialize(Hcons0 part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKSs0). assumption.
     (* END fullKernelIsInOneBlock *)
    }

    assert(sharedBlocksAdressesAreAllMappedInChild s1).
    { (* BEGIN sharedBlocksAdressesAreAllMappedInChild s1 *)
      assert(Hcons0: sharedBlocksAdressesAreAllMappedInChild s0) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1 HPDchildB Hloc HbeqChildNull
        HbeqLocNull addr HaddrInBlock. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEqs1 in *.
      assert(Hblocks0: sh1entryAddr block sh1entryaddr s0 /\ getAllPaddrAux [block] s1 = getAllPaddrAux [block] s0).
      {
        unfold sh1entryAddr in *. rewrite Hs1 in Hsh1. simpl in Hsh1.
        rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (Hsh1s0 & HgetBlocksEq). rewrite HgetBlocksEq in *. unfold sh1entryPDchild in *.
      unfold sh1entryInChildLocationWeak in *. rewrite Hs1 in HPDchildB. rewrite Hs1 in Hloc. simpl in HPDchildB.
      simpl in Hloc. destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1s0 HPDchildB Hloc
        HbeqChildNull HbeqLocNull addr HaddrInBlock). rewrite HgetMappedPEqs1s0; trivial. unfold getMappedPaddr in *.
      unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
      destruct (lookup child (memory s0) beqAddr); try(simpl in Hcons0; congruence).
      destruct v; try(simpl in Hcons0; congruence). trivial.
     (* END sharedBlocksAdressesAreAllMappedInChild *)
    }

    unfold consistency1. intuition.
  }
  assert(HgetPartsEqs: getPartitions multiplexer s = getPartitions multiplexer s1).
  {
    rewrite Hs. apply getPartitionsEqPDT with pdentry; auto; unfold consistency1 in *; intuition;
      unfold getPartitions; replace (maxAddr+2) with (S (maxAddr+1)); try(lia); simpl; auto.
  }

  assert(HgetKSEntriesEq: forall partition, getKSEntries partition s = getKSEntries partition s1).
  { intro partition. rewrite Hs. apply getKSEntriesEqPDT with pdentry; unfold consistency1 in *; intuition. }

  assert(HgetChildrenEq: forall pdparent, getChildren pdparent s = getChildren pdparent s1).
  { intro pdparent. rewrite Hs. apply getChildrenEqPDT with pdentry; unfold consistency1 in *; intuition. }

  assert(HgetMappedEq: forall partition, getMappedBlocks partition s = getMappedBlocks partition s1).
  { intro partition. rewrite Hs. apply getMappedBlocksEqPDT with pdentry; unfold consistency1 in *; intuition. }

  assert(HgetMappedPaddrEq: forall partition, isPDT partition s0
    -> getMappedPaddr partition s = getMappedPaddr partition s0).
  {
    intros partition HpartIsPDT. rewrite <-HgetMappedPEqs1s0; trivial.
    rewrite Hs. apply getMappedPaddrEqPDT with pdentry; simpl; trivial. unfold consistency1 in *.
    intuition.
  }

  assert(Hconsists: consistency1 s).
  {
    assert(nullAddrExists s).
    { (* BEGIN nullAddrExists s *)
      assert(Hcons0: nullAddrExists s1) by (unfold consistency1 in *; intuition).
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart nullAddr) eqn:HbeqCurrNull.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNull. rewrite HbeqCurrNull in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END nullAddrExists *)
    }

    assert(wellFormedFstShadowIfBlockEntry s).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s1)
        by (unfold consistency1 in *; intuition). intros block HblockIsBE. unfold isBE in *. unfold isSHE.
      rewrite Hs in HblockIsBE. rewrite Hs. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      specialize(Hcons0 block HblockIsBE). unfold isSHE in *.
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(PDTIfPDFlag s).
    { (* BEGIN PDTIfPDFlag s *)
      assert(Hcons0: PDTIfPDFlag s1) by (unfold consistency1 in *; intuition).
      intros idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild. rewrite HgetPartsEqs in *.
      rewrite HgetMappedEq in *.
      assert(HlookupEq: lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s1) beqAddr).
      {
        destruct HcheckChild as (_ & Hsh1). unfold sh1entryAddr in *. rewrite Hs in Hsh1. rewrite Hs. simpl in *.
        destruct (beqAddr currentPart idPDchild) eqn:HbeqCurrBlock; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). trivial.
      }
      assert(HcheckChilds1: true = checkChild idPDchild s1 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s1).
      {
        unfold checkChild in *. unfold sh1entryAddr in *. rewrite HlookupEq in *.
        destruct HcheckChild as (HcheckChild & Hsh1). split; trivial.
        destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
        rewrite Hs in HcheckChild. simpl in *.
        destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChilds1). unfold bentryAFlag.
      unfold bentryPFlag.
      unfold bentryStartAddr. unfold entryPDT in *. rewrite HlookupEq. destruct Hcons0 as (HAflags1 & HPflags1 &
        [startaddr (Hstarts1 & Hentry)]). split; trivial. split; trivial. exists startaddr. split; trivial.
      destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence). rewrite Hs.
      simpl. destruct (beqAddr currentPart (startAddr (blockrange b))) eqn:HbeqCurrStart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrStart. rewrite HbeqCurrStart in *. rewrite HlookupCurrs1 in *.
        assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag s).
    { (* BEGIN AccessibleNoPDFlag s *)
      assert(Hcons0: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
      intros block sh1entryaddr HblockIsBE Hsh1 HAflag. unfold isBE in *. unfold sh1entryAddr in *.
      unfold bentryAFlag in *. rewrite Hs in HblockIsBE. rewrite Hs in Hsh1. rewrite Hs in HAflag. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAflag). unfold sh1entryPDflag in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart HbeqFirstNull.
      assert(Hparts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)
        /\ firstfreeslot pdentryParts1 = firstfreeslot pdentryPart).
      {
        rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - exists pdentry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. split; trivial.
          injection HlookupPart as HlookupPart. rewrite <-HlookupPart. simpl. reflexivity.
        - exists pdentryPart. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hparts1 as [pdentryParts1 (HlookupParts1 & HfirstEq)]. rewrite <-HfirstEq in HbeqFirstNull.
      specialize(Hcons0 partition pdentryParts1 HlookupParts1 HbeqFirstNull). destruct Hcons0 as (_ & Hcons0).
      unfold isBE. unfold isFreeSlot in *. rewrite HfirstEq in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (firstfreeslot pdentryPart)) eqn:HbeqCurrFirst.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrFirst. rewrite HbeqCurrFirst in *. rewrite HlookupCurrs1 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup (firstfreeslot pdentryPart) (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split; trivial.
      destruct (beqAddr currentPart (CPaddr (firstfreeslot pdentryPart + sh1offset))) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup (CPaddr (firstfreeslot pdentryPart+sh1offset)) (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      destruct (beqAddr currentPart (CPaddr (firstfreeslot pdentryPart + scoffset))) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT s).
    { (* BEGIN multiplexerIsPDT s *)
      assert(Hcons0: multiplexerIsPDT s1) by (unfold consistency1 in *; intuition).
      unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart multiplexer) eqn:HbeqCurrMult; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END multiplexerIsPDT *)
    }

    assert(currentPartitionInPartitionsList s).
    { (* BEGIN currentPartitionInPartitionsList s *)
      assert(Hcons0: currentPartitionInPartitionsList s1) by (unfold consistency1 in *; intuition).
      unfold currentPartitionInPartitionsList. rewrite HgetPartsEqs. rewrite Hs. simpl. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry s).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s1)
        by (unfold consistency1 in *; intuition). intros block HblockIsBE. unfold isBE in *.
      rewrite Hs in HblockIsBE. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      specialize(Hcons0 block HblockIsBE). destruct Hcons0 as [scentryaddr (HSCE & Hsce)]. exists scentryaddr.
      split; trivial. unfold isSCE in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE s).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s1) by (unfold consistency1 in *; intuition).
      intros kernel idx HkernIsKS HltIdxKernEntries. unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (CPaddr (kernel + idx))) eqn:HbeqCurrIdx.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrIdx. rewrite HbeqCurrIdx in *. rewrite HlookupCurrs1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS s).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s1)
        by (unfold consistency1 in *; intuition). intros block idx HblockIsBE Hidx. unfold bentryBlockIndex in *.
      unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs in Hidx. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 block idx HblockIsBE Hidx). unfold isKS in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (CPaddr (block - idx))) eqn:HbeqCurrIdx.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrIdx. rewrite HbeqCurrIdx in *. rewrite HlookupCurrs1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(sh1InChildLocationIsBE s).
    { (* BEGIN sh1InChildLocationIsBE s *)
      assert(Hcons0: sh1InChildLocationIsBE s1) by (unfold consistency1 in *; intuition).
      intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull. rewrite Hs in HlookupSh1. simpl in *.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). unfold isBE in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (inChildLocation sh1entry)) eqn:HbeqCurrLoc.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrLoc. rewrite HbeqCurrLoc in *. rewrite HlookupCurrs1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END sh1InChildLocationIsBE *)
    }

    assert(StructurePointerIsKS s).
    { (* BEGIN StructurePointerIsKS s *)
      assert(Hcons0: StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart HbeqStructNull.
      assert(Hparts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)
        /\ structure pdentryParts1 = structure pdentryPart).
      {
        rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - exists pdentry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. split; trivial.
          injection HlookupPart as HlookupPart. rewrite <-HlookupPart. simpl. reflexivity.
        - exists pdentryPart. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hparts1 as [pdentryParts1 (HlookupParts1 & HstructEq)]. rewrite <-HstructEq in HbeqStructNull.
      specialize(Hcons0 partition pdentryParts1 HlookupParts1 HbeqStructNull). unfold isKS in *. rewrite Hs. simpl.
      rewrite HstructEq in *. destruct (beqAddr currentPart (structure pdentryPart)) eqn:HbeqCurrStruct.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrStruct. rewrite HbeqCurrStruct in *. rewrite HlookupCurrs1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END StructurePointerIsKS *)
    }

    assert(NextKSIsKS s).
    { (* BEGIN NextKSIsKS s *)
      assert(Hcons0: NextKSIsKS s1) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull. unfold nextKSAddr in *.
      unfold isKS in *. unfold nextKSentry in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr.
      rewrite Hs in HnextKSAddr. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      destruct (beqAddr currentPart nextKSaddr) eqn:HbeqCurrNextAddr; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull). unfold isKS in *.
      rewrite Hs. simpl. destruct (beqAddr currentPart nextKS) eqn:HbeqCurrNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR s).
    { (* BEGIN NextKSOffsetIsPADDR s *)
      assert(Hcons0: NextKSOffsetIsPADDR s1) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr HkernIsKS HnextAddr. unfold nextKSAddr in *. unfold isKS in *. rewrite Hs in HkernIsKS.
      rewrite Hs in HnextAddr. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 kernel nextKSaddr HkernIsKS HnextAddr). destruct Hcons0 as (Hcons0 & HbeqNextAddrNull).
      split; trivial. unfold isPADDR in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart nextKSaddr) eqn:HbeqCurrNextAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNextAddr. rewrite HbeqCurrNextAddr in *. rewrite HlookupCurrs1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(HgetFreeEq: forall partition, getFreeSlotsList partition s = getFreeSlotsList partition s1).
    {
      intro partition. unfold getFreeSlotsList. rewrite Hs. simpl.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs1. simpl.
        destruct (beqAddr (firstfreeslot pdentry) nullAddr) eqn:HbeqFirstNull; trivial.
        apply getFreeSlotsListRecEqPDT; try(unfold isBE); try(unfold isPADDR); try(rewrite HlookupCurrs1; intuition).
        intro Hcontra. rewrite <-beqAddrFalse in HbeqFirstNull.
        assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
        specialize(HfirstIsFree currentPart pdentry HlookupCurrs1 HbeqFirstNull). destruct HfirstIsFree as (HBE & _).
        unfold isBE in *. rewrite Hcontra in *. rewrite HlookupCurrs1 in *. congruence.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (lookup partition (memory s1) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
        apply getFreeSlotsListRecEqPDT; try(unfold isBE); try(unfold isPADDR); try(rewrite HlookupCurrs1; intuition).
        intro Hcontra. rewrite <-beqAddrFalse in HbeqFirstNull.
        assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
        specialize(HfirstIsFree partition p HlookupPart HbeqFirstNull). destruct HfirstIsFree as (HBE & _).
        unfold isBE in *. rewrite Hcontra in *. rewrite HlookupCurrs1 in *. congruence.
    }

    assert(NoDupInFreeSlotsList s).
    { (* BEGIN NoDupInFreeSlotsList s *)
      assert(Hcons0: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart.
      assert(Hparts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)).
      {
        rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - exists pdentry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. trivial.
        - exists pdentryPart. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct Hparts1 as [pdentryParts1 HlookupParts1]. specialize(Hcons0 partition pdentryParts1 HlookupParts1).
      rewrite HgetFreeEq. assumption.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot s).
    { (* BEGIN freeSlotsListIsFreeSlot s *)
      assert(Hcons0: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
      intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
      rewrite HgetFreeEq in HwellFormed. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDTs1 HwellFormed HaddrInList
        HbeqAddrNull). unfold isFreeSlot in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      destruct (lookup addr (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr currentPart (CPaddr (addr + sh1offset))) eqn:HbeqCurrSh1.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      destruct (lookup (CPaddr (addr + sh1offset)) (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr currentPart (CPaddr (addr + scoffset))) eqn:HbeqCurrSce.
      { rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(DisjointFreeSlotsLists s).
    { (* BEGIN DisjointFreeSlotsLists s *)
      assert(Hcons0: DisjointFreeSlotsLists s1) by (unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
      assert(Hpart1IsPDTs1: isPDT part1 s1).
      {
        unfold isPDT in *. rewrite Hs in Hpart1IsPDT. simpl in *.
        destruct (beqAddr currentPart part1) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part1. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(Hpart2IsPDTs1: isPDT part2 s1).
      {
        unfold isPDT in *. rewrite Hs in Hpart2IsPDT. simpl in *.
        destruct (beqAddr currentPart part2) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part2. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part1 part2 Hpart1IsPDTs1 Hpart2IsPDTs1 HbeqParts). rewrite HgetFreeEq. rewrite HgetFreeEq.
      assumption.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries s).
    { (* BEGIN inclFreeSlotsBlockEntries s *)
      assert(Hcons0: inclFreeSlotsBlockEntries s1) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition HpartIsPDTs1). rewrite HgetFreeEq. rewrite HgetKSEntriesEq. assumption.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries s).
    { (* BEGIN DisjointKSEntries s *)
      assert(Hcons0: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
      assert(Hpart1IsPDTs1: isPDT part1 s1).
      {
        unfold isPDT in *. rewrite Hs in Hpart1IsPDT. simpl in *.
        destruct (beqAddr currentPart part1) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part1. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(Hpart2IsPDTs1: isPDT part2 s1).
      {
        unfold isPDT in *. rewrite Hs in Hpart2IsPDT. simpl in *.
        destruct (beqAddr currentPart part2) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part2. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part1 part2 Hpart1IsPDTs1 Hpart2IsPDTs1 HbeqParts). rewrite HgetKSEntriesEq.
      rewrite HgetKSEntriesEq. assumption.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree s).
    { (* BEGIN noDupPartitionTree s *)
      assert(Hcons0: noDupPartitionTree s1) by (unfold consistency1 in *; intuition). unfold noDupPartitionTree in *.
      rewrite HgetPartsEqs. assumption.
      (* END noDupPartitionTree *)
    }

    assert(isParent s).
    { (* BEGIN isParent s *)
      assert(Hcons0: isParent s1) by (unfold consistency1 in *; intuition).
      intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEqs in *. rewrite HgetChildrenEq in *.
      specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. rewrite HbeqCurrPart in *. rewrite HlookupCurrs1 in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END isParent *)
    }

    assert(isChild s).
    { (* BEGIN isChild s *)
      assert(Hcons0: isChild s1) by (unfold consistency1 in *; intuition).
      intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEqs in *.
      assert(HparentIsParents1: pdentryParent partition pdparent s1).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - simpl in *. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. rewrite HbeqCurrPart in *. rewrite HlookupCurrs1.
          assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParents1 HbeqPartRoot). rewrite HgetChildrenEq.
      assumption.
      (* END isChild *)
    }

    assert(noDupKSEntriesList s).
    { (* BEGIN noDupKSEntriesList s *)
      assert(Hcons0: noDupKSEntriesList s1) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. rewrite HgetKSEntriesEq. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition HpartIsPDTs1). assumption.
      (* END noDupKSEntriesList *)
    }

    assert(noDupMappedBlocksList s).
    { (* BEGIN noDupMappedBlocksList s *)
      assert(Hcons0: noDupMappedBlocksList s1) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. rewrite HgetMappedEq. assert(HpartIsPDTs1: isPDT partition s1).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs1. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition HpartIsPDTs1). assumption.
      (* END noDupMappedBlocksList *)
    }

    assert(wellFormedBlock s).
    { (* BEGIN wellFormedBlock s *)
      assert(Hcons0: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr HPflag HstartBlock HendBlock. unfold bentryStartAddr in *.
      unfold bentryPFlag in *. unfold bentryEndAddr in *. rewrite Hs in HstartBlock. rewrite Hs in HendBlock.
      rewrite Hs in HPflag. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
      (* END wellFormedBlock *)
    }

    assert(parentOfPartitionIsPartition s).
    { (* BEGIN parentOfPartitionIsPartition s *)
      assert(Hcons0: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart.
      assert(Hparts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)
        /\ parent pdentryParts1 = parent pdentryPart).
      {
        rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - exists pdentry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. split; trivial.
          injection HlookupPart as HlookupPart. rewrite <-HlookupPart. simpl. reflexivity.
        - exists pdentryPart. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hparts1 as [pdentryParts1 (HlookupParts1 & HparentEq)].
      specialize(Hcons0 partition pdentryParts1 HlookupParts1). rewrite HparentEq in *. rewrite HgetPartsEqs.
      split; try(apply Hcons0). destruct Hcons0 as (Hcons0 & _). intro HbeqPartRoot. specialize(Hcons0 HbeqPartRoot).
      split; try(apply Hcons0). destruct Hcons0 as ([parentEntry Hlookup] & _). rewrite Hs. simpl.
      destruct (beqAddr currentPart (parent pdentryPart)) eqn:HbeqCurrParent.
      - exists {|
                 structure := structure pdentry;
                 firstfreeslot := firstfreeslot pdentry;
                 nbfreeslots := nbfreeslots pdentry;
                 nbprepare := nbprepare pdentry;
                 parent := parent pdentry;
                 MPU := MAL.removeBlockFromPhysicalMPUAux requisitionedBlockInCurrPartAddr realMPU;
                 vidtAddr := vidtAddr pdentry
               |}. reflexivity.
      - exists parentEntry. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END parentOfPartitionIsPartition *)
    }

    assert(NbFreeSlotsISNbFreeSlotsInList s).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s1) by (unfold consistency1 in *; intuition).
      intros partition nbfreeslots HpartIsPDT HnbFree.
      assert(Hparts1: isPDT partition s1 /\ pdentryNbFreeSlots partition nbfreeslots s1).
      {
        unfold isPDT in *. unfold pdentryNbFreeSlots in *. rewrite Hs in HpartIsPDT. rewrite Hs in HnbFree.
        simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs1. split; trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hparts1 as (HpartIsPDTs1 & HnbFrees1). specialize(Hcons0 partition nbfreeslots HpartIsPDTs1 HnbFrees1).
      rewrite HgetFreeEq. assumption.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(maxNbPrepareIsMaxNbKernels s).
    { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s1) by (unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. specialize(Hcons0 partition kernList). apply Hcons0.
      revert HlistOfKerns. rewrite Hs. apply isListOfKernelsEqPDT with pdentry; intuition.
      (* END maxNbPrepareIsMaxNbKernels *)
    }

    assert(blockInChildHasAtLeastEquivalentBlockInParent s).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s1)
        by (unfold consistency1 in *; intuition). intros pdparent child block startChild endChild
        HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild. rewrite HgetPartsEqs in *.
      rewrite HgetChildrenEq in *. rewrite HgetMappedEq in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      unfold bentryPFlag in *. rewrite Hs in HstartChild. rewrite Hs in HendChild. rewrite Hs in HPflagChild.
      simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        HstartChild HendChild HPflagChild).
      destruct Hcons0 as [blockParent [startParent [endParent (HblockPMapped & HstartP & HendP & Hbounds)]]].
      exists blockParent. exists startParent. exists endParent. split; trivial. rewrite Hs. simpl.
      destruct (beqAddr currentPart blockParent) eqn:HbeqCurrParent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite HbeqCurrParent in *. unfold bentryStartAddr in *.
        rewrite HlookupCurrs1 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split; try(split));
        trivial.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(partitionTreeIsTree s).
    { (* BEGIN partitionTreeIsTree s *)
      assert(Hcons0: partitionTreeIsTree s1) by (unfold consistency1 in *; intuition).
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
      rewrite HgetPartsEqs in *. assert(HparentIsParents1: pdentryParent child pdparent s1).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in *.
        destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. rewrite HlookupCurrs1. simpl in *. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParents1). apply Hcons0.
      destruct parentsList; try(simpl; trivial; congruence).
      apply isParentsListEqPDTSameParent with currentPart {|
                  structure := structure pdentry;
                  firstfreeslot := firstfreeslot pdentry;
                  nbfreeslots := nbfreeslots pdentry;
                  nbprepare := nbprepare pdentry;
                  parent := parent pdentry;
                  MPU := MAL.removeBlockFromPhysicalMPUAux requisitionedBlockInCurrPartAddr realMPU;
                  vidtAddr := vidtAddr pdentry
                |} s; try(assumption); simpl.
      - rewrite Hs. simpl. destruct (beqAddr currentPart pdparent) eqn:HbeqCurrParent.
        + rewrite <-DTL.beqAddrTrue in HbeqCurrParent. subst pdparent. exists pdentry.
          exists {|
                   structure := structure pdentry;
                   firstfreeslot := firstfreeslot pdentry;
                   nbfreeslots := nbfreeslots pdentry;
                   nbprepare := nbprepare pdentry;
                   parent := parent pdentry;
                   MPU := MAL.removeBlockFromPhysicalMPUAux requisitionedBlockInCurrPartAddr realMPU;
                   vidtAddr := vidtAddr pdentry
                 |}. exists pdentry. intuition.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; trivial). simpl in *.
          destruct (lookup p (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
          destruct HparentsList as (_ & [pdentryPart (HlookupP & _)] & _). rewrite Hs in HlookupP. simpl in *.
          rewrite beqAddrFalse in HbeqCurrParent. rewrite HbeqCurrParent in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial). exists pdentryPart. exists pdentryPart.
          exists pdentry. split; trivial. split; trivial. split; trivial. split; trivial. split.
          * intro. reflexivity.
          * intro Hcontra. exfalso; congruence.
      - unfold consistency1 in *; intuition.
      (* END partitionTreeIsTree *)
    }

    assert(nextKernelIsValid s).
    { (* BEGIN nextKernelIsValid s *)
      assert(Hcons0: nextKernelIsValid s1) by (unfold consistency1 in *; intuition).
      intros kernel HkernIsKS. unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      specialize(Hcons0 kernel HkernIsKS). destruct Hcons0 as (HlebNextMax & [nextKSaddr (HlookupNextA & HnextIsKS)]).
      split; trivial. exists nextKSaddr. split.
      - intro Hp. specialize(HlookupNextA Hp). rewrite Hs. simpl.
        destruct (beqAddr currentPart {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqCurrNext.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. rewrite HlookupCurrs1 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      - destruct HnextIsKS as [HnextIsKS | HnextIsNull]; try(right; assumption). left. rewrite Hs. simpl.
        unfold isKS in *. destruct (beqAddr currentPart nextKSaddr) eqn:HbeqCurrNext.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. rewrite HlookupCurrs1 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns s).
    { (* BEGIN noDupListOfKerns s *)
      assert(Hcons0: noDupListOfKerns s1) by (unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. specialize(Hcons0 partition). apply Hcons0. revert HlistOfKerns.
      rewrite Hs. apply isListOfKernelsEqPDT with pdentry; intuition.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax s).
    { (* BEGIN MPUsizeIsBelowMax s *)
      assert(Hcons0: MPUsizeIsBelowMax s1) by (unfold consistency1 in *; intuition).
      intros partition MPUlist HMPUBlock. unfold pdentryMPU in *. rewrite Hs in HMPUBlock. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. rewrite HbeqCurrPart in *.
        specialize(Hcons0 partition realMPU HMPU).
        subst MPUlist. simpl. assert(length (MAL.removeBlockFromPhysicalMPUAux requisitionedBlockInCurrPartAddr
           realMPU) <= length realMPU) by apply removeBlockFromPhysicalMPUAuxLenEq. lia.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
        specialize(Hcons0 partition MPUlist HMPUBlock). assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart s).
    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s1) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEqs in *. rewrite HgetMappedEq in *. unfold scentryOrigin in *. rewrite Hs in Horigin.
      simpl in *. destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      assert(Hparts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)
        /\ parent pdentryParts1 = parent pdentryPart).
      {
        rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - exists pdentry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. split; trivial.
          injection HlookupPart as HlookupPart. rewrite <-HlookupPart. simpl. reflexivity.
        - exists pdentryPart. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hparts1 as [pdentryParts1 (HlookupParts1 & HparentEq)].
      specialize(Hcons0 partition pdentryParts1 block scentryaddr scorigin HpartIsPart HlookupParts1 HblockMapped Hsce
        Horigin). destruct Hcons0 as (Hincl & HlebStart). rewrite HparentEq in *. split.
      - intro HbeqPartRoot. specialize(Hincl HbeqPartRoot).
        destruct Hincl as [blockParent (HPmapped & HstartP & Hincl)]. exists blockParent. split; trivial.
        unfold bentryStartAddr in *. rewrite Hs. simpl. destruct (beqAddr currentPart blockParent) eqn:HbeqCurrParent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite HbeqCurrParent in *. rewrite HlookupCurrs1 in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. split. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        intros addr HaddrInBlock.
        destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(simpl in *; exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
        specialize(Hincl addr HaddrInBlock). assumption.
      - intros startaddr HstartBlock. unfold bentryStartAddr in *. apply HlebStart. rewrite Hs in HstartBlock.
        simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(simpl in *; exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut s).
    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s1) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
        Hsce HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEqs in *. rewrite HgetMappedEq in *.
      assert(Hparts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)
        /\ parent pdentryParts1 = parent pdentryPart).
      {
        rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - exists pdentry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. split; trivial.
          injection HlookupPart as HlookupPart. rewrite <-HlookupPart. simpl. reflexivity.
        - exists pdentryPart. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hparts1 as [pdentryParts1 (HlookupParts1 & HparentEq)]. unfold bentryEndAddr in *.
      rewrite Hs in HendBlock. unfold scentryNext in *. rewrite Hs in Hnext. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      specialize(Hcons0 partition pdentryParts1 block scentryaddr scnext endaddr HpartIsPart HlookupParts1
        HblockMapped HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockPMapped & HendP & HltEnd & Hincl)]]. exists blockParent.
      exists endParent. rewrite HparentEq in *. split; trivial. apply mappedBlockIsBE in HblockMapped.
      destruct HblockMapped as [bentryB (HlookupBlock & _)]. unfold bentryEndAddr in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart blockParent) eqn:HbeqCurrParent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite HbeqCurrParent in *. rewrite HlookupCurrs1 in *.
        exfalso; congruence.
      }
      rewrite beqAddrFalse in HbeqCurrBlock. rewrite HbeqCurrBlock. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; trivial).
      rewrite removeDupIdentity; try(apply not_eq_sym; trivial). simpl in *. intuition.
      (* END nextImpliesBlockWasCut *)
    }

    assert(blocksAddressesTypes s).
    { (* BEGIN blocksAddressesTypes s *)
      assert(Hcons0: blocksAddressesTypes s1) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock.
      rewrite HgetPartsEqs in *. rewrite HgetMappedEq in *.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold sh1entryPDchild in *. rewrite Hs in HstartBlock.
      rewrite Hs in HendBlock. rewrite Hs in HPDchildBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      specialize(Hcons0 block startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock).
      destruct Hcons0 as [(HKS & HblockRange) | [(HPDT & HblockRange) | Hnone]].
      - left. split.
        + unfold isKS in *. rewrite Hs. simpl. destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrStart. rewrite HbeqCurrStart in *. rewrite HlookupCurrs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrInRange. specialize(HblockRange addr HaddrInRange).
          destruct HblockRange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
          * left. unfold isBE in *. rewrite Hs. simpl. destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. rewrite HbeqCurrAddr in *. rewrite HlookupCurrs1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. left. unfold isSHE in *. rewrite Hs. simpl. destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. rewrite HbeqCurrAddr in *. rewrite HlookupCurrs1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. left. unfold isSCE in *. rewrite Hs. simpl.
            destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. rewrite HbeqCurrAddr in *. rewrite HlookupCurrs1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. right. left. unfold isPADDR in *. rewrite Hs. simpl.
            destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. rewrite HbeqCurrAddr in *. rewrite HlookupCurrs1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. right. right. rewrite Hs. simpl.
            destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. rewrite HbeqCurrAddr in *. rewrite HlookupCurrs1 in *.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. left. split.
        + unfold isPDT. rewrite Hs. simpl. destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart; trivial.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrInRange. specialize(HblockRange addr HaddrInRange). rewrite Hs. simpl.
          destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. rewrite HbeqCurrAddr in *. rewrite HlookupCurrs1 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. right. intros addr HaddrInRange. specialize(Hnone addr HaddrInRange). rewrite Hs. simpl.
        destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. rewrite HbeqCurrAddr in *. rewrite HlookupCurrs1 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END blocksAddressesTypes *)
    }

    assert(notPDTIfNotPDflag s).
    { (* BEGIN notPDTIfNotPDflag s *)
      assert(Hcons0: notPDTIfNotPDflag s1) by (unfold consistency1 in *; intuition).
      intros block startaddr sh1entryaddr part HpartIsPart HblockMapped HstartBlock Hsh1 HPDflagBlock HPDchildBlock.
      unfold bentryStartAddr in *. rewrite HgetPartsEqs in *. rewrite HgetMappedEq in *.
      unfold sh1entryAddr in *. unfold sh1entryPDflag in *. unfold sh1entryPDchild in *. rewrite Hs in HstartBlock.
      rewrite Hs in Hsh1. rewrite Hs in HPDflagBlock. rewrite Hs in HPDchildBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      specialize(Hcons0 block startaddr sh1entryaddr part HpartIsPart HblockMapped HstartBlock Hsh1 HPDflagBlock
        HPDchildBlock). rewrite Hs.
      contradict Hcons0. unfold isPDT in *. simpl in *.
      destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrStart. rewrite HbeqCurrStart in *. rewrite HlookupCurrs1. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END notPDTIfNotPDflag *)
    }

    assert(nextKernAddrIsInSameBlock s).
    { (* BEGIN nextKernAddrIsInSameBlock s *)
      assert(Hcons0: nextKernAddrIsInSameBlock s1) by (unfold consistency1 in *; intuition).
      intros block kernel startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock
        HkernIsKS. rewrite HgetPartsEqs in *. rewrite HgetMappedEq in *.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold sh1entryPDchild in *.
      unfold isKS in *. rewrite Hs in HstartBlock. rewrite Hs in HendBlock. rewrite Hs in HPDchildBlock.
      rewrite Hs in HkernIsKS. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      specialize(Hcons0 block kernel startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock
        HPDchildBlock HkernIsKS). assumption.
      (* END nextKernAddrIsInSameBlock *)
    }

    (*assert(blockBelongsToAPart s).
    { (* BEGIN blockBelongsToAPart s *)
      assert(Hcons0: blockBelongsToAPart s1) by (unfold consistency1 in *; intuition).
      intros block HPflagBlock. unfold bentryPFlag in *. rewrite Hs in HPflagBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      specialize(Hcons0 block HPflagBlock). rewrite HgetPartsEqs. destruct Hcons0 as [part Hcons0]. exists part.
      rewrite HgetMappedEq. assumption.
      (* END blockBelongsToAPart *)
    }*)

    assert(PDflagMeansNoChild s).
    { (* BEGIN PDflagMeansNoChild s *)
      assert(Hcons0: PDflagMeansNoChild s1) by (unfold consistency1 in *; intuition).
      intros block HblockIsBE HPDflagBlock. unfold isBE in *. unfold sh1entryPDflag in *. unfold sh1entryPDchild.
      rewrite Hs in HblockIsBE. rewrite Hs in HPDflagBlock. rewrite Hs. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      specialize(Hcons0 block HblockIsBE HPDflagBlock). assumption.
      (* END PDflagMeansNoChild *)
    }

    assert(nbPrepareIsNbKern s).
    { (* BEGIN nbPrepareIsNbKern s *)
      assert(Hcons0: nbPrepareIsNbKern s1) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart.
      assert(HlookupParts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)
        /\ structure pdentryParts1 = structure pdentryPart /\ nbprepare pdentryParts1 = nbprepare pdentryPart).
      {
        rewrite Hs in HlookupPart. simpl in HlookupPart. destruct (beqAddr currentPart partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition.
          exists pdentry. split; trivial. injection HlookupPart as HlookupPart. rewrite <-HlookupPart. simpl.
          split; reflexivity.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
          exists pdentryPart. split; trivial. split; trivial.
      }
      destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HstructEq & HnbPrepEq)]. rewrite <-HstructEq.
      rewrite <-HnbPrepEq. specialize(Hcons0 partition pdentryParts1 HlookupParts1). rewrite Hs.
      rewrite completeListOfKernelsEqPDT; trivial. unfold isPDT. rewrite HlookupCurrs1. trivial.
      (* END nbPrepareIsNbKern *)
    }

    assert(pdchildIsPDT s).
    { (* BEGIN pdchildIsPDT s *)
      assert(Hcons0: pdchildIsPDT s1) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull.
      rewrite HgetPartsEqs in *. rewrite HgetMappedEq in *. rewrite HgetChildrenEq. unfold sh1entryAddr in *.
      unfold sh1entryPDchild in *. rewrite Hs in Hsh1. rewrite Hs in HPDchildB. simpl in Hsh1. simpl in HPDchildB.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull).
      assumption.
      (* END pdchildIsPDT *)
    }

    assert(childBlockNullIfChildNull s).
    { (* BEGIN childBlockNullIfChildNull s *)
      assert(Hcons0: childBlockNullIfChildNull s1) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchildB. rewrite HgetPartsEqs in *.
      rewrite HgetMappedEq in *. unfold sh1entryAddr in *. unfold sh1entryInChildLocation. rewrite Hs. simpl.
      unfold sh1entryPDchild in *. rewrite Hs in Hsh1. rewrite Hs in HPDchildB. simpl in Hsh1. simpl in HPDchildB.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchildB).
      unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). destruct Hcons0. split; trivial. intro. exfalso; congruence.
      (* END childBlockNullIfChildNull *)
    }

    assert(accessibleBlocksArePresent s).
    { (* BEGIN accessibleBlocksArePresent s *)
      assert(Hcons0: accessibleBlocksArePresent s1) by (unfold consistency1 in *; intuition).
      intros block HAflag. unfold bentryAFlag in *. unfold bentryPFlag. rewrite Hs in HAflag. rewrite Hs. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      apply Hcons0; assumption.
      (* END childLocHasSameStart *)
    }

    assert(sharedBlockIsPresent s).
    { (* BEGIN sharedBlockIsPresent s *)
      assert(Hcons0: sharedBlockIsPresent s1) by (unfold consistency1 in *; intuition).
      intros part block child HpartIsPart HblockIsEntry HPDchildB HbeqChildNull. rewrite HgetPartsEqs in *.
      rewrite HgetKSEntriesEq in *. unfold sh1entryPDchild in *. rewrite Hs in HPDchildB. simpl in HPDchildB.
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block child HpartIsPart HblockIsEntry HPDchildB HbeqChildNull). unfold bentryPFlag in *.
      rewrite Hs. simpl. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrBlock. subst block. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      (* END sharedBlockIsPresent *)
    }

    assert(HgetConfigBEqs: forall part, isPDT part s1 -> getConfigBlocks part s = getConfigBlocks part s1).
    {
      intros part HpartIsPDT. rewrite Hs. apply getConfigBlocksEqPDT with pdentry; auto.
    }

    assert(sharedBlockNoPDflagNoLocIsKern s).
    { (* BEGIN sharedBlockNoPDflagNoLocIsKern s *)
      assert(Hcons0: sharedBlockNoPDflagNoLocIsKern s1) by (unfold consistency1 in *; intuition).
      intros part block child startaddr HpartIsPart HblockIsEntry HPDchildB HbeqChildNull HPDflagB Hloc Hstart.
      rewrite HgetPartsEqs in *. rewrite HgetKSEntriesEq in *.  unfold sh1entryPDchild in *. rewrite Hs in HPDchildB.
      unfold sh1entryPDflag in *. rewrite Hs in HPDflagB. unfold sh1entryInChildLocationWeak in *. rewrite Hs in Hloc.
      simpl in HPDchildB. simpl in HPDflagB. simpl in Hloc. unfold bentryStartAddr in *. rewrite Hs in Hstart.
      simpl in Hstart. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block child startaddr HpartIsPart HblockIsEntry HPDchildB HbeqChildNull HPDflagB Hloc
        Hstart). rewrite HgetConfigBEqs; trivial. unfold getConfigBlocks in *. unfold isPDT.
      destruct (lookup child (memory s1) beqAddr); try(simpl in Hcons0; congruence).
      destruct v; try(simpl in Hcons0; congruence). trivial.
      (* END sharedBlockNoPDflagNoLocIsKern *)
    }

    assert(partitionNotAutoMapped s).
    { (* BEGIN partitionNotAutoMapped s *)
      assert(Hcons0: partitionNotAutoMapped s1) by (unfold consistency1 in *; intuition).
      intros part HpartIsPart. rewrite HgetPartsEqs in *. specialize(Hcons0 part HpartIsPart).
      assert(isPDT part s0).
      { rewrite HgetPartsEqs1 in *; apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedPaddrEq; trivial. rewrite <-HgetMappedPEqs1s0; trivial.
      (* END partitionNotAutoMapped *)
    }

    assert(configAddrNotMappedInChild s).
    { (* BEGIN configAddrNotMappedInChild s *)
      assert(Hcons0: configAddrNotMappedInChild s1) by (unfold consistency1 in *; intuition).
      intros part child addr HpartIsPart HchildIsChild HaddrIsConfig. rewrite HgetPartsEqs in *.
      rewrite HgetChildrenEq in *. assert(isPDT part s0).
      { rewrite HgetPartsEqs1 in *; apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetConfigPaddrEq in *; trivial. rewrite <-HgetConfigEqs1s0 in *; trivial.
      specialize(Hcons0 part child addr HpartIsPart HchildIsChild HaddrIsConfig).
      assert(isPDT child s0).
      {
        rewrite HgetChildrenEqs1 in *; trivial. rewrite HgetPartsEqs1 in *.
        apply childrenArePDT with part; trivial; unfold consistency1 in *; intuition.
      }
      rewrite HgetMappedPaddrEq; trivial. rewrite <-HgetMappedPEqs1s0; trivial.
     (* END configAddrNotMappedInChild *)
    }

    (* assert(configNotMappedRoot s).
    { (* BEGIN configNotMappedRoot s *)
      assert(Hcons0: configNotMappedRoot s1) by (unfold consistency1 in *; intuition).
      intros addr HaddrIsConfig. assert(isPDT multiplexer s0) by (unfold consistency1 in *; intuition).
      rewrite HgetConfigPaddrEq in *; trivial. rewrite <-HgetConfigEqs1s0 in *; trivial.
      specialize(Hcons0 addr HaddrIsConfig). rewrite HgetMappedPaddrEq; trivial.
      rewrite <-HgetMappedPEqs1s0; trivial.
     (* END configNotMappedRoot *)
    } *)

    assert(fullKernelIsInOneBlock s).
    { (* BEGIN fullKernelIsInOneBlock s *)
      assert(Hcons0: fullKernelIsInOneBlock s1) by (unfold consistency1 in *; intuition).
      intros part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKS. rewrite HgetPartsEqs in *.
      rewrite HgetMappedEq in *. rewrite Hs in HkernInBlock. unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs.
      simpl in HkernIsKS. simpl in HkernInBlock. simpl.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(simpl in HkernInBlock; exfalso; congruence).
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKS). assumption.
     (* END fullKernelIsInOneBlock *)
    }

    assert(sharedBlocksAdressesAreAllMappedInChild s).
    { (* BEGIN sharedBlocksAdressesAreAllMappedInChild s *)
      assert(Hcons0: sharedBlocksAdressesAreAllMappedInChild s1) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1 HPDchildB Hloc HbeqChildNull
        HbeqLocNull addr HaddrInBlock. rewrite HgetPartsEqs in *. rewrite HgetMappedEq in *. unfold sh1entryAddr in *.
      rewrite Hs in HaddrInBlock. unfold sh1entryPDchild in *. unfold sh1entryInChildLocationWeak in *.
      rewrite Hs in Hsh1. rewrite Hs in HPDchildB. rewrite Hs in Hloc. simpl in HPDchildB. simpl in HaddrInBlock.
      simpl in Hsh1. simpl in Hloc. destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1 HPDchildB Hloc
        HbeqChildNull HbeqLocNull addr HaddrInBlock). assert(isPDT child s0).
      {
        unfold getMappedPaddr in *. unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
        destruct (lookup child (memory s1) beqAddr) eqn:HlookupChilds1; try(simpl in Hcons0; exfalso; congruence).
        destruct v; try(simpl in Hcons0; exfalso; congruence). rewrite Hs1 in HlookupChilds1. simpl in HlookupChilds1.
        destruct (beqAddr requisitionedBlockInCurrPartAddr child) eqn:HbeqBlockChild; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite HlookupChilds1. trivial.
      }
      rewrite HgetMappedPaddrEq; trivial. rewrite <-HgetMappedPEqs1s0; trivial.
     (* END sharedBlocksAdressesAreAllMappedInChild *)
    }

    unfold consistency1. intuition.
  }
  split.
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
    rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. rewrite HgetChildrenEq in *.
    assert(isPDT pdparent s0).
    { apply partitionsArePDT; try(assumption); unfold consistency1 in *; intuition. }
    rewrite HgetChildrenEqs1 in Hchild1IsChild; trivial.
    rewrite HgetChildrenEqs1 in Hchild2IsChild; trivial. assert(isPDT child1 s0).
    { apply childrenArePDT with pdparent; try(assumption); unfold consistency1 in *; intuition. }
    assert(isPDT child2 s0).
    { apply childrenArePDT with pdparent; try(assumption); unfold consistency1 in *; intuition. }
    specialize(HPIs0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
    unfold getUsedPaddr in *. rewrite HgetMappedPaddrEq; trivial. rewrite HgetConfigPaddrEq; trivial.
    rewrite HgetMappedPaddrEq; trivial. rewrite HgetConfigPaddrEq; trivial.
    (* END partitionsIsolation *)
  }

  instantiate(2:= requisitionedBlockStart). instantiate(1:= requisitionedBlockEnd).

  assert(HgetAccMappedPaddrIncl: forall partition addr, isPDT partition s0
    -> In addr (getAccessibleMappedPaddr partition s) -> In addr (getAccessibleMappedPaddr partition s0)).
  {
    intros partition addr HpartIsPDT HaddrAccPart.
    assert(Heq: getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s1).
    {
      rewrite Hs. apply getAccessibleMappedPaddrEqPDT with pdentry; trivial; unfold consistency1 in *; intuition.
    }
    rewrite Heq in *. revert HaddrAccPart. rewrite Hs1.
    apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleFalseInclusion with bentry; trivial. simpl.
    unfold bentryPFlag in *. rewrite HlookupBlocks0 in *. apply eq_sym. assumption.
  }

  split.
  { (* BEGIN kernelDataIsolation s *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart addr HaddrAccPart1. rewrite HgetPartsEqs in *.
    rewrite HgetPartsEqs1 in *. assert(isPDT part1 s0).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    apply HgetAccMappedPaddrIncl in HaddrAccPart1; trivial. assert(isPDT part2 s0).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetConfigPaddrEq; trivial. specialize(HKDIs0 part1 part2 Hpart1IsPart Hpart2IsPart addr HaddrAccPart1).
    assumption.
    (* END kernelDataIsolation *)
  }
  split.
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild. rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *.
    assert(isPDT pdparent s0).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetChildrenEq in *. rewrite HgetChildrenEqs1 in HchildIsChild; trivial.
    specialize(HVSs0 pdparent child HparentIsPart HchildIsChild). unfold getUsedPaddr. assert(isPDT child s0).
    { apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetConfigPaddrEq; trivial. rewrite HgetMappedPaddrEq; trivial. rewrite HgetMappedPaddrEq; trivial.
    (* END verticalSharing *)
  }
  split. assumption. assert(HnoDups: noDupMappedPaddrList s).
  { (* BEGIN noDupMappedPaddrList s *)
    intros partition HpartIsPDT. assert(HpartIsPDTs0: isPDT partition s0).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite Hs1 in HlookupCurrs1. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
        rewrite HlookupCurrs1. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
        rewrite Hs1 in HpartIsPDT. simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(HnoDups0 partition HpartIsPDTs0). rewrite HgetMappedPaddrEq; trivial.
    (* END noDupMappedPaddrList *)
  }
  split; trivial. split.
  { (* BEGIN sharedBlockPointsToChild s *)
    intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild HaddrInBlockParent
      HblockParentMapped Hsh1. rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. assert(isPDT pdparent s0).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetChildrenEq in *. rewrite HgetChildrenEqs1 in *; trivial. rewrite HgetMappedEq in *.
    rewrite HgetMappedEqs1 in *. unfold getUsedPaddr in *. assert(isPDT child s0).
    { apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetConfigPaddrEq in *; trivial. rewrite HgetMappedPaddrEq in *; trivial.
    assert(Hblocks0: In addr (getAllPaddrAux [blockParent] s0) /\ sh1entryAddr blockParent sh1entryaddr s0).
    {
      unfold sh1entryAddr in *. rewrite Hs in HaddrInBlockParent. rewrite Hs in Hsh1. simpl in *.
      destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlock; try(exfalso; simpl in *; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HaddrInBlockParent. rewrite Hs1 in Hsh1. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlockBlockP.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockBlockP. subst blockParent. rewrite HlookupBlocks0. split; trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
    }
    destruct Hblocks0 as (HaddrInBlockParents0 & Hsh1s0). rewrite Hs1 in HlookupCurrs1. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    specialize(Hshareds0 pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParents0 HblockParentMapped Hsh1s0). destruct Hshareds0 as [HPDchildB | HPDflagB].
    1: left; unfold sh1entryPDchild in *. 2: right; unfold sh1entryPDflag in *.
    1,2: rewrite Hs; simpl; destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrSh1;
      try(rewrite <-DTL.beqAddrTrue in HbeqCurrSh1; rewrite HbeqCurrSh1 in *; rewrite HlookupCurrs1 in *; congruence);
      rewrite <-beqAddrFalse in *; rewrite removeDupIdentity; try(apply not_eq_sym; trivial); rewrite Hs1; simpl;
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlockSh1;
      try(rewrite <-DTL.beqAddrTrue in HbeqBlockSh1; rewrite HbeqBlockSh1 in *; rewrite HlookupBlocks0 in *;
      congruence); rewrite <-beqAddrFalse in *; rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END sharedBlockPointsToChild *)
  }
  split.
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
    intros partition pdentryPart block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE HstartBlock
      HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot.
    assert(Hblocks0: isBE block s0 /\ bentryStartAddr block startBlock s0 /\ bentryEndAddr block endBlock s0
      /\ bentryPFlag block true s0).
    {
      unfold isBE in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
      rewrite Hs in HblockIsBE. rewrite Hs in HstartBlock. rewrite Hs in HendBlock. rewrite Hs in HPflag. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      rewrite Hs1 in HblockIsBE. rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock. rewrite Hs1 in HPflag.
      simpl in *. destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. simpl in *. intuition.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). intuition.
    }
    destruct Hblocks0 as (HblockIsBEs0 & HstartBlocks0 & HendBlocks0 & HPflagBlocks0).
    rewrite Hs1 in HlookupCurrs1. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    assert(Hparts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
      /\ parent pdentryParts0 = parent pdentryPart).
    {
      rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - exists pdentry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. split; trivial.
        injection HlookupPart as HlookupPart. rewrite <-HlookupPart. simpl. reflexivity.
      - exists pdentryPart. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial. rewrite Hs1 in HlookupPart.
        simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    destruct Hparts0 as [pdentryParts0 (HlookupParts0 & HparentEq)]. rewrite HgetPartsEqs in *.
    rewrite HgetPartsEqs1 in *. rewrite HgetMappedEq in *. rewrite HgetMappedEqs1 in *. unfold scentryOrigin in *.
    unfold scentryNext in *. rewrite Hs in Horigin. rewrite Hs in Hnext. simpl in *.
    destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    rewrite Hs1 in Horigin. rewrite Hs1 in Hnext. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    specialize(Hranges0 partition pdentryParts0 block scentryaddr startBlock endBlock HpartIsPart HblockMapped
      HblockIsBEs0 HstartBlocks0 HendBlocks0 HPflagBlocks0 Hsce Horigin Hnext HlookupParts0 HbeqPartRoot).
    rewrite HparentEq in *. destruct Hranges0 as [blockParent (HblockPMapped & HblockPIsBE & HstartP & HendP)].
    exists blockParent. split; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold isBE in *.
    rewrite Hs. simpl. destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBlockP. subst blockParent. rewrite HlookupCurrs1 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; trivial). rewrite Hs1. simpl.
    destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlockBlockP.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockBlockP. subst blockParent. rewrite HlookupBlocks0 in *. simpl; intuition.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; trivial). intuition.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }
  assert(HchildBlockPropss: childsBlocksPropsInParent s).
  { (* BEGIN childsBlocksPropsInParent s *)
    intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart HchildIsChild
      HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent HPflagParent
      HlebStart HgebEnd. rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEq in *.
    rewrite HgetMappedEqs1 in *.
    assert(Hblocks0: bentryStartAddr blockChild startChild s0 /\ bentryEndAddr blockChild endChild s0
      /\ bentryPFlag blockChild true s0).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
      rewrite Hs in HstartChild. rewrite Hs in HendChild. rewrite Hs in HPflagChild. simpl in *.
      destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      rewrite Hs1 in HstartChild. rewrite Hs1 in HendChild. rewrite Hs1 in HPflagChild.
      simpl in *. destruct (beqAddr requisitionedBlockInCurrPartAddr blockChild) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockChild. rewrite HlookupBlocks0. simpl in *. intuition.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). intuition.
    }
    destruct Hblocks0 as (HstartChilds0 & HendChilds0 & HPflagChilds0).
    assert(HblockPs0: bentryStartAddr blockParent startParent s0 /\ bentryEndAddr blockParent endParent s0
      /\ bentryPFlag blockParent true s0).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
      rewrite Hs in HstartParent. rewrite Hs in HendParent. rewrite Hs in HPflagParent. simpl in *.
      destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
      rewrite Hs1 in HstartParent. rewrite Hs1 in HendParent. rewrite Hs1 in HPflagParent.
      simpl in *. destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0. simpl in *. intuition.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption). intuition.
    }
    destruct HblockPs0 as (HstartParents0 & HendParents0 & HPflagParents0). rewrite HgetChildrenEq in *.
    assert(isPDT pdparent s0).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetChildrenEqs1 in *; trivial.
    specialize(HchildBlockPropss0 child pdparent blockChild startChild endChild blockParent startParent endParent
      HparentIsPart HchildIsChild HblockChildMapped HstartChilds0 HendChilds0 HPflagChilds0 HblockParentMapped
      HstartParents0 HendParents0 HPflagParents0 HlebStart HgebEnd).
    rewrite Hs1 in HlookupCurrs1. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    destruct HchildBlockPropss0 as (HcheckChild & HPDchildP & HchildLocP & HAflagP). unfold checkChild in *.
    unfold sh1entryPDchild. unfold sh1entryInChildLocation. unfold bentryAFlag in *. unfold bentryPFlag in *.
    rewrite Hs. simpl.
    destruct (beqAddr currentPart blockParent) eqn:HbeqCurrParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrParent. subst blockParent. rewrite HlookupCurrs1 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; trivial).
    split; try(split; try(split)).
    - rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlocks.
      + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0 in *.
        destruct (beqAddr currentPart (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset))) eqn:HbeqCurrSh1; trivial.
        rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)))
          eqn:HbeqBlockSh1; trivial. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym; trivial).
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; trivial).
        destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrSh1; trivial.
        rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlockSh1;
          trivial. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; trivial).
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - intro childGlobalID. destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrSh1.
      { intro. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlockSh1.
      { intro. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. apply HPDchildP.
    - intros blockIDInChild HchildLoc. apply HchildLocP. unfold sh1entryInChildLocation.
      destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HchildLoc. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlockSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HchildLoc as (Hloc & HlocIsBE). split; trivial. intro HbeqLocNull.
      specialize(HlocIsBE HbeqLocNull). unfold isBE in *. simpl in *.
      destruct (beqAddr currentPart blockIDInChild) eqn:HbeqCurrLoc; try(exfalso; congruence).
      rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr in *. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr blockIDInChild) eqn:HbeqBlockLoc.
      + rewrite <-DTL.beqAddrTrue in HbeqBlockLoc. rewrite HbeqBlockLoc in *. rewrite HlookupBlocks0. trivial.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    - intro HboundsWrong. specialize(HAflagP HboundsWrong). rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlockBlockP.
      + trivial.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END childsBlocksPropsInParent *)
  }
  split; trivial. split.
  { (* BEGIN noChildImpliesAddressesNotShared s *)
    rewrite Hs1 in HlookupCurrs1. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    intros partition pdentryPart block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchildBlock child addr
      HchildIsChild HaddrInBlock. rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEq in *.
    rewrite HgetMappedEqs1 in *. rewrite HgetChildrenEq in *.
    assert(isPDT partition s0).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetChildrenEqs1 in *; trivial. assert(isPDT child s0).
    { apply childrenArePDT with partition; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedPaddrEq; trivial.
    assert(Hparts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)).
    {
      rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - exists pdentry. rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. trivial.
      - exists pdentryPart. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HlookupPart.
        simpl in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    destruct Hparts0 as [pdentryParts0 HlookupParts0].
    assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
    {
      rewrite Hs in HaddrInBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; simpl in *; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HaddrInBlock. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    unfold sh1entryPDchild in *. rewrite Hs in HPDchildBlock. simpl in HPDchildBlock.
    destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HPDchildBlock. simpl in HPDchildBlock.
    destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(HnoChilds0 partition pdentryParts0 block sh1entryaddr). apply HnoChilds0; trivial.
    (* END noChildImpliesAddressesNotShared *)
  }
  split.
  { (* BEGIN partial kernelsAreNotAccessible s *)
    rewrite Hs1 in HlookupCurrs1. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    intros block startBlock part HbeqStarts HpartIsPart HblockMapped HstartBlock HstartIsKS.
    rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEq in *. rewrite HgetMappedEqs1 in *.
    assert(HstartIsKSs0: isKS startBlock s0).
    {
      unfold isKS in *. rewrite Hs in HstartIsKS. simpl in *.
      destruct (beqAddr currentPart startBlock) eqn:HbeqCurrStart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HstartIsKS. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr startBlock) eqn:HbeqBlockStart.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockStart. subst startBlock. rewrite HlookupBlocks0. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    unfold bentryStartAddr in *. unfold bentryAFlag. rewrite Hs in HstartBlock. rewrite Hs. simpl in *.
    destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HstartBlock.
    rewrite Hs1. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(HkernAccs0 block startBlock part HbeqStarts HpartIsPart HblockMapped HstartBlock HstartIsKSs0).
    trivial.
    (* END kernelsAreNotAccessible *)
  }

  assert(blockAndNextAreSideBySide s).
  { (* BEGIN blockAndNextAreSideBySide s *)
    intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
      Hnext. rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEq in *.
    rewrite HgetMappedEqs1 in *. assert(HendBlocks0: bentryEndAddr block endaddr s0).
    {
      unfold bentryEndAddr in *. rewrite Hs in HendBlock. simpl in HendBlock.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HendBlock. simpl in HendBlock.
      destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    unfold scentryNext in *. rewrite Hs in Hnext. simpl in Hnext.
    destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in Hnext. simpl in Hnext.
    destruct (beqAddr requisitionedBlockInCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(HnextBlockSides0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlocks0 Hsce
      HbeqNextNull Hnext). destruct HnextBlockSides0 as (HstartNext & HnextMapped). unfold bentryStartAddr in *.
    split; trivial. rewrite Hs. simpl. destruct (beqAddr currentPart scnext) eqn:HbeqCurrNext.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. unfold isPDT in *.
      destruct (lookup scnext (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr requisitionedBlockInCurrPartAddr scnext) eqn:HbeqBlockNext.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite HbeqBlockNext in *. rewrite HlookupBlocks0 in *. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END blockAndNextAreSideBySide *)
  }

  assert(parentBlocksBoundsIfNoNext s).
  { (* BEGIN parentBlocksBoundsIfNoNext s *)
    intros partition pdentryPart block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock HendBlock
      Hsce Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *.
    rewrite HgetMappedEq in *. rewrite HgetMappedEqs1 in *.
    assert(Hblocks0: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
    {
      unfold bentryEndAddr in *. unfold bentryStartAddr in *. rewrite Hs in HstartBlock. rewrite Hs in HendBlock.
      simpl in HendBlock. simpl in HstartBlock.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HendBlock. simpl in HendBlock. rewrite Hs1 in HstartBlock. simpl in HstartBlock.
      destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct Hblocks0 as (HstartBlocks0 & HendBlocks0). unfold scentryNext in *. rewrite Hs in Hnext. simpl in Hnext.
    destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in Hnext. simpl in Hnext.
    destruct (beqAddr requisitionedBlockInCurrPartAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HlookupCurrs1. simpl in HlookupCurrs1.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
      /\ parent pdentryPart = parent pdentryParts0).
    {
      rewrite Hs in HlookupPart. simpl in HlookupPart. destruct (beqAddr currentPart partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition.
        exists pdentry. injection HlookupPart as HpdentriesEq. subst pdentryPart. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HlookupPart. simpl in HlookupPart. exists pdentryPart.
        destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    }
    destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq.
    specialize(HparentBoundss0 partition pdentryParts0 block scentryaddr startaddr endaddr HpartIsPart HblockMapped
      HstartBlocks0 HendBlocks0 Hsce Hnext HbeqPartRoot HlookupParts0).
    destruct HparentBoundss0 as [blockParent [startP (HblockPMapped & HstartP & HendP & HlebStarts)]].
    exists blockParent. exists startP. unfold bentryStartAddr in *. unfold bentryEndAddr in *. split; trivial.
    rewrite Hs. simpl. destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBP.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBP. rewrite HbeqCurrBP in *. rewrite HlookupCurrs1 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr requisitionedBlockInCurrPartAddr blockParent) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupBlocks0 in *. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
    (* END parentBlocksBoundsIfNoNext *)
  }

  assert(childLocMappedInChild s).
  { (* BEGIN childLocMappedInChild s *)
    intros part block sh1entryaddr blockChild idchild startaddr HpartIsPart HblockMapped Hsh1 HPDchildB Hloc
      HbeqIdChildNull Hstart HstartNotKS.
    rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEq in *. rewrite HgetMappedEqs1 in *.
    unfold sh1entryPDchild in *. unfold sh1entryInChildLocationWeak in *. rewrite Hs in HPDchildB.
    rewrite Hs in Hloc. simpl in HPDchildB. simpl in Hloc.
    destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HPDchildB. rewrite Hs1 in Hloc. simpl in HPDchildB. simpl in Hloc.
    destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    unfold sh1entryAddr in *. unfold bentryStartAddr in *.
    destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    assert(Hprops: sh1entryAddr block sh1entryaddr s0 /\ bentryStartAddr block startaddr s0).
    {
      rewrite Hs in HlookupBlock. simpl in HlookupBlock.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HlookupBlock. simpl in HlookupBlock. unfold sh1entryAddr. unfold bentryStartAddr.
      destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0.
        injection HlookupBlock as HbentriesEq. subst b. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite HlookupBlock. auto.
    }
    destruct Hprops as (Hsh1s0 & HstartBs0). assert(HstartNotKSs0: ~isKS startaddr s0).
    {
      unfold isKS in *. contradict HstartNotKS. rewrite Hs. simpl.
      destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrStart. rewrite <-HbeqCurrStart in *. unfold isPDT in *.
        destruct (lookup currentPart (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr startaddr) eqn:HbeqBlockStart.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite HbeqBlockStart in *. rewrite HlookupBlocks0 in *.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    specialize(HlocProps part block sh1entryaddr blockChild idchild startaddr HpartIsPart HblockMapped Hsh1s0
      HPDchildB Hloc HbeqIdChildNull HstartBs0 HstartNotKSs0).
    destruct HlocProps as (HbeqBCNull & HBCMapped & HstartsChild). split; trivial. split; trivial.
    unfold bentryStartAddr in *. rewrite Hs. simpl.
    destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBC. subst blockChild. unfold isPDT in *.
      destruct (lookup currentPart (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr requisitionedBlockInCurrPartAddr blockChild) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockChild. rewrite HlookupBlocks0 in *. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END childLocMappedInChild *)
  }

  assert(childLocHasSameStart s).
  { (* BEGIN childLocHasSameStart s *)
    intros part block sh1entryaddr blockChild idchild HpartIsPart HblockMapped Hsh1 HPDchildB Hloc
      HbeqIdChildNull HbeqBCNull.
    rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. rewrite HgetMappedEq in *. rewrite HgetMappedEqs1 in *.
    unfold sh1entryPDchild in *. unfold sh1entryInChildLocationWeak in *. rewrite Hs in HPDchildB.
    rewrite Hs in Hloc. simpl in HPDchildB. simpl in Hloc.
    destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs1 in HPDchildB. rewrite Hs1 in Hloc. simpl in HPDchildB. simpl in Hloc.
    destruct (beqAddr requisitionedBlockInCurrPartAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    unfold sh1entryAddr in *. unfold bentryStartAddr in *.
    destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    assert(Hsh1s0: sh1entryAddr block sh1entryaddr s0).
    {
      rewrite Hs in HlookupBlock. simpl in HlookupBlock.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HlookupBlock. simpl in HlookupBlock. unfold sh1entryAddr.
      destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite HlookupBlock. auto.
    }
    specialize(HsameStarts0 part block sh1entryaddr blockChild idchild HpartIsPart HblockMapped Hsh1s0
      HPDchildB Hloc HbeqIdChildNull HbeqBCNull). destruct HsameStarts0 as (HsameStart & HBCMapped). split; trivial.
    intros startaddr HstartB. assert(HstartBs0: bentryStartAddr block startaddr s0).
    {
      rewrite Hs in HlookupBlock. simpl in HlookupBlock.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HlookupBlock. simpl in HlookupBlock. unfold bentryStartAddr.
      destruct (beqAddr requisitionedBlockInCurrPartAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0.
        injection HlookupBlock as HbentriesEq. subst b. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite HlookupBlock. auto.
    }
    specialize(HsameStart startaddr HstartBs0). unfold bentryStartAddr in *. rewrite Hs. simpl.
    destruct (beqAddr currentPart blockChild) eqn:HbeqCurrBC.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBC. subst blockChild. unfold isPDT in *.
      destruct (lookup currentPart (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr requisitionedBlockInCurrPartAddr blockChild) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockChild. rewrite HlookupBlocks0 in *. auto.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END childLocHasSameStart *)
  }
  assert(Hcurrs: currentPart = currentPartition s).
  { rewrite Hs. trivial. }
  assert(HlookupBlockEq: lookup requisitionedBlockInCurrPartAddr (memory s) beqAddr
    = lookup requisitionedBlockInCurrPartAddr (memory s1) beqAddr).
  {
    rewrite Hs1 in HlookupCurrs1. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    rewrite Hs. simpl. destruct (beqAddr currentPart requisitionedBlockInCurrPartAddr) eqn:HbeqCurrBlock.
    { rewrite <-DTL.beqAddrTrue in HbeqCurrBlock. rewrite HbeqCurrBlock in *. exfalso; congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  split.
  {
    assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)).
    {
      rewrite Hs1 in HlookupCurrs1. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    instantiate(1 := fun s => isPDT globalIdPD s /\ childsBlocksPropsInParent s /\ noDupMappedPaddrList s
      /\ blockAndNextAreSideBySide s /\ parentBlocksBoundsIfNoNext s /\ childLocMappedInChild s
      /\ childLocHasSameStart s
      /\ pdentryNbPrepare globalIdPD nbPrepare s
      /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s
      /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s
      /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s
      /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
            (CIndex (kernelStructureEntriesNb-1)) s
      /\ currentPart = currentPartition s
      /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s))
      /\ lookup (CPaddr (requisitionedBlockStart+nextoffset)) (memory s) beqAddr = Some(PADDR nullAddr)
      /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s
      /\ (forall part kernList, isListOfKernels kernList part s -> ~ In requisitionedBlockStart kernList)
      /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
            -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s)
      /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
          -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s)
      /\ (forall partition, isPDT partition s
          -> Lib.disjoint
            (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
            (getFreeSlotsList partition s))
      /\ wellFormedFreeSlotsList
            (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb)) <> False
      /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
      /\ (forall block, In block
           (filterOptionPaddr
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb)))
            -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                /\ kernIdx < kernelStructureEntriesNb)
      /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
          -> block = CPaddr (requisitionedBlockStart+kernIdx)
          -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s
              (CIndex kernelStructureEntriesNb))))
      /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
            (SomePaddr requisitionedBlockStart)
          = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
      /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s
      /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
            -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1)) s)
      /\ (forall addr, In addr (filterOptionPaddr
              (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s (CIndex (kernelStructureEntriesNb-1))))
            -> forall part, isPDT part s -> ~In addr (filterOptionPaddr (getKSEntries part s)))
      /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s
      /\ (forall part,
            Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
            (getAllPaddrConfigAux (getConfigBlocks part s) s))
      /\ beqAddr nullAddr globalIdPD = false
      /\ false = StateLib.Index.leb maxnbprepare nbPrepare
      /\ kernelentriesnb = CIndex kernelStructureEntriesNb
      /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
      /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
      /\ kStructureTotalLength = Constants.kernelStructureTotalLength
      /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
      /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
      /\ newKStructurePointer = requisitionedBlockStart
      /\ i maxnbprepare = maxNbPrepare). simpl.
    rewrite HgetChildrenEq.
    assert(isPDT globalIdPD s /\ pdentryNbPrepare globalIdPD nbPrepare s).
    {
      unfold isPDT. unfold pdentryNbPrepare in *. rewrite Hs; simpl.
      destruct (beqAddr currentPart globalIdPD) eqn:HbeqCurrGlob.
      - split; trivial. rewrite <-DTL.beqAddrTrue in HbeqCurrGlob. rewrite HbeqCurrGlob in *.
        rewrite HlookupCurrs0 in *; trivial.
      - rewrite <-beqAddrFalse in *; rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1; simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr globalIdPD) eqn:HbeqBlockGlob.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockGlob; rewrite HbeqBlockGlob in *; rewrite HlookupBlocks0 in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *; rewrite removeDupIdentity; try(apply not_eq_sym); try(split); trivial.
    }
    assert(bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s
      /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockEq. rewrite Hs1; simpl.
      rewrite beqAddrTrue; rewrite HlookupBlocks0 in *; split; trivial.
    }
    assert(lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s) beqAddr = Some (PADDR nullAddr)).
    {
      rewrite Hs. simpl.
      destruct (beqAddr currentPart (CPaddr (requisitionedBlockStart + nextoffset))) eqn:HbeqCurrNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite HbeqCurrNext in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    assert(bentryBlockIndex requisitionedBlockStart (CIndex 0) s
      /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
            (CIndex (kernelStructureEntriesNb-1)) s).
    {
      assert(bentryBlockIndex requisitionedBlockStart (CIndex 0) s1
      /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
            (CIndex (kernelStructureEntriesNb-1)) s1).
      {
        unfold bentryBlockIndex in *. rewrite Hs1. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart) eqn:HbeqBlockStart.
        - rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite HbeqBlockStart in *. rewrite HlookupBlocks0 in *.
          split; trivial. destruct (beqAddr requisitionedBlockStart
            (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb - 1))) eqn:HbeqStartLast.
          {
            rewrite <-DTL.beqAddrTrue in HbeqStartLast. rewrite <-HbeqStartLast in *. rewrite HlookupBlocks0 in *.
            rewrite <-HidxLast in HidxKern. unfold CIndex in HidxKern. destruct (le_dec 0 maxIdx); try(lia).
            pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
            simpl in HidxKern. injection HidxKern as HidxKern. lia.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial.
          destruct (beqAddr requisitionedBlockInCurrPartAddr
            (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb - 1))) eqn:HbeqBlockLast.
          + rewrite <-DTL.beqAddrTrue in HbeqBlockLast. rewrite HbeqBlockLast in *. rewrite HlookupBlocks0 in *.
            trivial.
          + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold bentryBlockIndex in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart requisitionedBlockStart) eqn:HbeqCurrStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrStart. rewrite HbeqCurrStart in *. rewrite HlookupCurrs0 in *.
        exfalso; congruence.
      }
      destruct (beqAddr currentPart (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))) eqn:HbeqCurrLast.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrLast. rewrite HbeqCurrLast in *. rewrite HlookupCurrs0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(forall part kernList, isListOfKernels kernList part s -> ~ In requisitionedBlockStart kernList).
    {
      intros part kernList HkernList. apply HstartNotKern with part.
      destruct kernList as [ | kern kernList]; simpl; try(trivial). simpl in HkernList.
      destruct HkernList as [pdentryPart (HlookupPart & HbeqStructNull & Hkern & HkernList)].
      assert(HlookupParts0: exists pdentryParts0, lookup part (memory s0) beqAddr = Some (PDT pdentryParts0)
          /\ structure pdentryParts0 = structure pdentryPart).
      {
        rewrite Hs in HlookupPart. simpl in HlookupPart. destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. exists pdentry. split; trivial.
          injection HlookupPart as HlookupPart. rewrite <-HlookupPart. simpl. reflexivity.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; trivial).
          rewrite Hs1 in HlookupPart. simpl in HlookupPart.
          destruct (beqAddr requisitionedBlockInCurrPartAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; trivial).
          exists pdentryPart. split; trivial.
      }
      destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HstructEq)]. exists pdentryParts0. split; trivial.
      rewrite HstructEq. split; trivial. split; trivial.
      assert(HkernIsKS: StructurePointerIsKS s) by (unfold consistency1 in *; intuition).
      specialize(HkernIsKS part pdentryPart HlookupPart HbeqStructNull). rewrite Hkern in HkernIsKS. clear Hkern.
      revert kern HkernIsKS HkernList. induction kernList; simpl; intros; trivial.
      destruct HkernList as (HlookupKernNext & HlebNextMax & HbeqNextNull & HkernList).
      assert(HlookupKernNextCopy: lookup (CPaddr (kern+nextoffset)) (memory s) beqAddr = Some (PADDR a1))
        by assumption. rewrite Hs in HlookupKernNext. simpl in HlookupKernNext.
      destruct (beqAddr currentPart (CPaddr (kern + nextoffset))) eqn:HbeqCurrNext; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupKernNext; try(apply not_eq_sym; trivial).
      rewrite Hs1 in HlookupKernNext. simpl in HlookupKernNext.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (kern + nextoffset))) eqn:HbeqBlockNext;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HlookupKernNext; try(apply not_eq_sym; trivial). split; trivial. split; trivial.
      split; trivial. apply IHkernList; trivial.
      assert(HnextValid: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
      specialize(HnextValid kern HkernIsKS). destruct HnextValid as (_ & [nextAddr (HlookupKernNextBis & Hnext)]).
      unfold CPaddr in HlookupKernNextCopy. destruct (le_dec (kern + nextoffset) maxAddr); try(lia).
      rewrite HlookupKernNextBis in HlookupKernNextCopy. injection HlookupKernNextCopy as HlookupKernNextCopy.
      subst a1. destruct Hnext as [HnextIsKS | Hcontra]; try(exfalso; congruence). assumption.
    }
    assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
      -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s).
    {
      intros kernIdx HltIdxKernEntries. specialize(HPflagNew kernIdx HltIdxKernEntries).
      assert(bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s1).
      {
        unfold bentryPFlag in *. rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockStart+kernIdx))) eqn:HbeqStartIdx.
        {
          rewrite <-DTL.beqAddrTrue in HbeqStartIdx. rewrite HbeqStartIdx in *. rewrite HlookupBlocks0 in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      unfold bentryPFlag in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (CPaddr (requisitionedBlockStart + kernIdx))) eqn:HbeqCurrIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrIdx. rewrite HbeqCurrIdx in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
      -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s).
    {
      intros kernIdx HltIdxKernEntries. specialize(HnewFree kernIdx HltIdxKernEntries).
      assert(HnewFrees1: isFreeSlot (CPaddr (requisitionedBlockStart + kernIdx)) s1).
      {
        unfold isFreeSlot in *. rewrite Hs1. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockStart+kernIdx)))
          eqn:HbeqBlockIdx.
        {
          exfalso. specialize(HPflagNew kernIdx HltIdxKernEntries). rewrite <-DTL.beqAddrTrue in HbeqBlockIdx.
          rewrite HbeqBlockIdx in *. unfold bentryPFlag in *.
          destruct (lookup (CPaddr (requisitionedBlockStart + kernIdx)) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        destruct (lookup (CPaddr (requisitionedBlockStart + kernIdx)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). assert(HwellFormed: wellFormedBlock s0) by (unfold consistency1 in *; intuition).
        specialize(HwellFormed requisitionedBlockInCurrPartAddr requisitionedBlockStart requisitionedBlockEnd
          HPflags0 Hstarts0 Hends0). destruct HwellFormed as (_ & HwellFormed). unfold Constants.minBlockSize in *.
        unfold CIndex in HwellFormed. pose proof Constants.maxIdxBiggerThanMinBlock.
        destruct (le_dec 32 maxIdx); try(lia). simpl in HwellFormed.
        assert(Heq: forall addr, CPaddr (requisitionedBlockStart + kernIdx) + addr
          = requisitionedBlockStart + kernIdx + addr).
        {
          intro addr. unfold CPaddr. assert(requisitionedBlockEnd <= maxAddr) by (apply Hp).
          destruct (le_dec (requisitionedBlockStart+kernIdx) maxAddr); cbn in *; lia.
        }
        rewrite Heq in *. destruct (beqAddr requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockStart + kernIdx + sh1offset))) eqn:HbeqBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        destruct (lookup (CPaddr (requisitionedBlockStart+kernIdx+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). rewrite Heq in *.
        destruct (beqAddr requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockStart + kernIdx + scoffset))) eqn:HbeqBlockSce.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold isFreeSlot in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (CPaddr (requisitionedBlockStart+kernIdx))) eqn:HbeqCurrIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrIdx. rewrite HbeqCurrIdx in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (requisitionedBlockStart + kernIdx)) (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). assert(HwellFormed: wellFormedBlock s0) by (unfold consistency1 in *; intuition).
      specialize(HwellFormed requisitionedBlockInCurrPartAddr requisitionedBlockStart requisitionedBlockEnd
        HPflags0 Hstarts0 Hends0). destruct HwellFormed as (_ & HwellFormed). unfold Constants.minBlockSize in *.
      unfold CIndex in HwellFormed. pose proof Constants.maxIdxBiggerThanMinBlock.
      destruct (le_dec 32 maxIdx); try(lia). simpl in HwellFormed.
      assert(Heq: forall addr, CPaddr (requisitionedBlockStart + kernIdx) + addr
        = requisitionedBlockStart + kernIdx + addr).
      {
        intro addr. unfold CPaddr. assert(requisitionedBlockEnd <= maxAddr) by (apply Hp).
        destruct (le_dec (requisitionedBlockStart+kernIdx) maxAddr); cbn in *; lia.
      }
      rewrite Heq in *. destruct (beqAddr currentPart
        (CPaddr (requisitionedBlockStart + kernIdx + sh1offset))) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (requisitionedBlockStart+kernIdx+sh1offset)) (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). rewrite Heq in *.
      destruct (beqAddr currentPart (CPaddr (requisitionedBlockStart + kernIdx + scoffset))) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(HblockNotFree: ~isFreeSlot requisitionedBlockInCurrPartAddr s0).
    {
      unfold isFreeSlot. unfold bentryPFlag in *. rewrite HlookupBlocks0 in *.
      destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (memory s0) beqAddr);
        try(intuition; congruence). destruct v; try(intuition; congruence).
      destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr + scoffset)) (memory s0) beqAddr);
        try(intuition; congruence). destruct v; intuition; congruence.
    }
    assert(HgetNewFreeEq: getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb)
      = getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)).
    {
      assert(HeqStart: requisitionedBlockStart = CPaddr (requisitionedBlockStart+(CIndex 0))).
      {
        cbn. rewrite PeanoNat.Nat.add_0_r. unfold CPaddr. assert(requisitionedBlockStart <= maxAddr) by (apply Hp).
        destruct (le_dec requisitionedBlockStart maxAddr); try(lia). apply paddrEqNatEqEquiv. reflexivity.
      }
      assert(Heq: getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s1 (CIndex kernelStructureEntriesNb)
        = getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)).
      {
        rewrite Hs1. apply getFreeSlotsListRecEqBE; trivial.
        - intro Hcontra. assert(HltIdxKernEntries: CIndex 0 < kernelStructureEntriesNb).
          { cbn. lia. }
          specialize(HnewFree (CIndex 0) HltIdxKernEntries). rewrite <-HeqStart in HnewFree. rewrite Hcontra in *.
          congruence.
        - unfold isBE. rewrite HlookupBlocks0. trivial.
        - apply filterOptNoDup. assumption.
        - intro Hcontra. apply HnewFreeAreStartBlocks in Hcontra.
          destruct Hcontra as [kernIdx (HblockEq & HltIdxKernEntries)]. rewrite HblockEq in *.
          assert(HidxEq: kernIdx = CIndex kernIdx).
          {
            unfold CIndex. pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernIdx maxIdx); try(lia).
            reflexivity.
          }
          rewrite HidxEq in HltIdxKernEntries. specialize(HnewFree (CIndex kernIdx) HltIdxKernEntries).
          rewrite <-HidxEq in HnewFree. congruence.
      }
      rewrite <-Heq. rewrite Hs. apply getFreeSlotsListRecEqPDT; unfold isBE; unfold isPADDR;
        try(rewrite HlookupCurrs1; intuition). intro Hcontra. rewrite Hcontra in *. unfold bentryBlockIndex in *.
      rewrite HlookupCurrs0 in *. congruence.
    }
    rewrite HgetNewFreeEq.
    assert(HgetFreeEq: forall partition, getFreeSlotsList partition s = getFreeSlotsList partition s0).
    {
      intro partition. assert(Heq: getFreeSlotsList partition s1 = getFreeSlotsList partition s0).
      {
        rewrite Hs1. unfold getFreeSlotsList. simpl.
        destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst partition. rewrite HlookupBlocks0. reflexivity. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
        assert(HnoDupFree: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
        specialize(HnoDupFree partition p HlookupPart).
        destruct HnoDupFree as [listBis (Hlist & HwellFormedFree & HnoDupFree)]. subst listBis.
        unfold getFreeSlotsList in *. rewrite HlookupPart in *.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
        assert(Hfree: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition).
        assert(HpartIsPDT: isPDT partition s0) by (unfold isPDT; rewrite HlookupPart; trivial).
        assert(HgetFreeEq: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)
            = getFreeSlotsList partition s0
          /\ wellFormedFreeSlotsList (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
              <> False).
        { split; trivial. unfold getFreeSlotsList. rewrite HlookupPart. rewrite HbeqFirstNull. reflexivity. }
        specialize(Hfree partition requisitionedBlockInCurrPartAddr
          (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
          (filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))) HpartIsPDT
          HgetFreeEq). rewrite <-beqAddrFalse in *.
        apply getFreeSlotsListRecEqBE; trivial.
        - intro Hcontra. rewrite Hcontra in *.
          assert(HblockIn: filterOptionPaddr
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockInCurrPartAddr s0 (nbfreeslots p))
              = filterOptionPaddr
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockInCurrPartAddr s0 (nbfreeslots p))
            /\ In requisitionedBlockInCurrPartAddr
              (filterOptionPaddr
                 (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockInCurrPartAddr s0 (nbfreeslots p)))).
          {
            split; trivial. rewrite MaxIdxNextEq in *. simpl. simpl in HwellFormedFree. rewrite HlookupBlocks0 in *.
            destruct (StateLib.Index.pred (nbfreeslots p)); try(simpl in HwellFormedFree; exfalso; congruence).
            simpl. left. reflexivity.
          }
          specialize(Hfree HblockIn HbeqFirstNull). congruence.
        - unfold isBE. rewrite HlookupBlocks0. trivial.
        - intro Hcontra.
          assert(HblockIn: filterOptionPaddr
                (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
              = filterOptionPaddr
                (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
            /\ In requisitionedBlockInCurrPartAddr
              (filterOptionPaddr
                 (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)))).
          { split; trivial. }
          apply not_eq_sym in HbeqNullBlock. specialize(Hfree HblockIn HbeqNullBlock). congruence.
      }
      rewrite <-Heq. unfold getFreeSlotsList. rewrite Hs. simpl.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs1. simpl.
        destruct (beqAddr (firstfreeslot pdentry) nullAddr) eqn:HbeqFirstNull; trivial.
        apply getFreeSlotsListRecEqPDT; unfold isBE; unfold isPADDR; try(rewrite HlookupCurrs1); trivial;
          try(intuition; congruence).
        assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in *. specialize(HfirstIsFree currentPart pdentry HlookupCurrs0 HbeqFirstNull).
        destruct HfirstIsFree as (HfirstIsBE & _). intro Hcontra. rewrite Hcontra in *. unfold isBE in *.
        rewrite HlookupCurrs0 in *. congruence.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        destruct (lookup partition (memory s1) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
        apply getFreeSlotsListRecEqPDT; trivial; unfold isBE; unfold isPADDR; try(rewrite HlookupCurrs1);
          try(intuition; congruence).
        assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in *. specialize(HfirstIsFree partition p HlookupPart HbeqFirstNull).
        destruct HfirstIsFree as (HfirstIsBE & _). intro Hcontra. rewrite Hcontra in *. unfold isBE in *.
        rewrite HlookupCurrs1 in *. congruence.
    }
    assert(HPDTeq: forall partition, isPDT partition s -> isPDT partition s0).
    {
      intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs0. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HpartIsPDT. simpl in HpartIsPDT.
        destruct (beqAddr requisitionedBlockInCurrPartAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(bentryEndAddr (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb - 1)) nullAddr s).
    {
      pose proof maxIdxBiggerThanNbOfKernels.
      assert(HidxLastEq: requisitionedBlockStart + kernelStructureEntriesNb - 1
        = requisitionedBlockStart + CIndex (kernelStructureEntriesNb - 1)).
      {
        unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). cbn. lia.
      }
      assert(Hlt: CIndex (kernelStructureEntriesNb - 1) < kernelStructureEntriesNb).
      { unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). cbn. lia. }
      specialize(HnewFree (CIndex (kernelStructureEntriesNb - 1)) Hlt).
      assert(bentryEndAddr (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb - 1)) nullAddr s1).
      {
        unfold bentryEndAddr in *. rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb - 1))) eqn:HbeqBlockLast.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockLast. exfalso. rewrite HidxLastEq in HbeqBlockLast.
          rewrite HbeqBlockLast in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold bentryEndAddr in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))) eqn:HbeqCurrLast.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrLast. rewrite HbeqCurrLast in *. unfold isFreeSlot in *.
        rewrite HlookupCurrs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
      -> bentryEndAddr (CPaddr (requisitionedBlockStart + blkIdx)) (CPaddr (requisitionedBlockStart + blkIdx + 1)) s).
    {
      intros blkIdx HltIdxKernEntries. specialize(HendNew blkIdx HltIdxKernEntries).
      assert(Hlt: blkIdx < kernelStructureEntriesNb) by lia. specialize(HnewFree blkIdx Hlt).
      assert(bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1)) s1).
      {
        unfold bentryEndAddr in *. rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockStart + blkIdx))) eqn:HbeqBlockNew.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockNew. exfalso. rewrite HbeqBlockNew in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold bentryEndAddr in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (CPaddr (requisitionedBlockStart + blkIdx))) eqn:HbeqCurrNew.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNew. rewrite HbeqCurrNew in *. unfold isFreeSlot in *.
        rewrite HlookupCurrs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(HstructAuxEq: getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s
      (CIndex (kernelStructureEntriesNb-1)) = getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0
      (CIndex (kernelStructureEntriesNb-1))).
    {
      assert(HstructAuxEqs1: getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s
        (CIndex (kernelStructureEntriesNb-1)) = getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s1
        (CIndex (kernelStructureEntriesNb-1))).
      {
        rewrite Hs. apply getKSEntriesInStructAuxEqPDT.
        - intro Hcontra. rewrite Hcontra in *. unfold bentryBlockIndex in *. rewrite HlookupCurrs0 in *. congruence.
        - unfold isBE. rewrite HlookupCurrs1. congruence.
      }
      rewrite HstructAuxEqs1. rewrite Hs1. apply getKSEntriesInStructAuxEqBE. unfold isBE. rewrite HlookupBlocks0.
      trivial.
    }
    assert(forall addr, In addr (filterOptionPaddr
            (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s (CIndex (kernelStructureEntriesNb-1))))
          -> forall part, isPDT part s -> ~In addr (filterOptionPaddr (getKSEntries part s))).
    {
      intros addr HaddrIsNew part HpartIsPDT. apply HPDTeq in HpartIsPDT. rewrite HgetKSEntriesEq.
      rewrite HgetKSEntriesEqs1. rewrite HstructAuxEq in HaddrIsNew. apply HnewStructAreNotEntries; trivial.
    }
    assert(sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s).
    {
      unfold sh1entryPDflag in *. rewrite Hs. simpl.
      destruct (beqAddr currentPart (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))) eqn:HbeqCurrSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)))
        eqn:HbeqBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(forall part,
            Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
            (getAllPaddrConfigAux (getConfigBlocks part s) s)).
    {
      intros part addr HaddrIsNew. specialize(HnewNotConf part addr HaddrIsNew). contradict HnewNotConf.
      assert(HconfEq: getConfigBlocks part s = getConfigBlocks part s0).
      {
        assert(HpartIsPDT: isPDT part s).
        {
          unfold getConfigBlocks in HnewNotConf. unfold isPDT.
          destruct (lookup part (memory s) beqAddr); try(simpl in HnewNotConf; congruence).
          destruct v; try(simpl in HnewNotConf; congruence). trivial.
        }
        assert(HpartIsPDTs1: isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
          destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
          - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs1. trivial.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        }
        assert(Heqs: getConfigBlocks part s = getConfigBlocks part s1).
        { rewrite Hs. apply getConfigBlocksEqPDT with pdentry; trivial. }
        rewrite Heqs. rewrite Hs1. apply getConfigBlocksEqBE.
        - unfold isPDT in *. rewrite Hs1 in HpartIsPDTs1. simpl in HpartIsPDTs1.
          destruct (beqAddr requisitionedBlockInCurrPartAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        - unfold isBE. rewrite HlookupBlocks0. trivial.
      }
      rewrite HconfEq in HnewNotConf.
      assert(Heqs1: getAllPaddrConfigAux (getConfigBlocks part s0) s1
        = getAllPaddrConfigAux (getConfigBlocks part s0) s0).
      {
        rewrite Hs1. apply getAllPaddrConfigAuxEqBE. unfold isBE. rewrite HlookupBlocks0. trivial.
      }
      assert(Heqs: getAllPaddrConfigAux (getConfigBlocks part s0) s
        = getAllPaddrConfigAux (getConfigBlocks part s0) s0).
      {
        rewrite <-Heqs1. rewrite Hs. apply getAllPaddrConfigAuxEqPDT. unfold isPDT. rewrite HlookupCurrs1. trivial.
      }
      rewrite Heqs in *. assumption.
    }
    (*assert(forall kern part, In kern (getConfigBlocks part s) -> kern <> requisitionedBlockStart).
    {
      intros kern part HkernInConf. assert(HconfEq: getConfigBlocks part s = getConfigBlocks part s0).
      {
        assert(HpartIsPDT: isPDT part s).
        {
          unfold getConfigBlocks in HkernInConf. unfold isPDT.
          destruct (lookup part (memory s) beqAddr); try(simpl in HkernInConf; congruence).
          destruct v; try(simpl in HkernInConf; congruence). trivial.
        }
        assert(HpartIsPDTs1: isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
          destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
          - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs1. trivial.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        }
        assert(Heqs: getConfigBlocks part s = getConfigBlocks part s1).
        { rewrite Hs. apply getConfigBlocksEqPDT with pdentry; trivial. }
        rewrite Heqs. rewrite Hs1. apply getConfigBlocksEqBE.
        - unfold isPDT in *. rewrite Hs1 in HpartIsPDTs1. simpl in HpartIsPDTs1.
          destruct (beqAddr requisitionedBlockInCurrPartAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        - unfold isBE. rewrite HlookupBlocks0. trivial.
      }
      rewrite HconfEq in HkernInConf. apply HstartNotConf with part; assumption.
    }*)
    intuition; rewrite HgetFreeEq; apply HdisjointFree; apply HPDTeq; trivial.
  }
  split.
  {
    exists {|
             structure := structure pdentry;
             firstfreeslot := firstfreeslot pdentry;
             nbfreeslots := nbfreeslots pdentry;
             nbprepare := nbprepare pdentry;
             parent := parent pdentry;
             MPU := MAL.removeBlockFromPhysicalMPUAux requisitionedBlockInCurrPartAddr realMPU;
             vidtAddr := vidtAddr pdentry
           |}. rewrite Hs. simpl. rewrite beqAddrTrue. trivial.
  }
  split.
  {
    assert(Hres: In (currentPartition s1) (getPartitions multiplexer s1)) by (unfold consistency1 in *; intuition).
    rewrite Hcurr. rewrite HgetPartsEqs. assumption.
  }
  split. unfold bentryPFlag in *. rewrite HlookupBlockEq. rewrite Hs1. simpl. rewrite beqAddrTrue.
  rewrite HlookupBlocks0 in *. trivial.
  split. unfold bentryAFlag. rewrite HlookupBlockEq. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial.
  split. unfold bentryStartAddr in *. rewrite HlookupBlockEq. rewrite Hs1. simpl. rewrite beqAddrTrue.
  rewrite HlookupBlocks0 in *. trivial.
  split. unfold bentryEndAddr in *. rewrite HlookupBlockEq. rewrite Hs1. simpl. rewrite beqAddrTrue.
  rewrite HlookupBlocks0 in *. trivial.
  split. rewrite HgetMappedEq. rewrite HgetMappedEqs1. assumption.
  split.
  {
    rewrite Hs1 in HlookupCurrs1. simpl in *.
    destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
    unfold sh1entryPDchild in *. rewrite Hs. simpl.
    destruct (beqAddr currentPart (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))) eqn:HbeqCurrSh1.
    { rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs1 in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; trivial). rewrite Hs1. simpl.
    destruct (beqAddr requisitionedBlockInCurrPartAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)))
      eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  (* BEGIN partial accessibleParentPaddrIsAccessibleIntoChild s *)
  intros pdparent child addr HnotEdgeCase HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
  rewrite HgetPartsEqs in *. rewrite HgetPartsEqs1 in *. assert(isPDT pdparent s0).
  { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
  rewrite HgetChildrenEq in *. rewrite HgetChildrenEqs1 in *; trivial.
  apply HgetAccMappedPaddrIncl in HaddrAccMappedParent; trivial. assert(HchildIsPDT: isPDT child s0).
  { apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition. }
  rewrite HgetMappedPaddrEq in *; trivial.
  specialize(Haccesss0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild).
  assert(Heqs1: getAccessibleMappedPaddr child s = getAccessibleMappedPaddr child s1).
  {
    rewrite Hs. apply getAccessibleMappedPaddrEqPDT with pdentry; trivial; unfold consistency1 in *; intuition.
  }
  rewrite Heqs1. destruct (beqAddr child currentPart) eqn:HbeqChildCurr.
  - rewrite <-DTL.beqAddrTrue in HbeqChildCurr. rewrite HlookupBlockEq in *.
    destruct HnotEdgeCase as [Hcontra | HnotEdgeCase]; try(exfalso; congruence).
    set(newBentry:= {|
             read := read bentry;
             write := write bentry;
             exec := exec bentry;
             present := present bentry;
             accessible := false;
             blockindex := blockindex bentry;
             blockrange := blockrange bentry;
             Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
           |}).
    destruct (eqb (accessible newBentry) (accessible bentry)) eqn:HbeqAccess.
    + apply eqb_prop in HbeqAccess.
      assert(Heq: getAccessibleMappedPaddr child s1 = getAccessibleMappedPaddr child s0).
      {
        rewrite Hs1. apply getAccessibleMappedPaddrEqBEPresentAccessibleNoChange with bentry; trivial.
      }
      rewrite Heq. assumption.
    + apply eqb_false_iff in HbeqAccess. rewrite Hs1 in HnotEdgeCase. simpl in *. rewrite beqAddrTrue in *.
      simpl in *. rewrite app_nil_r in HnotEdgeCase. unfold bentryPFlag in *. rewrite HlookupBlocks0 in *.
      apply eq_sym in HPflags0. subst child. unfold getMappedBlocks in *.
      apply InFilterPresentInList in HblockMappeds0.
      apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleFalseChangeInclusionRev
        with currentPart requisitionedBlockInCurrPartAddr addr newBentry bentry s0 in Haccesss0; trivial.
      fold newBentry in Hs1. rewrite <-Hs1 in Haccesss0. simpl in Haccesss0. intuition.
  - rewrite <-beqAddrFalse in *.
    assert(~In requisitionedBlockInCurrPartAddr (filterOptionPaddr (getKSEntries child s0))).
    {
      rewrite Hs1 in HlookupCurrs1. simpl in *.
      destruct (beqAddr requisitionedBlockInCurrPartAddr currentPart) eqn:HbeqBlockCurr; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym; trivial).
      assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency1 in *; intuition).
      apply not_eq_sym in HbeqChildCurr.
      specialize(Hdisjoint currentPart child HcurrIsPDT HchildIsPDT HbeqChildCurr).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMappeds0.
      specialize(Hdisjoint requisitionedBlockInCurrPartAddr HblockMappeds0). assumption.
    }
    rewrite Hs1. rewrite getAccessibleMappedPaddrEqBENotInPart; trivial. unfold isBE. rewrite HlookupBlocks0. trivial.
  (* END accessibleParentPaddrIsAccessibleIntoChild *)
}
intro. eapply bindRev.
{ (** MAL.readPDStructurePointer **)
  eapply weaken. apply readPDStructurePointer. simpl. intros s Hprops.
  destruct Hprops as (HPI & HKDI & HVS & [s0 [pdentryCurr [statesList [parentsList [blockOrigin [blockNext (HPIs0 &
    HKDIs0 & HVSs0 & (HglobIsPDTs0 & HchildBlockPropss0 & HnoDupUseds0 & HblockNextSides0 & HparentBoundss0 &
    HlocPropss0 & HsameStarts0 & HnbPreps0 & Hstarts0 & Hends0 & HkernIdxs0 &
    HlastIdxs0 & Hcurrs0 & Hglob & HlookupNext & _ & HstartIsNotKern & HPflagNew & HnewFree & HdisjointNew &
    HwellFormedNew & HnoDupNew & HnewFreeAreStartBlocks & HstartsBlocksAreNewFree & HlastNew & HendLast & HendNew &
    HnewStructAreNotEntries & HPDflag & HnewNotConf & HbeqNullGlob & HlebMaxNbPrep & HkernEntriesNb & Hblock &
    HbeqNullBlock & HkernLen & HltSizeKernLen & Hsize & HstartEq & Hmax) & Hconsists0 & HparentsList & HsIsLast &
    HlookupCurr & HlookupCurrs0 & HcurrIsParts0 & Hconsist & HnoDupUsed & Hshared & Hrange & HchildBlockProps &
    HnoChild & HkernNotAcc & HlookupBlockEq & HPflags0 & HAflags0 & HblockMappeds0 & HblockNotAccs0 & HPDchilds0 &
    HblockMapped & HPDchild & Haccess & Hnexts0 & Horigins0 & HpropsOr & HlastPart & HisBuilt)]]]]]]).
  instantiate(1:= fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ consistency1 s /\ noDupMappedPaddrList s /\ sharedBlockPointsToChild s
    /\ adressesRangePreservedIfOriginAndNextOk s /\ childsBlocksPropsInParent s /\ noChildImpliesAddressesNotShared s
    /\ kernelsAreNotAccessible s /\ accessibleParentPaddrIsAccessibleIntoChild s
    /\ blockAndNextAreSideBySide s /\ parentBlocksBoundsIfNoNext s /\ childLocMappedInChild s
    /\ childLocHasSameStart s
    /\ pdentryNbPrepare globalIdPD nbPrepare s
    /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s
    /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s
    /\ bentryPFlag requisitionedBlockInCurrPartAddr true s
    /\ bentryAFlag requisitionedBlockInCurrPartAddr false s
    /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s)
    /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s
    /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
          (CIndex (kernelStructureEntriesNb-1)) s
    /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s
    /\ currentPart = currentPartition s
    /\ In currentPart (getPartitions multiplexer s)
    /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s))
    /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s) beqAddr = Some(PADDR nullAddr)
    /\ (forall part kernList, isListOfKernels kernList part s -> ~ In requisitionedBlockStart kernList)
    /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
          -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s)
    /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
        -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s)
    /\ (forall partition, isPDT partition s
        -> Lib.disjoint
          (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
          (getFreeSlotsList partition s))
    /\ wellFormedFreeSlotsList
          (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb)) <> False
    /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
    /\ (forall block, In block
         (filterOptionPaddr
            (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb)))
          -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
              /\ kernIdx < kernelStructureEntriesNb)
    /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
        -> block = CPaddr (requisitionedBlockStart+kernIdx)
        -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s
            (CIndex kernelStructureEntriesNb))))
    /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb))
          (SomePaddr requisitionedBlockStart)
        = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
    /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s
    /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
          -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1)) s)
    /\ (forall addr, In addr (filterOptionPaddr
            (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s (CIndex (kernelStructureEntriesNb-1))))
          -> forall part, isPDT part s -> ~In addr (filterOptionPaddr (getKSEntries part s)))
    /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s
    /\ (forall part,
          Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
          (getAllPaddrConfigAux (getConfigBlocks part s) s))
    /\ beqAddr nullAddr globalIdPD = false
    /\ false = StateLib.Index.leb maxnbprepare nbPrepare
    /\ kernelentriesnb = CIndex kernelStructureEntriesNb
    /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
    /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
    /\ kStructureTotalLength = Constants.kernelStructureTotalLength
    /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
    /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
    /\ newKStructurePointer = requisitionedBlockStart
    /\ i maxnbprepare = maxNbPrepare). simpl.
  assert(HlookupGlobEq: lookup globalIdPD (memory s) beqAddr = lookup globalIdPD (memory s0) beqAddr).
  {
    apply lookupPDTEqWriteAccess with statesList parentsList requisitionedBlockStart requisitionedBlockEnd false
      currentPart; trivial.
    - apply partitionsArePDT; trivial; unfold consistency1 in *; intuition.
    - destruct Hglob as [HbeqCurrGlob | HglobIsChild].
      + subst globalIdPD. apply basePartNotInParentsLists with pdentryCurr s0; trivial; unfold consistency1 in *;
          intuition.
      + intro Hcontra. assert(HglobIsAnc: In globalIdPD (filterOptionPaddr (completeParentsList currentPart s0))).
        {
          apply parentsListIsInclInComplete with parentsList; trivial; unfold consistency1 in *; intuition.
        }
        assert(HcurrNotAnc: ~In currentPart (filterOptionPaddr (completeParentsList globalIdPD s0))).
        {
          apply completeParentsListOrientation; trivial.
          1,2: unfold consistency1 in *; intuition.
          apply childrenPartitionInPartitionList with currentPart; trivial; unfold consistency1 in *; intuition.
        }
        unfold completeParentsList in HcurrNotAnc. simpl in HcurrNotAnc.
        assert(HisParent: isParent s0) by (unfold consistency1 in *; intuition).
        specialize(HisParent globalIdPD currentPart HcurrIsParts0 HglobIsChild). unfold pdentryParent in *.
        destruct (lookup globalIdPD (memory s0) beqAddr) eqn:HlookupGlob; try(congruence).
        destruct v; try(congruence). destruct (beqAddr globalIdPD constantRootPartM) eqn:HbeqGlobRoot.
        {
          rewrite <-DTL.beqAddrTrue in HbeqGlobRoot.
          assert(HparentOfPart: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
          specialize(HparentOfPart globalIdPD p HlookupGlob). destruct HparentOfPart as (_ & HparentOfRoot & _).
          specialize(HparentOfRoot HbeqGlobRoot). rewrite HparentOfRoot in *. rewrite HisParent in *.
          assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
          rewrite HlookupCurr in *. congruence.
        }
        simpl in HcurrNotAnc. apply Decidable.not_or in HcurrNotAnc. destruct HcurrNotAnc as (HbeqParentCurr & _).
        congruence.
  }
  assert(bentryBlockIndex requisitionedBlockStart (CIndex 0) s).
  {
    unfold bentryBlockIndex in *.
    destruct (lookup requisitionedBlockStart (memory s0) beqAddr) eqn:HlookupStart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart requisitionedBlockStart
      requisitionedBlockEnd false s requisitionedBlockStart b HlookupStart HisBuilt) as Hres.
    destruct Hres as [bentry (HlookupStarts & _ & _ & _ & _ & HidxEq & _)]. rewrite HlookupStarts.
    rewrite HidxEq. assumption.
  }
  assert(bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
            (CIndex (kernelStructureEntriesNb-1)) s).
  {
    unfold bentryBlockIndex in *.
    destruct (lookup (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1)) (memory s0) beqAddr)
      eqn:HlookupLast; try(exfalso; congruence). destruct v; try(exfalso; congruence).
    pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart requisitionedBlockStart
      requisitionedBlockEnd false s (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1)) b HlookupLast
      HisBuilt) as Hres.
    destruct Hres as [bentry (HlookupLasts & _ & _ & _ & _ & HidxEq & _)]. rewrite HlookupLasts.
    rewrite HidxEq. assumption.
  }
  unfold isPDT. unfold pdentryNbPrepare. rewrite HlookupGlobEq. split; trivial. unfold bentryStartAddr.
  unfold bentryEndAddr. unfold bentryPFlag. unfold bentryAFlag. rewrite HlookupBlockEq.
  assert(currentPart = currentPartition s).
  {
    apply eq_sym. rewrite Hcurrs0. revert HisBuilt. apply currentPartitionEqIsBuilt.
  }
  assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
  {
    revert HisBuilt. apply getPartitionsEqBuiltWithWriteAccFalse; trivial; unfold consistency1 in *; intuition.
  }
  rewrite <-HgetPartsEq in *.
  assert(lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s) beqAddr = Some(PADDR nullAddr)).
  {
    rewrite <-HlookupNext. revert HisBuilt. apply lookupPADDREqWriteAccess.
    - unfold isPDT. rewrite HlookupCurr. trivial.
    - unfold isPADDR. rewrite HlookupNext. trivial.
  }
  assert(HgetChildrenEq: getChildren currentPart s = getChildren currentPart s0).
  {
    revert HisBuilt. apply getChildrenEqBuiltWithWriteAcc; try(unfold isPDT; rewrite HlookupCurr);
      unfold consistency1 in *; intuition.
  }
  assert(forall part kernList, isListOfKernels kernList part s -> ~ In requisitionedBlockStart kernList).
  {
    intros part kernList HkernList. apply HstartIsNotKern with part.
    destruct kernList as [ | kern kernList]; simpl; trivial. simpl in HkernList.
    destruct HkernList as [pdentryPart (HlookupPart & HbeqStructNull & Hkern & HkernList)].
    assert(HcurrIsPDTs0: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurr; trivial).
    pose proof (stablePDTFieldsIsBuiltRev statesList s0 parentsList currentPart pdentryPart requisitionedBlockStart
      requisitionedBlockEnd false s part HcurrIsPDTs0 HisBuilt HlookupPart) as HlookupParts0.
    destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HstructEq & _)]. exists pdentryParts0.
    rewrite HstructEq. split; trivial. split; trivial. split; trivial.
    assert(HkernIsKS: StructurePointerIsKS s) by (unfold consistency1 in *; intuition).
    specialize(HkernIsKS part pdentryPart HlookupPart HbeqStructNull). rewrite Hkern in HkernIsKS. clear Hkern.
    revert kern HkernIsKS HkernList. induction kernList; simpl; intros; trivial.
    destruct HkernList as (HlookupKernNext & HlebNextMax & HbeqNextNull & HkernList).
    rewrite <-lookupPADDREqWriteAccessRev with statesList s0 parentsList (CPaddr (kern + nextoffset))
      requisitionedBlockStart requisitionedBlockEnd false s currentPart; trivial;
      try(unfold isPADDR; rewrite HlookupKernNext; trivial). split; trivial. split; trivial. split; trivial.
    apply IHkernList; trivial. assert(HnextValid: nextKernelIsValid s) by (unfold consistency1 in *; intuition).
    specialize(HnextValid kern HkernIsKS). destruct HnextValid as (_ & [nextAddr (HlookupKernNextBis & Hnext)]).
    unfold CPaddr in HlookupKernNext. destruct (le_dec (kern + nextoffset) maxAddr); try(lia).
    rewrite HlookupKernNextBis in HlookupKernNext. injection HlookupKernNext as HlookupKernNext. subst a2.
    destruct Hnext as [Hres | Hcontra]; try(exfalso; congruence). assumption.
  }
  assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
          -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s).
  {
    intros kernIdx HltIdxKernEntries. specialize(HPflagNew kernIdx HltIdxKernEntries). unfold bentryPFlag in *.
    destruct (lookup (CPaddr (requisitionedBlockStart + kernIdx)) (memory s0) beqAddr) eqn:HlookupIdx;
      try(exfalso; congruence). destruct v; try(exfalso; congruence).
    pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart requisitionedBlockStart
      requisitionedBlockEnd false s (CPaddr (requisitionedBlockStart + kernIdx)) b HlookupIdx HisBuilt) as Hres.
    destruct Hres as [bentry (Hlookups & _ & _ & _ & Hres & _)]. rewrite Hlookups. rewrite Hres. assumption.
  }
  assert(forall kernIdx: index, kernIdx < kernelStructureEntriesNb
          -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s).
  {
    intros kernIdx HltIdxKernEntries. specialize(HnewFree kernIdx HltIdxKernEntries). unfold isFreeSlot in *.
    assert(HPflag: bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0).
    {
      unfold bentryPFlag. destruct (lookup (CPaddr (requisitionedBlockStart + kernIdx)) (memory s0) beqAddr);
        try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct (lookup (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + sh1offset)) (memory s0) beqAddr);
        try(exfalso; congruence). destruct v; try(exfalso; congruence).
      destruct (lookup (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + scoffset)) (memory s0) beqAddr);
        try(exfalso; congruence). destruct v; try(exfalso; congruence). intuition.
    }
    pose proof (lookupBENotPresEqWriteAccess (CPaddr (requisitionedBlockStart + kernIdx)) requisitionedBlockStart
      requisitionedBlockEnd statesList s0 parentsList currentPart false s HPflag HisBuilt) as HlookupIdxEq.
    rewrite HlookupIdxEq.
    destruct (lookup (CPaddr (requisitionedBlockStart + kernIdx)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence).
    assert(Hshe: isSHE (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + sh1offset)) s0).
    {
      unfold isSHE.
      destruct (lookup (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + sh1offset)) (memory s0) beqAddr)
        eqn:HlookupShe; try(congruence). destruct v; try(congruence). trivial.
    }
    assert(HcurrIsPDT: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurr; trivial).
    pose proof (lookupSHEEqWriteAccess statesList s0 parentsList
      (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + sh1offset)) requisitionedBlockStart
      requisitionedBlockEnd false s currentPart HcurrIsPDT Hshe HisBuilt) as HlookupSheEq. rewrite HlookupSheEq.
    destruct (lookup (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + sh1offset)) (memory s0) beqAddr)
      eqn:HlookupShe; try(congruence). destruct v; try(congruence).
    assert(Hsce: isSCE (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + scoffset)) s0).
    {
      unfold isSCE.
      destruct (lookup (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + scoffset)) (memory s0) beqAddr)
        eqn:HlookupSce; try(congruence). destruct v; try(congruence). trivial.
    }
    pose proof (lookupSCEEqWriteAccess statesList s0 parentsList
      (CPaddr (CPaddr (requisitionedBlockStart + kernIdx) + scoffset)) requisitionedBlockStart
      requisitionedBlockEnd false s currentPart HcurrIsPDT Hsce HisBuilt) as HlookupSceEq. rewrite HlookupSceEq.
    assumption.
  }
  assert(HgetFreeEq: getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s (CIndex kernelStructureEntriesNb)
    = getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)).
  {
    apply getFreeSlotsListRecEqBuiltWithWriteAcc with statesList parentsList requisitionedBlockStart
      requisitionedBlockEnd currentPart false; trivial.
    - rewrite <-beqAddrFalse. intro Hcontra. unfold bentryBlockIndex in *. rewrite Hcontra in *.
      assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
      destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    - apply filterOptNoDup; assumption.
    - intros block HblockIn. apply optionIsInFilter in HblockIn. apply HnewFreeAreStartBlocks in HblockIn.
      destruct HblockIn as [kernIdx (HblockEq & HltIdxKernEntries)]. assert(HidxEq: kernIdx = CIndex kernIdx).
      {
        unfold CIndex. pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernIdx maxIdx); try(lia).
        reflexivity.
      }
      rewrite HidxEq in HltIdxKernEntries. apply HnewFree in HltIdxKernEntries. rewrite <-HidxEq in HltIdxKernEntries.
      subst block. assumption.
  }
  assert(forall partition, isPDT partition s
    -> Lib.disjoint (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
          (getFreeSlotsList partition s)).
  {
    intros partition HpartIsPDT block HblockIn. unfold isPDT in *.
    destruct (lookup partition (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). assert(HcurrIsPDT: isPDT currentPart s0).
    { unfold isPDT. rewrite HlookupCurr. trivial. }
    pose proof (stablePDTFieldsIsBuiltRev statesList s0 parentsList currentPart p requisitionedBlockStart
      requisitionedBlockEnd false s partition HcurrIsPDT HisBuilt HlookupPart) as Hres.
    destruct Hres as [pdentryPart (HlookupParts0 & _ & HfirstEq & HnbFreeEq & _)].
    assert(HpartIsPDTs0: isPDT partition s0).
    { unfold isPDT. rewrite HlookupParts0. trivial. }
    assert(HnoDupFree: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
    specialize(HnoDupFree partition pdentryPart HlookupParts0).
    destruct HnoDupFree as [optFreeList (Hlist & HwellFormedFree & HnoDupFree)]. subst optFreeList.
    specialize(HdisjointNew partition HpartIsPDTs0 block HblockIn). contradict HdisjointNew.
    unfold getFreeSlotsList in *. rewrite HlookupParts0 in *. rewrite HlookupPart in *. rewrite HfirstEq in *.
    rewrite HnbFreeEq in *. destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
    assert(HfreeEq: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s (nbfreeslots p)
      = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
    {
      apply getFreeSlotsListRecEqBuiltWithWriteAcc with statesList parentsList requisitionedBlockStart
        requisitionedBlockEnd currentPart false; trivial. intros blockBis HblockInBis.
      assert(HfreeIsFree: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition).
      assert(Hwell: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)
          = getFreeSlotsList partition s0
        /\ wellFormedFreeSlotsList (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
          <> False).
      {
        split; trivial. unfold getFreeSlotsList. rewrite HlookupParts0. rewrite HfirstEq. rewrite HbeqFirstNull.
        rewrite HnbFreeEq. reflexivity.
      }
      assert(HnoDup: filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
          = filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
        /\ In blockBis
         (filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)))).
      { split; trivial. apply optionIsInFilter; assumption. }
      assert(HbeqBlockBisNull: blockBis <> nullAddr).
      { revert HblockInBis. apply freeIsNotNull. unfold consistency1 in *; intuition. }
      specialize(HfreeIsFree partition blockBis
        (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p))
        (filterOptionPaddr (getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)))
        HpartIsPDTs0 Hwell HnoDup HbeqBlockBisNull). assumption.
    }
    rewrite <-HfreeEq. assumption.
  }
  assert(bentryEndAddr (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb - 1)) nullAddr s).
  {
    unfold bentryEndAddr in *.
    destruct (lookup (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) (memory s0) beqAddr)
      eqn:HlookupLast; try(exfalso; congruence). destruct v; try(exfalso; congruence).
    pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart requisitionedBlockStart
      requisitionedBlockEnd false s (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb - 1)) b HlookupLast
      HisBuilt) as HlookupLasts. destruct HlookupLasts as [bentrys (HlookupLasts & _ & _ & _ & _ & _ & HrangeEq)].
    rewrite HlookupLasts. rewrite HrangeEq. assumption.
  }
  assert(forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
    -> bentryEndAddr (CPaddr (requisitionedBlockStart + blkIdx)) (CPaddr (requisitionedBlockStart + blkIdx+1)) s).
  {
    intros blkIdx HltIdxKernEntries. specialize(HendNew blkIdx HltIdxKernEntries). unfold bentryEndAddr in *.
    destruct (lookup (CPaddr (requisitionedBlockStart+blkIdx)) (memory s0) beqAddr) eqn:HlookupNew;
      try(exfalso; congruence). destruct v; try(exfalso; congruence).
    pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart requisitionedBlockStart
      requisitionedBlockEnd false s (CPaddr (requisitionedBlockStart+blkIdx)) b HlookupNew HisBuilt) as HlookupLasts.
    destruct HlookupLasts as [bentrys (HlookupLasts & _ & _ & _ & _ & _ & HrangeEq)].
    rewrite HlookupLasts. rewrite HrangeEq. assumption.
  }
  rewrite HgetPartsEq in *. assert(HcurrIsPDTs0: isPDT currentPart s0).
  { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
  assert(HstructAuxEq: forall n (nidx:index), n > nidx
    -> getKSEntriesInStructAux n requisitionedBlockStart s nidx
        = getKSEntriesInStructAux n requisitionedBlockStart s0 nidx).
  {
    induction n; simpl; intros nidx HgtNIdx; try(lia).
    destruct (StateLib.Paddr.addPaddrIdx requisitionedBlockStart nidx); trivial.
    destruct (lookup p (memory s0) beqAddr) eqn:HlookupP.
    - destruct v.
      + assert(HpIsBEs0: isBE p s0) by (unfold isBE; rewrite HlookupP; trivial).
        assert(HpIsBEs: isBE p s) by (revert HisBuilt; apply stableBEIsBuilt; trivial). unfold isBE in HpIsBEs.
        destruct (lookup p (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        destruct (indexEq nidx zero); trivial. destruct (StateLib.Index.pred nidx) eqn:Hpred; trivial.
        f_equal. apply IHn. unfold StateLib.Index.pred in *. destruct (gt_dec nidx 0); try(exfalso; congruence).
        injection Hpred as Hpred. rewrite <-Hpred. simpl. lia.
      + assert(HlookupEq: lookup p (memory s) beqAddr = lookup p (memory s0) beqAddr).
        {
          revert HisBuilt. apply lookupSHEEqWriteAccess; trivial. unfold isSHE. rewrite HlookupP. trivial.
        }
        rewrite HlookupEq. rewrite HlookupP. trivial.
      + assert(HlookupEq: lookup p (memory s) beqAddr = lookup p (memory s0) beqAddr).
        {
          revert HisBuilt. apply lookupSCEEqWriteAccess; trivial. unfold isSCE. rewrite HlookupP. trivial.
        }
        rewrite HlookupEq. rewrite HlookupP. trivial.
      + assert(HpIsPDTs0: isPDT p s0) by (unfold isPDT; rewrite HlookupP; trivial).
        assert(HpIsPDTs: isPDT p s) by (revert HisBuilt HpIsPDTs0; apply stablePDTIsBuilt; trivial).
        unfold isPDT in HpIsPDTs. destruct (lookup p (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). trivial.
      + assert(HlookupEq: lookup p (memory s) beqAddr = lookup p (memory s0) beqAddr).
        {
          revert HisBuilt. apply lookupPADDREqWriteAccess; trivial. unfold isPADDR. rewrite HlookupP. trivial.
        }
        rewrite HlookupEq. rewrite HlookupP. trivial.
    - assert(HlookupEq: lookup p (memory s) beqAddr = lookup p (memory s0) beqAddr).
      {
        revert HisBuilt. apply lookupNoneEqWriteAccess; trivial.
      }
      rewrite HlookupEq. rewrite HlookupP. trivial.
  }
  assert(forall addr, In addr (filterOptionPaddr
      (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s (CIndex (kernelStructureEntriesNb-1))))
    -> forall part, isPDT part s -> ~In addr (filterOptionPaddr (getKSEntries part s))).
  {
    intros addr HaddrIsNew part HpartIsPDT. unfold isPDT in HpartIsPDT.
    destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    pose proof (stablePDTFieldsIsBuiltRev statesList s0 parentsList currentPart p requisitionedBlockStart
      requisitionedBlockEnd false s part HcurrIsPDTs0 HisBuilt HlookupPart) as HlookupParts0.
    destruct HlookupParts0 as [pdentry (HlookupParts0 & _)]. assert(HpartIsPDTs0: isPDT part s0).
    { unfold isPDT. rewrite HlookupParts0. trivial. }
    assert(HgetKSEq: getKSEntries part s = getKSEntries part s0).
    {
      revert HisBuilt. unfold bentryAFlag in *.
      assert(false = checkChild requisitionedBlockInCurrPartAddr s0
        (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset))).
      {
        unfold checkChild. unfold sh1entryPDflag in *.
        destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); trivial. destruct v; trivial.
        destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (memory s0) beqAddr); trivial.
        destruct v; trivial.
      }
      destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlock;
        try(exfalso; congruence). destruct v; try(exfalso; congruence).
      apply getKSEntriesEqBuiltWithWriteAcc with requisitionedBlockInCurrPartAddr b; trivial;
        unfold consistency1 in *; intuition.
    }
    rewrite HgetKSEq. rewrite HstructAuxEq in HaddrIsNew; try(apply HnewStructAreNotEntries; trivial). unfold CIndex.
    pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
    cbn -[kernelStructureEntriesNb]. lia.
  }
  assert(sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s).
  {
    unfold sh1entryPDflag in *. rewrite lookupSHEEqWriteAccess with statesList s0 parentsList
      (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) requisitionedBlockStart requisitionedBlockEnd
      false s currentPart; trivial. unfold isSHE.
    destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(forall part,
          Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
          (getAllPaddrConfigAux (getConfigBlocks part s) s)).
  {
    intros part addr HaddrIsNew Hcontra. assert(HconfEq: getConfigBlocks part s = getConfigBlocks part s0).
    {
      assert(isPDT part s0).
      {
        unfold getConfigBlocks in Hcontra. unfold isPDT.
        destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; try(simpl in Hcontra; exfalso; congruence).
        destruct v; try(simpl in Hcontra; exfalso; congruence).
        pose proof(stablePDTFieldsIsBuiltRev statesList s0 parentsList currentPart p requisitionedBlockStart
          requisitionedBlockEnd false s part HcurrIsPDTs0 HisBuilt HlookupPart) as Hres.
        destruct Hres as [pdentryPart (HlookupParts0 & _)]. rewrite HlookupParts0. trivial.
      }
      revert HisBuilt. apply getConfigBlocksEqBuiltWithWriteAcc; trivial.
    }
    rewrite HconfEq in *. assert(Heq: getAllPaddrConfigAux (getConfigBlocks part s0) s
      = getAllPaddrConfigAux (getConfigBlocks part s0) s0).
    { revert HisBuilt. apply getAllPaddrConfigAuxEqBuiltWithWriteAcc. }
    rewrite Heq in *. contradict Hcontra. apply HnewNotConf; assumption.
  }
  assert(HgetMappedEq: forall partition, isPDT partition s0
    -> getMappedBlocks partition s = getMappedBlocks partition s0).
  {
    intros partition HpartIsPDT. revert HisBuilt.
    assert(HlookupBlock: exists bentry,
      lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr = Some (BE bentry)).
    {
      unfold bentryEndAddr in *.
      destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists b. reflexivity.
    }
    destruct HlookupBlock as [bentry HlookupBlock].
    apply getMappedBlocksEqBuiltWithWriteAcc with requisitionedBlockInCurrPartAddr bentry; trivial.
    1-11: unfold consistency1 in *; intuition. unfold checkChild. rewrite HlookupBlock.
    unfold sh1entryPDflag in *.
    destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (memory s0) beqAddr); trivial.
    destruct v; trivial.
  }

  assert(blockAndNextAreSideBySide s).
  { (* BEGIN blockAndNextAreSideBySide s *)
    assert(Hcons0: blockAndNextAreSideBySide s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros partition block scentryaddr scnext endaddr HpartIsPart HblockBisMapped HendBlock Hsce HbeqNextNull
      Hnext. rewrite HgetPartsEq in *. assert(HpartIsPDT: isPDT partition s0).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedEq in *; trivial. assert(HendBlocks0: bentryEndAddr block endaddr s0).
    {
      unfold bentryEndAddr in *.
      destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      pose proof (stableBEFieldsIsBuiltRev statesList s0 parentsList currentPart requisitionedBlockStart
        requisitionedBlockEnd false s block b HlookupBlock HisBuilt) as HeqFields.
      destruct HeqFields as [bentrys0 (HlookupBlocks0 & _ & _ & _ & _ & _ & HrangeEq)]. rewrite HlookupBlocks0.
      rewrite HrangeEq. assumption.
    }
    assert(HnextBiss0: scentryNext scentryaddr scnext s0).
    {
      unfold scentryNext in *. rewrite <-lookupSCEEqWriteAccessRev with statesList s0 parentsList scentryaddr
        requisitionedBlockStart requisitionedBlockEnd false s currentPart; trivial. unfold isSCE.
      destruct (lookup scentryaddr (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockBisMapped HendBlocks0 Hsce
      HbeqNextNull HnextBiss0). destruct Hcons0 as (Hcons0 & HnextMapped). split; trivial.
    unfold bentryStartAddr in *.
    destruct (lookup scnext (memory s0) beqAddr) eqn:HlookupNexts0; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart requisitionedBlockStart
      requisitionedBlockEnd false s scnext b HlookupNexts0 HisBuilt) as HeqFields.
    destruct HeqFields as [bentrys0 (HlookupBlocks0 & _ & _ & _ & _ & _ & HrangeEq)]. rewrite HlookupBlocks0.
    rewrite HrangeEq. assumption.
    (* END blockAndNextAreSideBySide *)
  }

  assert(parentBlocksBoundsIfNoNext s).
  { (* BEGIN parentBlocksBoundsIfNoNext s *)
    assert(Hcons0: parentBlocksBoundsIfNoNext s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockBisMapped HstartBlock HendBlock
      Hsce Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEq in *. assert(HpartIsPDT: isPDT partition s0).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedEq in HblockBisMapped; trivial.
    assert(Hblocks0: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
    {
      unfold bentryEndAddr in *. unfold bentryStartAddr in *.
      destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      pose proof (stableBEFieldsIsBuiltRev statesList s0 parentsList currentPart requisitionedBlockStart
        requisitionedBlockEnd false s block b HlookupBlock HisBuilt) as HeqFields.
      destruct HeqFields as [bentrys0 (HlookupBlocks0 & _ & _ & _ & _ & _ & HrangeEq)]. rewrite HlookupBlocks0.
      rewrite HrangeEq. auto.
    }
    destruct Hblocks0 as (HstartBlocks0 & HendBlocks0). assert(HnextBiss0: scentryNext scentryaddr nullAddr s0).
    {
      unfold scentryNext in *. rewrite <-lookupSCEEqWriteAccessRev with statesList s0 parentsList scentryaddr
        requisitionedBlockStart requisitionedBlockEnd false s currentPart; trivial. unfold isSCE.
      destruct (lookup scentryaddr (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    assert(HlookupParts0: exists pdentrys0, lookup partition (memory s0) beqAddr = Some (PDT pdentrys0)
      /\ parent pdentry = parent pdentrys0).
    {
      pose proof (stablePDTFieldsIsBuiltRev statesList s0 parentsList currentPart pdentry requisitionedBlockStart
        requisitionedBlockEnd false s partition HcurrIsPDTs0 HisBuilt HlookupPart) as HeqFields.
      destruct HeqFields as [pdentrys0 (HlookupParts0 & _ & _ & _ & _ & HparentsEq & _)]. exists pdentrys0. auto.
    }
    destruct HlookupParts0 as [pdentrys0 (HlookupParts0 & HparentsEq)]. rewrite HparentsEq.
    specialize(Hcons0 partition pdentrys0 block scentryaddr startaddr endaddr HpartIsPart HblockBisMapped
      HstartBlocks0 HendBlocks0 Hsce HnextBiss0 HbeqPartRoot HlookupParts0).
    destruct Hcons0 as [blockParent [startP (HblockPMapped & HstartP & HendP & HlebStarts)]]. exists blockParent.
    exists startP. assert(isPDT (parent pdentrys0) s0).
    {
      unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
      destruct (lookup (parent pdentrys0) (memory s0) beqAddr); try(simpl in HblockPMapped; congruence).
      destruct v; try(simpl in HblockPMapped; congruence). trivial.
    }
    rewrite HgetMappedEq; trivial. split; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    destruct (lookup blockParent (memory s0) beqAddr) eqn:HlookupBP; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    pose proof (stableBEFieldsIsBuilt statesList s0 parentsList currentPart requisitionedBlockStart
      requisitionedBlockEnd false s blockParent b HlookupBP HisBuilt) as HeqFields.
    destruct HeqFields as [bentrys0 (HlookupBPs0 & _ & _ & _ & _ & _ & HrangeEq)]. rewrite HlookupBPs0.
    rewrite HrangeEq. auto.
    (* END parentBlocksBoundsIfNoNext *)
  }
  (*assert(forall kern part, In kern (getConfigBlocks part s) -> kern <> requisitionedBlockStart).
  {
    intros kern part HkernInConf. assert(HconfEq: getConfigBlocks part s = getConfigBlocks part s0).
    {
      assert(isPDT part s0).
      {
        unfold getConfigBlocks in HkernInConf. unfold isPDT.
        destruct (lookup part (memory s) beqAddr) eqn:HlookupPart; try(simpl in HkernInConf; exfalso; congruence).
        destruct v; try(simpl in HkernInConf; exfalso; congruence).
        pose proof(stablePDTFieldsIsBuiltRev statesList s0 parentsList currentPart p requisitionedBlockStart
          requisitionedBlockEnd false s part HcurrIsPDTs0 HisBuilt HlookupPart) as Hres.
        destruct Hres as [pdentryPart (HlookupParts0 & _)]. rewrite HlookupParts0. trivial.
      }
      revert HisBuilt. apply getConfigBlocksEqBuiltWithWriteAcc; trivial.
    }
    rewrite HconfEq in *. apply HstartNotConf with part; assumption.
  }*)

  assert(childLocMappedInChild s).
  { (* BEGIN childLocMappedInChild s *)
    revert HisBuilt. apply childLocMappedInChildPreservedIsBuiltRecFalse with pdentryCurr
      requisitionedBlockInCurrPartAddr; trivial; unfold consistency1 in *; intuition.
    (* END childLocMappedInChild *)
  }

  assert(childLocHasSameStart s).
  { (* BEGIN childLocHasSameStart s *)
    intros part block sh1entryaddr blockChild idchild.
    specialize(HsameStarts0 part block sh1entryaddr blockChild idchild).
    revert HisBuilt. apply childLocHasSameStartPartialPreservedIsBuiltRec with
      requisitionedBlockInCurrPartAddr; trivial.
    1-10: unfold consistency1 in *; intuition. intro. exfalso; congruence.
    (* END childLocHasSameStart *)
  }
  rewrite HgetChildrenEq. rewrite HgetFreeEq. intuition.
}
intro oldKStructurePointer. eapply bindRev.
{ (** MAL.writeNextFromKernelStructureStartLight **)
  eapply weaken. apply writeNextFromKernelStructureStartLight. simpl. intros s Hprops. apply Hprops.
}
intro. eapply bindRev.
{ (** MAL.writePDStructurePointer **)
  eapply weaken. apply writePDStructurePointer. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s0 ((Hprops & Hstruct) & Hs)]. unfold isPDT. unfold pdentryStructurePointer in *. rewrite Hs.
  assert(HlookupNext: lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr
    = Some (PADDR nullAddr)) by intuition. simpl.
  assert(newKStructurePointer = requisitionedBlockStart) by intuition. subst newKStructurePointer.
  destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) globalIdPD) eqn:HbeqNextGlob.
  {
    rewrite <-DTL.beqAddrTrue in HbeqNextGlob. rewrite HbeqNextGlob in *. rewrite HlookupNext in *. congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  destruct (lookup globalIdPD (memory s0) beqAddr); try(congruence). destruct v; try(congruence). trivial.
}
intro. eapply bindRev.
{ (** indexPredM **)
  eapply weaken. apply WP.Index.pred. intros s Hprops. simpl.
  destruct Hprops as [s1 [pdentry [newPDentry ([s0 Hpropss0] & HlookupGlobs1 & HnewPD & Hs)]]].
  assert(HentriesNb: kernelentriesnb = CIndex kernelStructureEntriesNb) by intuition. unfold CIndex in HentriesNb.
  pose proof KSEntriesNbLessThanMaxIdx. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
  split; try(rewrite HentriesNb; cbn; lia). intro Hi.
  instantiate(1 := fun idx s => i idx = kernelentriesnb - 1
    /\ beqAddr nullAddr globalIdPD = false
    /\ false = StateLib.Index.leb maxnbprepare nbPrepare
    /\ kernelentriesnb = CIndex kernelStructureEntriesNb
    /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
    /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
    /\ kStructureTotalLength = Constants.kernelStructureTotalLength
    /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
    /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
    /\ newKStructurePointer = requisitionedBlockStart
    /\ i maxnbprepare = maxNbPrepare
    /\ exists s1 s0 pdentry newPDentry,
        s =
          {|
            currentPartition := currentPartition s1;
            memory := add globalIdPD (PDT newPDentry) (memory s1) beqAddr
          |}
        /\ newPDentry = {|
                          structure := newKStructurePointer;
                          firstfreeslot := firstfreeslot pdentry;
                          nbfreeslots := nbfreeslots pdentry;
                          nbprepare := nbprepare pdentry;
                          parent := parent pdentry;
                          MPU := MPU pdentry;
                          vidtAddr := vidtAddr pdentry
                        |}
        /\ lookup globalIdPD (memory s1) beqAddr = Some (PDT pdentry)
        /\ s1 =
             {|
               currentPartition := currentPartition s0;
               memory :=
                 add (CPaddr (newKStructurePointer + nextoffset)) (PADDR oldKStructurePointer) 
                   (memory s0) beqAddr
             |}
        /\ pdentryStructurePointer globalIdPD oldKStructurePointer s0
        /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
        /\ consistency1 s0 /\ noDupMappedPaddrList s0 /\ sharedBlockPointsToChild s0
        /\ adressesRangePreservedIfOriginAndNextOk s0 /\ childsBlocksPropsInParent s0
        /\ noChildImpliesAddressesNotShared s0 /\ kernelsAreNotAccessible s0
        /\ accessibleParentPaddrIsAccessibleIntoChild s0 /\ blockAndNextAreSideBySide s0
        /\ parentBlocksBoundsIfNoNext s0 /\ childLocMappedInChild s0 /\ childLocHasSameStart s0
        /\ pdentryNbPrepare globalIdPD nbPrepare s0
        /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s0
        /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s0
        /\ bentryPFlag requisitionedBlockInCurrPartAddr true s0
        /\ bentryAFlag requisitionedBlockInCurrPartAddr false s0
        /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)
        /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s0
        /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
              (CIndex (kernelStructureEntriesNb-1)) s0
        /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s0
        /\ currentPart = currentPartition s0
        /\ In currentPart (getPartitions multiplexer s0)
        /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s0))
        /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr)
        /\ (forall part kernList, isListOfKernels kernList part s0 -> ~ In requisitionedBlockStart kernList)
        /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
              -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0)
        /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
            -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s0)
        /\ (forall partition, isPDT partition s0
            -> Lib.disjoint
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              (getFreeSlotsList partition s0))
        /\ wellFormedFreeSlotsList
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)) <> False
        /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
        /\ (forall block, In block
             (filterOptionPaddr
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)))
              -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                  /\ kernIdx < kernelStructureEntriesNb)
        /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
            -> block = CPaddr (requisitionedBlockStart+kernIdx)
            -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0
                (CIndex kernelStructureEntriesNb))))
        /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              (SomePaddr requisitionedBlockStart)
            = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
        /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s0
        /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
              -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1))
                  s0)
        /\ (forall addr, In addr (filterOptionPaddr
                (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0 (CIndex (kernelStructureEntriesNb-1))))
              -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
        /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s0
        /\ (forall part,
              Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
              (getAllPaddrConfigAux (getConfigBlocks part s0) s0))).
  simpl. intuition; exists s1; exists s0; exists pdentry; exists newPDentry; intuition.
}
intro lastidx. eapply bindRev.
{ (** MAL.getBlockEntryAddrFromKernelStructureStart **)
  eapply weaken. apply getBlockEntryAddrFromKernelStructureStart. intros s Hprops. simpl.
  assert(Hrange: BlocksRangeFromKernelStartIsBE s).
  {
    destruct Hprops as (Hlast & HbeqNullGlob & _ & _ & _ & _ & _ & _ & _ & HblockEq & _ & [s1 [s0 [pdentry [newPDentry
      (Hs & HnewPD & HlookupGlobs1 & Hs1 & Hprops)]]]]).
    assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by (unfold consistency1 in *; intuition).
    intros kernel idx HkernIsKS HltIdxKernEntries. unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
    destruct (beqAddr globalIdPD kernel) eqn:HbeqGlobKern; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption). rewrite Hs1 in HkernIsKS. simpl in *.
    destruct (beqAddr (CPaddr (newKStructurePointer + nextoffset)) kernel) eqn:HbeqNextKern; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
    specialize(Hcons0 kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *.
    assert(HlookupNextEq: lookup (CPaddr (kernel + idx)) (memory s1) beqAddr
      = lookup (CPaddr (kernel + idx)) (memory s0) beqAddr).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (newKStructurePointer + nextoffset)) (CPaddr (kernel + idx))) eqn:HbeqNextIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextIdx. subst newKStructurePointer. rewrite HbeqNextIdx in *.
        assert(HlookupNext: lookup (CPaddr (kernel + idx)) (memory s0) beqAddr = Some (PADDR nullAddr)) by intuition.
        rewrite HlookupNext in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    rewrite <-HlookupNextEq in Hcons0. rewrite Hs. simpl.
    destruct (beqAddr globalIdPD (CPaddr (kernel + idx))) eqn:HbeqGlobIdx.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobIdx. rewrite HbeqGlobIdx in *. rewrite HlookupGlobs1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HPDchild: sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s).
  {
    destruct Hprops as (Hlast & _ & _ & HentriesNb & _ & _ & _ & _ & _ & HblockEq & _ & [s1 [s0 [pdentry [newPDentry
        (Hs & HnewPD & HlookupGlobs1 & Hs1 & Hstructs0 & Hprops)]]]]).
    assert(HPDchilds0: sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s0)
      by intuition.
    assert(HlookupNext: lookup (CPaddr (requisitionedBlockStart+nextoffset)) (memory s0) beqAddr
      = Some (PADDR nullAddr)) by intuition. subst newKStructurePointer. unfold sh1entryPDchild in *. rewrite Hs.
    simpl. destruct (beqAddr globalIdPD (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))) eqn:HbeqGlobSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobSh1. rewrite <-HbeqGlobSh1 in *. unfold pdentryStructurePointer in *.
      destruct (lookup globalIdPD (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset))
      (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))) eqn:HbeqNextSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextSh1. rewrite HbeqNextSh1 in *. rewrite HlookupNext in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
  }
  split. apply (conj (conj Hprops Hrange) HPDchild). split; trivial.
  destruct Hprops as (Hlast & _ & _ & HentriesNb & _ & _ & _ & _ & _ & HblockEq & _ & [s1 [s0 [pdentry [newPDentry (Hs
      & HnewPD & HlookupGlobs1 & Hs1 & Hprops)]]]]). subst kernelentriesnb. unfold CIndex in Hlast.
  pose proof KSEntriesNbLessThanMaxIdx. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
  split; try(rewrite Hlast; cbn; lia). subst newKStructurePointer.
  assert(HkernIdx: bentryBlockIndex requisitionedBlockStart (CIndex 0) s0) by intuition. unfold isKS.
  assert(bentryBlockIndex requisitionedBlockStart (CIndex 0) s1).
  {
    unfold bentryBlockIndex in *. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) requisitionedBlockStart) eqn:HbeqNextStart.
    {
      assert(HlookupNext: lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr
        = Some (PADDR nullAddr)) by intuition.
      rewrite <-DTL.beqAddrTrue in HbeqNextStart. rewrite HbeqNextStart in *. rewrite HlookupNext in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  unfold bentryBlockIndex in *. rewrite Hs. simpl.
  destruct (beqAddr globalIdPD requisitionedBlockStart) eqn:HbeqGlobStart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqGlobStart. rewrite HbeqGlobStart in *. rewrite HlookupGlobs1 in *.
    congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  destruct (lookup requisitionedBlockStart (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
  unfold zero. apply eq_sym. assumption.
}
intro lastBlockEntryAddr. eapply bindRev.
{ (** MAL.readPDFirstFreeSlotPointer **)
  eapply weaken. apply readPDFirstFreeSlotPointer. intros s Hprops. simpl.
  destruct Hprops as ((((Hlast & HbeqNullGlob & HlebMaxNbPrep & HentriesNb & HblockEq & HbeqNullBlock & HlenKern &
    HltSizeLen & Hsize & HstartEq & Hmax & [s1 [s0 [pdentry [newPDentry (Hs & HnewPDentry & HlookupGlob & Hprops)]]]])
    & Hranges) & HPDchild) & HlastBlock & HlastBlockIsBE).
  assert(HlookupGlobs: lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)).
  {
    rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity.
  }
  instantiate(1 := fun s => isBE lastBlockEntryAddr s
    /\ lastBlockEntryAddr = CPaddr (newKStructurePointer + blkoffset + lastidx)
    /\ BlocksRangeFromKernelStartIsBE s
    /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s
    /\ i lastidx = kernelentriesnb - 1
    /\ beqAddr nullAddr globalIdPD = false
    /\ false = StateLib.Index.leb maxnbprepare nbPrepare
    /\ kernelentriesnb = CIndex kernelStructureEntriesNb
    /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
    /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
    /\ kStructureTotalLength = Constants.kernelStructureTotalLength
    /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
    /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
    /\ newKStructurePointer = requisitionedBlockStart
    /\ i maxnbprepare = maxNbPrepare
    /\ exists s1 s0 pdentry newPDentry,
        s =
          {|
            currentPartition := currentPartition s1;
            memory := add globalIdPD (PDT newPDentry) (memory s1) beqAddr
          |}
        /\ newPDentry = {|
                          structure := newKStructurePointer;
                          firstfreeslot := firstfreeslot pdentry;
                          nbfreeslots := nbfreeslots pdentry;
                          nbprepare := nbprepare pdentry;
                          parent := parent pdentry;
                          MPU := MPU pdentry;
                          vidtAddr := vidtAddr pdentry
                        |}
        /\ lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)
        /\ lookup globalIdPD (memory s1) beqAddr = Some (PDT pdentry)
        /\ s1 =
             {|
               currentPartition := currentPartition s0;
               memory :=
                 add (CPaddr (newKStructurePointer + nextoffset)) (PADDR oldKStructurePointer) 
                   (memory s0) beqAddr
             |}
        /\ pdentryStructurePointer globalIdPD oldKStructurePointer s0
        /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
        /\ consistency1 s0 /\ noDupMappedPaddrList s0 /\ sharedBlockPointsToChild s0
        /\ adressesRangePreservedIfOriginAndNextOk s0 /\ childsBlocksPropsInParent s0
        /\ noChildImpliesAddressesNotShared s0 /\ kernelsAreNotAccessible s0
        /\ accessibleParentPaddrIsAccessibleIntoChild s0 /\ blockAndNextAreSideBySide s0
        /\ parentBlocksBoundsIfNoNext s0 /\ childLocMappedInChild s0 /\ childLocHasSameStart s0
        /\ pdentryNbPrepare globalIdPD nbPrepare s0
        /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s0
        /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s0
        /\ bentryPFlag requisitionedBlockInCurrPartAddr true s0
        /\ bentryAFlag requisitionedBlockInCurrPartAddr false s0
        /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)
        /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s0
        /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
              (CIndex (kernelStructureEntriesNb-1)) s0
        /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s0
        /\ currentPart = currentPartition s0
        /\ In currentPart (getPartitions multiplexer s0)
        /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s0))
        /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr)
        /\ (forall part kernList, isListOfKernels kernList part s0 -> ~ In requisitionedBlockStart kernList)
        /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
              -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0)
        /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
            -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s0)
        /\ (forall partition, isPDT partition s0
            -> Lib.disjoint
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              (getFreeSlotsList partition s0))
        /\ wellFormedFreeSlotsList
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)) <> False
        /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
        /\ (forall block, In block
             (filterOptionPaddr
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)))
              -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                  /\ kernIdx < kernelStructureEntriesNb)
        /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
            -> block = CPaddr (requisitionedBlockStart+kernIdx)
            -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0
                (CIndex kernelStructureEntriesNb))))
        /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              (SomePaddr requisitionedBlockStart)
            = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
        /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s0
        /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
              -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1))
                  s0)
        /\ (forall addr, In addr (filterOptionPaddr
                (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0 (CIndex (kernelStructureEntriesNb-1))))
              -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
        /\ (forall addr, In addr (filterOptionPaddr
                (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0 (CIndex (kernelStructureEntriesNb-1))))
              -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
        /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s0
        /\ (forall part,
              Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
              (getAllPaddrConfigAux (getConfigBlocks part s0) s0))).
  unfold isPDT. rewrite HlookupGlobs. intuition; exists s1; exists s0; exists pdentry; exists newPDentry; intuition.
}
intro currFirstFreeSlot. eapply bindRev.
{ (** MAL.writeBlockEndFromBlockEntryAddr **)
  eapply weaken. apply writeBlockEndFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as ((HlastBlockIsBE & HlastBlock & Hranges & HPDchild & Hlast & HbeqNullGlob & HlebMaxNbPrep &
    HentriesNb & HblockEq & HbeqNullBlock & HlenKern & HltSizeLen & Hsize & HstartEq & Hmax & [s1 [s0 [pdentry
    [newPDentry Hprops]]]]) & HfirstFree).
  unfold isBE in *. destruct (lookup lastBlockEntryAddr (memory s) beqAddr) eqn:HlookupLast; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b. split; trivial.
  instantiate(1 := fun _ s =>
    (
      exists s2 s1 s0 pdentry newPDentry bentryStart,
        s = {|
              currentPartition := currentPartition s2;
              memory :=
                add lastBlockEntryAddr
                  (BE
                     (CBlockEntry (read bentryStart) (write bentryStart) (exec bentryStart) (present bentryStart)
                        (accessible bentryStart) (blockindex bentryStart)
                        (CBlock (startAddr (blockrange bentryStart)) currFirstFreeSlot)))
                  (memory s2) beqAddr
            |}
        /\ s2 =
            {|
              currentPartition := currentPartition s1;
              memory := add globalIdPD (PDT newPDentry) (memory s1) beqAddr
            |}
        /\ newPDentry = {|
                          structure := newKStructurePointer;
                          firstfreeslot := firstfreeslot pdentry;
                          nbfreeslots := nbfreeslots pdentry;
                          nbprepare := nbprepare pdentry;
                          parent := parent pdentry;
                          MPU := MPU pdentry;
                          vidtAddr := vidtAddr pdentry
                        |}
        /\ lookup lastBlockEntryAddr (memory s2) beqAddr = Some (BE bentryStart)
        /\ lookup globalIdPD (memory s2) beqAddr = Some (PDT newPDentry)
        /\ pdentryFirstFreeSlot globalIdPD currFirstFreeSlot s2
        /\ BlocksRangeFromKernelStartIsBE s2
        /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s2
        /\ lookup globalIdPD (memory s1) beqAddr = Some (PDT pdentry)
        /\ s1 =
             {|
               currentPartition := currentPartition s0;
               memory :=
                 add (CPaddr (newKStructurePointer + nextoffset)) (PADDR oldKStructurePointer) 
                   (memory s0) beqAddr
             |}
        /\ pdentryStructurePointer globalIdPD oldKStructurePointer s0
        /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
        /\ consistency1 s0 /\ noDupMappedPaddrList s0 /\ sharedBlockPointsToChild s0
        /\ adressesRangePreservedIfOriginAndNextOk s0 /\ childsBlocksPropsInParent s0
        /\ noChildImpliesAddressesNotShared s0 /\ kernelsAreNotAccessible s0
        /\ accessibleParentPaddrIsAccessibleIntoChild s0 /\ blockAndNextAreSideBySide s0
        /\ parentBlocksBoundsIfNoNext s0 /\ childLocMappedInChild s0 /\ childLocHasSameStart s0
        /\ pdentryNbPrepare globalIdPD nbPrepare s0
        /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s0
        /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s0
        /\ bentryPFlag requisitionedBlockInCurrPartAddr true s0
        /\ bentryAFlag requisitionedBlockInCurrPartAddr false s0
        /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)
        /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s0
        /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
              (CIndex (kernelStructureEntriesNb-1)) s0
        /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s0
        /\ currentPart = currentPartition s0
        /\ In currentPart (getPartitions multiplexer s0)
        /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s0))
        /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr)
        /\ (forall part kernList, isListOfKernels kernList part s0 -> ~ In requisitionedBlockStart kernList)
        /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
              -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0)
        /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
            -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s0)
        /\ (forall partition, isPDT partition s0
            -> Lib.disjoint
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              (getFreeSlotsList partition s0))
        /\ wellFormedFreeSlotsList
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)) <> False
        /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
        /\ (forall block, In block
             (filterOptionPaddr
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)))
              -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                  /\ kernIdx < kernelStructureEntriesNb)
        /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
            -> block = CPaddr (requisitionedBlockStart+kernIdx)
            -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0
                (CIndex kernelStructureEntriesNb))))
        /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              (SomePaddr requisitionedBlockStart)
            = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
        /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s0
        /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
              -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1))
                  s0)
        /\ (forall addr, In addr (filterOptionPaddr
                (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0 (CIndex (kernelStructureEntriesNb-1))))
              -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
        /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s0
        /\ (forall part,
              Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
              (getAllPaddrConfigAux (getConfigBlocks part s0) s0))
    )
    /\ lastBlockEntryAddr = CPaddr (newKStructurePointer + blkoffset + lastidx)
    /\ i lastidx = kernelentriesnb - 1
    /\ beqAddr nullAddr globalIdPD = false
    /\ false = StateLib.Index.leb maxnbprepare nbPrepare
    /\ kernelentriesnb = CIndex kernelStructureEntriesNb
    /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
    /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
    /\ kStructureTotalLength = Constants.kernelStructureTotalLength
    /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
    /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
    /\ newKStructurePointer = requisitionedBlockStart
    /\ i maxnbprepare = maxNbPrepare).
  simpl. intuition; exists s; exists s1; exists s0; exists pdentry; exists newPDentry; exists b; intuition.
}
intro. eapply bindRev.
{ (** MAL.writePDFirstFreeSlotPointer **)
  eapply weaken. apply writePDFirstFreeSlotPointer. intros s Hprops. simpl.
  destruct Hprops as ([s2 [s1 [s0 [pdentry [newPDentry [bentryStart (Hs & Hs2 & HnewPD & HlookupLasts2 & HlookupGlobs2
    & Hprops)]]]]]] & HpropsBis).
  assert(lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)).
  {
    rewrite Hs. simpl. destruct (beqAddr lastBlockEntryAddr globalIdPD) eqn:HbeqLastGlob.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastGlob. rewrite HbeqLastGlob in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  exists newPDentry. split; trivial.
  instantiate(1 := fun _ s =>
    (
      exists s3 s2 s1 s0 pdentry newPDentry prevPDentry bentryStart ,
        s = {|
              currentPartition := currentPartition s3;
              memory :=
                add globalIdPD
                  (PDT newPDentry) (memory s3) beqAddr
            |}
        /\ newPDentry = {|
                          structure := structure prevPDentry;
                          firstfreeslot := newKStructurePointer;
                          nbfreeslots := nbfreeslots prevPDentry;
                          nbprepare := nbprepare prevPDentry;
                          parent := parent prevPDentry;
                          MPU := MPU prevPDentry;
                          vidtAddr := vidtAddr prevPDentry
                        |}
        /\ lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)
        /\ s3 = {|
              currentPartition := currentPartition s2;
              memory :=
                add lastBlockEntryAddr
                  (BE
                     (CBlockEntry (read bentryStart) (write bentryStart) (exec bentryStart) (present bentryStart)
                        (accessible bentryStart) (blockindex bentryStart)
                        (CBlock (startAddr (blockrange bentryStart)) currFirstFreeSlot)))
                  (memory s2) beqAddr
            |}
        /\ lookup globalIdPD (memory s3) beqAddr = Some (PDT prevPDentry)
        /\ s2 =
            {|
              currentPartition := currentPartition s1;
              memory := add globalIdPD (PDT prevPDentry) (memory s1) beqAddr
            |}
        /\ prevPDentry = {|
                          structure := newKStructurePointer;
                          firstfreeslot := firstfreeslot pdentry;
                          nbfreeslots := nbfreeslots pdentry;
                          nbprepare := nbprepare pdentry;
                          parent := parent pdentry;
                          MPU := MPU pdentry;
                          vidtAddr := vidtAddr pdentry
                        |}
        /\ lookup lastBlockEntryAddr (memory s2) beqAddr = Some (BE bentryStart)
        /\ lookup globalIdPD (memory s2) beqAddr = Some (PDT prevPDentry)
        /\ pdentryFirstFreeSlot globalIdPD currFirstFreeSlot s2
        /\ BlocksRangeFromKernelStartIsBE s2
        /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s2
        /\ lookup globalIdPD (memory s1) beqAddr = Some (PDT pdentry)
        /\ s1 =
             {|
               currentPartition := currentPartition s0;
               memory :=
                 add (CPaddr (newKStructurePointer + nextoffset)) (PADDR oldKStructurePointer) 
                   (memory s0) beqAddr
             |}
        /\ pdentryStructurePointer globalIdPD oldKStructurePointer s0
        /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
        /\ consistency1 s0 /\ noDupMappedPaddrList s0 /\ sharedBlockPointsToChild s0
        /\ adressesRangePreservedIfOriginAndNextOk s0 /\ childsBlocksPropsInParent s0
        /\ noChildImpliesAddressesNotShared s0 /\ kernelsAreNotAccessible s0
        /\ accessibleParentPaddrIsAccessibleIntoChild s0 /\ blockAndNextAreSideBySide s0
        /\ parentBlocksBoundsIfNoNext s0 /\ childLocMappedInChild s0 /\ childLocHasSameStart s0
        /\ pdentryNbPrepare globalIdPD nbPrepare s0
        /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s0
        /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s0
        /\ bentryPFlag requisitionedBlockInCurrPartAddr true s0
        /\ bentryAFlag requisitionedBlockInCurrPartAddr false s0
        /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)
        /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s0
        /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
              (CIndex (kernelStructureEntriesNb-1)) s0
        /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s0
        /\ currentPart = currentPartition s0
        /\ In currentPart (getPartitions multiplexer s0)
        /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s0))
        /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr)
        /\ (forall part kernList, isListOfKernels kernList part s0 -> ~ In requisitionedBlockStart kernList)
        /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
              -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0)
        /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
            -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s0)
        /\ (forall partition, isPDT partition s0
            -> Lib.disjoint
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              (getFreeSlotsList partition s0))
        /\ wellFormedFreeSlotsList
              (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)) <> False
        /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
        /\ (forall block, In block
             (filterOptionPaddr
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)))
              -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                  /\ kernIdx < kernelStructureEntriesNb)
        /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
            -> block = CPaddr (requisitionedBlockStart+kernIdx)
            -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0
                (CIndex kernelStructureEntriesNb))))
        /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              (SomePaddr requisitionedBlockStart)
            = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
        /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s0
        /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
              -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1))
                  s0)
        /\ (forall addr, In addr (filterOptionPaddr
                (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0 (CIndex (kernelStructureEntriesNb-1))))
              -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
        /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s0
        /\ (forall part,
              Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
              (getAllPaddrConfigAux (getConfigBlocks part s0) s0))
    )
    /\ lastBlockEntryAddr = CPaddr (newKStructurePointer + blkoffset + lastidx)
    /\ i lastidx = kernelentriesnb - 1
    /\ beqAddr nullAddr globalIdPD = false
    /\ false = StateLib.Index.leb maxnbprepare nbPrepare
    /\ kernelentriesnb = CIndex kernelStructureEntriesNb
    /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
    /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
    /\ kStructureTotalLength = Constants.kernelStructureTotalLength
    /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
    /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
    /\ newKStructurePointer = requisitionedBlockStart
    /\ i maxnbprepare = maxNbPrepare).
  simpl. intuition; exists s; exists s2; exists s1; exists s0; exists pdentry;
    exists {|
             structure := structure newPDentry;
             firstfreeslot := newKStructurePointer;
             nbfreeslots := nbfreeslots newPDentry;
             nbprepare := nbprepare newPDentry;
             parent := parent newPDentry;
             MPU := MPU newPDentry;
             vidtAddr := vidtAddr newPDentry
           |}; exists newPDentry; exists bentryStart; intuition; rewrite beqAddrTrue; reflexivity.
}
intro. eapply bindRev.
{ (** MAL.readPDNbFreeSlots **)
  eapply weaken. apply readPDNbFreeSlots. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as ([s3 [s2 [s1 [s0 [pdentry [newPDentry [prevPDentry [bentryStart (Hs & HnewPD & HlookupGlobs &
    _)]]]]]]]] & _). unfold isPDT. rewrite HlookupGlobs. trivial.
}
intro currentNbFreeSlots. eapply bindRev.
{ (** indexAddM **)
  unfold indexAddM. destruct (le_dec (currentNbFreeSlots + kernelentriesnb) maxIdx) eqn:HleFreePlusEntriesNbMax.
  - eapply weaken. apply WP.ret. intros s Hprops.
    instantiate(1 := fun newFreeNb s => i newFreeNb = currentNbFreeSlots + kernelentriesnb
      /\ pdentryNbFreeSlots globalIdPD currentNbFreeSlots s
      /\ (
          exists s3 s2 s1 s0 pdentry newPDentry prevPDentry bentryStart,
            s = {|
                  currentPartition := currentPartition s3;
                  memory :=
                    add globalIdPD
                      (PDT newPDentry) (memory s3) beqAddr
                |}
            /\ newPDentry = {|
                              structure := structure prevPDentry;
                              firstfreeslot := newKStructurePointer;
                              nbfreeslots := nbfreeslots prevPDentry;
                              nbprepare := nbprepare prevPDentry;
                              parent := parent prevPDentry;
                              MPU := MPU prevPDentry;
                              vidtAddr := vidtAddr prevPDentry
                            |}
            /\ lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)
            /\ s3 = {|
                  currentPartition := currentPartition s2;
                  memory :=
                    add lastBlockEntryAddr
                      (BE
                         (CBlockEntry (read bentryStart) (write bentryStart) (exec bentryStart) (present bentryStart)
                            (accessible bentryStart) (blockindex bentryStart)
                            (CBlock (startAddr (blockrange bentryStart)) currFirstFreeSlot)))
                      (memory s2) beqAddr
                |}
            /\ lookup globalIdPD (memory s3) beqAddr = Some (PDT prevPDentry)
            /\ s2 =
                {|
                  currentPartition := currentPartition s1;
                  memory := add globalIdPD (PDT prevPDentry) (memory s1) beqAddr
                |}
            /\ prevPDentry = {|
                              structure := newKStructurePointer;
                              firstfreeslot := firstfreeslot pdentry;
                              nbfreeslots := nbfreeslots pdentry;
                              nbprepare := nbprepare pdentry;
                              parent := parent pdentry;
                              MPU := MPU pdentry;
                              vidtAddr := vidtAddr pdentry
                            |}
            /\ lookup lastBlockEntryAddr (memory s2) beqAddr = Some (BE bentryStart)
            /\ lookup globalIdPD (memory s2) beqAddr = Some (PDT prevPDentry)
            /\ pdentryFirstFreeSlot globalIdPD currFirstFreeSlot s2
            /\ BlocksRangeFromKernelStartIsBE s2
            /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s2
            /\ lookup globalIdPD (memory s1) beqAddr = Some (PDT pdentry)
            /\ s1 =
                 {|
                   currentPartition := currentPartition s0;
                   memory :=
                     add (CPaddr (newKStructurePointer + nextoffset)) (PADDR oldKStructurePointer) 
                       (memory s0) beqAddr
                 |}
            /\ pdentryStructurePointer globalIdPD oldKStructurePointer s0
            /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
            /\ consistency1 s0 /\ noDupMappedPaddrList s0 /\ sharedBlockPointsToChild s0
            /\ adressesRangePreservedIfOriginAndNextOk s0 /\ childsBlocksPropsInParent s0
            /\ noChildImpliesAddressesNotShared s0 /\ kernelsAreNotAccessible s0
            /\ accessibleParentPaddrIsAccessibleIntoChild s0 /\ blockAndNextAreSideBySide s0
            /\ parentBlocksBoundsIfNoNext s0 /\ childLocMappedInChild s0 /\ childLocHasSameStart s0
            /\ pdentryNbPrepare globalIdPD nbPrepare s0
            /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s0
            /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s0
            /\ bentryPFlag requisitionedBlockInCurrPartAddr true s0
            /\ bentryAFlag requisitionedBlockInCurrPartAddr false s0
            /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)
            /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s0
            /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
                  (CIndex (kernelStructureEntriesNb-1)) s0
            /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s0
            /\ currentPart = currentPartition s0
            /\ In currentPart (getPartitions multiplexer s0)
            /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s0))
            /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr)
            /\ (forall part kernList, isListOfKernels kernList part s0 -> ~ In requisitionedBlockStart kernList)
            /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                  -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0)
            /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s0)
            /\ (forall partition, isPDT partition s0
                -> Lib.disjoint
                  (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
                  (getFreeSlotsList partition s0))
            /\ wellFormedFreeSlotsList
                  (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
                <> False
            /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
            /\ (forall block, In block
                 (filterOptionPaddr
                    (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)))
                  -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                      /\ kernIdx < kernelStructureEntriesNb)
            /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
                -> block = CPaddr (requisitionedBlockStart+kernIdx)
                -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0
                    (CIndex kernelStructureEntriesNb))))
            /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
                  (SomePaddr requisitionedBlockStart)
                = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
            /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s0
            /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
                  -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx))
                      (CPaddr (requisitionedBlockStart+blkIdx+1)) s0)
            /\ (forall addr, In addr (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart
                    s0 (CIndex (kernelStructureEntriesNb-1))))
                  -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
            /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s0
            /\ (forall part,
                  Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
                  (getAllPaddrConfigAux (getConfigBlocks part s0) s0))
        )
        /\ lastBlockEntryAddr = CPaddr (newKStructurePointer + blkoffset + lastidx)
        /\ i lastidx = kernelentriesnb - 1
        /\ beqAddr nullAddr globalIdPD = false
        /\ false = StateLib.Index.leb maxnbprepare nbPrepare
        /\ kernelentriesnb = CIndex kernelStructureEntriesNb
        /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
        /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
        /\ kStructureTotalLength = Constants.kernelStructureTotalLength
        /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
        /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
        /\ newKStructurePointer = requisitionedBlockStart
        /\ i maxnbprepare = maxNbPrepare
        /\ newFreeNb <= maxIdx). intuition.
  - eapply weaken. apply WP.undefined. intros s Hprops. simpl. destruct Hprops as (Hprops & HnbFree).
    destruct Hprops as (Hprops & _ & _ & _ & HlebNbPrepMax & HkernEntries & _ & _ & _ & _ & _ & _ & HnbPrep).
    subst kernelentriesnb. pose proof maxNbFreeSlotsLessThanMaxIdx.
    unfold StateLib.Index.leb in *. apply eq_sym in HlebNbPrepMax. apply leb_iff_conv in HlebNbPrepMax.
    unfold pdentryNbFreeSlots in *. destruct Hprops as [s3 [s2 [s1 [s0 [pdentry [newPDentry [prevPDentry [bentryStart
      (Hs & HnewPD & HlookupGlobs & Hs3 & HlookupGlobs3 & Hs2 & Hprev & _ & HlookupGlobs2 & HfirstFree & Hrange &
      HPDchild & HlookupGlobs1 & Hs1 & Hprops)]]]]]]]].
    assert(HnbPrepIsLen: nbPrepareIsNbKern s0) by (unfold consistency1 in *; intuition).
    assert(HlookupGlobs0: lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry)).
    {
      rewrite Hs1 in HlookupGlobs1. simpl in HlookupGlobs1.
      destruct (beqAddr (CPaddr (newKStructurePointer+nextoffset)) globalIdPD) eqn:HbeqNextGlob;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(HnbPrepIsLen globalIdPD pdentry HlookupGlobs0).
    assert(HnbPreps0: pdentryNbPrepare globalIdPD nbPrepare s0) by intuition. unfold pdentryNbPrepare in HnbPreps0.
    rewrite HlookupGlobs0 in *. rewrite <-HnbPreps0 in *.
    assert(HnbFreeIsLen: NbFreeSlotsISNbFreeSlotsInList s0) by (unfold consistency1 in *; intuition).
    assert(HglobIsPDT: isPDT globalIdPD s0) by (unfold isPDT; rewrite HlookupGlobs0; trivial).
    assert(HnbFrees0: pdentryNbFreeSlots globalIdPD currentNbFreeSlots s0).
    {
      unfold pdentryNbFreeSlots. rewrite HlookupGlobs0. rewrite HlookupGlobs in *. rewrite HnewPD in HnbFree.
      simpl in HnbFree. rewrite Hprev in HnbFree. simpl in HnbFree. assumption.
    }
    specialize(HnbFreeIsLen globalIdPD currentNbFreeSlots HglobIsPDT HnbFrees0).
    destruct HnbFreeIsLen as [optFreeList (HoptList & HwellFormedOpt & HnbFreeIsLen)]. subst optFreeList.
    assert(HnoDupFree: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
    specialize(HnoDupFree globalIdPD pdentry HlookupGlobs0).
    destruct HnoDupFree as [optFreeList (Hlist & _ & HnoDupFree)]. subst optFreeList.
    assert(Hincl: inclFreeSlotsBlockEntries s0) by (unfold consistency1 in *; intuition).
    specialize(Hincl globalIdPD HglobIsPDT).
    assert(HinclFilter: incl (filterOptionPaddr (getFreeSlotsList globalIdPD s0))
      (filterOptionPaddr (getKSEntries globalIdPD s0))).
    {
      intros el HelIn. apply optionIsInFilter in HelIn. apply Hincl in HelIn. apply optionIsInFilter in HelIn.
      assumption.
    }
    apply NoDup_incl_length in HinclFilter; trivial. pose proof maxIdxBiggerThanNbOfKernels.
    assert(HlenGetKS: length (filterOptionPaddr (getKSEntries globalIdPD s0))
      = length (completeListOfKernels (structure pdentry) s0) * kernelStructureEntriesNb).
    { apply nbKernEq; trivial; unfold consistency1 in *; intuition. }
    pose proof (lenWellFormed (getFreeSlotsList globalIdPD s0) HwellFormedOpt) as HfreeLenEq. rewrite HfreeLenEq in *.
    rewrite HnbPrepIsLen in *. rewrite HnbPrep in *. rewrite HlenGetKS in *. rewrite <-HnbFreeIsLen in *.
    assert(HidxEq: kernelStructureEntriesNb = CIndex kernelStructureEntriesNb).
    { unfold CIndex. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). reflexivity. }
    clear HleFreePlusEntriesNbMax. rewrite <-HidxEq in n. rewrite kernelStructureTotalLengthVal in *.
    assert(currentNbFreeSlots + kernelStructureEntriesNb <= (nbPrepare+1) * kernelStructureEntriesNb) by lia.
    assert(nbPrepare+1 <= maxNbPrepare) by lia.
    assert((nbPrepare+1) * kernelStructureEntriesNb <= maxNbPrepare * kernelStructureEntriesNb) by (cbn in *; lia).
    lia.
}
intro newNbFreeSlots. eapply bindRev.
{ (** MAL.writePDNbFreeSlots **)
  eapply weaken. apply writePDNbFreeSlots. intros s Hprops. simpl.
  destruct Hprops as (HnewNbFree & HnbFree & [s3 [s2 [s1 [s0 [pdentry [newPDentry [prevPDentry [bentryStart (Hs &
    HnewPD & HlookupGlob & Hprops)]]]]]]]] & HpropsBis). exists newPDentry. split; trivial.
  instantiate(1 := fun _ s =>
      (
        exists s4 s3 s2 s1 s0 pdentry newPDentry prevPDentry2 prevPDentry bentryStart,
          s = {|
                currentPartition := currentPartition s4;
                memory :=
                  add globalIdPD (PDT newPDentry) (memory s4) beqAddr
              |}
          /\ newPDentry = {|
                            structure := structure prevPDentry2;
                            firstfreeslot := firstfreeslot prevPDentry2;
                            nbfreeslots := newNbFreeSlots;
                            nbprepare := nbprepare prevPDentry2;
                            parent := parent prevPDentry2;
                            MPU := MPU prevPDentry2;
                            vidtAddr := vidtAddr prevPDentry2
                          |}
          /\ lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)
          /\ s4 = {|
                currentPartition := currentPartition s3;
                memory :=
                  add globalIdPD (PDT prevPDentry2) (memory s3) beqAddr
              |}
          /\ prevPDentry2 = {|
                            structure := structure prevPDentry;
                            firstfreeslot := newKStructurePointer;
                            nbfreeslots := nbfreeslots prevPDentry;
                            nbprepare := nbprepare prevPDentry;
                            parent := parent prevPDentry;
                            MPU := MPU prevPDentry;
                            vidtAddr := vidtAddr prevPDentry
                          |}
          /\ lookup globalIdPD (memory s4) beqAddr = Some (PDT prevPDentry2)
          /\ pdentryNbFreeSlots globalIdPD currentNbFreeSlots s4
          /\ s3 = {|
                currentPartition := currentPartition s2;
                memory :=
                  add lastBlockEntryAddr
                    (BE
                       (CBlockEntry (read bentryStart) (write bentryStart) (exec bentryStart) (present bentryStart)
                          (accessible bentryStart) (blockindex bentryStart)
                          (CBlock (startAddr (blockrange bentryStart)) currFirstFreeSlot)))
                    (memory s2) beqAddr
              |}
          /\ lookup globalIdPD (memory s3) beqAddr = Some (PDT prevPDentry)
          /\ s2 =
              {|
                currentPartition := currentPartition s1;
                memory := add globalIdPD (PDT prevPDentry) (memory s1) beqAddr
              |}
          /\ prevPDentry = {|
                            structure := newKStructurePointer;
                            firstfreeslot := firstfreeslot pdentry;
                            nbfreeslots := nbfreeslots pdentry;
                            nbprepare := nbprepare pdentry;
                            parent := parent pdentry;
                            MPU := MPU pdentry;
                            vidtAddr := vidtAddr pdentry
                          |}
          /\ lookup lastBlockEntryAddr (memory s2) beqAddr = Some (BE bentryStart)
          /\ lookup globalIdPD (memory s2) beqAddr = Some (PDT prevPDentry)
          /\ pdentryFirstFreeSlot globalIdPD currFirstFreeSlot s2
          /\ BlocksRangeFromKernelStartIsBE s2
          /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s2
          /\ lookup globalIdPD (memory s1) beqAddr = Some (PDT pdentry)
          /\ s1 =
               {|
                 currentPartition := currentPartition s0;
                 memory :=
                   add (CPaddr (newKStructurePointer + nextoffset)) (PADDR oldKStructurePointer) 
                     (memory s0) beqAddr
               |}
          /\ pdentryStructurePointer globalIdPD oldKStructurePointer s0
          /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
          /\ consistency1 s0 /\ noDupMappedPaddrList s0 /\ sharedBlockPointsToChild s0
          /\ adressesRangePreservedIfOriginAndNextOk s0 /\ childsBlocksPropsInParent s0
          /\ noChildImpliesAddressesNotShared s0 /\ kernelsAreNotAccessible s0
          /\ accessibleParentPaddrIsAccessibleIntoChild s0 /\ blockAndNextAreSideBySide s0
          /\ parentBlocksBoundsIfNoNext s0 /\ childLocMappedInChild s0 /\ childLocHasSameStart s0
          /\ pdentryNbPrepare globalIdPD nbPrepare s0
          /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s0
          /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s0
          /\ bentryPFlag requisitionedBlockInCurrPartAddr true s0
          /\ bentryAFlag requisitionedBlockInCurrPartAddr false s0
          /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)
          /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s0
          /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
                (CIndex (kernelStructureEntriesNb-1)) s0
          /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s0
          /\ currentPart = currentPartition s0
          /\ In currentPart (getPartitions multiplexer s0)
          /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s0))
          /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr)
          /\ (forall part kernList, isListOfKernels kernList part s0 -> ~ In requisitionedBlockStart kernList)
          /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0)
          /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
              -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s0)
          /\ (forall partition, isPDT partition s0
              -> Lib.disjoint
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
                (getFreeSlotsList partition s0))
          /\ wellFormedFreeSlotsList
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              <> False
          /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
          /\ (forall block, In block
               (filterOptionPaddr
                  (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)))
                -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                    /\ kernIdx < kernelStructureEntriesNb)
          /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
              -> block = CPaddr (requisitionedBlockStart+kernIdx)
              -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0
                  (CIndex kernelStructureEntriesNb))))
          /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
                (SomePaddr requisitionedBlockStart)
              = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
          /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s0
          /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
                -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1))
                    s0)
          /\ (forall addr, In addr (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0
                  (CIndex (kernelStructureEntriesNb-1))))
                -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
          /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s0
          /\ (forall part,
                Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
                (getAllPaddrConfigAux (getConfigBlocks part s0) s0))
        )
        /\ lastBlockEntryAddr = CPaddr (newKStructurePointer + blkoffset + lastidx)
        /\ i lastidx = kernelentriesnb - 1
        /\ beqAddr nullAddr globalIdPD = false
        /\ false = StateLib.Index.leb maxnbprepare nbPrepare
        /\ kernelentriesnb = CIndex kernelStructureEntriesNb
        /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
        /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
        /\ kStructureTotalLength = Constants.kernelStructureTotalLength
        /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
        /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
        /\ newKStructurePointer = requisitionedBlockStart
        /\ i maxnbprepare = maxNbPrepare
        /\ i newNbFreeSlots = currentNbFreeSlots + kernelentriesnb
        /\ newNbFreeSlots <= maxIdx).
  intuition; exists s; exists s3; exists s2; exists s1; exists s0; exists pdentry;
    exists {|
             structure := structure newPDentry;
             firstfreeslot := firstfreeslot newPDentry;
             nbfreeslots := newNbFreeSlots;
             nbprepare := nbprepare newPDentry;
             parent := parent newPDentry;
             MPU := MPU newPDentry;
             vidtAddr := vidtAddr newPDentry
           |}; exists newPDentry; exists prevPDentry; exists bentryStart; intuition; simpl; rewrite beqAddrTrue;
    reflexivity.
}
intro. eapply bindRev.
{ (** MAL.readPDNbPrepare **)
  eapply weaken. apply readPDNbPrepare. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as ([s4 [s3 [s2 [s1 [s0 [pdentry [newPDentry [prevPDentry2 [prevPDentry [bentryStart (Hs &
    _ & HlookupGlob & _)]]]]]]]]]] & _). unfold isPDT. rewrite HlookupGlob. trivial.
}
intro currentNbPrepare. eapply bindRev.
{ (** indexSuccM **)
  eapply weaken. apply WP.Index.succ. intros s Hprops. simpl.
  destruct Hprops as ((Hprops & HpropsBis) & HnbPrepare). split.
  - assert(HlebNbPrep: false = StateLib.Index.leb maxnbprepare nbPrepare) by intuition.
    assert(HmaxEq: i maxnbprepare = maxNbPrepare) by intuition.
    destruct Hprops as [s4 [s3 [s2 [s1 [s0 [pdentry [newPDentry [prevPDentry2 [prevPDentry [bentryStart
      Hprops]]]]]]]]]].
    assert(HnbPrepareBis: pdentryNbPrepare globalIdPD nbPrepare s0) by intuition. unfold pdentryNbPrepare in *.
    assert(HlookupGlobs1: lookup globalIdPD (memory s1) beqAddr = Some (PDT pdentry)) by intuition.
    assert(Hs1: s1 = {|
                       currentPartition := currentPartition s0;
                       memory :=
                         add (CPaddr (newKStructurePointer + nextoffset))
                            (PADDR oldKStructurePointer) (memory s0) beqAddr
                     |}) by intuition.
    rewrite Hs1 in HlookupGlobs1. simpl in HlookupGlobs1.
    destruct (beqAddr (CPaddr (newKStructurePointer+nextoffset)) globalIdPD) eqn:HbeqNexGlob;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in HlookupGlobs1; try(apply not_eq_sym; assumption). rewrite HlookupGlobs1 in *.
    assert(HlookupGlobs: lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)) by intuition.
    rewrite HlookupGlobs in *.
    assert(HnewPD: newPDentry = {|
                                  structure := structure prevPDentry2;
                                  firstfreeslot := firstfreeslot prevPDentry2;
                                  nbfreeslots := newNbFreeSlots;
                                  nbprepare := nbprepare prevPDentry2;
                                  parent := parent prevPDentry2;
                                  MPU := MPU prevPDentry2;
                                  vidtAddr := vidtAddr prevPDentry2
                                |}) by intuition.
    assert(HprevPD2: prevPDentry2 = {|
                                      structure := structure prevPDentry;
                                      firstfreeslot := newKStructurePointer;
                                      nbfreeslots := nbfreeslots prevPDentry;
                                      nbprepare := nbprepare prevPDentry;
                                      parent := parent prevPDentry;
                                      MPU := MPU prevPDentry;
                                      vidtAddr := vidtAddr prevPDentry
                                    |}) by intuition.
    assert(HprevPD: prevPDentry = {|
                                    structure := newKStructurePointer;
                                    firstfreeslot := firstfreeslot pdentry;
                                    nbfreeslots := nbfreeslots pdentry;
                                    nbprepare := nbprepare pdentry;
                                    parent := parent pdentry;
                                    MPU := MPU pdentry;
                                    vidtAddr := vidtAddr pdentry
                                  |}) by intuition.
    rewrite HnewPD in HnbPrepare. simpl in HnbPrepare. rewrite HprevPD2 in HnbPrepare. simpl in HnbPrepare.
    rewrite HprevPD in HnbPrepare. simpl in HnbPrepare. rewrite <-HnbPrepare in HnbPrepareBis. subst nbPrepare.
    unfold StateLib.Index.leb in *. apply eq_sym in HlebNbPrep. apply PeanoNat.Nat.leb_gt in HlebNbPrep.
    rewrite HmaxEq in HlebNbPrep. pose proof maxNbPrepareNbLessThanMaxIdx. lia.
  - instantiate(1 := fun newNbPrep s => pdentryNbPrepare globalIdPD currentNbPrepare s /\
      (
        exists s4 s3 s2 s1 s0 pdentry newPDentry prevPDentry2 prevPDentry bentryStart,
          s = {|
                currentPartition := currentPartition s4;
                memory :=
                  add globalIdPD (PDT newPDentry) (memory s4) beqAddr
              |}
          /\ newPDentry = {|
                            structure := structure prevPDentry2;
                            firstfreeslot := firstfreeslot prevPDentry2;
                            nbfreeslots := newNbFreeSlots;
                            nbprepare := nbprepare prevPDentry2;
                            parent := parent prevPDentry2;
                            MPU := MPU prevPDentry2;
                            vidtAddr := vidtAddr prevPDentry2
                          |}
          /\ lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)
          /\ s4 = {|
                currentPartition := currentPartition s3;
                memory :=
                  add globalIdPD (PDT prevPDentry2) (memory s3) beqAddr
              |}
          /\ prevPDentry2 = {|
                            structure := structure prevPDentry;
                            firstfreeslot := newKStructurePointer;
                            nbfreeslots := nbfreeslots prevPDentry;
                            nbprepare := nbprepare prevPDentry;
                            parent := parent prevPDentry;
                            MPU := MPU prevPDentry;
                            vidtAddr := vidtAddr prevPDentry
                          |}
          /\ lookup globalIdPD (memory s4) beqAddr = Some (PDT prevPDentry2)
          /\ pdentryNbFreeSlots globalIdPD currentNbFreeSlots s4
          /\ s3 = {|
                currentPartition := currentPartition s2;
                memory :=
                  add lastBlockEntryAddr
                    (BE
                       (CBlockEntry (read bentryStart) (write bentryStart) (exec bentryStart) (present bentryStart)
                          (accessible bentryStart) (blockindex bentryStart)
                          (CBlock (startAddr (blockrange bentryStart)) currFirstFreeSlot)))
                    (memory s2) beqAddr
              |}
          /\ lookup globalIdPD (memory s3) beqAddr = Some (PDT prevPDentry)
          /\ s2 =
              {|
                currentPartition := currentPartition s1;
                memory := add globalIdPD (PDT prevPDentry) (memory s1) beqAddr
              |}
          /\ prevPDentry = {|
                            structure := newKStructurePointer;
                            firstfreeslot := firstfreeslot pdentry;
                            nbfreeslots := nbfreeslots pdentry;
                            nbprepare := nbprepare pdentry;
                            parent := parent pdentry;
                            MPU := MPU pdentry;
                            vidtAddr := vidtAddr pdentry
                          |}
          /\ lookup lastBlockEntryAddr (memory s2) beqAddr = Some (BE bentryStart)
          /\ lookup globalIdPD (memory s2) beqAddr = Some (PDT prevPDentry)
          /\ pdentryFirstFreeSlot globalIdPD currFirstFreeSlot s2
          /\ BlocksRangeFromKernelStartIsBE s2
          /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s2
          /\ lookup globalIdPD (memory s1) beqAddr = Some (PDT pdentry)
          /\ s1 =
               {|
                 currentPartition := currentPartition s0;
                 memory :=
                   add (CPaddr (newKStructurePointer + nextoffset)) (PADDR oldKStructurePointer) 
                     (memory s0) beqAddr
               |}
          /\ pdentryStructurePointer globalIdPD oldKStructurePointer s0
          /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
          /\ consistency1 s0 /\ noDupMappedPaddrList s0 /\ sharedBlockPointsToChild s0
          /\ adressesRangePreservedIfOriginAndNextOk s0 /\ childsBlocksPropsInParent s0
          /\ noChildImpliesAddressesNotShared s0 /\ kernelsAreNotAccessible s0
          /\ accessibleParentPaddrIsAccessibleIntoChild s0 /\ blockAndNextAreSideBySide s0
          /\ parentBlocksBoundsIfNoNext s0 /\ childLocMappedInChild s0 /\ childLocHasSameStart s0
          /\ pdentryNbPrepare globalIdPD nbPrepare s0
          /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s0
          /\ bentryEndAddr requisitionedBlockInCurrPartAddr requisitionedBlockEnd s0
          /\ bentryPFlag requisitionedBlockInCurrPartAddr true s0
          /\ bentryAFlag requisitionedBlockInCurrPartAddr false s0
          /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s0)
          /\ bentryBlockIndex requisitionedBlockStart (CIndex 0) s0
          /\ bentryBlockIndex (CPaddr (requisitionedBlockStart + kernelStructureEntriesNb-1))
                (CIndex (kernelStructureEntriesNb-1)) s0
          /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s0
          /\ currentPart = currentPartition s0
          /\ In currentPart (getPartitions multiplexer s0)
          /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s0))
          /\ lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s0) beqAddr = Some (PADDR nullAddr)
          /\ (forall part kernList, isListOfKernels kernList part s0 -> ~ In requisitionedBlockStart kernList)
          /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
                -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s0)
          /\ (forall kernIdx: index, kernIdx < kernelStructureEntriesNb
              -> isFreeSlot (CPaddr (requisitionedBlockStart+kernIdx)) s0)
          /\ (forall partition, isPDT partition s0
              -> Lib.disjoint
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
                (getFreeSlotsList partition s0))
          /\ wellFormedFreeSlotsList
                (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
              <> False
          /\ NoDup (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
          /\ (forall block, In block
               (filterOptionPaddr
                  (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb)))
                -> exists kernIdx, block = CPaddr (requisitionedBlockStart + kernIdx)
                    /\ kernIdx < kernelStructureEntriesNb)
          /\ (forall kernIdx block, kernIdx < kernelStructureEntriesNb
              -> block = CPaddr (requisitionedBlockStart+kernIdx)
              -> In block (filterOptionPaddr (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0
                  (CIndex kernelStructureEntriesNb))))
          /\ last (getFreeSlotsListRec (maxIdx+1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
                (SomePaddr requisitionedBlockStart)
              = SomePaddr (CPaddr (requisitionedBlockStart+ kernelStructureEntriesNb-1))
          /\ bentryEndAddr (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) nullAddr s0
          /\ (forall blkIdx:index, blkIdx < kernelStructureEntriesNb-1
                -> bentryEndAddr (CPaddr (requisitionedBlockStart+blkIdx)) (CPaddr (requisitionedBlockStart+blkIdx+1))
                    s0)
          /\ (forall addr, In addr (filterOptionPaddr (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0
                  (CIndex (kernelStructureEntriesNb-1))))
                -> forall part, isPDT part s0 -> ~In addr (filterOptionPaddr (getKSEntries part s0)))
          /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) false s0
          /\ (forall part,
                Lib.disjoint (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
                (getAllPaddrConfigAux (getConfigBlocks part s0) s0))
        )
        /\ lastBlockEntryAddr = CPaddr (newKStructurePointer + blkoffset + lastidx)
        /\ i lastidx = kernelentriesnb - 1
        /\ beqAddr nullAddr globalIdPD = false
        /\ false = StateLib.Index.leb maxnbprepare nbPrepare
        /\ kernelentriesnb = CIndex kernelStructureEntriesNb
        /\ requisitionedBlockInCurrPartAddr = idRequisitionedBlock
        /\ beqAddr nullAddr requisitionedBlockInCurrPartAddr = false
        /\ kStructureTotalLength = Constants.kernelStructureTotalLength
        /\ false = StateLib.Index.ltb blockSize kStructureTotalLength
        /\ i blockSize = requisitionedBlockEnd - requisitionedBlockStart
        /\ newKStructurePointer = requisitionedBlockStart
        /\ i maxnbprepare = maxNbPrepare
        /\ i newNbFreeSlots = currentNbFreeSlots + kernelentriesnb
        /\ i newNbPrep = currentNbPrepare + 1
        /\ newNbFreeSlots <= maxIdx). intuition.
}
intro succCurrentNbPrepare. eapply bindRev.
{ (** MAL.writePDNbPrepare **)
  eapply weaken. apply writePDNbPrepare. intros s Hprops. simpl. split. apply Hprops. destruct Hprops as (Hres & _).
  unfold isPDT. unfold pdentryNbPrepare in *. destruct (lookup globalIdPD (memory s) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
intro. eapply bindRev.
{ (** ret **)
  eapply weaken. apply WP.ret. intros s Hprops.
  destruct Hprops as [s5 [prevPDentry3Bis [newPDentry ((HnbPrep & [s4 [s3 [s2 [s1 [s0 [pdentry [prevPDentry3
    [prevPDentry2 [prevPDentry [bentryStart (Hs5 & Hprev3 & HlookupGlobs5 & Hprops)]]]]]]]]]] & HpropsBis) & Hs &
    HnewPD & HlookupGlobs5Bis)]]]. rewrite HlookupGlobs5 in HlookupGlobs5Bis.
  injection HlookupGlobs5Bis as HlookupGlobs5Bis. subst prevPDentry3Bis.
  destruct Hprops as (Hs4 & Hprev2 & HlookupGlobs4 & HnbFrees4 & Hs3 & HlookupGlobs3 & Hs2 & Hprev & HlookupLasts2 &
    HlookupGlobs2 & HfirstFrees2 & HblockRanges2 & HPDchild & HlookupGlobs1 & Hs1 & Hstructs0 & HPIs0 & HKDIs0 & HVSs0
    & Hconsists0 & HnoDupUseds0 & Hshareds0 & Hranges0 & HchildBlockPropss0 & HnoChilds0 & HkernNotAccs0 & Haccesss0 &
    HnextBlockSides0 & HparentBoundss0 & HlocPropss0 & HsameStarts0 & HnbPreps0 & HstartBlocks0 & HendBlocks0 &
    HPflagBlocks0 & HAflagBlocks0 & HblockMappedCurrs0 & Hblkidxs0 &
    HlastIdxs0 & HPDchilds0 & Hcurrs0 & HcurrIsParts0 & Hglob & HlookupNext & HstartNotKerns0 & HPflagNew & HnewFree
    & HdisjointNew & HwellFormedNew & HnoDupNew & HnewAreStartsBlocks & HstartsBlocksAreNew & HlastNew & HendLast &
    HendNew & HnewStructAreNotEntries & HPDflag & HnewNotConf).
  assert(HnewBs3: exists l1 l2, CBlockEntry (read bentryStart) (write bentryStart) (exec bentryStart)
      (present bentryStart) (accessible bentryStart) (blockindex bentryStart)
      (CBlock (startAddr (blockrange bentryStart)) currFirstFreeSlot)
    = {|
        read := read bentryStart;
        write := write bentryStart;
        exec := exec bentryStart;
        present := present bentryStart;
        accessible := accessible bentryStart;
        blockindex := blockindex bentryStart;
        blockrange := {|
                        startAddr := startAddr (blockrange bentryStart);
                        endAddr := currFirstFreeSlot;
                        Hsize := l2
                      |};
        Hidx := l1
      |}).
  {
    unfold CBlockEntry. assert(blockindex bentryStart < kernelStructureEntriesNb) by (apply Hidx).
    destruct (lt_dec (blockindex bentryStart) kernelStructureEntriesNb); try(lia). unfold CBlock.
    exists (ADT.CBlockEntry_obligation_1 (blockindex bentryStart) l).
    assert(currFirstFreeSlot <= maxIdx) by (rewrite maxIdxEqualMaxAddr; apply Hp).
    destruct (le_dec (currFirstFreeSlot - startAddr (blockrange bentryStart)) maxIdx); try(lia).
    exists (ADT.CBlock_obligation_1 (startAddr (blockrange bentryStart)) currFirstFreeSlot l0). f_equal.
  }
  destruct HnewBs3 as [l1 [l2 HnewBs3]].
  assert(HmultIsPDTs1: multiplexerIsPDT s1).
  {
    assert(Hcons0: isPDT multiplexer s0) by (unfold consistency1 in *; intuition).
    assert(newKStructurePointer = requisitionedBlockStart) by intuition. subst newKStructurePointer.
    unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) multiplexer) eqn:HbeqNextMult.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextMult. rewrite HbeqNextMult in *. rewrite HlookupNext in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HmultIsPDTs2: isPDT multiplexer s2).
  {
    assert(newKStructurePointer = requisitionedBlockStart) by intuition. subst newKStructurePointer.
    unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs2. simpl.
    destruct (beqAddr globalIdPD multiplexer) eqn:HbeqGlobMult; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupGlobs0: lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry)).
  {
    rewrite Hs1 in HlookupGlobs1. simpl in *.
    destruct (beqAddr (CPaddr (newKStructurePointer + nextoffset)) globalIdPD) eqn:HbeqNextGlob;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HstartIsKSs0: isKS requisitionedBlockStart s0).
  {
    unfold isKS. unfold bentryBlockIndex in *.
    destruct (lookup requisitionedBlockStart (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    auto.
  }
  assert(requisitionedBlockStart + nextoffset <= maxAddr).
  {
    assert(Hres: nextKernelIsValid s0) by (unfold consistency1 in *; intuition).
    apply Hres; assumption.
  }
  assert(HgetPartsEqs1: getPartitions multiplexer s1 = getPartitions multiplexer s0).
  {
    assert(newKStructurePointer = requisitionedBlockStart) by intuition. subst newKStructurePointer.
    rewrite Hs1. apply getPartitionsEqPADDR; trivial. 1-8: unfold consistency1 in *; intuition.
    unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }
  assert(newKStructurePointer = requisitionedBlockStart) by intuition. subst newKStructurePointer.
  assert(HgetMappedBEqs1: forall part, isPDT part s0 -> getMappedBlocks part s1 = getMappedBlocks part s0).
  {
    intros part HpartIsPDT. unfold isPDT in *.
    destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    rewrite Hs1. apply getMappedBlocksEqPADDR with p; trivial. 1-3: unfold consistency1 in *; intuition.
    exists (completeListOfKernels (structure p) s0). split; try(split).
    - apply completeKernList; trivial; unfold consistency1 in *; intuition.
    - apply HstartNotKerns0 with part.
      apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
    - assert(Hres: noDupListOfKerns s0) by (unfold consistency1 in *; intuition). unfold noDupListOfKerns in *.
      apply Hres with part. apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
  }
  assert(HPDTIfPDFlags1: PDTIfPDFlag s1).
  {
    assert(Hcons0: PDTIfPDFlag s0) by (unfold consistency1 in *; intuition).
    intros idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild. rewrite HgetPartsEqs1 in *.
    assert(isPDT part s0).
    { apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
    rewrite HgetMappedBEqs1 in *; trivial. unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag.
    unfold bentryPFlag. unfold bentryStartAddr. unfold entryPDT.
    assert(HlookupBlockEq: lookup idPDchild (memory s1) beqAddr = lookup idPDchild (memory s0) beqAddr).
    {
      destruct HcheckChild as (_ & Hsh1). rewrite Hs1. rewrite Hs1 in Hsh1. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) idPDchild) eqn:HbeqNextBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    rewrite HlookupBlockEq in *.
    assert(HlookupSh1Eq: lookup sh1entryaddr (memory s1) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
    {
      destruct HcheckChild as (HcheckChild & _).
      destruct (lookup idPDchild (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      rewrite Hs1. rewrite Hs1 in HcheckChild. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) sh1entryaddr) eqn:HbeqNextSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    rewrite HlookupSh1Eq in *. specialize(Hcons0 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild).
    destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
    exists startaddr. split; trivial. unfold entryPDT in *.
    destruct (lookup idPDchild (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) (startAddr (blockrange b))) eqn:HbeqNextStart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextStart. rewrite HbeqNextStart in *. rewrite HlookupNext in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(Hnulls1: isPADDR nullAddr s1).
  {
    assert(Hcons0: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *. rewrite Hs1.
    simpl. destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) nullAddr) eqn:HbeqNextNull; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(Hstructs1: StructurePointerIsKS s1).
  {
    assert(Hcons0: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart HbeqStructNull. rewrite Hs1 in HlookupPart. simpl in *.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentryPart HlookupPart HbeqStructNull). unfold isKS in *. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) (structure pdentryPart)) eqn:HbeqNextStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextStruct. rewrite HbeqNextStruct in *. rewrite HlookupNext in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HnextValids1: nextKernelIsValid s1).
  {
    assert(Hcons0: nextKernelIsValid s0) by (unfold consistency1 in *; intuition). intros kernel HkernIsKS.
    unfold isKS in *. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS.
    destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) kernel) eqn:HbeqNextKern;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 kernel HkernIsKS). destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNextNext & Hnext)]).
    split; trivial. rewrite Hs1. simpl. destruct (beqAddr requisitionedBlockStart kernel) eqn:HbeqKerns.
    - rewrite <-DTL.beqAddrTrue in HbeqKerns. subst kernel. exists oldKStructurePointer. split.
      + intro Hp. assert(HbeqNexts: beqAddr (CPaddr (requisitionedBlockStart + nextoffset))
          {| p := requisitionedBlockStart + nextoffset; Hp := Hp |} = true).
        {
          rewrite <-DTL.beqAddrTrue. unfold CPaddr.
          destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia). f_equal.
          apply proof_irrelevance.
        }
        rewrite HbeqNexts. reflexivity.
      + unfold CPaddr in HlookupNext.
        destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr) eqn:HleNext; try(lia).
        specialize(HlookupNextNext (ADT.CPaddr_obligation_1 (requisitionedBlockStart + nextoffset) l)).
        rewrite HlookupNext in HlookupNextNext. injection HlookupNextNext as HlookupNextNext.
        assert(HstructIsKSs0: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
        unfold pdentryStructurePointer in *. rewrite HlookupGlobs0 in *.
        destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
        * rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite Hstructs0 in *. right. assumption.
        * rewrite <-beqAddrFalse in *. specialize(HstructIsKSs0 globalIdPD pdentry HlookupGlobs0 HbeqStructNull).
          rewrite <-Hstructs0 in *. unfold isKS in *. left.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) oldKStructurePointer)
            eqn:HbeqNextAncStruct.
          {
            rewrite <-DTL.beqAddrTrue in HbeqNextAncStruct. rewrite HbeqNextAncStruct in *.
            unfold CPaddr in HbeqNextAncStruct. rewrite HleNext in HbeqNextAncStruct.
            rewrite HbeqNextAncStruct in *. rewrite HlookupNext in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - rewrite <-beqAddrFalse in *. exists nextAddr. split.
      + intro Hp. specialize(HlookupNextNext Hp).
        assert(HbeqNexts: beqAddr (CPaddr (requisitionedBlockStart+nextoffset))
          {| p := kernel+nextoffset; Hp := Hp |} = false).
        {
          rewrite <-beqAddrFalse. unfold CPaddr.
          assert(HnextValid: nextKernelIsValid s0) by (unfold consistency1 in *; intuition).
          specialize(HnextValid requisitionedBlockStart HstartIsKSs0). destruct HnextValid as (HlebBlockNextMax & _).
          destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia).
          apply paddrNeqNatNeqEquiv. simpl. intro Hcontra. apply PeanoNat.Nat.add_cancel_r in Hcontra.
          apply paddrEqNatEqEquiv in Hcontra. congruence.
        }
        rewrite HbeqNexts. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      + destruct Hnext as [HnextIsKS | HnextIsNull]; try(right; assumption). left. unfold isKS in *.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) nextAddr) eqn:HbeqNexts.
        {
          rewrite <-DTL.beqAddrTrue in HbeqNexts. rewrite HbeqNexts in *. rewrite HlookupNext in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HkernLists1s0: forall part kernList, isListOfKernels kernList part s1
    -> isListOfKernels kernList part s0).
  {
    intros part kernList. rewrite Hs1. apply isListOfKernelsEqPADDR.
    - assert(HnextValids0: nextKernelIsValid s0) by (unfold consistency1 in *; intuition).
      specialize(HnextValids0 requisitionedBlockStart HstartIsKSs0). apply HnextValids0.
    - apply HstartNotKerns0.
  }
  assert(HmaxNbPreps1: maxNbPrepareIsMaxNbKernels s1).
  {
    assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by (unfold consistency1 in *; intuition).
    intros partition kernList HlistOfKerns. apply HkernLists1s0 in HlistOfKerns.
    specialize(Hcons0 partition kernList HlistOfKerns). assumption.
  }
  assert(noDupPartitionTree s1).
  { unfold noDupPartitionTree. rewrite HgetPartsEqs1. unfold consistency in *; unfold consistency1 in *; intuition. }
  assert(HnotFulls0: length (completeListOfKernels (structure pdentry) s0) < maxNbPrepare).
  {
    destruct HpropsBis as (_ & _ & _ & HlebMaxNbPrep & _ & _ & _ & _ & _ & _ & _ & Hmax & _).
    unfold StateLib.Index.leb in *. apply eq_sym in HlebMaxNbPrep. apply PeanoNat.Nat.leb_gt in HlebMaxNbPrep.
    assert(HnbPrepIsKerns: nbPrepareIsNbKern s0) by (unfold consistency1 in *; intuition).
    specialize(HnbPrepIsKerns globalIdPD pdentry HlookupGlobs0). rewrite HnbPrepIsKerns. rewrite Hmax in *.
    unfold pdentryNbPrepare in *. rewrite HlookupGlobs0 in *. rewrite HnbPreps0 in *. assumption.
  }
  assert(HPflagNews1: forall kernIdx: index, kernIdx < kernelStructureEntriesNb
    -> bentryPFlag (CPaddr (requisitionedBlockStart + kernIdx)) false s1).
  {
    intros kernIdx HltIdxKernEntries. specialize(HPflagNew kernIdx HltIdxKernEntries). unfold bentryPFlag in *.
    rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) (CPaddr (requisitionedBlockStart + kernIdx)))
      eqn:HbeqNextIdx.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextIdx. rewrite HbeqNextIdx in *. rewrite HlookupNext in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HgetPartsEqs2: getPartitions multiplexer s2 = getPartitions multiplexer s1).
  {
    rewrite Hs2. apply getPartitionsEqPDTNewEmptyStruct with pdentry requisitionedBlockStart; trivial.
    - rewrite Hprev. reflexivity.
    - unfold isKS. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) requisitionedBlockStart) eqn:HbeqNextStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextStart. rewrite HbeqNextStart in *. unfold isKS in *.
        rewrite HlookupNext in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - rewrite Hs1. simpl. rewrite beqAddrTrue. f_equal. f_equal. unfold pdentryStructurePointer in *.
      rewrite HlookupGlobs0 in *. assumption.
    - assert(Heq: completeListOfKernels (structure pdentry) s1 = completeListOfKernels (structure pdentry) s0).
      {
        destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
        - rewrite <-DTL.beqAddrTrue in HbeqStructNull. unfold completeListOfKernels. rewrite HbeqStructNull.
          assert(Hnulls0: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
          destruct (lookup nullAddr (memory s1) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). reflexivity.
        - rewrite <-beqAddrFalse in *. rewrite Hs1. apply completeListOfKernelsEqPADDRNew; trivial.
          + unfold consistency1 in *; intuition.
          + assert(HstructIsKSs0: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
            unfold pdentryStructurePointer in *. rewrite HlookupGlobs0 in *.
            specialize(HstructIsKSs0 globalIdPD pdentry HlookupGlobs0 HbeqStructNull). assumption.
          + unfold isPADDR. rewrite HlookupNext. trivial.
          + apply HstartNotKerns0 with globalIdPD.
            apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
      }
      rewrite Heq. assumption.
    - intros block HblockInRange. assert(HblockIdx: exists kernIdx:index, kernIdx < kernelStructureEntriesNb
        /\ block = CPaddr (requisitionedBlockStart + kernIdx)).
      { apply getKSEntriesInStructAuxToIndex with s1. assumption. }
      destruct HblockIdx as [kernIdx (HltIdxKernEntries & Hblock)]. subst block. apply HPflagNews1. assumption.
    - unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }
  pose proof KSEntriesNbLessThanMaxIdx.
  assert(HidxEq: kernelStructureEntriesNb - 1 = CIndex (kernelStructureEntriesNb - 1)).
  { unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). reflexivity. }
  assert(HgetMappedBEqs2s1: forall part, getMappedBlocks part s2 = getMappedBlocks part s1).
  {
    intro part. rewrite Hs2. apply getMappedBlocksEqPDTNewEmptyStruct with pdentry requisitionedBlockStart; trivial.
    - rewrite Hprev. reflexivity.
    - unfold isKS in *. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) requisitionedBlockStart) eqn:HbeqNextStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextStart. rewrite HbeqNextStart in *. rewrite HlookupNext in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - rewrite Hs1. simpl. rewrite beqAddrTrue. unfold pdentryStructurePointer in *. rewrite HlookupGlobs0 in *.
      rewrite Hstructs0. reflexivity.
    - assert(HcompleteEq: completeListOfKernels (structure pdentry) s1
        = completeListOfKernels (structure pdentry) s0).
      {
        rewrite Hs1. destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
        - rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. unfold completeListOfKernels.
          assert(Hnulls0: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition).
          unfold nullAddrExists in *. unfold isPADDR in *. rewrite <-Hs1.
          destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          destruct (lookup nullAddr (memory s1) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). reflexivity.
        - rewrite <-beqAddrFalse in *.
          assert(HstructIsKS: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
          specialize(HstructIsKS globalIdPD pdentry HlookupGlobs0 HbeqStructNull).
          apply completeListOfKernelsEqPADDRNew; trivial.
          + unfold consistency1 in *; intuition.
          + unfold isPADDR. rewrite HlookupNext. trivial.
          + apply HstartNotKerns0 with globalIdPD.
            apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
      }
      rewrite HcompleteEq. assumption.
    - intros addr HaddrIn. apply getKSEntriesInStructAuxToIndexAux in HaddrIn; try(rewrite <-HidxEq; lia).
      destruct HaddrIn as [kernIdx (HltIdxKernEntries & Haddr)]. subst addr. rewrite <-HidxEq in *.
      apply HPflagNews1; lia.
  }
  assert(HPDTIfPDFlags2: PDTIfPDFlag s2).
  {
    intros idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild. rewrite HgetPartsEqs2 in *.
    rewrite HgetMappedBEqs2s1 in *. unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag.
    unfold bentryPFlag. unfold bentryStartAddr. unfold entryPDT.
    assert(HlookupBlockEq: lookup idPDchild (memory s2) beqAddr = lookup idPDchild (memory s1) beqAddr).
    {
      destruct HcheckChild as (_ & Hsh1). rewrite Hs2. rewrite Hs2 in Hsh1. simpl in *.
      destruct (beqAddr globalIdPD idPDchild) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    rewrite HlookupBlockEq in *.
    assert(HlookupSh1Eq: lookup sh1entryaddr (memory s2) beqAddr = lookup sh1entryaddr (memory s1) beqAddr).
    {
      destruct HcheckChild as (HcheckChild & _).
      destruct (lookup idPDchild (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      rewrite Hs2. rewrite Hs2 in HcheckChild. simpl in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    rewrite HlookupSh1Eq in *.
    specialize(HPDTIfPDFlags1 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild).
    destruct HPDTIfPDFlags1 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial. split; trivial.
    exists startaddr. split; trivial. unfold entryPDT in *.
    destruct (lookup idPDchild (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    rewrite Hs2. simpl. destruct (beqAddr globalIdPD (startAddr (blockrange b))) eqn:HbeqGlobStart.
    - rewrite <-DTL.beqAddrTrue in HbeqGlobStart. subst globalIdPD. rewrite HlookupGlobs1 in *. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HwellFormedSh1s2: wellFormedFstShadowIfBlockEntry s2).
  {
    assert(Hcons0: wellFormedFstShadowIfBlockEntry s0) by (unfold consistency1 in *; intuition).
    intros block HblockIsBE. assert(HblockIsBEs0: isBE block s0).
    {
      unfold isBE in *. rewrite Hs2 in HblockIsBE. simpl in *.
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 block HblockIsBEs0). unfold isSHE in *. rewrite Hs2. simpl.
    destruct (beqAddr globalIdPD (CPaddr (block + sh1offset))) eqn:HbeqGlobNext.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobNext. subst globalIdPD. rewrite HlookupGlobs0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) (CPaddr (block + sh1offset))) eqn:HbeqNextSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextSh1. rewrite HbeqNextSh1 in *. rewrite HlookupNext in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupStartEqs3: lookup requisitionedBlockStart (memory s3) beqAddr
    = lookup requisitionedBlockStart (memory s0) beqAddr).
  {
    unfold isKS in *. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr requisitionedBlockStart) eqn:HbeqLastStart.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqLastStart. subst lastBlockEntryAddr.
      destruct HpropsBis as (Hlast & Hlastidx & _ & _ & HentriesNb & _). rewrite Hlastidx in Hlast.
      subst kernelentriesnb. unfold CIndex in Hlast. pose proof maxIdxBiggerThanNbOfKernels.
      destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). unfold blkoffset in Hlast.
      rewrite PeanoNat.Nat.add_0_r in Hlast. cbn -[kernelStructureEntriesNb] in Hlast.
      assert(HblockRanges0: BlocksRangeFromKernelStartIsBE s0) by (unfold consistency1 in *; intuition).
      assert(HltIdx: CIndex (kernelStructureEntriesNb - 1) < kernelStructureEntriesNb).
      {
        unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia). cbn. lia.
      }
      specialize(HblockRanges0 requisitionedBlockStart (CIndex (kernelStructureEntriesNb - 1)) HstartIsKSs0 HltIdx).
      unfold CIndex in HblockRanges0. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
      cbn -[kernelStructureEntriesNb] in HblockRanges0. unfold isBE. unfold CPaddr in HblockRanges0.
      unfold CPaddr in Hlast. destruct (le_dec (requisitionedBlockStart + (kernelStructureEntriesNb - 1)) maxAddr).
      - destruct requisitionedBlockStart. simpl in Hlast. injection Hlast as Hlast. lia.
      - assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition).
        assert(HnullEq:
          {|
            p := 0; Hp := ADT.CPaddr_obligation_2 (requisitionedBlockStart + (kernelStructureEntriesNb - 1)) n
          |} = nullAddr).
        { unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance. }
        rewrite HnullEq in *. unfold isPADDR in *. unfold isBE in *.
        destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    destruct (beqAddr globalIdPD requisitionedBlockStart) eqn:HbeqGlobStart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobStart. rewrite HbeqGlobStart in *. rewrite HlookupGlobs0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) requisitionedBlockStart) eqn:HbeqNextStart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextStart. rewrite HbeqNextStart in *. rewrite HlookupNext in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupStartEqs: lookup requisitionedBlockStart (memory s) beqAddr
    = lookup requisitionedBlockStart (memory s0) beqAddr).
  {
    unfold isKS in *. rewrite <-HlookupStartEqs3. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
    destruct (beqAddr globalIdPD requisitionedBlockStart) eqn:HbeqGlobStart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobStart. rewrite HbeqGlobStart in *. rewrite HlookupGlobs0 in *.
      exfalso; congruence.
    }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlookupLasts1: lookup lastBlockEntryAddr (memory s1) beqAddr = Some (BE bentryStart)).
  {
    rewrite Hs2 in HlookupLasts2. simpl in *.
    destruct (beqAddr globalIdPD lastBlockEntryAddr) eqn:HbeqGlobLast; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HlookupLasts0: lookup lastBlockEntryAddr (memory s0) beqAddr = Some (BE bentryStart)).
  {
    rewrite Hs1 in HlookupLasts1. simpl in *.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) lastBlockEntryAddr) eqn:HbeqNextLast;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(Hstructs3: StructurePointerIsKS s3).
  {
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts1: exists pdentryParts1, lookup partition (memory s1) beqAddr = Some (PDT pdentryParts1)
      /\ (structure pdentryParts1 = structure pdentryPart \/ isKS (structure pdentryPart) s3)).
    {
      rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupPart. simpl in *. destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. injection HlookupPart as HlookupPart.
        subst pdentryPart. exists pdentry. rewrite Hprev. split; trivial. right. simpl. unfold isKS in *.
        rewrite <-HlookupStartEqs3 in HstartIsKSs0. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        exists pdentryPart. split; trivial. left. reflexivity.
    }
    destruct HlookupParts1 as [pdentryParts1 (HlookupParts1 & HpropsOr)].
    destruct HpropsOr as [HstructEq | Hres]; trivial. rewrite <-HstructEq in *.
    specialize(Hstructs1 partition pdentryParts1 HlookupParts1 HbeqStructNull). rewrite HstructEq in *.
    unfold isKS in *. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr (structure pdentryPart)) eqn:HbeqLastStruct.
    {
      pose proof maxIdxBiggerThanNbOfKernels.
      assert(Hlast: lastBlockEntryAddr = CPaddr (requisitionedBlockStart + kernelStructureEntriesNb - 1)).
      {
        destruct HpropsBis as (Hlast & HlastIdx & _ & _ & HentriesNb & _). subst kernelentriesnb.
        unfold CIndex in HlastIdx. cbn.
        destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl in HlastIdx. rewrite HlastIdx in *.
        unfold blkoffset in *. unfold CIndex in Hlast. destruct (le_dec 0 maxIdx); try(lia). simpl in Hlast.
        rewrite PeanoNat.Nat.add_0_r in Hlast.
        replace (requisitionedBlockStart + 8 - 1) with (requisitionedBlockStart + 7); try(lia). assumption.
      }
      rewrite <-Hlast in *. rewrite <-DTL.beqAddrTrue in HbeqLastStruct. rewrite <-HbeqLastStruct in *.
      unfold bentryBlockIndex in *. rewrite HlookupLasts0 in *. rewrite HlookupLasts1 in *.
      rewrite Hstructs1 in HlastIdxs0. unfold zero in HlastIdxs0. unfold CIndex in HlastIdxs0.
      destruct (le_dec 0 maxIdx); try(lia). destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
      injection HlastIdxs0 as HlastIdxs0. lia.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    destruct (beqAddr globalIdPD (structure pdentryPart)) eqn:HbeqGlobStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobStruct. rewrite HbeqGlobStruct in *. rewrite HlookupGlobs1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }
  assert(HlastSh1IsSHE: isSHE (CPaddr (lastBlockEntryAddr + sh1offset)) s2).
  {
    assert(HlastIsBEs2: isBE lastBlockEntryAddr s2) by (unfold isBE; rewrite HlookupLasts2; trivial).
    specialize(HwellFormedSh1s2 lastBlockEntryAddr HlastIsBEs2). assumption.
  }
  assert(HgetPartsEqs3: getPartitions multiplexer s3 = getPartitions multiplexer s2).
  {
    rewrite Hs3. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
      with bentryStart (CPaddr (lastBlockEntryAddr+sh1offset)); try(rewrite HnewBs3); trivial.
    - unfold sh1entryAddr; rewrite HlookupLasts2; reflexivity.
    - simpl. destruct (beqAddr lastBlockEntryAddr (CPaddr (lastBlockEntryAddr + sh1offset))) eqn:HbeqLastLastSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastLastSh1. rewrite <-HbeqLastLastSh1 in *. unfold isSHE in *.
        rewrite HlookupLasts2 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - unfold noDupPartitionTree. rewrite HgetPartsEqs2. assumption.
    - unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }
  assert(HgetMappedBEqs3s2: forall part, getMappedBlocks part s3 = getMappedBlocks part s2).
  {
    intro part. rewrite Hs3. apply getMappedBlocksEqBENoChange with bentryStart; trivial.
    rewrite HnewBs3. reflexivity.
  }
  assert(HPDTIfPDFlags3: PDTIfPDFlag s3).
  {
    intros idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild. rewrite HgetPartsEqs3 in *.
    rewrite HgetMappedBEqs3s2 in *.
    assert(HlookupBlocks3: exists bentryBlock, lookup idPDchild (memory s3) beqAddr = Some(BE bentryBlock)).
    {
      destruct HcheckChild as (_ & Hres). unfold sh1entryAddr in *.
      destruct (lookup idPDchild (memory s3) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      exists b. reflexivity.
    }
    destruct HlookupBlocks3 as [bentryBlock HlookupBlocks3]. unfold bentryAFlag. unfold bentryPFlag. unfold entryPDT.
    assert(HlookupBlocks2: exists bentryBlocks2, lookup idPDchild (memory s2) beqAddr = Some(BE bentryBlocks2)
      /\ present bentryBlocks2 = present bentryBlock /\ accessible bentryBlocks2 = accessible bentryBlock
      /\ startAddr (blockrange bentryBlocks2) = startAddr (blockrange bentryBlock)).
    {
      rewrite Hs3 in HlookupBlocks3. simpl in *. destruct (beqAddr lastBlockEntryAddr idPDchild) eqn:HbeqLastBlock.
      - exists bentryStart. rewrite <-DTL.beqAddrTrue in HbeqLastBlock. rewrite HbeqLastBlock in *. split; trivial.
        rewrite HnewBs3 in HlookupBlocks3. simpl in HlookupBlocks3. injection HlookupBlocks3 as HlookupBlocks3.
        rewrite <-HlookupBlocks3. split; trivial. split; trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupBlocks3; try(apply not_eq_sym); trivial.
        exists bentryBlock. split; trivial. split; trivial. split; trivial.
    }
    destruct HlookupBlocks2 as [bentryBlocks2 (HlookupBlocks2 & HpresEq & HaccessEq & HstartEq)].
    unfold bentryStartAddr. rewrite HlookupBlocks3. rewrite <-HpresEq. rewrite <-HaccessEq. rewrite <-HstartEq.
    assert(HcheckChilds2: true = checkChild idPDchild s2 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s2).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. rewrite HlookupBlocks2. rewrite HlookupBlocks3 in *.
      destruct HcheckChild as (HcheckChild & Hsh1). split; trivial. rewrite Hs3 in HcheckChild. simpl in *.
      destruct (beqAddr lastBlockEntryAddr sh1entryaddr) eqn:HbeqLastSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(HPDTIfPDFlags2 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChilds2).
    unfold bentryAFlag in *. unfold bentryPFlag in *.
    destruct HPDTIfPDFlags2 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). unfold bentryStartAddr in *.
    unfold entryPDT in *. rewrite HlookupBlocks2 in *. split; trivial. split; trivial. exists startaddr.
    split; trivial. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr (startAddr (blockrange bentryBlocks2))) eqn:HbeqLastStart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastStart. rewrite HbeqLastStart in *. rewrite HlookupLasts2 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(Hstructs4: StructurePointerIsKS s4).
  {
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts3: exists pdentryParts3, lookup partition (memory s3) beqAddr = Some (PDT pdentryParts3)
      /\ structure pdentryParts3 = structure pdentryPart).
    {
      rewrite Hs4 in HlookupPart. simpl in *. destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. exists prevPDentry.
        injection HlookupPart as HlookupPart. subst pdentryPart. rewrite Hprev2. split; trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        exists pdentryPart. split; trivial.
    }
    destruct HlookupParts3 as [pdentryParts3 (HlookupParts3 & HstructEq)]. rewrite <-HstructEq in *.
    specialize(Hstructs3 partition pdentryParts3 HlookupParts3 HbeqStructNull). unfold isKS in *. rewrite Hs4. simpl.
    destruct (beqAddr globalIdPD (structure pdentryParts3)) eqn:HbeqGlobStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobStruct. rewrite HbeqGlobStruct in *. rewrite HlookupGlobs3 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HgetPartsEqs4: getPartitions multiplexer s4 = getPartitions multiplexer s3).
  {
    rewrite Hs4. apply getPartitionsEqPDT with prevPDentry; try(rewrite Hprev2); trivial.
    - unfold noDupPartitionTree. rewrite HgetPartsEqs3. rewrite HgetPartsEqs2. assumption.
    - unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }
  assert(HgetMappedBEqs4s3: forall part, getMappedBlocks part s4 = getMappedBlocks part s3).
  {
    intro part. rewrite Hs4. apply getMappedBlocksEqPDT with prevPDentry; trivial. rewrite Hprev2.
    reflexivity.
  }
  assert(HPDTIfPDFlags4: PDTIfPDFlag s4).
  {
    intros idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild. rewrite HgetPartsEqs4 in *.
    rewrite HgetMappedBEqs4s3 in *.
    assert(HlookupBlockEq: lookup idPDchild (memory s4) beqAddr = lookup idPDchild (memory s3) beqAddr).
    {
      destruct HcheckChild as (_ & Hsh1). unfold sh1entryAddr in *. rewrite Hs4 in Hsh1. rewrite Hs4. simpl in *.
      destruct (beqAddr globalIdPD idPDchild) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HcheckChilds3: true = checkChild idPDchild s3 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s3).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. rewrite HlookupBlockEq in *.
      destruct HcheckChild as (HcheckChild & Hsh1).
      destruct (lookup idPDchild (memory s3) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      split; trivial. rewrite Hs4 in HcheckChild. simpl in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(HPDTIfPDFlags3 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChilds3).
    unfold bentryAFlag in *. unfold bentryPFlag in *.
    destruct HPDTIfPDFlags3 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). unfold bentryStartAddr in *.
    unfold entryPDT in *. rewrite HlookupBlockEq. split; trivial. split; trivial. exists startaddr. split; trivial.
    destruct (lookup idPDchild (memory s3) beqAddr); try(congruence). destruct v; try(congruence). rewrite Hs4. simpl.
    destruct (beqAddr globalIdPD (startAddr (blockrange b))) eqn:HbeqGlobStart; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(Hstructs5: StructurePointerIsKS s5).
  {
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts4: exists pdentryParts4, lookup partition (memory s4) beqAddr = Some (PDT pdentryParts4)
      /\ structure pdentryParts4 = structure pdentryPart).
    {
      rewrite Hs5 in HlookupPart. simpl in *. destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. exists prevPDentry2.
        injection HlookupPart as HlookupPart. subst pdentryPart. rewrite Hprev3. split; trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        exists pdentryPart. split; trivial.
    }
    destruct HlookupParts4 as [pdentryParts4 (HlookupParts4 & HstructEq)]. rewrite <-HstructEq in *.
    specialize(Hstructs4 partition pdentryParts4 HlookupParts4 HbeqStructNull). unfold isKS in *. rewrite Hs5. simpl.
    destruct (beqAddr globalIdPD (structure pdentryParts4)) eqn:HbeqGlobStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobStruct. rewrite HbeqGlobStruct in *. rewrite HlookupGlobs4 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HgetPartsEqs5: getPartitions multiplexer s5 = getPartitions multiplexer s4).
  {
    rewrite Hs5. apply getPartitionsEqPDT with prevPDentry2; try(rewrite Hprev3); trivial.
    - unfold noDupPartitionTree. rewrite HgetPartsEqs4. rewrite HgetPartsEqs3. rewrite HgetPartsEqs2. assumption.
    - unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }
  assert(HgetMappedBEqs5s4: forall part, getMappedBlocks part s5 = getMappedBlocks part s4).
  {
    intro part. rewrite Hs5. apply getMappedBlocksEqPDT with prevPDentry2; trivial. rewrite Hprev3.
    reflexivity.
  }
  assert(HPDTIfPDFlags5: PDTIfPDFlag s5).
  {
    intros idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild. rewrite HgetPartsEqs5 in *.
    rewrite HgetMappedBEqs5s4 in *.
    assert(HlookupBlockEq: lookup idPDchild (memory s5) beqAddr = lookup idPDchild (memory s4) beqAddr).
    {
      destruct HcheckChild as (_ & Hsh1). unfold sh1entryAddr in *. rewrite Hs5 in Hsh1. rewrite Hs5. simpl in *.
      destruct (beqAddr globalIdPD idPDchild) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HcheckChilds4: true = checkChild idPDchild s4 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s4).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. rewrite HlookupBlockEq in *.
      destruct HcheckChild as (HcheckChild & Hsh1).
      destruct (lookup idPDchild (memory s4) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      split; trivial. rewrite Hs5 in HcheckChild. simpl in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(HPDTIfPDFlags4 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChilds4).
    unfold bentryAFlag in *. unfold bentryPFlag in *.
    destruct HPDTIfPDFlags4 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). unfold bentryStartAddr in *.
    unfold entryPDT in *. rewrite HlookupBlockEq. split; trivial. split; trivial. exists startaddr. split; trivial.
    destruct (lookup idPDchild (memory s4) beqAddr); try(congruence). destruct v; try(congruence). rewrite Hs5. simpl.
    destruct (beqAddr globalIdPD (startAddr (blockrange b))) eqn:HbeqGlobStart; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }
  assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
  {
    rewrite <-HgetPartsEqs1. rewrite <-HgetPartsEqs2. rewrite <-HgetPartsEqs3. rewrite <-HgetPartsEqs4.
    rewrite <-HgetPartsEqs5. rewrite Hs. apply getPartitionsEqPDT with prevPDentry3; try(rewrite HnewPD); trivial.
    - unfold noDupPartitionTree. rewrite HgetPartsEqs5. rewrite HgetPartsEqs4. rewrite HgetPartsEqs3.
      rewrite HgetPartsEqs2. assumption.
    - unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }
  destruct HpropsBis as (HlastBlock & HlastIdx & HbeqNullGlob & HlebMaxPrep & HkernEntries & HblockEq & HbeqNullBlock
    & HtotLen & HltSizeTot & Hsize & HblockStartEq & Hmax & HnewNbFree & HsuccNbPrep & HlebNewFreeMax).
  rewrite beqAddrSym in HbeqNullGlob.

  assert(HstablePDTs0: forall part, isPDT part s0 -> isPDT part s).
  {
    intros part HpartIsPDT. unfold isPDT in *. rewrite Hs. rewrite Hs5. rewrite Hs4.
    simpl. destruct (beqAddr globalIdPD part) eqn:HbeqGlobPart; trivial. rewrite <-beqAddrFalse in *.
    rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr part) eqn:HbeqLastPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastPart. rewrite HbeqLastPart in *. rewrite HlookupLasts0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite Hs2. simpl. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part) eqn:HbeqNextPart.
    { rewrite <-DTL.beqAddrTrue in HbeqNextPart. rewrite HbeqNextPart in *. rewrite HlookupNext in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }

  assert(HstablePDT: forall part, isPDT part s -> isPDT part s0).
  {
    intros part HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT.
    rewrite Hs5 in HpartIsPDT. rewrite Hs4 in HpartIsPDT. simpl in *.
    destruct (beqAddr globalIdPD part) eqn:HbeqGlobPart.
    - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst part. rewrite HlookupGlobs0. trivial.
    - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HpartIsPDT. simpl in *.
      destruct (beqAddr lastBlockEntryAddr part) eqn:HbeqLastPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part) eqn:HbeqNextPart;
        try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
     rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }

  assert(HgetKSEqs1: forall partition, isPDT partition s0 -> getKSEntries partition s1 = getKSEntries partition s0).
  {
    intros partition HpartIsPDT. rewrite Hs1. unfold isPDT in *.
    destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply getKSEntriesEqPADDR with p; trivial.
    1,2,3: unfold consistency1 in *; intuition. exists (completeListOfKernels (structure p) s0). split; try(split).
    - apply completeKernList; trivial; unfold consistency1 in *; intuition.
    - apply HstartNotKerns0 with partition. apply completeKernListIsListOfKern; trivial; unfold consistency1 in *;
        intuition.
    - assert(Hres: noDupListOfKerns s0) by (unfold consistency1 in *; intuition). unfold noDupListOfKerns in *.
      apply Hres with partition. apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
  }

  assert(HgetKSEqss2: forall partition, getKSEntries partition s = getKSEntries partition s2).
  {
    intro partition. assert(Heqs3: getKSEntries partition s3 = getKSEntries partition s2).
    {
      rewrite Hs3. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupLasts2. trivial.
    }
    assert(Heqs4: getKSEntries partition s4 = getKSEntries partition s2).
    {
      rewrite <-Heqs3. rewrite Hs4. apply getKSEntriesEqPDT with prevPDentry; trivial. rewrite Hprev2. reflexivity.
    }
    assert(Heqs5: getKSEntries partition s5 = getKSEntries partition s2).
    {
      rewrite <-Heqs4. rewrite Hs5. apply getKSEntriesEqPDT with prevPDentry2; trivial. rewrite Hprev3. reflexivity.
    }
    rewrite <-Heqs5. rewrite Hs. apply getKSEntriesEqPDT with prevPDentry3; trivial. rewrite HnewPD. reflexivity.
  }

  assert(HgetKSEqNotGlob: forall partition, isPDT partition s0 -> beqAddr globalIdPD partition = false
    -> getKSEntries partition s = getKSEntries partition s0).
  {
    intros partition HpartIsPDT HbeqGlobPart. rewrite <-HgetKSEqs1; trivial. rewrite HgetKSEqss2. rewrite Hs2.
    rewrite <-beqAddrFalse in *. apply not_eq_sym in HbeqGlobPart. apply getKSEntriesEqPDTNotInPart; trivial.
    1,2: unfold isPADDR; unfold isBE; rewrite HlookupGlobs1; intuition.
  }

  assert(HgetKSEqGlob: getKSEntries globalIdPD s
    = (getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0 (CIndex (kernelStructureEntriesNb-1)))
        ++ getKSEntries globalIdPD s0).
  {
    rewrite <-HgetKSEqs1; trivial. rewrite HgetKSEqss2. rewrite Hs2.
    assert(HgetStructEq:
      getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s0 (CIndex (kernelStructureEntriesNb-1))
        = getKSEntriesInStructAux (maxIdx+1) requisitionedBlockStart s1 (CIndex (kernelStructureEntriesNb-1))).
    { apply eq_sym. rewrite Hs1. apply getKSEntriesInStructAuxEqPADDR; trivial. }
    rewrite HgetStructEq. apply getKSEntriesEqPDTNewStruct with pdentry; trivial.
    - rewrite Hprev. reflexivity.
    - rewrite <-beqAddrFalse. intro Hcontra. rewrite Hcontra in *. unfold isKS in *.
      assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
      destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    - unfold isKS in *. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) requisitionedBlockStart) eqn:HbeqNextStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextStart. rewrite HbeqNextStart in *. unfold isKS in *.
        rewrite HlookupNext in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - rewrite Hs1. simpl. rewrite beqAddrTrue. f_equal. f_equal. unfold pdentryStructurePointer in *.
      rewrite HlookupGlobs0 in *. assumption.
    - destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
      + rewrite <-DTL.beqAddrTrue in HbeqStructNull. auto.
      + right. rewrite <-beqAddrFalse in *. specialize(Hstructs1 globalIdPD pdentry HlookupGlobs1 HbeqStructNull).
        split; trivial. intros kernList HkernList.
        assert(HkernListCompl: isListOfKernels ((structure pdentry)::kernList) globalIdPD s1).
        { simpl. exists pdentry. auto. }
        specialize(HmaxNbPreps1 globalIdPD ((structure pdentry)::kernList) HkernListCompl). simpl in HmaxNbPreps1.
        assert(HlebLenMax: length kernList <= maxNbPrepare) by lia.
        pose proof (listOfKernIsInclInComplete (structure pdentry) kernList s1 HnextValids1 Hstructs1 HkernList
          HlebLenMax) as Hres. destruct Hres as [postList HcompListEq].
        assert(HcompleteEq: completeListOfKernels (structure pdentry) s1
          = completeListOfKernels (structure pdentry) s0).
        {
          rewrite Hs1. apply completeListOfKernelsEqPADDRNew; trivial.
          - unfold consistency1 in *; intuition.
          - unfold isKS in *. rewrite Hs1 in Hstructs1. simpl in Hstructs1.
            destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) (structure pdentry)) eqn:HbeqNextStruct;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          - unfold isPADDR. rewrite HlookupNext. trivial.
          - assert(Hnull: nullAddrExists s0) by (unfold consistency1 in *; intuition).
            assert(HnextValid: nextKernelIsValid s0) by (unfold consistency1 in *; intuition).
            pose proof (completeKernListIsListOfKern globalIdPD pdentry s0 Hnull HnextValid HlookupGlobs0)
              as HisKernList. apply HstartNotKerns0 with globalIdPD; assumption.
        }
        rewrite HcompleteEq in *.
        assert(Hres: length kernList <= length (completeListOfKernels (structure pdentry) s0)).
        { rewrite HcompListEq. simpl. rewrite length_app. lia. }
        lia.
    - unfold isPDT. rewrite HlookupGlobs0. trivial.
  }

  assert(HglobIsPDTs0: isPDT globalIdPD s0) by (unfold isPDT; rewrite HlookupGlobs0; trivial).
  unfold blkoffset in HlastBlock. rewrite HlastIdx in HlastBlock. cbn in HlastBlock.
  rewrite PeanoNat.Nat.add_0_r in HlastBlock. rewrite HkernEntries in HlastBlock. unfold CIndex in HlastBlock.
  destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia).
  cbn -[kernelStructureEntriesNb] in HlastBlock. rewrite PeanoNat.Nat.add_sub_assoc in HlastBlock; try(lia).

  assert(HgetFreeSlotsListEq: forall partition, beqAddr globalIdPD partition = false
    -> getFreeSlotsList partition s = getFreeSlotsList partition s0).
  {
    intros partition HbeqGlobPart. unfold getFreeSlotsList. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl lookup.
    rewrite HbeqGlobPart. rewrite beqAddrTrue. rewrite <-Hs4. rewrite <-Hs5. rewrite <-Hs.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastPart. subst partition. rewrite HlookupLasts0. reflexivity.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextPart. subst partition. rewrite HlookupNext. reflexivity.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
    destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
    assert(Hfirst: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
    rewrite <-beqAddrFalse in *. specialize(Hfirst partition p HlookupPart HbeqFirstNull).
    destruct Hfirst as (HfirstIsBE & _). unfold isBE in *.
    assert(Heqs1: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s1 (nbfreeslots p)
      = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
    {
      rewrite Hs1. apply getFreeSlotsListRecEqPADDR.
      - unfold isPADDR. rewrite HlookupNext. trivial.
      - destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) (firstfreeslot p)) eqn:HbeqNextFirst;
          trivial. exfalso. rewrite <-DTL.beqAddrTrue in HbeqNextFirst. rewrite HbeqNextFirst in *.
        rewrite HlookupNext in *. congruence.
    }
    destruct (beqAddr (firstfreeslot p) globalIdPD) eqn:HbeqFirstGlob.
    {
      rewrite <-DTL.beqAddrTrue in HbeqFirstGlob. rewrite HbeqFirstGlob in *. rewrite HlookupGlobs0 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. assert(Heqs2: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s2 (nbfreeslots p)
      = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
    {
      rewrite <-Heqs1. rewrite Hs2. apply getFreeSlotsListRecEqPDT; trivial; unfold isBE; unfold isPADDR;
        rewrite HlookupGlobs1; intuition.
    }
    assert(HnoDupFree: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
    specialize(HnoDupFree partition p HlookupPart).
    destruct HnoDupFree as [optFreeList (HoptFree & HwellFormedFree & HnoDupFree)]. unfold getFreeSlotsList in *.
    rewrite HlookupPart in *. rewrite beqAddrFalse in HbeqFirstNull. rewrite HbeqFirstNull in *. subst optFreeList.
    assert(HpartIsPDT: isPDT partition s0) by (unfold isPDT; rewrite HlookupPart; trivial).
    assert(HlastIsNew: In (SomePaddr lastBlockEntryAddr)
       (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))).
    {
      apply optionIsInFilter. apply HstartsBlocksAreNew with (kernelStructureEntriesNb-1). lia.
      rewrite PeanoNat.Nat.add_sub_assoc; try(lia). assumption.
    }
    specialize(HdisjointNew partition HpartIsPDT (SomePaddr lastBlockEntryAddr) HlastIsNew).
    rewrite HlookupPart in *. rewrite HbeqFirstNull in *.
    assert(Heqs3: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s3 (nbfreeslots p)
      = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
    {
      rewrite <-Heqs2. rewrite Hs3. apply getFreeSlotsListRecEqBE; try(rewrite Heqs2); trivial.
      - rewrite MaxIdxNextEq in *. simpl in HdisjointNew. simpl in HwellFormedFree.
        destruct (lookup (firstfreeslot p) (memory s0) beqAddr); try(exfalso; simpl in HwellFormedFree; congruence).
        destruct v; try(exfalso; simpl in HwellFormedFree; congruence).
        destruct (StateLib.Index.pred (nbfreeslots p)); try(exfalso; simpl in HwellFormedFree; congruence).
        simpl in HdisjointNew. apply Decidable.not_or in HdisjointNew. destruct HdisjointNew as (Hres & _).
        contradict Hres. f_equal. assumption.
      - unfold isBE. rewrite HlookupLasts2. trivial.
      - contradict HdisjointNew. apply optionIsInFilter; assumption.
    }
    assert(Heqs4: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s4 (nbfreeslots p)
      = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
    {
      rewrite <-Heqs3. rewrite Hs4. apply getFreeSlotsListRecEqPDT; unfold isBE; unfold isPADDR;
        try(rewrite HlookupGlobs3); trivial; intuition.
    }
    assert(Heqs5: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s5 (nbfreeslots p)
      = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
    {
      rewrite <-Heqs4. rewrite Hs5. apply getFreeSlotsListRecEqPDT; unfold isBE; unfold isPADDR;
        try(rewrite HlookupGlobs4); trivial; intuition.
    }
    rewrite <-Heqs5. rewrite Hs. apply getFreeSlotsListRecEqPDT; unfold isBE; unfold isPADDR;
      try(rewrite HlookupGlobs5); trivial; intuition.
  }

  assert(HnbFreeIsLen: NbFreeSlotsISNbFreeSlotsInList s0) by (unfold consistency1 in *; intuition).
  assert(HnbFrees0: pdentryNbFreeSlots globalIdPD currentNbFreeSlots s0).
  {
    unfold pdentryNbFreeSlots in *. rewrite HlookupGlobs0. rewrite HlookupGlobs4 in *. rewrite Hprev2 in HnbFrees4.
    simpl in HnbFrees4. rewrite Hprev in HnbFrees4. simpl in HnbFrees4. assumption.
  }
  specialize(HnbFreeIsLen globalIdPD currentNbFreeSlots HglobIsPDTs0 HnbFrees0).
  destruct HnbFreeIsLen as [optFreeList (Hlist & HwellFormedAncFree & HnbFreeIsLen)]. subst optFreeList.

  assert(HlookupLasts: lookup lastBlockEntryAddr (memory s) beqAddr
    = Some(BE (CBlockEntry (read bentryStart) (write bentryStart) (exec bentryStart) (present bentryStart)
        (accessible bentryStart) (blockindex bentryStart)
        (CBlock (startAddr (blockrange bentryStart)) currFirstFreeSlot)))).
  {
    rewrite Hs. rewrite Hs5. rewrite Hs4. simpl. destruct (beqAddr globalIdPD lastBlockEntryAddr) eqn:HbeqGlobLast.
    { rewrite <-DTL.beqAddrTrue in HbeqGlobLast. rewrite HbeqGlobLast in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl. rewrite beqAddrTrue.
    reflexivity.
  }
  rewrite HnewBs3 in HlookupLasts.

  assert(Hsh1offset: i sh1offset = kernelStructureEntriesNb).
  {
    unfold sh1offset. unfold blkoffset. unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl.
    pose proof maxIdxBiggerThanNbOfKernels. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl.
    reflexivity.
  }
  assert(Hscoffset: i scoffset = kernelStructureEntriesNb + kernelStructureEntriesNb).
  {
    unfold scoffset. rewrite Hsh1offset. unfold CIndex. cbn. pose proof Constants.maxIdxBiggerThanMinBlock.
    destruct (le_dec 16 maxIdx); try(lia). simpl. reflexivity.
  }
  assert(Hnextoffset: i nextoffset = kernelStructureEntriesNb + kernelStructureEntriesNb +kernelStructureEntriesNb).
  {
    unfold nextoffset. rewrite Hscoffset. unfold CIndex. cbn. pose proof Constants.maxIdxBiggerThanMinBlock.
    destruct (le_dec 24 maxIdx); try(lia). simpl. reflexivity.
  }

  assert(HblockFieldsEq: forall block bentry, lookup block (memory s0) beqAddr = Some(BE bentry)
    -> exists bentrys, lookup block (memory s) beqAddr = Some(BE bentrys)
        /\ read bentrys = read bentry /\ write bentrys = write bentry /\ exec bentrys = exec bentry
        /\ present bentrys = present bentry /\ accessible bentrys = accessible bentry
        /\ blockindex bentrys = blockindex bentry
        /\ startAddr (blockrange bentrys) = startAddr (blockrange bentry)).
  {
    intros block bentry HlookupBlocks0. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
    destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobBlock. subst block. exfalso; congruence.
    }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
    - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. rewrite HnewBs3. rewrite HlookupLasts0 in *.
      injection HlookupBlocks0 as HlookupBlocks0. subst bentry.
      exists {|
               read := read bentryStart;
               write := write bentryStart;
               exec := exec bentryStart;
               present := present bentryStart;
               accessible := accessible bentryStart;
               blockindex := blockindex bentryStart;
               blockrange :=
                 {|
                   startAddr := startAddr (blockrange bentryStart); endAddr := currFirstFreeSlot; Hsize := l2
                 |};
               Hidx := l1
             |}. simpl. intuition.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextBlock. subst block. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. exists bentry.
      intuition.
  }

  assert(HlookupSh1Eq: forall addr, isSHE addr s0
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intros addr HaddrIsSHE. unfold isSHE in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
    destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobAddr. subst addr. rewrite HlookupGlobs0 in *. exfalso; congruence.
    }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqLastAddr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastAddr. subst addr. rewrite HlookupLasts0 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in HbeqGlobAddr. rewrite HbeqGlobAddr. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) addr) eqn:HbeqNextAddr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextAddr. subst addr. rewrite HlookupNext in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }

  assert(HlookupSceEq: forall addr, isSCE addr s0
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intros addr HaddrIsSCE. unfold isSCE in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
    destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobAddr. subst addr. rewrite HlookupGlobs0 in *. exfalso; congruence.
    }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqLastAddr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastAddr. subst addr. rewrite HlookupLasts0 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in HbeqGlobAddr. rewrite HbeqGlobAddr. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) addr) eqn:HbeqNextAddr.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNextAddr. subst addr. rewrite HlookupNext in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }

  assert(HgetMappedBEq: forall part, isPDT part s0 -> getMappedBlocks part s = getMappedBlocks part s0).
  {
    intros part HpartIsPDT. rewrite <-HgetMappedBEqs1; trivial. rewrite <-HgetMappedBEqs2s1.
    rewrite <-HgetMappedBEqs3s2. rewrite <-HgetMappedBEqs4s3. rewrite <-HgetMappedBEqs5s4.
    rewrite Hs. apply getMappedBlocksEqPDT with prevPDentry3; trivial. rewrite HnewPD.
    reflexivity.
  }

  assert(HgetChildrenEq: forall part, isPDT part s0 -> getChildren part s = getChildren part s0).
  {
    intros part HpartIsPDT. unfold isPDT in *.
    destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). assert(Heqs1: getChildren part s1 = getChildren part s0).
    {
      rewrite Hs1. apply getChildrenEqPADDR with p; trivial. 1,2,3: unfold consistency1 in *; intuition.
      exists (completeListOfKernels (structure p) s0). split; try(split).
      - apply completeKernList; trivial; unfold consistency1 in *; intuition.
      - apply HstartNotKerns0 with part.
        apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
      - assert(Hres: noDupListOfKerns s0) by (unfold consistency1 in *; intuition). unfold noDupListOfKerns in *.
        apply Hres with part. apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
    }
    assert(HlookupParts1: lookup part (memory s1) beqAddr = Some (PDT p)).
    {
      rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part) eqn:HbeqNextPart.
      { rewrite <-DTL.beqAddrTrue in HbeqNextPart. subst part. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(Heqs2: getChildren part s2 = getChildren part s0).
    {
      rewrite <-Heqs1. rewrite Hs2.
      apply getChildrenEqPDTNewEmptyStruct with pdentry requisitionedBlockStart; trivial.
      - rewrite Hprev. reflexivity.
      - unfold isKS in *. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) requisitionedBlockStart) eqn:HbeqNextStart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqNextStart. rewrite HbeqNextStart in *. rewrite HlookupNext in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - rewrite Hs1. simpl. rewrite beqAddrTrue. unfold pdentryStructurePointer in *. rewrite HlookupGlobs0 in *.
        rewrite Hstructs0. reflexivity.
      - assert(HcompleteEq: completeListOfKernels (structure pdentry) s1
          = completeListOfKernels (structure pdentry) s0).
        {
          rewrite Hs1. destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
          - rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. unfold completeListOfKernels.
            assert(Hnulls0: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition).
            unfold nullAddrExists in *. unfold isPADDR in *. rewrite <-Hs1.
            destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence).
            destruct (lookup nullAddr (memory s1) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). reflexivity.
          - rewrite <-beqAddrFalse in *.
            assert(HstructIsKS: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
            specialize(HstructIsKS globalIdPD pdentry HlookupGlobs0 HbeqStructNull).
            apply completeListOfKernelsEqPADDRNew; trivial.
            + unfold consistency1 in *; intuition.
            + unfold isPADDR. rewrite HlookupNext. trivial.
            + apply HstartNotKerns0 with globalIdPD.
              apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
        }
        rewrite HcompleteEq. assumption.
      - intros addr HaddrIn. apply getKSEntriesInStructAuxToIndexAux in HaddrIn; try(rewrite <-HidxEq; lia).
        destruct HaddrIn as [kernIdx (HltIdxKernEntries & Haddr)]. subst addr. rewrite <-HidxEq in *.
        apply HPflagNews1; lia.
      - unfold isPDT. rewrite HlookupParts1. trivial.
    }
    assert(HlookupParts2: isPDT part s2).
    {
      unfold isPDT. rewrite Hs2. simpl.
      destruct (beqAddr globalIdPD part) eqn:HbeqParts; trivial. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParts1. trivial.
    }
    assert(Heqs3: getChildren part s3 = getChildren part s0).
    {
      rewrite <-Heqs2. rewrite Hs3. apply getChildrenEqBENoStartNoPresentChange with bentryStart; trivial.
      1,2: rewrite HnewBs3; reflexivity.
    }
    assert(Heqs4: getChildren part s4 = getChildren part s0).
    {
      rewrite <-Heqs3. rewrite Hs4. apply getChildrenEqPDT with prevPDentry; trivial. rewrite Hprev2.
      reflexivity.
    }
    assert(Heqs5: getChildren part s5 = getChildren part s0).
    {
      rewrite <-Heqs4. rewrite Hs5. apply getChildrenEqPDT with prevPDentry2; trivial. rewrite Hprev3.
      reflexivity.
    }
    rewrite <-Heqs5. rewrite Hs. apply getChildrenEqPDT with prevPDentry3; trivial. rewrite HnewPD.
    reflexivity.
  }

  assert(HPflagLasts0: bentryPFlag lastBlockEntryAddr false s0).
  {
    assert(HltIdxKernEntries: CIndex (kernelStructureEntriesNb-1) < kernelStructureEntriesNb) by lia.
    specialize(HnewFree (CIndex (kernelStructureEntriesNb-1)) HltIdxKernEntries). rewrite <-HidxEq in HnewFree.
    replace (CPaddr (requisitionedBlockStart+(kernelStructureEntriesNb-1))) with lastBlockEntryAddr in HnewFree;
      try(rewrite PeanoNat.Nat.add_sub_assoc; try(cbn; lia); auto). unfold bentryPFlag. unfold isFreeSlot in *.
    rewrite HlookupLasts0 in *.
    destruct (lookup (CPaddr (lastBlockEntryAddr + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct (lookup (CPaddr (lastBlockEntryAddr + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). destruct HnewFree as (_ & _ & _ & _ & Hres & _). auto.
  }

  assert(Hblkidx: bentryBlockIndex requisitionedBlockStart (CIndex 0) s).
  {
    unfold bentryBlockIndex in *.
    destruct (lookup requisitionedBlockStart (memory s0) beqAddr) eqn:Hlookup; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply HblockFieldsEq in Hlookup.
    destruct Hlookup as [bentry (Hlookup & _ & _ & _ & _ & _ & Heq & _)]. rewrite Hlookup. rewrite Heq. assumption.
  }

  assert(HlookupNexts: lookup (CPaddr (requisitionedBlockStart + nextoffset)) (memory s) beqAddr
    = Some(PADDR oldKStructurePointer)).
  {
    rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
    destruct (beqAddr globalIdPD (CPaddr (requisitionedBlockStart + nextoffset))) eqn:HbeqGlobNext.
    { rewrite <-DTL.beqAddrTrue in HbeqGlobNext. rewrite HbeqGlobNext in *. congruence. }
    rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr (CPaddr (requisitionedBlockStart + nextoffset))) eqn:HbeqLastNext.
    { rewrite <-DTL.beqAddrTrue in HbeqLastNext. rewrite HbeqLastNext in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in HbeqGlobNext. rewrite HbeqGlobNext. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial.
  }

  assert(HpartFieldsEq: forall partition pdentryPart, lookup partition (memory s) beqAddr = Some(PDT pdentryPart)
    -> exists pdentryParts0, lookup partition (memory s0) beqAddr = Some(PDT pdentryParts0)
        /\ parent pdentryParts0 = parent pdentryPart
        /\ MPU pdentryParts0 = MPU pdentryPart
        /\ vidtAddr pdentryParts0 = vidtAddr pdentryPart).
  {
    intros partition pdentryPart HlookupPart. rewrite Hs in HlookupPart.
    rewrite Hs5 in HlookupPart. rewrite Hs4 in HlookupPart. simpl in HlookupPart.
    destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
    - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. exists pdentry. split; trivial.
      injection HlookupPart as HlookupPart. subst pdentryPart. rewrite HnewPD. simpl. rewrite Hprev3. simpl.
      rewrite Hprev2. simpl. rewrite Hprev. auto.
    - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart.
      simpl in HlookupPart.
      destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupPart. simpl in HlookupPart. rewrite beqAddrFalse in HbeqParts. rewrite HbeqParts in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists pdentryPart. auto.
  }

  assert(HblockFieldsEqs: forall block bentry, lookup block (memory s) beqAddr = Some(BE bentry)
    -> exists bentrys, lookup block (memory s0) beqAddr = Some(BE bentrys)
        /\ read bentrys = read bentry /\ write bentrys = write bentry /\ exec bentrys = exec bentry
        /\ present bentrys = present bentry /\ accessible bentrys = accessible bentry
        /\ blockindex bentrys = blockindex bentry
        /\ startAddr (blockrange bentrys) = startAddr (blockrange bentry)).
  {
    intros block bentry HlookupBlocks0. rewrite Hs in HlookupBlocks0. rewrite Hs5 in HlookupBlocks0.
    rewrite Hs4 in HlookupBlocks0. simpl in HlookupBlocks0.
    destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupBlocks0.
    simpl in HlookupBlocks0. destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
    - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. injection HlookupBlocks0 as HlookupBlocks0.
      subst bentry. rewrite HnewBs3. simpl. exists bentryStart. intuition.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupBlocks0. simpl in HlookupBlocks0.
      rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HlookupBlocks0.
      simpl in HlookupBlocks0.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. exists bentry.
      intuition.
  }

  assert(HsheEq: forall addr, isSHE addr s -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intros addr HaddrIsSHE. unfold isSHE in *. rewrite Hs in HaddrIsSHE. rewrite Hs5 in HaddrIsSHE.
    rewrite Hs4 in HaddrIsSHE. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl in *.
    destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr; try(exfalso; congruence). rewrite beqAddrTrue in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HaddrIsSHE. rewrite Hs3.
    simpl in *. destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqLastAddr; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
    rewrite Hs2 in HaddrIsSHE. simpl in *. rewrite beqAddrFalse in HbeqGlobAddr. rewrite HbeqGlobAddr in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1.
    rewrite Hs1 in HaddrIsSHE. simpl in *. destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) addr)
      eqn:HbeqNextAddr; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }

  assert(HPDchilds: sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s).
  {
    unfold sh1entryPDchild in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl. rewrite beqAddrTrue.
    destruct (beqAddr globalIdPD (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))) eqn:HbeqGlobSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqGlobSh1. rewrite <-HbeqGlobSh1 in *. rewrite HlookupGlobs2 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite removeDupIdentity; auto.
    rewrite removeDupIdentity; auto. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))) eqn:HbeqLastSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastSh1. rewrite <-HbeqLastSh1 in *. rewrite HlookupLasts2 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
  }

  assert(HgetMappedPEq: forall part, isPDT part s0 -> getMappedPaddr part s = getMappedPaddr part s0).
  {
    intros part HpartIsPDT. specialize(HgetMappedBEq part HpartIsPDT). unfold getMappedPaddr. rewrite HgetMappedBEq.
    assert(Heqs1: getAllPaddrAux (getMappedBlocks part s0) s1 = getAllPaddrAux (getMappedBlocks part s0) s0).
    {
      rewrite Hs1. apply getAllPaddrAuxEqPADDR. unfold isPADDR. rewrite HlookupNext. trivial.
    }
    assert(Heqs2: getAllPaddrAux (getMappedBlocks part s0) s2 = getAllPaddrAux (getMappedBlocks part s0) s0).
    {
      rewrite <-Heqs1. rewrite Hs2. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupGlobs1. trivial.
    }
    assert(Heqs3: getAllPaddrAux (getMappedBlocks part s0) s3 = getAllPaddrAux (getMappedBlocks part s0) s0).
    {
      rewrite <-Heqs2. rewrite Hs3. apply getAllPaddrAuxEqBENoInList. intro Hcontra. apply mappedBlockIsBE in Hcontra.
      destruct Hcontra as [bentry (HlookupLastBis & Hpres)]. unfold bentryPFlag in *. rewrite HlookupLastBis in *.
      congruence.
    }
    assert(Heqs4: getAllPaddrAux (getMappedBlocks part s0) s4 = getAllPaddrAux (getMappedBlocks part s0) s0).
    {
      rewrite <-Heqs3. rewrite Hs4. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupGlobs3. trivial.
    }
    assert(Heqs5: getAllPaddrAux (getMappedBlocks part s0) s5 = getAllPaddrAux (getMappedBlocks part s0) s0).
    {
      rewrite <-Heqs4. rewrite Hs5. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupGlobs4. trivial.
    }
    rewrite <-Heqs5. rewrite Hs. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupGlobs5. trivial.
  }

  assert(HstartNotConf: forall kern part, In kern (getConfigBlocks part s0) -> kern <> requisitionedBlockStart).
  {
    intros kern part HkernIsConf Hcontra. subst kern.
    assert(HstartIsNew: In requisitionedBlockStart
      (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)).
    { rewrite kernelStructureTotalLengthVal. apply getAllPaddrBlockAuxIncl; cbn; lia. }
    specialize(HnewNotConf part requisitionedBlockStart HstartIsNew).
    apply getAllPaddrConfigAuxIncl with (getConfigBlocks part s0) s0 in HkernIsConf;
      try(intro block; apply configBlocksAreBE). congruence.
  }

  assert(HgetConfigPaddrEqs1: forall part, isPDT part s0 -> getConfigPaddr part s1 = getConfigPaddr part s0).
  {
    intros part HpartIsPDT. rewrite Hs1. apply getConfigPaddrEqPADDR.
    1,2,3: unfold consistency1 in *; intuition.
    - unfold isPADDR. rewrite HlookupNext. trivial.
    - destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) nullAddr) eqn:HbeqNextNull; trivial. exfalso.
      rewrite <-DTL.beqAddrTrue in HbeqNextNull. unfold CPaddr in HbeqNextNull.
      destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia). cbn in HbeqNextNull.
      injection HbeqNextNull as HbeqNextNull. cbn in *; lia.
    - intros kern HkernInConf. specialize(HstartNotConf kern part HkernInConf). unfold CPaddr.
      destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia). simpl. intro Hcontra.
      apply PeanoNat.Nat.add_cancel_r in Hcontra. apply paddrEqNatEqEquiv in Hcontra. congruence.
  }

  assert(HgetConfigPaddrEqss2: forall part, isPDT part s0 -> getConfigPaddr part s = getConfigPaddr part s2).
  {
    intros part HpartIsPDT. assert(HpartIsPDTs2: isPDT part s2).
    {
      unfold isPDT in *. rewrite Hs2. simpl. destruct (beqAddr globalIdPD part) eqn:HbeqParts; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part) eqn:HbeqNextPart.
      { rewrite <-DTL.beqAddrTrue in HbeqNextPart. rewrite HbeqNextPart in *. rewrite HlookupNext in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(Heqs3: getConfigPaddr part s3 = getConfigPaddr part s2).
    {
      rewrite Hs3. apply getConfigPaddrEqBE; trivial. unfold isBE. rewrite HlookupLasts2. trivial.
    }
    assert(HpartIsPDTs3: isPDT part s3).
    {
      unfold isPDT in *. rewrite Hs3. simpl. destruct (beqAddr lastBlockEntryAddr part) eqn:HbeqLastPart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastPart. rewrite HbeqLastPart in *. rewrite HlookupLasts0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(Heqs4: getConfigPaddr part s4 = getConfigPaddr part s2).
    {
      rewrite <-Heqs3. rewrite Hs4. apply getConfigPaddrEqPDT with prevPDentry; trivial.
      rewrite Hprev2. reflexivity.
    }
    assert(HpartIsPDTs4: isPDT part s4).
    {
      unfold isPDT in *. rewrite Hs4. simpl. destruct (beqAddr globalIdPD part) eqn:HbeqParts; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(Heqs5: getConfigPaddr part s5 = getConfigPaddr part s2).
    {
      rewrite <-Heqs4. rewrite Hs5. apply getConfigPaddrEqPDT with prevPDentry2; trivial.
      rewrite Hprev3. reflexivity.
    }
    rewrite <-Heqs5. rewrite Hs. apply getConfigPaddrEqPDT with prevPDentry3; trivial.
    - unfold isPDT in *. rewrite Hs5. simpl. destruct (beqAddr globalIdPD part) eqn:HbeqParts; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - rewrite HnewPD. reflexivity.
  }

  assert(HlookupGlobs: lookup globalIdPD (memory s) beqAddr = Some (PDT newPDentry)).
  { rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity. }

  assert(nullAddrExists s).
  { (* BEGIN nullAddrExists s *)
    unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
    rewrite HbeqNullGlob. rewrite beqAddrTrue. rewrite <-beqAddrFalse in HbeqNullGlob.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
    destruct (beqAddr lastBlockEntryAddr nullAddr) eqn:HbeqLastNull.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastNull. rewrite HbeqLastNull in *. rewrite HlookupLasts1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite beqAddrFalse in HbeqNullGlob. rewrite HbeqNullGlob. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END nullAddrExists *)
  }

  assert(nextKernelIsValid s).
  { (* BEGIN nextKernelIsValid s *)
    assert(Hcons0: nextKernelIsValid s0) by (unfold consistency1 in *; intuition).
    intros kernel HkernIsKS.
    assert(HkernIsKSs0: isKS kernel s0).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs5 in HkernIsKS. rewrite Hs4 in HkernIsKS.
      simpl in *. destruct (beqAddr globalIdPD kernel) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HkernIsKS.
      simpl in *. destruct (beqAddr lastBlockEntryAddr kernel) eqn:HbeqLastBlock.
      - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst kernel. rewrite HlookupLasts0.
        rewrite HnewBs3 in HkernIsKS. simpl in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs2 in HkernIsKS. simpl in *. rewrite beqAddrFalse in HbeqGlobBlock.
        rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.  rewrite Hs1 in HkernIsKS. simpl in *.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) kernel) eqn:HbeqNextBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 kernel HkernIsKSs0). destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupKerNext & Hnext)]).
    split; trivial. destruct (beqAddr requisitionedBlockStart kernel) eqn:HbeqKerns.
    - rewrite <-DTL.beqAddrTrue in HbeqKerns. subst kernel. exists oldKStructurePointer. split.
      + intro Hp. specialize(HlookupKerNext Hp). rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
        destruct (beqAddr globalIdPD {| p := requisitionedBlockStart + nextoffset; Hp := Hp |}) eqn:HbeqGlobNext.
        { rewrite <-DTL.beqAddrTrue in HbeqGlobNext. rewrite HbeqGlobNext in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr {| p:=requisitionedBlockStart+nextoffset; Hp:=Hp |}) eqn:HbeqLastNext.
        { rewrite <-DTL.beqAddrTrue in HbeqLastNext. rewrite HbeqLastNext in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in HbeqGlobNext. rewrite HbeqGlobNext. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        assert(Heq: CPaddr (requisitionedBlockStart + nextoffset)
          = {| p := requisitionedBlockStart + nextoffset; Hp := Hp |}).
        {
          unfold CPaddr. destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia).
          apply paddrEqNatEqEquiv. reflexivity.
        }
        rewrite <-Heq. rewrite beqAddrTrue. reflexivity.
      + unfold pdentryStructurePointer in *. rewrite HlookupGlobs0 in *.
        assert(Hstruct: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
        destruct (beqAddr oldKStructurePointer nullAddr) eqn:HbeqOldNull; try(rewrite DTL.beqAddrTrue; auto).
        rewrite <-beqAddrFalse in *. subst oldKStructurePointer. left.
        specialize(Hstruct globalIdPD pdentry HlookupGlobs0 HbeqOldNull). unfold isKS in *.
        destruct (lookup (structure pdentry) (memory s0) beqAddr) eqn:HlookupStruct; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply HblockFieldsEq in HlookupStruct.
        destruct HlookupStruct as [bentrys (HlookupStructs & _ & _ & _ & _ & _ & Heq & _)]. rewrite HlookupStructs.
        rewrite Heq. assumption.
    - exists nextAddr. split.
      + rewrite Hs. rewrite Hs5. rewrite Hs4. simpl. intro Hp. specialize(HlookupKerNext Hp).
        destruct (beqAddr globalIdPD {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqGlobNext.
        { rewrite <-DTL.beqAddrTrue in HbeqGlobNext. rewrite HbeqGlobNext in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr {| p:=kernel+nextoffset; Hp:=Hp |}) eqn:HbeqLastNext.
        { rewrite <-DTL.beqAddrTrue in HbeqLastNext. rewrite HbeqLastNext in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in HbeqGlobNext. rewrite HbeqGlobNext. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) {| p := kernel + nextoffset; Hp := Hp |})
          eqn:HbeqNexts.
        {
          exfalso. rewrite <-DTL.beqAddrTrue in HbeqNexts. unfold CPaddr in HbeqNexts.
          destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia).
          injection HbeqNexts as HbeqNexts. apply PeanoNat.Nat.add_cancel_r in HbeqNexts.
          apply paddrEqNatEqEquiv in HbeqNexts. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      + destruct Hnext as [HnextIsKS | HnextIsNull]; auto. left. unfold isKS in *.
        destruct (lookup nextAddr (memory s0) beqAddr) eqn:HlookupNextAddr; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply HblockFieldsEq in HlookupNextAddr.
        destruct HlookupNextAddr as [bentrys (Hlookups & _ & _ & _ & _ & _ & Heq & _)]. rewrite Hlookups.
        rewrite Heq. assumption.
    (* END nextKernelIsValid *)
  }

  assert(maxNbPrepareIsMaxNbKernels s).
  { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
    assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by (unfold consistency1 in *; intuition).
    intros partition kernList HlistOfKerns.
    destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
    - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. destruct kernList; try(simpl; lia).
      assert(HlistOfKernss0: p = requisitionedBlockStart
        /\ isListOfKernels kernList globalIdPD s1
        /\ isListOfKernels kernList globalIdPD s0).
      {
        simpl in HlistOfKerns. destruct HlistOfKerns as [newPDentryBis (HlookupGlobsBis & HbeqStructNull & Hrec)].
        rewrite HlookupGlobs in HlookupGlobsBis. injection HlookupGlobsBis as HlookupGlobsBis. subst newPDentryBis.
        destruct Hrec as (Heq & Hrec). subst p. rewrite HnewPD. simpl. rewrite Hprev3. simpl. rewrite Hprev2. simpl.
        rewrite Hprev. simpl. split; trivial. rewrite HnewPD in Hrec. simpl in Hrec. rewrite Hprev3 in Hrec.
        simpl in Hrec. rewrite Hprev2 in Hrec. simpl in Hrec. rewrite Hprev in Hrec. simpl in Hrec.
        destruct kernList as [ | firstEl kernList]; simpl; try(auto). split.
        1,2: exists pdentry; split; trivial; simpl in Hrec;
          destruct Hrec as (HlookupNextBis & HlebNextMax & HbeqFirstNull & Hrec); rewrite Hs in HlookupNextBis;
          rewrite Hs5 in HlookupNextBis; rewrite Hs4 in HlookupNextBis; simpl in HlookupNextBis;
          destruct (beqAddr globalIdPD (CPaddr (requisitionedBlockStart+nextoffset))) eqn:HbeqGlobNext;
            try(exfalso; congruence); rewrite beqAddrTrue in HlookupNextBis; rewrite <-beqAddrFalse in *;
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial;
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial;
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial; rewrite Hs3 in HlookupNextBis; simpl in *;
          destruct (beqAddr lastBlockEntryAddr (CPaddr (requisitionedBlockStart + nextoffset))) eqn:HbeqLastNext;
            try(exfalso; congruence); rewrite <-beqAddrFalse in *;
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial; rewrite Hs2 in HlookupNextBis; simpl in *;
          rewrite beqAddrFalse in HbeqGlobNext; rewrite HbeqGlobNext in *; rewrite <-beqAddrFalse in *;
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial; rewrite Hs1 in HlookupNextBis; simpl in *;
          rewrite beqAddrTrue in HlookupNextBis; injection HlookupNextBis as HlookupNextBis; subst firstEl;
          unfold pdentryStructurePointer in *; rewrite HlookupGlobs0 in *; rewrite <-Hstructs0; split; trivial;
          split; trivial; rewrite Hs in Hrec; apply isListOfKernelsAuxEqPDT in Hrec; rewrite Hs5 in Hrec;
          apply isListOfKernelsAuxEqPDT in Hrec; rewrite Hs4 in Hrec; apply isListOfKernelsAuxEqPDT in Hrec;
          rewrite Hs3 in Hrec; apply isListOfKernelsAuxEqBE in Hrec; rewrite Hs2 in Hrec;
          apply isListOfKernelsAuxEqPDT in Hrec; trivial. revert Hrec. rewrite Hs1.
        apply isListOfKernelsAuxEqPADDR; trivial.
        - assert(HkernList: isListOfKernels [oldKStructurePointer] globalIdPD s0).
          { simpl. exists pdentry. split; trivial. rewrite <-Hstructs0. auto. }
          specialize(HstartNotKerns0 globalIdPD [oldKStructurePointer] HkernList). simpl in HstartNotKerns0. auto.
        - intros klist Hklist. assert(HkernList: isListOfKernels (oldKStructurePointer::klist) globalIdPD s0).
          { simpl. exists pdentry. split; trivial. rewrite <-Hstructs0. auto. }
          specialize(HstartNotKerns0 globalIdPD (oldKStructurePointer::klist) HkernList). simpl in HstartNotKerns0.
          auto.
      }
      destruct HlistOfKernss0 as (Hfirst & HlistOfKernss1 & HlistOfKernss0). subst p. simpl.
      assert(HmaxNbPreps0: maxNbPrepareIsMaxNbKernels s0) by (unfold consistency1 in *; intuition).
      specialize(HmaxNbPreps0 globalIdPD kernList HlistOfKernss0).
      destruct kernList as [ | firstEl kernList]; try(simpl; lia). simpl in HlistOfKernss0.
      destruct HlistOfKernss0 as [pdentryBis (HlookupGlobs0Bis & HbeqStructNull & Hfirst & HlistOfKernss0)].
      rewrite HlookupGlobs0 in HlookupGlobs0Bis. injection HlookupGlobs0Bis as HlookupGlobs0Bis. subst pdentryBis.
      assert(HstructIsKS: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
      specialize(HstructIsKS globalIdPD pdentry HlookupGlobs0 HbeqStructNull). subst firstEl.
      assert(HnextValids0: nextKernelIsValid s0) by (unfold consistency1 in *; intuition).
      assert(HlebLenMax: length kernList <= maxNbPrepare) by (simpl in HmaxNbPreps0; lia).
      pose proof (listOfKernIsInclInComplete (structure pdentry) kernList s0 HnextValids0 HstructIsKS HlistOfKernss0
        HlebLenMax) as Hres. destruct Hres as [postList HcompListEq].
      assert(Hres: length kernList < length (completeListOfKernels (structure pdentry) s0)).
      { rewrite HcompListEq. simpl. rewrite length_app. lia. }
      simpl. lia.
    - assert(HlistOfKernss0: isListOfKernels kernList partition s0).
      {
        rewrite Hs in HlistOfKerns. apply isListOfKernelsEqPDTNotInPart in HlistOfKerns; trivial.
        rewrite Hs5 in HlistOfKerns. apply isListOfKernelsEqPDTNotInPart in HlistOfKerns; trivial.
        rewrite Hs4 in HlistOfKerns. apply isListOfKernelsEqPDTNotInPart in HlistOfKerns; trivial.
        rewrite Hs3 in HlistOfKerns. apply isListOfKernelsEqBE in HlistOfKerns.
        rewrite Hs2 in HlistOfKerns. apply isListOfKernelsEqPDTNotInPart in HlistOfKerns; trivial.
        revert HlistOfKerns. rewrite Hs1. apply isListOfKernelsEqPADDR; trivial. apply HstartNotKerns0.
      }
      specialize(Hcons0 partition kernList HlistOfKernss0). assumption.
    (* END maxNbPrepareIsMaxNbKernels *)
  }

  assert(StructurePointerIsKS s).
  { (* BEGIN StructurePointerIsKS s *)
    assert(Hcons0: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart HbeqStructNull.
    rewrite Hs in HlookupPart. rewrite Hs5 in HlookupPart. rewrite Hs4 in HlookupPart. simpl in *.
    destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
    - injection HlookupPart as HlookupPart. subst pdentryPart. rewrite HnewPD. simpl. rewrite Hprev3. simpl.
      rewrite Hprev2. simpl. rewrite Hprev. simpl. unfold isKS. rewrite HlookupStartEqs. assumption.
    - rewrite beqAddrTrue in HlookupPart. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupPart. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentryPart HlookupPart HbeqStructNull). unfold isKS in *.
      rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
      destruct (beqAddr globalIdPD (structure pdentryPart)) eqn:HbeqGlobStruct.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobStruct. rewrite HbeqGlobStruct in *. rewrite HlookupGlobs0 in *.
        exfalso; congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr (structure pdentryPart)) eqn:HbeqLastStruct.
      + (*technically false, but works anyway*)
        rewrite <-DTL.beqAddrTrue in HbeqLastStruct. rewrite HbeqLastStruct in *. rewrite HnewBs3.
        simpl. rewrite HlookupLasts0 in *. assumption.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in HbeqGlobStruct. rewrite HbeqGlobStruct. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) (structure pdentryPart))
          eqn:HbeqNextStruct.
        {
          rewrite <-DTL.beqAddrTrue in HbeqNextStruct. rewrite HbeqNextStruct in *. rewrite HlookupNext in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END StructurePointerIsKS *)
  }

  assert(HblocksEqs: getConfigBlocks globalIdPD s = completeListOfKernels (structure newPDentry) s).
  {
    apply completeKernListIsConfig; trivial; unfold consistency1 in *; intuition.
  }
  assert(HblocksEqs0: getConfigBlocks globalIdPD s0 = completeListOfKernels (structure pdentry) s0).
  {
    apply completeKernListIsConfig; trivial; unfold consistency1 in *; intuition.
  }
  assert(HgetConfigGlobEq: getConfigBlocks globalIdPD s = requisitionedBlockStart::getConfigBlocks globalIdPD s0).
  {
    rewrite HblocksEqs. rewrite HblocksEqs0. rewrite HnewPD. simpl. rewrite Hprev3. simpl. rewrite Hprev2. simpl.
    assert(HmaxNbPreps: maxNbPrepareIsMaxNbKernels s) by (unfold consistency1 in *; intuition).
    assert(Hlist: isListOfKernels (completeListOfKernels (structure newPDentry) s) globalIdPD s).
    { apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition. }
    specialize(HmaxNbPreps globalIdPD (completeListOfKernels (structure newPDentry) s) Hlist). clear Hlist.
    rewrite Hprev. simpl. rewrite HnewPD in HmaxNbPreps. simpl in HmaxNbPreps. rewrite Hprev3 in HmaxNbPreps.
    simpl in HmaxNbPreps. rewrite Hprev2 in HmaxNbPreps. simpl in HmaxNbPreps. rewrite Hprev in HmaxNbPreps.
    simpl in HmaxNbPreps. unfold completeListOfKernels in *. rewrite HlookupStartEqs in *. unfold isKS in *.
    destruct (lookup requisitionedBlockStart (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite HstartIsKSs0 in *. unfold zero in *. rewrite indexEqRefl in *.
    f_equal. unfold pdentryStructurePointer in *. rewrite HlookupGlobs0 in *. rewrite <-Hstructs0.
    assert(Hstruct: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
    replace maxNbPrepare with (S (maxNbPrepare-1)) at 1; try(cbn; lia). cbn -[maxNbPrepare CIndex nullAddr].
    replace maxNbPrepare with (S (maxNbPrepare-1)) in HmaxNbPreps; try(cbn; lia).
    cbn -[maxNbPrepare CIndex nullAddr] in HmaxNbPreps.
    rewrite HlookupNexts in *. destruct (beqAddr oldKStructurePointer nullAddr) eqn:HbeqOldNull.
    - rewrite <-DTL.beqAddrTrue in HbeqOldNull. rewrite HbeqOldNull.
      assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
      destruct (lookup nullAddr (memory s0) beqAddr); trivial. destruct v; trivial. exfalso; congruence.
    - rewrite <-beqAddrFalse in *. rewrite Hstructs0 in *.
      specialize(Hstruct globalIdPD pdentry HlookupGlobs0 HbeqOldNull). rewrite <-Hstructs0 in *. unfold isKS in *.
      assert(HstructIsKS: isKS oldKStructurePointer s0) by assumption.
      destruct (lookup oldKStructurePointer (memory s0) beqAddr) eqn:HlookupOlds0; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite Hstruct. unfold zero. rewrite indexEqRefl. f_equal.
      assert(HcompletesEq: completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s
        = completeListOfKernelsAux maxNbPrepare oldKStructurePointer s).
      {
        cbn -[maxNbPrepare] in HmaxNbPreps. apply completeListOfKernelsAuxN; lia.
      }
      rewrite HcompletesEq.
      assert(Heqs1: completeListOfKernelsAux maxNbPrepare oldKStructurePointer s1
        = completeListOfKernelsAux maxNbPrepare oldKStructurePointer s0).
      {
        rewrite Hs1. apply completeListOfKernelsAuxEqPADDRNew; trivial.
        - unfold consistency1 in *; intuition.
        - apply HstartNotKerns0 with globalIdPD.
          replace (oldKStructurePointer :: completeListOfKernelsAux maxNbPrepare oldKStructurePointer s0) with
            (completeListOfKernels oldKStructurePointer s0).
          + rewrite Hstructs0. apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
          + unfold completeListOfKernels. rewrite HlookupOlds0. rewrite Hstruct. unfold zero. rewrite indexEqRefl.
            reflexivity.
      }
      assert(Heqs2: completeListOfKernelsAux maxNbPrepare oldKStructurePointer s2
        = completeListOfKernelsAux maxNbPrepare oldKStructurePointer s0).
      {
        rewrite <-Heqs1. rewrite Hs2. apply completeListOfKernelsAuxEqPDT. unfold isPADDR. rewrite HlookupGlobs1.
        intuition.
      }
      assert(Heqs3: completeListOfKernelsAux maxNbPrepare oldKStructurePointer s3
        = completeListOfKernelsAux maxNbPrepare oldKStructurePointer s0).
      {
        rewrite <-Heqs2. rewrite Hs3. apply completeListOfKernelsAuxEqBE. unfold isPADDR. rewrite HlookupLasts2.
        intuition.
      }
      assert(Heqs4: completeListOfKernelsAux maxNbPrepare oldKStructurePointer s4
        = completeListOfKernelsAux maxNbPrepare oldKStructurePointer s0).
      {
        rewrite <-Heqs3. rewrite Hs4. apply completeListOfKernelsAuxEqPDT. unfold isPADDR. rewrite HlookupGlobs3.
        intuition.
      }
      assert(Heqs5: completeListOfKernelsAux maxNbPrepare oldKStructurePointer s5
        = completeListOfKernelsAux maxNbPrepare oldKStructurePointer s0).
      {
        rewrite <-Heqs4. rewrite Hs5. apply completeListOfKernelsAuxEqPDT. unfold isPADDR. rewrite HlookupGlobs4.
        intuition.
      }
      rewrite <-Heqs5. rewrite Hs. apply completeListOfKernelsAuxEqPDT. unfold isPADDR. rewrite HlookupGlobs5.
      intuition.
  }

  assert(HgetConfigPPartial1GlobEqs: getAllPaddrPDTAux [globalIdPD] s = getAllPaddrPDTAux [globalIdPD] s0).
  {
    simpl. rewrite HlookupGlobs. rewrite HlookupGlobs0. reflexivity.
  }

  assert(HgetConfigPPartial2GlobEqs: getAllPaddrConfigAux (getConfigBlocks globalIdPD s) s
    = (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
        ++ getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s0).
  {
    rewrite HgetConfigGlobEq. simpl. unfold bentryBlockIndex in *.
    destruct (lookup requisitionedBlockStart (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). f_equal.
    assert(Heqs1: getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s1
      = getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s0).
    {
      rewrite Hs1. apply getAllPaddrConfigAuxEqPADDR. unfold isPADDR. rewrite HlookupNext. trivial.
    }
    assert(Heqs2: getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s2
      = getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s0).
    {
      rewrite <-Heqs1. rewrite Hs2. apply getAllPaddrConfigAuxEqPDT. unfold isPDT. rewrite HlookupGlobs1. trivial.
    }
    assert(Heqs3: getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s3
      = getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s0).
    {
      rewrite <-Heqs2. rewrite Hs3. apply getAllPaddrConfigAuxEqBE. unfold isBE. rewrite HlookupLasts2. trivial.
    }
    assert(Heqs4: getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s4
      = getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s0).
    {
      rewrite <-Heqs3. rewrite Hs4. apply getAllPaddrConfigAuxEqPDT. unfold isPDT. rewrite HlookupGlobs3. trivial.
    }
    assert(Heqs5: getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s5
      = getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s0).
    {
      rewrite <-Heqs4. rewrite Hs5. apply getAllPaddrConfigAuxEqPDT. unfold isPDT. rewrite HlookupGlobs4. trivial.
    }
    rewrite <-Heqs5. rewrite Hs. apply getAllPaddrConfigAuxEqPDT. unfold isPDT. rewrite HlookupGlobs5. trivial.
  }

  assert(HgetConfigPNotGlobEq: forall part, part <> globalIdPD -> isPDT part s0
    -> getConfigPaddr part s = getConfigPaddr part s0).
  {
    intros part HbeqParts HpartIsPDT. rewrite HgetConfigPaddrEqss2; trivial. rewrite <-HgetConfigPaddrEqs1; trivial.
    rewrite Hs2. apply getConfigPaddrEqPDTNotInPart with pdentry; trivial.
  }

  assert(consistency1 s).
  {

    assert(wellFormedFstShadowIfBlockEntry s).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
      intros block HblockIsBE. assert(HblockIsBEs2: isBE block s2).
      {
        unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs5 in HblockIsBE. rewrite Hs4 in HblockIsBE. simpl in *.
        destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence).
        rewrite beqAddrTrue in HblockIsBE. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HblockIsBE. simpl in *.
        destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
        - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. rewrite HlookupLasts2. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(HwellFormedSh1s2 block HblockIsBEs2). unfold isSHE in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
      destruct (beqAddr globalIdPD (CPaddr (block + sh1offset))) eqn:HbeqGlobSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobSh1. rewrite HbeqGlobSh1 in *. rewrite HlookupGlobs2 in *. congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr (CPaddr (block + sh1offset))) eqn:HbeqLastSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastSh1. rewrite HbeqLastSh1 in *. rewrite HlookupLasts2 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(PDTIfPDFlag s).
    { (* BEGIN PDTIfPDFlag s *)
      intros idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild. rewrite HgetPartsEq in *.
      assert(isPDT part s0).
      {
        apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
      }
      rewrite <-HgetPartsEqs1 in *. rewrite <-HgetPartsEqs2 in *. rewrite <-HgetPartsEqs3 in *.
      rewrite <-HgetPartsEqs4 in *. rewrite <-HgetPartsEqs5 in *. rewrite HgetMappedBEq in *; trivial.
      rewrite <-HgetMappedBEqs1 in HblockMapped; trivial. rewrite <-HgetMappedBEqs2s1 in *.
      rewrite <-HgetMappedBEqs3s2 in *. rewrite <-HgetMappedBEqs4s3 in *. rewrite <-HgetMappedBEqs5s4 in *.
      assert(HlookupBlockEq: lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s5) beqAddr).
      {
        destruct HcheckChild as (_ & Hsh1). unfold sh1entryAddr in Hsh1. rewrite Hs. rewrite Hs in Hsh1. simpl in *.
        destruct (beqAddr globalIdPD idPDchild) eqn:HbeqGlobBlock; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      assert(HcheckChilds5: true = checkChild idPDchild s5 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s5).
      {
        unfold checkChild in *. unfold sh1entryAddr in *. rewrite HlookupBlockEq in *.
        destruct HcheckChild as (HcheckChild & Hsh1). split; trivial.
        destruct (lookup idPDchild (memory s5) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite Hs in HcheckChild. simpl in HcheckChild.
        destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(HPDTIfPDFlags5 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChilds5).
      unfold bentryStartAddr in *.
      unfold bentryPFlag in *. unfold bentryAFlag in *. unfold entryPDT in *. rewrite HlookupBlockEq.
      destruct HPDTIfPDFlags5 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]). split; trivial.
      split; trivial. exists startaddr. split; trivial.
      destruct (lookup idPDchild (memory s5) beqAddr); try(congruence). destruct v; try(congruence). rewrite Hs.
      simpl. destruct (beqAddr globalIdPD (startAddr (blockrange b))) eqn:HbeqGlobStart.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobStart. rewrite HbeqGlobStart in *. rewrite HlookupGlobs5 in *.
        assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag s).
    { (* BEGIN AccessibleNoPDFlag s *)
      assert(Hcons0: AccessibleNoPDFlag s0) by (unfold consistency1 in *; intuition).
      intros block sh1entryaddr HblockIsBE Hsh1 HAflag. unfold sh1entryAddr in *. unfold bentryAFlag in *.
      unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs in Hsh1. rewrite Hs in HAflag. rewrite Hs5 in HblockIsBE.
      rewrite Hs5 in Hsh1. rewrite Hs5 in HAflag. rewrite Hs4 in HblockIsBE. rewrite Hs4 in HAflag.
      rewrite Hs4 in Hsh1. simpl in *.
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(Hblocks0: isBE block s0 /\ sh1entryAddr block sh1entryaddr s0 /\ bentryAFlag block true s0).
      {
        rewrite Hs3 in HblockIsBE. rewrite Hs3 in Hsh1. rewrite Hs3 in HAflag. simpl in *.
        destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
        - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. rewrite HnewBs3 in HAflag. unfold sh1entryAddr.
          unfold isBE. unfold bentryAFlag. rewrite HlookupLasts0. split; trivial. split; trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HblockIsBE. rewrite Hs2 in Hsh1. rewrite Hs2 in HAflag. simpl in *.
          rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HblockIsBE.
          rewrite Hs1 in Hsh1. rewrite Hs1 in HAflag. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. split; trivial. split; trivial.
      }
      destruct Hblocks0 as (HblockIsBEs0 & Hsh1s0 & HAflags0).
      specialize(Hcons0 block sh1entryaddr HblockIsBEs0 Hsh1s0 HAflags0). unfold sh1entryPDflag in *. rewrite Hs.
      rewrite Hs5. rewrite Hs4. simpl. destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobSh1. rewrite HbeqGlobSh1 in *. rewrite HlookupGlobs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr sh1entryaddr) eqn:HbeqLastSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastSh1. rewrite HbeqLastSh1 in *. rewrite HlookupLasts0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in HbeqGlobSh1. rewrite HbeqGlobSh1. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) sh1entryaddr) eqn:HbeqNextSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextSh1. rewrite HbeqNextSh1 in *. rewrite HlookupNext in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart HbeqFirstNull.
      rewrite Hs in HlookupPart. rewrite Hs5 in HlookupPart. rewrite Hs4 in HlookupPart. simpl in *.
      destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
      - injection HlookupPart as HlookupPart. subst pdentryPart. rewrite HnewPD. simpl. rewrite Hprev3. simpl.
        rewrite Hprev2. simpl. unfold isBE. unfold isFreeSlot. rewrite HlookupStartEqs.
        assert(HltZeroKernEntries: CIndex 0 < kernelStructureEntriesNb) by (apply CIndex0ltKSEntriesNb; reflexivity).
        specialize(HnewFree (CIndex 0) HltZeroKernEntries). unfold isFreeSlot in *.
        assert(HeqZero: CPaddr (requisitionedBlockStart + CIndex 0) = requisitionedBlockStart).
        {
          unfold CIndex. destruct (le_dec 0 maxIdx); try(lia). simpl. rewrite PeanoNat.Nat.add_0_r. unfold CPaddr.
          destruct (le_dec requisitionedBlockStart maxAddr); try(lia). apply paddrEqNatEqEquiv. reflexivity.
        }
        rewrite HeqZero in *. destruct (lookup requisitionedBlockStart (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). split; trivial.
        assert(HlookupSheEq: lookup (CPaddr (requisitionedBlockStart + sh1offset)) (memory s) beqAddr
          = lookup (CPaddr (requisitionedBlockStart + sh1offset)) (memory s0) beqAddr).
        {
          rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
          destruct (beqAddr globalIdPD (CPaddr (requisitionedBlockStart + sh1offset))) eqn:HbeqGlobSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqGlobSh1. rewrite HbeqGlobSh1 in *. rewrite HlookupGlobs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          destruct (beqAddr lastBlockEntryAddr (CPaddr (requisitionedBlockStart + sh1offset))) eqn:HbeqLastSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqLastSh1. rewrite HbeqLastSh1 in *. rewrite HlookupLasts0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite beqAddrFalse in HbeqGlobSh1. rewrite HbeqGlobSh1. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset))
            (CPaddr (requisitionedBlockStart + sh1offset))) eqn:HbeqNextSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqNextSh1. rewrite HbeqNextSh1 in *. rewrite HlookupNext in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupSheEq.
        destruct (lookup (CPaddr (requisitionedBlockStart+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite HlookupSceEq; unfold isSCE;
          destruct (lookup (CPaddr (requisitionedBlockStart + scoffset)) (memory s0) beqAddr);
          try(exfalso; congruence); destruct v; try(exfalso; congruence); trivial.
      - rewrite beqAddrTrue in HlookupPart. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart. simpl in *.
        destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs2 in HlookupPart. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HlookupPart. simpl in *.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 partition pdentryPart HlookupPart HbeqFirstNull). destruct Hcons0 as (HBE & Hfree).
        unfold isBE in *. unfold isFreeSlot in *.
        assert(HlookupFirstSh1Eq: lookup (CPaddr (firstfreeslot pdentryPart + sh1offset)) (memory s) beqAddr
          = lookup (CPaddr (firstfreeslot pdentryPart + sh1offset)) (memory s0) beqAddr).
        {
          destruct (lookup (firstfreeslot pdentryPart) (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
          destruct (beqAddr globalIdPD (CPaddr (firstfreeslot pdentryPart + sh1offset))) eqn:HbeqGlobSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqGlobSh1. rewrite HbeqGlobSh1 in *. rewrite HlookupGlobs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          destruct (beqAddr lastBlockEntryAddr (CPaddr (firstfreeslot pdentryPart + sh1offset))) eqn:HbeqLastSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqLastSh1. rewrite HbeqLastSh1 in *. rewrite HlookupLasts0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite beqAddrFalse in HbeqGlobSh1. rewrite HbeqGlobSh1. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset))
            (CPaddr (firstfreeslot pdentryPart+sh1offset))) eqn:HbeqNextSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqNextSh1. rewrite HbeqNextSh1 in *. rewrite HlookupNext in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        assert(HlookupFirstSceEq: lookup (CPaddr (firstfreeslot pdentryPart + scoffset)) (memory s) beqAddr
          = lookup (CPaddr (firstfreeslot pdentryPart + scoffset)) (memory s0) beqAddr).
        {
          destruct (lookup (firstfreeslot pdentryPart) (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          destruct (lookup (CPaddr (firstfreeslot pdentryPart + sh1offset)) (memory s0) beqAddr);
            try(exfalso; congruence). destruct v; try(exfalso; congruence). rewrite Hs. rewrite Hs5. rewrite Hs4.
          simpl. destruct (beqAddr globalIdPD (CPaddr (firstfreeslot pdentryPart + scoffset))) eqn:HbeqGlobSce.
          {
            rewrite <-DTL.beqAddrTrue in HbeqGlobSce. rewrite HbeqGlobSce in *. rewrite HlookupGlobs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          destruct (beqAddr lastBlockEntryAddr (CPaddr (firstfreeslot pdentryPart + scoffset))) eqn:HbeqLastSce.
          {
            rewrite <-DTL.beqAddrTrue in HbeqLastSce. rewrite HbeqLastSce in *. rewrite HlookupLasts0 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite beqAddrFalse in HbeqGlobSce. rewrite HbeqGlobSce. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset))
            (CPaddr (firstfreeslot pdentryPart+scoffset))) eqn:HbeqNextSce.
          {
            rewrite <-DTL.beqAddrTrue in HbeqNextSce. rewrite HbeqNextSce in *. rewrite HlookupNext in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupFirstSh1Eq. rewrite HlookupFirstSceEq. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
        destruct (beqAddr globalIdPD (firstfreeslot pdentryPart)) eqn:HbeqGlobFirst.
        {
          rewrite <-DTL.beqAddrTrue in HbeqGlobFirst. rewrite HbeqGlobFirst in *. rewrite HlookupGlobs0 in *.
          exfalso; congruence.
        }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr (firstfreeslot pdentryPart)) eqn:HbeqLastFirst.
        + (*technically false, but works anyway*)
          split; trivial. rewrite <-DTL.beqAddrTrue in HbeqLastFirst. rewrite HbeqLastFirst in *. rewrite HnewBs3.
          simpl. rewrite HlookupLasts0 in *. assumption.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite beqAddrFalse in HbeqGlobFirst. rewrite HbeqGlobFirst. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) (firstfreeslot pdentryPart))
            eqn:HbeqNextFirst.
          {
            rewrite <-DTL.beqAddrTrue in HbeqNextFirst. rewrite HbeqNextFirst in *. rewrite HlookupNext in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); try(split); trivial.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT s).
    { (* BEGIN multiplexerIsPDT s *)
      unfold multiplexerIsPDT. unfold isPDT in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
      destruct (beqAddr globalIdPD multiplexer) eqn:HbeqGlobMult; trivial. rewrite beqAddrTrue.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr multiplexer) eqn:HbeqLastMult.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastMult. rewrite HbeqLastMult in *. rewrite HlookupLasts2 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END multiplexerIsPDT *)
    }

    assert(currentPartitionInPartitionsList s).
    { (* BEGIN currentPartitionInPartitionsList s *)
      assert(Hcons0: currentPartitionInPartitionsList s0) by (unfold consistency1 in *; intuition).
      unfold currentPartitionInPartitionsList in *. rewrite HgetPartsEq. rewrite Hs. rewrite Hs5. rewrite Hs4.
      rewrite Hs3. rewrite Hs2. rewrite Hs1. simpl. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry s).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s0) by (unfold consistency1 in *; intuition).
      intros block HblockIsBE.
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs5 in HblockIsBE. rewrite Hs4 in HblockIsBE. simpl in *.
        destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HblockIsBE. simpl in *.
        destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
        - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. rewrite HlookupLasts0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HblockIsBE. simpl in *. rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HblockIsBE. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 block HblockIsBEs0). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr.
      split; trivial. unfold isSCE in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
      destruct (beqAddr globalIdPD scentryaddr) eqn:HbeqGlobSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobSce. rewrite HbeqGlobSce in *. rewrite HlookupGlobs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr scentryaddr) eqn:HbeqLastSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastSce. rewrite HbeqLastSce in *. rewrite HlookupLasts0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in HbeqGlobSce. rewrite HbeqGlobSce. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) scentryaddr) eqn:HbeqNextSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextSce. rewrite HbeqNextSce in *. rewrite HlookupNext in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE s).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
      intros kernel idx HkernIsKS HltIdxKernEntries. assert(HkernIsKSs2: isKS kernel s2).
      {
        unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs5 in HkernIsKS. rewrite Hs4 in HkernIsKS. simpl in *.
        destruct (beqAddr globalIdPD kernel) eqn:HbeqGlobKern; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite beqAddrTrue in HkernIsKS. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HkernIsKS. simpl in *.
        destruct (beqAddr lastBlockEntryAddr kernel) eqn:HbeqLastKern.
        - rewrite <-DTL.beqAddrTrue in HbeqLastKern. rewrite HbeqLastKern in *. rewrite HlookupLasts2.
          rewrite HnewBs3 in HkernIsKS. simpl in *. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(HblockRanges2 kernel idx HkernIsKSs2 HltIdxKernEntries). unfold isBE in *. rewrite Hs. rewrite Hs5.
      rewrite Hs4. simpl. destruct (beqAddr globalIdPD (CPaddr (kernel + idx))) eqn:HbeqGlobIdx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobIdx. rewrite HbeqGlobIdx in *. rewrite HlookupGlobs2 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr (CPaddr (kernel + idx))) eqn:HbeqLastIdx; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS s).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0) by (unfold consistency1 in *; intuition).
      intros block idx HblockIsBE Hidx.
      assert(Hblocks0: isBE block s0 /\ bentryBlockIndex block idx s0).
      {
        unfold isBE in *. unfold bentryBlockIndex in *. rewrite Hs in HblockIsBE. rewrite Hs in Hidx.
        rewrite Hs5 in HblockIsBE. rewrite Hs5 in Hidx. rewrite Hs4 in HblockIsBE. rewrite Hs4 in Hidx. simpl in *.
        destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HblockIsBE.
        rewrite Hs3 in Hidx. simpl in *. destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
        - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. rewrite HlookupLasts0. rewrite HnewBs3 in Hidx.
          simpl in *. split; trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HblockIsBE. rewrite Hs2 in Hidx. simpl in *. rewrite beqAddrFalse in HbeqGlobBlock.
          rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.  rewrite Hs1 in HblockIsBE.
          rewrite Hs1 in Hidx. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hblocks0 as (HblockIsBEs0 & Hidxs0). specialize(Hcons0 block idx HblockIsBEs0 Hidxs0).
      unfold isKS in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
      destruct (beqAddr globalIdPD (CPaddr (block - idx))) eqn:HbeqGlobKern.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobKern. rewrite HbeqGlobKern in *. rewrite HlookupGlobs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr (CPaddr (block - idx))) eqn:HbeqLastKern.
      - (*technically false, but still works*)
        rewrite <-DTL.beqAddrTrue in HbeqLastKern. rewrite HbeqLastKern in *. rewrite HlookupLasts0 in *.
        rewrite HnewBs3. simpl. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
        simpl. rewrite beqAddrFalse in HbeqGlobKern. rewrite HbeqGlobKern. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) (CPaddr (block - idx))) eqn:HbeqNextKern.
        {
          rewrite <-DTL.beqAddrTrue in HbeqNextKern. rewrite HbeqNextKern in *. rewrite HlookupNext in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(sh1InChildLocationIsBE s).
    { (* BEGIN sh1InChildLocationIsBE s *)
      assert(Hcons0: sh1InChildLocationIsBE s0) by (unfold consistency1 in *; intuition).
      intros sh1entryaddr sh1entry HlookupSh1 HbeqLocNull. rewrite Hs in HlookupSh1. rewrite Hs5 in HlookupSh1.
      rewrite Hs4 in HlookupSh1. simpl in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupSh1. simpl in *.
      destruct (beqAddr lastBlockEntryAddr sh1entryaddr) eqn:HbeqLastSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HlookupSh1. simpl in *. rewrite beqAddrFalse in HbeqGlobSh1. rewrite HbeqGlobSh1 in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HlookupSh1. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) sh1entryaddr) eqn:HbeqNextSh1;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqLocNull). unfold isBE in *. rewrite Hs. rewrite Hs5.
      rewrite Hs4. simpl. destruct (beqAddr globalIdPD (inChildLocation sh1entry)) eqn:HbeqGlobdLoc.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobdLoc. rewrite HbeqGlobdLoc in *. rewrite HlookupGlobs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr (inChildLocation sh1entry)) eqn:HbeqLastLoc.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastLoc. rewrite HbeqLastLoc in *. rewrite HlookupLasts0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in HbeqGlobdLoc. rewrite HbeqGlobdLoc. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) (inChildLocation sh1entry)) eqn:HbeqNextLoc.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextLoc. rewrite HbeqNextLoc in *. rewrite HlookupNext in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END sh1InChildLocationIsBE *)
    }

    assert(NextKSIsKS s).
    { (* BEGIN NextKSIsKS s *)
      assert(Hcons0: NextKSIsKS s0) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull.
      assert(Hkerns0: isKS kernel s0 /\ nextKSAddr kernel nextKSaddr s0).
      {
        unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr.
        rewrite Hs5 in HkernIsKS. rewrite Hs5 in HnextAddr. rewrite Hs4 in HkernIsKS. rewrite Hs4 in HnextAddr.
        simpl in *. destruct (beqAddr globalIdPD kernel) eqn:HbeqGlobBlock; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HkernIsKS.
        rewrite Hs3 in HnextAddr. simpl in *. destruct (beqAddr lastBlockEntryAddr kernel) eqn:HbeqLastBlock.
        - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst kernel. rewrite HlookupLasts0.
          rewrite HnewBs3 in HkernIsKS. simpl in *. split; trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HkernIsKS. rewrite Hs2 in HnextAddr. simpl in *. rewrite beqAddrFalse in HbeqGlobBlock.
          rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.  rewrite Hs1 in HkernIsKS.
          rewrite Hs1 in HnextAddr. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) kernel) eqn:HbeqNextBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hkerns0 as (HkernIsKSs0 & HnextAddrs0). unfold nextKSentry in *. rewrite Hs in HnextKSAddr.
      rewrite Hs5 in HnextKSAddr. rewrite Hs4 in HnextKSAddr. simpl in *.
      destruct (beqAddr globalIdPD nextKSaddr) eqn:HbeqGlobNext; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HnextKSAddr. simpl in *.
      destruct (beqAddr lastBlockEntryAddr nextKSaddr) eqn:HbeqLastNext; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HnextKSAddr. simpl in *. rewrite beqAddrFalse in HbeqGlobNext. rewrite HbeqGlobNext in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HnextKSAddr. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) nextKSaddr) eqn:HbeqNexts.
      - subst nextKS. assert(Hstruct: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
        unfold pdentryStructurePointer in *. rewrite HlookupGlobs0 in *. subst oldKStructurePointer.
        specialize(Hstruct globalIdPD pdentry HlookupGlobs0 HbeqNextNull). unfold isKS in *. rewrite Hs. rewrite Hs5.
        rewrite Hs4. simpl. destruct (beqAddr globalIdPD (structure pdentry)) eqn:HbeqGlobOld.
        {
          rewrite <-DTL.beqAddrTrue in HbeqGlobOld. rewrite HbeqGlobOld in *. rewrite HlookupGlobs0 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr (structure pdentry)) eqn:HbeqLastOld.
        + (*technically false, but still works*)
          rewrite <-DTL.beqAddrTrue in HbeqLastOld. rewrite HbeqLastOld in *. rewrite HlookupLasts0 in *.
          rewrite HnewBs3. simpl. assumption.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
          simpl. rewrite beqAddrFalse in HbeqGlobOld. rewrite HbeqGlobOld. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) (structure pdentry)) eqn:HbeqNextOld.
          {
            rewrite <-DTL.beqAddrTrue in HbeqNextOld. rewrite HbeqNextOld in *. rewrite HlookupNext in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKSs0 HnextAddrs0 HnextKSAddr HbeqNextNull).
        unfold isKS in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
        destruct (beqAddr globalIdPD nextKS) eqn:HbeqGlobKern.
        {
          rewrite <-DTL.beqAddrTrue in HbeqGlobKern. rewrite HbeqGlobKern in *. rewrite HlookupGlobs0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr nextKS) eqn:HbeqLastKern.
        + (*technically false, but still works*)
          rewrite <-DTL.beqAddrTrue in HbeqLastKern. rewrite HbeqLastKern in *. rewrite HlookupLasts0 in *.
          rewrite HnewBs3. simpl. assumption.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
          simpl. rewrite beqAddrFalse in HbeqGlobKern. rewrite HbeqGlobKern. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) nextKS) eqn:HbeqNextKern.
          {
            rewrite <-DTL.beqAddrTrue in HbeqNextKern. rewrite HbeqNextKern in *. rewrite HlookupNext in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR s).
    { (* BEGIN NextKSOffsetIsPADDR s *)
      assert(Hcons0: NextKSOffsetIsPADDR s0) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr HkernIsKS HnextAddr.
      assert(Hkerns0: isKS kernel s0 /\ nextKSAddr kernel nextKSaddr s0).
      {
        unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr.
        rewrite Hs5 in HkernIsKS. rewrite Hs5 in HnextAddr. rewrite Hs4 in HkernIsKS. rewrite Hs4 in HnextAddr.
        simpl in *. destruct (beqAddr globalIdPD kernel) eqn:HbeqGlobBlock; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HkernIsKS.
        rewrite Hs3 in HnextAddr. simpl in *. destruct (beqAddr lastBlockEntryAddr kernel) eqn:HbeqLastBlock.
        - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst kernel. rewrite HlookupLasts0.
          rewrite HnewBs3 in HkernIsKS. simpl in *. split; trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HkernIsKS. rewrite Hs2 in HnextAddr. simpl in *. rewrite beqAddrFalse in HbeqGlobBlock.
          rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.  rewrite Hs1 in HkernIsKS.
          rewrite Hs1 in HnextAddr. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) kernel) eqn:HbeqNextBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); try(split); trivial.
      }
      destruct Hkerns0 as (HkernIsKSs0 & HnextAddrs0). specialize(Hcons0 kernel nextKSaddr HkernIsKSs0 HnextAddrs0).
      destruct Hcons0 as (HnextIsPADDR & HbeqNextNull). split; trivial. unfold isPADDR in *. rewrite Hs.
      rewrite Hs5. rewrite Hs4. simpl. destruct (beqAddr globalIdPD nextKSaddr) eqn:HbeqGlobNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobNext. rewrite HbeqGlobNext in *. rewrite HlookupGlobs0 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr nextKSaddr) eqn:HbeqLastNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastNext. rewrite HbeqLastNext in *. rewrite HlookupLasts0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in HbeqGlobNext. rewrite HbeqGlobNext. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) nextKSaddr) eqn:HbeqNexts; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(HnewFreeListAux: forall kernIdx n, kernIdx < kernelStructureEntriesNb
      -> n > currentNbFreeSlots+kernIdx+1
      -> n <= maxIdx + 1
      -> getFreeSlotsListRec n (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1-kernIdx)) s
            (CIndex (currentNbFreeSlots+kernIdx+1))
          = (getFreeSlotsListRec (maxIdx + 1 - kernelStructureEntriesNb+1+kernIdx)
              (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1-kernIdx)) s0 (CIndex (kernIdx+1)))
            ++ getFreeSlotsList globalIdPD s0).
    {
      unfold getFreeSlotsList in *. rewrite HlookupGlobs0 in *.
      assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
      induction kernIdx; cbn -[kernelStructureEntriesNb nullAddr]; intros n HltIdxKernEntries HgtNNidx HlebNMax.
      - rewrite PeanoNat.Nat.sub_0_r. rewrite PeanoNat.Nat.add_0_r in *.
        assert(HpredN: n = S(n-1)) by lia. rewrite HpredN.
        replace (maxIdx+1-kernelStructureEntriesNb+1+0) with (S (maxIdx+1-kernelStructureEntriesNb)); try(lia).
        cbn -[kernelStructureEntriesNb nullAddr]. rewrite <-HlastBlock. rewrite HlookupLasts.
        assert(HendLasts0: bentryEndAddr lastBlockEntryAddr nullAddr s0) by (rewrite HlastBlock; assumption).
        unfold bentryEndAddr in *. rewrite HlookupLasts0 in *. rewrite <-HendLasts0.
        cbn -[kernelStructureEntriesNb nullAddr]. unfold pdentryFirstFreeSlot in *. unfold pdentryNbFreeSlots in *.
        rewrite HlookupGlobs2 in *. rewrite HlookupGlobs0 in *. rewrite <-HnbFrees0. rewrite Hprev in HfirstFrees2.
        simpl in HfirstFrees2. rewrite <-HfirstFrees2 in *. pose proof maxIdxNotZero.
        assert(HpredNbFree: StateLib.Index.pred (CIndex (currentNbFreeSlots + 1)) = Some currentNbFreeSlots).
        {
          rewrite PeanoNat.Nat.add_1_r. unfold CIndex. unfold CIndex in HkernEntries.
          destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). rewrite HkernEntries in HnewNbFree.
          simpl in HnewNbFree. assert(newNbFreeSlots <= maxIdx) by (apply IdxLtMaxIdx).
          destruct (le_dec (S currentNbFreeSlots) maxIdx); try(lia). unfold StateLib.Index.pred. simpl. f_equal.
          apply index_eq_i. simpl. lia.
        }
        rewrite HpredNbFree. assert(HpredOne: StateLib.Index.pred (CIndex 1) = Some (CIndex 0)).
        {
          cbn. unfold CIndex. destruct (le_dec 1 maxIdx); try(lia). unfold StateLib.Index.pred. simpl. f_equal.
          f_equal. apply proof_irrelevance.
        }
        rewrite HpredOne.
        assert(Hempty: getFreeSlotsListRec (maxIdx+1-kernelStructureEntriesNb) nullAddr s0 (CIndex 0) = []).
        {
          replace (maxIdx+1-kernelStructureEntriesNb) with (S(maxIdx-kernelStructureEntriesNb)); try(lia). simpl.
          destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). reflexivity.
        }
        rewrite Hempty. destruct (beqAddr currFirstFreeSlot nullAddr) eqn:HbeqFirstNull.
        + rewrite <-DTL.beqAddrTrue in HbeqFirstNull. rewrite HbeqFirstNull. simpl in HnbFreeIsLen.
          rewrite HnbFreeIsLen in *. assert(HemptyBis: getFreeSlotsListRec (n-1) nullAddr s currentNbFreeSlots = []).
          {
            assert(HpredNP: (n-1) = S (n-2)) by lia. rewrite HpredNP. simpl. unfold nullAddrExists in *.
            unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). reflexivity.
          }
          rewrite HemptyBis. reflexivity.
        + assert(HeqBound: getFreeSlotsListRec (n - 1) currFirstFreeSlot s currentNbFreeSlots
            = getFreeSlotsListRec (maxIdx + 1) currFirstFreeSlot s currentNbFreeSlots).
          { apply getFreeSlotsListRecNBound; lia. }
          rewrite HeqBound. assert(Heq: getFreeSlotsListRec (maxIdx + 1) currFirstFreeSlot s currentNbFreeSlots
            = getFreeSlotsListRec (maxIdx + 1) currFirstFreeSlot s0 currentNbFreeSlots).
          {
            assert(Hfirst: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold consistency1 in *; intuition).
            rewrite <-beqAddrFalse in *. rewrite HfirstFrees2 in *. rewrite HnbFrees0 in *.
            specialize(Hfirst globalIdPD pdentry HlookupGlobs0 HbeqFirstNull).
            destruct Hfirst as (HfirstIsBE & _). unfold isBE in *.
            assert(Heqs1: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s1 (nbfreeslots pdentry)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
            {
              rewrite Hs1. apply getFreeSlotsListRecEqPADDR.
              - unfold isPADDR. rewrite HlookupNext. trivial.
              - destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) (firstfreeslot pdentry))
                  eqn:HbeqNextFirst; trivial. exfalso. rewrite <-DTL.beqAddrTrue in HbeqNextFirst.
                rewrite HbeqNextFirst in *. rewrite HlookupNext in *. congruence.
            }
            destruct (beqAddr (firstfreeslot pdentry) globalIdPD) eqn:HbeqFirstGlob.
            {
              rewrite <-DTL.beqAddrTrue in HbeqFirstGlob. rewrite HbeqFirstGlob in *. rewrite HlookupGlobs0 in *.
              exfalso; congruence.
            }
            rewrite <-beqAddrFalse in *.
            assert(Heqs2: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s2 (nbfreeslots pdentry)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
            {
              rewrite <-Heqs1. rewrite Hs2. apply getFreeSlotsListRecEqPDT; trivial; unfold isBE; unfold isPADDR;
                rewrite HlookupGlobs1; intuition.
            }
            assert(HnoDupFree: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
            specialize(HnoDupFree globalIdPD pdentry HlookupGlobs0).
            destruct HnoDupFree as [optFreeList (HoptFree & HwellFormedFree & HnoDupFree)].
            unfold getFreeSlotsList in *. rewrite HlookupGlobs0 in *. rewrite beqAddrFalse in HbeqFirstNull.
            rewrite HbeqFirstNull in *. subst optFreeList.
            assert(HlastIsNew: In (SomePaddr lastBlockEntryAddr)
               (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))).
            {
              apply optionIsInFilter. apply HstartsBlocksAreNew with (kernelStructureEntriesNb-1). lia.
              rewrite PeanoNat.Nat.add_sub_assoc; try(lia). assumption.
            }
            specialize(HdisjointNew globalIdPD HglobIsPDTs0 (SomePaddr lastBlockEntryAddr) HlastIsNew).
            rewrite HlookupGlobs0 in *. rewrite HbeqFirstNull in *.
            assert(Heqs3: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s3 (nbfreeslots pdentry)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
            {
              rewrite <-Heqs2. rewrite Hs3. apply getFreeSlotsListRecEqBE; try(rewrite Heqs2); trivial.
              - rewrite MaxIdxNextEq in *. simpl in HdisjointNew. simpl in HwellFormedFree.
                destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr);
                  try(exfalso; simpl in HwellFormedFree; congruence).
                destruct v; try(exfalso; simpl in HwellFormedFree; congruence).
                destruct (StateLib.Index.pred (nbfreeslots pdentry));
                  try(exfalso; simpl in HwellFormedFree; congruence).
                simpl in HdisjointNew. apply Decidable.not_or in HdisjointNew. destruct HdisjointNew as (Hres & _).
                contradict Hres. f_equal. assumption.
              - unfold isBE. rewrite HlookupLasts2. trivial.
              - contradict HdisjointNew. apply optionIsInFilter; assumption.
            }
            assert(Heqs4: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s4 (nbfreeslots pdentry)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
            {
              rewrite <-Heqs3. rewrite Hs4. apply getFreeSlotsListRecEqPDT; unfold isBE; unfold isPADDR;
                try(rewrite HlookupGlobs3); trivial; intuition.
            }
            assert(Heqs5: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s5 (nbfreeslots pdentry)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
            {
              rewrite <-Heqs4. rewrite Hs5. apply getFreeSlotsListRecEqPDT; unfold isBE; unfold isPADDR;
                try(rewrite HlookupGlobs4); trivial; intuition.
            }
            rewrite <-Heqs5. rewrite Hs. apply getFreeSlotsListRecEqPDT; unfold isBE; unfold isPADDR;
              try(rewrite HlookupGlobs5); trivial; intuition.
          }
          rewrite Heq. intuition.
      - assert(HltIdxKernEntriesRec: kernIdx < kernelStructureEntriesNb) by lia.
        replace (maxIdx+1-kernelStructureEntriesNb+1+ S kernIdx)
          with (S(maxIdx+1-kernelStructureEntriesNb+1+kernIdx)); try(lia).
        assert(HpredN: n = S(n-1)) by lia. rewrite HpredN. cbn -[kernelStructureEntriesNb nullAddr].
        assert(HltIdxRevKernEntries: kernelStructureEntriesNb - 1 - S kernIdx < kernelStructureEntriesNb-1) by lia.
        assert(HidxRevEq: kernelStructureEntriesNb-1 -S kernIdx = CIndex (kernelStructureEntriesNb-1 -S kernIdx)).
        {
          unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1 - S kernIdx) maxIdx); try(lia). simpl.
          lia.
        }
        assert(HblockIdxEq: requisitionedBlockStart + kernelStructureEntriesNb - 1 - S kernIdx
          = requisitionedBlockStart + CIndex (kernelStructureEntriesNb - 1 - S kernIdx)).
        { rewrite <-HidxRevEq. lia. }
        rewrite HblockIdxEq. rewrite HidxRevEq in HltIdxRevKernEntries.
        assert(HendNewBis: bentryEndAddr (CPaddr (requisitionedBlockStart
            + CIndex (kernelStructureEntriesNb-1-S kernIdx)))
          (CPaddr (requisitionedBlockStart + CIndex (kernelStructureEntriesNb-1-kernIdx))) s0).
        {
          assert(Hlt: kernelStructureEntriesNb-1 - S kernIdx < kernelStructureEntriesNb-1) by lia.
          rewrite HidxRevEq in Hlt. specialize(HendNew (CIndex (kernelStructureEntriesNb-1-S kernIdx)) Hlt).
          assert(Heq: requisitionedBlockStart + CIndex (kernelStructureEntriesNb - 1 - S kernIdx) + 1
            = requisitionedBlockStart + CIndex (kernelStructureEntriesNb - 1 - kernIdx)).
          {
            unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1 - S kernIdx) maxIdx); try(lia).
            destruct (le_dec (kernelStructureEntriesNb - 1 - kernIdx) maxIdx); try(lia).
            cbn -[kernelStructureEntriesNb]. lia.
          }
          rewrite <-Heq. assumption.
        }
        unfold bentryEndAddr in *.
        assert(HlookupEq: lookup (CPaddr (requisitionedBlockStart+CIndex (kernelStructureEntriesNb-1-S kernIdx)))
          (memory s) beqAddr = lookup (CPaddr (requisitionedBlockStart+CIndex (kernelStructureEntriesNb-1-S kernIdx)))
          (memory s0) beqAddr).
        {
          rewrite Hs. rewrite Hs5. rewrite Hs4. cbn -[kernelStructureEntriesNb].
          destruct (beqAddr globalIdPD
            (CPaddr (requisitionedBlockStart+CIndex (kernelStructureEntriesNb-1-S kernIdx)))) eqn:HbeqGlobBlock.
          {
            rewrite <-DTL.beqAddrTrue in HbeqGlobBlock. rewrite HbeqGlobBlock in *. rewrite HlookupGlobs0 in *.
            exfalso; congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. cbn -[kernelStructureEntriesNb].
          destruct (beqAddr lastBlockEntryAddr
            (CPaddr (requisitionedBlockStart+CIndex (kernelStructureEntriesNb-1-S kernIdx)))) eqn:HbeqLastBlock.
          {
            rewrite <-DTL.beqAddrTrue in HbeqLastBlock. rewrite <-HidxRevEq in HbeqLastBlock. rewrite HlastBlock in *.
            unfold CPaddr in HbeqLastBlock.
            destruct (le_dec (requisitionedBlockStart + kernelStructureEntriesNb-1) maxAddr); try(cbn in *; lia).
            destruct (le_dec (requisitionedBlockStart + (kernelStructureEntriesNb-1- S kernIdx)) maxAddr);
              try(cbn in *; lia).
            assert(Hcontra: requisitionedBlockStart + kernelStructureEntriesNb-1
              = requisitionedBlockStart + (kernelStructureEntriesNb-1- S kernIdx)).
            { injection HbeqLastBlock as HbeqLastBlock. simpl. assumption. }
            lia.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2.
          cbn -[kernelStructureEntriesNb]. rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1.
          cbn -[kernelStructureEntriesNb]. destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset))
            (CPaddr (requisitionedBlockStart + CIndex (kernelStructureEntriesNb-1- S kernIdx)))) eqn:HbeqNextBlock.
          {
            rewrite <-DTL.beqAddrTrue in HbeqNextBlock. rewrite HbeqNextBlock in *. rewrite HlookupNext in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        rewrite HlookupEq.
        destruct (lookup (CPaddr (requisitionedBlockStart + CIndex (kernelStructureEntriesNb-1- S kernIdx)))
          (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        assert(HpredGlobIdx: StateLib.Index.pred (CIndex (currentNbFreeSlots + S kernIdx +1))
          = Some(CIndex (currentNbFreeSlots + kernIdx +1))).
        {
          unfold CIndex. destruct (le_dec (currentNbFreeSlots + S kernIdx + 1) maxIdx); try(lia).
          destruct (le_dec (currentNbFreeSlots + kernIdx + 1) maxIdx); try(lia). unfold StateLib.Index.pred. simpl.
          destruct (gt_dec (currentNbFreeSlots + S kernIdx + 1) 0); try(lia). f_equal. apply index_eq_i. simpl. lia.
        }
        assert(HpredIdx: StateLib.Index.pred (CIndex (S (kernIdx + 1))) = Some(CIndex (kernIdx + 1))).
        {
          unfold CIndex. destruct (le_dec (S (kernIdx + 1)) maxIdx); try(lia).
          destruct (le_dec (kernIdx + 1) maxIdx); try(lia). unfold StateLib.Index.pred. simpl. f_equal.
          apply index_eq_i. simpl. lia.
        }
        rewrite HpredGlobIdx. rewrite HpredIdx. rewrite <-app_comm_cons. f_equal. rewrite <-HendNewBis.
        assert(HidxBlockEq: requisitionedBlockStart + kernelStructureEntriesNb-1-kernIdx
          = requisitionedBlockStart + CIndex (kernelStructureEntriesNb-1-kernIdx)).
        {
          unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - 1 - kernIdx) maxIdx); try(lia).
          cbn -[kernelStructureEntriesNb]. lia.
        }
        rewrite <-HidxBlockEq. apply IHkernIdx; lia.
    }

    assert(HnewFreeList: getFreeSlotsList globalIdPD s
      = (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
          ++ getFreeSlotsList globalIdPD s0).
    {
      unfold getFreeSlotsList at 1. rewrite HlookupGlobs. rewrite HnewPD. simpl. rewrite Hprev3. simpl.
      rewrite Hprev2. simpl. destruct (beqAddr requisitionedBlockStart nullAddr) eqn:HbeqStartNull.
      {
        rewrite <-DTL.beqAddrTrue in HbeqStartNull. unfold isKS in *. rewrite HbeqStartNull in *.
        assert(isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *. exfalso.
        destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      assert(HstartEq: requisitionedBlockStart
        = CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1-(kernelStructureEntriesNb-1))).
      {
        replace (requisitionedBlockStart+kernelStructureEntriesNb-1-(kernelStructureEntriesNb-1))
          with (p requisitionedBlockStart); try(lia). unfold CPaddr.
        destruct (le_dec requisitionedBlockStart maxAddr); try(lia). apply paddrEqNatEqEquiv. reflexivity.
      }
      assert(HnewNbEq: newNbFreeSlots = CIndex (currentNbFreeSlots + (kernelStructureEntriesNb-1) + 1)).
      {
        subst kernelentriesnb. unfold CIndex in HnewNbFree.
        destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl in HnewNbFree.
        replace (currentNbFreeSlots + (kernelStructureEntriesNb - 1) + 1)
          with (currentNbFreeSlots + kernelStructureEntriesNb); try(lia). unfold CIndex.
        destruct (le_dec (currentNbFreeSlots + kernelStructureEntriesNb) maxIdx); try(lia). apply index_eq_i. simpl.
        assumption.
      }
      assert(HkernEntriesEq: CIndex kernelStructureEntriesNb = CIndex (kernelStructureEntriesNb-1+1)).
      { assert(Heq: kernelStructureEntriesNb = kernelStructureEntriesNb-1+1) by lia. rewrite <-Heq. reflexivity. }
      assert(HmaxEq: maxIdx + 1 = maxIdx + 1 - kernelStructureEntriesNb + 1 + (kernelStructureEntriesNb-1)) by lia.
      rewrite HstartEq. rewrite HnewNbEq. rewrite HkernEntriesEq. rewrite HmaxEq. apply HnewFreeListAux; try(lia).
      rewrite <-HmaxEq. subst kernelentriesnb. unfold CIndex in HnewNbFree.
      destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl in HnewNbFree. lia.
    }

    assert(wellFormedFreeSlotsList (getFreeSlotsList globalIdPD s) <> False).
    {
      rewrite HnewFreeList. apply wellFormedFreeSlotsListSplit; assumption.
    }

    assert(NoDupInFreeSlotsList s).
    { (* BEGIN NoDupInFreeSlotsList s *)
      assert(Hcons0: NoDupInFreeSlotsList s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart.
      assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)).
      {
        rewrite Hs in HlookupPart. rewrite Hs5 in HlookupPart. rewrite Hs4 in HlookupPart. simpl in *.
        destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
        - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. exists pdentry. assumption.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *. exists pdentryPart.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart. simpl in *.
          destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HlookupPart. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HlookupPart. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
            try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
         rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct HlookupParts0 as [pdentryParts0 HlookupParts0].
      specialize(Hcons0 partition pdentryParts0 HlookupParts0).
      destruct Hcons0 as [optFreeList (Hlist & HwellFormedList & HnoDupList)].
      destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. exists (getFreeSlotsList globalIdPD s).
        rewrite HnewFreeList. rewrite <-Hlist. split; trivial. split.
        + apply wellFormedFreeSlotsListSplit; assumption.
        + rewrite filterOptionPaddrSplit. apply <-Lib.NoDupSplitInclIff. split; try(split; trivial).
          * apply filterOptNoDup; assumption.
          * subst optFreeList. intros addr HaddrIsNew. apply optionIsInFilter in HaddrIsNew.
            specialize(HdisjointNew globalIdPD HglobIsPDTs0 (SomePaddr addr) HaddrIsNew). contradict HdisjointNew.
            apply optionIsInFilter; assumption.
      - exists optFreeList. rewrite HgetFreeSlotsListEq; auto.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot s).
    { (* BEGIN freeSlotsListIsFreeSlot s *)
      assert(Hcons0: freeSlotsListIsFreeSlot s0) by (unfold consistency1 in *; intuition).
      intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
      assert(HpartIsPDTs0: isPDT partition s0).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs5 in HpartIsPDT. rewrite Hs4 in HpartIsPDT. simpl in *.
        destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
        - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. assumption.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HpartIsPDT. simpl in *.
          destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HpartIsPDT. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
            try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
         rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition.
        assert(HwellFormeds0: getFreeSlotsList globalIdPD s0 = getFreeSlotsList globalIdPD s0 /\
          wellFormedFreeSlotsList (getFreeSlotsList globalIdPD s0) <> False) by auto.
        specialize(Hcons0 globalIdPD addr (getFreeSlotsList globalIdPD s0)
          (filterOptionPaddr (getFreeSlotsList globalIdPD s0)) HpartIsPDTs0 HwellFormeds0).
        destruct HwellFormed as (HoptFreeList & HwellFree). destruct HaddrInList as (HfreeList & HaddrInList).
        rewrite HnewFreeList in HoptFreeList. subst optionfreeslotslist. subst freeslotslist.
        rewrite filterOptionPaddrSplit in HaddrInList. apply in_app_or in HaddrInList.
        destruct HaddrInList as [HaddrIsNew | HaddrInLists0].
        + apply HnewAreStartsBlocks in HaddrIsNew. destruct HaddrIsNew as [blkIdx (Haddr & HltIdxKernEntries)].
          assert(HblkidxEq: blkIdx = CIndex blkIdx).
          { unfold CIndex. destruct (le_dec blkIdx maxIdx); try(lia). reflexivity. }
          rewrite HblkidxEq in HltIdxKernEntries. specialize(HnewFree (CIndex blkIdx) HltIdxKernEntries).
          rewrite <-HblkidxEq in HnewFree. subst addr. unfold isFreeSlot in *.
          destruct (lookup (CPaddr (requisitionedBlockStart + blkIdx)) (memory s0) beqAddr) eqn:HlookupBlock;
            try(exfalso; congruence). destruct v; try(exfalso; congruence).
          specialize(HblockFieldsEq (CPaddr (requisitionedBlockStart + blkIdx)) b HlookupBlock).
          destruct HblockFieldsEq as [bentrys (HlookupBlocks & HreadEq & HwriteEq & HexecEq & HpresEq & HaccEq &
            _ & HblkrngEq)]. rewrite HlookupBlocks. rewrite HreadEq. rewrite HwriteEq. rewrite HexecEq.
          rewrite HpresEq. rewrite HaccEq. rewrite HblkrngEq. rewrite HlookupSh1Eq; unfold isSHE;
            destruct (lookup (CPaddr (CPaddr (requisitionedBlockStart + blkIdx) + sh1offset)) (memory s0) beqAddr);
              try(exfalso; congruence); destruct v; try(exfalso; congruence); trivial.
          rewrite HlookupSceEq; unfold isSCE;
            destruct (lookup (CPaddr (CPaddr (requisitionedBlockStart + blkIdx) + scoffset)) (memory s0) beqAddr);
              try(exfalso; congruence); destruct v; try(exfalso; congruence); trivial.
        + assert(HaddrInLists0Bis: filterOptionPaddr (getFreeSlotsList globalIdPD s0)
              = filterOptionPaddr (getFreeSlotsList globalIdPD s0)
            /\ In addr (filterOptionPaddr (getFreeSlotsList globalIdPD s0))) by auto.
          specialize(Hcons0 HaddrInLists0Bis HbeqAddrNull). unfold isFreeSlot in *.
          destruct (lookup addr (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). specialize(HblockFieldsEq addr b HlookupBlock).
          destruct HblockFieldsEq as [bentrys (HlookupBlocks & HreadEq & HwriteEq & HexecEq & HpresEq & HaccEq &
            _ & HblkrngEq)]. rewrite HlookupBlocks. rewrite HreadEq. rewrite HwriteEq. rewrite HexecEq.
          rewrite HpresEq. rewrite HaccEq. rewrite HblkrngEq. rewrite HlookupSh1Eq; unfold isSHE;
            destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence);
            destruct v; try(exfalso; congruence); trivial.
          rewrite HlookupSceEq; unfold isSCE;
            destruct (lookup (CPaddr (addr + scoffset)) (memory s0) beqAddr); try(exfalso; congruence);
            destruct v; try(exfalso; congruence); trivial.
      - rewrite HgetFreeSlotsListEq in HwellFormed; trivial.
        specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDTs0 HwellFormed HaddrInList
          HbeqAddrNull). unfold isFreeSlot in *.
        destruct (lookup addr (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). specialize(HblockFieldsEq addr b HlookupBlock).
        destruct HblockFieldsEq as [bentrys (HlookupBlocks & HreadEq & HwriteEq & HexecEq & HpresEq & HaccEq &
          _ & HblkrngEq)]. rewrite HlookupBlocks. rewrite HreadEq. rewrite HwriteEq. rewrite HexecEq.
        rewrite HpresEq. rewrite HaccEq. rewrite HblkrngEq. rewrite HlookupSh1Eq; unfold isSHE;
          destruct (lookup (CPaddr (addr + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence);
          destruct v; try(exfalso; congruence); trivial.
        rewrite HlookupSceEq; unfold isSCE;
          destruct (lookup (CPaddr (addr + scoffset)) (memory s0) beqAddr); try(exfalso; congruence);
          destruct v; try(exfalso; congruence); trivial.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(DisjointFreeSlotsLists s).
    { (* BEGIN DisjointFreeSlotsLists s *)
      assert(Hcons0: DisjointFreeSlotsLists s0) by (unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
      assert(Hpart1IsPDTs0: isPDT part1 s0).
      {
        unfold isPDT in *. rewrite Hs in Hpart1IsPDT. rewrite Hs5 in Hpart1IsPDT. rewrite Hs4 in Hpart1IsPDT.
        simpl in *. destruct (beqAddr globalIdPD part1) eqn:HbeqGlobPart.
        - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst part1. assumption.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hpart1IsPDT. simpl in *.
          destruct (beqAddr lastBlockEntryAddr part1) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in Hpart1IsPDT. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in Hpart1IsPDT. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part1) eqn:HbeqNextPart;
            try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
         rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(Hpart2IsPDTs0: isPDT part2 s0).
      {
        unfold isPDT in *. rewrite Hs in Hpart2IsPDT. rewrite Hs5 in Hpart2IsPDT. rewrite Hs4 in Hpart2IsPDT.
        simpl in *. destruct (beqAddr globalIdPD part2) eqn:HbeqGlobPart.
        - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst part2. assumption.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hpart2IsPDT. simpl in *.
          destruct (beqAddr lastBlockEntryAddr part2) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in Hpart2IsPDT. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in Hpart2IsPDT. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part2) eqn:HbeqNextPart;
            try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
         rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts).
      destruct Hcons0 as [optFreeList1 [optFreeList2 (Hlist1 & Hwell1 & Hlist2 & Hwell2 & Hdisjoint)]].
      destruct (beqAddr globalIdPD part1) eqn:HbeqGlobPart1.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobPart1. subst part1. exists (getFreeSlotsList globalIdPD s).
        exists optFreeList2. split; trivial. split; try(split; try(split));
          try(rewrite HgetFreeSlotsListEq; try(rewrite <-beqAddrFalse); assumption); trivial.
        intros addr HaddrInFree. rewrite HnewFreeList in HaddrInFree. rewrite filterOptionPaddrSplit in HaddrInFree.
        apply in_app_or in HaddrInFree. destruct HaddrInFree as [HaddrIsNew | HaddrInFrees0].
        + apply optionIsInFilter in HaddrIsNew.
          specialize(HdisjointNew part2 Hpart2IsPDTs0 (SomePaddr addr) HaddrIsNew). contradict HdisjointNew.
          subst optFreeList2. apply optionIsInFilter; assumption.
        + subst optFreeList1. specialize(Hdisjoint addr HaddrInFrees0). assumption.
      - replace (getFreeSlotsList part1 s) with (getFreeSlotsList part1 s0);
          try(apply eq_sym; apply HgetFreeSlotsListEq; assumption). exists optFreeList1.
        destruct (beqAddr globalIdPD part2) eqn:HbeqGlobPart2.
        + rewrite <-DTL.beqAddrTrue in HbeqGlobPart2. subst part2. exists (getFreeSlotsList globalIdPD s).
          split; trivial. split; try(split; try(split));
            try(rewrite HgetFreeSlotsListEq; try(rewrite <-beqAddrFalse); assumption); trivial.
          intros addr HaddrInFree. specialize(Hdisjoint addr HaddrInFree). rewrite HnewFreeList. subst optFreeList1.
          rewrite filterOptionPaddrSplit. subst optFreeList2. apply Lib.in_or_app_neg. split; trivial.
          contradict Hdisjoint. apply optionIsInFilter. apply optionIsInFilter in Hdisjoint.
          specialize(HdisjointNew part1 Hpart1IsPDTs0 (SomePaddr addr) Hdisjoint).
          apply optionIsInFilter in HaddrInFree. exfalso; congruence.
        + rewrite HgetFreeSlotsListEq; trivial. exists optFreeList2. intuition.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries s).
    { (* BEGIN inclFreeSlotsBlockEntries s *)
      assert(Hcons0: inclFreeSlotsBlockEntries s0) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT.
      assert(HpartIsPDTs0: isPDT partition s0).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs5 in HpartIsPDT. rewrite Hs4 in HpartIsPDT. simpl in *.
        destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
        - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. assumption.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HpartIsPDT. simpl in *.
          destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HpartIsPDT. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HpartIsPDT. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
            try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
         rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition HpartIsPDTs0). destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HgetKSEqGlob. rewrite HnewFreeList.
        intros addr HaddrInFree. apply in_or_app. apply in_app_or in HaddrInFree.
        destruct HaddrInFree as [HaddrIsNew | HaddrInFrees0].
        + left. pose proof (wellFormedGivesSomePaddr addr
            (getFreeSlotsListRec (maxIdx + 1) requisitionedBlockStart s0 (CIndex kernelStructureEntriesNb))
            HwellFormedNew HaddrIsNew) as HaddrIsNewFilt.
          destruct HaddrIsNewFilt as [someAddr (Haddr & HaddrIsNewFilt)]. apply HnewAreStartsBlocks in HaddrIsNewFilt.
          destruct HaddrIsNewFilt as [kernIdx (HsomeAddr & HltIdxKernEntries)]. subst addr. apply optionIsInFilter.
          assert(HsomeAddrCopy: someAddr = CPaddr (requisitionedBlockStart + kernIdx)) by assumption.
          unfold CPaddr in HsomeAddr. destruct (le_dec (requisitionedBlockStart + kernIdx)); try(lia).
          apply blockInRangeInStructLight; try(rewrite <-HidxEq); auto; try(lia); try(rewrite HsomeAddr; simpl; lia).
          1,2,3: unfold consistency1 in *; intuition.
          * assert(HidxAddrEq: kernIdx = CIndex kernIdx).
            { unfold CIndex. destruct (le_dec kernIdx maxIdx); try(lia). reflexivity. }
            rewrite HidxAddrEq in HltIdxKernEntries. specialize(HnewFree (CIndex kernIdx) HltIdxKernEntries).
            unfold isFreeSlot in *. unfold isBE. rewrite <-HidxAddrEq in HnewFree. rewrite <-HsomeAddrCopy in *.
            destruct (lookup someAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence). trivial.
          * rewrite HsomeAddr. cbn -[kernelStructureEntriesNb]. lia.
        + right. apply Hcons0; assumption.
      - rewrite HgetFreeSlotsListEq; trivial. rewrite HgetKSEqNotGlob; trivial.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries s).
    { (* BEGIN DisjointKSEntries s *)
      assert(Hcons0: DisjointKSEntries s0) by (unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
      assert(Hpart1IsPDTs0: isPDT part1 s0).
      {
        unfold isPDT in *. rewrite Hs in Hpart1IsPDT. rewrite Hs5 in Hpart1IsPDT. rewrite Hs4 in Hpart1IsPDT.
        simpl in *. destruct (beqAddr globalIdPD part1) eqn:HbeqGlobPart.
        - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst part1. assumption.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hpart1IsPDT. simpl in *.
          destruct (beqAddr lastBlockEntryAddr part1) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in Hpart1IsPDT. simpl in *. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in Hpart1IsPDT. simpl in Hpart1IsPDT.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part1) eqn:HbeqNextPart;
            try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
         rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(Hpart2IsPDTs0: isPDT part2 s0).
      {
        unfold isPDT in *. rewrite Hs in Hpart2IsPDT. rewrite Hs5 in Hpart2IsPDT. rewrite Hs4 in Hpart2IsPDT.
        simpl in Hpart2IsPDT. destruct (beqAddr globalIdPD part2) eqn:HbeqGlobPart.
        - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst part2. assumption.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Hpart2IsPDT.
          simpl in Hpart2IsPDT.
          destruct (beqAddr lastBlockEntryAddr part2) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in Hpart2IsPDT. simpl in Hpart2IsPDT. rewrite beqAddrFalse in HbeqGlobPart.
          rewrite HbeqGlobPart in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in Hpart2IsPDT. simpl in Hpart2IsPDT.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part2) eqn:HbeqNextPart;
            try(exfalso; congruence).  rewrite <-beqAddrFalse in *.
         rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts).
      destruct Hcons0 as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      destruct (beqAddr globalIdPD part1) eqn:HbeqParts1.
      - rewrite <-DTL.beqAddrTrue in HbeqParts1. subst part1. rewrite beqAddrFalse in HbeqParts.
        exists (getKSEntries globalIdPD s). exists (getKSEntries part2 s). split; trivial. split; trivial.
        rewrite HgetKSEqGlob. rewrite HgetKSEqNotGlob; trivial. intros addr HaddrIn.
        rewrite filterOptionPaddrSplit in HaddrIn. apply in_app_or in HaddrIn.
        destruct HaddrIn as [HaddrIsNew | HaddrIns0].
        + assert(CIndex (kernelStructureEntriesNb - 1) < maxIdx + 1).
          { rewrite <-HidxEq. lia. }
          apply HnewStructAreNotEntries with addr part2 in HaddrIsNew; trivial.
        + specialize(Hdisjoint addr HaddrIns0). assumption.
      - assert(HgetKSEq1: getKSEntries part1 s = getKSEntries part1 s0).
        { apply HgetKSEqNotGlob; trivial. }
        rewrite HgetKSEq1. exists (getKSEntries part1 s0). exists (getKSEntries part2 s).
        destruct (beqAddr globalIdPD part2) eqn:HbeqGlobPart2.
        + rewrite <-DTL.beqAddrTrue in HbeqGlobPart2. subst part2. split; trivial. split; trivial.
          intros addr HaddrIn. rewrite HgetKSEqGlob. rewrite filterOptionPaddrSplit. apply Lib.in_or_app_neg.
          split; try(apply Hdisjoint; trivial). intro Hcontra.
          apply HnewStructAreNotEntries with addr part1 in Hcontra; trivial. congruence.
        + rewrite HgetKSEqNotGlob; trivial. auto.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree s).
    { (* BEGIN noDupPartitionTree s *)
      assert(Hcons0: noDupPartitionTree s0) by (unfold consistency1 in *; intuition). unfold noDupPartitionTree.
      rewrite HgetPartsEq. assumption.
      (* END noDupPartitionTree *)
    }

    assert(isParent s).
    { (* BEGIN isParent s *)
      assert(Hcons0: isParent s0) by (unfold consistency1 in *; intuition).
      intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEq in *.
      assert(HparentIsPDT: isPDT pdparent s0) by (apply partitionsArePDT; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in HpartIsChild; trivial.
      specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent in *. rewrite Hs.
      rewrite Hs5. rewrite Hs4. simpl. destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupGlobs0 in *. rewrite Hcons0.
        rewrite HnewPD. simpl. rewrite Hprev3. simpl. rewrite Hprev2. simpl. rewrite Hprev. reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart.
        { rewrite <-DTL.beqAddrTrue in HbeqLastPart. subst partition. rewrite HlookupLasts0 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in HbeqParts. rewrite HbeqParts. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart.
        { rewrite <-DTL.beqAddrTrue in HbeqNextPart. subst partition. rewrite HlookupNext in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END isParent *)
    }

    assert(isChild s).
    { (* BEGIN isChild s *)
      assert(Hcons0: isChild s0) by (unfold consistency1 in *; intuition).
      intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEq in *.
      assert(HparentIsParents0: pdentryParent partition pdparent s0).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. rewrite Hs5 in HparentIsParent.
        rewrite Hs4 in HparentIsParent. simpl in HparentIsParent.
        destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupGlobs0. rewrite HparentIsParent.
          rewrite HnewPD. simpl. rewrite Hprev3. simpl. rewrite Hprev2. simpl. rewrite Hprev. reflexivity.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HparentIsParent.
          simpl in HparentIsParent.
          destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HparentIsParent. simpl in HparentIsParent. rewrite beqAddrFalse in HbeqParts.
          rewrite HbeqParts in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HparentIsParent. simpl in HparentIsParent.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParents0 HbeqPartRoot).
      rewrite HgetChildrenEq; trivial.
      assert(HparentOfPart: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
      unfold pdentryParent in *. destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart;
        try(exfalso; congruence). destruct v; try(exfalso; congruence). rewrite HparentIsParents0.
      specialize(HparentOfPart partition p HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
      specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as ([parentEntry HlookupParent] & _).
      unfold isPDT. rewrite HlookupParent. trivial.
      (* END isChild *)
    }

    assert(noDupKSEntriesList s).
    { (* BEGIN noDupKSEntriesList s *)
      assert(Hcons0: noDupKSEntriesList s0) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. apply HstablePDT in HpartIsPDT. specialize(Hcons0 partition HpartIsPDT).
      destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HgetKSEqGlob. rewrite filterOptionPaddrSplit.
        apply Lib.NoDupSplitInclIff. split; try(split); trivial.
        + assert(HBE: forall kernIdx:index, kernIdx <= CIndex (kernelStructureEntriesNb - 1)
            -> isBE (CPaddr (requisitionedBlockStart + kernIdx)) s0).
          {
            intros kernIdx HlebIdxKernEntries. assert(HltIdxKernEntries: kernIdx < kernelStructureEntriesNb) by lia.
            specialize(HnewFree kernIdx HltIdxKernEntries). unfold isBE. unfold isFreeSlot in *.
            destruct (lookup (CPaddr (requisitionedBlockStart + kernIdx)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). trivial.
          }
          assert(HgtMaxKernEntries: maxIdx+1 > CIndex (kernelStructureEntriesNb-1)).
          { pose proof KSEntriesNbLessThanMaxIdx. lia. }
          assert(HltMax: requisitionedBlockStart+ CIndex (kernelStructureEntriesNb-1) < maxAddr-1) by (cbn in *; lia).
          pose proof (getKSEntriesInStructAuxIsRange (maxIdx+1) requisitionedBlockStart s0
            (CIndex (kernelStructureEntriesNb-1)) HBE HgtMaxKernEntries HltMax) as Heq. rewrite Heq. apply NoDup_rev.
          apply NoDupPaddrBlock.
        + intros addr HaddrIn. apply HnewStructAreNotEntries; trivial.
      - rewrite HgetKSEqNotGlob; trivial.
      (* END noDupKSEntriesList *)
    }

    assert(noDupMappedBlocksList s).
    { (* BEGIN noDupMappedBlocksList s *)
      assert(Hcons0: noDupMappedBlocksList s0) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. apply HstablePDT in HpartIsPDT. specialize(Hcons0 partition HpartIsPDT).
      rewrite HgetMappedBEq; trivial.
      (* END noDupMappedBlocksList *)
    }

    assert(wellFormedBlock s).
    { (* BEGIN wellFormedBlock s *)
      assert(Hcons0: wellFormedBlock s0) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr HPflag HstartBlock HendBlock. unfold bentryStartAddr in *.
      unfold bentryPFlag in *. unfold bentryEndAddr in *. rewrite Hs in HPflag. rewrite Hs in HstartBlock.
      rewrite Hs in HendBlock. rewrite Hs5 in HPflag. rewrite Hs5 in HstartBlock. rewrite Hs5 in HendBlock.
      rewrite Hs4 in HPflag. rewrite Hs4 in HstartBlock. rewrite Hs4 in HendBlock. simpl in *.
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPflag.
      rewrite Hs3 in HstartBlock. rewrite Hs3 in HendBlock. simpl in *.
      destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqBlocks.
      {
        rewrite HnewBs3 in HPflag. simpl in HPflag.
        assert(HltKernEntries: CIndex (kernelStructureEntriesNb-1) < kernelStructureEntriesNb) by (cbn; lia).
        specialize(HnewFree (CIndex (kernelStructureEntriesNb-1)) HltKernEntries).
        replace (requisitionedBlockStart + (CIndex (kernelStructureEntriesNb-1)))
          with (requisitionedBlockStart+kernelStructureEntriesNb-1) in HnewFree; try(cbn; lia).
        rewrite <-HlastBlock in *. unfold isFreeSlot in *. rewrite HlookupLasts0 in *. exfalso.
        destruct (lookup (CPaddr (lastBlockEntryAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HPflag. rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. simpl in *.
      rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HPflag. rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
      (* END wellFormedBlock *)
    }

    assert(HparentOfParts1: parentOfPartitionIsPartition s1).
    {
      assert(Hcons0: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart. rewrite HgetPartsEqs1. rewrite Hs1 in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentryPart HlookupPart). destruct Hcons0 as (HparentIsPart & HparentOfPart).
      split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) (parent pdentryPart)) eqn:HbeqNextParent.
      { rewrite <-DTL.beqAddrTrue in HbeqNextParent. rewrite HbeqNextParent in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. exists parentEntry.
      assumption.
    }

    assert(HparentOfParts2: parentOfPartitionIsPartition s2).
    {
      intros partition pdentryPart HlookupPart. rewrite HgetPartsEqs2. rewrite Hs2 in HlookupPart. simpl in *.
      destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HlookupPart.
        subst pdentryPart. rewrite Hprev. simpl. specialize(HparentOfParts1 globalIdPD pdentry HlookupGlobs1).
        destruct HparentOfParts1 as (HparentIsPart & HparentOfPart). split; trivial. intro HbeqGlobRoot.
        specialize(HparentIsPart HbeqGlobRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
        apply isPDTLookupEq. unfold isPDT. rewrite Hs2. simpl.
        destruct HparentOfPart as (_ & HbeqParentGlob). rewrite beqAddrFalse in HbeqParentGlob.
        rewrite beqAddrSym in HbeqParentGlob. rewrite HbeqParentGlob. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(HparentOfParts1 partition pdentryPart HlookupPart).
        destruct HparentOfParts1 as (HparentIsPart & HparentOfPart). split; trivial. intro HbeqPartRoot.
        specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
        apply isPDTLookupEq. unfold isPDT. rewrite Hs2. simpl.
        destruct (beqAddr globalIdPD (parent pdentryPart)) eqn:HbeqGlobParent; trivial. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent. trivial.
    }

    assert(HparentOfParts3: parentOfPartitionIsPartition s3).
    {
      intros partition pdentryPart HlookupPart. rewrite HgetPartsEqs3.
      rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(HparentOfParts2 partition pdentryPart HlookupPart).
      destruct HparentOfParts2 as (HparentIsPart & HparentOfPart). split; trivial. intro HbeqPartRoot.
      specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
      apply isPDTLookupEq. unfold isPDT. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr (parent pdentryPart)) eqn:HbeqLastParent.
      { rewrite <-DTL.beqAddrTrue in HbeqLastParent. rewrite HbeqLastParent in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent.
      trivial.
    }

    assert(HparentOfParts4: parentOfPartitionIsPartition s4).
    {
      intros partition pdentryPart HlookupPart. rewrite HgetPartsEqs4. rewrite Hs4 in HlookupPart. simpl in *.
      destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HlookupPart.
        subst pdentryPart. rewrite Hprev2. simpl.
        specialize(HparentOfParts3 globalIdPD prevPDentry HlookupGlobs3).
        destruct HparentOfParts3 as (HparentIsPart & HparentOfPart).
        split; trivial. intro HbeqGlobRoot. specialize(HparentIsPart HbeqGlobRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
        apply isPDTLookupEq. unfold isPDT. rewrite Hs4. simpl. destruct HparentOfPart as (_ & HbeqParentGlob).
        rewrite beqAddrFalse in HbeqParentGlob. rewrite beqAddrSym in HbeqParentGlob. rewrite HbeqParentGlob.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent.
        trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(HparentOfParts3 partition pdentryPart HlookupPart).
        destruct HparentOfParts3 as (HparentIsPart & HparentOfPart).
        split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
        apply isPDTLookupEq. unfold isPDT. rewrite Hs4. simpl.
        destruct (beqAddr globalIdPD (parent pdentryPart)) eqn:HbeqGlobParent; trivial.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent.
        trivial.
    }

    assert(HparentOfParts5: parentOfPartitionIsPartition s5).
    {
      intros partition pdentryPart HlookupPart. rewrite HgetPartsEqs5. rewrite Hs5 in HlookupPart. simpl in *.
      destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HlookupPart.
        subst pdentryPart. rewrite Hprev3. simpl.
        specialize(HparentOfParts4 globalIdPD prevPDentry2 HlookupGlobs4).
        destruct HparentOfParts4 as (HparentIsPart & HparentOfPart).
        split; trivial. intro HbeqGlobRoot. specialize(HparentIsPart HbeqGlobRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
        apply isPDTLookupEq. unfold isPDT. rewrite Hs5. simpl. destruct HparentOfPart as (_ & HbeqParentGlob).
        rewrite beqAddrFalse in HbeqParentGlob. rewrite beqAddrSym in HbeqParentGlob. rewrite HbeqParentGlob.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent.
        trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(HparentOfParts4 partition pdentryPart HlookupPart).
        destruct HparentOfParts4 as (HparentIsPart & HparentOfPart).
        split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
        apply isPDTLookupEq. unfold isPDT. rewrite Hs5. simpl.
        destruct (beqAddr globalIdPD (parent pdentryPart)) eqn:HbeqGlobParent; trivial.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent.
        trivial.
    }

    assert(parentOfPartitionIsPartition s).
    { (* BEGIN parentOfPartitionIsPartition s *)
      assert(Hcons0: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart. rewrite HgetPartsEq. rewrite <-HgetPartsEqs1.
      rewrite <-HgetPartsEqs2. rewrite <-HgetPartsEqs3. rewrite <-HgetPartsEqs4. rewrite <-HgetPartsEqs5.
      rewrite Hs in HlookupPart. simpl in *. destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HlookupPart.
        subst pdentryPart. rewrite HnewPD. simpl. specialize(HparentOfParts5 globalIdPD prevPDentry3 HlookupGlobs5).
        destruct HparentOfParts5 as (HparentIsPart & HparentOfPart).
        split; trivial. intro HbeqGlobRoot. specialize(HparentIsPart HbeqGlobRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
        apply isPDTLookupEq. unfold isPDT. rewrite Hs. simpl.
        destruct HparentOfPart as (_ & HbeqParentGlob). rewrite beqAddrFalse in HbeqParentGlob.
        rewrite beqAddrSym in HbeqParentGlob. rewrite HbeqParentGlob.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent.
        trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(HparentOfParts5 partition pdentryPart HlookupPart).
        destruct HparentOfParts5 as (HparentIsPart & HparentOfPart).
        split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial.
        apply isPDTLookupEq. unfold isPDT. rewrite Hs. simpl.
        destruct (beqAddr globalIdPD (parent pdentryPart)) eqn:HbeqGlobParent; trivial.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite HlookupParent.
        trivial.
      (* END parentOfPartitionIsPartition *)
    }

    assert(HlenFree: forall n (kernIdx:index), n > kernelStructureEntriesNb-kernIdx
      -> kernIdx < kernelStructureEntriesNb
      -> length (getFreeSlotsListRec n (CPaddr (requisitionedBlockStart+kernIdx)) s0
          (CIndex (kernelStructureEntriesNb-kernIdx))) = kernelStructureEntriesNb-kernIdx).
    {
      induction n; cbn -[kernelStructureEntriesNb nullAddr]; intros kernIdx HgtNIdx HltIdxKernEntries; try(lia).
      unfold bentryEndAddr in *. destruct (Nat.eqb kernIdx (kernelStructureEntriesNb-1)) eqn:HbeqIdxKernEntries.
      - apply PeanoNat.Nat.eqb_eq in HbeqIdxKernEntries. replace (requisitionedBlockStart + kernIdx) with
          (requisitionedBlockStart+kernelStructureEntriesNb-1); try(lia).
        destruct (lookup (CPaddr (requisitionedBlockStart+kernelStructureEntriesNb-1)) (memory s0) beqAddr);
          try(exfalso; congruence). destruct v; try(exfalso; congruence).
        replace (kernelStructureEntriesNb - kernIdx) with 1; try(lia). unfold StateLib.Index.pred.
        unfold CIndex; pose proof maxIdxNotZero; destruct (le_dec 1 maxIdx); simpl; try(lia). rewrite <-HendLast.
        replace n with (S (n-1)); try(lia). simpl.
        assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
        destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). simpl. lia.
      - apply PeanoNat.Nat.eqb_neq in HbeqIdxKernEntries.
        assert(HltIdxKernEntriesMin: kernIdx < kernelStructureEntriesNb-1) by lia.
        specialize(HendNew kernIdx HltIdxKernEntriesMin).
        destruct (lookup (CPaddr (requisitionedBlockStart + kernIdx)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). unfold StateLib.Index.pred.
        unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - kernIdx) maxIdx); try(lia).
        cbn -[kernelStructureEntriesNb]. destruct (gt_dec (kernelStructureEntriesNb - kernIdx) 0); try(lia).
        rewrite <-HendNew. cbn -[kernelStructureEntriesNb].
        assert(HidxPlusEq:  kernIdx + 1 = CIndex (kernIdx + 1)).
        { unfold CIndex. destruct (le_dec (kernIdx + 1) maxIdx); try(lia). reflexivity. }
        assert(HgtNIdxRec: n > kernelStructureEntriesNb - CIndex (kernIdx+1)) by lia.
        assert(HltIdxKernEntriesRec: CIndex (kernIdx+1) < kernelStructureEntriesNb) by lia.
        specialize(IHn (CIndex (kernIdx+1)) HgtNIdxRec HltIdxKernEntriesRec). rewrite <-HidxPlusEq in IHn.
        replace (requisitionedBlockStart+(kernIdx+1)) with (requisitionedBlockStart+kernIdx+1) in IHn; try(lia).
        assert(HidxMinEq: {|
                            i := kernelStructureEntriesNb - kernIdx - 1;
                            Hi :=
                              StateLib.Index.pred_obligation_1
                                {|
                                  i := kernelStructureEntriesNb - kernIdx;
                                  Hi := ADT.CIndex_obligation_1 (kernelStructureEntriesNb - kernIdx) l0
                                |} g
                          |} = CIndex (kernelStructureEntriesNb - (kernIdx + 1))).
        {
          unfold CIndex. destruct (le_dec (kernelStructureEntriesNb - (kernIdx + 1)) maxIdx); try(lia).
          apply index_eq_i. cbn -[kernelStructureEntriesNb]. lia.
        }
        rewrite HidxMinEq. rewrite IHn. lia.
    }

    assert(NbFreeSlotsISNbFreeSlotsInList s).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0) by (unfold consistency1 in *; intuition).
      intros partition nbfreeslots HpartIsPDT HnbFree. apply HstablePDT in HpartIsPDT. unfold pdentryNbFreeSlots in *.
      rewrite Hs in HnbFree. rewrite Hs5 in HnbFree. rewrite Hs4 in HnbFree. simpl in HnbFree.
      destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. rewrite HnewPD in HnbFree. simpl in HnbFree.
        rewrite Hprev3 in HnbFree. simpl in HnbFree. subst nbfreeslots.
        specialize(Hcons0 globalIdPD currentNbFreeSlots HpartIsPDT HnbFrees0). rewrite HnewFreeList.
        destruct Hcons0 as [optFreeList (Hlist & HwellFormedList & Hlen)]. exists (getFreeSlotsList globalIdPD s).
        split; trivial. split; trivial. rewrite HnewFreeList. rewrite length_app. rewrite <-HnbFreeIsLen.
        subst kernelentriesnb. assert(HidxKernEntries: kernelStructureEntriesNb = CIndex kernelStructureEntriesNb).
        { unfold CIndex. destruct (le_dec kernelStructureEntriesNb maxIdx); try(lia). reflexivity. }
        rewrite <-HidxKernEntries in HnewNbFree.
        assert(HgtMaxKernEntries: maxIdx+1 > kernelStructureEntriesNb - (CIndex 0)).
        { cbn -[kernelStructureEntriesNb]. lia. }
        assert(HltZeroKernEntries: CIndex 0 < kernelStructureEntriesNb) by (cbn -[kernelStructureEntriesNb]; lia).
        specialize(HlenFree (maxIdx+1) (CIndex 0) HgtMaxKernEntries HltZeroKernEntries).
        replace (CPaddr (requisitionedBlockStart + CIndex 0)) with requisitionedBlockStart in HlenFree;
          try(cbn; rewrite PeanoNat.Nat.add_0_r; rewrite paddrEqId; reflexivity).
        cbn -[kernelStructureEntriesNb] in HlenFree. rewrite PeanoNat.Nat.sub_0_r in HlenFree. rewrite HlenFree.
        lia.
      - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HnbFree. simpl in HnbFree.
        destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs2 in HnbFree. simpl in HnbFree. rewrite beqAddrFalse in HbeqGlobPart. rewrite HbeqGlobPart in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HnbFree. simpl in HnbFree.
        destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) partition) eqn:HbeqNextPart;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree). rewrite beqAddrFalse in HbeqGlobPart.
        rewrite HgetFreeSlotsListEq; trivial.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(blockInChildHasAtLeastEquivalentBlockInParent s).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0)
        by (unfold consistency1 in *; intuition). intros pdparent child block startChild endChild
        HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild. rewrite HgetPartsEq in *.
      assert(isPDT pdparent s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetMappedBEq; trivial.
      assert(isPDT child s0) by (apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition).
      rewrite HgetMappedBEq in HblockMappedChild; trivial. unfold bentryStartAddr in *.
      unfold bentryPFlag in *. unfold bentryEndAddr in *. rewrite Hs in HPflagChild. rewrite Hs in HstartChild.
      rewrite Hs in HendChild. rewrite Hs5 in HPflagChild. rewrite Hs5 in HstartChild. rewrite Hs5 in HendChild.
      rewrite Hs4 in HPflagChild. rewrite Hs4 in HstartChild. rewrite Hs4 in HendChild. simpl in *.
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPflagChild.
      rewrite Hs3 in HstartChild. rewrite Hs3 in HendChild. simpl in *.
      destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqBlocks.
      {
        rewrite HnewBs3 in HPflagChild. simpl in HPflagChild.
        assert(HltKernEntries: CIndex (kernelStructureEntriesNb-1) < kernelStructureEntriesNb) by (cbn; lia).
        specialize(HnewFree (CIndex (kernelStructureEntriesNb-1)) HltKernEntries).
        replace (requisitionedBlockStart + (CIndex (kernelStructureEntriesNb-1)))
          with (requisitionedBlockStart+kernelStructureEntriesNb-1) in HnewFree; try(cbn; lia).
        rewrite <-HlastBlock in *. unfold isFreeSlot in *. rewrite HlookupLasts0 in *. exfalso.
        destruct (lookup (CPaddr (lastBlockEntryAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HPflagChild. rewrite Hs2 in HstartChild. rewrite Hs2 in HendChild. simpl in *.
      rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs1 in HPflagChild. rewrite Hs1 in HstartChild. rewrite Hs1 in HendChild. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        HstartChild HendChild HPflagChild). destruct Hcons0 as [blockParent [startParent [endParent
        (HblockParentMapped & HstartParent & HendParent & Hbounds)]]]. exists blockParent. exists startParent.
      exists endParent. split; trivial. rewrite Hs. rewrite Hs5. rewrite Hs4. unfold bentryStartAddr in *. simpl.
      destruct (beqAddr globalIdPD blockParent) eqn:HbeqGlobBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobBlockP. rewrite HbeqGlobBlockP in *. rewrite HlookupGlobs0 in *.
        exfalso; congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr blockParent) eqn:HbeqLastBlockP.
      {
        apply mappedBlockIsBE in HblockParentMapped. rewrite <-DTL.beqAddrTrue in HbeqLastBlockP. subst blockParent.
        destruct HblockParentMapped as [bentryParent (HlookupBlockP & Hpres)].
        assert(HltKernEntries: CIndex (kernelStructureEntriesNb-1) < kernelStructureEntriesNb) by (cbn; lia).
        specialize(HnewFree (CIndex (kernelStructureEntriesNb-1)) HltKernEntries).
        replace (requisitionedBlockStart + (CIndex (kernelStructureEntriesNb-1)))
          with (requisitionedBlockStart+kernelStructureEntriesNb-1) in HnewFree; try(cbn; lia).
        rewrite <-HlastBlock in *. unfold isFreeSlot in *. rewrite HlookupBlockP in *. exfalso.
        destruct (lookup (CPaddr (lastBlockEntryAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in HbeqGlobBlockP. rewrite HbeqGlobBlockP. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) blockParent) eqn:HbeqNextBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextBlockP. rewrite HbeqNextBlockP in *. rewrite HlookupNext in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. auto.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(partitionTreeIsTree s).
    { (* BEGIN partitionTreeIsTree s *)
      assert(Hcons0: partitionTreeIsTree s0) by (unfold consistency1 in *; intuition).
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
      rewrite HgetPartsEq in *.
      assert(isPDT child s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      assert(HparentIsParents0: pdentryParent child pdparent s0).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. rewrite Hs5 in HparentIsParent.
        rewrite Hs4 in HparentIsParent. simpl in HparentIsParent. destruct (beqAddr globalIdPD child) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst child. rewrite HlookupGlobs0. subst pdparent. rewrite HnewPD.
          simpl. rewrite Hprev3. simpl. rewrite Hprev2. simpl. rewrite Hprev. reflexivity.
        - rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in HparentIsParent.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HparentIsParent.
          simpl in HparentIsParent.
          destruct (beqAddr lastBlockEntryAddr child) eqn:HbeqLastChild; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HparentIsParent. simpl in HparentIsParent. rewrite beqAddrFalse in HbeqParts.
          rewrite HbeqParts in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HparentIsParent.
          simpl in HparentIsParent.
          destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) child) eqn:HbeqNextChild;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      assert(HparentsLists0: isParentsList s0 parentsList pdparent).
      {
        assert(Hentries: exists pdentrys pdentrys5 pdentrys4 pdentrys3 pdentrys2 pdentrys1,
          lookup pdparent (memory s1) beqAddr = Some (PDT pdentrys1)
          /\ lookup pdparent (memory s2) beqAddr = Some (PDT pdentrys2)
          /\ lookup pdparent (memory s3) beqAddr = Some (PDT pdentrys3)
          /\ lookup pdparent (memory s4) beqAddr = Some (PDT pdentrys4)
          /\ lookup pdparent (memory s5) beqAddr = Some (PDT pdentrys5)
          /\ lookup pdparent (memory s) beqAddr = Some (PDT pdentrys)
          /\ (pdparent <> globalIdPD -> pdentrys = pdentrys5 /\ pdentrys5 = pdentrys4 /\ pdentrys4 = pdentrys3
              /\ pdentrys3 = pdentrys2 /\ pdentrys2 = pdentrys1)).
        {
          unfold pdentryParent in *.
          destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          assert(HparentOfParts0: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
          specialize(HparentOfParts0 child p HlookupChild). destruct HparentOfParts0 as (HparentIsParts0 & _).
          specialize(HparentIsParts0 HbeqChildRoot). destruct HparentIsParts0 as ([parentEntrys0 Hlookups0] & _).
          destruct (beqAddr globalIdPD pdparent) eqn:HbeqGlobParent.
          - rewrite <-DTL.beqAddrTrue in HbeqGlobParent. rewrite HbeqGlobParent in *. exists newPDentry.
            exists prevPDentry3. exists prevPDentry2. exists prevPDentry. exists prevPDentry. exists pdentry.
            intuition.
          - rewrite Hs. rewrite Hs5. rewrite Hs4. rewrite Hs2. simpl. rewrite HbeqGlobParent. rewrite beqAddrTrue.
            rewrite <-beqAddrFalse in *. repeat rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            rewrite Hs3. simpl. destruct (beqAddr lastBlockEntryAddr pdparent) eqn:HbeqLastParent.
            {
              rewrite <-DTL.beqAddrTrue in HbeqLastParent. rewrite HbeqLastParent in *. exfalso; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2.
            simpl. rewrite beqAddrFalse in HbeqGlobParent. rewrite HbeqGlobParent.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1.
            simpl. destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) pdparent) eqn:HbeqNextParent.
            { rewrite <-DTL.beqAddrTrue in HbeqNextParent. rewrite HbeqNextParent in *. exfalso; congruence. }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
            exists parentEntrys0. exists parentEntrys0. exists parentEntrys0. exists parentEntrys0.
            exists parentEntrys0. exists parentEntrys0. rewrite HparentIsParents0. intuition.
        }
        destruct Hentries as [pdentrys [pdentrys5 [pdentrys4 [pdentrys3 [pdentrys2 [pdentrys1 (Hlookups1 & Hlookups2 &
          Hlookups3 & Hlookups4 & Hlookups5 & Hlookups & HnotGlob)]]]]]].
        assert(Hpropss5: isParentsList s5 parentsList pdparent).
        {
          revert HparentsList. apply isParentsListEqPDTSameParent with globalIdPD newPDentry; trivial.
          destruct (beqAddr globalIdPD pdparent) eqn:HbeqParts.
          - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists prevPDentry3. exists newPDentry.
            exists prevPDentry3. split; trivial. split; trivial. split; trivial. split. rewrite HnewPD. reflexivity.
            split; intro Hbeq; try(exfalso; congruence). rewrite HnewPD. auto.
          - exists pdentrys5. exists pdentrys. exists prevPDentry3. split; trivial. split; trivial. split; trivial.
            rewrite HnewPD. split. reflexivity. rewrite <-beqAddrFalse in *.
            split; intro Hbeq; try(exfalso; congruence). specialize(HnotGlob Hbeq). intuition.
        }
        assert(Hpropss4: isParentsList s4 parentsList pdparent).
        {
          revert Hpropss5. apply isParentsListEqPDTSameParent with globalIdPD prevPDentry3; trivial.
          destruct (beqAddr globalIdPD pdparent) eqn:HbeqParts.
          - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists prevPDentry2. exists prevPDentry3.
            exists prevPDentry2. split; trivial. split; trivial. split; trivial. split. rewrite Hprev3. reflexivity.
            split; intro Hbeq; try(exfalso; congruence). rewrite Hprev3. auto.
          - exists pdentrys4. exists pdentrys5. exists prevPDentry2. split; trivial. split; trivial. split; trivial.
            rewrite Hprev3. split. reflexivity. rewrite <-beqAddrFalse in *.
            split; intro Hbeq; try(exfalso; congruence). specialize(HnotGlob Hbeq). intuition.
        }
        assert(Hpropss3: isParentsList s3 parentsList pdparent).
        {
          revert Hpropss4. apply isParentsListEqPDTSameParent with globalIdPD prevPDentry2; trivial.
          destruct (beqAddr globalIdPD pdparent) eqn:HbeqParts.
          - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists prevPDentry. exists prevPDentry2.
            exists prevPDentry. split; trivial. split; trivial. split; trivial. split. rewrite Hprev2. reflexivity.
            split; intro Hbeq; try(exfalso; congruence). rewrite Hprev2. auto.
          - exists pdentrys3. exists pdentrys4. exists prevPDentry. split; trivial. split; trivial. split; trivial.
            rewrite Hprev2. split. reflexivity. rewrite <-beqAddrFalse in *.
            split; intro Hbeq; try(exfalso; congruence). specialize(HnotGlob Hbeq). intuition.
        }
        assert(Hpropss2: isParentsList s2 parentsList pdparent).
        {
          revert Hpropss3. rewrite Hs3. apply isParentsListEqBERev with bentryStart; trivial. exists pdentrys2.
          assumption.
        }
        assert(Hpropss1: isParentsList s1 parentsList pdparent).
        {
          revert Hpropss2. apply isParentsListEqPDTSameParent with globalIdPD prevPDentry; trivial.
          destruct (beqAddr globalIdPD pdparent) eqn:HbeqParts.
          - rewrite <-DTL.beqAddrTrue in HbeqParts. subst pdparent. exists pdentry. exists prevPDentry.
            exists pdentry. split; trivial. split; trivial. split; trivial. split. rewrite Hprev. reflexivity.
            split; intro Hbeq; try(exfalso; congruence). rewrite Hprev. auto.
          - exists pdentrys1. exists pdentrys2. exists pdentry. split; trivial. split; trivial. split; trivial.
            rewrite Hprev. split. reflexivity. rewrite <-beqAddrFalse in *.
            split; intro Hbeq; try(exfalso; congruence). specialize(HnotGlob Hbeq). intuition.
        }
        revert Hpropss1. rewrite Hs1. apply isParentsListEqPADDRRev with nullAddr; trivial.
        - exists pdentrys1. rewrite Hs1 in Hlookups1. simpl in Hlookups1.
          destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) pdparent) eqn:HbeqNextParent;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        - unfold consistency1 in *; intuition.
      }
      specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParents0 HparentsLists0).
      assumption.
      (* END partitionTreeIsTree *)
    }

    assert(noDupListOfKerns s).
    { (* BEGIN noDupListOfKerns s *)
      assert(Hcons0: noDupListOfKerns s0) by (unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
      - rewrite <-DTL.beqAddrTrue in HbeqGlobPart. subst partition. destruct kernList; try(apply NoDup_nil).
        assert(HlistOfKernss0: p = requisitionedBlockStart /\ isListOfKernels kernList globalIdPD s0).
        {
          simpl in HlistOfKerns. destruct HlistOfKerns as [newPDentryBis (HlookupGlobsBis & HbeqStructNull & Hrec)].
          rewrite HlookupGlobs in HlookupGlobsBis. injection HlookupGlobsBis as HlookupGlobsBis. subst newPDentryBis.
          destruct Hrec as (Heq & Hrec). subst p. rewrite HnewPD. simpl. rewrite Hprev3. simpl. rewrite Hprev2. simpl.
          rewrite Hprev. simpl. split; trivial. rewrite HnewPD in Hrec. simpl in Hrec. rewrite Hprev3 in Hrec.
          simpl in Hrec. rewrite Hprev2 in Hrec. simpl in Hrec. rewrite Hprev in Hrec. simpl in Hrec.
          destruct kernList as [ | firstEl kernList]; simpl; try(auto).
          exists pdentry; split; trivial; simpl in Hrec.
          destruct Hrec as (HlookupNextBis & HlebNextMax & HbeqFirstNull & Hrec); rewrite Hs in HlookupNextBis.
          rewrite Hs5 in HlookupNextBis; rewrite Hs4 in HlookupNextBis; simpl in HlookupNextBis.
          destruct (beqAddr globalIdPD (CPaddr (requisitionedBlockStart+nextoffset))) eqn:HbeqGlobNext;
            try(exfalso; congruence); rewrite beqAddrTrue in HlookupNextBis; rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupNextBis; simpl in *.
          destruct (beqAddr lastBlockEntryAddr (CPaddr (requisitionedBlockStart + nextoffset))) eqn:HbeqLastNext;
            try(exfalso; congruence); rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial; rewrite Hs2 in HlookupNextBis; simpl in *.
          rewrite beqAddrFalse in HbeqGlobNext; rewrite HbeqGlobNext in *; rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial; rewrite Hs1 in HlookupNextBis; simpl in *.
          rewrite beqAddrTrue in HlookupNextBis; injection HlookupNextBis as HlookupNextBis; subst firstEl.
          unfold pdentryStructurePointer in *; rewrite HlookupGlobs0 in *; rewrite <-Hstructs0; split; trivial.
          split; trivial; rewrite Hs in Hrec; apply isListOfKernelsAuxEqPDT in Hrec; rewrite Hs5 in Hrec.
          apply isListOfKernelsAuxEqPDT in Hrec; rewrite Hs4 in Hrec; apply isListOfKernelsAuxEqPDT in Hrec.
          rewrite Hs3 in Hrec; apply isListOfKernelsAuxEqBE in Hrec; rewrite Hs2 in Hrec.
          apply isListOfKernelsAuxEqPDT in Hrec; trivial. revert Hrec. rewrite Hs1.
          apply isListOfKernelsAuxEqPADDR; trivial.
          - assert(HkernList: isListOfKernels [oldKStructurePointer] globalIdPD s0).
            { simpl. exists pdentry. split; trivial. rewrite <-Hstructs0. auto. }
            specialize(HstartNotKerns0 globalIdPD [oldKStructurePointer] HkernList). simpl in HstartNotKerns0. auto.
          - intros klist Hklist. assert(HkernList: isListOfKernels (oldKStructurePointer::klist) globalIdPD s0).
            { simpl. exists pdentry. split; trivial. rewrite <-Hstructs0. auto. }
            specialize(HstartNotKerns0 globalIdPD (oldKStructurePointer::klist) HkernList). simpl in HstartNotKerns0.
            auto.
        }
        destruct HlistOfKernss0 as (Hfirst & HlistOfKernss0). subst p.
        specialize(Hcons0 globalIdPD kernList HlistOfKernss0). apply NoDup_cons; auto.
        apply HstartNotKerns0 with globalIdPD; trivial.
      - assert(HlistOfKernss0: isListOfKernels kernList partition s0).
        {
          rewrite Hs in HlistOfKerns. apply isListOfKernelsEqPDTNotInPart in HlistOfKerns; trivial.
          rewrite Hs5 in HlistOfKerns. apply isListOfKernelsEqPDTNotInPart in HlistOfKerns; trivial.
          rewrite Hs4 in HlistOfKerns. apply isListOfKernelsEqPDTNotInPart in HlistOfKerns; trivial.
          rewrite Hs3 in HlistOfKerns. apply isListOfKernelsEqBE in HlistOfKerns.
          rewrite Hs2 in HlistOfKerns. apply isListOfKernelsEqPDTNotInPart in HlistOfKerns; trivial.
          revert HlistOfKerns. rewrite Hs1. apply isListOfKernelsEqPADDR; trivial. apply HstartNotKerns0.
        }
        specialize(Hcons0 partition kernList HlistOfKernss0). assumption.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax s).
    { (* BEGIN MPUsizeIsBelowMax s *)
      assert(Hcons0: MPUsizeIsBelowMax s0) by (unfold consistency1 in *; intuition).
      intros partition MPUlist HMPU. assert(HMPUs0: pdentryMPU partition MPUlist s0).
      {
        unfold pdentryMPU in *. rewrite Hs in HMPU. rewrite Hs5 in HMPU.
        rewrite Hs4 in HMPU. simpl in HMPU. destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. rewrite HlookupGlobs0. subst MPUlist.
          rewrite HnewPD. simpl. rewrite Hprev3. simpl. rewrite Hprev2. simpl. rewrite Hprev. reflexivity.
        - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HMPU. simpl in HMPU.
          destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HMPU. simpl in HMPU. rewrite beqAddrFalse in HbeqParts. rewrite HbeqParts in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs1 in HMPU. simpl in HMPU.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 partition MPUlist HMPUs0). assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(HsceEq: forall addr, isSCE addr s -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
    {
      intros addr HaddrIsSCE. unfold isSCE in *. rewrite Hs in HaddrIsSCE. rewrite Hs5 in HaddrIsSCE.
      rewrite Hs4 in HaddrIsSCE. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl in *.
      destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr; try(exfalso; congruence). rewrite beqAddrTrue in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HaddrIsSCE. rewrite Hs3.
      simpl in *. destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqLastAddr; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
      rewrite Hs2 in HaddrIsSCE. simpl in *. rewrite beqAddrFalse in HbeqGlobAddr. rewrite HbeqGlobAddr in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1.
      rewrite Hs1 in HaddrIsSCE. simpl in *. destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) addr)
        eqn:HbeqNextAddr; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }

    assert(HpresentBlockLookEq: forall block, bentryPFlag block true s0
      -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    {
      intros block HPflag. unfold bentryPFlag in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobBlock. rewrite HbeqGlobBlock in *. rewrite HlookupGlobs0 in *.
        exfalso; congruence.
      }
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBlock. rewrite HbeqLastBlock in *. rewrite HlookupLasts0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqNextBlock. rewrite HbeqNextBlock in *. rewrite HlookupNext in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }

    assert(originIsParentBlocksStart s).
    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEq in *. apply HpartFieldsEq in HlookupPart.
      destruct HlookupPart as [pdentryParts0 (HlookupParts0 & HparentsEq & HMPUEq & HVidtEq)]. rewrite <-HparentsEq.
      rewrite HgetMappedBEq in HblockMapped; try(unfold isPDT; rewrite HlookupParts0; trivial).
      unfold scentryOrigin in *.
      rewrite HsceEq in Horigin; try(unfold isSCE; destruct (lookup scentryaddr (memory s) beqAddr); try(congruence);
        destruct v; try(congruence); trivial).
      specialize(Hcons0 partition pdentryParts0 block scentryaddr scorigin HpartIsPart HlookupParts0 HblockMapped
        Hsce Horigin). destruct Hcons0 as (Hincl & HlebStart). apply mappedBlockIsBE in HblockMapped.
      destruct HblockMapped as [bentry (HlookupBlock & Hpresent)].
      assert(HlookupEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
      { apply HpresentBlockLookEq. unfold bentryPFlag. rewrite HlookupBlock. auto. }
      split.
      - intro HbeqPartRoot. specialize(Hincl HbeqPartRoot).
        destruct Hincl as [blockParent (HblockParentMapped & HstartParent & Hincl)]. exists blockParent.
        assert(isPDT (parent pdentryParts0) s0).
        {
          unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
          destruct (lookup (parent pdentryParts0) (memory s0) beqAddr); try(simpl in HblockParentMapped; congruence).
          destruct v; try(simpl in HblockParentMapped; congruence). trivial.
        }
        rewrite HgetMappedBEq; trivial. split; trivial. apply mappedBlockIsBE in HblockParentMapped.
        destruct HblockParentMapped as [bentryP (HlookupBlockP & HpresentP)].
        assert(HlookupPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
        { apply HpresentBlockLookEq. unfold bentryPFlag. rewrite HlookupBlockP. auto. }
        unfold bentryStartAddr. simpl. rewrite HlookupPEq. rewrite HlookupEq. auto.
      - unfold bentryStartAddr. rewrite HlookupEq. assumption.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut s).
    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s0) by (unfold consistency1 in *; intuition).
      intros partition pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock
        Hsce HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEq in *. apply HpartFieldsEq in HlookupPart.
      destruct HlookupPart as [pdentryParts0 (HlookupParts0 & HparentsEq & _)]. rewrite <-HparentsEq.
      rewrite HgetMappedBEq in HblockMapped; try(unfold isPDT; rewrite HlookupParts0; trivial).
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
      {
        apply HpresentBlockLookEq. apply mappedBlockIsBE in HblockMapped. unfold bentryPFlag.
        destruct HblockMapped as [bentry (HlookupBlock & Hpres)]. rewrite HlookupBlock. auto.
      }
      unfold bentryEndAddr in *. rewrite HlookupBlockEq in *. unfold scentryNext in *. rewrite HsceEq in Hnext;
        try(unfold isSCE; destruct (lookup scentryaddr (memory s) beqAddr); try(congruence); destruct v;
        try(congruence); trivial). specialize(Hcons0 partition pdentryParts0 block scentryaddr scnext endaddr
        HpartIsPart HlookupParts0 HblockMapped HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & HltEnd & Hincl)]].
      exists blockParent. exists endParent. assert(isPDT (parent pdentryParts0) s0).
      {
        unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
        destruct (lookup (parent pdentryParts0) (memory s0) beqAddr); try(simpl in HblockParentMapped; congruence).
        destruct v; try(simpl in HblockParentMapped; congruence). trivial.
      }
      rewrite HgetMappedBEq; trivial. split; trivial. apply mappedBlockIsBE in HblockParentMapped.
      destruct HblockParentMapped as [bentryP (HlookupBlockP & HpresentP)].
      assert(HlookupPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
      { apply HpresentBlockLookEq. unfold bentryPFlag. rewrite HlookupBlockP. auto. }
      simpl. rewrite HlookupPEq. rewrite HlookupBlockEq. auto.
      (* END nextImpliesBlockWasCut *)
    }

    assert(HpresentBlockLookEqs: forall block, bentryPFlag block true s
      -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    {
      intros block HPflag. unfold bentryPFlag in *. rewrite Hs. rewrite Hs5. rewrite Hs4. rewrite Hs in HPflag.
      rewrite Hs5 in HPflag. rewrite Hs4 in HPflag. simpl in *.
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. rewrite Hs3 in HPflag. simpl in *.
      destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBlock. rewrite HbeqLastBlock in *. rewrite HnewBs3 in HPflag.
        simpl in HPflag. rewrite HlookupLasts0 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
      rewrite Hs2 in HPflag. simpl in *. rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1.
      rewrite Hs1 in HPflag. simpl in *.
      destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }

    assert(blocksAddressesTypes s).
    { (* BEGIN blocksAddressesTypes s *)
      assert(Hcons0: blocksAddressesTypes s0) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock.
      rewrite HgetPartsEq in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
      {
        apply HpresentBlockLookEqs; trivial. apply mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag. rewrite Hlookup. auto.
      }
      rewrite HgetMappedBEq in *; trivial.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockEq in *.
      unfold sh1entryPDchild in *. rewrite HsheEq in HPDchildBlock; try(unfold isSHE;
        destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr); try(congruence); destruct v;
        try(congruence); trivial).
      specialize(Hcons0 block startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock).
      destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hnone]].
      - left. unfold isKS in *.
        destruct (lookup startaddr (memory s0) beqAddr) eqn:HlookupStart; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply HblockFieldsEq in HlookupStart.
        destruct HlookupStart as [bentry (HlookupStarts & _ & _ & _ & _ & _ & Heq & _)]. rewrite HlookupStarts.
        rewrite Heq. split; trivial. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
        destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
        + left. unfold isBE in *.
          destruct (lookup addr (memory s0) beqAddr) eqn:HlookupAddr; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). apply HblockFieldsEq in HlookupAddr.
          destruct HlookupAddr as [bentryA (HlookupAddr & _)]. rewrite HlookupAddr. trivial.
        + right. left. unfold isSHE in *. rewrite HlookupSh1Eq; trivial.
        + right. right. left. unfold isSCE in *. rewrite HlookupSceEq; trivial.
        + right. right. right. left. unfold isPADDR in *. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
          destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqGlobAddr. rewrite HbeqGlobAddr in *. rewrite HlookupGlobs0 in *.
            congruence.
          }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqLastAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqLastAddr. rewrite HbeqLastAddr in *. rewrite HlookupLasts0 in *.
            congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite beqAddrFalse in HbeqGlobAddr. rewrite HbeqGlobAddr. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) addr) eqn:HbeqNextAddr; trivial.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + right. right. right. right. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
          destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr.
          { rewrite <-DTL.beqAddrTrue in HbeqGlobAddr. rewrite HbeqGlobAddr in *. congruence. }
          rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
          destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqLastAddr.
          { rewrite <-DTL.beqAddrTrue in HbeqLastAddr. rewrite HbeqLastAddr in *. congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite beqAddrFalse in HbeqGlobAddr. rewrite HbeqGlobAddr. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) addr) eqn:HbeqNextAddr.
          { rewrite <-DTL.beqAddrTrue in HbeqNextAddr. rewrite HbeqNextAddr in *. congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. left. split; try(apply HstablePDTs0; assumption). intros addr HaddrInRange.
        specialize(Hrange addr HaddrInRange). rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
        destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqGlobAddr. rewrite HbeqGlobAddr in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqLastAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqLastAddr. rewrite HbeqLastAddr in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in HbeqGlobAddr. rewrite HbeqGlobAddr. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) addr) eqn:HbeqNextAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqNextAddr. rewrite HbeqNextAddr in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. right. intros addr HaddrInRange.
        specialize(Hnone addr HaddrInRange). rewrite Hs. rewrite Hs5. rewrite Hs4. simpl.
        destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqGlobAddr. rewrite HbeqGlobAddr in *. congruence. }
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqLastAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqLastAddr. rewrite HbeqLastAddr in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in HbeqGlobAddr. rewrite HbeqGlobAddr. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) addr) eqn:HbeqNextAddr.
        { rewrite <-DTL.beqAddrTrue in HbeqNextAddr. rewrite HbeqNextAddr in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END blocksAddressesTypes *)
    }

    assert(notPDTIfNotPDflag s).
    { (* BEGIN notPDTIfNotPDflag s *)
      assert(Hcons0: notPDTIfNotPDflag s0) by (unfold consistency1 in *; intuition).
      intros block startaddr sh1entryaddr part HpartIsPart HblockMapped HstartBlock Hsh1 HPDflagBlock HPDchildB.
      rewrite HgetPartsEq in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *; trivial.
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ sh1entryAddr block sh1entryaddr s0).
      {
        unfold bentryStartAddr in *. unfold sh1entryAddr in *.
        destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply HblockFieldsEqs in HlookupBlock.
        destruct HlookupBlock as [bentrys (HlookupBlock & _ & _ & _ & _ & _ & _ & HstartEq)].
        rewrite HlookupBlock. rewrite HstartEq. auto.
      }
      destruct Hblocks0 as (HstartBlockBiss0 & Hsh1s0). unfold sh1entryPDflag in *.
      unfold sh1entryPDchild in *.
      assert(isSHE sh1entryaddr s) by (unfold isSHE; destruct (lookup sh1entryaddr (memory s) beqAddr);
        try(congruence); destruct v; try(congruence); trivial).
      rewrite HsheEq in HPDflagBlock; trivial. rewrite HsheEq in HPDchildB; trivial.
      specialize(Hcons0 block startaddr sh1entryaddr part HpartIsPart HblockMapped HstartBlockBiss0 Hsh1s0
        HPDflagBlock HPDchildB).
      contradict Hcons0. revert Hcons0. apply HstablePDT.
      (* END notPDTIfNotPDflag *)
    }

    assert(nextKernAddrIsInSameBlock s).
    { (* BEGIN nextKernAddrIsInSameBlock s *)
      assert(Hcons0: nextKernAddrIsInSameBlock s0) by (unfold consistency1 in *; intuition).
      intros block kernel startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HnextInRange
        HkernIsKS.
      rewrite HgetPartsEq in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      assert(HPflagBlock: bentryPFlag block true s).
      {
        apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
        unfold bentryPFlag. rewrite Hlookup. auto.
      }
      rewrite HgetMappedBEq in *; trivial.
      specialize(HpresentBlockLookEqs block HPflagBlock). unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      unfold bentryPFlag in *. rewrite HpresentBlockLookEqs in *. unfold sh1entryPDchild in *.
      rewrite HsheEq in HnextInRange; try(unfold isSHE;
        destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr); try(congruence); destruct v;
        try(congruence); trivial).
      assert(HkernIsKSs0: isKS kernel s0).
      {
        unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs5 in HkernIsKS. rewrite Hs4 in HkernIsKS.
        simpl in *. destruct (beqAddr globalIdPD kernel) eqn:HbeqGlobBlock; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HkernIsKS.
        simpl in *. destruct (beqAddr lastBlockEntryAddr kernel) eqn:HbeqLastBlock.
        - rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst kernel. rewrite HlookupLasts0.
          rewrite HnewBs3 in HkernIsKS. simpl in *. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          rewrite Hs2 in HkernIsKS. simpl in *. rewrite beqAddrFalse in HbeqGlobBlock.
          rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.  rewrite Hs1 in HkernIsKS. simpl in *.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) kernel) eqn:HbeqNextBlock;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 block kernel startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock
        HnextInRange HkernIsKSs0). assumption.
      (* END nextKernAddrIsInSameBlock *)
    }

    assert(PDflagMeansNoChild s).
    { (* BEGIN PDflagMeansNoChild s *)
      assert(Hcons0: PDflagMeansNoChild s0) by (unfold consistency1 in *; intuition).
      intros block HblockIsBE HPDflagBlock.
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE in *. destruct (lookup block (memory s) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply HblockFieldsEqs in HlookupBlock.
        destruct HlookupBlock as [bentry (HlookupBlock & _)]. rewrite HlookupBlock. trivial.
      }
      assert(isSHE (CPaddr (block + sh1offset)) s).
      {
        unfold sh1entryPDflag in *. unfold isSHE.
        destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      unfold sh1entryPDflag in *. unfold sh1entryPDchild. rewrite HsheEq in HPDflagBlock; trivial.
      rewrite HsheEq; trivial. specialize(Hcons0 block HblockIsBEs0 HPDflagBlock). assumption.
      (* END PDflagMeansNoChild *)
    }

    assert(nbPrepareIsNbKern s).
    { (* BEGIN nbPrepareIsNbKern s *)
      assert(Hcons0: nbPrepareIsNbKern s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros partition pdentryPart HlookupPart. rewrite Hs in HlookupPart. rewrite Hs5 in HlookupPart.
      rewrite Hs4 in HlookupPart. simpl in HlookupPart. destruct (beqAddr globalIdPD partition) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst partition. injection HlookupPart as HlookupPart.
        subst pdentryPart. rewrite HnewPD. simpl. rewrite Hprev3. simpl. rewrite Hprev2. simpl. rewrite Hprev. simpl.
        assert(HnewComplete: completeListOfKernels requisitionedBlockStart s
          = requisitionedBlockStart::(completeListOfKernels (structure pdentry) s0)).
        {
          unfold completeListOfKernels at 1. unfold bentryBlockIndex in *.
          destruct (lookup requisitionedBlockStart (memory s) beqAddr) eqn:HlookupStart; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-Hblkidx. rewrite indexEqRefl. f_equal.
          unfold pdentryStructurePointer in *. rewrite HlookupGlobs0 in *. rewrite <-Hstructs0 in *.
          replace maxNbPrepare with (S (maxNbPrepare-1)); try(lia). cbn -[maxNbPrepare nullAddr].
          rewrite HlookupNexts. destruct (beqAddr oldKStructurePointer nullAddr) eqn:HbeqOldNull.
          + unfold completeListOfKernels. assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition).
            unfold isPADDR in *. rewrite <-DTL.beqAddrTrue in HbeqOldNull. rewrite HbeqOldNull.
            destruct (lookup nullAddr (memory s0) beqAddr); trivial. destruct v; try(exfalso; congruence). trivial.
          + rewrite <-beqAddrFalse in *. rewrite Hstructs0 in *.
            assert(Hstruct: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
            specialize(Hstruct globalIdPD pdentry HlookupGlobs0 HbeqOldNull). unfold completeListOfKernels.
            assert(HstructIsKS: isKS (structure pdentry) s0) by assumption. rewrite <-Hstructs0 in *.
            unfold isKS in Hstruct.
            destruct (lookup oldKStructurePointer (memory s0) beqAddr) eqn:HlookupOld; try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite Hstruct. rewrite indexEqRefl. f_equal.
            assert(Heqss0: completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s
              = completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s0).
            {
              assert(Heqs1: completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s1
                = completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s0).
              {
                rewrite Hs1. apply completeListOfKernelsAuxEqPADDRNew; trivial.
                - unfold consistency1 in *; intuition.
                - apply HstartNotKerns0 with globalIdPD. cbn -[maxNbPrepare nullAddr]. exists pdentry. split; trivial.
                  rewrite <-Hstructs0. split; trivial. split; trivial.
                  apply completeKernListIsListOfKernAux; unfold consistency1 in *; intuition.
              }
              assert(Heqs2: completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s2
                = completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s0).
              {
                rewrite <-Heqs1. rewrite Hs2. apply completeListOfKernelsAuxEqPDT.
                unfold isPADDR; rewrite HlookupGlobs1; intuition.
              }
              assert(Heqs3: completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s3
                = completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s0).
              {
                rewrite <-Heqs2. rewrite Hs3. apply completeListOfKernelsAuxEqBE. unfold isPADDR.
                rewrite HlookupLasts2. intuition.
              }
              assert(Heqs4: completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s4
                = completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s0).
              {
                rewrite <-Heqs3. rewrite Hs4. apply completeListOfKernelsAuxEqPDT. unfold isPADDR.
                rewrite HlookupGlobs3. intuition.
              }
              assert(Heqs5: completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s5
                = completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s0).
              {
                rewrite <-Heqs4. rewrite Hs5. apply completeListOfKernelsAuxEqPDT. unfold isPADDR.
                rewrite HlookupGlobs4. intuition.
              }
              rewrite <-Heqs5. rewrite Hs. apply completeListOfKernelsAuxEqPDT. unfold isPADDR.
              rewrite HlookupGlobs5. intuition.
            }
            rewrite Heqss0. apply completeListOfKernelsAuxN; try(lia). unfold completeListOfKernels in *.
            rewrite HlookupOld in *. unfold zero in *. rewrite Hstruct in *. rewrite indexEqRefl in *.
            cbn -[maxNbPrepare] in HnotFulls0.
            assert(length (completeListOfKernelsAux (maxNbPrepare - 1) oldKStructurePointer s0)
              <= length (completeListOfKernelsAux maxNbPrepare oldKStructurePointer s0)).
            { apply lowerLenLowerBoundCompleteAux; lia. }
            lia.
        }
        rewrite HnewComplete. simpl. assert(Hres: nbPrepareIsNbKern s0) by (unfold consistency1 in *; intuition).
        specialize(Hres globalIdPD pdentry HlookupGlobs0). unfold pdentryNbPrepare in *. rewrite HlookupGlobs5 in *.
        rewrite Hprev3 in HnbPrep. simpl in HnbPrep. rewrite Hprev2 in HnbPrep. simpl in HnbPrep.
        rewrite Hprev in HnbPrep. simpl in HnbPrep. rewrite <-HnbPrep in *. lia.
      - rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HlookupPart.
        simpl in HlookupPart.
        destruct (beqAddr lastBlockEntryAddr partition) eqn:HbeqLastPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs2 in HlookupPart. simpl in HlookupPart. rewrite beqAddrFalse in HbeqParts. rewrite HbeqParts in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        rewrite Hs1 in HlookupPart. simpl in HlookupPart.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) partition) eqn:HbeqNextPart;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 partition pdentryPart HlookupPart). rewrite <-Hcons0. f_equal.
        destruct (beqAddr (structure pdentryPart) nullAddr) eqn:HbeqStructNull.
        + rewrite <-DTL.beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. unfold completeListOfKernels.
          assert(Hnull: nullAddrExists s0) by (unfold consistency1 in *; intuition). unfold nullAddrExists in *.
          unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). reflexivity.
        + rewrite <-beqAddrFalse in *.
          assert(Hstruct: StructurePointerIsKS s0) by (unfold consistency1 in *; intuition).
          specialize(Hstruct partition pdentryPart HlookupPart HbeqStructNull).
          assert(Heqs1: completeListOfKernels (structure pdentryPart) s1
            = completeListOfKernels (structure pdentryPart) s0).
          {
            rewrite Hs1. apply completeListOfKernelsEqPADDRNew; trivial.
            - unfold consistency1 in *; intuition.
            - unfold isPADDR. rewrite HlookupNext. trivial.
            - apply HstartNotKerns0 with partition.
              apply completeKernListIsListOfKern; trivial; unfold consistency1 in *; intuition.
          }
          assert(Heqs2: completeListOfKernels (structure pdentryPart) s2
            = completeListOfKernels (structure pdentryPart) s0).
          {
            rewrite <-Heqs1. rewrite Hs2. apply completeListOfKernelsEqPDT; trivial. unfold isPDT.
            rewrite HlookupGlobs1. trivial.
          }
          assert(Heqs3: completeListOfKernels (structure pdentryPart) s3
            = completeListOfKernels (structure pdentryPart) s0).
          {
            rewrite <-Heqs2. rewrite Hs3. apply completeListOfKernelsEqBE with bentryStart; trivial. rewrite HnewBs3.
            reflexivity.
          }
          assert(Heqs4: completeListOfKernels (structure pdentryPart) s4
            = completeListOfKernels (structure pdentryPart) s0).
          {
            rewrite <-Heqs3. rewrite Hs4. apply completeListOfKernelsEqPDT; trivial. unfold isPDT.
            rewrite HlookupGlobs3. trivial.
          }
          assert(Heqs5: completeListOfKernels (structure pdentryPart) s5
            = completeListOfKernels (structure pdentryPart) s0).
          {
            rewrite <-Heqs4. rewrite Hs5. apply completeListOfKernelsEqPDT; trivial. unfold isPDT.
            rewrite HlookupGlobs4. trivial.
          }
          rewrite <-Heqs5. rewrite Hs. apply completeListOfKernelsEqPDT; trivial. unfold isPDT.
          rewrite HlookupGlobs5. trivial.
     (* END nbPrepareIsNbKern *)
    }

    assert(pdchildIsPDT s).
    { (* BEGIN pdchildIsPDT s *)
      assert(Hcons0: pdchildIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull.
      rewrite HgetPartsEq in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *; trivial. unfold sh1entryPDchild in *. unfold sh1entryAddr in *.
      rewrite Hs in HPDchildB. rewrite Hs in Hsh1. rewrite Hs5 in HPDchildB. rewrite Hs4 in HPDchildB.
      rewrite Hs5 in Hsh1. rewrite Hs4 in Hsh1. simpl in HPDchildB. simpl in Hsh1. rewrite beqAddrTrue in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPDchildB. simpl in HPDchildB.
      rewrite Hs3 in Hsh1. simpl in Hsh1. destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. apply mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag in *. rewrite Hlookup in *.
        exfalso; congruence.
      }
      destruct (beqAddr lastBlockEntryAddr sh1entryaddr) eqn:HbeqLastSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HPDchildB. simpl in HPDchildB. rewrite Hs2 in Hsh1. simpl in Hsh1. rewrite beqAddrFalse in *.
      rewrite HbeqGlobSh1 in *. rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPDchildB. simpl in HPDchildB.
      rewrite Hs1 in Hsh1. simpl in Hsh1.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) sh1entryaddr) eqn:HbeqNextSh1;
        try(exfalso; congruence).
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull).
      rewrite HgetChildrenEq; trivial.
      (* END pdchildIsPDT *)
    }

    assert(childBlockNullIfChildNull s).
    { (* BEGIN childBlockNullIfChildNull s *)
      assert(Hcons0: childBlockNullIfChildNull s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchildB.
      rewrite HgetPartsEq in *. unfold sh1entryInChildLocation. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *; trivial. unfold sh1entryPDchild in *. unfold sh1entryAddr in *. rewrite Hs.
      simpl. rewrite <-Hs. rewrite Hs5. rewrite Hs4. simpl.
      rewrite Hs in HPDchildB. rewrite Hs in Hsh1. rewrite Hs5 in HPDchildB. rewrite Hs4 in HPDchildB.
      rewrite Hs5 in Hsh1. rewrite Hs4 in Hsh1. simpl in HPDchildB. simpl in Hsh1. rewrite beqAddrTrue in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPDchildB. simpl in HPDchildB.
      rewrite Hs3 in Hsh1. simpl in Hsh1. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. apply mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag in *. rewrite Hlookup in *.
        exfalso; congruence.
      }
      destruct (beqAddr lastBlockEntryAddr sh1entryaddr) eqn:HbeqLastSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HPDchildB. simpl in HPDchildB. rewrite Hs2 in Hsh1. simpl in Hsh1. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqGlobSh1 in *. rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPDchildB. simpl in HPDchildB.
      rewrite Hs1 in Hsh1. simpl in Hsh1. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) sh1entryaddr) eqn:HbeqNextSh1;
        try(exfalso; congruence).
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchildB).
      unfold sh1entryInChildLocation in *.
      destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      destruct Hcons0. split; trivial. intro. exfalso; congruence.
      (* END childBlockNullIfChildNull *)
    }

    assert(accessibleBlocksArePresent s).
    { (* BEGIN accessibleBlocksArePresent s *)
      assert(Hcons0: accessibleBlocksArePresent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros block HAflag. unfold bentryAFlag in *. unfold bentryPFlag. rewrite Hs in HAflag. rewrite Hs5 in HAflag.
      rewrite Hs4 in HAflag. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl in *. rewrite beqAddrTrue in *.
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HAflag. rewrite Hs3. simpl in *.
      destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. rewrite HnewBs3 in *. simpl in *.
        assert(HAflags0: bentryAFlag lastBlockEntryAddr true s0).
        { unfold bentryAFlag. rewrite HlookupLasts0. assumption. }
        specialize(Hcons0 lastBlockEntryAddr HAflags0). unfold bentryPFlag in *. rewrite HlookupLasts0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HAflag. simpl in HAflag. rewrite Hs2. simpl. rewrite beqAddrFalse in *.
      rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HAflag. simpl in HAflag.
      rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) block) eqn:HbeqNextBlock; try(congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      apply Hcons0; assumption.
      (* END accessibleBlocksArePresent *)
    }

    assert(sharedBlockIsPresent s).
    { (* BEGIN sharedBlockIsPresent s *)
      assert(Hcons0: sharedBlockIsPresent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part block child HpartIsPart HblockIsEntry HPDchildB HbeqChildNull. rewrite HgetPartsEq in *.
      unfold sh1entryPDchild in *. assert(isSHE (CPaddr (block + sh1offset)) s).
      {
        unfold isSHE. destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      rewrite HsheEq in HPDchildB; trivial.
      assert(HblockIsEntrys0: In block (filterOptionPaddr (getKSEntries part s0))).
      {
        destruct (beqAddr globalIdPD part) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. rewrite HgetKSEqGlob in HblockIsEntry.
          rewrite filterOptionPaddrSplit in HblockIsEntry. apply in_app_or in HblockIsEntry.
          destruct HblockIsEntry as [Hcontra | Hres]; trivial. exfalso.
          apply getKSEntriesInStructAuxToIndexAux in Hcontra; try(lia).
          destruct Hcontra as [kernIdx (HlebIdxStructNb & Hblock)].
          assert(HltIdxStructNb: kernIdx < kernelStructureEntriesNb).
          {
            unfold CIndex in HlebIdxStructNb. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
            cbn -[kernelStructureEntriesNb] in HlebIdxStructNb. lia.
          }
          specialize(HnewFree kernIdx HltIdxStructNb). unfold isFreeSlot in *. rewrite <-Hblock in *.
          destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). rewrite <-HPDchildB in *.
          destruct (lookup (CPaddr (block+scoffset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). destruct HnewFree as (_ & _ & _ & _ & _ & _ & Hchild & _). congruence.
        - rewrite HgetKSEqNotGlob in HblockIsEntry; trivial.
          apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
      }
      specialize(Hcons0 part block child HpartIsPart HblockIsEntrys0 HPDchildB HbeqChildNull).
      unfold bentryPFlag in *. destruct (lookup block (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). apply HblockFieldsEq in HlookupBlock.
      destruct HlookupBlock as [bentrys (HlookupBlocks & _ & _ & _ & HpresEq & _)]. rewrite HlookupBlocks.
      rewrite HpresEq. assumption.
      (* END sharedBlockIsPresent *)
    }

    assert(HgetConfigBEqNotGlob: forall part, isPDT part s0 -> globalIdPD <> part
      -> getConfigBlocks part s = getConfigBlocks part s0).
    {
      intros part HpartIsPDT HbeqParts. assert(Heqs1: getConfigBlocks part s1 = getConfigBlocks part s0).
      {
        rewrite Hs1. apply getConfigBlocksEqPADDR; trivial. 1-3: unfold consistency1 in *; intuition.
        - unfold isPADDR. rewrite HlookupNext. trivial.
        - rewrite <-beqAddrFalse. unfold CPaddr.
          destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia). apply paddrNeqNatNeqEquiv.
          cbn. rewrite Hnextoffset. cbn. lia.
        - intros kern HkernIsConfB. unfold CPaddr.
          destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia). simpl. intro Hcontra.
          apply PeanoNat.Nat.add_cancel_r in Hcontra. apply paddrEqNatEqEquiv in Hcontra. subst kern.
          apply HstartNotConf in HkernIsConfB. congruence.
      }
      assert(Heqs2: getConfigBlocks part s2 = getConfigBlocks part s0).
      {
        rewrite <-Heqs1. rewrite Hs2. apply getConfigBlocksEqPDTNotInPart with pdentry; auto.
      }
      assert(HpartIsPDTs2: isPDT part s2).
      {
        unfold isPDT in *. rewrite Hs2. simpl. rewrite beqAddrFalse in HbeqParts. rewrite HbeqParts.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) part) eqn:HbeqNextPart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqNextPart. subst part. rewrite HlookupNext in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      assert(Heqs3: getConfigBlocks part s3 = getConfigBlocks part s0).
      {
        rewrite <-Heqs2. rewrite Hs3. apply getConfigBlocksEqBE; auto. unfold isBE. rewrite HlookupLasts2. trivial.
      }
      assert(HpartIsPDTs3: isPDT part s3).
      {
        unfold isPDT in *. rewrite Hs3. simpl. destruct (beqAddr lastBlockEntryAddr part) eqn:HbeqLastPart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqLastPart. subst part. rewrite HlookupLasts2 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      assert(Heqs4: getConfigBlocks part s4 = getConfigBlocks part s0).
      {
        rewrite <-Heqs3. rewrite Hs4. apply getConfigBlocksEqPDT with prevPDentry; trivial. rewrite Hprev2. auto.
      }
      assert(HpartIsPDTs4: isPDT part s4).
      {
        unfold isPDT in *. rewrite Hs4. simpl. rewrite beqAddrFalse in HbeqParts. rewrite HbeqParts.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      assert(Heqs5: getConfigBlocks part s5 = getConfigBlocks part s0).
      {
        rewrite <-Heqs4. rewrite Hs5. apply getConfigBlocksEqPDT with prevPDentry2; trivial. rewrite Hprev3. auto.
      }
      assert(HpartIsPDTs5: isPDT part s5).
      {
        unfold isPDT in *. rewrite Hs5. simpl. rewrite beqAddrFalse in HbeqParts. rewrite HbeqParts.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      rewrite <-Heqs5. rewrite Hs. apply getConfigBlocksEqPDT with prevPDentry3; trivial. rewrite HnewPD. auto.
    }

    assert(HgetConfigBImpl: forall part kern, isPDT part s0 -> In kern (getConfigBlocks part s0)
      -> In kern (getConfigBlocks part s)).
    {
      intros part kern HpartIsPDT HkernIsConfB. destruct (beqAddr globalIdPD part) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. rewrite HgetConfigGlobEq. simpl. auto.
      - rewrite <-beqAddrFalse in *. rewrite HgetConfigBEqNotGlob; trivial.
    }

    assert(sharedBlockNoPDflagNoLocIsKern s).
    { (* BEGIN sharedBlockNoPDflagNoLocIsKern s *)
      assert(Hcons0: sharedBlockNoPDflagNoLocIsKern s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part block child startaddr HpartIsPart HblockIsEntry HPDchildB HbeqChildNull HPDflagB Hloc Hstart.
      rewrite HgetPartsEq in *. unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
      unfold sh1entryInChildLocationWeak in *. assert(isSHE (CPaddr (block + sh1offset)) s).
      {
        unfold isSHE. destruct (lookup (CPaddr (block + sh1offset)) (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      rewrite HsheEq in HPDchildB; trivial. rewrite HsheEq in HPDflagB; trivial. rewrite HsheEq in Hloc; trivial.
      assert(HblockIsEntrys0: In block (filterOptionPaddr (getKSEntries part s0))).
      {
        destruct (beqAddr globalIdPD part) eqn:HbeqParts.
        - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. rewrite HgetKSEqGlob in HblockIsEntry.
          rewrite filterOptionPaddrSplit in HblockIsEntry. apply in_app_or in HblockIsEntry.
          destruct HblockIsEntry as [Hcontra | Hres]; trivial. exfalso.
          apply getKSEntriesInStructAuxToIndexAux in Hcontra; try(lia).
          destruct Hcontra as [kernIdx (HlebIdxStructNb & Hblock)].
          assert(HltIdxStructNb: kernIdx < kernelStructureEntriesNb).
          {
            unfold CIndex in HlebIdxStructNb. destruct (le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
            cbn -[kernelStructureEntriesNb] in HlebIdxStructNb. lia.
          }
          specialize(HnewFree kernIdx HltIdxStructNb). unfold isFreeSlot in *. rewrite <-Hblock in *.
          destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). rewrite <-HPDchildB in *.
          destruct (lookup (CPaddr (block+scoffset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). destruct HnewFree as (_ & _ & _ & _ & _ & _ & Hchild & _). congruence.
        - rewrite HgetKSEqNotGlob in HblockIsEntry; trivial.
          apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
      }
      assert(Hstarts0: bentryStartAddr block startaddr s0).
      {
        unfold bentryStartAddr in *. destruct (lookup block (memory s) beqAddr) eqn:Hlookup; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply HblockFieldsEqs in Hlookup.
        destruct Hlookup as [bentry (Hlookups0 & _ & _ & _ & _ & _ & _ & Heq)]. rewrite Hlookups0. rewrite Heq.
        assumption.
      }
      specialize(Hcons0 part block child startaddr HpartIsPart HblockIsEntrys0 HPDchildB HbeqChildNull HPDflagB Hloc
        Hstarts0). apply HgetConfigBImpl; trivial. unfold getConfigBlocks in *. unfold isPDT.
      destruct (lookup child (memory s0) beqAddr); try(simpl in Hcons0; congruence).
      destruct v; try(simpl in Hcons0; congruence). trivial.
      (* END sharedBlockNoPDflagNoLocIsKern *)
    }

    assert(partitionNotAutoMapped s).
    { (* BEGIN partitionNotAutoMapped s *)
      assert(Hcons0: partitionNotAutoMapped s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part HpartIsPart. rewrite HgetPartsEq in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
      specialize(Hcons0 part HpartIsPart). rewrite HgetMappedPEq; trivial.
      (* END partitionNotAutoMapped *)
    }

    assert(HnewConfigInReq: forall addr,
      In addr (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
      -> In addr (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)).
    {
      rewrite <-HtotLen. intros addr HaddrInNewConfig. apply eq_sym in HltSizeTot.
      apply DTL.indexltbFalse in HltSizeTot. rewrite Hsize in *. simpl. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *.
      destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(simpl; congruence).
      destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartBlocks0. rewrite <-HendBlocks0.
      apply getAllPaddrBlockInclRevAux in HaddrInNewConfig.
      destruct HaddrInNewConfig as (HlebStartAddr & HltAddrEndKS & _). apply getAllPaddrBlockIncl; lia.
    }

    assert(configAddrNotMappedInChild s).
    { (* BEGIN configAddrNotMappedInChild s *)
      assert(Hcons0: configAddrNotMappedInChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part child addr HpartIsPart HchildIsChild HaddrIsConfig. rewrite HgetPartsEq in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
      rewrite HgetChildrenEq in *; trivial.
      assert(Himpl: In addr (getConfigPaddr part s0) -> ~In addr (getMappedPaddr child s)).
      {
        intro HaddrIsConfigs0. specialize(Hcons0 part child addr HpartIsPart HchildIsChild HaddrIsConfigs0).
        rewrite HgetMappedPEq; trivial. apply childrenArePDT with part; trivial; unfold consistency in *;
          unfold consistency1 in *; intuition.
      }
      assert(isPDT child s0).
      { apply childrenArePDT with part; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
      destruct (beqAddr part globalIdPD) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. unfold getConfigPaddr in HaddrIsConfig.
        rewrite HgetConfigPPartial2GlobEqs in *. rewrite HgetConfigPPartial1GlobEqs in *.
        assert(HpropsOr: In addr (getConfigPaddr globalIdPD s0)
          \/ In addr (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)).
        {
          apply in_app_or in HaddrIsConfig. unfold getConfigPaddr. destruct HaddrIsConfig as [HPDT | Hright].
          - left. apply in_or_app. auto.
          - apply in_app_or in Hright. destruct Hright as [Hright | Hleft]; try(right; assumption).
            left. apply in_or_app. auto.
        }
        destruct HpropsOr as [HaddrIsConfigs0 | HaddrIsNewKern]; try(apply Himpl; assumption).
        apply HnewConfigInReq in HaddrIsNewKern. assert(HnotShared: noChildImpliesAddressesNotShared s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HlookupCurrs0: exists pdentryCurr, lookup currentPart (memory s0) beqAddr = Some(PDT pdentryCurr)).
        {
          apply isPDTLookupEq. apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *;
            intuition.
        }
        destruct HlookupCurrs0 as [pdentryCurr HlookupCurrs0].
        assert(HeqTriv: CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)
          = CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) by reflexivity.
        specialize(HnotShared currentPart pdentryCurr requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) HcurrIsParts0 HlookupCurrs0 HblockMappedCurrs0
          HeqTriv HPDchilds0). destruct Hglob as [Heq | HglobIsChild].
        + subst globalIdPD. specialize(HnotShared child addr HchildIsChild HaddrIsNewKern).
          rewrite HgetMappedPEq; trivial.
        + specialize(HnotShared globalIdPD addr HglobIsChild HaddrIsNewKern). rewrite HgetMappedPEq; trivial.
          contradict HnotShared. assert(Hres: childPaddrIsIntoParent s0).
          { apply blockInclImpliesAddrIncl; unfold consistency in *; unfold consistency1 in *; intuition. }
          specialize(Hres globalIdPD child). apply Hres; trivial.
      - rewrite <-beqAddrFalse in *. rewrite HgetConfigPNotGlobEq in *; trivial. apply Himpl; assumption.
     (* END configAddrNotMappedInChild *)
    }

    (* assert(configNotMappedRoot s).
    { (* BEGIN configNotMappedRoot s *)
      assert(Hcons0: configNotMappedRoot s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros addr HaddrIsConfig.
      assert(isPDT multiplexer s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(Himpl: In addr (getConfigPaddr multiplexer s0) -> ~In addr (getMappedPaddr multiplexer s)).
      {
        intro HaddrIsConfigs0. specialize(Hcons0 addr HaddrIsConfigs0). rewrite HgetMappedPEq; trivial.
      }
      destruct (beqAddr multiplexer globalIdPD) eqn:HbeqParts.
      - rewrite <-DTL.beqAddrTrue in HbeqParts. rewrite <-HbeqParts in *. unfold getConfigPaddr in HaddrIsConfig.
        rewrite HgetConfigPPartial2GlobEqs in *. rewrite HgetConfigPPartial1GlobEqs in *.
        assert(HpropsOr: In addr (getConfigPaddr multiplexer s0)
          \/ In addr (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)).
        {
          apply in_app_or in HaddrIsConfig. unfold getConfigPaddr. destruct HaddrIsConfig as [HPDT | Hright].
          - left. apply in_or_app. auto.
          - apply in_app_or in Hright. destruct Hright as [Hright | Hleft]; try(right; assumption).
            left. apply in_or_app. auto.
        }
        destruct HpropsOr as [HaddrIsConfigs0 | HaddrIsNewKern]; try(apply Himpl; assumption).
        apply HnewConfigInReq in HaddrIsNewKern. assert(HnotShared: noChildImpliesAddressesNotShared s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HlookupCurrs0: exists pdentryCurr, lookup currentPart (memory s0) beqAddr = Some(PDT pdentryCurr)).
        {
          apply isPDTLookupEq. apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *;
            intuition.
        }
        destruct HlookupCurrs0 as [pdentryCurr HlookupCurrs0].
        assert(HeqTriv: CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)
          = CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) by reflexivity.
        specialize(HnotShared currentPart pdentryCurr requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) HcurrIsParts0 HlookupCurrs0 HblockMappedCurrs0
          HeqTriv HPDchilds0). destruct Hglob as [Heq | HglobIsChild].
        + rewrite Heq in *. (*nope, not provable*) specialize(HnotShared child addr HchildIsChild HaddrIsNewKern).
          rewrite HgetMappedPEq; trivial.
        + specialize(HnotShared globalIdPD addr HglobIsChild HaddrIsNewKern). rewrite HgetMappedPEq; trivial.
          contradict HnotShared. assert(Hres: childPaddrIsIntoParent s0).
          { apply blockInclImpliesAddrIncl; unfold consistency in *; unfold consistency1 in *; intuition. }
          specialize(Hres globalIdPD child). apply Hres; trivial.
      - rewrite <-beqAddrFalse in *. rewrite HgetConfigPNotGlobEq in *; trivial. apply Himpl; assumption.
     (* END configNotMappedRoot *)
    } *)

    assert(fullKernelIsInOneBlock s).
    { (* BEGIN fullKernelIsInOneBlock s *)
      assert(Hcons0: fullKernelIsInOneBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKS. rewrite HgetPartsEq in *.
      assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *; trivial. assert(Heq: getAllPaddrAux [block] s = getAllPaddrAux [block] s0).
      {
        rewrite Hs. rewrite Hs5. rewrite Hs4. rewrite Hs in HkernInBlock. rewrite Hs5 in HkernInBlock.
        rewrite Hs4 in HkernInBlock. simpl in HkernInBlock. simpl. rewrite beqAddrTrue in *.
        destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(simpl in HkernInBlock; exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite removeDupIdentity in *; auto.
        rewrite removeDupIdentity in *; auto. rewrite Hs3. rewrite Hs3 in HkernInBlock. simpl in HkernInBlock. simpl.
        destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
        {
          rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. apply mappedBlockIsBE in HblockMapped.
          unfold bentryPFlag in *. destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs2 in HkernInBlock. rewrite Hs2.
        simpl in HkernInBlock. simpl. rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HkernInBlock. rewrite Hs1.
        simpl in HkernInBlock. simpl. destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) block)
          eqn:HbeqNextBlock; try(simpl in HkernInBlock; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; auto.
      }
      rewrite Heq in *. assert(HkernIsKSs0: isKS kernel s0).
      {
        unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs5 in HkernIsKS. rewrite Hs4 in HkernIsKS.
        simpl in HkernIsKS. destruct (beqAddr globalIdPD kernel) eqn:HbeqGlobKern; try(exfalso; congruence).
        rewrite beqAddrTrue in *. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        rewrite removeDupIdentity in *; auto. rewrite removeDupIdentity in *; auto. rewrite Hs3 in HkernIsKS.
        simpl in HkernIsKS. destruct (beqAddr lastBlockEntryAddr kernel) eqn:HbeqLastKern.
        - rewrite <-DTL.beqAddrTrue in HbeqLastKern. subst kernel. rewrite HnewBs3 in *. rewrite HlookupLasts0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs2 in HkernIsKS.
          simpl in HkernIsKS. rewrite beqAddrFalse in HbeqGlobKern. rewrite HbeqGlobKern in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HkernIsKS.
          simpl in HkernIsKS. destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) kernel)
            eqn:HbeqNextKern; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKSs0). assumption.
     (* END fullKernelIsInOneBlock *)
    }

    assert(sharedBlocksAdressesAreAllMappedInChild s).
    { (* BEGIN sharedBlocksAdressesAreAllMappedInChild s *)
      assert(Hcons0: sharedBlocksAdressesAreAllMappedInChild s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      intros part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1 HPDchildB Hloc HbeqChildNull
        HbeqLocNull addr HaddrInBlock. rewrite HgetPartsEq in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *; trivial. unfold sh1entryAddr in *. simpl in HaddrInBlock.
      assert(Heq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
      {
        rewrite Hs. rewrite Hs5. rewrite Hs4. rewrite Hs in Hsh1. rewrite Hs5 in Hsh1.
        rewrite Hs4 in Hsh1. simpl in Hsh1. simpl. rewrite beqAddrTrue in *.
        destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite removeDupIdentity in *; auto.
        rewrite removeDupIdentity in *; auto. rewrite Hs3. rewrite Hs3 in Hsh1. simpl in Hsh1. simpl.
        destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
        {
          rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. apply mappedBlockIsBE in HblockMapped.
          unfold bentryPFlag in *. destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs2 in Hsh1. rewrite Hs2.
        simpl in Hsh1. simpl. rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hsh1. rewrite Hs1.
        simpl in Hsh1. simpl. destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) block)
          eqn:HbeqNextBlock; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; auto.
      }
      rewrite Heq in *. unfold sh1entryPDchild in *. unfold sh1entryInChildLocationWeak in *. rewrite Hs in HPDchildB.
      rewrite Hs5 in HPDchildB. rewrite Hs4 in HPDchildB. rewrite Hs in Hloc. rewrite Hs5 in Hloc.
      rewrite Hs4 in Hloc. simpl in HPDchildB. simpl in Hloc. rewrite beqAddrTrue in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite removeDupIdentity in *; auto.
      rewrite removeDupIdentity in *; auto. rewrite Hs3 in HPDchildB. rewrite Hs3 in Hloc. simpl in HPDchildB.
      simpl in Hloc. destruct (beqAddr lastBlockEntryAddr sh1entryaddr) eqn:HbeqLastSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs2 in HPDchildB.
      rewrite Hs2 in Hloc. simpl in HPDchildB. simpl in Hloc. rewrite beqAddrFalse in HbeqGlobSh1.
      rewrite HbeqGlobSh1 in *. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      rewrite Hs1 in HPDchildB. rewrite Hs1 in Hloc. simpl in HPDchildB. simpl in Hloc.
      destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) sh1entryaddr)
        eqn:HbeqNextSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1 HPDchildB Hloc
        HbeqChildNull HbeqLocNull addr HaddrInBlock). rewrite HgetMappedPEq; trivial. unfold getMappedPaddr in *.
      unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
      destruct (lookup child (memory s0) beqAddr); try(simpl in Hcons0; congruence).
      destruct v; try(simpl in Hcons0; congruence). trivial.
     (* END sharedBlocksAdressesAreAllMappedInChild *)
    }

    unfold consistency1. intuition.
  }

  assert(HgetAccMappedBEq: forall part, isPDT part s0
    -> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s0).
  {
    intros part HpartIsPDT. unfold getAccessibleMappedBlocks.
    rewrite HgetMappedBEq; trivial. assert(HpartIsPDTs := HstablePDTs0 part HpartIsPDT). unfold isPDT in *.
    destruct (lookup part (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    destruct (lookup part (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    assert(Heqs1: filterAccessible (getMappedBlocks part s0) s1 = filterAccessible (getMappedBlocks part s0) s0).
    {
      rewrite Hs1. apply filterAccessibleEqPADDR. unfold isPADDR. rewrite HlookupNext. trivial.
    }
    assert(Heqs2: filterAccessible (getMappedBlocks part s0) s2 = filterAccessible (getMappedBlocks part s0) s0).
    {
      rewrite <-Heqs1. rewrite Hs2. apply filterAccessibleEqPDT. unfold isPDT. rewrite HlookupGlobs1. trivial.
    }
    assert(Heqs3: filterAccessible (getMappedBlocks part s0) s3 = filterAccessible (getMappedBlocks part s0) s0).
    {
      rewrite <-Heqs2. rewrite Hs3. apply filterAccessibleEqBEAccessibleNoChange with bentryStart; trivial.
      rewrite HnewBs3. reflexivity.
    }
    assert(Heqs4: filterAccessible (getMappedBlocks part s0) s4 = filterAccessible (getMappedBlocks part s0) s0).
    {
      rewrite <-Heqs3. rewrite Hs4. apply filterAccessibleEqPDT. unfold isPDT. rewrite HlookupGlobs3. trivial.
    }
    assert(Heqs5: filterAccessible (getMappedBlocks part s0) s5 = filterAccessible (getMappedBlocks part s0) s0).
    {
      rewrite <-Heqs4. rewrite Hs5. apply filterAccessibleEqPDT. unfold isPDT. rewrite HlookupGlobs4. trivial.
    }
    rewrite <-Heqs5 in *. rewrite Hs. rewrite filterAccessibleEqPDT; trivial. unfold isPDT. rewrite HlookupGlobs5.
    assumption.
  }

  assert(HgetAccMappedPEq: forall part, isPDT part s0
    -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s0).
  {
    intros part HpartIsPDT. unfold getAccessibleMappedPaddr.
    rewrite HgetAccMappedBEq; trivial.
    assert(Heqs1: getAllPaddrAux (getAccessibleMappedBlocks part s0) s1
      = getAllPaddrAux (getAccessibleMappedBlocks part s0) s0).
    {
      rewrite Hs1. apply getAllPaddrAuxEqPADDR. unfold isPADDR. rewrite HlookupNext. trivial.
    }
    assert(Heqs2: getAllPaddrAux (getAccessibleMappedBlocks part s0) s2
      = getAllPaddrAux (getAccessibleMappedBlocks part s0) s0).
    {
      rewrite <-Heqs1. rewrite Hs2. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupGlobs1. trivial.
    }
    assert(Heqs3: getAllPaddrAux (getAccessibleMappedBlocks part s0) s3
      = getAllPaddrAux (getAccessibleMappedBlocks part s0) s0).
    {
      rewrite <-Heqs2. rewrite Hs3. apply getAllPaddrAuxEqBENoInList. apply BlockNotMappedNotAccessible.
      intro Hcontra. apply mappedBlockIsBE in Hcontra. destruct Hcontra as [bentry (Hlookup & Hcontra)].
      unfold bentryPFlag in *. rewrite Hlookup in *. congruence.
    }
    assert(Heqs4: getAllPaddrAux (getAccessibleMappedBlocks part s0) s4
      = getAllPaddrAux (getAccessibleMappedBlocks part s0) s0).
    {
      rewrite <-Heqs3. rewrite Hs4. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupGlobs3. trivial.
    }
    assert(Heqs5: getAllPaddrAux (getAccessibleMappedBlocks part s0) s5
      = getAllPaddrAux (getAccessibleMappedBlocks part s0) s0).
    {
      rewrite <-Heqs4. rewrite Hs5. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupGlobs4. trivial.
    }
    rewrite <-Heqs5 in *. rewrite Hs. rewrite getAllPaddrAuxEqPDT; trivial. unfold isPDT. rewrite HlookupGlobs5.
    trivial.
  }

  assert(HpresentLookEq: forall block, bentryPFlag block true s
    -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
  {
    intros block HPflag. unfold bentryPFlag in *. rewrite Hs in HPflag. rewrite Hs5 in HPflag. rewrite Hs.
    rewrite Hs4 in HPflag. rewrite Hs5. rewrite Hs4. simpl in HPflag. simpl.
    destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite beqAddrTrue in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPflag. rewrite Hs3. simpl.
    simpl in HPflag. destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
    {
      rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. exfalso. rewrite HnewBs3 in HPflag. simpl in HPflag.
      assert(HltKernEntries: CIndex (kernelStructureEntriesNb-1) < kernelStructureEntriesNb) by lia.
      specialize(HnewFree (CIndex (kernelStructureEntriesNb-1)) HltKernEntries).
      replace (requisitionedBlockStart + (CIndex (kernelStructureEntriesNb-1)))
        with (requisitionedBlockStart+kernelStructureEntriesNb-1) in HnewFree; try(lia).
      rewrite <-HlastBlock in *. unfold isFreeSlot in *. rewrite HlookupLasts0 in *.
      destruct (lookup (CPaddr (lastBlockEntryAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite Hs2 in HPflag. rewrite Hs2. simpl. simpl in HPflag. rewrite beqAddrFalse in HbeqGlobBlock.
    rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPflag. rewrite Hs1. simpl.
    simpl in HPflag. destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
  }

  assert(noDupMappedPaddrList s /\ accessibleParentPaddrIsAccessibleIntoChild s
    /\ adressesRangePreservedIfOriginAndNextOk s /\ childsBlocksPropsInParent s
    /\ noChildImpliesAddressesNotShared s /\ kernelsAreNotAccessible s /\ blockAndNextAreSideBySide s
    /\ parentBlocksBoundsIfNoNext s /\ childLocMappedInChild s /\ childLocHasSameStart s).
  {
    assert(noDupMappedPaddrList s).
    { (* BEGIN noDupMappedPaddrList s *)
      assert(Hcons0: noDupMappedPaddrList s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition HpartIsPDT. apply HstablePDT in HpartIsPDT. specialize(Hcons0 partition HpartIsPDT).
      rewrite HgetMappedPEq; trivial.
      (* END noDupMappedPaddrList *)
    }

    assert(accessibleParentPaddrIsAccessibleIntoChild s).
    { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
      assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
      rewrite HgetPartsEq in *.
      assert(isPDT pdparent s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetAccMappedPEq in HaddrAccMappedParent; trivial.
      assert(isPDT child s0) by (apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition).
      rewrite HgetMappedPEq in HaddrMappedChild; trivial. rewrite HgetAccMappedPEq; trivial.
      specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild).
      assumption.
      (* END accessibleParentPaddrIsAccessibleIntoChild *)
    }

    assert(adressesRangePreservedIfOriginAndNextOk s).
    { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
      assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition pdentryPart block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE
        HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. rewrite HgetPartsEq in *.
      assert(isPDT partition s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      unfold bentryPFlag in *. unfold isBE in *. rewrite HpresentLookEq in HstartBlock; trivial.
      rewrite HpresentLookEq in HendBlock; trivial. rewrite HpresentLookEq in HblockIsBE; trivial.
      rewrite HpresentLookEq in HPflag; trivial.
      unfold scentryNext in *. unfold scentryOrigin in *. rewrite Hs in Horigin. rewrite Hs in Hnext.
      rewrite Hs5 in Horigin. rewrite Hs5 in Hnext. rewrite Hs4 in Horigin. rewrite Hs4 in Hnext. simpl in Horigin.
      simpl in Hnext. destruct (beqAddr globalIdPD scentryaddr) eqn:HbeqGlobSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite beqAddrTrue in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in Horigin. rewrite Hs3 in Hnext.
      simpl in Horigin. simpl in Hnext.
      destruct (beqAddr lastBlockEntryAddr scentryaddr) eqn:HbeqLastSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in Hnext. rewrite Hs2 in Horigin. simpl in Horigin. simpl in Hnext.
      rewrite beqAddrFalse in HbeqGlobSce. rewrite HbeqGlobSce in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in Hnext. rewrite Hs1 in Horigin.
      simpl in Horigin. simpl in Hnext.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) scentryaddr) eqn:HbeqNextSce;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(HlookupParts0 := HpartFieldsEq partition pdentryPart HlookupPart).
      destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentsEq & _)]. rewrite <-HparentsEq.
      specialize(Hcons0 partition pdentryParts0 block scentryaddr startBlock endBlock HpartIsPart HblockMapped
        HblockIsBE HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupParts0 HbeqPartRoot).
      destruct Hcons0 as [blockParent (HblockParentMapped & HblockParentIsBE & HstartParent & HendParent)].
      exists blockParent. assert(isPDT (parent pdentryParts0) s0).
      {
        unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
        destruct (lookup (parent pdentryParts0) (memory s0) beqAddr); try(simpl in HblockParentMapped; congruence).
        destruct v; try(simpl in HblockParentMapped; congruence). trivial.
      }
      rewrite <-HgetMappedBEq in HblockParentMapped; trivial.
      assert(bentryPFlag blockParent true s).
      {
        apply mappedBlockIsBE in HblockParentMapped. unfold bentryPFlag.
        destruct HblockParentMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup. auto.
      }
      rewrite HpresentLookEq; trivial. auto.
      (* END adressesRangePreservedIfOriginAndNextOk *)
    }

    assert(childsBlocksPropsInParent s).
    { (* BEGIN childsBlocksPropsInParent s *)
      assert(Hcons0: childsBlocksPropsInParent s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
        HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
        HPflagParent HlebStart HgebEnd. rewrite HgetPartsEq in *.
      assert(isPDT pdparent s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetMappedBEq in HblockParentMapped; trivial.
      assert(isPDT child s0) by (apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition).
      rewrite HgetMappedBEq in HblockChildMapped; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      assert(HlookupChildEq:= HpresentLookEq blockChild HPflagChild). unfold bentryPFlag in *. unfold bentryAFlag.
      assert(HlookupParentEq:= HpresentLookEq blockParent HPflagParent). unfold checkChild.
      rewrite HlookupChildEq in *. rewrite HlookupParentEq in *.
      specialize(Hcons0 child pdparent blockChild startChild endChild blockParent
        startParent endParent HparentIsPart HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild
        HblockParentMapped HstartParent HendParent HPflagParent HlebStart HgebEnd).
      destruct Hcons0 as (HcheckChild & HPDchildB & HinChildLoc & HAflag).
      assert(HlookupSh1ParentEq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
        = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
      {
        apply HlookupSh1Eq.
        assert(HwellFormedSh1: wellFormedFstShadowIfBlockEntry s0) by (unfold consistency1 in *; intuition).
        apply HwellFormedSh1. unfold isBE.
        destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence). trivial.
      }
      unfold sh1entryPDchild. unfold sh1entryInChildLocation. rewrite HlookupSh1ParentEq.
      split; try(split; try(split)); trivial. intros blockIDInChild HchildLoc.
      assert(HchildLocs0: sh1entryInChildLocation (CPaddr (blockParent + sh1offset)) blockIDInChild s0).
      {
        unfold sh1entryInChildLocation.
        destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). destruct HchildLoc as (HlocEq & HlocIsBE). split; trivial. intro HlocNotNull.
        specialize(HlocIsBE HlocNotNull). unfold isBE in *.
        destruct (lookup blockIDInChild (memory s) beqAddr) eqn:HlookupLoc; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply HblockFieldsEqs in HlookupLoc.
        destruct HlookupLoc as [bentry (HlookupLocs0 & _)]. rewrite HlookupLocs0. trivial.
      }
      specialize(HinChildLoc blockIDInChild HchildLocs0). assumption.
      (* END childsBlocksPropsInParent *)
    }

    assert(noChildImpliesAddressesNotShared s).
    { (* BEGIN noChildImpliesAddressesNotShared s *)
      assert(Hcons0: noChildImpliesAddressesNotShared s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition pdentryPart block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchildB child addr
        HchildIsChild HaddrInBlock. rewrite HgetPartsEq in *.
      assert(isPDT partition s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      assert(HlookupParts0 := HpartFieldsEq partition pdentryPart HlookupPart).
      assert(bentryPFlag block true s).
      {
        unfold bentryPFlag. apply mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup. auto.
      }
      destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & _)]. rewrite HgetMappedBEq in HblockMapped; trivial.
      unfold sh1entryPDchild in *. assert(isSHE sh1entryaddr s).
      {
        unfold isSHE. destruct (lookup sh1entryaddr (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      rewrite HsheEq in HPDchildB; trivial. rewrite HgetChildrenEq in HchildIsChild; trivial.
      assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
      {
        simpl. simpl in HaddrInBlock. rewrite <-HpresentLookEq; trivial.
      }
      specialize(Hcons0 partition pdentryParts0 block sh1entryaddr HpartIsPart HlookupParts0 HblockMapped Hsh1
        HPDchildB child addr HchildIsChild HaddrInBlocks0).
      assert(isPDT child s0) by (apply childrenArePDT with partition; trivial; unfold consistency1 in *; intuition).
      rewrite HgetMappedPEq; trivial.
      (* END noChildImpliesAddressesNotShared *)
    }

    assert(kernelsAreNotAccessible s).
    { (* BEGIN kernelsAreNotAccessible s *)
      assert(Hcons0: kernelsAreNotAccessible s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros block startaddr part HpartIsPart HblockMapped Hstart HstartBlockIsKS.
      rewrite HgetPartsEq in *. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      assert(HPflag: bentryPFlag block true s).
      {
        apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
        unfold bentryPFlag. rewrite Hlookup. auto.
      }
      rewrite HgetMappedBEq in *; trivial. assert(HlookupBlockEq:= HpresentLookEq block HPflag).
      unfold bentryStartAddr in *. unfold bentryPFlag in *. unfold bentryAFlag. rewrite HlookupBlockEq in *.
      assert(HstartBlockIsKSs0: isKS startaddr s0).
      {
        unfold isKS in *. destruct (lookup startaddr (memory s) beqAddr) eqn:HlookupStart; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply HblockFieldsEqs in HlookupStart.
        destruct HlookupStart as [bentry (HlookupStart & _ & _ & _ & _ & _ & HblkidxEq & _)]. rewrite HlookupStart.
        rewrite HblkidxEq. assumption.
      }
      specialize(Hcons0 block startaddr part HpartIsPart HblockMapped Hstart HstartBlockIsKSs0). assumption.
      (* END kernelsAreNotAccessible *)
    }

    assert(HlookupSceRev: forall addr, isSCE addr s
      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
    {
      intros addr HaddrIsSCE. unfold isSCE in *. rewrite Hs. rewrite Hs in HaddrIsSCE. rewrite Hs5 in HaddrIsSCE.
      rewrite Hs5. rewrite Hs4. rewrite Hs4 in HaddrIsSCE. simpl in HaddrIsSCE. simpl. rewrite beqAddrTrue in *.
      destruct (beqAddr globalIdPD addr) eqn:HbeqGlobAddr; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HaddrIsSCE. rewrite Hs3. simpl.
      simpl in HaddrIsSCE. destruct (beqAddr lastBlockEntryAddr addr) eqn:HbeqBlockAddr; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2.
      rewrite Hs2 in HaddrIsSCE. simpl. simpl in HaddrIsSCE. rewrite beqAddrFalse in *. rewrite HbeqGlobAddr in *.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1.
      rewrite Hs1 in HaddrIsSCE. simpl. simpl in HaddrIsSCE.
      destruct (beqAddr (CPaddr(requisitionedBlockStart+nextoffset)) addr) eqn:HbeqNextAddr; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }

    assert(blockAndNextAreSideBySide s).
    { (* BEGIN blockAndNextAreSideBySide s *)
      assert(Hcons0: blockAndNextAreSideBySide s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
        Hnext. rewrite HgetPartsEq in *. assert(isPDT partition s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      assert(HendBlockBiss0: bentryEndAddr block endaddr s0).
      {
        unfold bentryEndAddr in *. rewrite <-HpresentLookEq; trivial.
        apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBlock & Hpres)].
        unfold bentryPFlag. rewrite HlookupBlock. auto.
      }
      rewrite HgetMappedBEq in *; trivial. assert(isSCE scentryaddr s).
      {
        unfold scentryNext in *. unfold isSCE. destruct (lookup scentryaddr (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      unfold scentryNext in *. rewrite HlookupSceRev in Hnext; trivial.
      specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlockBiss0 Hsce
        HbeqNextNull Hnext). destruct Hcons0 as (Hcons0 & HnextMapped). split; trivial. unfold bentryStartAddr in *.
      destruct (lookup scnext (memory s0) beqAddr) eqn:HlookupScnext; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      apply HblockFieldsEq in HlookupScnext.
      destruct HlookupScnext as [bentry (HlookupScnext & _ & _ & _ & _ & _ & _ & HstartsEq)]. rewrite HlookupScnext.
      rewrite HstartsEq. assumption.
      (* END blockAndNextAreSideBySide *)
    }

    assert(parentBlocksBoundsIfNoNext s).
    { (* BEGIN parentBlocksBoundsIfNoNext s *)
      assert(Hcons0: parentBlocksBoundsIfNoNext s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros partition pdentryPart block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock HendBlock
        Hsce Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEq in *. assert(isPDT partition s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite <-HpresentLookEq; auto.
        apply mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (HlookupBlock & Hpres)].
        unfold bentryPFlag. rewrite HlookupBlock. auto.
      }
      destruct Hblocks0 as (HstartBlockBiss0 & HendBlockBiss0). rewrite HgetMappedBEq in HblockMapped; trivial.
      assert(isSCE scentryaddr s).
      {
        unfold scentryNext in *. unfold isSCE. destruct (lookup scentryaddr (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      unfold scentryNext in *. rewrite HlookupSceRev in Hnext; trivial. apply HpartFieldsEq in HlookupPart.
      destruct HlookupPart as [pdentryParts0 (HlookupParts0 & HparentsEq & _)]. rewrite <-HparentsEq.
      specialize(Hcons0 partition pdentryParts0 block scentryaddr startaddr endaddr HpartIsPart HblockMapped
        HstartBlockBiss0 HendBlockBiss0 Hsce Hnext HbeqPartRoot HlookupParts0).
      destruct Hcons0 as [blockParent [startP (HblockPMapped & HstartP & HendP & HlebStarts)]]. exists blockParent.
      exists startP. assert(HblockPMappeds: In blockParent (getMappedBlocks (parent pdentryParts0) s)).
      {
        rewrite HgetMappedBEq; trivial. unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
        destruct (lookup (parent pdentryParts0) (memory s0) beqAddr); try(simpl in HblockPMapped; congruence).
        destruct v; try(simpl in HblockPMapped; congruence). trivial.
      }
      split; trivial. unfold bentryStartAddr. unfold bentryEndAddr. rewrite HpresentLookEq; auto. unfold bentryPFlag.
      apply mappedBlockIsBE in HblockPMappeds. destruct HblockPMappeds as [bentry (HlookupBP & Hpres)].
      rewrite HlookupBP. auto.
      (* END parentBlocksBoundsIfNoNext *)
    }

    assert(childLocMappedInChild s).
    { (* BEGIN childLocMappedInChild s *)
      assert(Hcons0: childLocMappedInChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1 HPDchildB Hloc
        HbeqIdChildNull Hstart HstartNotKern. rewrite HgetPartsEq in *. unfold sh1entryInChildLocationWeak in *.
      unfold bentryStartAddr in Hstart. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryPDchild in *. unfold sh1entryAddr in *.
      rewrite Hs in Hloc. rewrite Hs in Hstart. rewrite Hs5 in Hstart. rewrite Hs4 in Hstart.
      simpl in Hstart. rewrite Hs5 in Hloc. rewrite Hs4 in Hloc. simpl in Hloc.
      rewrite Hs in HPDchildB. rewrite Hs in Hsh1. rewrite Hs5 in HPDchildB. rewrite Hs4 in HPDchildB.
      rewrite Hs5 in Hsh1. rewrite Hs4 in Hsh1. simpl in HPDchildB. simpl in Hsh1. rewrite beqAddrTrue in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPDchildB. simpl in HPDchildB.
      rewrite Hs3 in Hsh1. simpl in Hsh1. rewrite Hs3 in Hloc. simpl in Hloc. rewrite Hs3 in Hstart. simpl in Hstart.
      destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. apply mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag in *. rewrite Hlookup in *.
        exfalso; congruence.
      }
      destruct (beqAddr lastBlockEntryAddr sh1entryaddr) eqn:HbeqLastSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HPDchildB. simpl in HPDchildB. rewrite Hs2 in Hsh1. simpl in Hsh1. rewrite Hs2 in Hloc.
      simpl in Hloc. rewrite Hs2 in Hstart. simpl in Hstart.
      rewrite beqAddrFalse in *. rewrite HbeqGlobSh1 in *. rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPDchildB. simpl in HPDchildB.
      rewrite Hs1 in Hsh1. simpl in Hsh1. rewrite Hs1 in Hloc. simpl in Hloc. rewrite Hs1 in Hstart. simpl in Hstart.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) sh1entryaddr) eqn:HbeqNextSh1;
        try(exfalso; congruence).
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(HstartNotKSs0: ~isKS startaddr s0).
      {
        unfold isKS in *. contradict HstartNotKern. rewrite Hs. rewrite Hs5. rewrite Hs4. simpl. rewrite beqAddrTrue.
        destruct (beqAddr globalIdPD startaddr) eqn:HbeqGlobStart.
        { rewrite <-DTL.beqAddrTrue in HbeqGlobStart. subst startaddr. rewrite HlookupGlobs0 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
        destruct (beqAddr lastBlockEntryAddr startaddr) eqn:HbeqLastStart.
        - rewrite <-DTL.beqAddrTrue in HbeqLastStart. subst startaddr. rewrite HlookupLasts0 in *. rewrite HnewBs3.
          auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
          rewrite beqAddrFalse in *. rewrite HbeqGlobStart. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) startaddr) eqn:HbeqNextStart.
          { rewrite <-DTL.beqAddrTrue in HbeqNextStart. subst startaddr. rewrite HlookupNext in *. congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1
        HPDchildB Hloc HbeqIdChildNull Hstart HstartNotKSs0).
      destruct Hcons0 as (HbeqBCNull & HBCMapped & HstartsChild). split; trivial.
      assert(In blockChild (getMappedBlocks idchild s)).
      {
        rewrite HgetMappedBEq; trivial. unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
        destruct (lookup idchild (memory s0) beqAddr); try(simpl in HBCMapped; congruence).
        destruct v; try(simpl in HBCMapped; congruence). trivial.
      }
      split; trivial. unfold bentryStartAddr in *.
      rewrite Hs. rewrite Hs5. rewrite Hs4. simpl. rewrite beqAddrTrue.
      destruct (beqAddr globalIdPD blockChild) eqn:HbeqGlobBC.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobBC. subst blockChild. rewrite HlookupGlobs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr blockChild) eqn:HbeqLastBC.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBC. subst blockChild. apply mappedBlockIsBE in HBCMapped.
        destruct HBCMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag in *. rewrite Hlookup in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqGlobBC. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) blockChild) eqn:HbeqNextBC.
      { rewrite <-DTL.beqAddrTrue in HbeqNextBC. subst blockChild. rewrite HlookupNext in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END childLocMappedInChild *)
    }

    assert(childLocHasSameStart s).
    { (* BEGIN childLocHasSameStart s *)
      assert(Hcons0: childLocHasSameStart s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
      intros part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1 HPDchildB Hloc
        HbeqIdChildNull HbeqBCNull. rewrite HgetPartsEq in *.
      unfold sh1entryInChildLocationWeak in *. unfold bentryStartAddr at 1. assert(isPDT part s0).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryPDchild in *. unfold sh1entryAddr in *.
      rewrite Hs in Hloc. rewrite Hs5 in Hloc. rewrite Hs4 in Hloc. simpl in Hloc. rewrite Hs. simpl. rewrite <-Hs.
      rewrite Hs5. rewrite Hs4. simpl.
      rewrite Hs in HPDchildB. rewrite Hs in Hsh1. rewrite Hs5 in HPDchildB. rewrite Hs4 in HPDchildB.
      rewrite Hs5 in Hsh1. rewrite Hs4 in Hsh1. simpl in HPDchildB. simpl in Hsh1. rewrite beqAddrTrue in *.
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso; congruence).
      destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3 in HPDchildB. simpl in HPDchildB.
      rewrite Hs3 in Hsh1. simpl in Hsh1. rewrite Hs3 in Hloc. simpl in Hloc. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr block) eqn:HbeqLastBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBlock. subst block. apply mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag in *. rewrite Hlookup in *.
        exfalso; congruence.
      }
      destruct (beqAddr lastBlockEntryAddr sh1entryaddr) eqn:HbeqLastSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      rewrite Hs2 in HPDchildB. simpl in HPDchildB. rewrite Hs2 in Hsh1. simpl in Hsh1. rewrite Hs2 in Hloc.
      simpl in Hloc. rewrite Hs2. simpl.
      rewrite beqAddrFalse in *. rewrite HbeqGlobSh1 in *. rewrite HbeqGlobBlock in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1 in HPDchildB. simpl in HPDchildB.
      rewrite Hs1 in Hsh1. simpl in Hsh1. rewrite Hs1 in Hloc. simpl in Hloc. rewrite Hs1. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) sh1entryaddr) eqn:HbeqNextSh1;
        try(exfalso; congruence).
      destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) block) eqn:HbeqNextBlock;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1 HPDchildB
        Hloc HbeqIdChildNull HbeqBCNull). destruct Hcons0 as (HsameStart & HBCMapped). assert(isPDT idchild s0).
      {
        unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
        destruct (lookup idchild (memory s0) beqAddr); try(simpl in HBCMapped; congruence).
        destruct v; try(simpl in HBCMapped; congruence). trivial.
      }
      rewrite HgetMappedBEq; trivial. split; trivial.
      intros startaddr Hstart. specialize(HsameStart startaddr Hstart). unfold bentryStartAddr in *.
      rewrite Hs. rewrite Hs5. rewrite Hs4. simpl. rewrite beqAddrTrue.
      destruct (beqAddr globalIdPD blockChild) eqn:HbeqGlobBC.
      {
        rewrite <-DTL.beqAddrTrue in HbeqGlobBC. subst blockChild. rewrite HlookupGlobs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs3. simpl.
      destruct (beqAddr lastBlockEntryAddr blockChild) eqn:HbeqLastBC.
      - rewrite <-DTL.beqAddrTrue in HbeqLastBC. subst blockChild. rewrite HlookupLasts0 in *. rewrite HnewBs3.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
        rewrite beqAddrFalse in *. rewrite HbeqGlobBC. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockStart + nextoffset)) blockChild) eqn:HbeqNextBC.
        { rewrite <-DTL.beqAddrTrue in HbeqNextBC. subst blockChild. rewrite HlookupNext in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END childLocHasSameStart *)
    }

    intuition.
  }

  assert(HpartialShared: forall pdarent child addr parentblock sh1entryaddr,
    child <> globalIdPD
    -> In pdarent (getPartitions multiplexer s)
    -> In child (getChildren pdarent s)
    -> In addr (getUsedPaddr child s)
    -> In addr (getAllPaddrAux [parentblock] s)
    -> In parentblock (getMappedBlocks pdarent s)
    -> sh1entryAddr parentblock sh1entryaddr s
    -> sh1entryPDchild (CPaddr (parentblock + sh1offset)) child s
        \/ sh1entryPDflag (CPaddr (parentblock + sh1offset)) true s).
  { (* BEGIN sharedBlockPointsToChild s *)
    assert(Hcons0: sharedBlockPointsToChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros pdparent child addr blockParent sh1entryaddr HbeqGlobChild HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParent HblockParentMapped Hsh1. rewrite HgetPartsEq in *.
    assert(isPDT pdparent s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    assert(bentryPFlag blockParent true s).
    {
      unfold bentryPFlag. apply mappedBlockIsBE in HblockParentMapped.
      destruct HblockParentMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup. auto.
    }
    rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetMappedBEq in HblockParentMapped; trivial.
    assert(HaddrInBlockParents0: In addr (getAllPaddrAux [blockParent] s0)).
    { simpl. simpl in HaddrInBlockParent. rewrite <-HpresentLookEq; trivial. }
    unfold sh1entryAddr in *. rewrite HpresentLookEq in Hsh1; trivial. unfold getUsedPaddr in HaddrUsedChild.
    assert(isPDT child s0) by (apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition).
    rewrite HgetConfigPNotGlobEq in HaddrUsedChild; trivial. rewrite HgetMappedPEq in HaddrUsedChild; trivial.
    specialize(Hcons0 pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParents0 HblockParentMapped Hsh1). unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
    assert(isSHE (CPaddr (blockParent + sh1offset)) s0).
    {
      unfold isSHE.
      destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr); try(intuition; congruence).
      destruct v; intuition.
    }
    rewrite HlookupSh1Eq; trivial.
    (* END sharedBlockPointsToChild *)
  }

  assert(beqAddr globalIdPD currentPart = true -> sharedBlockPointsToChild s).
  {
    intro HbeqGlobCurr. rewrite <-DTL.beqAddrTrue in HbeqGlobCurr. rewrite <-HbeqGlobCurr in *.
    assert(Hcons0: sharedBlockPointsToChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParent HblockParentMapped Hsh1.
    destruct (beqAddr child globalIdPD) eqn:HbeqChildGlob.
    - rewrite <-DTL.beqAddrTrue in HbeqChildGlob. subst child. rewrite HgetPartsEq in *.
      assert(isPDT pdparent s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      assert(bentryPFlag blockParent true s).
      {
        unfold bentryPFlag. apply mappedBlockIsBE in HblockParentMapped.
        destruct HblockParentMapped as [bentry (Hlookup & Hpres)]. rewrite Hlookup. auto.
      }
      rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetMappedBEq in HblockParentMapped; trivial.
      assert(HaddrInBlockParents0: In addr (getAllPaddrAux [blockParent] s0)).
      { simpl. simpl in HaddrInBlockParent. rewrite <-HpresentLookEq; trivial. }
      unfold sh1entryAddr in *. rewrite HpresentLookEq in Hsh1; trivial.
      assert(HaddrUsedChilds0: In addr (getUsedPaddr globalIdPD s0)).
      {
        unfold getUsedPaddr in *. rewrite HgetMappedPEq in HaddrUsedChild; trivial. unfold getConfigPaddr in *.
        rewrite HgetConfigPPartial1GlobEqs in *. rewrite HgetConfigGlobEq in *. apply in_app_or in HaddrUsedChild.
        apply in_or_app. destruct HaddrUsedChild as [HaddrConfigChild | HaddrMappedChild]; try(right; assumption).
        apply in_app_or in HaddrConfigChild. destruct HaddrConfigChild as [HaddrPDT | HaddrConfigChild];
          try(left; apply in_or_app; left; assumption). rewrite HgetConfigPPartial2GlobEqs in HaddrConfigChild.
        apply in_app_or in HaddrConfigChild.
        destruct HaddrConfigChild as [HaddrNew | HaddrConfigChilds0]; try(left; apply in_or_app; right; assumption).
        right. apply addrInBlockIsMapped with requisitionedBlockInCurrPartAddr; trivial. simpl.
        unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0. apply in_or_app. left.
        unfold StateLib.Index.ltb in *. apply eq_sym in HltSizeTot. apply PeanoNat.Nat.ltb_ge in HltSizeTot.
        subst kStructureTotalLength. apply getAllPaddrBlockInclRevAux in HaddrNew.
        destruct HaddrNew as (HlebStartAddr & HltAddrLen & _). apply getAllPaddrBlockIncl; lia.
      }
      specialize(Hcons0 pdparent globalIdPD addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChilds0
        HaddrInBlockParents0 HblockParentMapped Hsh1). unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
      assert(isSHE (CPaddr (blockParent + sh1offset)) s0).
      {
        unfold isSHE.
        destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr); try(intuition; congruence).
        destruct v; intuition.
      }
      rewrite HlookupSh1Eq; trivial.
    - rewrite <-beqAddrFalse in *. apply HpartialShared with pdparent addr sh1entryaddr; assumption.
  }

  assert(verticalSharing s /\ partitionsIsolation s /\ kernelDataIsolation s).
  {
    assert(verticalSharing s).
    { (* BEGIN verticalSharing s *)
      intros pdparent child HparentIsPart HchildIsChild. rewrite HgetPartsEq in *.
      assert(isPDT pdparent s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in HchildIsChild; trivial.
      assert(isPDT child s0) by (apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition).
      specialize(HVSs0 pdparent child HparentIsPart HchildIsChild). rewrite HgetMappedPEq; trivial.
      intros addr HaddrUsedChild.
      assert(HpropsOrAddr: In addr (getUsedPaddr child s0) \/ In addr (getMappedPaddr pdparent s0)).
      {
        unfold getUsedPaddr in *. rewrite HgetMappedPEq in HaddrUsedChild; trivial.
        destruct (beqAddr child globalIdPD) eqn:HbeqChildGlob.
        - rewrite <-DTL.beqAddrTrue in HbeqChildGlob. subst child. apply in_app_or in HaddrUsedChild.
          destruct HaddrUsedChild as [Hconfig | Hmapped]; try(left; apply in_or_app; right; assumption).
          unfold getConfigPaddr in *. rewrite HgetConfigPPartial1GlobEqs in *.
          rewrite HgetConfigPPartial2GlobEqs in *. apply in_app_or in Hconfig.
          destruct Hconfig as [HaddrPDT | HconfigRight]; try(left; apply in_or_app; left; apply in_or_app; left;
            assumption). apply in_app_or in HconfigRight.
          destruct HconfigRight as [HaddrNew | Hconfig]; try(left; apply in_or_app; left; apply in_or_app; right;
            assumption). destruct Hglob as [HcurrIsGlob | HglobIdChild].
          + rewrite HcurrIsGlob in *. left. apply in_or_app. right.
            apply addrInBlockIsMapped with requisitionedBlockInCurrPartAddr; try(assumption). simpl.
            unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0. apply in_or_app.
            left. unfold StateLib.Index.ltb in *. apply eq_sym in HltSizeTot. apply PeanoNat.Nat.ltb_ge in HltSizeTot.
            subst kStructureTotalLength. apply getAllPaddrBlockInclRevAux in HaddrNew.
            destruct HaddrNew as (HlebStartAddr & HltAddrLen & _). apply getAllPaddrBlockIncl; lia.
          + right. assert(HparentsEq: pdparent = currentPart).
            {
              apply uniqueParent with globalIdPD s0; try(assumption).
              1,2: unfold consistency in *; unfold consistency1 in *; intuition.
              apply childrenPartitionInPartitionList with pdparent; try(assumption).
              unfold consistency in *; unfold consistency1 in *; intuition.
            }
            subst pdparent. apply addrInBlockIsMapped with requisitionedBlockInCurrPartAddr; try(assumption). simpl.
            unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0. apply in_or_app.
            left. unfold StateLib.Index.ltb in *. apply eq_sym in HltSizeTot.
            apply PeanoNat.Nat.ltb_ge in HltSizeTot. subst kStructureTotalLength.
            apply getAllPaddrBlockInclRevAux in HaddrNew. destruct HaddrNew as (HlebStartAddr & HltAddrLen & _).
            apply getAllPaddrBlockIncl; lia.
        - rewrite <-beqAddrFalse in *. left. rewrite <-HgetConfigPNotGlobEq; assumption.
      }
      destruct HpropsOrAddr as [HaddrUsedChilds0 | Hres]; try(assumption). apply HVSs0; assumption.
      (* END verticalSharing *)
    }

    assert(partitionsIsolation s).
    { (* BEGIN partitionsIsolation s *)
      intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
      rewrite HgetPartsEq in *.
      assert(isPDT pdparent s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in Hchild1IsChild; trivial. rewrite HgetChildrenEq in Hchild2IsChild; trivial.
      specialize(HPIs0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
      assert(isPDT child1 s0) by (apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition).
      assert(isPDT child2 s0) by (apply childrenArePDT with pdparent; trivial; unfold consistency1 in *; intuition).
      unfold getUsedPaddr in *. rewrite HgetMappedPEq; trivial. rewrite HgetMappedPEq; trivial.
      intros addr HaddrUsedChild1. destruct (beqAddr child1 globalIdPD) eqn:HbeqChild1Glob.
      - rewrite <-DTL.beqAddrTrue in HbeqChild1Glob. subst child1. apply not_eq_sym in HbeqChildren.
        rewrite HgetConfigPNotGlobEq; trivial.
        assert(HpropsOrAddr: In addr (getUsedPaddr globalIdPD s0) \/ ~ In addr (getUsedPaddr child2 s0)).
        {
          unfold getUsedPaddr. unfold getConfigPaddr in HaddrUsedChild1. unfold getConfigPaddr at 1.
          rewrite HgetConfigPPartial1GlobEqs in *. rewrite HgetConfigPPartial2GlobEqs in *.
          apply in_app_or in HaddrUsedChild1. destruct HaddrUsedChild1 as [Hconfig | Hmapped];
            try(left; apply in_or_app; right; assumption). apply in_app_or in Hconfig.
          destruct Hconfig as [HaddrPDT | HconfigRight]; try(left; apply in_or_app; left; apply in_or_app; left;
            assumption). apply in_app_or in HconfigRight.
          destruct HconfigRight as [HaddrNew | HconfigRight]; try(left; apply in_or_app; left; apply in_or_app; right;
            assumption). destruct Hglob as [HcurrIsGlob | HglobIdChild].
          + rewrite HcurrIsGlob in *. left. apply in_or_app. right.
            apply addrInBlockIsMapped with requisitionedBlockInCurrPartAddr; try(assumption). simpl.
            unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0. apply in_or_app.
            left. unfold StateLib.Index.ltb in *. apply eq_sym in HltSizeTot. apply PeanoNat.Nat.ltb_ge in HltSizeTot.
            subst kStructureTotalLength. apply getAllPaddrBlockInclRevAux in HaddrNew.
            destruct HaddrNew as (HlebStartAddr & HltAddrLen & _). apply getAllPaddrBlockIncl; lia.
          + right. assert(HparentsEq: pdparent = currentPart).
            {
              apply uniqueParent with globalIdPD s0; try(assumption).
              1,2: unfold consistency in *; unfold consistency1 in *; intuition.
              apply childrenPartitionInPartitionList with pdparent; try(assumption).
              unfold consistency in *; unfold consistency1 in *; intuition.
            }
            subst pdparent. intro Hcontra.
            assert(HaddrInReq: In addr (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)).
            {
              simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
              destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0. apply in_or_app.
              left. unfold StateLib.Index.ltb in *. apply eq_sym in HltSizeTot.
              apply PeanoNat.Nat.ltb_ge in HltSizeTot. subst kStructureTotalLength.
              apply getAllPaddrBlockInclRevAux in HaddrNew. destruct HaddrNew as (HlebStartAddr & HltAddrLen & _).
              apply getAllPaddrBlockIncl; lia.
            }
            assert(Hsh1: sh1entryAddr requisitionedBlockInCurrPartAddr
              (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) s0).
            {
              unfold sh1entryAddr. unfold bentryStartAddr in *.
              destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence).
            }
            specialize(Hshareds0 currentPart child2 addr requisitionedBlockInCurrPartAddr
              (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) HcurrIsParts0 Hchild2IsChild Hcontra HaddrInReq
              HblockMappedCurrs0 Hsh1). unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s0) beqAddr);
              try(congruence). destruct v; try(congruence). rewrite <-HPDchilds0 in *.
            destruct Hshareds0 as [HcontraChild | HcontraFlag]; try(congruence). subst child2.
            assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
            unfold isPDT in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
        }
        destruct HpropsOrAddr as [HaddrUsedChild1s0 | Hres]; try(assumption). apply HPIs0; assumption.
      - rewrite <-beqAddrFalse in *. rewrite HgetConfigPNotGlobEq in HaddrUsedChild1; try(assumption).
        specialize(HPIs0 addr HaddrUsedChild1). destruct (beqAddr child2 globalIdPD) eqn:HbeqChild2Glob.
        + rewrite <-DTL.beqAddrTrue in HbeqChild2Glob. subst child2. unfold getConfigPaddr.
          rewrite HgetConfigPPartial1GlobEqs. rewrite HgetConfigPPartial2GlobEqs. apply Lib.in_app_or_neg in HPIs0.
          apply Lib.in_or_app_neg. destruct HPIs0 as (HaddrNotConfigG & HaddrNotMappedG). split; try(assumption).
          apply Lib.in_or_app_neg. unfold getConfigPaddr in HaddrNotConfigG.
          apply Lib.in_app_or_neg in HaddrNotConfigG. destruct HaddrNotConfigG as (HaddrNotPDTG & HaddrNotConfigG).
          split; try(assumption). apply Lib.in_or_app_neg. split; try(assumption). intro Hcontra.
          assert(HaddrInReq: In addr (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)).
          {
            simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0. apply in_or_app.
            left. unfold StateLib.Index.ltb in *. apply eq_sym in HltSizeTot.
            apply PeanoNat.Nat.ltb_ge in HltSizeTot. subst kStructureTotalLength.
            apply getAllPaddrBlockInclRevAux in Hcontra. destruct Hcontra as (HlebStartAddr & HltAddrLen & _).
            apply getAllPaddrBlockIncl; lia.
          }
          destruct Hglob as [HcurrIsGlob | HglobIsChild].
          * rewrite HcurrIsGlob in *. contradict HaddrNotMappedG.
            apply addrInBlockIsMapped with requisitionedBlockInCurrPartAddr; assumption.
          * assert(Hsh1: sh1entryAddr requisitionedBlockInCurrPartAddr
              (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) s0).
            {
              unfold sh1entryAddr. unfold bentryStartAddr in *.
              destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence).
            }
            assert(HparentsEq: pdparent = currentPart).
            {
              apply uniqueParent with globalIdPD s0; try(assumption).
              1,2: unfold consistency in *; unfold consistency1 in *; intuition.
              apply childrenPartitionInPartitionList with pdparent; try(assumption).
              unfold consistency in *; unfold consistency1 in *; intuition.
            }
            subst pdparent. specialize(Hshareds0 currentPart child1 addr requisitionedBlockInCurrPartAddr
              (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) HparentIsPart Hchild1IsChild HaddrUsedChild1
              HaddrInReq HblockMappedCurrs0 Hsh1). unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s0) beqAddr);
              try(congruence). destruct v; try(congruence). rewrite <-HPDchilds0 in *.
            destruct Hshareds0 as [HcontraChild | HcontraFlag]; try(congruence). subst child1.
            assert(Hnull: isPADDR nullAddr s0) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
            unfold isPDT in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
        + rewrite <-beqAddrFalse in *. rewrite HgetConfigPNotGlobEq; assumption.
      (* END partitionsIsolation *)
    }

    assert(kernelDataIsolation s).
    { (* BEGIN kernelDataIsolation s *)
      intros part1 part2 Hpart1IsPart Hpart2IsPart. rewrite HgetPartsEq in *.
      assert(isPDT part1 s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      assert(isPDT part2 s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      specialize(HKDIs0 part1 part2 Hpart1IsPart Hpart2IsPart). rewrite HgetAccMappedPEq; trivial.
      destruct (beqAddr part2 globalIdPD) eqn:HbeqPart2Glob.
      - rewrite <-DTL.beqAddrTrue in HbeqPart2Glob. subst part2. intros addr HaddrAccPart1.
        specialize(HKDIs0 addr HaddrAccPart1). unfold getConfigPaddr in *. rewrite HgetConfigPPartial1GlobEqs.
        rewrite HgetConfigPPartial2GlobEqs. apply Lib.in_app_or_neg in HKDIs0.
        apply Lib.in_or_app_neg. destruct HKDIs0 as (HaddrNotPDTG & HaddrNotConfigG). split; try(assumption).
        apply Lib.in_or_app_neg. split; try(assumption). intro Hcontra.
        assert(HaddrInReq: In addr (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)).
        {
          simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0. apply in_or_app.
          left. unfold StateLib.Index.ltb in *. apply eq_sym in HltSizeTot.
          apply PeanoNat.Nat.ltb_ge in HltSizeTot. subst kStructureTotalLength.
          apply getAllPaddrBlockInclRevAux in Hcontra. destruct Hcontra as (HlebStartAddr & HltAddrLen & _).
          apply getAllPaddrBlockIncl; lia.
        }
        assert(Hbloodline: In part1 (currentPart::filterOptionPaddr (completeParentsList currentPart s0))).
        {
          assert(In addr (getMappedPaddr part1 s0)) by (apply addrInAccessibleMappedIsIsMappedPaddr; assumption).
          apply addressesBloodlineIfNotShared with addr requisitionedBlockInCurrPartAddr; try(assumption);
            unfold consistency1 in *; intuition.
        }
        simpl in Hbloodline. destruct Hbloodline as [HcurrIsPart1 | Hbloodline].
        + subst part1. assert(bentryAFlag requisitionedBlockInCurrPartAddr true s0).
          {
            apply addrInAccessibleMappedIsAccessible with currentPart addr; assumption.
          }
          unfold bentryAFlag in *.
          destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        + assert(HisChilds0: isChild s0) by (unfold consistency1 in *; intuition).
          assert(HPDTIfPDFlags0: PDTIfPDFlag s0) by (unfold consistency1 in *; intuition).
          assert(HmultPDTs0: multiplexerIsPDT s0) by (unfold consistency1 in *; intuition).
          assert(HparentOfParts0: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
          assert(HchildEqs0: blockInChildHasAtLeastEquivalentBlockInParent s0)
            by (unfold consistency1 in *; intuition).
          assert(HnoDupTree: noDupPartitionTree s0)
            by (unfold consistency1 in *; intuition).
          pose proof (equivalentAncestorsBlock currentPart requisitionedBlockInCurrPartAddr requisitionedBlockStart
            requisitionedBlockEnd part1 s0 HisChilds0 HPDTIfPDFlags0 HmultPDTs0 HparentOfParts0 HnoDupTree HchildEqs0
            HcurrIsParts0 Hpart1IsPart Hbloodline HstartBlocks0 HendBlocks0 HblockMappedCurrs0) as HblockAnc.
          destruct HblockAnc as [block1 [start1 [end1 (Hblock1Mapped & Hstart1 & Hend1 & HlebStart & HgebEnd)]]].
          unfold completeParentsList in *.
          assert(HwellFormeds0: wellFormedBlock s0) by (unfold consistency1 in *; intuition).
          assert(Haccesss0Spec: forall parent child addr, In child (currentPart
              :: filterOptionPaddr (completeParentsListRec (S (S maxAddr)) currentPart s0))
            -> In parent (getPartitions multiplexer s0)
            -> In child (getChildren parent s0)
            -> In addr (getAccessibleMappedPaddr parent s0)
            -> In addr (getMappedPaddr child s0) -> In addr (getAccessibleMappedPaddr child s0)).
          {
            intros pdparent child addrBis Hspec. apply Haccesss0.
          }
          assert(HaddrMappedCurr: In addr (getMappedPaddr currentPart s0)).
          { apply addrInBlockIsMapped with requisitionedBlockInCurrPartAddr; assumption. }
          assert(HaddrNotAccCurr: ~ In addr (getAccessibleMappedPaddr currentPart s0)).
          {
            unfold bentryAFlag in *. destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr)
              eqn:HlookupReq; try(exfalso; congruence). destruct v; try(exfalso; congruence).
            apply addrInBlockNotAccIsNotAcc with requisitionedBlockInCurrPartAddr b; try(assumption).
            - apply partitionsArePDT; try(assumption); unfold consistency1 in *; intuition.
            - apply eq_sym. assumption.
          }
          assert(HaddrInBlock1: In addr (getAllPaddrAux [block1] s0)).
          {
            unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
            destruct (lookup block1 (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-Hstart1. rewrite <-Hend1. rewrite app_nil_r.
            simpl in HaddrInReq.
            destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0 in *. rewrite <-HendBlocks0 in *.
            rewrite app_nil_r in HaddrInReq. apply getAllPaddrBlockInclRev in HaddrInReq.
            apply getAllPaddrBlockIncl; lia.
          }
          pose proof (ancestorsAddrNotAccIfNotInDesc (S (S maxAddr)) currentPart part1 addr block1 s0 HparentOfParts0
            HisChilds0 HchildEqs0 HwellFormeds0 Haccesss0Spec HcurrIsParts0 Hbloodline HaddrMappedCurr HaddrNotAccCurr
            Hblock1Mapped HaddrInBlock1) as HancAflag. contradict HaddrAccPart1. unfold bentryAFlag in *.
          destruct (lookup block1 (memory s0) beqAddr) eqn:Hlookup1; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). apply addrInBlockNotAccIsNotAcc with block1 b; try(assumption).
          apply eq_sym. assumption.
      - rewrite <-beqAddrFalse in *. rewrite HgetConfigPNotGlobEq; assumption.
      (* END kernelDataIsolation *)
    }
    auto.
  }

  assert(incl (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
    (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)).
  {
    intros addr HaddrIn. simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0.
    apply getAllPaddrBlockInclRevAux in HaddrIn. unfold StateLib.Index.ltb in *. apply eq_sym in HltSizeTot.
    apply PeanoNat.Nat.ltb_ge in HltSizeTot. subst kStructureTotalLength. rewrite app_nil_r.
    apply getAllPaddrBlockIncl; lia.
  }

  assert(forall block, isBE block s -> beqAddr lastBlockEntryAddr block = false
    -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
  {
    intros block HblockIsBE HbeqLastBlock. unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs. rewrite Hs5.
    rewrite Hs5 in HblockIsBE. rewrite Hs4. rewrite Hs4 in HblockIsBE. simpl. simpl in HblockIsBE.
    destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite beqAddrTrue in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs3. rewrite Hs3 in HblockIsBE. simpl.
    simpl in HblockIsBE. rewrite beqAddrFalse in HbeqLastBlock. rewrite HbeqLastBlock in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs2. simpl.
    rewrite Hs2 in HblockIsBE. simpl in HblockIsBE. rewrite beqAddrFalse in HbeqGlobBlock. rewrite HbeqGlobBlock in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs1. simpl.
    rewrite Hs1 in HblockIsBE. simpl in HblockIsBE.
    destruct (beqAddr (CPaddr (requisitionedBlockStart+nextoffset)) block) eqn:HbeqNextBlock;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  }

  assert(bentryPFlag lastBlockEntryAddr false s).
  {
    unfold bentryPFlag in *. rewrite HlookupLasts0 in *. rewrite HlookupLasts. simpl. assumption.
  }

  assert(sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) false s).
  {
    unfold sh1entryPDflag in *. rewrite HlookupSh1Eq; try(assumption). unfold isSHE.
    destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(isPDT currentPart s0) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
  rewrite <-HgetChildrenEq in Hglob; trivial.
  rewrite <-HgetPartsEq in *. rewrite <-HgetMappedBEq in HblockMappedCurrs0; trivial.

  assert(bentryAFlag requisitionedBlockInCurrPartAddr false s).
  {
    unfold bentryAFlag in *.
    destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply HblockFieldsEq in HlookupBlock.
    destruct HlookupBlock as [bentry (HlookupBlock & _ & _ & _ & _ & HaccEq & _)]. rewrite HlookupBlock.
    rewrite HaccEq. assumption.
  }

  assert(bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s).
  {
    unfold bentryStartAddr in *.
    destruct (lookup requisitionedBlockInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply HblockFieldsEq in HlookupBlock.
    destruct HlookupBlock as [bentry (HlookupBlock & _ & _ & _ & _ & _ & _ & HstartEq)]. rewrite HlookupBlock.
    rewrite HstartEq. assumption.
  }

  assert(pdentryStructurePointer globalIdPD requisitionedBlockStart s).
  {
    unfold pdentryStructurePointer. rewrite HlookupGlobs. rewrite HnewPD. simpl. rewrite Hprev3. simpl.
    rewrite Hprev2. simpl. rewrite Hprev. auto.
  }

  assert(HstartIsKSs: isKS requisitionedBlockStart s).
  { unfold isKS. rewrite HlookupStartEqs. assumption. }

  instantiate(1 := fun globIsCurr s => beqAddr globalIdPD currentPart = globIsCurr
    /\ (exists s0, consistency1 s0 /\ noDupMappedPaddrList s0 /\ sharedBlockPointsToChild s0
        /\ getPartitions multiplexer s = getPartitions multiplexer s0
        /\ (forall part, isPDT part s0 -> getChildren part s = getChildren part s0)
        /\ (forall part, isPDT part s0 -> getMappedPaddr part s = getMappedPaddr part s0)
        /\ (forall part, isPDT part s0 -> getMappedBlocks part s = getMappedBlocks part s0)
        /\ (forall addr, isSHE addr s0 -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
        /\ getAllPaddrPDTAux [globalIdPD] s = getAllPaddrPDTAux [globalIdPD] s0
        /\ getAllPaddrConfigAux (getConfigBlocks globalIdPD s) s
            = getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength
              ++ getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s0
        /\ incl (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
            (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)
        /\ (forall block, isBE block s -> beqAddr lastBlockEntryAddr block = false
            -> lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr))
    /\ consistency1 s /\ noDupMappedPaddrList s /\ accessibleParentPaddrIsAccessibleIntoChild s
    /\ adressesRangePreservedIfOriginAndNextOk s /\ childsBlocksPropsInParent s /\ noChildImpliesAddressesNotShared s
    /\ kernelsAreNotAccessible s /\ blockAndNextAreSideBySide s /\ parentBlocksBoundsIfNoNext s
    /\ childLocMappedInChild s /\ childLocHasSameStart s
    /\ verticalSharing s /\ partitionsIsolation s /\ kernelDataIsolation s
    /\ (beqAddr globalIdPD currentPart = true -> sharedBlockPointsToChild s)
    /\ (forall pdarent child addr parentblock sh1entryaddr,
          child <> globalIdPD
          -> In pdarent (getPartitions multiplexer s)
          -> In child (getChildren pdarent s)
          -> In addr (getUsedPaddr child s)
          -> In addr (getAllPaddrAux [parentblock] s)
          -> In parentblock (getMappedBlocks pdarent s)
          -> sh1entryAddr parentblock sh1entryaddr s
          -> sh1entryPDchild (CPaddr (parentblock + sh1offset)) child s
              \/ sh1entryPDflag (CPaddr (parentblock + sh1offset)) true s)
    /\ bentryPFlag lastBlockEntryAddr false s
    /\ sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s
    /\ sh1entryPDflag (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) false s
    /\ (currentPart = globalIdPD \/ In globalIdPD (getChildren currentPart s))
    /\ In currentPart (getPartitions multiplexer s)
    /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s)
    /\ bentryAFlag requisitionedBlockInCurrPartAddr false s
    /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s
    /\ pdentryStructurePointer globalIdPD newKStructurePointer s
    /\ newKStructurePointer = requisitionedBlockStart
    /\ isKS requisitionedBlockStart s
  ).

  split; trivial. split; try(exists s0); intuition.
}
intro isCurrentPart. destruct (negb isCurrentPart) eqn:HnegIsCurrent.
- eapply bindRev.
  { (** MAL.writeSh1PDChildFromBlockEntryAddr **)
    eapply weaken. apply writeSh1PDChildFromBlockEntryAddr. intros s Hprops.
    destruct Hprops as (HbeqGlobCurr & [s0 Hpropss0] & Hconsist & HnoDupP & Haccess & Hrange & HchildBlockProps &
      HnoChild & HkernNotAcc & HnextBlockSide & HparentBounds & HlocProps & HsameStart & HVS & HPI & HKDI & _ &
      HpartialShared & HPflagLast & HPDchildBlock & HPDflagBlock & Hglob & HcurrIsPart & HblockMappedCurr & HAflag &
      Hstart & HstructGlob & HstructEq & HstartIsKS).
    unfold sh1entryPDchild in HPDchildBlock. unfold sh1entryPDflag in *.
    destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s) beqAddr) eqn:HlookupSh1;
      try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s1. split; trivial.
    apply negb_true_iff in HnegIsCurrent. subst isCurrentPart. rewrite <-beqAddrFalse in HbeqGlobCurr.
    destruct Hglob as [Hcontra | HglobIsChild]; try(exfalso; congruence).
    instantiate(1 := fun _ s => exists s2 s0 sh1entry,
      s = {|
            currentPartition := currentPartition s2;
            memory :=
              add (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))
                (SHE {| PDchild := globalIdPD; PDflag := PDflag sh1entry;
                        inChildLocation := inChildLocation sh1entry |})
                (memory s2) beqAddr
          |}
      /\ consistency1 s2 /\ noDupMappedPaddrList s2 /\ accessibleParentPaddrIsAccessibleIntoChild s2
      /\ adressesRangePreservedIfOriginAndNextOk s2 /\ childsBlocksPropsInParent s2
      /\ noChildImpliesAddressesNotShared s2
      /\ kernelsAreNotAccessible s2 /\ blockAndNextAreSideBySide s2 /\ parentBlocksBoundsIfNoNext s2
      /\ childLocMappedInChild s2 /\ childLocHasSameStart s2
      /\ verticalSharing s2 /\ partitionsIsolation s2 /\ kernelDataIsolation s2
      /\ (forall pdarent child addr parentblock sh1entryaddr,
            child <> globalIdPD
            -> In pdarent (getPartitions multiplexer s2)
            -> In child (getChildren pdarent s2)
            -> In addr (getUsedPaddr child s2)
            -> In addr (getAllPaddrAux [parentblock] s2)
            -> In parentblock (getMappedBlocks pdarent s2)
            -> sh1entryAddr parentblock sh1entryaddr s2
            -> sh1entryPDchild (CPaddr (parentblock + sh1offset)) child s2
                \/ sh1entryPDflag (CPaddr (parentblock + sh1offset)) true s2)
      /\ bentryPFlag lastBlockEntryAddr false s2
      /\ In globalIdPD (getChildren currentPart s2)
      /\ In currentPart (getPartitions multiplexer s2)
      /\ In requisitionedBlockInCurrPartAddr (getMappedBlocks currentPart s2)
      /\ lookup (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (memory s2) beqAddr = Some (SHE sh1entry)
      /\ false = PDflag sh1entry /\ nullAddr = PDchild sh1entry
      /\ bentryAFlag requisitionedBlockInCurrPartAddr false s2
      /\ bentryStartAddr requisitionedBlockInCurrPartAddr requisitionedBlockStart s2
      /\ pdentryStructurePointer globalIdPD newKStructurePointer s2
      /\ newKStructurePointer = requisitionedBlockStart
      /\ isKS requisitionedBlockStart s2 /\ consistency1 s0
      /\ noDupMappedPaddrList s0
      /\ sharedBlockPointsToChild s0 /\ getPartitions multiplexer s2 = getPartitions multiplexer s0
      /\ (forall part, isPDT part s0 -> getChildren part s2 = getChildren part s0)
      /\ (forall part, isPDT part s0 -> getMappedPaddr part s2 = getMappedPaddr part s0)
      /\ (forall part, isPDT part s0 -> getMappedBlocks part s2 = getMappedBlocks part s0)
      /\ (forall addr, isSHE addr s0 -> lookup addr (memory s2) beqAddr = lookup addr (memory s0) beqAddr)
      /\ getAllPaddrPDTAux [globalIdPD] s2 = getAllPaddrPDTAux [globalIdPD] s0
      /\ getAllPaddrConfigAux (getConfigBlocks globalIdPD s2) s2
          = getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength
            ++ getAllPaddrConfigAux (getConfigBlocks globalIdPD s0) s0
      /\ incl (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)
          (getAllPaddrAux [requisitionedBlockInCurrPartAddr] s0)
      /\ (forall block, isBE block s2 -> beqAddr lastBlockEntryAddr block = false
          -> lookup block (memory s2) beqAddr = lookup block (memory s0) beqAddr)). split.
    - exists s. exists s0. exists s1. intuition.
    - unfold isBE. apply mappedBlockIsBE in HblockMappedCurr. destruct HblockMappedCurr as [bentry (Hlookup & _)].
      rewrite Hlookup. unfold consistency1 in *. intuition.
  }
  intro. eapply weaken. apply WP.ret. intros s Hprops. simpl.
  destruct Hprops as [s1 [s0 [sh1entry (Hs & Hconsists2 & HnoDupPs2 & Haccesss2 & Hranges2 & HchildBlockPropss2 &
    HnoChilds2 & HkernNotAccs2 & HnextBlockSides2 & HparentBoundss2 & HlocPropss2 & HsameStarts2 & HVSs2 & HPIs2 &
    HKDIs2 & HpartialShareds2 & HPflags2 & HglobIsChilds2 & HcurrIsParts2 & HblockMappedCurrs2 & HlookupSh1
    & HPDflagSh1 & HPDchildSh1 & HAflags2 & Hstarts2 & HstructGlob & HstructEq & HstartIsKS & Hconsists0 & HnoDupPs0 &
    Hshareds0 & HgetPartsEqs2 & HgetChildEqs2 & HgetMappedPEqs2 & HgetMappedBEqs2 & HlookupSh1Eqs2 & HaddrPDTEqs2 &
    HconfigEqs2 & HinclNews2 & HlookupBEEqs2)]]]. subst newKStructurePointer.

  assert(HcurrEq: currentPartition s = currentPartition s1) by (rewrite Hs; reflexivity).
  assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s1).
  {
    rewrite Hs. apply getPartitionsEqSHE with sh1entry; trivial; unfold consistency1 in *; intuition.
    unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }

  assert(HgetKSEq: forall part, isPDT part s1 -> getKSEntries part s = getKSEntries part s1).
  {
    intros part HpartIsPDT. rewrite Hs. unfold isPDT in *.
    destruct (lookup part (memory s1) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply getKSEntriesEqSHE with p; trivial. unfold isSHE. rewrite HlookupSh1.
    trivial.
  }

  assert(HgetMappedBEq: forall part, isPDT part s1 -> getMappedBlocks part s = getMappedBlocks part s1).
  {
    intros part HpartIsPDT. rewrite Hs. apply getMappedBlocksEqSHE; trivial. unfold isSHE. rewrite HlookupSh1.
    trivial.
  }

  assert(HgetMappedPEq: forall part, isPDT part s1 -> getMappedPaddr part s = getMappedPaddr part s1).
  {
    intros part HpartIsPDT. rewrite Hs. apply getMappedPaddrEqSHE; trivial. unfold isSHE. rewrite HlookupSh1.
    trivial.
  }

  assert(HgetAccMappedBEq: forall part, isPDT part s1
    -> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s1).
  {
    intros part HpartIsPDT. rewrite Hs. apply getAccessibleMappedBlocksEqSHE; trivial. unfold isSHE.
    rewrite HlookupSh1. trivial.
  }

  assert(HgetAccMappedPEq: forall part, isPDT part s1
    -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s1).
  {
    intros part HpartIsPDT. rewrite Hs. apply getAccessibleMappedPaddrEqSHE; trivial. unfold isSHE.
    rewrite HlookupSh1. trivial.
  }

  assert(HgetChildrenEq: forall part, isPDT part s1 -> getChildren part s = getChildren part s1).
  {
    intros part HpartIsPDT. rewrite Hs. apply getChildrenEqSHE with sh1entry; trivial.
  }

  assert(CPaddr (requisitionedBlockInCurrPartAddr + sh1offset) <> nullAddr).
  {
    assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
    intro Hcontra. rewrite Hcontra in *. rewrite HlookupSh1 in *. congruence.
  }
  assert(HcurrIsPDTs1: isPDT currentPart s1).
  { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
  assert(HgetConfigPEq: forall part, isPDT part s1 -> getConfigPaddr part s = getConfigPaddr part s1).
  {
    intros part HpartIsPDT. rewrite Hs. apply getConfigPaddrEqSHE; trivial. unfold isSHE. rewrite HlookupSh1. trivial.
  }

  assert(consistency1 s).
  {
    assert(nullAddrExists s).
    { (* BEGIN nullAddrExists s *)
      assert(Hcons0: nullAddrExists s1) by (unfold consistency1 in *; intuition).
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr) eqn:HbeqSh1Null.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Null. rewrite HbeqSh1Null in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END nullAddrExists *)
    }

    assert(wellFormedFstShadowIfBlockEntry s).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s1) by (unfold consistency1 in *; intuition).
      intros block HblockIsBE. unfold isBE in *. rewrite Hs in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 block HblockIsBE).
      unfold isSHE in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset))) eqn:HbeqSh1;
        trivial. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(PDTIfPDFlag s).
    { (* BEGIN PDTIfPDFlag s *)
      assert(Hcons0: PDTIfPDFlag s1) by (unfold consistency1 in *; intuition).
      intros idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChild. rewrite HgetPartsEq in *.
      assert(isPDT part s1).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *; trivial.
      assert(HlookupBlockEq: lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s1) beqAddr).
      {
        destruct HcheckChild as (_ & Hsh1B). unfold sh1entryAddr in *. rewrite Hs. rewrite Hs in Hsh1B. simpl.
        simpl in Hsh1B. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) idPDchild)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag. unfold bentryPFlag. unfold entryPDT.
      unfold bentryStartAddr. rewrite HlookupBlockEq in *.
      assert(HcheckChilds1: true = checkChild idPDchild s1 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s1).
      {
        unfold checkChild. destruct HcheckChild as (HcheckChild & Hsh1B). split; trivial.
        destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
        rewrite Hs in HcheckChild. simpl in HcheckChild.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1.
        - rewrite <-DTL.beqAddrTrue in HbeqSh1. rewrite HbeqSh1 in *. rewrite HlookupSh1. simpl in HcheckChild.
          assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChilds1).
      destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & Hentry)]). split; trivial. split; trivial.
      exists startaddr. split; trivial. unfold entryPDT in *.
      destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence). rewrite Hs.
      simpl. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (startAddr (blockrange b)))
        eqn:HbeqSh1Start.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag s).
    { (* BEGIN AccessibleNoPDFlag s *)
      assert(Hcons0: AccessibleNoPDFlag s1) by (unfold consistency1 in *; intuition).
      intros block sh1entryaddr HblockIsBE Hsh1 HAflag. unfold isBE in *. unfold sh1entryAddr in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HblockIsBE. simpl. simpl in HblockIsBE.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold bentryAFlag in *. rewrite HlookupBlockEq in *.
      specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1 HAflag). unfold sh1entryPDflag in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1. exfalso.
        destruct (lookup block (memory s1) beqAddr) eqn:HlookupBlock; try(congruence).
        destruct v; try(congruence). subst sh1entryaddr. unfold CPaddr in HlookupSh1.
        unfold CPaddr in HbeqSh1. assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition).
        unfold isPADDR in *. destruct (le_dec (requisitionedBlockInCurrPartAddr + sh1offset) maxAddr).
        - destruct (le_dec (block + sh1offset) maxAddr).
          + injection HbeqSh1 as HbeqSh1. apply PeanoNat.Nat.add_cancel_r in HbeqSh1.
            apply paddrEqNatEqEquiv in HbeqSh1. subst block. rewrite HlookupBlock in *. congruence.
          + injection HbeqSh1 as HbeqSh1. pose proof sh1offsetVal as Hsh1off. cbn in Hsh1off. lia.
        - replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (requisitionedBlockInCurrPartAddr+sh1offset) n |}
            with nullAddr in *; try(cbn; f_equal; apply proof_irrelevance). rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
      intros partition pdentry HlookupPart HbeqFirstNull. rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart HbeqFirstNull). destruct Hcons0 as (HfirstIsBE & HfirstIsFree).
      unfold isBE in *. unfold isFreeSlot in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (firstfreeslot pdentry))
        eqn:HbeqSh1First.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1First. rewrite HbeqSh1First in *. rewrite HlookupSh1 in *. exfalso.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; trivial.
      destruct (lookup (firstfreeslot pdentry) (memory s1) beqAddr) eqn:HlookupFirst; try(congruence).
      destruct v; try(congruence). destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))
        (CPaddr (firstfreeslot pdentry + sh1offset))) eqn:HbeqBlockFirst.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockFirst. apply mappedBlockIsBE in HblockMappedCurrs2. exfalso.
        destruct HblockMappedCurrs2 as [bentry (HlookupBlock & Hpres)]. rewrite HbeqBlockFirst in *.
        unfold CPaddr in HbeqBlockFirst. unfold CPaddr in HlookupSh1.
        assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
        destruct (le_dec (firstfreeslot pdentry + sh1offset) maxAddr).
        - destruct (le_dec (requisitionedBlockInCurrPartAddr + sh1offset) maxAddr).
          + injection HbeqBlockFirst as HbeqSh1. apply PeanoNat.Nat.add_cancel_r in HbeqSh1.
            apply paddrEqNatEqEquiv in HbeqSh1. rewrite <-HbeqSh1 in *. rewrite HlookupFirst in HlookupBlock.
            injection HlookupBlock as HlookupBlock. subst b.
            destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
            destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+scoffset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
            destruct HfirstIsFree as (_ & _ & _ & _ & HpresBis & _). congruence.
          + injection HbeqBlockFirst as HbeqSh1. pose proof sh1offsetVal as Hsh1off. cbn in Hsh1off. lia.
        - replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (firstfreeslot pdentry+sh1offset) n |}
            with nullAddr in *; try(cbn; f_equal; apply proof_irrelevance). rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))
        (CPaddr (firstfreeslot pdentry + scoffset))) eqn:HbeqSh1Sce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT s).
    { (* BEGIN multiplexerIsPDT s *)
      assert(Hcons0: multiplexerIsPDT s1) by (unfold consistency1 in *; intuition).
      unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) multiplexer) eqn:HbeqSh1Mult.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Mult. rewrite HbeqSh1Mult in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END multiplexerIsPDT *)
    }

    assert(currentPartitionInPartitionsList s).
    { (* BEGIN currentPartitionInPartitionsList s *)
      assert(Hcons0: currentPartitionInPartitionsList s1) by (unfold consistency1 in *; intuition).
      unfold currentPartitionInPartitionsList. rewrite HcurrEq. rewrite HgetPartsEq. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry s).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s1) by (unfold consistency1 in *; intuition).
      intros block HblockIsBE. unfold isBE in *. rewrite Hs in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
        eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 block HblockIsBE).
      destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr. split; trivial. unfold isSCE in *.
      rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) scentryaddr) eqn:HbeqSh1Sce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE s).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s1) by (unfold consistency1 in *; intuition).
      intros kernel idx HkernIsKS HltIdxKernEntries. unfold isKS in *. rewrite Hs in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) kernel)
        eqn:HbeqSh1Kern; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel idx HkernIsKS HltIdxKernEntries). unfold isBE in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (kernel+idx))) eqn:HbeqSh1Idx.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Idx. rewrite HbeqSh1Idx in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS s).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s1) by (unfold consistency1 in *; intuition).
      intros block idx HblockIsBE Hidx. unfold isBE in *. unfold bentryBlockIndex in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HblockIsBE. simpl. simpl in HblockIsBE.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupBlockEq in *. specialize(Hcons0 block idx HblockIsBE Hidx). unfold isKS in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (block-idx))) eqn:HbeqSh1Kern.
      { rewrite <-DTL.beqAddrTrue in HbeqSh1Kern. rewrite HbeqSh1Kern in *. rewrite HlookupSh1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(sh1InChildLocationIsBE s).
    { (* BEGIN sh1InChildLocationIsBE s *)
      assert(Hcons0: sh1InChildLocationIsBE s1) by (unfold consistency1 in *; intuition).
      intros sh1entryaddr sh1entryBis HlookupSh1Bis HbeqLocNull.
      assert(Hshe: exists sh1entryBiss1, lookup sh1entryaddr (memory s1) beqAddr = Some (SHE sh1entryBiss1)
        /\ inChildLocation sh1entryBis = inChildLocation sh1entryBiss1).
      {
        rewrite Hs in HlookupSh1Bis. simpl in HlookupSh1Bis.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1.
        - exists sh1entry. rewrite <-DTL.beqAddrTrue in HbeqSh1. injection HlookupSh1Bis as HlookupSh1Bis.
          rewrite HbeqSh1 in *. rewrite <-HlookupSh1Bis. split; trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
          exists sh1entryBis. split; trivial.
      }
      destruct Hshe as [sh1entryBiss1 (HlookupSh1Biss1 & HchildLocEq)]. rewrite HchildLocEq in *.
      specialize(Hcons0 sh1entryaddr sh1entryBiss1 HlookupSh1Biss1 HbeqLocNull). unfold isBE in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (inChildLocation sh1entryBiss1))
        eqn:HbeqSh1Loc.
      { rewrite <-DTL.beqAddrTrue in HbeqSh1Loc. rewrite HbeqSh1Loc in *. rewrite HlookupSh1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END sh1InChildLocationIsBE *)
    }

    assert(StructurePointerIsKS s).
    { (* BEGIN StructurePointerIsKS s *)
      assert(Hcons0: StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
      intros partition pdentry HlookupPart HbeqStructNull. rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart HbeqStructNull). unfold isKS in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (structure pdentry)) eqn:HbeqSh1Struct.
      { rewrite <-DTL.beqAddrTrue in HbeqSh1Struct. rewrite HbeqSh1Struct in *. rewrite HlookupSh1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END StructurePointerIsKS *)
    }

    assert(NextKSIsKS s).
    { (* BEGIN NextKSIsKS s *)
      assert(Hcons0: NextKSIsKS s1) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull. unfold nextKSAddr in *.
      assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HnextAddr. simpl. simpl in HnextAddr.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) kernel)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold isKS in *. rewrite HlookupKernEq in *. unfold nextKSentry in *. rewrite Hs in HnextKSAddr.
      simpl in HnextKSAddr. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nextKSaddr)
        eqn:HbeqSh1Next; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKSAddr HbeqNextNull). unfold isKS in *.
      rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nextKS) eqn:HbeqSh1NextKS.
      { rewrite <-DTL.beqAddrTrue in HbeqSh1NextKS. rewrite HbeqSh1NextKS in *. rewrite HlookupSh1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR s).
    { (* BEGIN NextKSOffsetIsPADDR s *)
      assert(Hcons0: NextKSOffsetIsPADDR s1) by (unfold consistency1 in *; intuition).
      intros kernel nextKSaddr HkernIsKS HnextAddr. unfold nextKSAddr in *. unfold isKS in *.
      assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HnextAddr. simpl. simpl in HnextAddr.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) kernel)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupKernEq in *. specialize(Hcons0 kernel nextKSaddr HkernIsKS HnextAddr).
      destruct Hcons0 as (Hcons0 & HbeqNextNull). split; trivial. unfold isPADDR in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nextKSaddr) eqn:HbeqSh1NextAddr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1NextAddr. rewrite HbeqSh1NextAddr in *. rewrite HlookupSh1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(HgetFreeEq: forall part, isPDT part s1 -> getFreeSlotsList part s = getFreeSlotsList part s1).
    {
      intros part HpartIsPDT. unfold getFreeSlotsList in *. unfold isPDT in *.
      rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) part) eqn:HbeqSh1Part.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Part. rewrite HbeqSh1Part in *. rewrite HlookupSh1 in *. exfalso.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup part (memory s1) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
      destruct (beqAddr (firstfreeslot p) nullAddr); trivial. apply getFreeSlotsListRecEqSHE.
      2,3: unfold isBE; unfold isPADDR; rewrite HlookupSh1; congruence.
      assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
      assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). intro Hcontra.
      destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull.
      - rewrite <-DTL.beqAddrTrue in HbeqFirstNull. rewrite HbeqFirstNull in *. rewrite Hcontra in *.
        unfold isPADDR in *. rewrite HlookupSh1 in *. congruence.
      - rewrite <-beqAddrFalse in *. specialize(HfirstIsBE part p HlookupPart HbeqFirstNull).
        destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in *. rewrite Hcontra in *. rewrite HlookupSh1 in *.
        congruence.
    }

    assert(NoDupInFreeSlotsList s).
    { (* BEGIN NoDupInFreeSlotsList s *)
      assert(Hcons0: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
      intros partition pdentry HlookupPart. rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart). destruct Hcons0 as [optFreeList (Hlist & Hwell & HnoDup)].
      exists optFreeList. split; try(split); trivial. subst optFreeList. apply eq_sym. apply HgetFreeEq.
      unfold isPDT. rewrite HlookupPart. trivial.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot s).
    { (* BEGIN freeSlotsListIsFreeSlot s *)
      assert(Hcons0: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
      intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList HbeqAddrNull.
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HgetFreeEq in HwellFormed; trivial.
      specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDT HwellFormed HaddrInList
        HbeqAddrNull). unfold isFreeSlot in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
      { rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite HlookupSh1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup addr (memory s1) beqAddr) eqn:HlookupAddr; try(congruence). destruct v; try(congruence).
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (addr+sh1offset))) eqn:HbeqSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1. apply mappedBlockIsBE in HblockMappedCurrs2. exfalso.
        destruct HblockMappedCurrs2 as [bentry (HlookupBlock & Hpres)]. rewrite HbeqSh1 in *.
        unfold CPaddr in HbeqSh1. unfold CPaddr in HlookupSh1.
        assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
        destruct (le_dec (addr + sh1offset) maxAddr).
        - destruct (le_dec (requisitionedBlockInCurrPartAddr + sh1offset) maxAddr).
          + injection HbeqSh1 as HbeqSh1. apply PeanoNat.Nat.add_cancel_r in HbeqSh1.
            apply paddrEqNatEqEquiv in HbeqSh1. rewrite <-HbeqSh1 in *. rewrite HlookupAddr in HlookupBlock.
            injection HlookupBlock as HlookupBlock. subst b.
            destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
            destruct (lookup (CPaddr (requisitionedBlockInCurrPartAddr+scoffset)) (memory s1) beqAddr);
              try(congruence). destruct v; try(congruence).
            destruct Hcons0 as (_ & _ & _ & _ & HpresBis & _). congruence.
          + injection HbeqSh1 as HbeqSh1. pose proof sh1offsetVal as Hsh1off. cbn in Hsh1off. lia.
        - replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (addr+sh1offset) n |}
            with nullAddr in *; try(cbn; f_equal; apply proof_irrelevance). rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      destruct (lookup (CPaddr (addr + sh1offset)) (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (addr+scoffset)))
        eqn:HbeqSh1Sce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(DisjointFreeSlotsLists s).
    { (* BEGIN DisjointFreeSlotsLists s *)
      assert(Hcons0: DisjointFreeSlotsLists s1) by (unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. rewrite Hs in Hpart1IsPDT.
      simpl in Hpart1IsPDT. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) part1)
        eqn:HbeqSh1Part1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs in Hpart2IsPDT.
      simpl in Hpart2IsPDT. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) part2)
        eqn:HbeqSh1Part2; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts).
      destruct Hcons0 as [optFreeList1 [optFreeList2 (Hlist1 & Hwell1 & Hlist2 & Hwell2 & Hdisjoint)]].
      exists optFreeList1. exists optFreeList2. split; try(split; try(split; try(split))); trivial.
      - subst optFreeList1. apply eq_sym. apply HgetFreeEq. assumption.
      - subst optFreeList2. apply eq_sym. apply HgetFreeEq. assumption.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries s).
    { (* BEGIN inclFreeSlotsBlockEntries s *)
      assert(Hcons0: inclFreeSlotsBlockEntries s1) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT.
      simpl in HpartIsPDT. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
        eqn:HbeqSh1Part; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HgetFreeEq; trivial.
      specialize(Hcons0 partition HpartIsPDT). rewrite HgetKSEq; trivial.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries s).
    { (* BEGIN DisjointKSEntries s *)
      assert(Hcons0: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts. unfold isPDT in *. rewrite Hs in Hpart1IsPDT.
      simpl in Hpart1IsPDT. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) part1)
        eqn:HbeqSh1Part1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs in Hpart2IsPDT.
      simpl in Hpart2IsPDT. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) part2)
        eqn:HbeqSh1Part2; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts).
      destruct Hcons0 as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. exists list1. exists list2.
      rewrite HgetKSEq; trivial. rewrite HgetKSEq; auto.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree s).
    { (* BEGIN noDupPartitionTree s *)
      assert(Hcons0: noDupPartitionTree s1) by (unfold consistency1 in *; intuition). unfold noDupPartitionTree.
      rewrite HgetPartsEq. assumption.
      (* END noDupPartitionTree *)
    }

    assert(isParent s).
    { (* BEGIN isParent s *)
      assert(Hcons0: isParent s1) by (unfold consistency1 in *; intuition).
      intros partition pdparent HparentIsPart HpartIsChild. rewrite HgetPartsEq in *.
      assert(isPDT pdparent s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in HpartIsChild; trivial.
      specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent. rewrite Hs. simpl.
      assert(isPDT partition s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1Part. rewrite HbeqSh1Part in *. unfold isPDT in *.
        rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END isParent *)
    }

    assert(isChild s).
    { (* BEGIN isChild s *)
      assert(Hcons0: isChild s1) by (unfold consistency1 in *; intuition).
      intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEq in *.
      unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in HparentIsParent.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
        eqn:HbeqSh1Part1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
      assert(isPDT pdparent s1).
      {
        unfold getChildren in Hcons0. unfold isPDT.
        destruct (lookup pdparent (memory s1) beqAddr); try(simpl in Hcons0; congruence).
        destruct v; try(simpl in Hcons0; congruence). trivial.
      }
      rewrite HgetChildrenEq; trivial.
      (* END isChild *)
    }

    assert(noDupKSEntriesList s).
    { (* BEGIN noDupKSEntriesList s *)
      assert(Hcons0: noDupKSEntriesList s1) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
        eqn:HbeqSh1Part1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition HpartIsPDT). rewrite HgetKSEq; trivial.
      (* END noDupKSEntriesList *)
    }

    assert(noDupMappedBlocksList s).
    { (* BEGIN noDupMappedBlocksList s *)
      assert(Hcons0: noDupMappedBlocksList s1) by (unfold consistency1 in *; intuition).
      intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
        eqn:HbeqSh1Part1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition HpartIsPDT). rewrite HgetMappedBEq; trivial.
      (* END noDupMappedBlocksList *)
    }

    assert(wellFormedBlock s).
    { (* BEGIN wellFormedBlock s *)
      assert(Hcons0: wellFormedBlock s1) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr HPflag HstartBlock HendBlock. unfold bentryPFlag in *. unfold bentryEndAddr in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HPflag. simpl. simpl in HPflag.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold bentryStartAddr in *. rewrite HlookupBlockEq in *.
      specialize(Hcons0 block startaddr endaddr HPflag HstartBlock HendBlock). assumption.
      (* END wellFormedBlock *)
    }

    assert(parentOfPartitionIsPartition s).
    { (* BEGIN parentOfPartitionIsPartition s *)
      assert(Hcons0: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
      intros partition pdentry HlookupPart. rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
        eqn:HbeqSh1Part; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart). destruct Hcons0 as (HparentIsPart & HparentRest).
      rewrite HgetPartsEq. split; trivial. intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split; trivial. exists parentEntry.
      rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (parent pdentry)) eqn:HbeqSh1Parent.
      { rewrite <-DTL.beqAddrTrue in HbeqSh1Parent. rewrite HbeqSh1Parent in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END parentOfPartitionIsPartition *)
    }

    assert(NbFreeSlotsISNbFreeSlotsInList s).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s1) by (unfold consistency1 in *; intuition).
      intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. unfold pdentryNbFreeSlots in *.
      rewrite Hs in HpartIsPDT. rewrite Hs in HnbFree. simpl in HpartIsPDT. simpl in HnbFree.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree).
      destruct Hcons0 as [optFreeList (Hlist & Hwell & Hlen)]. exists optFreeList. rewrite HgetFreeEq; auto.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(maxNbPrepareIsMaxNbKernels s).
    { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s1) by (unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. rewrite Hs in HlistOfKerns. apply isListOfKernelsEqSHE in HlistOfKerns.
      specialize(Hcons0 partition kernList HlistOfKerns). assumption.
      (* END maxNbPrepareIsMaxNbKernels *)
    }

    assert(blockInChildHasAtLeastEquivalentBlockInParent s).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s1)
        by (unfold consistency1 in *; intuition). intros pdparent child block startChild endChild
        HparentIsPart HchildIsChild HblockMappedChild HstartChild HendChild HPflagChild. rewrite HgetPartsEq in *.
      assert(isPDT pdparent s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in HchildIsChild; trivial.
      assert(isPDT child s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
      rewrite HgetMappedBEq in HblockMappedChild; trivial. rewrite HgetMappedBEq; trivial. unfold bentryPFlag in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HPflagChild. simpl. simpl in HPflagChild.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlockEq in *.
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        HstartChild HendChild HPflagChild).
      destruct Hcons0 as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & HendParent &
        Hbounds)]]]. exists blockParent. exists startParent. exists endParent. rewrite Hs. simpl.
      unfold bentryStartAddr in *.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh1BlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1BlockP. rewrite HbeqSh1BlockP in *. rewrite HlookupSh1 in *. exfalso.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); auto.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(partitionTreeIsTree s).
    { (* BEGIN partitionTreeIsTree s *)
      assert(Hcons0: partitionTreeIsTree s1) by (unfold consistency1 in *; intuition).
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
      rewrite HgetPartsEq in *. unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in HparentIsParent.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) child) eqn:HbeqSh1Child;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent). apply Hcons0.
      revert HparentsList. rewrite Hs. apply isParentsListEqSHERev with sh1entry; trivial.
      - assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
        destruct (lookup child (memory s1) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild).
        destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqChildRoot). subst pdparent.
        apply HparentIsPart.
      - unfold consistency1 in *; intuition.
      (* END partitionTreeIsTree *)
    }

    assert(nextKernelIsValid s).
    { (* BEGIN nextKernelIsValid s *)
      assert(Hcons0: nextKernelIsValid s1) by (unfold consistency1 in *; intuition).
      intros kernel HkernIsKS. unfold isKS in *.
      assert(HlookupKernEq: lookup kernel (memory s) beqAddr = lookup kernel (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HkernIsKS. simpl. simpl in HkernIsKS.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) kernel)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupKernEq in *. specialize(Hcons0 kernel HkernIsKS).
      destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]). split; trivial. exists nextAddr. split.
      - intro Hp. specialize(HlookupNext Hp). rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset))
          {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqSh1Next.
        { rewrite <-DTL.beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - destruct Hnext as [HnextIsKS | HnextIsNull]; try(right; assumption). unfold isKS in *. rewrite Hs. simpl.
        left. destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nextAddr) eqn:HbeqSh1Next.
        { rewrite <-DTL.beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *. rewrite HlookupSh1 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns s).
    { (* BEGIN noDupListOfKerns s *)
      assert(Hcons0: noDupListOfKerns s1) by (unfold consistency1 in *; intuition).
      intros partition kernList HlistOfKerns. rewrite Hs in HlistOfKerns. apply isListOfKernelsEqSHE in HlistOfKerns.
      specialize(Hcons0 partition kernList HlistOfKerns). assumption.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax s).
    { (* BEGIN MPUsizeIsBelowMax s *)
      assert(Hcons0: MPUsizeIsBelowMax s1) by (unfold consistency1 in *; intuition).
      intros partition MPUlist HMPU. unfold pdentryMPU in *. rewrite Hs in HMPU. simpl in HMPU.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 partition MPUlist HMPU).
      assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart s).
    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s1) by (unfold consistency1 in *; intuition).
      intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEq in *. rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
        eqn:HbeqSh1Part; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold scentryOrigin in *.
      assert(isPDT partition s1) by (unfold isPDT; rewrite HlookupPart; trivial).
      rewrite HgetMappedBEq in HblockMapped; trivial. rewrite Hs in Horigin. simpl in Horigin.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
        Horigin). destruct Hcons0 as (HinclParent & Hstart). split.
      - intro HbeqPartRoot. specialize(HinclParent HbeqPartRoot).
        destruct HinclParent as [blockParent (HblockParentMapped & HstartParent & Hincl)]. exists blockParent.
        assert(isPDT (parent pdentry) s1).
        {
          unfold isPDT. unfold getMappedBlocks in HblockParentMapped. unfold getKSEntries in HblockParentMapped.
          destruct (lookup (parent pdentry) (memory s1) beqAddr); try(simpl in HblockParentMapped; congruence).
          destruct v; try(simpl in HblockParentMapped; congruence). trivial.
        }
        rewrite HgetMappedBEq; trivial. unfold bentryStartAddr in *.
        assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
        {
          rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) blockParent)
            eqn:HbeqSh1BlockP.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSh1BlockP. rewrite HbeqSh1BlockP in *. rewrite HlookupSh1 in *.
            exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        }
        simpl. rewrite HlookupBlockPEq. split; trivial. split; trivial. intros addr HaddrInBlock. simpl in Hincl.
        rewrite Hs in HaddrInBlock. simpl in HaddrInBlock.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
          try(simpl in HaddrInBlock; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hincl addr HaddrInBlock).
        assumption.
      - intros startaddr HstartBlock. apply Hstart. unfold bentryStartAddr in *. rewrite Hs in HstartBlock.
        simpl in HstartBlock.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut s).
    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s1) by (unfold consistency1 in *; intuition).
      intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock Hsce
        HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEq in *. rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
        eqn:HbeqSh1Part; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(isPDT partition s1) by (unfold isPDT; rewrite HlookupPart; trivial).
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryEndAddr in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HendBlock. simpl. simpl in HendBlock.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      simpl. rewrite HlookupBlockEq in *. unfold scentryNext in *. rewrite Hs in Hnext. simpl in Hnext.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
        HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & HltEnd & Hincl)]].
      exists blockParent. exists endParent.
      assert(isPDT (parent pdentry) s1).
      {
        unfold isPDT. unfold getMappedBlocks in HblockParentMapped. unfold getKSEntries in *.
        destruct (lookup (parent pdentry) (memory s1) beqAddr); try(simpl in HblockParentMapped; congruence).
        destruct v; try(simpl in HblockParentMapped; congruence). trivial.
      }
      rewrite HgetMappedBEq; trivial. split; trivial. unfold bentryEndAddr in *.
      assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
      {
        rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) blockParent)
          eqn:HbeqSh1BlockP.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1BlockP. rewrite HbeqSh1BlockP in *. rewrite HlookupSh1 in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupBlockPEq. split; trivial. auto.
      (* END nextImpliesBlockWasCut *)
    }

    assert(blocksAddressesTypes s).
    { (* BEGIN blocksAddressesTypes s *)
      assert(Hcons0: blocksAddressesTypes s1) by (unfold consistency1 in *; intuition).
      intros block startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock.
      rewrite HgetPartsEq in *. assert(isPDT part s1).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HstartBlock. simpl. simpl in HstartBlock.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold bentryEndAddr in *. rewrite HlookupBlockEq in *.
      assert(HPDchildBlocks1: sh1entryPDchild (CPaddr (block + sh1offset)) nullAddr s1).
      {
        unfold sh1entryPDchild in *. rewrite Hs in HPDchildBlock. simpl in HPDchildBlock.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset)))
          eqn:HbeqSh1.
        {
          simpl in HPDchildBlock. assert(isPDT globalIdPD s1)
            by (apply childrenArePDT with currentPart; unfold consistency1 in *; intuition). unfold isPDT in *.
          assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *. exfalso.
          subst globalIdPD. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 block startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlocks1).
      destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hrange]].
      - left. split.
        + unfold isKS in *. rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh1Start.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *. rewrite HlookupSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrIn. specialize(Hrange addr HaddrIn).
          destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
          * left. unfold isBE in *. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite HlookupSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. left. unfold isSHE in *. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite HlookupSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. left. unfold isSCE in *. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite HlookupSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. right. left. unfold isPADDR in *. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite HlookupSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
          * right. right. right. right. rewrite Hs. simpl.
            destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
            {
              rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite HlookupSh1 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. left. split.
        + unfold isPDT in *. rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh1Start.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *. rewrite HlookupSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
        + intros addr HaddrIn. specialize(Hrange addr HaddrIn). rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite HlookupSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      - right. right. intros addr HaddrIn. specialize(Hrange addr HaddrIn). rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) addr) eqn:HbeqSh1Addr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *. rewrite HlookupSh1 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      (* END blocksAddressesTypes *)
    }

    assert(notPDTIfNotPDflag s).
    { (* BEGIN notPDTIfNotPDflag s *)
      assert(Hcons0: notPDTIfNotPDflag s1) by (unfold consistency1 in *; intuition).
      intros block startaddr sh1entryaddr part HpartIsPart HblockMapped HstartBlock Hsh1 HPDflag HPDchild.
      rewrite HgetPartsEq in *. assert(isPDT part s1).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HstartBlock. simpl. simpl in HstartBlock.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      unfold sh1entryAddr in *. rewrite HlookupBlockEq in *.
      assert(HSh1s1: sh1entryPDflag sh1entryaddr false s1 /\ sh1entryPDchild sh1entryaddr nullAddr s1).
      {
        unfold sh1entryPDchild in *. unfold sh1entryPDflag in *. rewrite Hs in HPDchild. simpl in HPDchild.
        rewrite Hs in HPDflag. simpl in HPDflag.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) sh1entryaddr) eqn:HbeqSh1.
        {
          simpl in HPDchild. assert(isPDT globalIdPD s1)
            by (apply childrenArePDT with currentPart; unfold consistency1 in *; intuition). unfold isPDT in *.
          assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *. exfalso.
          subst globalIdPD. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
      }
      destruct HSh1s1 as (HPDflags1 & HPDchilds1).
      specialize(Hcons0 block startaddr sh1entryaddr part HpartIsPart HblockMapped HstartBlock Hsh1 HPDflags1
        HPDchilds1). unfold isPDT in *.
      rewrite Hs. simpl. contradict Hcons0.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh1Start;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      (* END notPDTIfNotPDflag *)
    }

    assert(nextKernAddrIsInSameBlock s).
    { (* BEGIN nextKernAddrIsInSameBlock s *)
      assert(Hcons0: nextKernAddrIsInSameBlock s1) by (unfold consistency1 in *; intuition).
      intros block kernel startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HnextInRange
        HkernIsKS.
      rewrite HgetPartsEq in *. assert(isPDT part s1).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HstartBlock. simpl. simpl in HstartBlock.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupBlockEq in *. unfold isKS in *. rewrite Hs in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) kernel) eqn:HbeqSh1Kern;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      assert(HnextInRanges1: sh1entryPDchild (CPaddr (block + sh1offset)) nullAddr s1).
      {
        unfold sh1entryPDchild in *. rewrite Hs in HnextInRange. simpl in HnextInRange.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset)))
          eqn:HbeqSh1.
        {
          simpl in HnextInRange. assert(isPDT globalIdPD s1)
            by (apply childrenArePDT with currentPart; unfold consistency1 in *; intuition). unfold isPDT in *.
          assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *. exfalso.
          subst globalIdPD. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      }
      specialize(Hcons0 block kernel startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock
        HnextInRanges1 HkernIsKS). assumption.
      (* END nextKernAddrIsInSameBlock *)
    }

    assert(PDflagMeansNoChild s).
    { (* BEGIN PDflagMeansNoChild s *)
      assert(Hcons0: PDflagMeansNoChild s1) by (unfold consistency1 in *; intuition).
      intros block HblockIsBE HPDflagBlock. unfold isBE in *.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite Hs. rewrite Hs in HblockIsBE. simpl. simpl in HblockIsBE.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
          eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      }
      rewrite HlookupBlockEq in *. unfold sh1entryPDflag in *. unfold sh1entryPDchild. rewrite Hs. simpl.
      rewrite Hs in HPDflagBlock. simpl in HPDflagBlock.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset)))
        eqn:HbeqSh1.
      { simpl in HPDflagBlock. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 block HblockIsBE HPDflagBlock). assumption.
      (* END PDflagMeansNoChild *)
    }

    assert(nbPrepareIsNbKern s).
    { (* BEGIN nbPrepareIsNbKern s *)
      assert(Hcons0: nbPrepareIsNbKern s1) by (unfold consistency1 in *; intuition).
      intros partition pdentry HlookupPart. rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
        eqn:HbeqSh1Part; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 partition pdentry HlookupPart). rewrite Hs. rewrite completeListOfKernelsEqSHE; trivial.
      unfold isSHE. rewrite HlookupSh1. trivial.
     (* END nbPrepareIsNbKern *)
    }

    assert(pdchildIsPDT s).
    { (* BEGIN pdchildIsPDT s *)
      assert(Hcons0: pdchildIsPDT s1) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
      rewrite HgetPartsEq in *. assert(HpartIsPDT: isPDT part s1).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *; trivial. unfold sh1entryAddr in *. rewrite Hs in Hsh1. simpl in Hsh1.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite HgetChildrenEq in *; trivial.
      unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
      - destruct (lookup block (memory s1) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst sh1entryaddr. rewrite <-DTL.beqAddrTrue in HbeqSh1s.
        apply CPaddrAddEq in HbeqSh1s; trivial. subst block. assert(part = currentPart).
        {
          destruct (beqAddr part currentPart) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
          assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in *. specialize(Hdisjoint part currentPart HpartIsPDT HcurrIsPDTs1 HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMappedCurrs2.
          apply InFilterPresentInList in HblockMapped.
          specialize(Hdisjoint requisitionedBlockInCurrPartAddr HblockMapped). congruence.
        }
        subst part. simpl in HPDchild. subst idchild. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(Hcons0 part block sh1entryaddr idchild HpartIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull).
        assumption.
      (* END pdchildIsPDT *)
    }

    assert(childBlockNullIfChildNull s).
    { (* BEGIN childBlockNullIfChildNull s *)
      assert(Hcons0: childBlockNullIfChildNull s1) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchild.
      rewrite HgetPartsEq in *. assert(HpartIsPDT: isPDT part s1).
      { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
      rewrite HgetMappedBEq in *; trivial. unfold sh1entryAddr in *. rewrite Hs in Hsh1. simpl in Hsh1.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryInChildLocation.
      unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in HPDchild. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
      {
        simpl in HPDchild. subst globalIdPD. exfalso. assert(isPDT nullAddr s1).
        { apply childrenArePDT with currentPart; trivial; unfold consistency1 in *; intuition. }
        assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *. unfold isPDT in *.
        destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      specialize(Hcons0 part block sh1entryaddr HpartIsPart HblockMapped Hsh1 HPDchild).
      unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddr (memory s1) beqAddr); try(congruence).
      destruct v; try(congruence). destruct Hcons0. split; trivial. intro. exfalso; congruence.
      (* END childBlockNullIfChildNull *)
    }

    assert(accessibleBlocksArePresent s).
    { (* BEGIN accessibleBlocksArePresent s *)
      assert(Hcons0: accessibleBlocksArePresent s1) by (unfold consistency1 in *; intuition).
      intros block HAflag. unfold bentryAFlag in *. unfold bentryPFlag in *. rewrite Hs in HAflag. simpl in HAflag.
      rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
        try(congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. apply Hcons0; assumption.
      (* END accessibleBlocksArePresent *)
    }

    assert(sharedBlockIsPresent s).
    { (* BEGIN sharedBlockIsPresent s *)
      assert(Hcons0: sharedBlockIsPresent s1) by (unfold consistency1 in *; intuition).
      intros part block child HpartIsPart HblockIsEntry HPDchild HbeqChildNull. rewrite HgetPartsEq in *.
      assert(isPDT part s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetKSEq in *; trivial. unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset)))
        eqn:HbeqSh1s.
      - rewrite <-DTL.beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. subst block.
        rewrite <-HgetMappedBEq in HblockMappedCurrs2; trivial. apply mappedBlockIsBE in HblockMappedCurrs2.
        destruct HblockMappedCurrs2 as [bentry (Hlookup & Hpres)]. unfold bentryPFlag. rewrite Hlookup. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(Hcons0 part block child HpartIsPart HblockIsEntry HPDchild HbeqChildNull). unfold bentryPFlag in *.
        rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Block. subst block. rewrite HlookupSh1 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END sharedBlockIsPresent *)
    }

    (* assert(HbeqGlobNull: globalIdPD <> nullAddr).
    {
      assert(isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold pdentryStructurePointer in *.
      unfold isPADDR in *. intro. subst globalIdPD. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence).
      destruct v; congruence.
    } *)
    assert(HgetConfigBEq: forall part, isPDT part s1 -> getConfigBlocks part s = getConfigBlocks part s1).
    {
      intros part HpartIsPDT. rewrite Hs. unfold isPDT in *.
      destruct (lookup part (memory s1) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). apply getConfigBlocksEqSHE with p; trivial. unfold isSHE.
      rewrite HlookupSh1. trivial.
    }

    assert(sharedBlockNoPDflagNoLocIsKern s).
    { (* BEGIN sharedBlockNoPDflagNoLocIsKern s *)
      assert(Hcons0: sharedBlockNoPDflagNoLocIsKern s1) by (unfold consistency1 in *; intuition).
      intros part block child startaddr HpartIsPart HblockIsEntry HPDchild HbeqChildNull HPDflag Hloc Hstart.
      rewrite HgetPartsEq in *. unfold bentryStartAddr in *.
      assert(isPDT part s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetKSEq in *; trivial. unfold sh1entryPDchild in *. unfold sh1entryPDflag in *. rewrite Hs in HPDchild.
      unfold sh1entryInChildLocationWeak in *. rewrite Hs in HPDflag. simpl in HPDchild. simpl in HPDflag.
      rewrite Hs in Hloc. simpl in Hloc. rewrite Hs in Hstart. simpl in Hstart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hstart; auto.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (block+sh1offset)))
        eqn:HbeqSh1s.
      - rewrite <-DTL.beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. subst block. simpl in HPDchild.
        subst child. destruct (lookup requisitionedBlockInCurrPartAddr (memory s1) beqAddr) eqn:HlookupReq;
          try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-Hstarts2 in Hstart. subst startaddr. unfold getConfigBlocks.
        unfold pdentryStructurePointer in *. rewrite Hs at 1. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) globalIdPD) eqn:HbeqSh1Glob.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Glob. subst globalIdPD. rewrite HlookupSh1 in *. simpl. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        destruct (lookup globalIdPD (memory s1) beqAddr); try(simpl; congruence). destruct v; try(simpl; congruence).
        rewrite <-HstructGlob. rewrite DTL.MaxIdxNextEq. simpl. rewrite Hs at 1. simpl. unfold isKS in *.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) requisitionedBlockStart)
          eqn:HbeqSh1Start.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *. rewrite HlookupSh1 in *. simpl.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        assert(HnextValid: nextKernelIsValid s1) by (unfold consistency1 in *; intuition).
        specialize(HnextValid requisitionedBlockStart HstartIsKS).
        destruct HnextValid as (HlebNextMax & [nextLookup (HlookupNext & _)]).
        destruct (lookup requisitionedBlockStart (memory s1) beqAddr); try(simpl; congruence).
        destruct v; try(exfalso; congruence). unfold StateLib.Paddr.addPaddrIdx.
        destruct (le_dec (requisitionedBlockStart + nextoffset) maxAddr); try(lia).
        specialize(HlookupNext (StateLib.Paddr.addPaddrIdx_obligation_1 requisitionedBlockStart nextoffset l)).
        rewrite Hs at 1. simpl.
        set(nextAddr := {|
                          p := requisitionedBlockStart + nextoffset;
                          Hp := StateLib.Paddr.addPaddrIdx_obligation_1 requisitionedBlockStart nextoffset l
                        |}). fold nextAddr in HlookupNext.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nextAddr) eqn:HbeqSh1Next.
        {
          rewrite <-DTL.beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *. simpl. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite HlookupNext.
        destruct (StateLib.Index.pred (CIndex maxNbPrepare)); simpl; auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(Hcons0 part block child startaddr HpartIsPart HblockIsEntry HPDchild HbeqChildNull HPDflag Hloc
          Hstart). rewrite HgetConfigBEq; trivial. unfold getConfigBlocks in *. unfold isPDT.
        destruct (lookup child (memory s1) beqAddr); try(simpl in Hcons0; congruence).
        destruct v; try(simpl in Hcons0; congruence). trivial.
      (* END sharedBlockNoPDflagNoLocIsKern *)
    }

    assert(partitionNotAutoMapped s).
    { (* BEGIN partitionNotAutoMapped s *)
      assert(Hcons0: partitionNotAutoMapped s1) by (unfold consistency1 in *; intuition).
      intros part HpartIsPart. rewrite HgetPartsEq in *. specialize(Hcons0 part HpartIsPart).
      rewrite HgetMappedPEq; trivial. apply partitionsArePDT; trivial; unfold consistency1 in *; intuition.
      (* END partitionNotAutoMapped *)
    }

    assert(configAddrNotMappedInChild s).
    { (* BEGIN configAddrNotMappedInChild s *)
      assert(Hcons0: configAddrNotMappedInChild s1) by (unfold consistency1 in *; intuition).
      intros part child addr HpartIsPart HchildIsChild HaddrIsConfig. rewrite HgetPartsEq in *.
      assert(isPDT part s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetChildrenEq in *; trivial. rewrite HgetConfigPEq in *; trivial.
      specialize(Hcons0 part child addr HpartIsPart HchildIsChild HaddrIsConfig). rewrite HgetMappedPEq; trivial.
      apply childrenArePDT with part; trivial; unfold consistency1 in *; intuition.
      (* END configAddrNotMappedInChild *)
    }

    assert(fullKernelIsInOneBlock s).
    { (* BEGIN fullKernelIsInOneBlock s *)
      assert(Hcons0: fullKernelIsInOneBlock s1) by (unfold consistency1 in *; intuition).
      intros part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKS. rewrite HgetPartsEq in *.
      assert(isPDT part s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetMappedBEq in *; trivial. rewrite Hs in HkernInBlock. unfold isKS in *. rewrite Hs in HkernIsKS.
      rewrite Hs. simpl in HkernInBlock. simpl in HkernIsKS. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
        try(simpl in HkernInBlock; exfalso; congruence).
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) kernel) eqn:HbeqSh1Kern;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKS). assumption.
      (* END fullKernelIsInOneBlock *)
    }

    assert(sharedBlocksAdressesAreAllMappedInChild s).
    { (* BEGIN sharedBlocksAdressesAreAllMappedInChild s *)
      assert(Hcons0: sharedBlocksAdressesAreAllMappedInChild s1) by (unfold consistency1 in *; intuition).
      intros part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1 HPDchild Hloc HbeqChildNull
        HbeqLocNull addr HaddrInBlock. rewrite HgetPartsEq in *.
      assert(isPDT part s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
      rewrite HgetMappedBEq in *; trivial. unfold sh1entryAddr in *. rewrite Hs in Hsh1. rewrite Hs in HaddrInBlock.
      unfold sh1entryPDchild in *. unfold sh1entryInChildLocationWeak in *. rewrite Hs in HPDchild.
      rewrite Hs in Hloc. simpl in Hsh1. simpl in HaddrInBlock. simpl in HPDchild. simpl in Hloc.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block) eqn:HbeqSh1Block;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hsh1; auto.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
      {
        simpl in Hloc. exfalso. assert(Hsh1Req: sh1entryAddr requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) s1).
        {
          unfold sh1entryAddr. unfold bentryStartAddr in *.
          destruct (lookup requisitionedBlockInCurrPartAddr (memory s1) beqAddr); try(congruence).
          destruct v; congruence.
        }
        assert(HPDchildReq: sh1entryPDchild (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) nullAddr s1).
        { unfold sh1entryPDchild. rewrite HlookupSh1. assumption. }
        assert(HlocNull: childBlockNullIfChildNull s1) by (unfold consistency1 in *; intuition).
        specialize(HlocNull currentPart requisitionedBlockInCurrPartAddr
          (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) HcurrIsParts2 HblockMappedCurrs2 Hsh1Req HPDchildReq).
        unfold sh1entryInChildLocation in *. rewrite HlookupSh1 in *. destruct HlocNull as (HlocNull & _).
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1 HPDchild Hloc
        HbeqChildNull HbeqLocNull addr HaddrInBlock). rewrite HgetMappedPEq; trivial. unfold getMappedPaddr in *.
      unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
      destruct (lookup child (memory s1) beqAddr); try(simpl in Hcons0; congruence).
      destruct v; try(simpl in Hcons0; congruence). trivial.
      (* END sharedBlocksAdressesAreAllMappedInChild *)
    }

    unfold consistency1 in *. intuition.
  }
  split.
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren. rewrite HgetPartsEq in *.
    assert(isPDT pdparent s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    rewrite HgetChildrenEq in Hchild1IsChild; trivial. rewrite HgetChildrenEq in Hchild2IsChild; trivial.
    specialize(HPIs2 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
    assert(isPDT child1 s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
    assert(isPDT child2 s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
    unfold getUsedPaddr. rewrite HgetMappedPEq; trivial. rewrite HgetMappedPEq; trivial.
    rewrite HgetConfigPEq; trivial. rewrite HgetConfigPEq; trivial.
    (* END partitionsIsolation *)
  }
  split.
  { (* BEGIN kernelDataIsolation s *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart. rewrite HgetPartsEq in *.
    specialize(HKDIs2 part1 part2 Hpart1IsPart Hpart2IsPart).
    assert(isPDT part1 s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    assert(isPDT part2 s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    rewrite HgetConfigPEq; trivial. rewrite HgetAccMappedPEq; trivial.
    (* END kernelDataIsolation *)
  }
  split.
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild. rewrite HgetPartsEq in *.
    assert(isPDT pdparent s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    rewrite HgetChildrenEq in HchildIsChild; trivial. specialize(HVSs2 pdparent child HparentIsPart HchildIsChild).
    assert(isPDT child s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
    unfold getUsedPaddr. rewrite HgetMappedPEq; trivial. rewrite HgetMappedPEq; trivial.
    rewrite HgetConfigPEq; trivial.
    (* END verticalSharing *)
  }
  unfold consistency. split; trivial. unfold consistency2. split.
  { (* BEGIN noDupMappedPaddrList s *)
    assert(Hcons0: noDupMappedPaddrList s1) by (unfold consistency2 in *; intuition).
    intros partition HpartIsPDT. unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
      eqn:HbeqSh1Part; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. specialize(Hcons0 partition HpartIsPDT).
    rewrite HgetMappedPEq; trivial.
    (* END noDupMappedPaddrList *)
  }
  split.
  { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
    assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s1) by (unfold consistency2 in *; intuition).
    intros pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
    rewrite HgetPartsEq in *.
    assert(isPDT pdparent s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetAccMappedPEq in HaddrAccMappedParent; trivial.
    assert(isPDT child s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
    rewrite HgetMappedPEq in HaddrMappedChild; trivial. rewrite HgetAccMappedPEq; trivial.
    specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild). trivial.
    (* END accessibleParentPaddrIsAccessibleIntoChild *)
  }
  split.
  { (* BEGIN sharedBlockPointsToChild s *)
    intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild HaddrInBlockParent
      HblockParentMapped Hsh1. rewrite HgetPartsEq in *.
    assert(isPDT pdparent s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetMappedBEq in HblockParentMapped; trivial.
    unfold sh1entryAddr in *.
    assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
    {
      rewrite Hs. rewrite Hs in Hsh1. simpl. simpl in Hsh1.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) blockParent)
        eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    rewrite HlookupBlockPEq in *. assert(HaddrInBlockParents1: In addr (getAllPaddrAux [blockParent] s1)).
    {
      simpl. simpl in HaddrInBlockParent. rewrite HlookupBlockPEq in HaddrInBlockParent. assumption.
    }
    assert(isPDT child s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
    unfold getUsedPaddr in *. rewrite HgetConfigPEq in HaddrUsedChild; trivial.
    rewrite HgetMappedPEq in HaddrUsedChild; trivial. destruct (beqAddr child globalIdPD) eqn:HbeqChildGlob.
    - rewrite <-DTL.beqAddrTrue in HbeqChildGlob. subst child.
      assert(pdparent = currentPart).
      {
        apply uniqueParent with globalIdPD s1; trivial. 1,2: unfold consistency1 in *; intuition.
        apply childrenPartitionInPartitionList with pdparent; trivial. unfold consistency1 in *; intuition.
      }
      subst pdparent. rewrite HgetPartsEqs2 in *.
      assert(HcurrIsPDTs0: isPDT currentPart s0) by (apply partitionsArePDT; unfold consistency1 in *; intuition).
      assert(HaddrInBlockParents0: In addr (getAllPaddrAux [blockParent] s0)).
      {
        simpl. simpl in HaddrInBlockParents1. destruct (beqAddr lastBlockEntryAddr blockParent) eqn:HbeqLastBlockP.
        {
          rewrite <-DTL.beqAddrTrue in HbeqLastBlockP. subst blockParent. apply mappedBlockIsBE in HblockParentMapped.
          destruct HblockParentMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag in *. rewrite Hlookup in *.
          exfalso; congruence.
        }
        rewrite <-HlookupBEEqs2; trivial. apply mappedBlockIsBE in HblockParentMapped.
        destruct HblockParentMapped as [bentry (Hlookup & _)]. unfold isBE. rewrite Hlookup. trivial.
      }
      destruct (beqAddr lastBlockEntryAddr blockParent) eqn:HbeqLastBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqLastBlockP. subst blockParent. apply mappedBlockIsBE in HblockParentMapped.
        destruct HblockParentMapped as [bentry (Hlookup & Hpres)]. unfold bentryPFlag in *.
        rewrite Hlookup in *. exfalso; congruence.
      }
      assert(isBE blockParent s1).
      {
        unfold isBE. destruct (lookup blockParent (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
        trivial.
      }
      rewrite HgetChildEqs2 in HchildIsChild; trivial. rewrite HgetMappedBEqs2 in HblockParentMapped; trivial.
      assert(isPDT globalIdPD s0) by (apply childrenArePDT with currentPart; unfold consistency1 in *; intuition).
      rewrite HgetMappedPEqs2 in HaddrUsedChild; trivial. unfold getConfigPaddr in HaddrUsedChild.
      rewrite HaddrPDTEqs2 in *. rewrite HconfigEqs2 in *.
      assert(HpropsOrAddr: In addr (getUsedPaddr globalIdPD s0)
        \/ In addr (getAllPaddrBlockAux 0 requisitionedBlockStart Constants.kernelStructureTotalLength)).
      {
        unfold getUsedPaddr. unfold getConfigPaddr. apply in_app_or in HaddrUsedChild.
        destruct HaddrUsedChild as [HaddrConfig | HaddrMapped]; try(left; apply in_or_app; right; assumption).
        apply in_app_or in HaddrConfig. destruct HaddrConfig as [HaddrPDT | HaddrConfAux];
          try(left; apply in_or_app; left; apply in_or_app; left; assumption). apply in_app_or in HaddrConfAux.
        destruct HaddrConfAux as [HaddrNew | HaddrConfAux]; try(right; assumption). left. apply in_or_app. left.
        apply in_or_app. right. assumption.
      }
      rewrite HlookupBEEqs2 in Hsh1; trivial.
      destruct HpropsOrAddr as [HaddrUsedChilds0 | HaddrIsNew].
      + specialize(Hshareds0 currentPart globalIdPD addr blockParent sh1entryaddr HparentIsPart HchildIsChild
          HaddrUsedChilds0 HaddrInBlockParents0 HblockParentMapped Hsh1). unfold sh1entryPDchild in *.
        unfold sh1entryPDflag in *. assert(isSHE (CPaddr (blockParent + sh1offset)) s0).
        {
          unfold isSHE. destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr);
            try(destruct Hshareds0; exfalso; congruence). destruct v; try(destruct Hshareds0; exfalso; congruence).
          trivial.
        }
        rewrite <-HlookupSh1Eqs2 in Hshareds0; trivial. rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset)))
          eqn:HbeqSh1.
        * left. reflexivity.
        * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
      + specialize(HinclNews2 addr HaddrIsNew). assert(blockParent = requisitionedBlockInCurrPartAddr).
        {
          destruct (beqAddr blockParent requisitionedBlockInCurrPartAddr) eqn:HbeqBlocks;
            try(rewrite DTL.beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in *.
          rewrite HgetMappedBEqs2 in HblockMappedCurrs2; try(assumption).
          pose proof (DisjointPaddrInPart currentPart blockParent requisitionedBlockInCurrPartAddr addr s0
            HnoDupPs0 HcurrIsPDTs0 HblockParentMapped HblockMappedCurrs2 HbeqBlocks HaddrInBlockParents0). congruence.
        }
        subst blockParent. left. unfold sh1entryPDchild. rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity.
    - rewrite <-beqAddrFalse in *. specialize(HpartialShareds2 pdparent child addr blockParent sh1entryaddr
        HbeqChildGlob HparentIsPart HchildIsChild HaddrUsedChild HaddrInBlockParents1 HblockParentMapped Hsh1).
      unfold sh1entryPDchild in *. unfold sh1entryPDflag in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) (CPaddr (blockParent+sh1offset)))
        eqn:HbeqSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1. exfalso. unfold CPaddr in HbeqSh1. unfold CPaddr in HlookupSh1.
        assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *.
        destruct (le_dec (requisitionedBlockInCurrPartAddr + sh1offset) maxAddr) eqn:Hl.
        - destruct (le_dec (blockParent + sh1offset) maxAddr).
          + injection HbeqSh1 as HbeqSh1. apply PeanoNat.Nat.add_cancel_r in HbeqSh1.
            apply paddrEqNatEqEquiv in HbeqSh1. subst blockParent. unfold CPaddr in HpartialShareds2.
            rewrite Hl in *. rewrite HlookupSh1 in *. destruct HpartialShareds2 as [Hchild | Hflag]; try(congruence).
            rewrite <-Hchild in *. rewrite <-HPDchildSh1 in *. unfold isPDT in *.
            destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
          + rewrite HbeqSh1 in HlookupSh1.
            assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockParent + sh1offset) n |} = nullAddr).
            { cbn. f_equal. apply proof_irrelevance. }
            rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
        - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (requisitionedBlockInCurrPartAddr+sh1offset) n |}
            = nullAddr).
          { cbn. f_equal. apply proof_irrelevance. }
          rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END sharedBlockPointsToChild *)
  }
  split.
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
    assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s1) by (unfold consistency2 in *; intuition).
    intros partition pdentry block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE HstartBlock
      HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. rewrite HgetPartsEq in *.
    assert(isPDT partition s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold isBE in *. unfold bentryStartAddr in *.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
    {
      rewrite Hs. rewrite Hs in HstartBlock. simpl. simpl in HstartBlock.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
        eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite HlookupBlockEq in *. unfold scentryOrigin in *.
    unfold scentryNext in *. rewrite Hs in Horigin. rewrite Hs in Hnext. simpl in Horigin. simpl in Hnext.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. rewrite Hs in HlookupPart. simpl in HlookupPart.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
      eqn:HbeqSh1Part; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 partition pdentry block scentryaddr startBlock endBlock HpartIsPart HblockMapped HblockIsBE
      HstartBlock HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot).
    destruct Hcons0 as [blockParent (HblockParentMapped & HblockPIsBE & HstartParent & HendParent)].
    assert(isPDT (parent pdentry) s1).
    {
      unfold getMappedBlocks in HblockParentMapped. unfold getKSEntries in HblockParentMapped. unfold isPDT.
      destruct (lookup (parent pdentry) (memory s1) beqAddr); try(simpl in HblockParentMapped; congruence).
      destruct v; try(simpl in HblockParentMapped; congruence). trivial.
    }
    rewrite HgetMappedBEq; trivial. exists blockParent. unfold isBE in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh1BlockP.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1BlockP. subst blockParent. rewrite HlookupSh1 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); auto.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }
  split.
  { (* BEGIN childsBlocksPropsInParent s *)
    assert(Hcons0: childsBlocksPropsInParent s1) by (unfold consistency2 in *; intuition).
    intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart HchildIsChild
      HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent HPflagParent
      HlebStart HgebEnd. rewrite HgetPartsEq in *.
    assert(isPDT pdparent s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetMappedBEq in HblockParentMapped; trivial.
    assert(isPDT child s1) by (apply childrenArePDT with pdparent; unfold consistency1 in *; intuition).
    rewrite HgetMappedBEq in HblockChildMapped; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
    {
      rewrite Hs. rewrite Hs in HstartParent. simpl. simpl in HstartParent.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) blockParent)
        eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    assert(HlookupBlockCEq: lookup blockChild (memory s) beqAddr = lookup blockChild (memory s1) beqAddr).
    {
      rewrite Hs. rewrite Hs in HstartChild. simpl. simpl in HstartChild.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) blockChild)
        eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    unfold bentryPFlag in *. rewrite HlookupBlockPEq in *. rewrite HlookupBlockCEq in *.
    specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
      HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
      HPflagParent HlebStart HgebEnd).
    destruct Hcons0 as (HcheckChild & HPDchild & HinChildLoc & HAflag). unfold checkChild in *. unfold bentryAFlag.
    rewrite HlookupBlockPEq. split; try(split; try(split)); trivial.
    - destruct (lookup blockParent (memory s1) beqAddr); trivial. destruct v; trivial. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (CPaddr (blockParent + sh1offset)))
        eqn:HbeqSh1.
      + rewrite <-DTL.beqAddrTrue in HbeqSh1. rewrite HbeqSh1 in *. simpl. rewrite HlookupSh1 in *. assumption.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    - intros childGlobalID HPDchildID. unfold sh1entryPDchild in *. rewrite Hs in HPDchildID. simpl in HPDchildID.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (CPaddr (blockParent + sh1offset)))
        eqn:HbeqSh1.
      + simpl in HPDchildID. subst childGlobalID. intro Hcontra. assert(isPDT globalIdPD s1).
        { apply childrenArePDT with currentPart; trivial; unfold consistency1 in *; intuition. }
        subst globalIdPD. assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition).
        unfold isPADDR in *. unfold isPDT in *.
        destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        specialize(HPDchild childGlobalID HPDchildID). auto.
    - intros blockIDInChild HchildLoc. apply HinChildLoc. unfold sh1entryInChildLocation in *.
      rewrite Hs in HchildLoc. simpl in HchildLoc.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) (CPaddr (blockParent + sh1offset)))
        eqn:HbeqSh1.
      + rewrite <-DTL.beqAddrTrue in HbeqSh1. rewrite HbeqSh1 in *. simpl in HchildLoc. rewrite HlookupSh1.
        destruct HchildLoc as (Hloc & HlocIsBE). split; trivial. intro HbeqLocNull. specialize(HlocIsBE HbeqLocNull).
        unfold isBE in *. simpl in HlocIsBE.
        destruct (beqAddr (CPaddr (blockParent + sh1offset)) blockIDInChild) eqn:HbeqSh1Loc; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
        destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence). destruct HchildLoc as (Hloc & HlocIsBE). split; trivial. intro HbeqLocNull.
        specialize(HlocIsBE HbeqLocNull). unfold isBE in *. simpl in HlocIsBE.
        destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) blockIDInChild) eqn:HbeqSh1Loc;
          try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END childsBlocksPropsInParent *)
  }
  split.
  { (* BEGIN noChildImpliesAddressesNotShared s *)
    assert(Hcons0: noChildImpliesAddressesNotShared s1) by (unfold consistency2 in *; intuition).
    intros partition pdentry block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild child addr
      HchildIsChild HaddrInBlock. rewrite HgetPartsEq in *.
    assert(isPDT partition s1) by (apply partitionsArePDT; trivial; unfold consistency1 in *; intuition).
    rewrite HgetChildrenEq in HchildIsChild; trivial. rewrite HgetMappedBEq in HblockMapped; trivial.
    assert(isPDT child s1) by (apply childrenArePDT with partition; unfold consistency1 in *; intuition).
    rewrite HgetMappedPEq; trivial. rewrite Hs in HlookupPart. simpl in HlookupPart.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition)
      eqn:HbeqSh1Part; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    assert(HPDchilds1: sh1entryPDchild sh1entryaddr nullAddr s1).
    {
      unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) sh1entryaddr) eqn:HbeqSh1.
      {
        simpl in HPDchild. assert(isPDT globalIdPD s1)
          by (apply childrenArePDT with currentPart; unfold consistency1 in *; intuition). unfold isPDT in *.
        assert(Hnull: isPADDR nullAddr s1) by (unfold consistency1 in *; intuition). unfold isPADDR in *. exfalso.
        subst globalIdPD. destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    assert(HaddrInBlocks1: In addr (getAllPaddrAux [block] s1)).
    {
      simpl. rewrite Hs in HaddrInBlock. simpl in HaddrInBlock.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
        try(simpl in HaddrInBlock; exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    specialize(Hcons0 partition pdentry block sh1entryaddr HpartIsPart HlookupPart HblockMapped Hsh1 HPDchilds1 child
      addr HchildIsChild HaddrInBlocks1). assumption.
    (* END noChildImpliesAddressesNotShared *)
  }
  split.
  {
    (* BEGIN kernelsAreNotAccessible s *)
    assert(Hcons0: kernelsAreNotAccessible s1) by (unfold consistency2 in *; intuition).
    intros block startaddr part HpartIsPart HblockMapped Hstart HstartBIsKS.
    rewrite HgetPartsEq in *. assert(isPDT part s1).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
    {
      rewrite Hs. rewrite Hs in Hstart. simpl. simpl in Hstart.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr+sh1offset)) block)
        eqn:HbeqSh1Block; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    }
    unfold bentryAFlag. rewrite HlookupBlockEq in *. unfold isKS in *. rewrite Hs in HstartBIsKS.
    simpl in HstartBIsKS.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh1Start;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(Hcons0 block startaddr part HpartIsPart HblockMapped Hstart HstartBIsKS). assumption.
    (* END kernelsAreNotAccessible *)
  }
  split.
  { (* BEGIN blockAndNextAreSideBySide s *)
    intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull
      Hnext. rewrite HgetPartsEq in *. assert(isPDT partition s1).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedBEq in *; trivial. unfold bentryEndAddr in *. unfold scentryNext in *. rewrite Hs in Hnext.
    rewrite Hs in HendBlock. simpl in Hnext. simpl in HendBlock.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
      try(exfalso; congruence).
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(HnextBlockSides2 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce
      HbeqNextNull Hnext). unfold bentryStartAddr in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) scnext) eqn:HbeqSh1Next.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *. rewrite HlookupSh1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial.
    (* END blockAndNextAreSideBySide *)
  }
  split.
  { (* BEGIN parentBlocksBoundsIfNoNext s *)
    intros partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock HendBlock Hsce
      Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEq in *. assert(isPDT partition s1).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    unfold scentryNext in *. rewrite Hs in HstartBlock. rewrite Hs in Hnext. rewrite Hs in HendBlock. simpl in Hnext.
    simpl in HstartBlock. simpl in HendBlock. rewrite Hs in HlookupPart. simpl in HlookupPart.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
      try(exfalso; congruence).
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) partition) eqn:HbeqSh1Part;
      try(exfalso; congruence).
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) scentryaddr) eqn:HbeqSh1Sce;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(HparentBoundss2 partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped
      HstartBlock HendBlock Hsce Hnext HbeqPartRoot HlookupPart).
    destruct HparentBoundss2 as [blockParent [startP (HblockPMappped & HstartP & HendP & HlebStarts)]].
    exists blockParent. exists startP. unfold bentryEndAddr in *. rewrite Hs. simpl. rewrite <-Hs.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) blockParent) eqn:HbeqSh1BP.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1BP. rewrite HbeqSh1BP in *. rewrite HlookupSh1 in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); trivial. split; auto.
    rewrite HgetMappedBEq; trivial. unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
    destruct (lookup (parent pdentry) (memory s1) beqAddr); try(simpl in HblockPMappped; congruence).
    destruct v; try(simpl in HblockPMappped; congruence). trivial.
    (* END parentBlocksBoundsIfNoNext *)
  }
  split.
  { (* BEGIN childLocMappedInChild s *)
    intros part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1 HPDchild Hloc
      HbeqIdChildNull Hstart HstartNotKern.
    rewrite HgetPartsEq in *. assert(HpartIsPDT: isPDT part s1).
    { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryAddr in *. rewrite Hs in Hsh1. simpl in Hsh1.
    unfold bentryStartAddr in *. rewrite Hs in Hstart. simpl in Hstart.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryInChildLocationWeak in *.
    assert(HstartNotKerns1: ~isKS startaddr s1).
    {
      unfold isKS in *. contradict HstartNotKern. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) startaddr) eqn:HbeqSh1Start.
      { rewrite <-DTL.beqAddrTrue in HbeqSh1Start. subst startaddr. rewrite HlookupSh1 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    }
    unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in HPDchild. rewrite Hs in Hloc. simpl in Hloc.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
    {
      destruct (lookup block (memory s1) beqAddr) eqn:HlookupBlock; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). subst sh1entryaddr. rewrite <-DTL.beqAddrTrue in HbeqSh1s.
      apply CPaddrAddEq in HbeqSh1s; trivial. subst block. assert(part = currentPart).
      {
        destruct (beqAddr part currentPart) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
        assert(Hdisjoint: DisjointKSEntries s1) by (unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in *. specialize(Hdisjoint part currentPart HpartIsPDT HcurrIsPDTs1 HbeqParts).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMappedCurrs2.
        apply InFilterPresentInList in HblockMapped.
        specialize(Hdisjoint requisitionedBlockInCurrPartAddr HblockMapped). congruence.
      }
      subst part. simpl in HPDchild. subst idchild. simpl in Hloc. subst blockChild. rewrite HlookupBlock in *.
      rewrite <-Hstarts2 in *. subst startaddr. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    specialize(HlocPropss2 part block sh1entryaddr blockChild idchild startaddr HpartBisIsPart HblockMapped Hsh1
      HPDchild Hloc HbeqIdChildNull Hstart HstartNotKerns1).
    destruct HlocPropss2 as (HbeqBCNull & HBCMapped & HstartChild). split; trivial. assert(isPDT idchild s1).
    {
      unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
      destruct (lookup idchild (memory s1) beqAddr); try(simpl in HBCMapped; congruence).
      destruct v; try(simpl in HBCMapped; congruence). trivial.
    }
    rewrite HgetMappedBEq; trivial. split; trivial. unfold bentryStartAddr in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) blockChild) eqn:HbeqSh1BC.
    { rewrite <-DTL.beqAddrTrue in HbeqSh1BC. subst blockChild. rewrite HlookupSh1 in *. congruence. }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
    (* END childLocMappedInChild *)
  }
  (* BEGIN childLocHasSameStart s *)
  intros part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1 HPDchild Hloc
    HbeqIdChildNull HbeqBCNull.
  rewrite HgetPartsEq in *. assert(HpartIsPDT: isPDT part s1).
  { apply partitionsArePDT; trivial; unfold consistency1 in *; intuition. }
  rewrite HgetMappedBEq in HblockMapped; trivial. unfold sh1entryAddr in *. rewrite Hs in Hsh1. simpl in Hsh1.
  unfold bentryStartAddr at 1. rewrite Hs. simpl. rewrite <-Hs.
  destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) block) eqn:HbeqSh1Block;
    try(exfalso; congruence). rewrite <-beqAddrFalse in *.
  rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial. unfold sh1entryInChildLocationWeak in *.
  unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in HPDchild. rewrite Hs in Hloc. simpl in Hloc.
  destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
  {
    assert(HchildLoc: sh1entryInChildLocation (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) nullAddr s1).
    {
      assert(Hres: childBlockNullIfChildNull s1) by (unfold consistency1 in *; intuition).
      specialize(Hres currentPart requisitionedBlockInCurrPartAddr). apply Hres; trivial.
      - unfold sh1entryAddr. unfold bentryStartAddr in *.
        destruct (lookup requisitionedBlockInCurrPartAddr (memory s1) beqAddr); try(congruence).
        destruct v; congruence.
      - unfold sh1entryPDchild. rewrite HlookupSh1. assumption.
    }
    simpl in Hloc. subst blockChild. unfold sh1entryInChildLocation in *. rewrite HlookupSh1 in *.
    destruct HchildLoc. exfalso; congruence.
  }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  specialize(HsameStarts2 part block sh1entryaddr blockChild idchild HpartBisIsPart HblockMapped Hsh1
    HPDchild Hloc HbeqIdChildNull HbeqBCNull). destruct HsameStarts2 as (HsameStart & HBCMapped).
  assert(isPDT idchild s1).
  {
    unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
    destruct (lookup idchild (memory s1) beqAddr); try(simpl in HBCMapped; congruence).
    destruct v; try(simpl in HBCMapped; congruence). trivial.
  }
  rewrite HgetMappedBEq; trivial. split; trivial. intros startaddr Hstart.
  specialize(HsameStart startaddr Hstart). unfold bentryStartAddr in *. rewrite Hs. simpl.
  destruct (beqAddr (CPaddr (requisitionedBlockInCurrPartAddr + sh1offset)) blockChild) eqn:HbeqSh1BC.
  { rewrite <-DTL.beqAddrTrue in HbeqSh1BC. subst blockChild. rewrite HlookupSh1 in *. congruence. }
  rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; try(apply not_eq_sym); trivial.
  (* END childLocHasSameStart *)
- eapply weaken. apply WP.ret. intros s Hprops. apply negb_false_iff in HnegIsCurrent. subst isCurrentPart.
  unfold consistency. unfold consistency2. intuition.
Qed.