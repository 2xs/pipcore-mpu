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

(** * Summary
    This file contains the invariant of [createPartition].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas.
Require Import Invariants (*getGlobalIdPDCurrentOrChild*) findBlockInKSWithAddr sizeOfBlock eraseBlock
writeAccessibleToAncestorsIfNotCutRec lookupInvariant.
Require Import Compare_dec Bool List Lia.
Import List.ListNotations.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Module WP := WeakestPreconditions.
Module DTL := DependentTypeLemmas.

Lemma createPartition (idBlock: paddr):
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.createPartition idBlock
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold createPartition. eapply bindRev.
{ (* MAL.getCurPartition *)
  eapply weaken. apply getCurPartition. intros s Hprops. apply Hprops.
}
intro currentPart. eapply bindRev.
{ (* Internal.findBlockInKSWithAddr *)
  eapply weaken. apply findBlockInKSWithAddr. intros s Hprops. simpl.
  destruct Hprops as ((HPI & HKDI & HVS & Hconsist) & Hcurr).
  assert(HcurrIsPDT: isPDT currentPart s).
  {
    subst currentPart.
    assert(HcurrIsPDT: currentPartitionInPartitionsList s)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold currentPartitionInPartitionsList in HcurrIsPDT. apply partitionsArePDT; try(assumption).
    unfold consistency in *; unfold consistency1 in *; intuition.
    unfold consistency in *; unfold consistency1 in *; intuition.
  }
  split; try(split; assumption).
  assert(Hres: partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
                  /\ currentPart = currentPartition s /\ isPDT currentPart s) by intuition.
  apply Hres.
}
intro blockInCurrentPartitionAddr. eapply bindRev.
{ (* Internal.compareAddrToNull *)
  eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
}
intro addrIsNull. destruct addrIsNull.
{
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
eapply bindRev.
{ (* MAL.readBlockAccessibleFromBlockEntryAddr *)
  eapply weaken. apply readBlockAccessibleFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as ((Hprops & Hconsist & Hblock) & HbeqNullBlock). rewrite <-beqAddrFalse in HbeqNullBlock.
  destruct Hblock as [Hcontra | Hblock]; try(exfalso; congruence). rewrite beqAddrFalse in HbeqNullBlock.
  split.
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
                            /\ consistency s /\ currentPart = currentPartition s /\ isPDT currentPart s
                            /\ (exists bentry,
                                  lookup blockInCurrentPartitionAddr (memory s) beqAddr = Some (BE bentry) /\
                                  blockInCurrentPartitionAddr = idBlock /\
                                  bentryPFlag blockInCurrentPartitionAddr true s /\
                                  In blockInCurrentPartitionAddr (getMappedBlocks currentPart s))
                            /\ beqAddr nullAddr blockInCurrentPartitionAddr = false). simpl. intuition.
  destruct Hblock as [bentry (HlookupBlock & Hblock)]. unfold isBE. rewrite HlookupBlock. trivial.
}
intro addrIsAccessible. destruct (negb addrIsAccessible) eqn:HnegAcc.
{
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
apply negb_false_iff in HnegAcc. subst addrIsAccessible.
eapply bindRev.
{ (* MAL.checkBlockInRAM *)
  eapply weaken. apply checkBlockInRAM. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as (_ & Hres). unfold bentryAFlag in Hres. unfold isBE.
  destruct (lookup blockInCurrentPartitionAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  trivial.
}
intro isInRAM. destruct (negb isInRAM) eqn:HnegInRAM.
{
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
(*apply negb_false_iff in HnegInRAM. subst isInRAM.*) eapply bindRev.
{ (* Internal.sizeOfBlock *)
  eapply weaken. apply sizeOfBlock. intros s Hprops. simpl. split. apply Hprops. split. apply Hprops.
  destruct Hprops as (_ & Hres). unfold isBlockInRAM in Hres. unfold isBE.
  destruct (lookup blockInCurrentPartitionAddr (memory s) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
intro blockSize. eapply bindRev.
{ (* getMinBlockSize *)
  eapply weaken. apply Invariants.getMinBlockSize. intros s Hprops. simpl. apply Hprops.
}
intro minBlockSize. eapply bindRev.
{ (* ret *)
  eapply weaken. apply WP.ret. intros s Hprops.
  instantiate(1 := fun isBlockTooSmall s =>
                    partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
                    /\ currentPart = currentPartition s /\ isPDT currentPart s
                    /\ (exists bentry,
                          lookup blockInCurrentPartitionAddr (memory s) beqAddr = Some (BE bentry) /\
                          blockInCurrentPartitionAddr = idBlock /\
                          bentryPFlag blockInCurrentPartitionAddr true s /\
                          List.In blockInCurrentPartitionAddr (getMappedBlocks currentPart s))
                    /\ beqAddr nullAddr blockInCurrentPartitionAddr = false
                    /\ bentryAFlag blockInCurrentPartitionAddr true s
                    /\ isBlockInRAM blockInCurrentPartitionAddr isInRAM s
                    /\ minBlockSize = Constants.minBlockSize
                    /\ isBlockTooSmall = indexLt blockSize minBlockSize
                    /\ exists startaddr endaddr,
                        bentryStartAddr blockInCurrentPartitionAddr startaddr s
                        /\ bentryEndAddr blockInCurrentPartitionAddr endaddr s
                        /\ i blockSize = endaddr - startaddr). simpl. intuition.
}
intro isBlockTooSmall1. destruct isBlockTooSmall1.
{
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
eapply bindRev.
{ (* getPDStructureTotalLength *)
  eapply weaken. unfold getPDStructureTotalLength. apply WP.ret. intros s Hprops.
  instantiate(1 := fun structLen s =>
                    partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
                    /\ currentPart = currentPartition s /\ isPDT currentPart s
                    /\ (exists bentry,
                          lookup blockInCurrentPartitionAddr (memory s) beqAddr = Some (BE bentry) /\
                          blockInCurrentPartitionAddr = idBlock /\
                          bentryPFlag blockInCurrentPartitionAddr true s /\
                          List.In blockInCurrentPartitionAddr (getMappedBlocks currentPart s))
                    /\ beqAddr nullAddr blockInCurrentPartitionAddr = false
                    /\ bentryAFlag blockInCurrentPartitionAddr true s
                    /\ isBlockInRAM blockInCurrentPartitionAddr isInRAM s
                    /\ minBlockSize = Constants.minBlockSize
                    /\ false = indexLt blockSize minBlockSize
                    /\ structLen = Constants.PDStructureTotalLength
                    /\ exists startaddr endaddr,
                        bentryStartAddr blockInCurrentPartitionAddr startaddr s
                        /\ bentryEndAddr blockInCurrentPartitionAddr endaddr s
                        /\ i blockSize = endaddr - startaddr). simpl. intuition.
}
intro PDStructureTotalLength. eapply bindRev.
{ (* ret *)
  eapply weaken. apply WP.ret. intros s Hprops.
  instantiate(1 := fun isBlockTooSmall s =>
                    partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
                    /\ currentPart = currentPartition s /\ isPDT currentPart s
                    /\ (exists bentry,
                          lookup blockInCurrentPartitionAddr (memory s) beqAddr = Some (BE bentry) /\
                          blockInCurrentPartitionAddr = idBlock /\
                          bentryPFlag blockInCurrentPartitionAddr true s /\
                          List.In blockInCurrentPartitionAddr (getMappedBlocks currentPart s))
                    /\ beqAddr nullAddr blockInCurrentPartitionAddr = false
                    /\ bentryAFlag blockInCurrentPartitionAddr true s
                    /\ isBlockInRAM blockInCurrentPartitionAddr isInRAM s
                    /\ minBlockSize = Constants.minBlockSize
                    /\ false = indexLt blockSize minBlockSize
                    /\ PDStructureTotalLength = Constants.PDStructureTotalLength
                    /\ isBlockTooSmall = indexLt blockSize PDStructureTotalLength
                    /\ exists startaddr endaddr,
                        bentryStartAddr blockInCurrentPartitionAddr startaddr s
                        /\ bentryEndAddr blockInCurrentPartitionAddr endaddr s
                        /\ i blockSize = endaddr - startaddr). simpl. intuition.
}
intro isBlockTooSmall2. destruct isBlockTooSmall2.
{
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
eapply bindRev.
{ (* MAL.readSh1PDChildFromBlockEntryAddr *)
  eapply weaken. apply readSh1PDChildFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops. split.
  apply Hprops. destruct Hprops as (_ & _ & _ & Hconsist & _ & _ & Hres & _).
  destruct Hres as [bentry (Hlookup & _)]. unfold consistency in *. unfold consistency1 in *. split. intuition.
  split. intuition. split. intuition. exists bentry. assumption.
}
intro PDChildAddr. eapply bindRev.
{ (* Internal.compareAddrToNull *)
  eapply weaken. apply compareAddrToNull. intros s Hprops. simpl. apply Hprops.
}
intro PDChildAddrIsNull. destruct (negb PDChildAddrIsNull) eqn:HnegChildNull.
{
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
eapply bindRev.
{ (* MAL.readBlockStartFromBlockEntryAddr *)
  eapply weaken. apply readBlockStartFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
  assert(Hres: bentryAFlag blockInCurrentPartitionAddr true s) by intuition.
  unfold isBE. unfold bentryAFlag in Hres.
  destruct (lookup blockInCurrentPartitionAddr (memory s) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
intro newPDBlockStartAddr. eapply bindRev.
{ (* MAL.readBlockEndFromBlockEntryAddr *)
  eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
  assert(Hres: bentryAFlag blockInCurrentPartitionAddr true s) by intuition.
  unfold isBE. unfold bentryAFlag in Hres.
  destruct (lookup blockInCurrentPartitionAddr (memory s) beqAddr); try(congruence).
  destruct v; try(congruence). trivial.
}
intro newPDBlockEndAddr. eapply bindRev.
{ (* MAL.eraseBlock *)
  eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.
}
intro. eapply bindRev.
{ (* MAL.initPDTable *)
  eapply weaken. apply initPDTable. intros s Hprops. simpl.
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
                  /\ currentPart = currentPartition s
                  /\ isPDT currentPart s
                  /\ (exists bentry,
                        lookup blockInCurrentPartitionAddr (memory s) beqAddr = Some (BE bentry) /\
                        blockInCurrentPartitionAddr = idBlock /\
                        bentryPFlag blockInCurrentPartitionAddr true s /\
                        In blockInCurrentPartitionAddr (getMappedBlocks currentPart s))
                  /\ beqAddr nullAddr blockInCurrentPartitionAddr = false
                  /\ bentryAFlag blockInCurrentPartitionAddr true s
                  (*/\ isBlockInRAM blockInCurrentPartitionAddr isInRAM s*)
                  /\ minBlockSize = Constants.minBlockSize
                  /\ false = indexLt blockSize minBlockSize
                  /\ PDStructureTotalLength = Constants.PDStructureTotalLength
                  /\ false = indexLt blockSize PDStructureTotalLength
                  /\ (exists sh1entry sh1entryaddr,
                         lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) /\
                         sh1entryPDchild sh1entryaddr PDChildAddr s /\
                         sh1entryAddr blockInCurrentPartitionAddr sh1entryaddr s)
                  /\ bentryStartAddr blockInCurrentPartitionAddr newPDBlockStartAddr s
                  /\ bentryEndAddr blockInCurrentPartitionAddr newPDBlockEndAddr s
                  /\ i blockSize = newPDBlockEndAddr - newPDBlockStartAddr
                  /\ (forall addr,
                         In addr (getAllPaddrBlock newPDBlockStartAddr newPDBlockEndAddr)
                         -> lookup addr (memory s) beqAddr = None)).
  simpl. destruct Hprops as [s0 ((((((HPIs0 & HKDIs0 & HVSs0 & Hconsists0 & Hcurrs0 & HcurrIsPDTs0 & Hblock &
    HbeqNullBlock & HAFlagBlock & _ & Hmin & HltSizeMin & Hlen & HltSizeLen & Hbounds) & Hsh1) & HbeqNullChild) &
    HstartBlock) & HendBlock) & Hcurr & HremovedAddr & HkeptAddr & _)].
  destruct Hblock as [bentry (HlookupBlocks0 & HblocksEq & HPFlagBlock & HblockMappeds0)].
  destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChildBlocks0 & Hsh1s0)]].
  assert(HlookupsEq: forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intro. set(P := In addr (getAllPaddrBlock newPDBlockStartAddr newPDBlockEndAddr)).
    assert(HpropsOr: P \/ ~P) by (apply Classical_Prop.classic). subst P.
    destruct HpropsOr as [HaddrInBlock | HaddrNotInBlock]; try(apply HkeptAddr; assumption).
    rewrite HremovedAddr; try(assumption). apply eq_sym.
    assert(Htypes: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(Htypes blockInCurrentPartitionAddr newPDBlockStartAddr newPDBlockEndAddr HstartBlock HendBlock).
    assert(HnotPDT: notPDTIfNotPDflag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HPDFlagBlocks0: sh1entryPDflag sh1entryaddr false s0).
    {
      assert(HnoPDFlag: AccessibleNoPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(HblockIsBE: isBE blockInCurrentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
      specialize(HnoPDFlag blockInCurrentPartitionAddr sh1entryaddr HblockIsBE Hsh1s0 HAFlagBlock).
      assumption.
    }
    specialize(HnotPDT blockInCurrentPartitionAddr newPDBlockStartAddr sh1entryaddr HstartBlock Hsh1s0
      HPDFlagBlocks0).
    destruct Htypes as [(HKS & _) | [(HPDT & _) | Hnull]]; try(apply Hnull; assumption); try(exfalso; congruence).
    assert(HkernNotAcc: kernelsAreNotAccessible s0)
      by (unfold consistency in *; unfold consistency2 in *; intuition). exfalso.
    specialize(HkernNotAcc blockInCurrentPartitionAddr newPDBlockStartAddr HstartBlock HKS).
    unfold bentryAFlag in *. rewrite HlookupBlocks0 in *. congruence.
  }
  assert(Hconsists: consistency s).
  {
    unfold consistency in *. unfold consistency1 in *. unfold consistency2 in *.
    assert(nullAddrExists s).
    { (* BEGIN nullAddrExists s *)
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupsEq. intuition.
      (* END nullAddrExists *)
    }
    assert(wellFormedFstShadowIfBlockEntry s).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s0) by intuition.
      intros block HblockIsBE. unfold isBE in HblockIsBE. rewrite HlookupsEq in HblockIsBE. unfold isSHE.
      rewrite HlookupsEq. specialize(Hcons0 block HblockIsBE). assumption.
      (* END wellFormedFstShadowIfBlockEntry *)
    }
    assert(PDTIfPDFlag s).
    { (* BEGIN PDTIfPDFlag s *)
      assert(Hcons0: PDTIfPDFlag s0) by intuition.
      intros idPDchild sh1entryaddrBis Hcheck. unfold checkChild in Hcheck. unfold sh1entryAddr in Hcheck.
      rewrite HlookupsEq in Hcheck. rewrite HlookupsEq in Hcheck. unfold bentryAFlag. unfold bentryPFlag.
      unfold bentryStartAddr. unfold entryPDT. rewrite HlookupsEq.
      specialize(Hcons0 idPDchild sh1entryaddrBis Hcheck).
      destruct Hcons0 as (HAFlag & HPFlag & [startaddr (Hstart & HstartIsPDT)]). split. assumption. split.
      assumption. exists startaddr. split. assumption. unfold entryPDT in HstartIsPDT.
      destruct (lookup idPDchild (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite HlookupsEq. assumption.
      (* END PDTIfPDFlag *)
    }
    assert(AccessibleNoPDFlag s).
    { (* BEGIN AccessibleNoPDFlag s *)
      assert(Hcons0: AccessibleNoPDFlag s0) by intuition.
      intros block sh1entryaddrBis HblockIsBE Hsh1Bis HAFlag. unfold isBE in HblockIsBE.
      unfold sh1entryAddr in Hsh1Bis. unfold bentryAFlag in HAFlag. unfold sh1entryPDflag.
      rewrite HlookupsEq in *. specialize(Hcons0 block sh1entryaddrBis HblockIsBE Hsh1Bis HAFlag).
      assumption.
      (* END AccessibleNoPDFlag *)
    }
    assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0) by intuition.
      intros partition pdentry HlookupPart HbeqFirstNull. unfold isBE. unfold isFreeSlot. rewrite HlookupsEq in *.
      specialize(Hcons0 partition pdentry HlookupPart HbeqFirstNull).
      destruct Hcons0 as (HfirstIsBE & HfirstFree). split. assumption. unfold isFreeSlot in HfirstFree.
      destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite HlookupsEq.
      destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). rewrite HlookupsEq. assumption.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }
    assert(multiplexerIsPDT s).
    { (* BEGIN multiplexerIsPDT s *)
      unfold multiplexerIsPDT. unfold isPDT. rewrite HlookupsEq. intuition.
      (* END multiplexerIsPDT *)
    }
    assert(currentPartitionInPartitionsList s).
    { (* BEGIN currentPartitionInPartitionsList s *)
      assert(Hcons0: currentPartitionInPartitionsList s0) by intuition. unfold currentPartitionInPartitionsList.
      rewrite Hcurr. rewrite getPartitionsEqLookup with multiplexer s s0; assumption.
      (* END currentPartitionInPartitionsList *)
    }
    assert(wellFormedShadowCutIfBlockEntry s).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s0) by intuition.
      intros block HblockIsBE. unfold isBE in HblockIsBE. unfold isSCE. rewrite HlookupsEq in *.
      specialize(Hcons0 block HblockIsBE). destruct Hcons0 as [scentryaddr Hsce]. exists scentryaddr.
      rewrite HlookupsEq. assumption.
      (* END wellFormedShadowCutIfBlockEntry *)
    }
    assert(BlocksRangeFromKernelStartIsBE s).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by intuition. intros kernel blockidx HkernIsKS Hblockidx.
      unfold isKS in HkernIsKS. unfold isBE. rewrite HlookupsEq in *.
      specialize(Hcons0 kernel blockidx HkernIsKS Hblockidx). assumption.
      (* END BlocksRangeFromKernelStartIsBE *)
    }
    assert(KernelStructureStartFromBlockEntryAddrIsKS s).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s*)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0) by intuition.
      intros block blockidx HblockIsBE Hblockidx. unfold isBE in HblockIsBE. unfold bentryBlockIndex in Hblockidx.
      unfold isKS. rewrite HlookupsEq in *. specialize(Hcons0 block blockidx HblockIsBE Hblockidx). assumption.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }
    assert(sh1InChildLocationIsBE s).
    { (* BEGIN sh1InChildLocationIsBE s*)
      assert(Hcons0: sh1InChildLocationIsBE s0) by intuition.
      intros sh1entryaddrBis sh1entryBis HlookupSh1Bis HbeqInChildNull. unfold isBE. rewrite HlookupsEq in *.
      specialize(Hcons0 sh1entryaddrBis sh1entryBis HlookupSh1Bis HbeqInChildNull). assumption.
      (* END sh1InChildLocationIsBE *)
    }
    assert(StructurePointerIsKS s).
    { (* BEGIN StructurePointerIsKS s *)
      assert(Hcons0: StructurePointerIsKS s0) by intuition. intros partition pdentry HlookupPart HbeqStructNull.
      unfold isKS. rewrite HlookupsEq in *. specialize(Hcons0 partition pdentry HlookupPart HbeqStructNull).
      assumption.
      (* END StructurePointerIsKS *)
    }
    assert(NextKSIsKS s).
    { (* BEGIN NextKSIsKS s *)
      assert(Hcons0: NextKSIsKS s0) by intuition. intros kernel nextKSaddr nextKS HkernIsKS HnextKSAddr HnextKS.
      unfold isKS in *. unfold nextKSAddr in HnextKSAddr. unfold nextKSentry in HnextKS. rewrite HlookupsEq in *.
      specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextKSAddr HnextKS). assumption.
      (* END NextKSIsKS *)
    }
    assert(NextKSOffsetIsPADDR s).
    { (* BEGIN NextKSOffsetIsPADDR s *)
      assert(Hcons0: NextKSOffsetIsPADDR s0) by intuition. intros kern nextksaddr HkernIsKS HnextIsNext.
      unfold isKS in HkernIsKS. unfold nextKSAddr in HnextIsNext. unfold isPADDR. rewrite HlookupsEq in *.
      specialize(Hcons0 kern nextksaddr HkernIsKS HnextIsNext). assumption.
      (* END NextKSOffsetIsPADDR *)
    }
    assert(NoDupInFreeSlotsList s).
    { (* BEGIN NoDupInFreeSlotsList s *)
      assert(Hcons0: NoDupInFreeSlotsList s0) by intuition. intros partition pdentry HlookupPart.
      rewrite HlookupsEq in *. rewrite getFreeSlotsListEqLookup with partition s s0; try(assumption).
      specialize(Hcons0 partition pdentry HlookupPart). assumption.
      (* END NoDupInFreeSlotsList *)
    }
    assert(freeSlotsListIsFreeSlot s).
    { (* BEGIN freeSlotsListIsFreeSlot s *)
      assert(Hcons0: freeSlotsListIsFreeSlot s0) by intuition.
      intros partition freeslot optionfreeslotslist freeslotslist HpartIsPDT Hoption HslotsList HbeqFreeNull.
      rewrite getFreeSlotsListEqLookup with partition s s0 in Hoption; try(assumption).
      unfold isPDT in HpartIsPDT. unfold isFreeSlot. rewrite HlookupsEq in *.
      specialize(Hcons0 partition freeslot optionfreeslotslist freeslotslist HpartIsPDT Hoption HslotsList
        HbeqFreeNull). unfold isFreeSlot in Hcons0.
      destruct (lookup freeslot (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite HlookupsEq. destruct (lookup (CPaddr (freeslot + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). rewrite HlookupsEq. assumption.
      (* END freeSlotsListIsFreeSlot *)
    }
    assert(DisjointFreeSlotsLists s).
    { (* BEGIN DisjointFreeSlotsLists s *)
      assert(Hcons0: DisjointFreeSlotsLists s0) by intuition.
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2. unfold isPDT in *.
      rewrite getFreeSlotsListEqLookup with part1 s s0; try(assumption).
      rewrite getFreeSlotsListEqLookup with part2 s s0; try(assumption). rewrite HlookupsEq in *.
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2). assumption.
      (* END DisjointFreeSlotsLists *)
    }
    assert(inclFreeSlotsBlockEntries s).
    { (* BEGIN inclFreeSlotsBlockEntries s *)
      assert(Hcons0: inclFreeSlotsBlockEntries s0) by intuition. intros partition HpartIsPDT.
      unfold isPDT in *. rewrite HlookupsEq in *. specialize(Hcons0 partition HpartIsPDT).
      rewrite getFreeSlotsListEqLookup with partition s s0; try(assumption).
      rewrite getKSEntriesEqLookup with partition s s0; assumption.
      (* END inclFreeSlotsBlockEntries *)
    }
    assert(DisjointKSEntries s).
    { (* BEGIN DisjointKSEntries s *)
      assert(Hcons0: DisjointKSEntries s0) by intuition.
      intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2. unfold isPDT in *. rewrite HlookupsEq in *.
      rewrite getKSEntriesEqLookup with part1 s s0; try(assumption).
      rewrite getKSEntriesEqLookup with part2 s s0; try(assumption).
      specialize(Hcons0 part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqPart1Part2). assumption.
      (* END DisjointKSEntries *)
    }
    assert(noDupPartitionTree s).
    { (* BEGIN noDupPartitionTree s *)
      assert(Hcons0: noDupPartitionTree s0) by intuition. unfold noDupPartitionTree in *.
      rewrite getPartitionsEqLookup with multiplexer s s0; assumption.
      (* END noDupPartitionTree *)
    }
    assert(isParent s).
    { (* BEGIN isParent s *)
      assert(Hcons0: isParent s0) by intuition. intros partition pdparent HparentIsPart HpartIsChild.
      unfold pdentryParent. rewrite HlookupsEq.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0 in HpartIsChild; try(assumption).
      specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). assumption.
      (* END isParent *)
    }
    assert(isChild s).
    { (* BEGIN isChild s *)
      assert(Hcons0: isChild s0) by intuition. intros partition pdparent HpartIsPart HparentIsParent.
      unfold pdentryParent in *. rewrite HlookupsEq in *.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0; try(assumption).
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent). assumption.
      (* END isChild *)
    }
    assert(noDupKSEntriesList s).
    { (* BEGIN noDupKSEntriesList s *)
      assert(Hcons0: noDupKSEntriesList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition HpartIsPDT).
      rewrite getKSEntriesEqLookup with partition s s0; assumption.
      (* END noDupKSEntriesList *)
    }
    assert(noDupMappedBlocksList s).
    { (* BEGIN noDupMappedBlocksList s *)
      assert(Hcons0: noDupMappedBlocksList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition HpartIsPDT).
      rewrite getMappedBlocksEqLookup with partition s s0; assumption.
      (* END noDupMappedBlocksList *)
    }
    assert(wellFormedBlock s).
    { (* BEGIN wellFormedBlock s *)
      assert(Hcons0: wellFormedBlock s0) by intuition. intros block startaddr endaddr HPFlag Hstart Hend.
      unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupsEq in *.
      specialize(Hcons0 block startaddr endaddr HPFlag Hstart Hend). assumption.
      (* END wellFormedBlock *)
    }
    assert(parentOfPartitionIsPartition s).
    { (* BEGIN parentOfPartitionIsPartition s *)
      assert(Hcons0: parentOfPartitionIsPartition s0) by intuition. intros partition pdentry HlookupPart.
      rewrite HlookupsEq in *. specialize(Hcons0 partition pdentry HlookupPart).
      rewrite getPartitionsEqLookup with multiplexer s s0; assumption.
      (* END parentOfPartitionIsPartition *)
    }
    assert(NbFreeSlotsISNbFreeSlotsInList s).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0) by intuition.
      intros partition nbfreeslots HpartIsPDT HnbFree. unfold isPDT in *. unfold pdentryNbFreeSlots in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition nbfreeslots HpartIsPDT HnbFree).
      rewrite getFreeSlotsListEqLookup with partition s s0; assumption.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }
    assert(maxNbPrepareIsMaxNbKernels s).
    { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by intuition. intros partition kernList HkernList.
      rewrite isListOfKernelsEqLookup with kernList partition s s0 in HkernList; try(assumption).
      specialize(Hcons0 partition kernList HkernList). assumption.
      (* END maxNbPrepareIsMaxNbKernels *)
    }
    assert(blockInChildHasAtLeastEquivalentBlockInParent s).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0) by intuition.
      intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild Hstart Hend
        HPFlag. rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0 in HchildIsChild; try(assumption).
      rewrite getMappedBlocksEqLookup with child s s0 in HblockMappedChild; try(assumption).
      rewrite getMappedBlocksEqLookup with pdparent s s0; try(assumption). unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite HlookupsEq in *.
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        Hstart Hend HPFlag). destruct Hcons0 as [blockParent [startParent [endParent Hcons0]]].
      exists blockParent. exists startParent. exists endParent. rewrite HlookupsEq. assumption.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }
    assert(partitionTreeIsTree s).
    { (* BEGIN  partitionTreeIsTrees *)
      assert(Hcons0: partitionTreeIsTree s0) by intuition.
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsparent HparentsList.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HchildIsPart; try(assumption).
      unfold pdentryParent in *. rewrite HlookupsEq in *.
      rewrite isParentsListEqLookup with parentsList pdparent s s0 in HparentsList; try(assumption).
      specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsparent HparentsList).
      assumption.
      (* END partitionTreeIsTree *)
    }
    assert(kernelEntriesAreValid s).
    { (* BEGIN kernelEntriesAreValid s *)
      assert(Hcons0: kernelEntriesAreValid s0) by intuition. intros kernel idx HkernisKS Hidx.
      unfold isKS in *. unfold isBE. rewrite HlookupsEq in *. specialize(Hcons0 kernel idx HkernisKS Hidx).
      assumption.
      (* END kernelEntriesAreValid *)
    }
    assert(nextKernelIsValid s).
    { (* BEGIN nextKernelIsValid s *)
      assert(Hcons0: nextKernelIsValid s0) by intuition. intros kernel HkernisKS. unfold isKS in *.
      rewrite HlookupsEq in *. specialize(Hcons0 kernel HkernisKS). split. apply Hcons0.
      destruct Hcons0 as (_ & [nextAddr Hcons0]). exists nextAddr. rewrite HlookupsEq.
      split; try(apply Hcons0). destruct Hcons0 as (Hcons0 & _). intro Hp. rewrite HlookupsEq. apply Hcons0.
      (* END nextKernelIsValid *)
    }
    assert(noDupListOfKerns s).
    { (* BEGIN noDupListOfKerns s *)
      assert(Hcons0: noDupListOfKerns s0) by intuition. intros partition kernList HkernList.
      rewrite isListOfKernelsEqLookup with kernList partition s s0 in HkernList; try(assumption).
      specialize(Hcons0 partition kernList HkernList). assumption.
      (* END noDupListOfKerns *)
    }
    assert(MPUsizeIsBelowMax s).
    { (* BEGIN MPUsizeIsBelowMax s *)
      assert(Hcons0: MPUsizeIsBelowMax s0) by intuition. intros partition MPUlist HMPU.
      unfold pdentryMPU in *. rewrite HlookupsEq in *. specialize(Hcons0 partition MPUlist HMPU). assumption.
      (* END MPUsizeIsBelowMax *)
    }
    assert(originIsParentBlocksStart s).
    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s0) by intuition.
      intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getMappedBlocksEqLookup with partition s s0 in HblockMapped; try(assumption).
      unfold scentryOrigin in *. rewrite HlookupsEq in *.
      specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
        Horigin). destruct Hcons0 as (Hleft & Hright). unfold bentryStartAddr. rewrite HlookupsEq.
      split; try(assumption). intro HbeqPartRoot. specialize(Hleft HbeqPartRoot).
      destruct Hleft as [blockParent Hleft]. exists blockParent. rewrite HlookupsEq.
      rewrite getAllPaddrAuxEqLookup with [block] s s0; try(assumption).
      rewrite getAllPaddrAuxEqLookup with [blockParent] s s0; try(assumption).
      rewrite getMappedBlocksEqLookup with (parent pdentry) s s0; assumption.
      (* END originIsParentBlocksStart *)
    }
    assert(nextImpliesBlockWasCut s).
    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s0) by intuition.
      intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped Hend Hsce
        HbeqNextNull Hnext HbeqPartRoot.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getMappedBlocksEqLookup with partition s s0 in HblockMapped; try(assumption).
      unfold bentryEndAddr in *. unfold scentryNext in *. rewrite HlookupsEq in *.
      specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
        Hend Hsce HbeqNextNull Hnext HbeqPartRoot). destruct Hcons0 as [blockParent [endParent Hcons0]].
      exists blockParent. exists endParent. rewrite HlookupsEq.
      rewrite getAllPaddrAuxEqLookup with [block] s s0; try(assumption).
      rewrite getAllPaddrAuxEqLookup with [blockParent] s s0; try(assumption).
      rewrite getMappedBlocksEqLookup with (parent pdentry) s s0; assumption.
      (* END nextImpliesBlockWasCut *)
    }
    assert(blocksAddressesTypes s).
    { (* BEGIN blocksAddressesTypes s *)
      assert(Hcons0: blocksAddressesTypes s0) by intuition. intros block startaddr endaddr Hstart Hend.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold isKS in *. unfold isPDT in *.
      rewrite HlookupsEq in *. specialize(Hcons0 block startaddr endaddr Hstart Hend).
      destruct Hcons0 as [HKS | [HPDT | Hnone]].
      - left. split. apply HKS. intro addr. unfold isBE. unfold isSHE. unfold isSCE. rewrite HlookupsEq.
        apply HKS.
      - right. left. split. apply HPDT. intro addr. unfold isBE. unfold isSHE. unfold isSCE. rewrite HlookupsEq.
        apply HPDT.
      - right. right. intro addr. unfold isBE. unfold isSHE. unfold isSCE. rewrite HlookupsEq. apply Hnone.
      (* END blocksAddressesTypes *)
    }
    assert(notPDTIfNotPDflag s).
    { (* BEGIN notPDTIfNotPDflag s *)
      assert(Hcons0: notPDTIfNotPDflag s0) by intuition.
      intros block startaddr sh1entryaddrBis Hstart Hsh1 HPDFlag. unfold bentryStartAddr in *.
      unfold sh1entryAddr in *. unfold sh1entryPDflag in *. unfold isPDT. rewrite HlookupsEq in *.
      specialize(Hcons0 block startaddr sh1entryaddrBis Hstart Hsh1 HPDFlag). assumption.
      (* END notPDTIfNotPDflag *)
    }
    assert(nextKernAddrIsInSameBlock s).
    { (* BEGIN nextKernAddrIsInSameBlock s *)
      assert(Hcons0: nextKernAddrIsInSameBlock s0) by intuition.
      intros block kernel startaddr endaddr Hstart Hend HkernIsKS HnextInBlock. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. unfold isKS in *. rewrite HlookupsEq in *.
      specialize(Hcons0 block kernel startaddr endaddr Hstart Hend HkernIsKS HnextInBlock). assumption.
      (* END nextKernAddrIsInSameBlock *)
    }
    assert(noDupUsedPaddrList s).
    { (* BEGIN noDupUsedPaddrList s *)
      assert(Hcons0: noDupUsedPaddrList s0) by intuition. intros partition HpartIsPDT. unfold isPDT in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition HpartIsPDT).
      rewrite getUsedPaddrEqLookup with partition s s0; assumption.
      (* END noDupUsedPaddrList *)
    }
    assert(accessibleParentPaddrIsAccessibleIntoChild s).
    { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
      assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s0) by intuition.
      intros pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0 in HchildIsChild; try(assumption).
      rewrite getAccessibleMappedPaddrEqLookup with pdparent s s0 in HaddrAccParent; try(assumption).
      rewrite getMappedPaddrEqLookup with child s s0 in HaddrMappedChild; try(assumption).
      specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild).
      rewrite getAccessibleMappedPaddrEqLookup with child s s0; assumption.
      (* END accessibleParentPaddrIsAccessibleIntoChild *)
    }
    assert(sharedBlockPointsToChild s).
    { (* BEGIN sharedBlockPointsToChild s *)
      assert(Hcons0: sharedBlockPointsToChild s0) by intuition.
      intros pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParent HblockParentMapped Hsh1Bis.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with pdparent s s0 in HchildIsChild; try(assumption).
      rewrite getUsedPaddrEqLookup with child s s0 in HaddrUsedChild; try(assumption).
      rewrite getAllPaddrAuxEqLookup with [blockParent] s s0 in HaddrInBlockParent; try(assumption).
      rewrite getMappedBlocksEqLookup with pdparent s s0 in HblockParentMapped; try(assumption).
      unfold sh1entryAddr in *. unfold sh1entryPDchild. unfold sh1entryPDflag. rewrite HlookupsEq in *.
      specialize(Hcons0 pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParent HblockParentMapped Hsh1Bis). assumption.
      (* END sharedBlockPointsToChild *)
    }
    assert(adressesRangePreservedIfOriginAndNextOk s).
    { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
      assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0) by intuition.
      intros partition pdentry block scentryaddr start endaddr HpartIsPart HblockMapped HblockIsBE Hstart Hend
        HPFlag Hsce Horigin Hnext HlookupPart HbeqPartRoot.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getMappedBlocksEqLookup with partition s s0 in HblockMapped; try(assumption). unfold isBE in *.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. unfold scentryOrigin in *.
      unfold scentryNext in *. rewrite HlookupsEq in *.
      rewrite getMappedBlocksEqLookup with (parent pdentry) s s0; try(assumption).
      specialize(Hcons0 partition pdentry block scentryaddr start endaddr HpartIsPart HblockMapped HblockIsBE
        Hstart Hend HPFlag Hsce Horigin Hnext HlookupPart HbeqPartRoot). destruct Hcons0 as [blockParent Hcons0].
      exists blockParent. rewrite HlookupsEq. assumption.
      (* END adressesRangePreservedIfOriginAndNextOk *)
    }
    assert(childsBlocksPropsInParent s).
    { (* BEGIN childsBlocksPropsInParent s *)
      assert(Hcons0: childsBlocksPropsInParent s0) by intuition.
      intros child parentPart blockChild startChild endChild blockParent startParent endParent HparentIsPart
        HchildIsChild HchildMapped HstartChild HendChild HPFlagChild HparentMapped HparentStart HparentEnd
        HPFlagParent HleStart HgeEnd.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
      rewrite getChildrenEqLookup with parentPart s s0 in HchildIsChild; try(assumption).
      rewrite getMappedBlocksEqLookup with child s s0 in HchildMapped; try(assumption).
      rewrite getMappedBlocksEqLookup with parentPart s s0 in HparentMapped; try(assumption).
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. unfold checkChild.
      unfold sh1entryPDchild. unfold sh1entryInChildLocation. unfold bentryAFlag. unfold isBE.
      rewrite HlookupsEq in *. specialize(Hcons0 child parentPart blockChild startChild endChild blockParent
        startParent endParent HparentIsPart HchildIsChild HchildMapped HstartChild HendChild HPFlagChild
        HparentMapped HparentStart HparentEnd HPFlagParent HleStart HgeEnd).
      destruct Hcons0 as (HcheckChild & HPDChild & HinChildLoc & HAFlagParent). unfold checkChild in *.
      unfold sh1entryPDchild in *. unfold sh1entryInChildLocation in *. unfold bentryAFlag in *.
      split; try(split; try(split)).
      - destruct (lookup blockParent (memory s0) beqAddr); try(reflexivity). destruct v; try(reflexivity).
        rewrite HlookupsEq. assumption.
      - intro childGlobalID. rewrite HlookupsEq. apply HPDChild.
      - intros blockIDInChild HchildLoc. rewrite HlookupsEq in HchildLoc. apply HinChildLoc.
        destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). rewrite HlookupsEq in HchildLoc. assumption.
      - assumption.
      (* END childsBlocksPropsInParent *)
    }
    assert(noChildImpliesAddressesNotShared s).
    { (* BEGIN noChildImpliesAddressesNotShared s *)
      assert(Hcons0: noChildImpliesAddressesNotShared s0) by intuition.
      intros partition pdentry block sh1entryaddrBis HpartIsPart HlookupPart HblockMapped Hsh1Bis HPDChild child
        addr HchildIsChild HaddrInBlock.
      rewrite getPartitionsEqLookup with multiplexer s s0 in HpartIsPart; try(assumption).
      rewrite getMappedBlocksEqLookup with partition s s0 in HblockMapped; try(assumption).
      rewrite getChildrenEqLookup with partition s s0 in HchildIsChild; try(assumption).
      rewrite getAllPaddrAuxEqLookup with [block] s s0 in HaddrInBlock; try(assumption).
      rewrite getMappedPaddrEqLookup with child s s0; try(assumption). unfold sh1entryPDchild in *.
      rewrite HlookupsEq in *. specialize(Hcons0 partition pdentry block sh1entryaddrBis HpartIsPart HlookupPart
        HblockMapped Hsh1Bis HPDChild child addr HchildIsChild HaddrInBlock). assumption.
      (* END noChildImpliesAddressesNotShared *)
    }
    assert(kernelsAreNotAccessible s).
    { (* BEGIN kernelsAreNotAccessible s *)
      assert(Hcons0: kernelsAreNotAccessible s0) by intuition. intros block startaddr Hstart HstartIsKS.
      unfold bentryStartAddr in *. unfold isKS in *. unfold bentryAFlag. rewrite HlookupsEq in *.
      specialize(Hcons0 block startaddr Hstart HstartIsKS). assumption.
      (* END kernelsAreNotAccessible *)
    }
    intuition.
  }
  split.
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
    rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
    rewrite getChildrenEqLookup with pdparent s s0 in Hchild1IsChild; try(assumption).
    rewrite getChildrenEqLookup with pdparent s s0 in Hchild2IsChild; try(assumption).
    rewrite getUsedPaddrEqLookup with child1 s s0; try(assumption).
    rewrite getUsedPaddrEqLookup with child2 s s0; try(assumption).
    specialize(HPIs0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
    assumption.
    (* END partitionsIsolation *)
  }
  split.
  { (* BEGIN kernelDataIsolation s *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart.
    rewrite getPartitionsEqLookup with multiplexer s s0 in Hpart1IsPart; try(assumption).
    rewrite getPartitionsEqLookup with multiplexer s s0 in Hpart2IsPart; try(assumption).
    rewrite getAccessibleMappedPaddrEqLookup with part1 s s0; try(assumption).
    rewrite getConfigPaddrEqLookup with part2 s s0; try(assumption).
    specialize(HKDIs0 part1 part2 Hpart1IsPart Hpart2IsPart). assumption.
    (* END kernelDataIsolation *)
  }
  split.
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild.
    rewrite getPartitionsEqLookup with multiplexer s s0 in HparentIsPart; try(assumption).
    rewrite getChildrenEqLookup with pdparent s s0 in HchildIsChild; try(assumption).
    rewrite getUsedPaddrEqLookup with child s s0; try(assumption).
    rewrite getMappedPaddrEqLookup with pdparent s s0; try(assumption).
    specialize(HVSs0 pdparent child HparentIsPart HchildIsChild). assumption.
    (* END verticalSharing *)
  }
  split. assumption. split. rewrite Hcurr. assumption. split. unfold isPDT. rewrite HlookupsEq. assumption.
  split.
  {
    exists bentry. unfold bentryPFlag. rewrite HlookupsEq.
    rewrite getMappedBlocksEqLookup with currentPart s s0; try(assumption). intuition.
  }
  split. assumption. split. unfold bentryAFlag. rewrite HlookupsEq. assumption. split. assumption. split.
  assumption. split. assumption. split. assumption. split.
  {
    exists sh1entry. exists sh1entryaddr. unfold sh1entryPDchild. unfold sh1entryAddr. rewrite HlookupsEq.
    rewrite HlookupsEq. intuition.
  }
  split. unfold bentryStartAddr. rewrite HlookupsEq. assumption. split. unfold bentryEndAddr. rewrite HlookupsEq.
  assumption. split.
  {
    destruct Hbounds as [startaddr [endaddr (Hstart & Hend & Hres)]]. unfold bentryStartAddr in *.
    unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *. subst startaddr. subst endaddr.
    rewrite <-HstartBlock in *. rewrite <-HendBlock in *. assumption.
  }
  assumption.
}
intro. eapply bindRev.
{ (* MAL.writePDParent *)
  eapply weaken. apply writePDParent. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s0 (_ & Hs)]. rewrite Hs. simpl. rewrite beqAddrTrue.
  reflexivity.
}
intro. simpl. eapply bindRev.
{ (* MAL.writeBlockAccessibleFromBlockEntryAddr *)
  eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as [s1 [newPDEntry ([s0 ((HPI & HKDI & HVS & Hconsist & Hcurr & HcurrIsPDTs0 & Hblock
    & HbeqNullBlock & HAFlagBlock & HminSize & HltSizeMin & HtotalLen & HltSizeTot & HPDChild
    & HstartBlock & HendBlock & HsizeBlock & HremovedAddr) & Hs1)] & HlookupNewPD & Hs &
    HnewPDEntry)]]. destruct Hblock as [bentry (HlookupBlock & HblockEq & HPFlagBlock & HblockMapped)].
  rewrite HblockEq in *.
  assert(HlookupEqss1: forall addr, newPDBlockStartAddr <> addr
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s1) beqAddr).
  {
    intros addr HbeqNewPDAddr. rewrite Hs. simpl. rewrite beqAddrFalse in HbeqNewPDAddr. rewrite HbeqNewPDAddr.
    rewrite <-beqAddrFalse in HbeqNewPDAddr. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    reflexivity.
  }
  assert(HlookupEqs1s0: forall addr, newPDBlockStartAddr <> addr
                      -> lookup addr (memory s1) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intros addr HbeqNewPDAddr. rewrite Hs1. simpl. rewrite beqAddrFalse in HbeqNewPDAddr. rewrite HbeqNewPDAddr.
    rewrite <-beqAddrFalse in HbeqNewPDAddr. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    reflexivity.
  }
  assert(HlookupEqss0: forall addr, newPDBlockStartAddr <> addr
                      -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intros addr HbeqNewPDAddr. rewrite HlookupEqss1; try(assumption). apply HlookupEqs1s0. assumption.
  }
  set(newBEntry := CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) false
                    (blockindex bentry) (blockrange bentry)).
  assert(HnewB: exists l, newBEntry = {|
                                        read := read bentry;
                                        write := write bentry;
                                        exec := exec bentry;
                                        present := present bentry;
                                        accessible := false;
                                        blockindex := blockindex bentry;
                                        blockrange := blockrange bentry;
                                        Hidx := l
                                      |}).
  {
    subst newBEntry. unfold CBlockEntry. assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
    destruct (lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
    exists (ADT.CBlockEntry_obligation_1 (blockindex bentry) l). reflexivity.
  }
  assert(HwellFormed: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  specialize(HwellFormed idBlock newPDBlockStartAddr newPDBlockEndAddr HPFlagBlock HstartBlock HendBlock).
  destruct HwellFormed as (HwellFormed & _).
  destruct (beqAddr newPDBlockStartAddr idBlock) eqn:HbeqNewPDBlock.
  {
    rewrite <-DTL.beqAddrTrue in HbeqNewPDBlock. subst newPDBlockStartAddr.
    assert(Htypes: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HkernNotAcc: kernelsAreNotAccessible s0)
      by (unfold consistency in *; unfold consistency2 in *; intuition).
    specialize(Htypes idBlock idBlock newPDBlockEndAddr HstartBlock HendBlock). exfalso.
    destruct Htypes as [HKS | [HPDT | Hnull]].
    - destruct HKS as (HKS & _). specialize(HkernNotAcc idBlock idBlock HstartBlock HKS). unfold bentryAFlag in *.
      rewrite HlookupBlock in *. congruence.
    - destruct HPDT as (HPDT & _). unfold isPDT in HPDT. rewrite HlookupBlock in HPDT. congruence.
    - assert(HstartInRange: In idBlock (getAllPaddrBlock idBlock newPDBlockEndAddr)).
      { apply getAllPaddrBlockIncl; lia. }
      specialize(Hnull idBlock HstartInRange). congruence.
  }
  assert(HlookupBlocks: lookup idBlock (memory s) beqAddr = Some (BE bentry)).
  {
    rewrite Hs. simpl. rewrite HbeqNewPDBlock.
    rewrite <-beqAddrFalse in HbeqNewPDBlock. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite Hs1. simpl. rewrite beqAddrFalse in HbeqNewPDBlock. rewrite HbeqNewPDBlock.
    rewrite <-beqAddrFalse in HbeqNewPDBlock. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    assumption.
  }
  exists bentry. split. assumption. fold newBEntry.
  instantiate(1 := fun _ s =>
    exists s2 s1 s0 newBEntry bentry newPDEntry,
      s = {|
            currentPartition := currentPartition s2; memory := add idBlock (BE newBEntry) (memory s2) beqAddr
          |}
      /\ (exists l,
            newBEntry =
            {|
              read := read bentry;
              write := write bentry;
              exec := exec bentry;
              present := present bentry;
              accessible := false;
              blockindex := blockindex bentry;
              blockrange := blockrange bentry;
              Hidx := l
            |})
      /\ blockInCurrentPartitionAddr = idBlock
      (* properties of s2 *)
      /\ lookup idBlock (memory s2) beqAddr = Some (BE bentry)
      /\ (forall addr, newPDBlockStartAddr <> addr
            -> lookup addr (memory s2) beqAddr = lookup addr (memory s0) beqAddr)
      /\ lookup newPDBlockStartAddr (memory s2) beqAddr = Some (PDT newPDEntry)
      /\ newPDEntry =
          {|
            structure := nullAddr;
            firstfreeslot := nullAddr;
            nbfreeslots := zero;
            nbprepare := zero;
            parent := currentPart;
            MPU := [];
            vidtAddr := nullAddr
          |}
      /\ s2 =
          {|
            currentPartition := currentPartition s1;
            memory := add newPDBlockStartAddr (PDT newPDEntry) (memory s1) beqAddr
          |}
      (* properties of s1 *)
      /\ s1 =
          {|
            currentPartition := currentPartition s0;
            memory :=
              add newPDBlockStartAddr
                (PDT
                   {|
                     structure := nullAddr;
                     firstfreeslot := nullAddr;
                     nbfreeslots := zero;
                     nbprepare := zero;
                     parent := nullAddr;
                     MPU := [];
                     vidtAddr := nullAddr
                   |}) (memory s0) beqAddr
          |}
      (* properties of s0 *)
      /\ (forall addr, In addr (getAllPaddrBlock newPDBlockStartAddr newPDBlockEndAddr)
          -> lookup addr (memory s0) beqAddr = None)
      /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ consistency s0
      /\ isPDT currentPart s0
      /\ currentPart = currentPartition s0
      /\ bentryStartAddr idBlock newPDBlockStartAddr s0
      /\ bentryEndAddr idBlock newPDBlockEndAddr s0
      /\ bentryAFlag idBlock true s0 /\ bentryPFlag idBlock true s0
      /\ In idBlock (getMappedBlocks currentPart s0)
      /\ lookup idBlock (memory s0) beqAddr = Some (BE bentry)
      /\ (exists sh1entry sh1entryaddr, lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
            /\ sh1entryPDchild sh1entryaddr PDChildAddr s0 /\ sh1entryAddr idBlock sh1entryaddr s0)
      (* other properties *)
      /\ beqAddr newPDBlockStartAddr idBlock = false
      /\ beqAddr nullAddr idBlock = false
      /\ minBlockSize = Constants.minBlockSize
      /\ false = indexLt blockSize minBlockSize
      /\ PDStructureTotalLength = Constants.PDStructureTotalLength
      /\ false = indexLt blockSize PDStructureTotalLength
      /\ i blockSize = newPDBlockEndAddr - newPDBlockStartAddr).
  simpl. exists s. exists s1. exists s0. exists newBEntry. exists bentry. exists newPDEntry. intuition.
}
intro. eapply bindRev.
{ (* MAL.removeBlockFromPhysicalMPU *)
  eapply weaken. apply removeBlockFromPhysicalMPU. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [s2 [s1 [s0 [newBEntry [bentry [newPDEntry (Hs & Hprops)]]]]]].
  assert(HcurrIsPDTs0: isPDT currentPart s0) by intuition. unfold isPDT in *. rewrite Hs. simpl.
  destruct (beqAddr idBlock currentPart) eqn:HbeqBlockCurr.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockCurr. subst idBlock.
    assert(Hlookup: lookup currentPart (memory s0) beqAddr = Some (BE bentry)) by intuition.
    rewrite Hlookup in *. congruence.
  }
  rewrite <-beqAddrFalse in HbeqBlockCurr. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  assert(Hs2: s2 =
                  {|
                    currentPartition := currentPartition s1;
                    memory := add newPDBlockStartAddr (PDT newPDEntry) (memory s1) beqAddr
                  |}) by intuition.
  assert(Hs1: s1 =
                  {|
                    currentPartition := currentPartition s0;
                    memory :=
                      add newPDBlockStartAddr
                        (PDT
                           {|
                             structure := nullAddr;
                             firstfreeslot := nullAddr;
                             nbfreeslots := zero;
                             nbprepare := zero;
                             parent := nullAddr;
                             MPU := [];
                             vidtAddr := nullAddr
                           |}) (memory s0) beqAddr
                  |}) by intuition.
  rewrite Hs2. rewrite Hs1. simpl. destruct (beqAddr newPDBlockStartAddr currentPart) eqn:HbeqNewPDCurr; trivial.
  rewrite beqAddrTrue. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
  rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
}
intro. eapply bindRev.
{ (* MAL.writeSh1PDFlagFromBlockEntryAddr *)
  eapply weaken. apply writeSh1PDFlagFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as [s3 [pdentry [realMPU (HMPU & [s2 [s1 [s0 [newBentry [bentry [newPDEntry (Hs3 & HnewBEntry &
    HblocksEq & HlookupBlocks2 & HlookupEqs2s0 & HlookupNewPDs2 & HnewPD & Hs2 & Hs1 & HremovedAddr & HPIs0 &
    HKDIs0 & HVSs0 & Hconsists0 & HcurrIsPDTs0 & Hcurr & HstartBlock & HendBlock & HAFlagBlock & HPFlagBlock &
    HblockMapped & HlookupBlocks0 & Hsh1 & HbeqNewPDBlock & HbeqNullBlock & Hmin & HltSizeMin & Hlen &
    HltSizeLen & HsizeBlock)]]]]]] & HlookupCurrs3 & Hs)]]].

  destruct (beqAddr idBlock currentPart) eqn:HbeqBlockCurr.
  {
    rewrite <-DTL.beqAddrTrue in HbeqBlockCurr. rewrite HbeqBlockCurr in *. unfold isPDT in HcurrIsPDTs0.
    rewrite HlookupBlocks0 in *. exfalso; congruence.
  }
  assert(HstartInRange: In newPDBlockStartAddr (getAllPaddrBlock newPDBlockStartAddr newPDBlockEndAddr)).
  {
    assert(HwellFormed: wellFormedBlock s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HwellFormed idBlock newPDBlockStartAddr newPDBlockEndAddr HPFlagBlock HstartBlock HendBlock).
    destruct HwellFormed. apply getAllPaddrBlockIncl; lia.
  }
  assert(HbeqCurrBlock: beqAddr currentPart idBlock = false) by (rewrite beqAddrSym; assumption).
  specialize(HremovedAddr newPDBlockStartAddr HstartInRange).
  assert(HlookupBlocks: lookup idBlock (memory s) beqAddr = Some(BE newBentry)).
  {
    rewrite Hs. rewrite Hs3. simpl. rewrite HbeqCurrBlock. rewrite HbeqBlockCurr. simpl. rewrite beqAddrTrue.
    reflexivity.
  }
  destruct HnewBEntry as [l HnewBEntry].
  assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)).
  {
    rewrite Hs3 in HlookupCurrs3. simpl in HlookupCurrs3. rewrite HbeqBlockCurr in HlookupCurrs3.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupCurrs3; try(apply not_eq_sym; assumption).
    rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    rewrite HremovedAddr in *. congruence.
  }
  set(newPDCurr := {|
                      structure := structure pdentry;
                      firstfreeslot := firstfreeslot pdentry;
                      nbfreeslots := nbfreeslots pdentry;
                      nbprepare := nbprepare pdentry;
                      parent := parent pdentry;
                      MPU := MAL.removeBlockFromPhysicalMPUAux blockInCurrentPartitionAddr realMPU;
                      vidtAddr := vidtAddr pdentry
                    |}). fold newPDCurr in Hs.
  assert(HlookupCurrs: lookup currentPart (memory s) beqAddr = Some (PDT newPDCurr)).
  {
    rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity.
  }
  assert(HblockNotFree: ~isFreeSlot idBlock s0).
  {
    unfold isFreeSlot. unfold bentryPFlag in HPFlagBlock. rewrite HlookupBlocks0 in *.
    destruct (lookup (CPaddr (idBlock + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (lookup (CPaddr (idBlock + scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). intro Hcontra. destruct Hcontra as (_ & _ & _ & _ & Hcontra & _). congruence.
  }
  destruct (beqAddr currentPart newPDBlockStartAddr) eqn:HbeqCurrStart.
  {
    rewrite <-DTL.beqAddrTrue in HbeqCurrStart. rewrite HbeqCurrStart in *. exfalso; congruence.
  }
  assert(HlookupNewPDs: lookup newPDBlockStartAddr (memory s) beqAddr = Some (PDT newPDEntry)).
  {
    rewrite Hs. rewrite Hs3. simpl. rewrite HbeqCurrStart. rewrite HbeqBlockCurr. simpl.
    rewrite beqAddrSym in HbeqNewPDBlock. rewrite HbeqNewPDBlock. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
  }

  assert(nullAddrExists s).
  { (* BEGIN nullAddrExists s *)
    assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart nullAddr) eqn:HbeqCurrNull.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrNull. rewrite HbeqCurrNull in *. unfold isPDT in *.
      destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HbeqBlockCurr. simpl. rewrite beqAddrSym in HbeqNullBlock. rewrite HbeqNullBlock.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (beqAddr newPDBlockStartAddr nullAddr) eqn:HbeqNewPDNull.
    {
      rewrite <-DTL.beqAddrTrue in HbeqNewPDNull. subst newPDBlockStartAddr. exfalso.
      assert(Htypes: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      specialize(Htypes idBlock nullAddr newPDBlockEndAddr HstartBlock HendBlock).
      destruct Htypes as [(HKS & _) | [(HPDT & _) | Hnone]].
      - unfold isKS in HKS. destruct (lookup nullAddr (memory s0) beqAddr); congruence.
      - unfold isPDT in HPDT. destruct (lookup nullAddr (memory s0) beqAddr); congruence.
      - specialize(Hnone nullAddr HstartInRange). rewrite Hnone in Hnull. congruence.
    }
    rewrite <-beqAddrFalse in HbeqNewPDNull. rewrite HlookupEqs2s0; assumption.
    (* END nullAddrExists *)
  }
  assert(wellFormedFstShadowIfBlockEntry s).
  { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
    assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block HblockIsBE.
    assert(HblockIsBEs0: isBE block s0).
    {
      unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs3 in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
      rewrite HbeqBlockCurr in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      assert(HbeqNewPDBlockBis: newPDBlockStartAddr <> block).
      {
        intro Hcontra. subst block. rewrite HlookupNewPDs2 in *. congruence.
      }
      rewrite <-HlookupEqs2s0; assumption.
    }
    specialize(Hcons0 block HblockIsBEs0). unfold isSHE in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite <-HbeqCurrBlockSh1 in *.
      unfold isPDT in HcurrIsPDTs0. destruct (lookup currentPart (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock (CPaddr (block + sh1offset))) eqn:HbeqBlockBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
      rewrite HlookupBlocks0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    assert(HbeqNewPDBlockSh1: newPDBlockStartAddr <> (CPaddr (block + sh1offset))).
    {
      intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
    }
    rewrite HlookupEqs2s0; assumption.
    (* END wellFormedFstShadowIfBlockEntry *)
  }
  assert(PDTIfPDFlag s).
  { (* BEGIN PDTIfPDFlag s *)
    assert(Hcons0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros idPDchild sh1entryaddr HcheckChild. destruct HcheckChild as (HcheckChild & Hsh1Bis).
    assert(HcheckChilds0: true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. destruct (beqAddr idBlock idPDchild) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst idPDchild. rewrite HlookupBlocks0.
        rewrite HlookupBlocks in *. split; try(assumption). rewrite Hs in HcheckChild. rewrite Hs3 in HcheckChild.
        simpl in *. destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
        rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        assert(HbeqNewPDSh1: newPDBlockStartAddr <> sh1entryaddr).
        {
          intro Hcontra. rewrite <-Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite <-HlookupEqs2s0; assumption.
      - rewrite Hs in HcheckChild. rewrite Hs in Hsh1Bis. rewrite Hs3 in HcheckChild. rewrite Hs3 in Hsh1Bis.
        simpl in *. destruct (beqAddr currentPart idPDchild) eqn:HbeqCurrPDChild; try(exfalso; congruence).
        rewrite HbeqBlockCurr in *. simpl in *. rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
        assert(HbeqStartPDChild: newPDBlockStartAddr <> idPDchild).
        {
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite <-HlookupEqs2s0; try(assumption). split; try(assumption).
        destruct (lookup idPDchild (memory s2) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
        destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *.
        rewrite HlookupNewPDs2 in *. congruence.
    }
    specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds0). unfold bentryAFlag in *. unfold bentryPFlag in *.
    destruct Hcons0 as (HAFlag & HPFlag & [startaddr (Hstart & HstartIsPDT)]). unfold bentryStartAddr in *.
    unfold entryPDT in *. destruct (beqAddr idBlock idPDchild) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst idPDchild. rewrite HlookupBlocks0 in *.
      rewrite HlookupBlocks. rewrite <-HstartBlock in Hstart. subst startaddr. exfalso.
      rewrite <-HstartBlock in *. rewrite HremovedAddr in *. congruence.
    - unfold sh1entryAddr in Hsh1Bis. rewrite Hs. rewrite Hs3. rewrite Hs in Hsh1Bis. rewrite Hs3 in Hsh1Bis.
      simpl. simpl in Hsh1Bis.
      destruct (beqAddr currentPart idPDchild) eqn:HbeqCurrPDChild; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
      assert(HbeqStartPDChild: newPDBlockStartAddr <> idPDchild).
      {
        intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
      }
      rewrite HlookupEqs2s0; try(assumption). split. assumption. split. assumption. exists startaddr. split.
      assumption. destruct (lookup idPDchild (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr currentPart (startAddr (blockrange b))) eqn:HbeqCurrStartBis.
      + rewrite <-DTL.beqAddrTrue in HbeqCurrStartBis. rewrite <-HbeqCurrStartBis in *. assumption.
      + destruct (beqAddr idBlock (startAddr (blockrange b))) eqn:HbeqBlockStart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite <-HbeqBlockStart in *. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END PDTIfPDFlag *)
  }
  assert(AccessibleNoPDFlag s).
  { (* BEGIN AccessibleNoPDFlag s *)
    assert(Hcons0: AccessibleNoPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block sh1entryaddr HblockIsBE Hsh1Bis HAFlag. unfold isBE in *. unfold sh1entryAddr in *.
    unfold bentryAFlag in *. rewrite Hs in HblockIsBE. rewrite Hs3 in HblockIsBE. rewrite Hs in Hsh1Bis.
    rewrite Hs3 in Hsh1Bis. rewrite Hs in HAFlag. rewrite Hs3 in HAFlag. simpl in *.
    destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
    rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
    {
      rewrite HnewBEntry in HAFlag. simpl in HAFlag. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HAFlag; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HAFlag; try(apply not_eq_sym; assumption).
    assert(HbeqStartBlock: newPDBlockStartAddr <> block).
    {
      intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
    }
    rewrite HlookupEqs2s0 in HblockIsBE; try(assumption). rewrite HlookupEqs2s0 in Hsh1Bis; try(assumption).
    rewrite HlookupEqs2s0 in HAFlag; try(assumption).
    specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1Bis HAFlag). unfold sh1entryPDflag in *. rewrite Hs.
    rewrite Hs3. simpl. destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. unfold isPDT in HcurrIsPDTs0.
      destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr. simpl.
    destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
    intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END AccessibleNoPDFlag *)
  }
  assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
  { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
    assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart HbeqFirstFreeNull.
    assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
                                                /\ firstfreeslot pdentryParts0 = firstfreeslot pdentryPart).
    {
      rewrite Hs in HlookupPart. rewrite Hs3 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. injection HlookupPart as HpdentriesEq.
        subst pdentryPart. simpl in *. exists pdentry. split. assumption. reflexivity.
      - rewrite HbeqBlockCurr in HlookupPart. simpl in HlookupPart.
        destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        assert(HbeqStartPart: newPDBlockStartAddr <> partition).
        {
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in HlookupPart.
          injection HlookupPart as HpdentriesEq. subst pdentryPart. rewrite HnewPD in HbeqFirstFreeNull.
          simpl in HbeqFirstFreeNull. congruence.
        }
        rewrite HlookupEqs2s0 in HlookupPart; try(assumption). exists pdentryPart. split. assumption.
        reflexivity.
    }
    destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HfirstFreeEq)]. rewrite <-HfirstFreeEq in *.
    specialize(Hcons0 partition pdentryParts0 HlookupParts0 HbeqFirstFreeNull).
    destruct Hcons0 as (_ & HfirstFree). unfold isBE. unfold isFreeSlot in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart (firstfreeslot pdentryParts0)) eqn:HbeqCurrFirstFree.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqCurrFirstFree. rewrite <-HbeqCurrFirstFree in *.
      rewrite HlookupCurrs0 in *. congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock (firstfreeslot pdentryParts0)) eqn:HbeqBlockFirstFree.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockFirstFree. rewrite <-HbeqBlockFirstFree in *. exfalso.
      unfold bentryPFlag in HPFlagBlock. rewrite HlookupBlocks0 in *.
      destruct (lookup (CPaddr (idBlock + sh1offset)) (memory s0) beqAddr); try(congruence).
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    assert(HbeqStartFirstFree: newPDBlockStartAddr <> firstfreeslot pdentryParts0).
    {
      intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
    }
    rewrite HlookupEqs2s0; try(assumption).
    destruct (lookup (firstfreeslot pdentryParts0) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). split; trivial.
    destruct (beqAddr currentPart (CPaddr (firstfreeslot pdentryParts0 + sh1offset))) eqn:HbeqCurrFirstSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrFirstSh1. rewrite <-HbeqCurrFirstSh1 in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    destruct (beqAddr idBlock (CPaddr (firstfreeslot pdentryParts0 + sh1offset))) eqn:HbeqBlockFirstSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockFirstSh1. rewrite <-HbeqBlockFirstSh1 in *.
      rewrite HlookupBlocks0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    assert(HbeqStartFirstSh1: newPDBlockStartAddr <> CPaddr (firstfreeslot pdentryParts0 + sh1offset)).
    {
      intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
    }
    rewrite HlookupEqs2s0; try(assumption).
    destruct (lookup (CPaddr (firstfreeslot pdentryParts0 + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (beqAddr currentPart (CPaddr (firstfreeslot pdentryParts0 + scoffset))) eqn:HbeqCurrFirstSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrFirstSce. rewrite <-HbeqCurrFirstSce in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    destruct (beqAddr idBlock (CPaddr (firstfreeslot pdentryParts0 + scoffset))) eqn:HbeqBlockFirstSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockFirstSce. rewrite <-HbeqBlockFirstSce in *.
      rewrite HlookupBlocks0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
    intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
  }
  assert(multiplexerIsPDT s).
  { (* BEGIN multiplexerIsPDT s *)
    assert(Hcons0: multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart multiplexer) eqn:HbeqCurrMult; trivial. rewrite HbeqBlockCurr. simpl.
    destruct (beqAddr idBlock multiplexer) eqn:HbeqBlockMult.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockMult. rewrite HbeqBlockMult in *. rewrite HlookupBlocks0 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
    intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END multiplexerIsPDT *)
  }
  (*assert(currentPartitionInPartitionsList s).
  { (* BEGIN currentPartitionInPartitionsList s *)
    assert(Hcons0: currentPartitionInPartitionsList s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold currentPartitionInPartitionsList in *.
    assert(HcurrEq: currentPartition s = currentPartition s0).
    {
      rewrite Hs. rewrite Hs3. simpl. rewrite Hs2. rewrite Hs1. simpl. reflexivity.
    }
    assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
    {
      assert(HgetPartsEqss3: getPartitions multiplexer s = getPartitions multiplexer s3).
      {
        rewrite Hs. apply getPartitionsEqPDT with pdentry; try(assumption). simpl. reflexivity. 1,2: admit.
        (*StructurePointerIsKS s3, PDTIfPDFlag s3*)
      }
      assert(HgetPartsEqs3s2: getPartitions multiplexer s3 = getPartitions multiplexer s2).
      {
        rewrite Hs3. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry
          (CPaddr (idBlock + sh1offset)); try(assumption); try(rewrite HnewBEntry; simpl; reflexivity).
        - admit. (*isPDT multiplexer s2*)
        - admit. (*PDTIfPDFlag s2*)
        - apply lookupSh1EntryAddr with bentry. assumption.
        - simpl. admit. (*wellFormedFstShadowIfBlockEntry s2*)
        - admit. (*wellFormedFstShadowIfBlockEntry s2*)
      }
      assert(HgetPartsEqs2s1: getPartitions multiplexer s2 = getPartitions multiplexer s1).
      {
        rewrite Hs2. apply getPartitionsEqPDT.
        - 
        - 
        - admit. (*StructurePointerIsKS s1*)
        - admit. (*PDTIfPDFlag s1*)
      }
      
    }
    (* END currentPartitionInPartitionsList *)
  }*)
  assert(wellFormedShadowCutIfBlockEntry s).
  { (* BEGIN wellFormedShadowCutIfBlockEntry s*)
    assert(Hcons0: wellFormedShadowCutIfBlockEntry s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition). intros block HblockIsBE.
    unfold isBE in *. rewrite Hs in HblockIsBE. rewrite Hs3 in HblockIsBE. simpl in *.
    destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
    rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block.
      assert(HblockIsBEs0: isBE idBlock s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
      specialize(Hcons0 idBlock HblockIsBEs0). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)].
      exists scentryaddr. split; try(assumption). unfold isSCE in *. rewrite Hs. rewrite Hs3. simpl.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs0 in *.
        congruence.
      }
      rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock scentryaddr) eqn:HbeqBlockSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *. rewrite HlookupBlocks0 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
      intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      assert(HbeqStartBlock: newPDBlockStartAddr <> block).
      {
        intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
      }
      rewrite HlookupEqs2s0 in HblockIsBE; try(assumption). specialize(Hcons0 block HblockIsBE).
      destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)].
      exists scentryaddr. split; try(assumption). unfold isSCE in *. rewrite Hs. rewrite Hs3. simpl.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrSce. rewrite HbeqCurrSce in *. rewrite HlookupCurrs0 in *.
        congruence.
      }
      rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr. simpl.
      destruct (beqAddr idBlock scentryaddr) eqn:HbeqBlockSce.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *. rewrite HlookupBlocks0 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
      intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END wellFormedShadowCutIfBlockEntry *)
  }
  assert(BlocksRangeFromKernelStartIsBE s).
  { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
    assert(Hcons0: BlocksRangeFromKernelStartIsBE s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros kernel blockidx HkernIsKS Hblockidx.
    assert(HkernIsKSs0: isKS kernel s0).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs3 in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in HkernIsKS. destruct (beqAddr idBlock kernel) eqn:HbeqBlockKern.
      - rewrite HnewBEntry in HkernIsKS. simpl in *. rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel.
        rewrite HlookupBlocks0. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *.
        rewrite HlookupNewPDs2 in *. congruence.
    }
    specialize(Hcons0 kernel blockidx HkernIsKSs0 Hblockidx). unfold isBE in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart (CPaddr (kernel + blockidx))) eqn:HbeqCurrKernIdx.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrKernIdx. rewrite <-HbeqCurrKernIdx in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock (CPaddr (kernel + blockidx))) eqn:HbeqBlockKernIdx;
      trivial. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
    intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END BlocksRangeFromKernelStartIsBE *)
  }
  assert(KernelStructureStartFromBlockEntryAddrIsKS s).
  { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
    assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block blockidx HblockIsBE HblockIdx.
    assert(Hblock: isBE block s0 /\ bentryBlockIndex block blockidx s0).
    {
      unfold isBE. unfold bentryBlockIndex in *. rewrite Hs in HblockIdx. rewrite Hs3 in HblockIdx. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in HblockIdx. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite HnewBEntry in HblockIdx. simpl in *. rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block.
        rewrite HlookupBlocks0. split; trivial; assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIdx; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HblockIdx; try(apply not_eq_sym; assumption).
        assert(HbeqStartBlock: newPDBlockStartAddr <> block).
        {
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite HlookupEqs2s0 in HblockIdx; try(assumption). split; try(assumption).
        destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    destruct Hblock as (HblockIsBEs0 & HblockIdxs0). specialize(Hcons0 block blockidx HblockIsBEs0 HblockIdxs0).
    unfold isKS in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart (CPaddr (block - blockidx))) eqn:HbeqCurrKern.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrKern. rewrite <-HbeqCurrKern in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock (CPaddr (block - blockidx))) eqn:HbeqBlockKern.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. rewrite <-HbeqBlockKern in *. rewrite HlookupBlocks0 in *.
      rewrite HnewBEntry. simpl. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
      intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (*END KernelStructureStartFromBlockEntryAddrIsKS *)
  }
  assert(sh1InChildLocationIsBE s).
  { (* BEGIN sh1InChildLocationIsBE s *)
    assert(Hcons0: sh1InChildLocationIsBE s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros sh1entryaddr sh1entry HlookupSh1 HbeqChildLocNull. rewrite Hs in HlookupSh1. rewrite Hs3 in HlookupSh1.
    simpl in *. destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
    rewrite HbeqBlockCurr in HlookupSh1. simpl in HlookupSh1.
    destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
    assert(HbeqStartSh1: newPDBlockStartAddr <> sh1entryaddr).
    {
      intro Hcontra. rewrite Hcontra in *. congruence.
    }
    rewrite HlookupEqs2s0 in HlookupSh1; try(assumption).
    specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1 HbeqChildLocNull). unfold isBE in *. rewrite Hs.
    rewrite Hs3. simpl. destruct (beqAddr currentPart (inChildLocation sh1entry)) eqn:HbeqCurrChildLoc.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrChildLoc. rewrite <-HbeqCurrChildLoc in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr. simpl.
    destruct (beqAddr idBlock (inChildLocation sh1entry)) eqn:HbeqBlockChildLoc; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
    intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END sh1InChildLocationIsBE *)
  }
  assert(StructurePointerIsKS s).
  { (* BEGIN StructurePointerIsKS s *)
    assert(Hcons0: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
                                                /\ structure pdentryParts0 = structure pdentryPart).
    {
      rewrite Hs in HlookupPart. rewrite Hs3 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - exists pdentry. injection HlookupPart as HpdentriesEq. rewrite <-HpdentriesEq. simpl.
        rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. split. assumption. reflexivity.
      - rewrite HbeqBlockCurr in HlookupPart. simpl in HlookupPart.
        destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        assert(HbeqStartPart: newPDBlockStartAddr <> partition).
        {
          intro Hcontra. subst partition. rewrite HlookupNewPDs2 in *. injection HlookupPart as HpdentriesEq.
          subst pdentryPart. rewrite HnewPD in HbeqStructNull. simpl in HbeqStructNull. congruence.
        }
        rewrite HlookupEqs2s0 in HlookupPart; try(assumption). exists pdentryPart. split. assumption.
        reflexivity.
    }
    destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HstructEq)]. rewrite <-HstructEq in *.
    specialize(Hcons0 partition pdentryParts0 HlookupParts0 HbeqStructNull). unfold isKS in *. rewrite Hs.
    rewrite Hs3. simpl. destruct (beqAddr currentPart (structure pdentryParts0)) eqn:HbeqCurrStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrStruct. rewrite <-HbeqCurrStruct in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock (structure pdentryParts0)) eqn:HbeqBlockStruct.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockStruct. rewrite <-HbeqBlockStruct in *. rewrite HlookupBlocks0 in *.
      rewrite HnewBEntry. simpl. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
      intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END StructurePointerIsKS *)
  }
  assert(NextKSIsKS s).
  { (* BEGIN NextKSIsKS s *)
    assert(Hcons0: NextKSIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKS HbeqNextNull.
    assert(Hkernel: isKS kernel s0 /\ nextKSAddr kernel nextKSaddr s0).
    {
      unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr.
      rewrite Hs3 in HkernIsKS. rewrite Hs3 in HnextAddr. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock kernel) eqn:HbeqBlockKern.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. split; assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HnextAddr; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HnextAddr; try(apply not_eq_sym; assumption).
        assert(HbeqStartKern: newPDBlockStartAddr <> kernel).
        {
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite HlookupEqs2s0 in HkernIsKS; try(assumption). rewrite HlookupEqs2s0 in HnextAddr; try(assumption).
        split; assumption.
    }
    destruct Hkernel as (HkernIsKSs0 & HnextAddrs0).
    assert(HnextKSs0: nextKSentry nextKSaddr nextKS s0).
    {
      unfold nextKSentry in *. rewrite Hs in HnextKS. rewrite Hs3 in HnextKS. simpl in HnextKS.
      destruct (beqAddr currentPart nextKSaddr) eqn:HbeqCurrNext; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *.
      destruct (beqAddr idBlock nextKSaddr) eqn:HbeqBlockNext; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HnextKS; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HnextKS; try(apply not_eq_sym; assumption).
      rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *.
      congruence.
    }
    specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKSs0 HnextAddrs0 HnextKSs0 HbeqNextNull).
    unfold isKS in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart nextKS) eqn:HbeqCurrNext.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrNext. subst nextKS. rewrite HlookupCurrs0 in *. congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock nextKS) eqn:HbeqBlockNext.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockNext. subst nextKS. rewrite HlookupBlocks0 in *. rewrite HnewBEntry.
      simpl. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
      intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END NextKSIsKS *)
  }
  assert(NextKSOffsetIsPADDR s).
  { (* BEGIN NextKSOffsetIsPADDR s *)
    assert(Hcons0: NextKSOffsetIsPADDR s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros kernel nextKSaddr HkernIsKS HnextAddr.
    assert(Hkernel: isKS kernel s0 /\ nextKSAddr kernel nextKSaddr s0).
    {
      unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr.
      rewrite Hs3 in HkernIsKS. rewrite Hs3 in HnextAddr. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock kernel) eqn:HbeqBlockKern.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. split; assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HnextAddr; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HnextAddr; try(apply not_eq_sym; assumption).
        assert(HbeqStartKern: newPDBlockStartAddr <> kernel).
        {
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite HlookupEqs2s0 in HkernIsKS; try(assumption). rewrite HlookupEqs2s0 in HnextAddr; try(assumption).
        split; assumption.
    }
    destruct Hkernel as (HkernIsKSs0 & HnextAddrs0). specialize(Hcons0 kernel nextKSaddr HkernIsKSs0 HnextAddrs0).
    destruct Hcons0 as (HnextIsPADDR & HbeqNextNull). split; try(assumption). unfold isPADDR in *.
    rewrite Hs. rewrite Hs3. simpl. destruct (beqAddr currentPart nextKSaddr) eqn:HbeqCurrNext.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrNext. subst nextKSaddr. rewrite HlookupCurrs0 in *. congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock nextKSaddr) eqn:HbeqBlockNext.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockNext. subst nextKSaddr. rewrite HlookupBlocks0 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
    intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END NextKSOffsetIsPADDR *)
  }
  assert(NoDupInFreeSlotsList s).
  { (* BEGIN NoDupInFreeSlotsList s *)
    assert(Hcons0: NoDupInFreeSlotsList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart.
    assert(HlookupPartCopy: lookup partition (memory s) beqAddr = Some (PDT pdentryPart)) by assumption.
    rewrite Hs in HlookupPart. rewrite Hs3 in HlookupPart. simpl in *.
    destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
    - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition.
      specialize(Hcons0 currentPart pdentry HlookupCurrs0).
      destruct Hcons0 as [optionfreeslotslist (Hlist & Hwell & HnoDup)]. exists optionfreeslotslist.
      split; try(split; assumption). rewrite Hlist. apply eq_sym. unfold getFreeSlotsList in *.
      rewrite HlookupCurrs0 in *. rewrite HlookupCurrs. unfold newPDCurr. simpl.
      destruct (beqAddr (firstfreeslot pdentry) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
      assert(firstfreeslot pdentry <> newPDBlockStartAddr).
      {
        assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in HbeqFirstNull.
        specialize(HfirstIsBE currentPart pdentry HlookupCurrs0 HbeqFirstNull).
        destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. intro Hcontra. rewrite <-Hcontra in *.
        rewrite HremovedAddr in *. congruence.
      }
      assert(~ isBE newPDBlockStartAddr s0).
      {
        unfold isBE. rewrite HremovedAddr. congruence.
      }
      assert(~ isPADDR newPDBlockStartAddr s0).
      {
        unfold isPADDR. rewrite HremovedAddr. congruence.
      }
      assert(HgetFreeEqs1s0: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s1 (nbfreeslots pdentry)
                            = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
      {
        rewrite Hs1. apply getFreeSlotsListRecEqPDT; assumption.
      }
      rewrite <-HgetFreeEqs1s0 in *.
      assert(HgetFreeEqs2s1: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s2 (nbfreeslots pdentry)
                            = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s1 (nbfreeslots pdentry)).
      {
        rewrite Hs2. apply getFreeSlotsListRecEqPDT; try(assumption).
        - unfold isBE. rewrite Hs1. simpl. rewrite beqAddrTrue. congruence.
        - unfold isPADDR. rewrite Hs1. simpl. rewrite beqAddrTrue. congruence.
      }
      rewrite <-HgetFreeEqs2s1 in *.
      assert(HgetFreeEqs3s2: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s3 (nbfreeslots pdentry)
                            = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s2 (nbfreeslots pdentry)).
      {
        rewrite Hs3. apply getFreeSlotsListRecEqBE; try(reflexivity); try(rewrite <-Hlist; assumption).
        assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in HbeqFirstNull.
        specialize(HfirstIsBE currentPart pdentry HlookupCurrs0 HbeqFirstNull).
        destruct HfirstIsBE as (_ & HfirstIsFree).
        - intro Hcontra. rewrite Hcontra in *. congruence.
        - unfold isBE. rewrite HlookupBlocks2. trivial.
        - rewrite HgetFreeEqs1s0. assert(HfreeSlots: freeSlotsListIsFreeSlot s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HwellFormed: optionfreeslotslist = getFreeSlotsList currentPart s0
                              /\ wellFormedFreeSlotsList optionfreeslotslist <> False).
          {
            split; try(assumption). unfold getFreeSlotsList. rewrite HlookupCurrs0. rewrite HbeqFirstNull.
            rewrite <-HgetFreeEqs1s0. assumption.
          }
          intro Hcontra.
          assert(HblockIn: filterOptionPaddr optionfreeslotslist = filterOptionPaddr optionfreeslotslist
                            /\ In idBlock (filterOptionPaddr optionfreeslotslist)).
          {
            split; try(reflexivity). rewrite Hlist. rewrite HgetFreeEqs1s0. assumption.
          }
          rewrite beqAddrSym in HbeqNullBlock. rewrite <-beqAddrFalse in HbeqNullBlock.
          specialize(HfreeSlots currentPart idBlock optionfreeslotslist (filterOptionPaddr optionfreeslotslist)
            HcurrIsPDTs0 HwellFormed HblockIn HbeqNullBlock). congruence.
      }
      rewrite <-HgetFreeEqs3s2 in *.
      assert(HgetFreeEqss3: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s (nbfreeslots pdentry)
                            = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s3 (nbfreeslots pdentry)).
      {
        rewrite Hs. apply getFreeSlotsListRecEqPDT.
        - assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in HbeqFirstNull.
          specialize(HfirstIsBE currentPart pdentry HlookupCurrs0 HbeqFirstNull).
          destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. intro Hcontra.
          rewrite <-Hcontra in *. rewrite HlookupCurrs0 in *. congruence.
        - unfold isBE. rewrite HlookupCurrs3. congruence.
        - unfold isPADDR. rewrite HlookupCurrs3. congruence.
      }
      assumption.
    - rewrite HbeqBlockCurr in HlookupPart. simpl in *.
      destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
      destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
      + rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getFreeSlotsList. exists [].
        rewrite Hs. rewrite Hs3. simpl. rewrite beqAddrFalse in HbeqCurrPart. rewrite HbeqCurrPart.
        rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr. simpl.
        rewrite beqAddrFalse in HbeqBlockPart. rewrite HbeqBlockPart. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupNewPDs2. rewrite HnewPD.
        simpl. split. reflexivity. split. intro Hcontra. rewrite <-Hcontra. trivial. apply NoDup_nil.
      + rewrite <-beqAddrFalse in HbeqStartPart. rewrite HlookupEqs2s0 in HlookupPart; try(assumption).
        specialize(Hcons0 partition pdentryPart HlookupPart).
        destruct Hcons0 as [optionfreeslotslist (Hlist & Hwell & HnoDup)]. exists optionfreeslotslist.
        split; try(split; assumption). rewrite Hlist. apply eq_sym. unfold getFreeSlotsList in *.
        rewrite HlookupPart in *. rewrite HlookupPartCopy.
        destruct (beqAddr (firstfreeslot pdentryPart) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
        assert(firstfreeslot pdentryPart <> newPDBlockStartAddr).
        {
          assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in HbeqFirstNull.
          specialize(HfirstIsBE partition pdentryPart HlookupPart HbeqFirstNull).
          destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. intro Hcontra.
          rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
        }
        assert(~ isBE newPDBlockStartAddr s0).
        {
          unfold isBE. rewrite HremovedAddr. congruence.
        }
        assert(~ isPADDR newPDBlockStartAddr s0).
        {
          unfold isPADDR. rewrite HremovedAddr. congruence.
        }
        assert(HgetFreeEqs1s0:
                getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s1 (nbfreeslots pdentryPart)
                  = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s0 (nbfreeslots pdentryPart)).
        {
          rewrite Hs1. apply getFreeSlotsListRecEqPDT; assumption.
        }
        rewrite <-HgetFreeEqs1s0 in *.
        assert(HgetFreeEqs2s1:
                getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s2 (nbfreeslots pdentryPart)
                  = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s1 (nbfreeslots pdentryPart)).
        {
          rewrite Hs2. apply getFreeSlotsListRecEqPDT; try(assumption).
          - unfold isBE. rewrite Hs1. simpl. rewrite beqAddrTrue. congruence.
          - unfold isPADDR. rewrite Hs1. simpl. rewrite beqAddrTrue. congruence.
        }
        rewrite <-HgetFreeEqs2s1 in *.
        assert(HgetFreeEqs3s2:
                getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s3 (nbfreeslots pdentryPart)
                  = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s2 (nbfreeslots pdentryPart)).
        {
          rewrite Hs3. apply getFreeSlotsListRecEqBE; try(reflexivity); try(rewrite <-Hlist; assumption).
          assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in HbeqFirstNull.
          specialize(HfirstIsBE partition pdentryPart HlookupPart HbeqFirstNull).
          destruct HfirstIsBE as (_ & HfirstIsFree).
          - intro Hcontra. rewrite Hcontra in *. congruence.
          - unfold isBE. rewrite HlookupBlocks2. trivial.
          - rewrite HgetFreeEqs1s0. assert(HfreeSlots: freeSlotsListIsFreeSlot s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HwellFormed: optionfreeslotslist = getFreeSlotsList partition s0
                                /\ wellFormedFreeSlotsList optionfreeslotslist <> False).
            {
              split; try(assumption). unfold getFreeSlotsList. rewrite HlookupPart. rewrite HbeqFirstNull.
              rewrite <-HgetFreeEqs1s0. assumption.
            }
            intro Hcontra.
            assert(HblockIn: filterOptionPaddr optionfreeslotslist = filterOptionPaddr optionfreeslotslist
                              /\ In idBlock (filterOptionPaddr optionfreeslotslist)).
            {
              split; try(reflexivity). rewrite Hlist. rewrite HgetFreeEqs1s0. assumption.
            }
            assert(HpartIsPDTs0: isPDT partition s0) by (unfold isPDT; rewrite HlookupPart; trivial).
            apply not_eq_sym in HbeqNullBlock.
            specialize(HfreeSlots partition idBlock optionfreeslotslist (filterOptionPaddr optionfreeslotslist)
              HpartIsPDTs0 HwellFormed HblockIn HbeqNullBlock). congruence.
        }
        rewrite <-HgetFreeEqs3s2 in *.
        assert(HgetFreeEqss3:
                getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s (nbfreeslots pdentryPart)
                  = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s3 (nbfreeslots pdentryPart)).
        {
          rewrite Hs. apply getFreeSlotsListRecEqPDT.
          - assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
              by (unfold consistency in *; unfold consistency1 in *; intuition).
            rewrite <-beqAddrFalse in HbeqFirstNull.
            specialize(HfirstIsBE partition pdentryPart HlookupPart HbeqFirstNull).
            destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. intro Hcontra.
            rewrite <-Hcontra in *. rewrite HlookupCurrs0 in *. congruence.
          - unfold isBE. rewrite HlookupCurrs3. congruence.
          - unfold isPADDR. rewrite HlookupCurrs3. congruence.
        }
        assumption.
    (* END NoDupInFreeSlotsList *)
  }

  (*TODO HERE assert(HgetFreeSlotsListEq: forall part, beqAddr ? part = false
          -> getFreeSlotsList part s = getFreeSlotsList part s0).*)

  assert(freeSlotsListIsFreeSlot s).
  { (* BEGIN freeSlotsListIsFreeSlot s *)
    assert(Hcons0: freeSlotsListIsFreeSlot s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition freeslotaddr optionfreeslotslist freeslotslist HpartIsPDT (HoptList & Hwell)
      (Hlist & HaddrIn) HbeqAddrNull.
    destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getFreeSlotsList in HoptList.
      rewrite HlookupNewPDs in HoptList. rewrite HnewPD in HoptList. simpl in HoptList.
      rewrite HoptList in Hlist. simpl in Hlist. rewrite Hlist in HaddrIn. contradict HaddrIn.
    }
    assert(HlookupPartEq: exists pdentryPart pdentryParts0,
                            lookup partition (memory s) beqAddr = Some(PDT pdentryPart)
                            /\ lookup partition (memory s0) beqAddr = Some(PDT pdentryParts0)
                            /\ firstfreeslot pdentryParts0 = firstfreeslot pdentryPart
                            /\ nbfreeslots pdentryParts0 = nbfreeslots pdentryPart).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. rewrite Hs. rewrite Hs3. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. exists newPDCurr. exists pdentry. split.
        reflexivity. split. assumption. unfold newPDCurr. simpl. split; reflexivity.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        rewrite HlookupEqs2s0 in HpartIsPDT; try(assumption).
        destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists p. exists p. split. reflexivity. split. reflexivity.
        split; reflexivity.
    }
    destruct HlookupPartEq as [pdentryPart [pdentryParts0 (HlookupPart & HlookupParts0 & HfirstFreeEq &
      HnbFreeEq)]].
    assert(HpartIsPDTs0: isPDT partition s0).
    {
      unfold isPDT. rewrite HlookupParts0. trivial.
    }
    assert(HoptLists0: optionfreeslotslist = getFreeSlotsList partition s0).
    {
      rewrite HoptList. unfold getFreeSlotsList in *. rewrite HlookupPart in *. rewrite HlookupParts0.
      rewrite HfirstFreeEq. rewrite HnbFreeEq.
      destruct (beqAddr (firstfreeslot pdentryPart) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
      assert(firstfreeslot pdentryPart <> newPDBlockStartAddr).
      {
        assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in HbeqFirstNull. rewrite <-HfirstFreeEq in HbeqFirstNull.
        specialize(HfirstIsBE partition pdentryParts0 HlookupParts0 HbeqFirstNull).
        destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. rewrite HfirstFreeEq in *.
        intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
      }
      assert(~ isBE newPDBlockStartAddr s0).
      {
        unfold isBE. rewrite HremovedAddr. congruence.
      }
      assert(~ isPADDR newPDBlockStartAddr s0).
      {
        unfold isPADDR. rewrite HremovedAddr. congruence.
      }
      assert(HgetFreeEqs1s0:
              getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s1 (nbfreeslots pdentryPart)
                = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s0 (nbfreeslots pdentryPart)).
      {
        rewrite Hs1. apply getFreeSlotsListRecEqPDT; assumption.
      }
      rewrite <-HgetFreeEqs1s0 in *.
      assert(HgetFreeEqs2s1:
              getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s2 (nbfreeslots pdentryPart)
                = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s1 (nbfreeslots pdentryPart)).
      {
        rewrite Hs2. apply getFreeSlotsListRecEqPDT; try(assumption).
        - unfold isBE. rewrite Hs1. simpl. rewrite beqAddrTrue. congruence.
        - unfold isPADDR. rewrite Hs1. simpl. rewrite beqAddrTrue. congruence.
      }
      rewrite <-HgetFreeEqs2s1 in *.
      assert(HgetFreeEqss3:
              getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s (nbfreeslots pdentryPart)
                = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s3 (nbfreeslots pdentryPart)).
      {
        rewrite Hs. apply getFreeSlotsListRecEqPDT.
        - assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          rewrite <-beqAddrFalse in HbeqFirstNull. rewrite <-HfirstFreeEq in *.
          specialize(HfirstIsBE partition pdentryParts0 HlookupParts0 HbeqFirstNull).
          destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. intro Hcontra.
          rewrite <-Hcontra in *. rewrite HlookupCurrs0 in *. congruence.
        - unfold isBE. rewrite HlookupCurrs3. congruence.
        - unfold isPADDR. rewrite HlookupCurrs3. congruence.
      }
      rewrite HgetFreeEqss3 in *.
      assert(HgetFreeEqs3s2:
              getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s3 (nbfreeslots pdentryPart)
                = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryPart) s2 (nbfreeslots pdentryPart)).
      {
        rewrite Hs3. assert(HnoDupFree: NoDupInFreeSlotsList s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HnoDupFree partition pdentryParts0 HlookupParts0). rewrite <-HfirstFreeEq in *.
        destruct HnoDupFree as [optionfreeslotslists0 (Hlists0 & Hwells0 & HnoDups0)].
        unfold getFreeSlotsList in *. rewrite HlookupParts0 in *. rewrite HbeqFirstNull in *.
        subst optionfreeslotslists0. rewrite <-HnbFreeEq in *.
        assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in HbeqFirstNull.
        specialize(HfirstFree partition pdentryParts0 HlookupParts0 HbeqFirstNull).
        destruct HfirstFree as (_ & HfirstFree). unfold isFreeSlot in HfirstFree.
        apply getFreeSlotsListRecEqBE; try(reflexivity); try(rewrite HgetFreeEqs1s0); try(assumption).
        - intro Hcontra. rewrite Hcontra in *. unfold bentryPFlag in *. rewrite HlookupBlocks0 in *.
          destruct (lookup (CPaddr (idBlock + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          destruct (lookup (CPaddr (idBlock + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). destruct HfirstFree as (_ & _ & _ & _ & Hpresent & _).
          congruence.
        - unfold isBE. rewrite HlookupBlocks2. trivial.
        - assert(HwellFormed: getFreeSlotsList partition s0 = getFreeSlotsList partition s0
                              /\ wellFormedFreeSlotsList (getFreeSlotsList partition s0) <> False).
          {
            split. reflexivity. unfold getFreeSlotsList. rewrite HlookupParts0.
            rewrite beqAddrFalse in HbeqFirstNull. rewrite HbeqFirstNull. assumption.
          }
          intro Hcontra.
          assert(HblockIn: filterOptionPaddr (getFreeSlotsList partition s0)
                              = filterOptionPaddr (getFreeSlotsList partition s0)
                            /\ In idBlock (filterOptionPaddr (getFreeSlotsList partition s0))).
          {
            split; try(reflexivity). unfold getFreeSlotsList. rewrite HlookupParts0.
            rewrite beqAddrFalse in HbeqFirstNull. rewrite HbeqFirstNull. assumption.
          }
          rewrite beqAddrSym in HbeqNullBlock. rewrite <-beqAddrFalse in HbeqNullBlock.
          specialize(Hcons0 partition idBlock (getFreeSlotsList partition s0)
            (filterOptionPaddr (getFreeSlotsList partition s0)) HpartIsPDTs0 HwellFormed HblockIn HbeqNullBlock).
          congruence.
      }
      rewrite <-HgetFreeEqs3s2 in *. reflexivity.
    }
    assert(HoptListWells0: optionfreeslotslist = getFreeSlotsList partition s0 /\
       wellFormedFreeSlotsList optionfreeslotslist <> False) by (split; assumption).
    assert(HlistIn: freeslotslist = filterOptionPaddr optionfreeslotslist /\ In freeslotaddr freeslotslist).
    {split; assumption. }
    specialize(Hcons0 partition freeslotaddr optionfreeslotslist freeslotslist HpartIsPDTs0 HoptListWells0
      HlistIn HbeqAddrNull). unfold isFreeSlot in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart freeslotaddr) eqn:HbeqCurrSlot.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrSlot. rewrite HbeqCurrSlot in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock freeslotaddr) eqn:HbeqBlockFree.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockFree. rewrite HbeqBlockFree in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    assert(HbeqStartFree: newPDBlockStartAddr <> freeslotaddr).
    {
      intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    }
    rewrite HlookupEqs2s0; try(assumption).
    destruct (lookup freeslotaddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    destruct (beqAddr currentPart (CPaddr (freeslotaddr + sh1offset))) eqn:HbeqCurrFreeSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrFreeSh1. rewrite <-HbeqCurrFreeSh1 in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    destruct (beqAddr idBlock (CPaddr (freeslotaddr + sh1offset))) eqn:HbeqBlockFreeSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockFreeSh1. rewrite <-HbeqBlockFreeSh1 in *. rewrite HlookupBlocks0 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    assert(HbeqStartFreeSh1: newPDBlockStartAddr <> CPaddr (freeslotaddr + sh1offset)).
    {
      intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    }
    rewrite HlookupEqs2s0; try(assumption).
    destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (beqAddr currentPart (CPaddr (freeslotaddr + scoffset))) eqn:HbeqCurrFreeSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrFreeSce. rewrite <-HbeqCurrFreeSce in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    destruct (beqAddr idBlock (CPaddr (freeslotaddr + scoffset))) eqn:HbeqBlockFreeSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockFreeSce. rewrite <-HbeqBlockFreeSce in *. rewrite HlookupBlocks0 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    assert(HbeqStartFreeSce: newPDBlockStartAddr <> CPaddr (freeslotaddr + scoffset)).
    {
      intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    }
    rewrite HlookupEqs2s0; assumption.
    (* END freeSlotsListIsFreeSlot *)
  }
  assert(DisjointFreeSlotsLists s).
  { (* BEGIN DisjointFreeSlotsLists s *)
    assert(Hcons0: DisjointFreeSlotsLists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
    destruct (beqAddr newPDBlockStartAddr part1) eqn:HbeqStartPart1.
    - rewrite <-DTL.beqAddrTrue in HbeqStartPart1. subst part1.
      destruct (beqAddr newPDBlockStartAddr part2) eqn:HbeqStartPart2.
      { rewrite <-DTL.beqAddrTrue in HbeqStartPart2. subst part2. exfalso; congruence. }
      assert(wellFormedFreeSlotsList (getFreeSlotsList part2 s) <> False).
      {
        assert(Hpart2IsPDTs0: isPDT part2 s0).
        {
          unfold isPDT in *. rewrite Hs in Hpart2IsPDT. rewrite Hs3 in Hpart2IsPDT. simpl in *.
          destruct (beqAddr currentPart part2) eqn:HbeqCurrPart2.
          - rewrite <-DTL.beqAddrTrue in HbeqCurrPart2. subst part2. rewrite HlookupCurrs0. trivial.
          - rewrite HbeqBlockCurr in *. simpl in *.
            destruct (beqAddr idBlock part2) eqn:HbeqBlockPart2; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in Hpart2IsPDT; try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hpart2IsPDT; try(apply not_eq_sym; assumption).
            rewrite <-HlookupEqs2s0; assumption.
        }
        assert(HnbFree: NbFreeSlotsISNbFreeSlotsInList s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HlookupPart2: isPDT part2 s0) by assumption. apply isPDTLookupEq in HlookupPart2.
        destruct HlookupPart2 as [pdentryPart2 HlookupPart2].
        assert(HnbFreePart2: pdentryNbFreeSlots part2 (nbfreeslots pdentryPart2) s0).
        { unfold pdentryNbFreeSlots. rewrite HlookupPart2. reflexivity. }
        specialize(HnbFree part2 (nbfreeslots pdentryPart2) Hpart2IsPDTs0 HnbFreePart2).
        destruct HnbFree as [optionfreeslotslist (Hlist & Hres & _)]. (*TODO HERE*)
      }
      unfold getFreeSlotsList.
      rewrite HlookupNewPDs in HoptList. rewrite HnewPD in HoptList. simpl in HoptList.
      rewrite HoptList in Hlist. simpl in Hlist. rewrite Hlist in HaddrIn. contradict HaddrIn.
    - 
    assert(HlookupPartEq: exists pdentryPart pdentryParts0,
                            lookup partition (memory s) beqAddr = Some(PDT pdentryPart)
                            /\ lookup partition (memory s0) beqAddr = Some(PDT pdentryParts0)
                            /\ firstfreeslot pdentryParts0 = firstfreeslot pdentryPart
                            /\ nbfreeslots pdentryParts0 = nbfreeslots pdentryPart).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. rewrite Hs. rewrite Hs3. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. exists newPDCurr. exists pdentry. split.
        reflexivity. split. assumption. unfold newPDCurr. simpl. split; reflexivity.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        rewrite HlookupEqs2s0 in HpartIsPDT; try(assumption).
        destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists p. exists p. split. reflexivity. split. reflexivity.
        split; reflexivity.
    }
    destruct HlookupPartEq as [pdentryPart [pdentryParts0 (HlookupPart & HlookupParts0 & HfirstFreeEq &
      HnbFreeEq)]].
    destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getFreeSlotsList in HoptList.
      rewrite HlookupNewPDs in HoptList. rewrite HnewPD in HoptList. simpl in HoptList.
      rewrite HoptList in Hlist. simpl in Hlist. rewrite Hlist in HaddrIn. contradict HaddrIn.
    }
    assert(HlookupPartEq: exists pdentryPart pdentryParts0,
                            lookup partition (memory s) beqAddr = Some(PDT pdentryPart)
                            /\ lookup partition (memory s0) beqAddr = Some(PDT pdentryParts0)
                            /\ firstfreeslot pdentryParts0 = firstfreeslot pdentryPart
                            /\ nbfreeslots pdentryParts0 = nbfreeslots pdentryPart).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. rewrite Hs. rewrite Hs3. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. exists newPDCurr. exists pdentry. split.
        reflexivity. split. assumption. unfold newPDCurr. simpl. split; reflexivity.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        rewrite HlookupEqs2s0 in HpartIsPDT; try(assumption).
        destruct (lookup partition (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists p. exists p. split. reflexivity. split. reflexivity.
        split; reflexivity.
    }
    destruct HlookupPartEq as [pdentryPart [pdentryParts0 (HlookupPart & HlookupParts0 & HfirstFreeEq &
      HnbFreeEq)]].
    (* END DisjointFreeSlotsLists *)
  }
  assert(inclFreeSlotsBlockEntries s).
  { (*TODO lemmas getFreeSlotsList pd s and getKSEntries pd s unchanged if pd unchanged*)
    
  }
  assert(DisjointKSEntries s).
  { (*TODO lemma getKSEntries pd s unchanged if pd unchanged*)
    
  }
  assert(noDupPartitionTree s).
  { (*TODO lemma: no BE or PDT were changed -> getChildren/getPartitions stay the same*)
    
  }
  assert(isParent s).
  { (*OK*)
    
  }
  assert(isChild s).
  { (*TODO lemma: no BE or PDT were changed -> getChildren stays the same*)
    
  }
  assert(noDupKSEntriesList s).
  { (*TODO lemma getKSEntries pd s unchanged if pd unchanged*)
    
  }
  assert(noDupMappedBlocksList s).
  { (*TODO lemma getKSEntries pd s unchanged if pd unchanged -> getMappedBlocks unchanged*)
    
  }
  assert(wellFormedBlock s).
  { (*TODO startaddr not BE -> block still BE*)
    
  }
  assert(parentOfPartitionIsPartition s).
  { (*TODO no PDTs changed + lemma on getPartitions*)
    
  }
  assert(NbFreeSlotsISNbFreeSlotsInList s).
  { (*TODO lemma getFreeSlotsList pd s unchanged if pd unchanged*)
    
  }
  assert(maxNbPrepareIsMaxNbKernels s).
  { (*OK*)
    
  }
  assert(blockInChildHasAtLeastEquivalentBlockInParent s).
  { (*TODO lemmas on getPartitions/getChildren/getMappedBlocks + no BE changed*)
    
  }
  assert(partitionTreeIsTree s).
  { (*TODO*)
    
  }
  assert(kernelEntriesAreValid s).
  { (*TODO no BEs changed*)
    
  }
  assert(nextKernelIsValid s).
  {
    
  }
  assert(noDupListOfKerns s).
  {
    
  }
  assert(MPUsizeIsBelowMax s).
  {
    
  }
  assert(originIsParentBlocksStart s).
  {
    
  }
  assert(nextImpliesBlockWasCut s).
  {
    
  }*)
  assert(isBE blockInCurrentPartitionAddr s).
  {
    
  }
  instantiate(1 := fun _ s =>
    exists s3 s2 s1 s0 newBEntry bentry newPDEntry,
      s = {|
            currentPartition := currentPartition s3; memory := add idBlock (BE newBEntry) (memory s3) beqAddr
          |}
      /\ (exists l,
            newBEntry =
            {|
              read := read bentry;
              write := write bentry;
              exec := exec bentry;
              present := present bentry;
              accessible := false;
              blockindex := blockindex bentry;
              blockrange := blockrange bentry;
              Hidx := l
            |})
      /\ wellFormedFstShadowIfBlockEntry s
      /\ KernelStructureStartFromBlockEntryAddrIsKS s
      /\ BlocksRangeFromKernelStartIsBE s
      /\ nullAddrExists s
      /\ isBE blockInCurrentPartitionAddr s
      (* properties of s3 *)
      /\ lookup idBlock (memory s3) beqAddr = Some (BE bentry)
      /\ (forall addr, newPDBlockStartAddr <> addr
            -> lookup addr (memory s3) beqAddr = lookup addr (memory s1) beqAddr)
      /\ lookup newPDBlockStartAddr (memory s3) beqAddr = Some (PDT newPDEntry)
      /\ newPDEntry =
          {|
            structure := nullAddr;
            firstfreeslot := nullAddr;
            nbfreeslots := zero;
            nbprepare := zero;
            parent := currentPart;
            MPU := [];
            vidtAddr := nullAddr
          |}
      /\ s3 =
          {|
            currentPartition := currentPartition s2;
            memory := add newPDBlockStartAddr (PDT newPDEntry) (memory s2) beqAddr
          |}
      (* properties of s2 *)
      /\ s2 =
          {|
            currentPartition := currentPartition s1;
            memory :=
              add newPDBlockStartAddr
                (PDT
                   {|
                     structure := nullAddr;
                     firstfreeslot := nullAddr;
                     nbfreeslots := zero;
                     nbprepare := zero;
                     parent := nullAddr;
                     MPU := [];
                     vidtAddr := nullAddr
                   |}) (memory s1) beqAddr
          |}
      (* properties of s1 *)
      /\ (forall addr, In addr (getAllPaddrBlock newPDBlockStartAddr newPDBlockEndAddr)
          -> lookup addr (memory s1) beqAddr = None)
      /\ (forall addr, ~ In addr (getAllPaddrBlock newPDBlockStartAddr newPDBlockEndAddr)
          -> lookup addr (memory s1) beqAddr = lookup addr (memory s0) beqAddr)
      (* properties of s0 *)
      /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ consistency s0
      /\ isPDT currentPart s0
      /\ currentPart = currentPartition s0
      /\ bentryStartAddr idBlock newPDBlockStartAddr s0
      /\ bentryEndAddr idBlock newPDBlockEndAddr s0 /\ isBlockInRAM idBlock isInRAM s0
      /\ bentryAFlag idBlock true s0 /\ bentryPFlag idBlock true s0
      /\ In idBlock (getMappedBlocks currentPart s0)
      /\ lookup idBlock (memory s0) beqAddr = Some (BE bentry)
      /\ (exists sh1entry sh1entryaddr, lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
            /\ sh1entryPDchild sh1entryaddr PDChildAddr s0 /\ sh1entryAddr idBlock sh1entryaddr s0)).
}
intro. eapply bindRev.
{ (* MAL.readSCOriginFromBlockEntryAddr *)
  (*eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.*) admit.
}


(*TODO use writeAccessibleRecAuxFalse*)
Qed.

