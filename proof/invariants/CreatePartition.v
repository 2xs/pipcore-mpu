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
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas Proof.InternalLemmas2.
Require Import Invariants (*getGlobalIdPDCurrentOrChild*) findBlockInKSWithAddr sizeOfBlock eraseBlock
writeAccessibleToAncestorsIfNotCutRec lookupInvariant.
Require Import Compare_dec Bool List Lia Coq.Logic.ProofIrrelevance.
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
                         sh1entryPDchild sh1entryaddr nullAddr s /\
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
  apply negb_false_iff in HnegChildNull. subst PDChildAddrIsNull. rewrite <-DTL.beqAddrTrue in HbeqNullChild.
  subst PDChildAddr.
  assert(HlookupsEq: forall addr, lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intro. set(P := In addr (getAllPaddrBlock newPDBlockStartAddr newPDBlockEndAddr)).
    assert(HpropsOr: P \/ ~P) by (apply Classical_Prop.classic). subst P.
    destruct HpropsOr as [HaddrInBlock | HaddrNotInBlock]; try(apply HkeptAddr; assumption).
    rewrite HremovedAddr; try(assumption). apply eq_sym.
    assert(Htypes: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(Hsh1IsSh1: sh1entryaddr = CPaddr (blockInCurrentPartitionAddr + sh1offset)).
    {
      unfold sh1entryAddr in *. rewrite HlookupBlocks0 in *. assumption.
    }
    rewrite Hsh1IsSh1 in HPDChildBlocks0. specialize(Htypes blockInCurrentPartitionAddr newPDBlockStartAddr
        newPDBlockEndAddr HstartBlock HendBlock HPDChildBlocks0).
    assert(HnotPDT: notPDTIfNotPDflag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HPDFlagBlocks0: sh1entryPDflag sh1entryaddr false s0).
    {
      assert(HnoPDFlag: AccessibleNoPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(HblockIsBE: isBE blockInCurrentPartitionAddr s0) by (unfold isBE; rewrite HlookupBlocks0; trivial).
      specialize(HnoPDFlag blockInCurrentPartitionAddr sh1entryaddr HblockIsBE Hsh1s0 HAFlagBlock).
      assumption.
    }
    rewrite <-Hsh1IsSh1 in *. specialize(HnotPDT blockInCurrentPartitionAddr newPDBlockStartAddr sh1entryaddr
      HstartBlock Hsh1s0 HPDFlagBlocks0 HPDChildBlocks0).
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
      assert(Hcons0: blocksAddressesTypes s0) by intuition. intros block startaddr endaddr Hstart Hend HPDchild.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold isKS in *. unfold isPDT in *.
      unfold sh1entryPDchild in *. rewrite HlookupsEq in *.
      specialize(Hcons0 block startaddr endaddr Hstart Hend HPDchild). destruct Hcons0 as [HKS | [HPDT | Hnone]].
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
      intros block startaddr sh1entryaddrBis Hstart Hsh1 HPDFlag HPDchild. unfold bentryStartAddr in *.
      unfold sh1entryAddr in *. unfold sh1entryPDflag in *. unfold sh1entryPDchild in *. unfold isPDT.
      rewrite HlookupsEq in *. specialize(Hcons0 block startaddr sh1entryaddrBis Hstart Hsh1 HPDFlag HPDchild).
      assumption.
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
    assert(blockBelongsToAPart s).
    { (* BEGIN blockBelongsToAPart s *)
      assert(Hcons0: blockBelongsToAPart s0) by intuition. intros block HblockIsBE. unfold isBE in HblockIsBE.
      rewrite HlookupsEq in *. specialize(Hcons0 block HblockIsBE). destruct Hcons0 as [part Hcons0]. exists part.
      rewrite getPartitionsEqLookup with multiplexer s s0; try(assumption).
      rewrite getMappedBlocksEqLookup with part s s0; assumption.
      (* END blockBelongsToAPart *)
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
    destruct HPDChild as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchild & Hsh1)]]. unfold sh1entryAddr in *.
    rewrite HlookupBlock in *. subst sh1entryaddr.
    specialize(Htypes idBlock idBlock newPDBlockEndAddr HstartBlock HendBlock HPDchild). exfalso.
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
            /\ sh1entryPDchild sh1entryaddr nullAddr s0 /\ sh1entryAddr idBlock sh1entryaddr s0)
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
  assert(HbeqStartCurr: newPDBlockStartAddr <> currentPart).
  {
    intro Hcontra. rewrite Hcontra in *. congruence.
  }
  assert(HlookupCurrs2: lookup currentPart (memory s2) beqAddr = Some (PDT pdentry)).
  {
    rewrite HlookupEqs2s0; assumption.
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
  assert(HlookupBlocks3: lookup idBlock (memory s3) beqAddr = Some (BE newBentry)).
  {
    rewrite Hs3. simpl. rewrite beqAddrTrue. reflexivity.
  }
  assert(StructurePointerIsKS s1).
  { (* BEGIN StructurePointerIsKS s1 *)
    assert(Hcons0: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts0: lookup partition (memory s0) beqAddr = Some (PDT pdentryPart)).
    {
      rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. injection HlookupPart as HpdentriesEq.
        subst pdentryPart. simpl in HbeqStructNull. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
      assumption.
    }
    specialize(Hcons0 partition pdentryPart HlookupParts0 HbeqStructNull). unfold isKS in *. rewrite Hs1.
    simpl. destruct (beqAddr newPDBlockStartAddr (structure pdentryPart)) eqn:HbeqStartStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartStruct. rewrite <-HbeqStartStruct in *. rewrite HremovedAddr in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END StructurePointerIsKS *)
  }
  assert(StructurePointerIsKS s3).
  { (* BEGIN StructurePointerIsKS s3 *)
    assert(Hcons0: StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts0: lookup partition (memory s0) beqAddr = Some (PDT pdentryPart)).
    {
      rewrite Hs3 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
      assert(HbeqStartPart: newPDBlockStartAddr <> partition).
      {
        intro Hcontra. subst partition. rewrite HlookupNewPDs2 in *. injection HlookupPart as HpdentriesEq.
        subst pdentryPart. rewrite HnewPD in HbeqStructNull. simpl in HbeqStructNull. congruence.
      }
      rewrite HlookupEqs2s0 in HlookupPart; assumption.
    }
    specialize(Hcons0 partition pdentryPart HlookupParts0 HbeqStructNull). unfold isKS in *.
    rewrite Hs3. simpl. destruct (beqAddr idBlock (structure pdentryPart)) eqn:HbeqBlockStruct.
    - rewrite <-DTL.beqAddrTrue in HbeqBlockStruct. rewrite <-HbeqBlockStruct in *. rewrite HlookupBlocks0 in *.
      rewrite HnewBEntry. simpl. assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite HlookupEqs2s0; try(assumption). intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *.
      congruence.
    (* END StructurePointerIsKS *)
  }
  assert(PDTIfPDFlag s1).
  { (* BEGIN PDTIfPDFlag s1 *)
    assert(Hcons0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros idPDchild sh1entryaddr HcheckChild. destruct HcheckChild as (HcheckChild & Hsh1Bis).
    assert(HcheckChilds0: true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. rewrite Hs1 in HcheckChild. rewrite Hs1 in Hsh1Bis.
      simpl in *.
      destruct (beqAddr newPDBlockStartAddr idPDchild) eqn:HbeqStartPDChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
      split; try(assumption). rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
      destruct (lookup idPDchild (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      destruct (beqAddr newPDBlockStartAddr sh1entryaddr) eqn:HbeqNewSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
      assumption.
    }
    specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds0). unfold bentryAFlag in *. unfold bentryPFlag in *.
    destruct Hcons0 as (HAFlag & HPFlag & [startaddr (Hstart & HstartIsPDT)]). unfold bentryStartAddr in *.
    unfold entryPDT in *. unfold sh1entryAddr in Hsh1Bis. rewrite Hs1. rewrite Hs1 in Hsh1Bis. simpl.
    simpl in Hsh1Bis.
    destruct (beqAddr newPDBlockStartAddr idPDchild) eqn:HbeqStartPDChild; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    split. assumption. split. assumption. exists startaddr. split. assumption.
    destruct (lookup idPDchild (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    destruct (beqAddr newPDBlockStartAddr (startAddr (blockrange b))) eqn:HbeqStartStartBis.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartStartBis. rewrite <-HbeqStartStartBis in *. rewrite HremovedAddr in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END PDTIfPDFlag *)
  }
  assert(PDTIfPDFlag s2).
  { (* BEGIN PDTIfPDFlag s2 *)
    assert(Hcons0: PDTIfPDFlag s1) by assumption.
    intros idPDchild sh1entryaddr HcheckChild. destruct HcheckChild as (HcheckChild & Hsh1Bis).
    assert(HcheckChilds0: true = checkChild idPDchild s1 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s1).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. rewrite Hs2 in HcheckChild. rewrite Hs2 in Hsh1Bis.
      simpl in *.
      destruct (beqAddr newPDBlockStartAddr idPDchild) eqn:HbeqStartPDChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
      split; try(assumption). rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
      destruct (lookup idPDchild (memory s1) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      destruct (beqAddr newPDBlockStartAddr sh1entryaddr) eqn:HbeqNewSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
      assumption.
    }
    specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds0). unfold bentryAFlag in *. unfold bentryPFlag in *.
    destruct Hcons0 as (HAFlag & HPFlag & [startaddr (Hstart & HstartIsPDT)]). unfold bentryStartAddr in *.
    unfold entryPDT in *. unfold sh1entryAddr in Hsh1Bis. rewrite Hs2. rewrite Hs2 in Hsh1Bis. simpl.
    simpl in Hsh1Bis.
    destruct (beqAddr newPDBlockStartAddr idPDchild) eqn:HbeqStartPDChild; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    split. assumption. split. assumption. exists startaddr. split. assumption.
    destruct (lookup idPDchild (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
    destruct (beqAddr newPDBlockStartAddr (startAddr (blockrange b))) eqn:HbeqStartStartBis.
    + rewrite <-DTL.beqAddrTrue in HbeqStartStartBis. rewrite <-HbeqStartStartBis in *.
      rewrite Hs1 in HstartIsPDT. simpl in HstartIsPDT. rewrite beqAddrTrue in HstartIsPDT. assumption.
    + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END PDTIfPDFlag *)
  }
  assert(PDTIfPDFlag s3).
  { (* BEGIN PDTIfPDFlag s3 *)
    assert(Hcons0: PDTIfPDFlag s2) by assumption.
    intros idPDchild sh1entryaddr HcheckChild. destruct HcheckChild as (HcheckChild & Hsh1Bis).
    assert(HcheckChilds0: true = checkChild idPDchild s2 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s2).
    {
      unfold checkChild in *. unfold sh1entryAddr in *. destruct (beqAddr idBlock idPDchild) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst idPDchild. rewrite HlookupBlocks2.
        rewrite HlookupBlocks3 in *. split; try(assumption). rewrite Hs3 in HcheckChild.
        simpl in *. destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym); assumption.
      - rewrite Hs3 in HcheckChild. rewrite Hs3 in Hsh1Bis. simpl in *. rewrite HbeqBlocks in *.
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption). split; try(assumption).
        destruct (lookup idPDchild (memory s2) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds0). unfold bentryAFlag in *. unfold bentryPFlag in *.
    destruct Hcons0 as (HAFlag & HPFlag & [startaddr (Hstart & HstartIsPDT)]). unfold bentryStartAddr in *.
    unfold entryPDT in *. destruct (beqAddr idBlock idPDchild) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst idPDchild. rewrite HlookupBlocks0 in *.
      rewrite HlookupBlocks2 in *. rewrite HlookupBlocks3. rewrite HnewBEntry. simpl. split. reflexivity. split.
      assumption. exists startaddr. rewrite Hs3. simpl. split. assumption.
      destruct (beqAddr idBlock (startAddr (blockrange bentry))) eqn:HbeqBlockStartBis.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockStartBis. rewrite <-HbeqBlockStartBis in *.
        rewrite HlookupBlocks2 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    - unfold sh1entryAddr in Hsh1Bis. rewrite Hs3. rewrite Hs3 in Hsh1Bis. simpl. simpl in Hsh1Bis.
      rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption). split. assumption. split.
      assumption. exists startaddr. split. assumption.
      destruct (lookup idPDchild (memory s2) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr idBlock (startAddr (blockrange b))) eqn:HbeqBlockStart.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockStart. rewrite <-HbeqBlockStart in *. rewrite HlookupBlocks2 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END PDTIfPDFlag *)
  }
  assert(wellFormedFstShadowIfBlockEntry s2).
  { (* BEGIN wellFormedFstShadowIfBlockEntry s2 *)
    assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block HblockIsBE.
    assert(HblockIsBEs0: isBE block s0).
    {
      unfold isBE in *.
      assert(HbeqNewPDBlockBis: newPDBlockStartAddr <> block).
      {
        intro Hcontra. subst block. rewrite HlookupNewPDs2 in *. congruence.
      }
      rewrite <-HlookupEqs2s0; assumption.
    }
    specialize(Hcons0 block HblockIsBEs0). unfold isSHE in *.
    assert(HbeqNewPDBlockSh1: newPDBlockStartAddr <> (CPaddr (block + sh1offset))).
    {
      intro Hcontra. rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
    }
    rewrite HlookupEqs2s0; assumption.
    (* END wellFormedFstShadowIfBlockEntry *)
  }
  assert(HgetPartsEqs1s0: getPartitions multiplexer s1 = getPartitions multiplexer s0).
  {
    rewrite Hs1. apply getPartitionsEqPDTNewEmptyPart.
    - left. assumption.
    - simpl. reflexivity.
    - unfold consistency in *; unfold consistency1 in *; intuition.
    - unfold consistency in *; unfold consistency1 in *; intuition.
  }
  assert(HgetPartsEqs2s1: getPartitions multiplexer s2 = getPartitions multiplexer s1).
  {
    rewrite Hs2. apply getPartitionsEqPDTNewEmptyPart; try(assumption).
    - right. exists {|
                      structure := nullAddr;
                      firstfreeslot := nullAddr;
                      nbfreeslots := zero;
                      nbprepare := zero;
                      parent := nullAddr;
                      MPU := [];
                      vidtAddr := nullAddr
                    |}. rewrite Hs1. simpl. rewrite beqAddrTrue. split; reflexivity.
    - rewrite HnewPD. simpl. reflexivity.
  }
  assert(HgetPartsEqs3s2: getPartitions multiplexer s3 = getPartitions multiplexer s2).
  {
    rewrite Hs3. destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChild & Hsh1)]].
    apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentry sh1entryaddr;
      try(rewrite HnewBEntry; simpl; reflexivity); try(assumption).
    - unfold isPDT. rewrite Hs2. rewrite Hs1. simpl.
      destruct (beqAddr newPDBlockStartAddr multiplexer) eqn:HbeqStartMult; trivial.
      rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      unfold consistency in *; unfold consistency1 in *; intuition.
    - unfold sh1entryAddr in *. rewrite HlookupBlocks2. rewrite HlookupBlocks0 in *. assumption.
    - simpl. destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1.
      {
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. subst sh1entryaddr. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      reflexivity.
  }
  assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
  {
    rewrite <-HgetPartsEqs1s0. rewrite <-HgetPartsEqs2s1. rewrite <-HgetPartsEqs3s2. rewrite Hs.
    apply getPartitionsEqPDT with pdentry; try(assumption). simpl. reflexivity.
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
      destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchild & Hsh1)]]. unfold sh1entryAddr in *.
      rewrite HlookupBlocks0 in *. subst sh1entryaddr.
      specialize(Htypes idBlock nullAddr newPDBlockEndAddr HstartBlock HendBlock HPDchild).
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
  assert(HcurrEq: currentPartition s = currentPartition s0).
  {
    rewrite Hs. rewrite Hs3. simpl. rewrite Hs2. rewrite Hs1. simpl. reflexivity.
  }
  assert(currentPartitionInPartitionsList s).
  { (* BEGIN currentPartitionInPartitionsList s *)
    assert(Hcons0: currentPartitionInPartitionsList s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold currentPartitionInPartitionsList in *.
    rewrite HcurrEq. rewrite HgetPartsEq. assumption.
    (* END currentPartitionInPartitionsList *)
  }
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
    assert(Hcons0: StructurePointerIsKS s3) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s3) beqAddr = Some (PDT pdentryParts0)
                                                /\ structure pdentryParts0 = structure pdentryPart).
    {
      rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - exists pdentry. injection HlookupPart as HpdentriesEq. rewrite <-HpdentriesEq. simpl.
        rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. split. assumption. reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        exists pdentryPart. split. assumption. reflexivity.
    }
    destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HstructEq)]. rewrite <-HstructEq in *.
    specialize(Hcons0 partition pdentryParts0 HlookupParts0 HbeqStructNull). unfold isKS in *. rewrite Hs.
    simpl. destruct (beqAddr currentPart (structure pdentryParts0)) eqn:HbeqCurrStruct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrStruct. rewrite <-HbeqCurrStruct in *. rewrite HlookupCurrs3 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
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

  assert(HgetFreeSlotsListEq: forall part, isPDT part s
          -> beqAddr newPDBlockStartAddr part = false
          -> getFreeSlotsList part s = getFreeSlotsList part s0).
  {
    intros part HpartIsPDT HbeqStartPart.
    assert(HlookupPartEq: exists pdentryPart pdentryParts0,
                            lookup part (memory s) beqAddr = Some(PDT pdentryPart)
                            /\ lookup part (memory s0) beqAddr = Some(PDT pdentryParts0)
                            /\ firstfreeslot pdentryParts0 = firstfreeslot pdentryPart
                            /\ nbfreeslots pdentryParts0 = nbfreeslots pdentryPart).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. rewrite Hs. rewrite Hs3. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. exists newPDCurr. exists pdentry. split.
        reflexivity. split. assumption. unfold newPDCurr. simpl. split; reflexivity.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock part) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        rewrite HlookupEqs2s0 in HpartIsPDT; try(assumption).
        destruct (lookup part (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists p. exists p. split. reflexivity. split. reflexivity.
        split; reflexivity.
    }
    destruct HlookupPartEq as [pdentryPart [pdentryParts0 (HlookupPart & HlookupParts0 & HfirstFreeEq &
      HnbFreeEq)]]. unfold getFreeSlotsList. rewrite HlookupPart. rewrite HlookupParts0.
    rewrite <-HfirstFreeEq in *. rewrite <-HnbFreeEq in *.
    destruct (beqAddr (firstfreeslot pdentryParts0) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
    assert(firstfreeslot pdentryParts0 <> newPDBlockStartAddr).
    {
      assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      rewrite <-beqAddrFalse in HbeqFirstNull.
      specialize(HfirstIsBE part pdentryParts0 HlookupParts0 HbeqFirstNull).
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
            getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryParts0) s1 (nbfreeslots pdentryParts0)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryParts0) s0 (nbfreeslots pdentryParts0)).
    {
      rewrite Hs1. apply getFreeSlotsListRecEqPDT; assumption.
    }
    rewrite <-HgetFreeEqs1s0 in *.
    assert(HgetFreeEqs2s1:
            getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryParts0) s2 (nbfreeslots pdentryParts0)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryParts0) s1 (nbfreeslots pdentryParts0)).
    {
      rewrite Hs2. apply getFreeSlotsListRecEqPDT; try(assumption).
      - unfold isBE. rewrite Hs1. simpl. rewrite beqAddrTrue. congruence.
      - unfold isPADDR. rewrite Hs1. simpl. rewrite beqAddrTrue. congruence.
    }
    rewrite <-HgetFreeEqs2s1 in *.
    assert(HgetFreeEqss3:
            getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryParts0) s (nbfreeslots pdentryParts0)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryParts0) s3 (nbfreeslots pdentryParts0)).
    {
      rewrite Hs. apply getFreeSlotsListRecEqPDT.
      - assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        rewrite <-beqAddrFalse in HbeqFirstNull.
        specialize(HfirstIsBE part pdentryParts0 HlookupParts0 HbeqFirstNull).
        destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. intro Hcontra.
        rewrite <-Hcontra in *. rewrite HlookupCurrs0 in *. congruence.
      - unfold isBE. rewrite HlookupCurrs3. congruence.
      - unfold isPADDR. rewrite HlookupCurrs3. congruence.
    }
    rewrite HgetFreeEqss3 in *.
    assert(HgetFreeEqs3s2:
            getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryParts0) s3 (nbfreeslots pdentryParts0)
              = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentryParts0) s2 (nbfreeslots pdentryParts0)).
    {
      rewrite Hs3. assert(HnoDupFree: NoDupInFreeSlotsList s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      specialize(HnoDupFree part pdentryParts0 HlookupParts0).
      destruct HnoDupFree as [optionfreeslotslists0 (Hlists0 & Hwells0 & HnoDups0)].
      unfold getFreeSlotsList in *. rewrite HlookupParts0 in *. rewrite HbeqFirstNull in *.
      subst optionfreeslotslists0.
      assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      rewrite <-beqAddrFalse in HbeqFirstNull.
      specialize(HfirstFree part pdentryParts0 HlookupParts0 HbeqFirstNull).
      destruct HfirstFree as (_ & HfirstFree). unfold isFreeSlot in HfirstFree.
      apply getFreeSlotsListRecEqBE; try(reflexivity); try(rewrite HgetFreeEqs1s0); try(assumption).
      - intro Hcontra. rewrite Hcontra in *. unfold bentryPFlag in *. rewrite HlookupBlocks0 in *.
        destruct (lookup (CPaddr (idBlock + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (lookup (CPaddr (idBlock + scoffset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). destruct HfirstFree as (_ & _ & _ & _ & Hpresent & _).
        congruence.
      - unfold isBE. rewrite HlookupBlocks2. trivial.
      - assert(HwellFormed: getFreeSlotsList part s0 = getFreeSlotsList part s0
                            /\ wellFormedFreeSlotsList (getFreeSlotsList part s0) <> False).
        {
          split. reflexivity. unfold getFreeSlotsList. rewrite HlookupParts0.
          rewrite beqAddrFalse in HbeqFirstNull. rewrite HbeqFirstNull. assumption.
        }
        intro Hcontra.
        assert(HblockIn: filterOptionPaddr (getFreeSlotsList part s0)
                            = filterOptionPaddr (getFreeSlotsList part s0)
                          /\ In idBlock (filterOptionPaddr (getFreeSlotsList part s0))).
        {
          split; try(reflexivity). unfold getFreeSlotsList. rewrite HlookupParts0.
          rewrite beqAddrFalse in HbeqFirstNull. rewrite HbeqFirstNull. assumption.
        }
        rewrite beqAddrSym in HbeqNullBlock. rewrite <-beqAddrFalse in HbeqNullBlock.
        assert(HfreeList: freeSlotsListIsFreeSlot s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HpartIsPDTs0: isPDT part s0).
        {
          unfold isPDT. rewrite HlookupParts0. trivial.
        }
        specialize(HfreeList part idBlock (getFreeSlotsList part s0)
          (filterOptionPaddr (getFreeSlotsList part s0)) HpartIsPDTs0 HwellFormed HblockIn HbeqNullBlock).
        congruence.
    }
    rewrite <-HgetFreeEqs3s2 in *. reflexivity.
  }
  assert(HgetKSEntriesEq: forall part, isPDT part s
          -> beqAddr newPDBlockStartAddr part = false
          -> getKSEntries part s = getKSEntries part s0).
  {
    intros part HpartIsPDT HbeqStartPart.
    assert(HlookupPartEq: exists pdentryPart pdentryParts0,
                            lookup part (memory s) beqAddr = Some(PDT pdentryPart)
                            /\ lookup part (memory s0) beqAddr = Some(PDT pdentryParts0)
                            /\ structure pdentryParts0 = structure pdentryPart).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. rewrite Hs. rewrite Hs3. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. exists newPDCurr. exists pdentry. split.
        reflexivity. split. assumption. unfold newPDCurr. simpl. reflexivity.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock part) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        rewrite HlookupEqs2s0 in HpartIsPDT; try(assumption).
        destruct (lookup part (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists p. exists p. split. reflexivity. split. reflexivity.
        reflexivity.
    }
    destruct HlookupPartEq as [pdentryPart [pdentryParts0 (HlookupPart & HlookupParts0 & HstructEq)]].
    rewrite <-beqAddrFalse in HbeqStartPart.
    assert(HgetKSEqs1s0: getKSEntries part s1 = getKSEntries part s0).
    {
      rewrite Hs1. apply getKSEntriesEqPDTNewEmptyPart.
      - left. assumption.
      - simpl. reflexivity.
      - unfold consistency in *; unfold consistency1 in *; intuition.
    }
    assert(HgetKSEqs2s1: getKSEntries part s2 = getKSEntries part s1).
    {
      rewrite Hs2. apply getKSEntriesEqPDTNewEmptyPart; try(assumption).
      - right. rewrite Hs1. simpl. rewrite beqAddrTrue. exists {|
                                                                 structure := nullAddr;
                                                                 firstfreeslot := nullAddr;
                                                                 nbfreeslots := zero;
                                                                 nbprepare := zero;
                                                                 parent := nullAddr;
                                                                 MPU := [];
                                                                 vidtAddr := nullAddr
                                                               |}. split. reflexivity. simpl. reflexivity.
      - rewrite HnewPD. simpl. reflexivity.
    }
    assert(HgetKSEqs3s2: getKSEntries part s3 = getKSEntries part s2).
    {
      rewrite Hs3. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks2. trivial.
    }
    assert(HgetKSEqss3: getKSEntries part s = getKSEntries part s3).
    {
      rewrite Hs. apply getKSEntriesEqPDT with pdentry; try(assumption). unfold newPDCurr. simpl. reflexivity.
    }
    rewrite HgetKSEqss3. rewrite HgetKSEqs3s2. rewrite HgetKSEqs2s1. assumption.
  }
  assert(HgetMappedBlocksEq: forall part, isPDT part s
          -> beqAddr newPDBlockStartAddr part = false
          -> getMappedBlocks part s = getMappedBlocks part s0).
  {
    intros part HpartIsPDT HbeqStartPart. unfold getMappedBlocks. rewrite HgetKSEntriesEq; try(assumption).
    set(list := filterOptionPaddr (getKSEntries part s0)).
    assert(HfiltPresEqs1s0: filterPresent list s1 = filterPresent list s0).
    {
      rewrite Hs1. apply filterPresentEqPDTNotBE. unfold isBE. rewrite HremovedAddr. intro Hcontra.
      contradict Hcontra.
    }
    assert(HfiltPresEqs2s1: filterPresent list s2 = filterPresent list s1).
    {
      rewrite Hs2. apply filterPresentEqPDT. unfold isPDT. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial.
    }
    assert(HfiltPresEqs3s2: filterPresent list s3 = filterPresent list s2).
    {
      rewrite Hs3. apply filterPresentEqBENoChange with bentry; try(assumption). rewrite HnewBEntry. simpl.
      reflexivity.
    }
    rewrite <-HfiltPresEqs1s0. rewrite <-HfiltPresEqs2s1. rewrite <-HfiltPresEqs3s2. rewrite Hs.
    apply filterPresentEqPDT. unfold isPDT. rewrite HlookupCurrs3. trivial.
  }
  assert(HgetMappedPaddrEq: forall part, isPDT part s
          -> beqAddr newPDBlockStartAddr part = false
          -> getMappedPaddr part s = getMappedPaddr part s0).
  {
    intros part HpartIsPDT HbeqStartPart. unfold getMappedPaddr. rewrite HgetMappedBlocksEq; try(assumption).
    set(list := getMappedBlocks part s0).
    assert(HpaddrAuxEqs1s0: getAllPaddrAux list s1 = getAllPaddrAux list s0).
    {
      rewrite Hs1. apply getAllPaddrAuxEqPDTNewPart. assumption.
    }
    assert(HpaddrAuxEqs2s1: getAllPaddrAux list s2 = getAllPaddrAux list s1).
    {
      rewrite Hs2. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial.
    }
    assert(HpaddrAuxEqs3s2: getAllPaddrAux list s3 = getAllPaddrAux list s2).
    {
      rewrite Hs3. apply getAllPaddrAuxEqBEStartEndNoChange with bentry; try(assumption); rewrite HnewBEntry;
        simpl; reflexivity.
    }
    rewrite <-HpaddrAuxEqs1s0. rewrite <-HpaddrAuxEqs2s1. rewrite <-HpaddrAuxEqs3s2. rewrite Hs.
    apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupCurrs3. trivial.
  }
  assert(HgetConfigPaddrEq: forall part, isPDT part s0
          -> beqAddr newPDBlockStartAddr part = false
          -> getConfigPaddr part s = getConfigPaddr part s0).
  {
    intros part HpartIsPDTs0 HbeqStartPart.
    assert(HconfigEqs1s0: getConfigPaddr part s1 = getConfigPaddr part s0).
    {
      rewrite Hs1. apply getConfigPaddrEqPDTNewEmptyPart; try(assumption).
      left. assumption.
      simpl. reflexivity.
      unfold consistency in *; unfold consistency1 in *; intuition.
    }
    assert(HconfigEqs2s1: getConfigPaddr part s2 = getConfigPaddr part s1).
    {
      rewrite Hs2. apply getConfigPaddrEqPDT with {|
                                                    structure := nullAddr;
                                                    firstfreeslot := nullAddr;
                                                    nbfreeslots := zero;
                                                    nbprepare := zero;
                                                    parent := nullAddr;
                                                    MPU := [];
                                                    vidtAddr := nullAddr
                                                  |}; try(assumption).
      rewrite Hs1. simpl. rewrite beqAddrTrue. reflexivity.
      unfold isPDT in *. rewrite Hs1. simpl. rewrite HbeqStartPart. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      rewrite HnewPD. simpl. reflexivity.
    }
    assert(HconfigEqs3s2: getConfigPaddr part s3 = getConfigPaddr part s2).
    {
      rewrite Hs3. apply getConfigPaddrEqBE; try(assumption).
      unfold isPDT in *. rewrite Hs2. rewrite Hs1. simpl. rewrite HbeqStartPart. rewrite beqAddrTrue.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      unfold isBE. rewrite HlookupBlocks2. trivial.
    }
    rewrite <-HconfigEqs1s0. rewrite <-HconfigEqs2s1. rewrite <-HconfigEqs3s2. rewrite Hs.
    apply getConfigPaddrEqPDT with pdentry; try(assumption).
    unfold isPDT in *. rewrite Hs3. rewrite Hs2. rewrite Hs1. simpl.
    destruct (beqAddr idBlock part) eqn:HbeqBlockPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockPart. subst part. rewrite HlookupBlocks0 in *. congruence.
    }
    rewrite HbeqNewPDBlock. simpl. rewrite HbeqStartPart. rewrite beqAddrTrue.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    simpl. reflexivity.
  }
  assert(HstartNotPart: ~ In newPDBlockStartAddr (getPartitions multiplexer s0)).
  {
    intro Hcontra. assert(HstartIsPDTs0: isPDT newPDBlockStartAddr s0).
    { apply partitionsArePDT; try(assumption); unfold consistency in *; unfold consistency1 in *; intuition. }
    unfold isPDT in *. rewrite HremovedAddr in *. congruence.
  }
  assert(HgetChildrenEq: forall part, In part (getPartitions multiplexer s0)
                          -> getChildren part s = getChildren part s0).
  {
    intros part HpartIsPart.
    destruct (beqAddr newPDBlockStartAddr part) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst part. exfalso; congruence.
    }
    assert(HgetChildrenEqs1s0: getChildren part s1 = getChildren part s0).
    {
      rewrite Hs1. apply getChildrenEqPDTNewEmptyPart.
      - left. assumption.
      - simpl. reflexivity.
      - unfold consistency in *; unfold consistency1 in *; intuition.
    }
    assert(HgetChildrenEqs2s1: getChildren part s2 = getChildren part s1).
    {
      rewrite Hs2. apply getChildrenEqPDTNewEmptyPart.
      - right. exists {|
                        structure := nullAddr;
                        firstfreeslot := nullAddr;
                        nbfreeslots := zero;
                        nbprepare := zero;
                        parent := nullAddr;
                        MPU := [];
                        vidtAddr := nullAddr
                      |}. rewrite Hs1. simpl. rewrite beqAddrTrue. split; reflexivity.
      - rewrite HnewPD. simpl. reflexivity.
      - assumption.
    }
    assert(HgetChildrenEqs3s2: getChildren part s3 = getChildren part s2).
    {
      rewrite Hs3. destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChild & Hsh1)]].
      apply getChildrenEqBEPDflagNoChangePresentNoChange with bentry sh1entryaddr;
        try(rewrite HnewBEntry; simpl; reflexivity); try(assumption).
      - unfold isPDT. rewrite Hs2. rewrite Hs1. simpl. rewrite HbeqStartPart.
        rewrite beqAddrTrue. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). apply partitionsArePDT; try(assumption).
        1,2: unfold consistency in *; unfold consistency1 in *; intuition.
      - unfold sh1entryAddr in *. rewrite HlookupBlocks2. rewrite HlookupBlocks0 in *. assumption.
      - simpl. destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1.
        {
          exfalso. rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. subst sh1entryaddr. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        reflexivity.
    }
    rewrite <-HgetChildrenEqs1s0. rewrite <-HgetChildrenEqs2s1. rewrite <-HgetChildrenEqs3s2. rewrite Hs.
    apply getChildrenEqPDT with pdentry; try(assumption). simpl. reflexivity.
  }

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
    assert(HgetFreeEq: getFreeSlotsList partition s = getFreeSlotsList partition s0).
    { apply HgetFreeSlotsListEq; assumption. }
    rewrite HgetFreeEq in HoptList.
    assert(HpartIsPDTs0: isPDT partition s0).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs0. trivial.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
        rewrite HlookupEqs2s0 in HpartIsPDT; assumption.
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
        destruct HnbFree as [optionfreeslotslist (Hlist & Hres & _)].
        assert(HgetFreePart2Eq: getFreeSlotsList part2 s = getFreeSlotsList part2 s0).
        { apply HgetFreeSlotsListEq; assumption. }
        rewrite HgetFreePart2Eq. subst optionfreeslotslist. assumption.
      }
      exists []. exists (getFreeSlotsList part2 s). split.
      + unfold getFreeSlotsList. rewrite HlookupNewPDs. rewrite HnewPD. simpl. reflexivity.
      + simpl. split. intro Hcontra; rewrite <-Hcontra; trivial. split. reflexivity. split. assumption.
        intros addr Hcontra. contradict Hcontra.
    - assert(HgetFreePart1Eq: getFreeSlotsList part1 s = getFreeSlotsList part1 s0).
      { apply HgetFreeSlotsListEq; assumption. }
      rewrite HgetFreePart1Eq.
      assert(Hpart1IsPDTs0: isPDT part1 s0).
      {
        unfold isPDT in *. rewrite Hs in Hpart1IsPDT. rewrite Hs3 in Hpart1IsPDT. simpl in *.
        destruct (beqAddr currentPart part1) eqn:HbeqCurrPart1.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart1. subst part1. rewrite HlookupCurrs0. trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr idBlock part1) eqn:HbeqBlockPart1; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in Hpart1IsPDT; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in Hpart1IsPDT; try(apply not_eq_sym; assumption).
          rewrite <-HlookupEqs2s0; assumption.
      }
      assert(wellFormedFreeSlotsList (getFreeSlotsList part1 s) <> False).
      {
        assert(HnbFree: NbFreeSlotsISNbFreeSlotsInList s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HlookupPart1: isPDT part1 s0) by assumption. apply isPDTLookupEq in HlookupPart1.
        destruct HlookupPart1 as [pdentryPart1 HlookupPart1].
        assert(HnbFreePart1: pdentryNbFreeSlots part1 (nbfreeslots pdentryPart1) s0).
        { unfold pdentryNbFreeSlots. rewrite HlookupPart1. reflexivity. }
        specialize(HnbFree part1 (nbfreeslots pdentryPart1) Hpart1IsPDTs0 HnbFreePart1).
        destruct HnbFree as [optionfreeslotslist (Hlist & Hres & _)].
        rewrite HgetFreePart1Eq. subst optionfreeslotslist. assumption.
      }
      destruct (beqAddr newPDBlockStartAddr part2) eqn:HbeqStartPart2.
      + rewrite <-DTL.beqAddrTrue in HbeqStartPart2. subst part2. exists (getFreeSlotsList part1 s). exists [].
        split. assumption. split. assumption. split.
        * unfold getFreeSlotsList. rewrite HlookupNewPDs. rewrite HnewPD. simpl. reflexivity.
        * simpl. split. intro Hcontra; rewrite <-Hcontra; trivial. intros addr HaddrIn. apply in_nil.
      + assert(HgetFreePart2Eq: getFreeSlotsList part2 s = getFreeSlotsList part2 s0).
        { apply HgetFreeSlotsListEq; assumption. }
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
        specialize(Hcons0 part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts). rewrite HgetFreePart2Eq.
        assumption.
    (* END DisjointFreeSlotsLists *)
  }
  assert(inclFreeSlotsBlockEntries s).
  { (* BEGIN inclFreeSlotsBlockEntries s *)
    assert(Hcons0: inclFreeSlotsBlockEntries s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition HpartIsPDT. destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    - unfold getFreeSlotsList. rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. rewrite HlookupNewPDs.
      rewrite HnewPD. simpl. apply incl_nil_l.
    - assert(HgetFreePartEq: getFreeSlotsList partition s = getFreeSlotsList partition s0).
      { apply HgetFreeSlotsListEq; assumption. }
      rewrite HgetFreePartEq. rewrite HgetKSEntriesEq; try(assumption).
      assert(HpartIsPDTs0: isPDT partition s0).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs0. trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite HlookupEqs2s0 in HpartIsPDT; assumption.
      }
      specialize(Hcons0 partition HpartIsPDTs0). assumption.
    (* END inclFreeSlotsBlockEntries *)
  }
  assert(DisjointKSEntries s).
  { (* BEGIN DisjointKSEntries s *)
    assert(Hcons0: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
    destruct (beqAddr newPDBlockStartAddr part1) eqn:HbeqStartPart1.
    - rewrite <-DTL.beqAddrTrue in HbeqStartPart1. subst part1.
      destruct (beqAddr newPDBlockStartAddr part2) eqn:HbeqStartPart2.
      { rewrite <-DTL.beqAddrTrue in HbeqStartPart2. subst part2. exfalso; congruence. }
      exists []. exists (getKSEntries part2 s). split.
      + unfold getKSEntries. rewrite HlookupNewPDs. rewrite HnewPD. simpl. reflexivity.
      + simpl. split. reflexivity. intros addr Hcontra. contradict Hcontra.
    - assert(HgetKSPart1Eq: getKSEntries part1 s = getKSEntries part1 s0).
      { apply HgetKSEntriesEq; assumption. }
      rewrite HgetKSPart1Eq.
      assert(Hpart1IsPDTs0: isPDT part1 s0).
      {
        unfold isPDT in *. rewrite Hs in Hpart1IsPDT. rewrite Hs3 in Hpart1IsPDT. simpl in *.
        destruct (beqAddr currentPart part1) eqn:HbeqCurrPart1.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart1. subst part1. rewrite HlookupCurrs0. trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr idBlock part1) eqn:HbeqBlockPart1; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in Hpart1IsPDT; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in Hpart1IsPDT; try(apply not_eq_sym; assumption).
          rewrite <-HlookupEqs2s0; assumption.
      }
      destruct (beqAddr newPDBlockStartAddr part2) eqn:HbeqStartPart2.
      + rewrite <-DTL.beqAddrTrue in HbeqStartPart2. subst part2. exists (getKSEntries part1 s). exists [].
        split. assumption. split.
        * unfold getKSEntries. rewrite HlookupNewPDs. rewrite HnewPD. simpl. reflexivity.
        * simpl. intros addr HaddrIn. apply in_nil.
      + assert(HgetKSPart2Eq: getKSEntries part2 s = getKSEntries part2 s0).
        { apply HgetKSEntriesEq; assumption. }
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
        specialize(Hcons0 part1 part2 Hpart1IsPDTs0 Hpart2IsPDTs0 HbeqParts). rewrite HgetKSPart2Eq.
        assumption.
    (* END DisjointKSEntries *)
  }
  assert(noDupPartitionTree s).
  { (* BEGIN noDupPartitionTree s*)
    assert(Hcons0: noDupPartitionTree s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold noDupPartitionTree. rewrite HgetPartsEq. assumption.
    (* END noDupPartitionTree *)
  }
  assert(isParent s).
  { (* BEGIN isParent s *)
    assert(Hcons0: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros child pdparent HparentIsPart HchildIsChild. rewrite HgetPartsEq in HparentIsPart.
    assert(HgetChildrenParentEq: getChildren pdparent s = getChildren pdparent s0).
    { apply HgetChildrenEq; assumption. }
    rewrite HgetChildrenParentEq in HchildIsChild. specialize(Hcons0 child pdparent HparentIsPart HchildIsChild).
    unfold pdentryParent in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
    - rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. rewrite HlookupCurrs0 in *. simpl. assumption.
    - rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock child) eqn:HbeqBlockChild.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockChild. subst child. rewrite HlookupBlocks0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      assert(HbeqStartChild: newPDBlockStartAddr <> child).
      {
        intro Hcontra. subst child. rewrite HremovedAddr in *. congruence.
      }
      rewrite HlookupEqs2s0; assumption.
    (* END isParent *)
  }
  assert(isChild s).
  { (* BEGIN isChild s *)
    assert(Hcons0: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros child pdparent HchildIsPart HparentIsParent HbeqChildRoot. rewrite HgetPartsEq in HchildIsPart.
    assert(HparentIsParents0: pdentryParent child pdparent s0).
    {
      unfold pdentryParent in *. rewrite Hs in HparentIsParent. rewrite Hs3 in HparentIsParent. simpl in *.
      destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. rewrite HlookupCurrs0. simpl in *. assumption.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock child) eqn:HbeqBlockChild; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HparentIsParent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HparentIsParent; try(apply not_eq_sym; assumption).
        assert(HbeqStartChild: newPDBlockStartAddr <> child).
        {
          intro Hcontra. subst child. congruence.
        }
        rewrite <-HlookupEqs2s0; assumption.
    }
    assert(HgetChildrenParentEq: getChildren pdparent s = getChildren pdparent s0).
    {
      apply HgetChildrenEq. assert(HparentOfPart: parentOfPartitionIsPartition s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      apply partitionsArePDT in HchildIsPart; try(unfold consistency in *; unfold consistency1 in *; intuition;
        congruence). unfold isPDT in *.
      destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild).
      destruct HparentOfPart as (HparentIsPart & _ & _). specialize(HparentIsPart HbeqChildRoot).
      destruct HparentIsPart as (_ & HparentIsPart). unfold pdentryParent in *. rewrite HlookupChild in *.
      subst pdparent. assumption.
    }
    rewrite HgetChildrenParentEq. specialize(Hcons0 child pdparent HchildIsPart HparentIsParents0 HbeqChildRoot).
    assumption.
    (* END isChild *)
  }
  assert(noDupKSEntriesList s).
  { (* BEGIN noDupKSEntriesList s *)
    assert(Hcons0: noDupKSEntriesList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition HpartIsPDT. destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    - rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition.
      unfold getKSEntries. rewrite HlookupNewPDs. rewrite HnewPD. simpl. apply NoDup_nil.
    - assert(HpartIsPDTs0: isPDT partition s0).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs0. trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite HlookupEqs2s0 in HpartIsPDT; assumption.
      }
      specialize(Hcons0 partition HpartIsPDTs0). rewrite HgetKSEntriesEq; assumption.
    (* END noDupKSEntriesList *)
  }
  assert(noDupMappedBlocksList s).
  { (* BEGIN noDupMappedBlocksList s *)
    assert(Hcons0: noDupMappedBlocksList s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition HpartIsPDT. destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    - rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getMappedBlocks.
      unfold getKSEntries. rewrite HlookupNewPDs. rewrite HnewPD. simpl. apply NoDup_nil.
    - assert(HpartIsPDTs0: isPDT partition s0).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs0. trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite HlookupEqs2s0 in HpartIsPDT; assumption.
      }
      specialize(Hcons0 partition HpartIsPDTs0). rewrite HgetMappedBlocksEq; assumption.
    (* END noDupMappedBlocksList *)
  }
  assert(wellFormedBlock s).
  { (* BEGIN wellFormedBlock s *)
    assert(Hcons0: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block startaddr endaddr HPFlag Hstart Hend. unfold bentryPFlag in *. unfold bentryStartAddr in *.
    unfold bentryEndAddr in *. rewrite Hs in HPFlag. rewrite Hs in Hstart. rewrite Hs in Hend.
    rewrite Hs3 in HPFlag. rewrite Hs3 in Hstart. rewrite Hs3 in Hend. simpl in *.
    destruct (beqAddr currentPart block) eqn:HbeqCurBlockBis; try(exfalso; congruence).
    rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
    - rewrite HnewBEntry in *. simpl in *. rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block.
      assert(HPFlags0: bentryPFlag idBlock true s0).
      {
        unfold bentryPFlag. rewrite HlookupBlocks0. assumption.
      }
      assert(Hstarts0: bentryStartAddr idBlock startaddr s0).
      {
        unfold bentryStartAddr. rewrite HlookupBlocks0. assumption.
      }
      assert(Hends0: bentryEndAddr idBlock endaddr s0).
      {
        unfold bentryEndAddr. rewrite HlookupBlocks0. assumption.
      }
      specialize(Hcons0 idBlock startaddr endaddr HPFlags0 Hstarts0 Hends0). assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HPFlag; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HPFlag; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hend; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hend; try(apply not_eq_sym; assumption).
      assert(HbeqStartBlock: newPDBlockStartAddr <> block).
      {
        intro Hcontra. subst block. rewrite HlookupNewPDs2 in *. congruence.
      }
      rewrite HlookupEqs2s0 in HPFlag; try(assumption).
      rewrite HlookupEqs2s0 in Hstart; try(assumption).
      rewrite HlookupEqs2s0 in Hend; try(assumption).
      specialize(Hcons0 block startaddr endaddr HPFlag Hstart Hend). assumption.
    (* END wellFormedBlock *)
  }
  assert(parentOfPartitionIsPartition s2).
  { (* BEGIN parentOfPartitionIsPartition s2 *)
    assert(Hcons0: parentOfPartitionIsPartition s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart HlookupPart. destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    - rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. rewrite HlookupPart in HlookupNewPDs2.
      injection HlookupNewPDs2 as HpdentriesEq. subst pdentryPart. rewrite HnewPD. simpl.
      assert(HbeqStartRoot: newPDBlockStartAddr <> constantRootPartM).
      {
        intro Hcontra. subst newPDBlockStartAddr.
        assert(HmultPDT: multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold multiplexerIsPDT in *. unfold isPDT in *. unfold multiplexer in *. rewrite HremovedAddr in *.
        congruence.
      }
      rewrite <-beqAddrFalse in HbeqCurrStart. split; try(split; try(assumption); congruence). intro.
      split.
      + exists pdentry. assumption.
      + rewrite HgetPartsEqs2s1. rewrite HgetPartsEqs1s0.
        assert(HcurrIsPart: currentPartitionInPartitionsList s0)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold currentPartitionInPartitionsList. rewrite Hcurr. assumption.
    - rewrite <-beqAddrFalse in *. rewrite HlookupEqs2s0 in HlookupPart; try(assumption).
      specialize(Hcons0 partition pdentryPart HlookupPart).
      destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split; try(split; assumption).
      intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
      rewrite HgetPartsEqs2s1. rewrite HgetPartsEqs1s0.
      split; try(assumption). exists parentEntry.
      destruct (beqAddr idBlock (parent pdentryPart)) eqn:HbeqBlockParent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite <-HbeqBlockParent in *. congruence.
      }
      assert(HbeqStartParent: newPDBlockStartAddr <> parent pdentryPart).
      { intro Hcontra. rewrite Hcontra in *. congruence. }
      rewrite HlookupEqs2s0; assumption.
    (* END parentOfPartitionIsPartition *)
  }
  assert(parentOfPartitionIsPartition s3).
  { (* BEGIN parentOfPartitionIsPartition s3 *)
    assert(Hcons0: parentOfPartitionIsPartition s2) by assumption.
    intros partition pdentryPart HlookupPart. rewrite Hs3 in HlookupPart. simpl in *.
    destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
    specialize(Hcons0 partition pdentryPart HlookupPart).
    destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split; try(split; assumption).
    intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEqs3s2.
    split; try(assumption). rewrite Hs3. simpl. exists parentEntry.
    destruct (beqAddr idBlock (parent pdentryPart)) eqn:HbeqBlockParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite <-HbeqBlockParent in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END parentOfPartitionIsPartition *)
  }
  assert(parentOfPartitionIsPartition s).
  { (* BEGIN parentOfPartitionIsPartition s *)
    assert(Hcons0: parentOfPartitionIsPartition s3) by assumption.
    intros partition pdentryPart HlookupPart. rewrite Hs in HlookupPart. simpl in *.
    destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
    + rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. injection HlookupPart as HpdentriesEq.
      subst pdentryPart. simpl. specialize(Hcons0 currentPart pdentry HlookupCurrs3).
      destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentCurr).
      split; try(split; try(assumption); congruence). intro HbeqCurrRoot.
      specialize(HparentIsPart HbeqCurrRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEq.
      rewrite <-HgetPartsEqs1s0. rewrite <-HgetPartsEqs2s1. rewrite <-HgetPartsEqs3s2.
      split; try(assumption). exists parentEntry. rewrite Hs. simpl.
      rewrite beqAddrFalse in HbeqParentCurr. rewrite beqAddrSym in HbeqParentCurr. rewrite HbeqParentCurr.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      assumption.
    + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
      specialize(Hcons0 partition pdentryPart HlookupPart).
      destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split; try(split; assumption).
      intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
      destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEq.
      rewrite <-HgetPartsEqs1s0. rewrite <-HgetPartsEqs2s1. rewrite <-HgetPartsEqs3s2.
      split; try(assumption). rewrite Hs. simpl.
      destruct (beqAddr currentPart (parent pdentryPart)) eqn:HbeqCurrParent.
      * rewrite <-DTL.beqAddrTrue in HbeqCurrParent. rewrite <-HbeqCurrParent in *. exists newPDCurr.
        reflexivity.
      * exists parentEntry. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
    (* END parentOfPartitionIsPartition *)
  }
  assert(NbFreeSlotsISNbFreeSlotsInList s).
  { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
    assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition nbfree HpartIsPDT HnbFree.
    destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    - rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getFreeSlotsList. rewrite HlookupNewPDs.
      rewrite HnewPD. simpl. exists []. split. reflexivity. simpl. split. intro Hcontra. rewrite <-Hcontra.
      trivial. unfold pdentryNbFreeSlots in *. rewrite HlookupNewPDs in *. rewrite HnewPD in *. simpl in *.
      unfold zero in *. unfold CIndex in *. destruct (le_dec 0 maxIdx); try(lia). rewrite HnbFree. simpl.
      reflexivity.
    - assert(Hparts0: isPDT partition s0 /\ pdentryNbFreeSlots partition nbfree s0).
      {
        unfold isPDT in *. unfold pdentryNbFreeSlots in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT.
        rewrite Hs in HnbFree. rewrite Hs3 in HnbFree. simpl in *.
        destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs0. split; trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HnbFree; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HnbFree; try(apply not_eq_sym; assumption).
          rewrite <-HlookupEqs2s0; try(assumption). split; assumption.
      }
      destruct Hparts0 as (HpartIsPDTs0 & HnbFrees0). specialize(Hcons0 partition nbfree HpartIsPDTs0 HnbFrees0).
      rewrite HgetFreeSlotsListEq; assumption.
    (* END NbFreeSlotsISNbFreeSlotsInList *)
  }
  assert(HisListOfKernelsEq: forall part kernList, beqAddr newPDBlockStartAddr part = false
          -> isListOfKernels kernList part s -> isListOfKernels kernList part s0).
  {
    intros part kernList HbeqStartPart HkernLists.
    assert(HkernEqs3: isListOfKernels kernList part s3).
    {
      rewrite Hs in HkernLists. revert HkernLists. apply isListOfKernelsEqPDT with pdentry; try(assumption).
      simpl. reflexivity.
    }
    assert(HkernEqs2: isListOfKernels kernList part s2).
    {
      rewrite Hs3 in HkernEqs3. revert HkernEqs3. apply isListOfKernelsEqBE.
    }
    assert(HkernEqs1: isListOfKernels kernList part s1).
    {
      rewrite Hs2 in HkernEqs2. revert HkernEqs2. apply isListOfKernelsEqPDT with {|
                                                                                    structure := nullAddr;
                                                                                    firstfreeslot := nullAddr;
                                                                                    nbfreeslots := zero;
                                                                                    nbprepare := zero;
                                                                                    parent := nullAddr;
                                                                                    MPU := [];
                                                                                    vidtAddr := nullAddr
                                                                                  |}.
      - rewrite Hs1. simpl. rewrite beqAddrTrue. reflexivity.
      - rewrite HnewPD. simpl. reflexivity.
    }
    revert HkernEqs1. rewrite Hs1. apply isListOfKernelsEqPDTNewEmptyPart; try(simpl; reflexivity). left.
    assumption.
  }
  assert(maxNbPrepareIsMaxNbKernels s).
  { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
    assert(Hcons0: maxNbPrepareIsMaxNbKernels s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition kernList HkernList. destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold isListOfKernels in *.
      destruct kernList; try(simpl; lia). exfalso.
      destruct HkernList as [newPDEntryBis (HlookupNewPDsBis & HstructNotNull & _)].
      rewrite HlookupNewPDsBis in *. injection HlookupNewPDs as HpdentriesEq. subst newPDEntryBis.
      rewrite HnewPD in *. simpl in *. congruence.
    }
    assert(HkernLists0: isListOfKernels kernList partition s0).
    { apply HisListOfKernelsEq; assumption. }
    specialize(Hcons0 partition kernList HkernLists0). assumption.
    (* END maxNbPrepareIsMaxNbKernels *)
  }
  assert(blockInChildHasAtLeastEquivalentBlockInParent s).
  { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
    assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild
      HendChild HPFlagChild. rewrite HgetPartsEq in HparentIsPart.
    destruct (beqAddr newPDBlockStartAddr pdparent) eqn:HbeqStartParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartParent. subst pdparent. exfalso; congruence.
    }
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child. unfold getMappedBlocks in HblockMappedChild.
      unfold getKSEntries in HblockMappedChild. rewrite HlookupNewPDs in *. rewrite HnewPD in HblockMappedChild.
      simpl in *. exfalso; congruence.
    }
    assert(HchildIsPDTs: isPDT child s).
    { apply childrenArePDT with pdparent; assumption. }
    rewrite HgetChildrenEq in HchildIsChild; try(assumption).
    rewrite HgetMappedBlocksEq in HblockMappedChild; try(assumption).
    assert(HparentIsPDTs: isPDT pdparent s).
    { rewrite <-HgetPartsEq in HparentIsPart. apply partitionsArePDT; assumption. }
    rewrite HgetMappedBlocksEq; try(assumption).
    assert(Hblocks0: bentryStartAddr block startChild s0 /\ bentryEndAddr block endChild s0
                    /\ bentryPFlag block true s0).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartChild.
      rewrite Hs in HendChild. rewrite Hs in HPFlagChild. rewrite Hs3 in HstartChild. rewrite Hs3 in HendChild.
      rewrite Hs3 in HPFlagChild. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewBEntry in *. simpl in *.
        rewrite HlookupBlocks0. split; try(split); assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HstartChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HstartChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HendChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HendChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPFlagChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPFlagChild; try(apply not_eq_sym; assumption).
        assert(HbeqStartBlock: newPDBlockStartAddr <> block).
        {
          intro Hcontra. subst block. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite HlookupEqs2s0 in HstartChild; try(assumption).
        rewrite HlookupEqs2s0 in HendChild; try(assumption).
        rewrite HlookupEqs2s0 in HPFlagChild; try(assumption). split; try(split); assumption.
    }
    destruct Hblocks0 as (HstartChilds0 & HendChilds0 & HPFlagChilds0).
    specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
      HstartChilds0 HendChilds0 HPFlagChilds0).
    destruct Hcons0 as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & HendParent &
      Hbounds)]]]. exists blockParent. exists startParent. exists endParent. split. assumption.
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBlockP. subst blockParent. rewrite HlookupCurrs0 in *.
      exfalso; congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock blockParent) eqn:HbeqBlocks.
    - rewrite HnewBEntry. simpl. rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent.
      rewrite HlookupBlocks0 in *. intuition.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      assert(HbeqStartBlockP: newPDBlockStartAddr <> blockParent).
      {
        intro Hcontra. subst blockParent. rewrite HremovedAddr in *. congruence.
      }
      rewrite HlookupEqs2s0; try(assumption). intuition.
    (* END blockInChildHasAtLeastEquivalentBlockInParent *)
  }
  assert(HparentsListCons: forall parentsList part, beqAddr newPDBlockStartAddr part = false
          -> isParentsList s parentsList part
          -> isParentsList s0 parentsList part).
  {
    intros parentsList part HbeqStartPart HparentsList.
    assert(HnewNotInList: ~ In newPDBlockStartAddr parentsList).
    {
      intro Hcontra. assert(HnewIsPart: In newPDBlockStartAddr (getPartitions multiplexer s)).
      { revert HparentsList Hcontra. apply partInParentsListIsPartition. assumption. }
      rewrite HgetPartsEq in HnewIsPart. congruence.
    }
    assert(HpartIsPDT: isParentsList s0 parentsList part \/ isPDT part s).
    {
      destruct parentsList.
      - simpl. left. trivial.
      - right. simpl in *. destruct (lookup p (memory s) beqAddr); try(exfalso; congruence). unfold isPDT.
        destruct v; try(exfalso; congruence). destruct HparentsList as (_ & Hres & _).
        destruct Hres as [pdentryPart (Hlookup & _)]. rewrite Hlookup. trivial.
    }
    destruct HpartIsPDT as [Hres | HpartIsPDT]; try(assumption).
    assert(HpartIsPDTs3: isPDT part s3).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *. destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs3. trivial.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym); assumption.
    }
    assert(HparentsLists3: isParentsList s3 parentsList part).
    {
      revert HparentsList. rewrite Hs. apply isParentsListEqPDTSameParent with currentPart newPDCurr.
      reflexivity.
      - rewrite <-Hs. unfold isPDT in *.
        destruct (lookup part (memory s3) beqAddr) eqn:HlookupParts3; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (lookup part (memory s) beqAddr) eqn:HlookupParts; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists p. exists p0. exists pdentry. split. reflexivity. split.
        reflexivity. split. assumption. simpl. split. reflexivity. split.
        + rewrite Hs in HlookupParts. simpl in *. intro HbeqCurrPart. rewrite beqAddrFalse in HbeqCurrPart.
          rewrite beqAddrSym in HlookupParts. rewrite HbeqCurrPart in HlookupParts. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in HlookupParts; try(assumption). rewrite HlookupParts in *.
          injection HlookupParts3 as HpdentriesEq. assumption.
        + intro Heq. subst part. rewrite Hs in HlookupParts. simpl in *. rewrite beqAddrTrue in HlookupParts.
          injection HlookupParts as HpdentriesEq. subst p0. split. reflexivity. rewrite HlookupCurrs3 in *.
          injection HlookupParts3 as HpdentriesEq. subst p. reflexivity.
      - assumption.
    }
    assert(HparentsLists2: isParentsList s2 parentsList part).
    {
      revert HparentsLists3. rewrite Hs3. apply isParentsListEqBERev with bentry; try(assumption).
      unfold isPDT in HpartIsPDTs3. rewrite Hs3 in HpartIsPDTs3. simpl in *.
      destruct (beqAddr idBlock part) eqn:HbeqBlockPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDTs3; try(apply not_eq_sym; assumption).
      destruct (lookup part (memory s2) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      exists p. reflexivity.
    }
    assert(HparentsLists1: isParentsList s1 parentsList part).
    {
      revert HparentsLists2. rewrite Hs2. apply isParentsListEqPDTExternalPart with newPDBlockStartAddr
        newPDEntry; try(assumption); reflexivity.
    }
    revert HparentsLists1. rewrite Hs1. apply isParentsListEqPDTExternalPart with newPDBlockStartAddr
        {|
         structure := nullAddr;
         firstfreeslot := nullAddr;
         nbfreeslots := zero;
         nbprepare := zero;
         parent := nullAddr;
         MPU := [];
         vidtAddr := nullAddr
       |}; try(assumption); reflexivity.
  }
  assert(partitionTreeIsTree s).
  { (* BEGIN partitionTreeIsTree s *)
    assert(Hcons0: partitionTreeIsTree s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
    rewrite HgetPartsEq in HchildIsPart.
    assert(HparentIsParents3: pdentryParent child pdparent s3).
    {
      unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in *.
      destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. rewrite HlookupCurrs3. simpl in *.
        assumption.
      - rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HparentIsParent; try(apply not_eq_sym); assumption.
    }
    assert(HparentIsParents0: pdentryParent child pdparent s0).
    {
      unfold pdentryParent in *. rewrite Hs3 in HparentIsParents3. simpl in *.
      destruct (beqAddr idBlock child) eqn:HbeqBlockChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HparentIsParents3; try(apply not_eq_sym; assumption).
      assert(HbeqStartChild: newPDBlockStartAddr <> child).
      {
        intro Hcontra. subst child. congruence.
      }
      rewrite <-HlookupEqs2s0; assumption.
    }
    assert(HparentsLists0: isParentsList s0 parentsList pdparent).
    {
      apply HparentsListCons; try(assumption). rewrite <-beqAddrFalse.
      assert(HparentOfPart: parentOfPartitionIsPartition s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold pdentryParent in HparentIsParents0.
      destruct (lookup child (memory s0) beqAddr) eqn:HlookupChilds0; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChilds0).
      destruct HparentOfPart as (HparentIsPart & _ & HbeqParentChild).
      specialize(HparentIsPart HbeqChildRoot). rewrite <-HparentIsParents0 in *.
      destruct HparentIsPart as (_ & HparentIsPart). intro Hcontra. rewrite <-Hcontra in *. congruence.
    }
    specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParents0 HparentsLists0).
    assumption.
    (* END partitionTreeIsTree *)
  }
  assert(kernelEntriesAreValid s).
  { (* BEGIN kernelEntriesAreValid s *)
    assert(Hcons0: kernelEntriesAreValid s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros kernel idx HkernIsKS Hindex.
    assert(HkernIsKSs0: isKS kernel s0).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs3 in HkernIsKS. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock kernel) eqn:HbeqBlockKern.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        assert(HbeqStartKern: newPDBlockStartAddr <> kernel).
        {
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite HlookupEqs2s0 in HkernIsKS; assumption.
    }
    specialize(Hcons0 kernel idx HkernIsKSs0 Hindex). unfold isBE in *. rewrite Hs. rewrite Hs3.
     simpl. destruct (beqAddr currentPart (CPaddr (kernel + idx))) eqn:HbeqCurrKernIdx.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrKernIdx. rewrite <-HbeqCurrKernIdx in *. rewrite HlookupCurrs0 in *.
      congruence.
    }
    rewrite HbeqBlockCurr. simpl.
    destruct (beqAddr idBlock (CPaddr (kernel + idx))) eqn:HbeqBlockKernIdx; trivial.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
    intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END kernelEntriesAreValid *)
  }
  assert(nextKernelIsValid s).
  { (* BEGIN nextKernelIsValid s *)
    assert(Hcons0: nextKernelIsValid s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros kernel HkernIsKS.
    assert(HkernIsKSs0: isKS kernel s0).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs3 in HkernIsKS. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock kernel) eqn:HbeqBlockKern.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        assert(HbeqStartKern: newPDBlockStartAddr <> kernel).
        {
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite HlookupEqs2s0 in HkernIsKS; assumption.
    }
    specialize(Hcons0 kernel HkernIsKSs0).
    destruct Hcons0 as (HnewtBounded & [nextAddr (HlookupNext & HnextIsKS)]). split. assumption. exists nextAddr.
    split.
    - intro Hp. specialize(HlookupNext Hp). rewrite Hs. rewrite Hs3. simpl.
      destruct (beqAddr currentPart {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqCurrNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite <-HbeqCurrNext in *. congruence.
      }
      rewrite HbeqBlockCurr. simpl.
      destruct (beqAddr idBlock {| p := kernel + nextoffset; Hp := Hp |}) eqn:HbeqBlockNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite <-HbeqBlockNext in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      assert(HbeqStartNext: newPDBlockStartAddr <> {| p := kernel + nextoffset; Hp := Hp |}).
      { intro Hcontra. rewrite <-Hcontra in *. congruence. }
      rewrite HlookupEqs2s0; assumption.
    - destruct HnextIsKS as [HnextIsKS | HnextIsNull]; try(right; assumption). left. unfold isKS in *.
      rewrite Hs. rewrite Hs3. simpl. destruct (beqAddr currentPart nextAddr) eqn:HbeqCurrNext.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrNext. rewrite <-HbeqCurrNext in *. rewrite HlookupCurrs0 in *.
        congruence.
      }
      rewrite HbeqBlockCurr. simpl.
      destruct (beqAddr idBlock nextAddr) eqn:HbeqBlockNext.
      + rewrite <-DTL.beqAddrTrue in HbeqBlockNext. subst nextAddr. rewrite HnewBEntry. simpl.
        rewrite HlookupBlocks0 in *. assumption.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
    (* END nextKernelIsValid *)
  }
  assert(noDupListOfKerns s).
  { (* BEGIN noDupListOfKerns s *)
    assert(Hcons0: noDupListOfKerns s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition kernList HkernList. destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold isListOfKernels in *.
      destruct kernList; try(apply NoDup_nil). exfalso.
      destruct HkernList as [newPDEntryBis (HlookupNewPDsBis & HstructNotNull & _)].
      rewrite HlookupNewPDsBis in *. injection HlookupNewPDs as HpdentriesEq. subst newPDEntryBis.
      rewrite HnewPD in *. simpl in *. congruence.
    }
    assert(HkernLists0: isListOfKernels kernList partition s0).
    { apply HisListOfKernelsEq; assumption. }
    specialize(Hcons0 partition kernList HkernLists0). assumption.
    (* END noDupListOfKerns *)
  }
  assert(MPUsizeIsBelowMax s).
  { (* BEGIN MPUsizeIsBelowMax s *)
    assert(Hcons0: MPUsizeIsBelowMax s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition MPUlist HMPUPart.
    destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    - rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold pdentryMPU in HMPUPart.
      rewrite HlookupNewPDs in HMPUPart. rewrite HnewPD in HMPUPart. simpl in *. subst MPUlist. simpl. lia.
    - destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      + rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition.
        assert(HMPUParts0: pdentryMPU currentPart realMPU s0).
        {
          unfold pdentryMPU in *. rewrite HlookupCurrs3 in *. rewrite HlookupCurrs0. assumption.
        }
        specialize(Hcons0 currentPart realMPU HMPUParts0). unfold pdentryMPU in *. rewrite HlookupCurrs in *.
        simpl in HMPUPart. pose proof (removeBlockFromPhysicalMPUAuxLenEq blockInCurrentPartitionAddr realMPU).
        subst MPUlist. lia.
      + assert(HMPUParts0: pdentryMPU partition MPUlist s0).
        {
          unfold pdentryMPU in *. rewrite Hs in HMPUPart. rewrite Hs3 in HMPUPart. simpl in *.
          rewrite HbeqCurrPart in *. rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HMPUPart; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HMPUPart; try(apply not_eq_sym; assumption).
          rewrite <-HlookupEqs2s0; assumption.
        }
        specialize(Hcons0 partition MPUlist HMPUParts0). assumption.
    (* END MPUsizeIsBelowMax *)
  }
  assert(originIsParentBlocksStart s).
  { (* BEGIN originIsParentBlocksStart s *)
    assert(Hcons0: originIsParentBlocksStart s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMappedPart Hsce
      Horigin. rewrite HgetPartsEq in HpartIsPart.
    destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    { rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. congruence. }
    assert(HpartIsPDT: isPDT partition s).
    { rewrite <-HgetPartsEq in HpartIsPart. apply partitionsArePDT; assumption. }
    rewrite HgetMappedBlocksEq in HblockMappedPart; try(assumption).
    assert(Horigins0: scentryOrigin scentryaddr scorigin s0).
    {
      unfold scentryOrigin in *. rewrite Hs in Horigin. rewrite Hs3 in Horigin. simpl in *.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *.
      destruct (beqAddr idBlock scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Horigin; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Horigin; try(apply not_eq_sym; assumption).
      rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *.
      congruence.
    }
    assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
                            /\ parent pdentryParts0 = parent pdentryPart).
    {
      rewrite Hs in HlookupPart. rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. exists pdentry. split. assumption.
        injection HlookupPart as HpdentriesEq. subst pdentryPart. simpl. reflexivity.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite HlookupEqs2s0 in HlookupPart; try(assumption). exists pdentryPart. split. assumption. reflexivity.
    }
    destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentsEq)].
    specialize(Hcons0 partition pdentryParts0 block scentryaddr scorigin HpartIsPart HlookupParts0
      HblockMappedPart Hsce Horigins0). destruct Hcons0 as (HblockParent & HstartAbove).
    assert(HlookupBlocksEq: forall blockBis, beqAddr idBlock blockBis = false
            -> isBE blockBis s
            -> lookup blockBis (memory s) beqAddr = lookup blockBis (memory s0) beqAddr).
    {
      intros blockBis HbeqBlocks HblockIsBE. unfold isBE in HblockIsBE. rewrite Hs. rewrite Hs3.
      rewrite Hs in HblockIsBE. rewrite Hs3 in HblockIsBE. simpl in *.
      destruct (beqAddr currentPart blockBis) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(reflexivity).
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      intro Hcontra. subst blockBis. rewrite HlookupNewPDs2 in *. congruence.
    }
    assert(HblockIsBE: isBE block s).
    {
      rewrite <-HgetMappedBlocksEq in HblockMappedPart; try(assumption).
      apply mappedBlockIsBE in HblockMappedPart. destruct HblockMappedPart as [bentryBlock (HlookupBlock & _)].
      unfold isBE. rewrite HlookupBlock. trivial.
    }
    rewrite <-HparentsEq in *. split.
    - intro HbeqPartRoot. specialize(HblockParent HbeqPartRoot).
      destruct HblockParent as [blockParent (HblockParentMapped & HstartParent & Hincl)]. exists blockParent.
      destruct (beqAddr newPDBlockStartAddr (parent pdentryParts0)) eqn:HbeqStartParent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqStartParent. rewrite <-HbeqStartParent in *. unfold getMappedBlocks in *.
        unfold getKSEntries in *. rewrite HremovedAddr in *. simpl in HblockParentMapped. exfalso; congruence.
      }
      assert(HparentIsPDT: isPDT (parent pdentryParts0) s).
      {
        assert(HparentOfPart: parentOfPartitionIsPartition s) by assumption.
        specialize(HparentOfPart partition pdentryPart HlookupPart).
        destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & _). unfold isPDT. rewrite HparentsEq.
        rewrite HlookupParent. trivial.
      }
      assert(HblockPIsBE: isBE blockParent s).
      {
        rewrite <-HgetMappedBlocksEq in HblockParentMapped; try(assumption).
        apply mappedBlockIsBE in HblockParentMapped.
        destruct HblockParentMapped as [bentryBlock (HlookupBlock & _)].
        unfold isBE. rewrite HlookupBlock. trivial.
      }
      rewrite HgetMappedBlocksEq; try(assumption). split. assumption.
      destruct (beqAddr idBlock blockParent) eqn:HbeqBlockBlockP.
      + rewrite <-DTL.beqAddrTrue in HbeqBlockBlockP. subst blockParent. unfold bentryStartAddr in *. simpl.
        rewrite HlookupBlocks. rewrite HlookupBlocks0 in *. rewrite HnewBEntry. simpl. split. assumption.
        destruct (beqAddr idBlock block) eqn:HbeqBlocks.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks. rewrite HnewBEntry. simpl.
          intuition.
        }
        rewrite HlookupBlocksEq; try(assumption). simpl in Hincl. rewrite HlookupBlocks0 in *. assumption.
      + unfold bentryStartAddr. simpl. rewrite HlookupBlocksEq; try(assumption). split. assumption.
        destruct (beqAddr idBlock block) eqn:HbeqBlocks.
        * rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks. rewrite HnewBEntry.
          simpl in *. rewrite HlookupBlocks0 in *. intuition.
        * rewrite HlookupBlocksEq; assumption.
    - destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold bentryStartAddr in *. rewrite HlookupBlocks.
        rewrite HnewBEntry. simpl. rewrite HlookupBlocks0 in *. assumption.
      + unfold bentryStartAddr. rewrite HlookupBlocksEq; assumption.
    (* END originIsParentBlocksStart *)
  }
  assert(HlookupBlocksEq: forall blockBis, beqAddr idBlock blockBis = false
          -> isBE blockBis s
          -> lookup blockBis (memory s) beqAddr = lookup blockBis (memory s0) beqAddr).
  {
    intros blockBis HbeqBlocks HblockIsBE. unfold isBE in HblockIsBE. rewrite Hs. rewrite Hs3.
    rewrite Hs in HblockIsBE. rewrite Hs3 in HblockIsBE. simpl in *.
    destruct (beqAddr currentPart blockBis) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
    rewrite HbeqBlockCurr in *. simpl in *. rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(reflexivity).
    rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
    intro Hcontra. subst blockBis. rewrite HlookupNewPDs2 in *. congruence.
  }
  assert(nextImpliesBlockWasCut s).
  { (* BEGIN nextImpliesBlockWasCut s *)
    assert(Hcons0: nextImpliesBlockWasCut s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMappedPart
      Hend Hsce HbeqNextNull Hnext HbeqPartRoot.
    destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. exfalso; congruence.
    }
    assert(HpartIsPDT: isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial).
    rewrite HgetMappedBlocksEq in HblockMappedPart; try(assumption). rewrite HgetPartsEq in HpartIsPart.
    assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
                            /\ parent pdentryParts0 = parent pdentryPart).
    {
      rewrite Hs in HlookupPart. rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. exists pdentry. split. assumption.
        injection HlookupPart as HpdentriesEq. subst pdentryPart. simpl. reflexivity.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock partition) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite HlookupEqs2s0 in HlookupPart; try(assumption). exists pdentryPart. split. assumption. reflexivity.
    }
    destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentsEq)].
    assert(Hnexts0: scentryNext scentryaddr scnext s0).
    {
      unfold scentryNext in *. rewrite Hs in Hnext. rewrite Hs3 in Hnext. simpl in *.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *.
      destruct (beqAddr idBlock scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hnext; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hnext; try(apply not_eq_sym; assumption).
      rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *.
      congruence.
    }
    assert(HparentOfPart: parentOfPartitionIsPartition s) by assumption.
    specialize(HparentOfPart partition pdentryPart HlookupPart).
    destruct HparentOfPart as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
    destruct (beqAddr newPDBlockStartAddr (parent pdentryPart)) eqn:HbeqStartParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartParent. rewrite HbeqStartParent in *. exfalso; congruence.
    }
    assert(HblockIsBE: isBE block s).
    {
      rewrite <-HgetMappedBlocksEq in HblockMappedPart; try(assumption).
      apply mappedBlockIsBE in HblockMappedPart. destruct HblockMappedPart as [bentryBlock (HlookupBlock & _)].
      unfold isBE. rewrite HlookupBlock. trivial.
    }
    destruct (beqAddr idBlock block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold bentryEndAddr in Hend.
      rewrite HlookupBlocks in *. rewrite HnewBEntry in Hend. simpl in *. rewrite HlookupBlocks.
      rewrite HnewBEntry. simpl. specialize(Hcons0 partition pdentryParts0 idBlock scentryaddr scnext
        newPDBlockEndAddr HpartIsPart HlookupParts0 HblockMappedPart HendBlock Hsce HbeqNextNull Hnexts0
        HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & HendBounded & Hincl)]].
      exists blockParent. exists endParent. rewrite HparentsEq in *.
      assert(HparentIsPDT: isPDT (parent pdentryPart) s) by (unfold isPDT; rewrite HlookupParent; trivial).
      assert(HblockPIsBE: isBE blockParent s).
      {
        rewrite <-HgetMappedBlocksEq in HblockParentMapped; try(assumption).
        apply mappedBlockIsBE in HblockParentMapped.
        destruct HblockParentMapped as [bentryBlock (HlookupBlock & _)].
        unfold isBE. rewrite HlookupBlock. trivial.
      }
      rewrite HgetMappedBlocksEq; try(assumption). split. assumption.
      assert(HbeqCurrPart: currentPart = partition).
      {
        destruct(beqAddr currentPart partition) eqn:HbeqCurrPart; try(rewrite DTL.beqAddrTrue; assumption).
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HpartIsPDTs0: isPDT partition s0) by (unfold isPDT; rewrite HlookupParts0; trivial).
        exfalso. rewrite <-beqAddrFalse in HbeqCurrPart.
        specialize(Hdisjoint currentPart partition HcurrIsPDTs0 HpartIsPDTs0 HbeqCurrPart).
        unfold getMappedBlocks in *. destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]].
        subst list1. subst list2. apply InFilterPresentInList in HblockMappedPart.
        apply InFilterPresentInList in HblockMapped. specialize(Hdisjoint idBlock HblockMapped). congruence.
      }
      subst partition.
      destruct (beqAddr idBlock blockParent) eqn:HbeqBlockBlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlockP. subst blockParent. exfalso.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HparentIsPDTs0: isPDT (parent pdentryPart) s0).
        {
          rewrite HgetPartsEq in *. apply partitionsArePDT; try(assumption);
            unfold consistency in *; unfold consistency1 in *; intuition.
        }
        specialize(Hdisjoint (parent pdentryPart) currentPart HparentIsPDTs0 HcurrIsPDTs0 HbeqParentPart).
        unfold getMappedBlocks in *. destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]].
        subst list1. subst list2. apply InFilterPresentInList in HblockParentMapped.
        apply InFilterPresentInList in HblockMapped. specialize(Hdisjoint idBlock HblockParentMapped). congruence.
      }
      assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
      { apply HlookupBlocksEq; assumption. }
      unfold bentryEndAddr in *. rewrite HlookupBlockPEq. rewrite HlookupBlocks0 in HendBlock.
      rewrite <-HendBlock in Hend. subst endaddr. split. assumption. split. assumption. simpl in *.
      rewrite HlookupBlocks0 in *. assumption.
    - assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
      { apply HlookupBlocksEq; assumption. }
      unfold bentryEndAddr in Hend. rewrite HlookupBlockEq in Hend.
      specialize(Hcons0 partition pdentryParts0 block scentryaddr scnext endaddr HpartIsPart HlookupParts0
        HblockMappedPart Hend Hsce HbeqNextNull Hnexts0 HbeqPartRoot).
      destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & HendBounded & Hincl)]].
      exists blockParent. exists endParent. rewrite HparentsEq in *.
      assert(HparentIsPDT: isPDT (parent pdentryPart) s) by (unfold isPDT; rewrite HlookupParent; trivial).
      assert(HblockPIsBE: isBE blockParent s).
      {
        rewrite <-HgetMappedBlocksEq in HblockParentMapped; try(assumption).
        apply mappedBlockIsBE in HblockParentMapped.
        destruct HblockParentMapped as [bentryBlock (HlookupBlock & _)].
        unfold isBE. rewrite HlookupBlock. trivial.
      }
      rewrite HgetMappedBlocksEq; try(assumption). split. assumption. simpl in *. rewrite HlookupBlockEq.
      destruct (beqAddr idBlock blockParent) eqn:HbeqBlockBlockP.
      + rewrite <-DTL.beqAddrTrue in HbeqBlockBlockP. subst blockParent. unfold bentryEndAddr in *.
        rewrite HlookupBlocks. rewrite HnewBEntry. simpl. rewrite HlookupBlocks0 in *. split. assumption. split;
          assumption.
      + assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
        { apply HlookupBlocksEq; assumption. }
        unfold bentryEndAddr. rewrite HlookupBlockPEq. split. assumption. split; assumption.
    (* END nextImpliesBlockWasCut *)
  }
  assert(HcurrIsPart: In currentPart (getPartitions multiplexer s0)).
  {
    assert(HcurrIsPart: currentPartitionInPartitionsList s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold currentPartitionInPartitionsList in *. subst currentPart. assumption.
  }
  assert(blocksAddressesTypes s).
  { (* BEGIN blocksAddressesTypes s *)
    assert(Hcons0: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block startaddr endaddr Hstart Hend HPDchild.
    assert(Hblock: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
    {
      destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold bentryStartAddr in *.
        unfold bentryEndAddr in *. rewrite HlookupBlocks in *. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. split; assumption.
      - unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        assert(isBE block s).
        {
          unfold isBE. unfold bentryStartAddr in *. destruct (lookup block (memory s) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
        }
        rewrite HlookupBlocksEq in Hstart; try(assumption). rewrite HlookupBlocksEq in Hend; try(assumption).
        split; assumption.
    }
    assert(HPDchilds0: sh1entryPDchild (CPaddr (block + sh1offset)) nullAddr s0).
    {
      unfold sh1entryPDchild in *. rewrite Hs in HPDchild. rewrite Hs3 in HPDchild. simpl in *.
      destruct (beqAddr currentPart (CPaddr (block + sh1offset))) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite HbeqBlockCurr in HPDchild. simpl in *.
      destruct (beqAddr idBlock (CPaddr (block + sh1offset))) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym; assumption).
      assert(HbeqStartSh1: newPDBlockStartAddr <> CPaddr (block + sh1offset)).
      {
        intro Hcontra. rewrite <-Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
      }
      rewrite HlookupEqs2s0 in HPDchild; assumption.
    }
    destruct Hblock as (Hstarts0 & Hends0). specialize(Hcons0 block startaddr endaddr Hstarts0 Hends0 HPDchilds0).
    destruct Hcons0 as [(HKS & HotherAddr) | [(HPDT & HotherAddr) | Hnull]].
    - left. split.
      + unfold isKS in *. rewrite Hs. rewrite Hs3. simpl.
        destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStartBis.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrStartBis. subst startaddr. rewrite HlookupCurrs0 in *. congruence.
        }
        rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock startaddr) eqn:HbeqBlockStartBis.
        * rewrite <-DTL.beqAddrTrue in HbeqBlockStartBis. subst startaddr. rewrite HnewBEntry. simpl.
          rewrite HlookupBlocks0 in *. assumption.
        * rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          assert(newPDBlockStartAddr <> startaddr).
          { intro Hcontra. subst startaddr. rewrite HremovedAddr in *. exfalso; congruence. }
          rewrite HlookupEqs2s0; assumption.
      + intros addr HaddrInRange. specialize(HotherAddr addr HaddrInRange).
        destruct HotherAddr as [HBE | [HSHE | HSCE]].
        * left. unfold isBE in *. rewrite Hs. rewrite Hs3. simpl.
          destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs0 in *. congruence.
          }
          rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock addr) eqn:HbeqBlockAddr; trivial.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          assert(newPDBlockStartAddr <> addr).
          { intro Hcontra. subst addr. rewrite HremovedAddr in *. exfalso; congruence. }
          rewrite HlookupEqs2s0; assumption.
        * right. left. unfold isSHE in *. rewrite Hs. rewrite Hs3. simpl.
          destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs0 in *. congruence.
          }
          rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock addr) eqn:HbeqBlockAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          assert(newPDBlockStartAddr <> addr).
          { intro Hcontra. subst addr. rewrite HremovedAddr in *. exfalso; congruence. }
          rewrite HlookupEqs2s0; assumption.
        * right. right. unfold isSCE in *. rewrite Hs. rewrite Hs3. simpl.
          destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. rewrite HlookupCurrs0 in *. congruence.
          }
          rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock addr) eqn:HbeqBlockAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. rewrite HlookupBlocks0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          assert(newPDBlockStartAddr <> addr).
          { intro Hcontra. subst addr. rewrite HremovedAddr in *. exfalso; congruence. }
          rewrite HlookupEqs2s0; assumption.
    - right. left. split.
      + unfold isPDT in *. rewrite Hs. rewrite Hs3. simpl.
        destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStartBis; trivial.
        rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock startaddr) eqn:HbeqBlockStartBis.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockStartBis. subst startaddr. rewrite HlookupBlocks0 in *.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        assert(newPDBlockStartAddr <> startaddr).
        { intro Hcontra. subst startaddr. rewrite HremovedAddr in *. exfalso; congruence. }
        rewrite HlookupEqs2s0; assumption.
      + intros addr HaddrInRange. specialize(HotherAddr addr HaddrInRange).
        destruct HaddrInRange as (HaddrInRange & HbeqAddrStart).
        rewrite Hs. rewrite Hs3. simpl.
        destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. congruence.
        }
        rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock addr) eqn:HbeqBlockAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (beqAddr newPDBlockStartAddr addr) eqn:HbeqStartAddr.
        * rewrite <-DTL.beqAddrTrue in HbeqStartAddr. subst addr. exfalso.
          assert(HblocksPart: exists part, In part (getPartitions multiplexer s0)
                                          /\ In block (getMappedBlocks part s0)).
          {
            assert(Hres: blockBelongsToAPart s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HblockIsBE: isBE block s0).
            {
              unfold bentryStartAddr in *. unfold isBE. destruct (lookup block (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence). trivial.
            }
            specialize(Hres block HblockIsBE). assumption.
          }
          destruct HblocksPart as [part (HpartIsPart & HblockBisMapped)].
          assert(In newPDBlockStartAddr (getAllPaddrAux [block] s0)).
          {
            simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-Hstarts0. rewrite <-Hends0. rewrite app_nil_r.
            assumption.
          }
          assert(HstartInBlock: In newPDBlockStartAddr (getAllPaddrAux [idBlock] s0)).
          {
            simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *.
            rewrite <-HstartBlock. rewrite <-HendBlock. rewrite app_nil_r. assumption.
          }
          assert(In newPDBlockStartAddr (getMappedPaddr currentPart s0)).
          { apply addrInBlockIsMapped with idBlock; assumption. }
          assert(HpartIsDesc: In currentPart (part::(filterOptionPaddr (completeParentsList part s0)))).
          {
            unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *.
            apply addressesBloodlineIfNotShared with newPDBlockStartAddr block; try(assumption); intuition.
          }
          assert(In newPDBlockStartAddr (getMappedPaddr part s0)).
          { apply addrInBlockIsMapped with block; assumption. }
          destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchildBlock & Hsh1)]].
          unfold sh1entryAddr in *. rewrite HlookupBlocks0 in *. subst sh1entryaddr.
          assert(HpartIsAnc: In part (currentPart::(filterOptionPaddr (completeParentsList currentPart s0)))).
          {
            unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *.
            apply addressesBloodlineIfNotShared with newPDBlockStartAddr idBlock; try(assumption); intuition.
          }
          destruct (beqAddr part currentPart) eqn:HbeqPartCurr.
          -- rewrite <-DTL.beqAddrTrue in HbeqPartCurr. subst part.
             assert(HbeqBlocks: block = idBlock).
             {
               destruct (beqAddr block idBlock) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption).
               rewrite <-beqAddrFalse in HbeqBlocks. exfalso.
               assert(HnoDupPaddr: noDupUsedPaddrList s0)
                 by (unfold consistency in *; unfold consistency2 in *; intuition).
               apply not_eq_sym in HbeqBlocks.
               pose proof (DisjointPaddrInPart currentPart idBlock block newPDBlockStartAddr s0 HnoDupPaddr
                 HcurrIsPDTs0 HblockMapped HblockBisMapped HbeqBlocks HstartInBlock). congruence.
             }
             subst block. unfold bentryStartAddr in *. rewrite HlookupBlocks0 in *. rewrite <-Hstarts0 in *.
             rewrite HstartBlock in *. congruence.
          -- rewrite <-beqAddrFalse in *.
             destruct HpartIsDesc as [Hcontra | HpartIsDescStrict]; try(exfalso; congruence).
             destruct HpartIsAnc as [Hcontra | HpartIsAncStrict]; try(exfalso; congruence).
             contradict HpartIsAncStrict. apply completeParentsListOrientation; try(assumption).
             unfold consistency in *; unfold consistency1 in *; intuition.
             unfold consistency in *; unfold consistency1 in *; intuition.
        * rewrite <-beqAddrFalse in *. rewrite HlookupEqs2s0; assumption.
    - right. destruct (beqAddr newPDBlockStartAddr startaddr) eqn:HbeqStartStartaddr.
      + left. rewrite <-DTL.beqAddrTrue in HbeqStartStartaddr. subst startaddr. split.
        * unfold isPDT. rewrite HlookupNewPDs. trivial.
        * intros addr (HaddrInRange & HbeqAddrStart). specialize(Hnull addr HaddrInRange).
          rewrite Hs. rewrite Hs3. simpl.
          destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. congruence.
          }
          rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock addr) eqn:HbeqBlockAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). apply not_eq_sym in HbeqAddrStart.
          rewrite HlookupEqs2s0; assumption.
      + right. rewrite <-beqAddrFalse in HbeqStartStartaddr. intros addr HaddrInRange.
        specialize(Hnull addr HaddrInRange). rewrite Hs. rewrite Hs3. simpl.
        destruct (beqAddr currentPart addr) eqn:HbeqCurrAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrAddr. subst addr. congruence.
        }
        rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock addr) eqn:HbeqBlockAddr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. subst addr. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        destruct (beqAddr newPDBlockStartAddr addr) eqn:HbeqStartAddr.
        * rewrite <-DTL.beqAddrTrue in HbeqStartAddr. subst addr. exfalso.
          assert(HblocksPart: exists part, In part (getPartitions multiplexer s0)
                                          /\ In block (getMappedBlocks part s0)).
          {
            assert(Hres: blockBelongsToAPart s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
            assert(HblockIsBE: isBE block s0).
            {
              unfold bentryStartAddr in *. unfold isBE. destruct (lookup block (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence). trivial.
            }
            specialize(Hres block HblockIsBE). assumption.
          }
          destruct HblocksPart as [part (HpartIsPart & HblockBisMapped)].
          assert(In newPDBlockStartAddr (getAllPaddrAux [block] s0)).
          {
            simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-Hstarts0. rewrite <-Hends0. rewrite app_nil_r.
            assumption.
          }
          assert(HstartInBlock: In newPDBlockStartAddr (getAllPaddrAux [idBlock] s0)).
          {
            simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *.
            rewrite <-HstartBlock. rewrite <-HendBlock. rewrite app_nil_r. assumption.
          }
          assert(In newPDBlockStartAddr (getMappedPaddr currentPart s0)).
          { apply addrInBlockIsMapped with idBlock; assumption. }
          assert(HpartIsDesc: In currentPart (part::(filterOptionPaddr (completeParentsList part s0)))).
          {
            unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *.
            apply addressesBloodlineIfNotShared with newPDBlockStartAddr block; try(assumption); intuition.
          }
          assert(In newPDBlockStartAddr (getMappedPaddr part s0)).
          { apply addrInBlockIsMapped with block; assumption. }
          destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchildBlock & Hsh1)]].
          unfold sh1entryAddr in *. rewrite HlookupBlocks0 in *. subst sh1entryaddr.
          assert(HpartIsAnc: In part (currentPart::(filterOptionPaddr (completeParentsList currentPart s0)))).
          {
            unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *.
            apply addressesBloodlineIfNotShared with newPDBlockStartAddr idBlock; try(assumption); intuition.
          }
          destruct (beqAddr part currentPart) eqn:HbeqPartCurr.
          -- rewrite <-DTL.beqAddrTrue in HbeqPartCurr. subst part.
             assert(HbeqBlocks: block = idBlock).
             {
               destruct (beqAddr block idBlock) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption).
               rewrite <-beqAddrFalse in HbeqBlocks. exfalso.
               assert(HnoDupPaddr: noDupUsedPaddrList s0)
                 by (unfold consistency in *; unfold consistency2 in *; intuition).
               apply not_eq_sym in HbeqBlocks.
               pose proof (DisjointPaddrInPart currentPart idBlock block newPDBlockStartAddr s0 HnoDupPaddr
                 HcurrIsPDTs0 HblockMapped HblockBisMapped HbeqBlocks HstartInBlock). congruence.
             }
             subst block. unfold bentryStartAddr in *. rewrite HlookupBlocks0 in *. rewrite <-Hstarts0 in *.
             rewrite HstartBlock in *. congruence.
          -- rewrite <-beqAddrFalse in *.
             destruct HpartIsDesc as [Hcontra | HpartIsDescStrict]; try(exfalso; congruence).
             destruct HpartIsAnc as [Hcontra | HpartIsAncStrict]; try(exfalso; congruence).
             contradict HpartIsAncStrict. apply completeParentsListOrientation; try(assumption).
             unfold consistency in *; unfold consistency1 in *; intuition.
             unfold consistency in *; unfold consistency1 in *; intuition.
        * rewrite <-beqAddrFalse in *. rewrite HlookupEqs2s0; assumption.
    (* END blocksAddressesTypes *)
  }
  (*assert(notPDTIfNotPDflag s).
  { (* BEGIN notPDTIfNotPDflag s *)
    assert(Hcons0: notPDTIfNotPDflag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block startaddr sh1entryaddr Hstart Hsh1Bis HPDflag.
    assert(Hblocks0: bentryStartAddr block startaddr s0 /\ sh1entryAddr block sh1entryaddr s0).
    {
      destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold bentryStartAddr in *.
        unfold sh1entryAddr in *. rewrite HlookupBlocks in *. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. split; assumption.
      - unfold bentryStartAddr in *. unfold sh1entryAddr in *.
        assert(isBE block s).
        {
          unfold isBE. unfold bentryStartAddr in *. destruct (lookup block (memory s) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
        }
        rewrite HlookupBlocksEq in Hstart; try(assumption). rewrite HlookupBlocksEq in Hsh1Bis; try(assumption).
        split; assumption.
    }
    destruct Hblocks0 as (Hstarts0 & Hsh1Biss0).
    assert(HPDflags0: sh1entryPDflag sh1entryaddr false s0).
    {
      unfold sh1entryPDflag in *. rewrite Hs in HPDflag. rewrite Hs3 in HPDflag. simpl in *.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite HbeqBlockCurr in HPDflag. simpl in *.
      destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HPDflag; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HPDflag; try(apply not_eq_sym; assumption).
      assert(HbeqStartSh1: newPDBlockStartAddr <> sh1entryaddr).
      {
        intro Hcontra. rewrite <-Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
      }
      rewrite HlookupEqs2s0 in HPDflag; assumption.
    }
    specialize(Hcons0 block startaddr sh1entryaddr Hstarts0 Hsh1Biss0 HPDflags0). (*TODO this prop is false*)
    (* END notPDTIfNotPDflag *)
  }*)
  assert(nextKernAddrIsInSameBlock s).
  { (* BEGIN nextKernAddrIsInSameBlock s *)
    assert(Hcons0: nextKernAddrIsInSameBlock s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block kernel startaddr endaddr Hstart Hend HkernIsKS.
    assert(Hblock: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
    {
      destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold bentryStartAddr in *.
        unfold bentryEndAddr in *. rewrite HlookupBlocks in *. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. split; assumption.
      - unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        assert(isBE block s).
        {
          unfold isBE. unfold bentryStartAddr in *. destruct (lookup block (memory s) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
        }
        rewrite HlookupBlocksEq in Hstart; try(assumption). rewrite HlookupBlocksEq in Hend; try(assumption).
        split; assumption.
    }
    destruct Hblock as (Hstarts0 & Hends0).
    assert(HkernIsKSs0: isKS kernel s0).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. rewrite Hs3 in HkernIsKS. simpl in *.
      destruct (beqAddr currentPart kernel) eqn:HbeqCurrKern; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock kernel) eqn:HbeqBlockKern.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
        assert(HbeqStartKern: newPDBlockStartAddr <> kernel).
        {
          intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence.
        }
        rewrite HlookupEqs2s0 in HkernIsKS; assumption.
    }
    specialize(Hcons0 block kernel startaddr endaddr Hstarts0 Hends0 HkernIsKSs0). assumption.
    (* END nextKernAddrIsInSameBlock *)
  }
  (*assert(consistency1 s) by (unfold consistency1; intuition).*)
  assert(noDupUsedPaddrList s).
  { (* BEGIN noDupUsedPaddrList s*)
    assert(Hcons0: noDupUsedPaddrList s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros part HpartIsPDT.
    destruct (beqAddr newPDBlockStartAddr part) eqn:HbeqStartPart.
    - rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst part. unfold getUsedPaddr. unfold getConfigPaddr.
      unfold getMappedPaddr. unfold getConfigBlocks. unfold getMappedBlocks. unfold getKSEntries.
      unfold getAllPaddrPDTAux. rewrite HlookupNewPDs. rewrite HnewPD. simpl. rewrite app_nil_r.
      rewrite app_nil_r.
      assert(HnoConfig: (filterOptionPaddr (getConfigBlocksAux (maxIdx + 1) nullAddr s (CIndex maxNbPrepare)))
                        = []).
      {
        rewrite MaxIdxNextEq. simpl. unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (beqAddr p nullAddr); try(simpl; reflexivity).
      }
      rewrite HnoConfig. rewrite app_nil_r. apply NoDupPaddrBlockAux.
    - assert(HpartIsPDTs0: isPDT part s0).
      {
        unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs3 in HpartIsPDT. simpl in *.
        destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. rewrite HlookupCurrs0. trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr idBlock part) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
          rewrite <-HlookupEqs2s0; assumption.
      }
      unfold getUsedPaddr. rewrite HgetConfigPaddrEq; try(assumption).
      rewrite HgetMappedPaddrEq; try(assumption). specialize(Hcons0 part HpartIsPDTs0). assumption.
    (* END noDupUsedPaddrList *)
  }

  assert(HgetAccessibleMappedPaddrEq: forall part, isPDT part s
                    -> isPDT part s0
                    -> beqAddr newPDBlockStartAddr part = false
                    -> part <> currentPart
                    -> getAccessibleMappedPaddr part s0 = getAccessibleMappedPaddr part s).
  {
    intros part HpartIsPDT HpartIsPDTs0 HbeqStartPart HbeqPartCurr. unfold getAccessibleMappedPaddr in *.
    unfold getAccessibleMappedBlocks in *. rewrite HgetMappedBlocksEq; try(assumption).
    assert(HpartIsPDTs0Copy: isPDT part s0) by assumption.
    unfold isPDT in HpartIsPDT. unfold isPDT in HpartIsPDTs0Copy.
    destruct (lookup part (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    destruct (lookup part (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). set(list := getMappedBlocks part s0).
    assert(HfiltAccEqs1s0: filterAccessible list s1 = filterAccessible list s0).
    {
      rewrite Hs1. apply filterAccessibleEqPDTNewPart. left. assumption.
    }
    assert(HfiltAccEqs2s1: filterAccessible list s2 = filterAccessible list s1).
    {
      rewrite Hs2. apply filterAccessibleEqPDT. unfold isPDT. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial.
    }
    assert(HfiltAccEqEqss3: filterAccessible list s = filterAccessible list s3).
    {
      rewrite Hs. apply filterAccessibleEqPDT. unfold isPDT. rewrite HlookupCurrs3. trivial.
    }
    fold list. rewrite HfiltAccEqEqss3. rewrite <-HfiltAccEqs1s0. rewrite <-HfiltAccEqs2s1.
    set(filtList := filterAccessible list s3).
    assert(HpaddrAuxEqss0: getAllPaddrAux filtList s = getAllPaddrAux filtList s0).
    {
      assert(HpaddrAuxEqs1s0: getAllPaddrAux filtList s1 = getAllPaddrAux filtList s0).
      {
        rewrite Hs1. apply getAllPaddrAuxEqPDTNewPart. assumption.
      }
      assert(HpaddrAuxEqs2s1: getAllPaddrAux filtList s2 = getAllPaddrAux filtList s1).
      {
        rewrite Hs2. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial.
      }
      assert(HpaddrAuxEqs3s2: getAllPaddrAux filtList s3 = getAllPaddrAux filtList s2).
      {
        rewrite Hs3. apply getAllPaddrAuxEqBEStartEndNoChange with bentry; try(assumption); rewrite HnewBEntry;
          simpl; reflexivity.
      }
      rewrite <-HpaddrAuxEqs1s0. rewrite <-HpaddrAuxEqs2s1. rewrite <-HpaddrAuxEqs3s2. rewrite Hs.
      apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupCurrs3. trivial.
    }
    subst filtList. rewrite HpaddrAuxEqss0. clear HfiltAccEqs1s0.  clear HfiltAccEqs2s1. clear HfiltAccEqEqss3.
    clear HpaddrAuxEqss0.
    assert(HblockNotInList: ~ In idBlock list).
    {
      subst list. intro Hcontra. unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMapped.
      apply InFilterPresentInList in Hcontra.
      assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      specialize(Hdisjoint part currentPart HpartIsPDTs0 HcurrIsPDTs0 HbeqPartCurr).
      destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
      specialize(Hdisjoint idBlock Hcontra). congruence.
    }
    assert(HfiltEqs3: filterAccessible list s3 = filterAccessible list s2).
    { rewrite Hs3. apply filterAccessibleEqBENotInListNoChange. assumption. }
    rewrite HfiltEqs3. reflexivity.
  }

  assert(HcurrIsPDT: isPDT currentPart s) by (unfold isPDT; rewrite HlookupCurrs; trivial).
  assert(HgetAccessibleMappedPaddrCurrEquiv: forall addr,
                    (In addr (getAccessibleMappedPaddr currentPart s0)
                        <-> In addr (getAllPaddrAux [idBlock] s ++ getAccessibleMappedPaddr currentPart s))).
  {
    intro addr. unfold getAccessibleMappedPaddr. unfold getAccessibleMappedBlocks. rewrite beqAddrFalse in *.
    rewrite HgetMappedBlocksEq; try(assumption). rewrite HlookupCurrs0. rewrite HlookupCurrs.
    set(list := getMappedBlocks currentPart s0).
    assert(HfiltAccEqs1s0: filterAccessible list s1 = filterAccessible list s0).
    {
      rewrite Hs1. apply filterAccessibleEqPDTNewPart. left. assumption.
    }
    assert(HfiltAccEqs2s1: filterAccessible list s2 = filterAccessible list s1).
    {
      rewrite Hs2. apply filterAccessibleEqPDT. unfold isPDT. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial.
    }
    assert(HfiltAccEqEqss3: filterAccessible list s = filterAccessible list s3).
    {
      rewrite Hs. apply filterAccessibleEqPDT. unfold isPDT. rewrite HlookupCurrs3. trivial.
    }
    fold list. rewrite HfiltAccEqEqss3. rewrite <-HfiltAccEqs1s0. rewrite <-HfiltAccEqs2s1.
    set(filtList := filterAccessible list s3).
    assert(HpaddrAuxEqss0: getAllPaddrAux filtList s = getAllPaddrAux filtList s0).
    {
      assert(HpaddrAuxEqs1s0: getAllPaddrAux filtList s1 = getAllPaddrAux filtList s0).
      {
        rewrite Hs1. apply getAllPaddrAuxEqPDTNewPart. assumption.
      }
      assert(HpaddrAuxEqs2s1: getAllPaddrAux filtList s2 = getAllPaddrAux filtList s1).
      {
        rewrite Hs2. apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite Hs1. simpl. rewrite beqAddrTrue. trivial.
      }
      assert(HpaddrAuxEqs3s2: getAllPaddrAux filtList s3 = getAllPaddrAux filtList s2).
      {
        rewrite Hs3. apply getAllPaddrAuxEqBEStartEndNoChange with bentry; try(assumption); rewrite HnewBEntry;
          simpl; reflexivity.
      }
      rewrite <-HpaddrAuxEqs1s0. rewrite <-HpaddrAuxEqs2s1. rewrite <-HpaddrAuxEqs3s2. rewrite Hs.
      apply getAllPaddrAuxEqPDT. unfold isPDT. rewrite HlookupCurrs3. trivial.
    }
    subst filtList. rewrite HpaddrAuxEqss0. simpl. rewrite HlookupBlocks. rewrite app_nil_r. clear HfiltAccEqs1s0.
    clear HfiltAccEqs2s1. clear HfiltAccEqEqss3. clear HpaddrAuxEqss0.
    assert(HblockInLists2: In idBlock (filterAccessible list s2)).
    {
      subst list. apply accessibleIsInFilterAccessible with bentry; try(assumption). unfold bentryAFlag in *.
      rewrite HlookupBlocks0 in *. apply eq_sym. assumption.
    }
    assert(HnoDupCurr: noDupMappedBlocksList s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HnoDupCurr currentPart HcurrIsPDTs0). fold list in HnoDupCurr.
    induction list; simpl in *; try(exfalso; congruence). rewrite Hs3. simpl. rewrite <-Hs3.
    apply NoDup_cons_iff in HnoDupCurr. destruct HnoDupCurr as (HblockNotInList & HnoDupCurrRec).
    destruct (beqAddr idBlock a4) eqn:HbeqBlockA.
    - assert(Hacc: accessible newBentry = false) by (rewrite HnewBEntry; simpl; reflexivity). rewrite Hacc.
      rewrite <-DTL.beqAddrTrue in HbeqBlockA. subst a4. rewrite HlookupBlocks2. unfold bentryAFlag in *.
      rewrite HlookupBlocks0 in *. rewrite <-HAFlagBlock. rewrite HnewBEntry; simpl. rewrite HlookupBlocks0.
      assert(HfiltEqs3: filterAccessible list s3 = filterAccessible list s2).
      { rewrite Hs3. apply filterAccessibleEqBENotInListNoChange. assumption. }
      rewrite HfiltEqs3. intuition.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup a4 (memory s2) beqAddr); try(apply IHlist; assumption).
      destruct v; try(apply IHlist; assumption). destruct (accessible b); try(apply IHlist; assumption).
      simpl in *. destruct HblockInLists2 as [Hcontra | HblockInLists2Rec]; try(exfalso; congruence).
      destruct (lookup a4 (memory s0) beqAddr); try(apply IHlist; assumption).
      destruct v; try(apply IHlist; assumption). specialize(IHlist HblockInLists2Rec HnoDupCurrRec).
      destruct IHlist as (Hleft & Hright). split; intro HaddrMapped; apply in_or_app;
        apply in_app_or in HaddrMapped.
      + destruct HaddrMapped as [Ha | HaddrMappedRec].
        * right. apply in_or_app. left. assumption.
        * specialize(Hleft HaddrMappedRec). apply in_app_or in Hleft. destruct Hleft as [Hnew | HleftRec].
          -- left. assumption.
          -- right. apply in_or_app. right. assumption.
      + destruct HaddrMapped as [Hnew | HaddrMapped].
        * right. apply Hright. apply in_or_app. left. assumption.
        * apply in_app_or in HaddrMapped. destruct HaddrMapped as [Ha | HaddrMappedRec].
          -- left. assumption.
          -- right. apply Hright. apply in_or_app. right. assumption.
  }

  assert(adressesRangePreservedIfOriginAndNextOk s).
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s*)
    assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0)
      by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros part pdentryPart block scentryaddr startaddr endaddr HpartIsPart HblockMappedPart HblockIsBE
      Hstart Hend HPFlag Hsce Horigin Hnext HlookupPart HbeqPartRoot.
    destruct (beqAddr newPDBlockStartAddr part) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst part. unfold getMappedBlocks in HblockMappedPart.
      unfold getKSEntries in HblockMappedPart. rewrite HlookupNewPDs in *. rewrite HnewPD in *. simpl in *.
      exfalso; congruence.
    }
    assert(HpartIsPDT: isPDT part s) by (unfold isPDT; rewrite HlookupPart; trivial).
    rewrite HgetMappedBlocksEq in HblockMappedPart; try(assumption). rewrite HgetPartsEq in HpartIsPart.
    assert(Hblocks0: isBE block s0 /\ bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0
            /\ bentryPFlag block true s0).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in Hstart.
      rewrite Hs in Hend. rewrite Hs in HPFlag. rewrite Hs3 in Hstart. rewrite Hs3 in Hend. rewrite Hs3 in HPFlag.
      simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold isBE. rewrite HlookupBlocks0.
        rewrite HnewBEntry in *. simpl in *. split. trivial. split; try(split); assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hend; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hend; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPFlag; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPFlag; try(apply not_eq_sym; assumption).
        assert(newPDBlockStartAddr <> block).
        {
          intro Hcontra. subst block. rewrite HlookupNewPDs2 in *. exfalso; congruence.
        }
        unfold isBE. rewrite <-HlookupEqs2s0; try(assumption).
        destruct (lookup block (memory s2) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). split. trivial. split; try(split); assumption.
    }
    destruct Hblocks0 as (HblockIsBEs0 & Hstarts0 & Hends0 & HPFlags0).
    assert(Hsces0: scentryOrigin scentryaddr startaddr s0 /\ scentryNext scentryaddr nullAddr s0).
    {
      unfold scentryOrigin in *. unfold scentryNext in *. rewrite Hs in Horigin. rewrite Hs in Hnext.
      rewrite Hs3 in Horigin. rewrite Hs3 in Hnext. simpl in *.
      destruct (beqAddr currentPart scentryaddr) eqn:HbeqCurrSce; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *.
      destruct (beqAddr idBlock scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Horigin; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Horigin; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hnext; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hnext; try(apply not_eq_sym; assumption).
      assert(newPDBlockStartAddr <> scentryaddr).
      { intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. exfalso; congruence. }
      rewrite <-HlookupEqs2s0; try(assumption). split; assumption.
    }
    destruct Hsces0 as (Horigins0 & Hnexts0).
    assert(HlookupParts0: exists pdentryParts0, lookup part (memory s0) beqAddr = Some (PDT pdentryParts0)
                            /\ parent pdentryParts0 = parent pdentryPart).
    {
      rewrite Hs in HlookupPart. rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. exists pdentry. split. assumption.
        injection HlookupPart as HpdentriesEq. subst pdentryPart. simpl. reflexivity.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock part) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite HlookupEqs2s0 in HlookupPart; try(assumption). exists pdentryPart. split. assumption. reflexivity.
    }
    destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HparentsEq)].
    specialize(Hcons0 part pdentryParts0 block scentryaddr startaddr endaddr HpartIsPart HblockMappedPart
      HblockIsBEs0 Hstarts0 Hends0 HPFlags0 Hsce Horigins0 Hnexts0 HlookupParts0 HbeqPartRoot).
    destruct Hcons0 as [blockParent (HblockParentMapped & HblockParentIsBE & HstartParent & HendParent)].
    exists blockParent.
    assert(HparentOfPart: parentOfPartitionIsPartition s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HparentOfPart part pdentryParts0 HlookupParts0). destruct HparentOfPart as (HparentIsPart & _).
    specialize(HparentIsPart HbeqPartRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HparentsEq in *.
    assert(newPDBlockStartAddr <> parent pdentryPart).
    {
      intro Hcontra. rewrite Hcontra in *. congruence.
    }
    rewrite beqAddrFalse in *. rewrite <-HgetPartsEq in HparentIsPart.
    rewrite HgetMappedBlocksEq; try(assumption); try(apply partitionsArePDT; assumption). split. assumption.
    unfold isBE. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs. rewrite Hs3. simpl.
    destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP.
    {
      rewrite <-DTL.beqAddrTrue in HbeqCurrBlockP. subst blockParent. rewrite HlookupCurrs0 in *.
      exfalso; congruence.
    }
    rewrite HbeqBlockCurr. simpl. destruct (beqAddr idBlock blockParent) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0 in *. rewrite HnewBEntry.
      simpl. split. trivial. split; assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      assert(newPDBlockStartAddr <> blockParent).
      {
        intro Hcontra. rewrite Hcontra in *. rewrite HremovedAddr in *. congruence.
      }
      rewrite HlookupEqs2s0; try(assumption).
      destruct (lookup blockParent (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split. trivial. split; assumption.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }
  assert(childsBlocksPropsInParent s).
  { (* BEGIN childsBlocksPropsInParent s*)
    assert(Hcons0: childsBlocksPropsInParent s0)
      by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
      HchildIsChild HblockChildMapped HstartChild HendChild HPFlagChild HblockParentMapped HstartParent
      HendParent HPFlagParent HlebStart HgebEnd.
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child. unfold getMappedBlocks in HblockChildMapped.
      unfold getKSEntries in HblockChildMapped. rewrite HlookupNewPDs in *. rewrite HnewPD in *. simpl in *.
      exfalso; congruence.
    }
    destruct (beqAddr newPDBlockStartAddr pdparent) eqn:HbeqStartParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartParent. subst pdparent. unfold getMappedBlocks in HblockParentMapped.
      unfold getKSEntries in HblockParentMapped. rewrite HlookupNewPDs in *. rewrite HnewPD in *. simpl in *.
      exfalso; congruence.
    }
    assert(HchildIsPDT: isPDT child s).
    { apply childrenArePDT with pdparent; assumption. }
    assert(HparentIsPDT: isPDT pdparent s).
    { apply partitionsArePDT; assumption. }
    rewrite HgetPartsEq in HparentIsPart. rewrite HgetMappedBlocksEq in HblockChildMapped; try(assumption).
    rewrite HgetMappedBlocksEq in HblockParentMapped; try(assumption).
    rewrite HgetChildrenEq in HchildIsChild; try(assumption).
    assert(Hchilds0: bentryStartAddr blockChild startChild s0 /\ bentryEndAddr blockChild endChild s0
            /\ bentryPFlag blockChild true s0).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartChild.
      rewrite Hs in HendChild. rewrite Hs in HPFlagChild. rewrite Hs3 in HstartChild. rewrite Hs3 in HendChild.
      rewrite Hs3 in HPFlagChild. simpl in *.
      destruct (beqAddr currentPart blockChild) eqn:HbeqCurrChild; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock blockChild) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockChild. rewrite HlookupBlocks0.
        rewrite HnewBEntry in *. simpl in *. split; try(split); assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HstartChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HstartChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HendChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HendChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPFlagChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPFlagChild; try(apply not_eq_sym; assumption).
        assert(newPDBlockStartAddr <> blockChild).
        { intro Hcontra. subst blockChild. rewrite HlookupNewPDs2 in *. congruence. }
        rewrite <-HlookupEqs2s0; try(assumption). split; try(split); assumption.
    }
    destruct Hchilds0 as (HstartChilds0 & HendChilds0 & HPFlagChilds0).
    assert(Hparents0: bentryStartAddr blockParent startParent s0 /\ bentryEndAddr blockParent endParent s0
            /\ bentryPFlag blockParent true s0).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartParent.
      rewrite Hs in HendParent. rewrite Hs in HPFlagParent. rewrite Hs3 in HstartParent.
      rewrite Hs3 in HendParent. rewrite Hs3 in HPFlagParent. simpl in *.
      destruct (beqAddr currentPart blockParent) eqn:HbeqCurrParent; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock blockParent) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0.
        rewrite HnewBEntry in *. simpl in *. split; try(split); assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HendParent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPFlagParent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPFlagParent; try(apply not_eq_sym; assumption).
        assert(newPDBlockStartAddr <> blockParent).
        { intro Hcontra. subst blockParent. rewrite HlookupNewPDs2 in *. congruence. }
        rewrite <-HlookupEqs2s0; try(assumption). split; try(split); assumption.
    }
    destruct Hparents0 as (HstartParents0 & HendParents0 & HPFlagParents0).
    specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent endParent
      HparentIsPart HchildIsChild HblockChildMapped HstartChilds0 HendChilds0 HPFlagChilds0 HblockParentMapped
      HstartParents0 HendParents0 HPFlagParents0 HlebStart HgebEnd).
    destruct Hcons0 as (HcheckChild & HPDchild & HInChildLoc & Haccess). unfold checkChild in *.
    assert(HlookupSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                          = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
    {
      rewrite Hs. rewrite Hs3. simpl.
      assert(HwellFormedSh1: wellFormedFstShadowIfBlockEntry s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(HblockPIsBE: isBE blockParent s0).
      {
        apply mappedBlockIsBE in HblockParentMapped. destruct HblockParentMapped as [bentryParent (Hlookup & _)].
        unfold isBE. rewrite Hlookup. trivial.
      }
      specialize(HwellFormedSh1 blockParent HblockPIsBE). unfold isSHE in *.
      destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrParentSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrParentSh1. rewrite <-HbeqCurrParentSh1 in *.
        rewrite HlookupCurrs0 in *. exfalso; congruence.
      }
      rewrite HbeqBlockCurr. simpl.
      destruct (beqAddr idBlock (CPaddr (blockParent + sh1offset))) eqn:HbeqBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *. rewrite HlookupBlocks0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). apply HlookupEqs2s0. intro Hcontra.
      rewrite <-Hcontra in *. rewrite HremovedAddr in *. congruence.
    }
    unfold sh1entryPDchild. unfold sh1entryInChildLocation. rewrite HlookupSh1Eq.
    unfold bentryAFlag in *. unfold bentryStartAddr in HstartParent. rewrite Hs. rewrite Hs in HstartParent.
    rewrite Hs3. rewrite Hs3 in HstartParent. simpl in *.
    destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP; try(exfalso; congruence).
    rewrite HbeqBlockCurr. simpl.
    split; try(split; try(split)); try(assumption).
    - destruct (beqAddr idBlock blockParent) eqn:HbeqBlocks.
      + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0 in *. assumption.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        intro Hcontra. subst blockParent. unfold bentryEndAddr in *. rewrite HremovedAddr in *. congruence.
    - intros blockIDInChild HchildLocs. apply HInChildLoc. unfold sh1entryInChildLocation.
      destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HchildLocs as (HchildLocs & HlocNotNull). split. assumption.
      intro HbeqLocNull. specialize(HlocNotNull HbeqLocNull). unfold isBE in *. simpl in *.
      destruct (beqAddr currentPart blockIDInChild) eqn:HbeqCurrLoc; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock blockIDInChild) eqn:HbeqBlocks.
      + rewrite <-DTL.beqAddrTrue in HbeqBlocks. rewrite <-HbeqBlocks. rewrite HlookupBlocks0. trivial.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlocNotNull; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HlocNotNull; try(apply not_eq_sym; assumption).
        rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *.
        rewrite HlookupNewPDs2 in *. congruence.
    - intro Hbounds. specialize(Haccess Hbounds). destruct (beqAddr idBlock blockParent) eqn:HbeqBlocks.
      + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HnewBEntry. simpl. reflexivity.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *.
        rewrite HremovedAddr in *. congruence.
    (* END childsBlocksPropsInParent *)
  }
  assert(noChildImpliesAddressesNotShared s).
  { (* BEGIN noChildImpliesAddressesNotShared s*)
    assert(Hcons0: noChildImpliesAddressesNotShared s0)
      by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros part pdentryPart block sh1entryaddr HpartIsPart HlookupPart HblockMappedPart Hsh1Bis HPDchild
      child addr HchildIsChild HaddrInBlock.
    destruct (beqAddr newPDBlockStartAddr part) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst part. unfold getMappedBlocks in *.
      unfold getKSEntries in *. rewrite HlookupNewPDs in *. rewrite HnewPD in *. simpl in *. exfalso; congruence.
    }
    assert(HpartIsPDT: isPDT part s).
    { unfold isPDT. rewrite HlookupPart. trivial. }
    assert(HchildIsPDT: isPDT child s).
    { apply childrenArePDT with part; assumption. }
    rewrite HgetPartsEq in HpartIsPart. rewrite HgetMappedBlocksEq in HblockMappedPart; try(assumption).
    rewrite HgetChildrenEq in HchildIsChild; try(assumption).
    assert(HlookupParts0: exists pdentryParts0, lookup part (memory s0) beqAddr = Some (PDT pdentryParts0)).
    {
      rewrite Hs in HlookupPart. rewrite Hs3 in HlookupPart. simpl in *.
      destruct (beqAddr currentPart part) eqn:HbeqCurrPart.
      - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst part. exists pdentry. assumption.
      - rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr idBlock part) eqn:HbeqBlockPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
        rewrite HlookupEqs2s0 in HlookupPart; try(assumption). exists pdentryPart. assumption.
    }
    destruct HlookupParts0 as [pdentryParts0 HlookupParts0].
    assert(HPDchilds0: sh1entryPDchild sh1entryaddr nullAddr s0).
    {
      unfold sh1entryPDchild in *. rewrite Hs in HPDchild. rewrite Hs3 in HPDchild. simpl in *.
      destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *.
      destruct (beqAddr idBlock sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym; assumption).
      rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *.
      congruence.
    }
    assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
    {
      rewrite Hs in HaddrInBlock. rewrite Hs3 in HaddrInBlock. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(simpl in *; exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0. rewrite HnewBEntry in *.
        simpl in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HaddrInBlock; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HaddrInBlock; try(apply not_eq_sym; assumption).
        rewrite <-HlookupEqs2s0; try(assumption). intro Hcontra. rewrite Hcontra in *.
        rewrite HlookupNewPDs2 in *. simpl in *. congruence.
    }
    specialize(Hcons0 part pdentryParts0 block sh1entryaddr HpartIsPart HlookupParts0 HblockMappedPart Hsh1Bis
      HPDchilds0 child addr HchildIsChild HaddrInBlocks0).
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    - rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child. unfold getMappedPaddr. unfold getMappedBlocks.
      unfold getKSEntries. rewrite HlookupNewPDs. rewrite HnewPD. simpl. intro Hcontra. congruence.
    - rewrite HgetMappedPaddrEq; assumption.
    (* END noChildImpliesAddressesNotShared *)
  }
  assert(kernelsAreNotAccessible s).
  { (* BEGIN kernelsAreNotAccessible s*)
    assert(Hcons0: kernelsAreNotAccessible s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros block startaddr Hstart HstartIsKS.
    assert(Hstarts0: bentryStartAddr block startaddr s0).
    {
      unfold bentryStartAddr in *. rewrite Hs in Hstart. rewrite Hs3 in Hstart. simpl in *.
      destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0.
        rewrite HnewBEntry in Hstart. simpl in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
        assert(newPDBlockStartAddr <> block).
        { intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence. }
        rewrite <-HlookupEqs2s0; assumption.
    }
    assert(HstartIsKSs0: isKS startaddr s0).
    {
      unfold isKS in *. rewrite Hs in HstartIsKS. rewrite Hs3 in HstartIsKS. simpl in *.
      destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStartBis; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock startaddr) eqn:HbeqBlockStart.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockStart. subst startaddr. rewrite HlookupBlocks0.
        rewrite HnewBEntry in HstartIsKS. simpl in *. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HstartIsKS; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HstartIsKS; try(apply not_eq_sym; assumption).
        assert(newPDBlockStartAddr <> startaddr).
        { intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence. }
        rewrite <-HlookupEqs2s0; assumption.
    }
    specialize(Hcons0 block startaddr Hstarts0 HstartIsKSs0). unfold bentryAFlag in *. rewrite Hs. rewrite Hs3.
    unfold bentryStartAddr in *. rewrite Hs in Hstart. rewrite Hs3 in Hstart. simpl in *.
    destruct (beqAddr currentPart block) eqn:HbeqCurrBlockBis; try(exfalso; congruence).
    rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr idBlock block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HnewBEntry. simpl. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hstart; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      assert(newPDBlockStartAddr <> block).
      { intro Hcontra. rewrite Hcontra in *. rewrite HlookupNewPDs2 in *. congruence. }
      rewrite HlookupEqs2s0; assumption.
    (* END kernelsAreNotAccessible *)
  }

  assert(isBE blockInCurrentPartitionAddr s).
  {
    subst blockInCurrentPartitionAddr. unfold isBE. rewrite HlookupBlocks. trivial.
  }
  (*Three props missing: notPDTIfNotPDflag s
        accessibleParentPaddrIsAccessibleIntoChild s
        sharedBlockPointsToChild s*)
  instantiate(1 := fun s =>
    exists s3 s2 s1 s0 newBentry bentry newPDEntry realMPU pdentry newPDCurr,
      s = {|
            currentPartition := currentPartition s3;
            memory := add currentPart (PDT newPDCurr) (memory s3) beqAddr
          |}
      /\ newPDCurr = {|
                       structure := structure pdentry;
                       firstfreeslot := firstfreeslot pdentry;
                       nbfreeslots := nbfreeslots pdentry;
                       nbprepare := nbprepare pdentry;
                       parent := parent pdentry;
                       MPU := MAL.removeBlockFromPhysicalMPUAux blockInCurrentPartitionAddr realMPU;
                       vidtAddr := vidtAddr pdentry
                     |}
      /\ PDTIfPDFlag s
      /\ wellFormedFstShadowIfBlockEntry s
      /\ currentPartitionInPartitionsList s
      /\ AccessibleNoPDFlag s
      /\ FirstFreeSlotPointerIsBEAndFreeSlot s
      /\ multiplexerIsPDT s
      /\ sh1InChildLocationIsBE s
      /\ StructurePointerIsKS s
      /\ DisjointKSEntries s
      /\ NextKSOffsetIsPADDR s
      /\ wellFormedShadowCutIfBlockEntry s
      /\ NextKSIsKS s
      /\ maxNbPrepareIsMaxNbKernels s
      /\ partitionTreeIsTree s
      /\ blockInChildHasAtLeastEquivalentBlockInParent s
      /\ noDupKSEntriesList s
      /\ noDupMappedBlocksList s
      /\ NoDupInFreeSlotsList s
      /\ freeSlotsListIsFreeSlot s
      /\ DisjointFreeSlotsLists s
      /\ inclFreeSlotsBlockEntries s
      /\ isParent s
      /\ isChild s
      /\ MPUsizeIsBelowMax s
      /\ noDupPartitionTree s
      /\ wellFormedBlock s
      /\ parentOfPartitionIsPartition s
      /\ NbFreeSlotsISNbFreeSlotsInList s
      /\ originIsParentBlocksStart s
      /\ nextImpliesBlockWasCut s
      /\ nextKernAddrIsInSameBlock s
      /\ blocksAddressesTypes s
      /\ childsBlocksPropsInParent s
      /\ noDupUsedPaddrList s
      /\ adressesRangePreservedIfOriginAndNextOk s
      /\ noChildImpliesAddressesNotShared s
      /\ kernelEntriesAreValid s
      /\ nextKernelIsValid s
      /\ noDupListOfKerns s
      /\ kernelsAreNotAccessible s
      /\ KernelStructureStartFromBlockEntryAddrIsKS s
      /\ BlocksRangeFromKernelStartIsBE s
      /\ nullAddrExists s
      /\ lookup currentPart (memory s) beqAddr = Some (PDT newPDCurr)
      /\ lookup newPDBlockStartAddr (memory s) beqAddr = Some (PDT newPDEntry)
      /\ lookup idBlock (memory s) beqAddr = Some (BE newBentry)
      /\ (forall part, isPDT part s -> beqAddr newPDBlockStartAddr part = false
            -> getFreeSlotsList part s = getFreeSlotsList part s0)
      /\ (forall parentsList part, beqAddr newPDBlockStartAddr part = false
          -> isParentsList s parentsList part
          -> isParentsList s0 parentsList part)
      /\ (forall blockBis, beqAddr idBlock blockBis = false
          -> isBE blockBis s
          -> lookup blockBis (memory s) beqAddr = lookup blockBis (memory s0) beqAddr)
      (* properties of s3 *)
      /\ s3 = {|
                currentPartition := currentPartition s2; memory := add idBlock (BE newBentry) (memory s2) beqAddr
              |}
      /\ (exists l,
            newBentry =
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
      /\ lookup idBlock (memory s3) beqAddr = Some (BE newBentry)
      /\ lookup currentPart (memory s3) beqAddr = Some (PDT pdentry)
      /\ pdentryMPU currentPart realMPU s3
      (* properties of s2 *)
      /\ s2 =
          {|
            currentPartition := currentPartition s1;
            memory := add newPDBlockStartAddr (PDT newPDEntry) (memory s1) beqAddr
          |}
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
      /\ lookup currentPart (memory s2) beqAddr = Some (PDT pdentry)
      /\ lookup idBlock (memory s2) beqAddr = Some (BE bentry)
      /\ lookup newPDBlockStartAddr (memory s2) beqAddr = Some (PDT newPDEntry)
      /\  (forall addr, newPDBlockStartAddr <> addr
            -> lookup addr (memory s2) beqAddr = lookup addr (memory s0) beqAddr)
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
      /\ partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ consistency s0
      /\ isPDT currentPart s0
      /\ currentPart = currentPartition s0
      /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)
      /\ bentryStartAddr idBlock newPDBlockStartAddr s0
      /\ bentryEndAddr idBlock newPDBlockEndAddr s0
      /\ bentryAFlag idBlock true s0 /\ bentryPFlag idBlock true s0
      /\ In idBlock (getMappedBlocks currentPart s0)
      /\ lookup idBlock (memory s0) beqAddr = Some (BE bentry)
      /\ lookup newPDBlockStartAddr (memory s0) beqAddr = None
      /\ ~ isFreeSlot idBlock s0
      /\ (exists sh1entry sh1entryaddr, lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
            /\ sh1entryPDchild sh1entryaddr nullAddr s0 /\ sh1entryAddr idBlock sh1entryaddr s0)
      (* other properties *)
      /\ blockInCurrentPartitionAddr = idBlock
      /\ beqAddr newPDBlockStartAddr idBlock = false
      /\ beqAddr nullAddr idBlock = false
      /\ minBlockSize = Constants.minBlockSize
      /\ false = indexLt blockSize minBlockSize
      /\ PDStructureTotalLength = Constants.PDStructureTotalLength
      /\ false = indexLt blockSize PDStructureTotalLength
      /\ i blockSize = newPDBlockEndAddr - newPDBlockStartAddr
      /\ beqAddr idBlock currentPart = false
      /\ newPDBlockStartAddr <> currentPart
      /\ beqAddr currentPart newPDBlockStartAddr = false
      (* properties needed for the missing consistency properties *)
      /\ getPartitions multiplexer s = getPartitions multiplexer s0
      /\ (forall part, In part (getPartitions multiplexer s0) -> getChildren part s = getChildren part s0)
      /\ (forall addr, In addr (getAccessibleMappedPaddr currentPart s0)
                        <-> In addr (getAllPaddrAux [idBlock] s ++ getAccessibleMappedPaddr currentPart s))
      /\ (forall part,
            isPDT part s
            -> isPDT part s0
            -> beqAddr newPDBlockStartAddr part = false
            -> part <> currentPart
            -> getAccessibleMappedPaddr part s0 = getAccessibleMappedPaddr part s)
      /\ (forall part, isPDT part s -> beqAddr newPDBlockStartAddr part = false
              -> getMappedPaddr part s = getMappedPaddr part s0)
      /\ (forall part, isPDT part s0 -> beqAddr newPDBlockStartAddr part = false
              -> getConfigPaddr part s = getConfigPaddr part s0)
      /\ (forall part, isPDT part s -> beqAddr newPDBlockStartAddr part = false
              -> getMappedBlocks part s = getMappedBlocks part s0)).
  intuition. exists s3. exists s2. exists s1. exists s0. exists newBentry. exists bentry. exists newPDEntry.
  exists realMPU. exists pdentry. exists newPDCurr. intuition. exists l. assumption.
}
intro. eapply bindRev.
{ (* MAL.readSCOriginFromBlockEntryAddr *)
  eapply weaken. apply readSCOriginFromBlockEntryAddr. intros s Hprops. simpl. destruct Hprops as [s4 [sh1entry ([s3
    [s2 [s1 [s0 [newBentry [bentry [newPDentry [realMPU [pdentry [newPDCurr Hprops]]]]]]]]]] & HlookupSh1 & Hs)]].

  assert(nullAddrExists s).
  { (* BEGIN nullAddrExists s *)
    assert(Hnull: nullAddrExists s4) by intuition.
    unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) nullAddr) eqn:HbeqSh1Null.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Null. rewrite HbeqSh1Null in *. rewrite HlookupSh1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END nullAddrExists *)
  }
  assert(wellFormedFstShadowIfBlockEntry s).
  { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
    assert(Hcons0: wellFormedFstShadowIfBlockEntry s4) by intuition.
    intros block HblockIsBE.
    assert(HblockIsBEs0: isBE block s4).
    {
      unfold isBE in *. rewrite Hs in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqSh1BlockBis;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 block HblockIsBEs0). unfold isSHE in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1;
      trivial. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END wellFormedFstShadowIfBlockEntry *)
  }
  assert(Hs4: s4 = {|
                    currentPartition := currentPartition s3;
                    memory := add currentPart (PDT newPDCurr) (memory s3) beqAddr
                  |}) by intuition.
  assert(HnewBentry: exists l,
                      newBentry =
                      {|
                        read := read bentry;
                        write := write bentry;
                        exec := exec bentry;
                        present := present bentry;
                        accessible := false;
                        blockindex := blockindex bentry;
                        blockrange := blockrange bentry;
                        Hidx := l
                      |}) by intuition. destruct HnewBentry as [l HnewBentry].
  assert(HlookupBlocks0: lookup idBlock (memory s0) beqAddr = Some (BE bentry)) by intuition.
  assert(HlookupBlocks3: lookup idBlock (memory s3) beqAddr = Some (BE newBentry)) by intuition.
  assert(HbeqBlockCurr: beqAddr idBlock currentPart = false) by intuition.
  assert(HlookupBlocks4: lookup idBlock (memory s4) beqAddr = Some (BE newBentry)).
  {
    rewrite Hs4. simpl. rewrite beqAddrSym in HbeqBlockCurr. rewrite HbeqBlockCurr. rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
  }
  assert(HlookupBlocks: lookup idBlock (memory s) beqAddr = Some (BE newBentry)).
  {
    rewrite Hs. simpl. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) idBlock) eqn:HbeqSh1Block.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Block. rewrite HbeqSh1Block in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
  }
  assert(HlookupNews4: lookup newPDBlockStartAddr (memory s4) beqAddr = Some (PDT newPDentry)) by intuition.
  assert(HlookupNews: lookup newPDBlockStartAddr (memory s) beqAddr = Some (PDT newPDentry)).
  {
    rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) newPDBlockStartAddr) eqn:HbeqSh1Start.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Start. rewrite <-HbeqSh1Start in *. exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
  }
  assert(PDTIfPDFlag s).
  { (* BEGIN PDTIfPDFlag s *)
    assert(Hcons0: PDTIfPDFlag s4) by intuition.
    intros idPDchild sh1entryaddr HcheckChild. destruct HcheckChild as (HcheckChild & Hsh1Bis).
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1.
    - rewrite <-DTL.beqAddrTrue in HbeqSh1. subst sh1entryaddr.
      assert(HblocksEq: idPDchild = blockInCurrentPartitionAddr).
      {
        unfold sh1entryAddr in *. destruct (lookup idPDchild (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). unfold CPaddr in Hsh1Bis. unfold CPaddr in HlookupSh1.
        assert(HnullExists: nullAddrExists s4) by intuition. unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr).
        - destruct (le_dec (idPDchild + sh1offset) maxAddr).
          + injection Hsh1Bis as Hres. apply PeanoNat.Nat.add_cancel_r in Hres. destruct blockInCurrentPartitionAddr.
            destruct idPDchild. simpl in *. subst p0. f_equal. apply proof_irrelevance.
          + rewrite Hsh1Bis in HlookupSh1.
            assert(Hnull: nullAddr = {| p := 0; Hp := ADT.CPaddr_obligation_2 (p idPDchild + i sh1offset) n |}).
            {
              unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            rewrite <-Hnull in *. rewrite HlookupSh1 in *. exfalso; congruence.
        - exfalso.
          assert(Hnull: nullAddr
                      = {| p := 0; Hp := ADT.CPaddr_obligation_2 (p blockInCurrentPartitionAddr + i sh1offset) n |}).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite <-Hnull in *. rewrite HlookupSh1 in *. congruence.
      }
      subst idPDchild. assert(blockInCurrentPartitionAddr = idBlock) by intuition. subst idBlock. unfold bentryAFlag.
      assert(bentryPFlag blockInCurrentPartitionAddr true s0) by intuition.
      assert(bentryStartAddr blockInCurrentPartitionAddr newPDBlockStartAddr s0) by intuition.
      unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold entryPDT. rewrite HlookupBlocks.
      rewrite HnewBentry. simpl. split. reflexivity. rewrite HlookupBlocks0 in *. split. assumption.
      exists newPDBlockStartAddr. split. assumption. subst newPDBlockStartAddr. rewrite HlookupNews. reflexivity.
    - assert(HcheckChilds0: true = checkChild idPDchild s4 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s4).
      {
        unfold checkChild in *. unfold sh1entryAddr in *. rewrite Hs in HcheckChild. rewrite Hs in Hsh1Bis.
        simpl in *. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) idPDchild)
          eqn:HbeqSh1PDChild; try(exfalso; congruence). rewrite HbeqSh1 in *. rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption). split; try(assumption).
        destruct (lookup idPDchild (memory s4) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        rewrite removeDupIdentity in HcheckChild; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 idPDchild sh1entryaddr HcheckChilds0). unfold bentryAFlag in *. unfold bentryPFlag in *.
      destruct Hcons0 as (HAFlag & HPFlag & [startaddr (Hstart & HstartIsPDT)]). unfold bentryStartAddr in *.
      unfold entryPDT in *. unfold sh1entryAddr in Hsh1Bis. rewrite Hs. rewrite Hs in Hsh1Bis. simpl.
      simpl in Hsh1Bis.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) idPDchild) eqn:HbeqSh1PDChild;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption). split. assumption. split. assumption.
      exists startaddr. split. assumption. destruct (lookup idPDchild (memory s4) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (startAddr (blockrange b)))
        eqn:HbeqSh1StartBis.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1StartBis. rewrite <-HbeqSh1StartBis in *. rewrite HlookupSh1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END PDTIfPDFlag *)
  }
  assert(AccessibleNoPDFlag s).
  { (* BEGIN AccessibleNoPDFlag s *)
    assert(Hcons0: AccessibleNoPDFlag s4) by intuition.
    intros block sh1entryaddr HblockIsBE Hsh1Bis HAFlag. unfold isBE in *. unfold sh1entryAddr in *.
    unfold bentryAFlag in *. rewrite Hs in HblockIsBE. rewrite Hs in Hsh1Bis. rewrite Hs in HAFlag. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqSh1BlockBis;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in Hsh1Bis; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HAFlag; try(apply not_eq_sym; assumption).
    specialize(Hcons0 block sh1entryaddr HblockIsBE Hsh1Bis HAFlag). unfold sh1entryPDflag in *. rewrite Hs.
    simpl. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1s. rewrite HbeqSh1s in *. exfalso.
      destruct (lookup block (memory s4) beqAddr) eqn:HlookupBlockBis; try(congruence). destruct v; try(congruence).
      subst sh1entryaddr. unfold CPaddr in HbeqSh1s. unfold CPaddr in Hcons0.
      assert(HnullExists: nullAddrExists s4) by intuition. unfold nullAddrExists in *. unfold isPADDR in *.
      destruct (le_dec (block + sh1offset) maxAddr).
      - destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr).
        + injection HbeqSh1s as Heq. apply PeanoNat.Nat.add_cancel_r in Heq.
          assert(blockInCurrentPartitionAddr = block).
          {
            destruct block. destruct blockInCurrentPartitionAddr. simpl in *. subst p0. f_equal.
            apply proof_irrelevance.
          }
          subst block. assert(blockInCurrentPartitionAddr = idBlock) by intuition. subst idBlock.
          rewrite HlookupBlocks4 in *. injection HlookupBlockBis as HbentriesEq. subst b. rewrite HnewBentry in *.
          simpl in *. congruence.
        + rewrite <-HbeqSh1s in Hcons0.
          assert(HnullEq: nullAddr
                            = {| p := 0;
                                 Hp := ADT.CPaddr_obligation_2 (p blockInCurrentPartitionAddr + i sh1offset) n |}).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite <-HnullEq in *. destruct (lookup nullAddr (memory s4) beqAddr); try(congruence).
          destruct v; congruence.
      - assert(HnullEq: nullAddr
                          = {| p := 0;
                               Hp := ADT.CPaddr_obligation_2 (p block + i sh1offset) n |}).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite <-HnullEq in *. destruct (lookup nullAddr (memory s4) beqAddr); try(congruence).
        destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END AccessibleNoPDFlag *)
  }
  assert(Hs3: s3 = {|
                     currentPartition := currentPartition s2; memory := add idBlock (BE newBentry) (memory s2) beqAddr
                   |}) by intuition.
  assert(HlookupCurrs0: lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
  assert(HnewPDCurr: newPDCurr = {|
                                   structure := structure pdentry;
                                   firstfreeslot := firstfreeslot pdentry;
                                   nbfreeslots := nbfreeslots pdentry;
                                   nbprepare := nbprepare pdentry;
                                   parent := parent pdentry;
                                   MPU := MAL.removeBlockFromPhysicalMPUAux blockInCurrentPartitionAddr realMPU;
                                   vidtAddr := vidtAddr pdentry
                                 |}) by intuition.
  assert(HlookupEqs2s0: forall addr, newPDBlockStartAddr <> addr
            -> lookup addr (memory s2) beqAddr = lookup addr (memory s0) beqAddr) by intuition.
  assert(HnewPDentry: newPDentry =
                                  {|
                                    structure := nullAddr;
                                    firstfreeslot := nullAddr;
                                    nbfreeslots := zero;
                                    nbprepare := zero;
                                    parent := currentPart;
                                    MPU := [];
                                    vidtAddr := nullAddr
                                  |}) by intuition.
  assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
  { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
    assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s4) by intuition.
    intros partition pdentryPart HlookupPart HbeqFirstFreeNull.
    assert(HlookupParts4: lookup partition (memory s4) beqAddr = Some (PDT pdentryPart)).
    {
      rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
    }
    specialize(Hcons0 partition pdentryPart HlookupParts4 HbeqFirstFreeNull).
    destruct Hcons0 as (_ & HfirstFree). unfold isBE. unfold isFreeSlot in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (firstfreeslot pdentryPart))
      eqn:HbeqSh1FirstFree.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqSh1FirstFree. rewrite HbeqSh1FirstFree in *.
      rewrite HlookupSh1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup (firstfreeslot pdentryPart) (memory s4) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). split; trivial.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset))
                      (CPaddr (firstfreeslot pdentryPart + sh1offset))) eqn:HbeqSh1FirstSh1.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1FirstSh1. exfalso. rewrite <-HbeqSh1FirstSh1 in *. rewrite HlookupSh1 in *.
      destruct (lookup (CPaddr (firstfreeslot pdentryPart + scoffset)) (memory s4) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HfirstFree as (_ & _ & _ & _ & _ & Hcontra & _).
      assert(HnullExists: nullAddrExists s4) by intuition. unfold nullAddrExists in *. unfold isPADDR in *.
      unfold CPaddr in HbeqSh1FirstSh1. unfold CPaddr in HlookupSh1.
      destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr).
      - destruct (le_dec (firstfreeslot pdentryPart + sh1offset) maxAddr).
        + injection HbeqSh1FirstSh1 as Heq. apply PeanoNat.Nat.add_cancel_r in Heq.
          assert(blockInCurrentPartitionAddr = firstfreeslot pdentryPart).
          {
            destruct (firstfreeslot pdentryPart). destruct blockInCurrentPartitionAddr. simpl in *. subst p0. f_equal.
            apply proof_irrelevance.
          }
          subst blockInCurrentPartitionAddr. assert(HblockIsNotFree: ~ isFreeSlot idBlock s0) by intuition.
          assert(firstfreeslot pdentryPart = idBlock) by intuition. subst idBlock.
          destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
          {
            rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. rewrite HlookupNews4 in HlookupParts4.
            injection HlookupParts4 as HpdentriesEq. subst pdentryPart. rewrite HnewPDentry in HbeqFirstFreeNull.
            simpl in *. congruence.
          }
          assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HlookupParts0: exists pdentryParts0, lookup partition (memory s0) beqAddr = Some (PDT pdentryParts0)
                                  /\ firstfreeslot pdentryParts0 = firstfreeslot pdentryPart).
          {
            rewrite Hs4 in HlookupParts4. rewrite Hs3 in HlookupParts4. simpl in *.
            destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
            - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. exists pdentry. split. assumption.
              injection HlookupParts4 as HpdentriesEq. subst pdentryPart. rewrite HnewPDCurr. simpl. reflexivity.
            - rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr in *. simpl in *.
              destruct (beqAddr (firstfreeslot pdentryPart) partition) eqn:HbeqBlockPart; try(exfalso; congruence).
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupParts4;
                try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in HlookupParts4; try(apply not_eq_sym; assumption).
              rewrite HlookupEqs2s0 in HlookupParts4; try(assumption). exists pdentryPart. split. assumption.
              reflexivity.
          }
          destruct HlookupParts0 as [pdentryParts0 (HlookupParts0 & HfirstEq)]. rewrite <-HfirstEq in *.
          specialize(HfirstIsFree partition pdentryParts0 HlookupParts0 HbeqFirstFreeNull).
          destruct HfirstIsFree as (_ & HfirstIsFree). congruence.
        + rewrite HbeqSh1FirstSh1 in HlookupSh1.
          assert(HnullEq: nullAddr
                          = {| p := 0; Hp := ADT.CPaddr_obligation_2 (firstfreeslot pdentryPart + sh1offset) n |}).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite <-HnullEq in *. destruct (lookup nullAddr (memory s4) beqAddr); try(congruence).
          destruct v; congruence.
      - assert(HnullEq: nullAddr
                        = {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockInCurrentPartitionAddr + sh1offset) n |}).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite <-HnullEq in *. destruct (lookup nullAddr (memory s4) beqAddr); try(congruence).
        destruct v; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup (CPaddr (firstfreeslot pdentryPart + sh1offset)) (memory s4) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset))
                      (CPaddr (firstfreeslot pdentryPart + scoffset))) eqn:HbeqSh1FirstSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1FirstSce. rewrite <-HbeqSh1FirstSce in *. rewrite HlookupSh1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
  }
  assert(multiplexerIsPDT s).
  { (* BEGIN multiplexerIsPDT s *)
    assert(Hcons0: multiplexerIsPDT s4) by intuition.
    unfold multiplexerIsPDT in *. unfold isPDT in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) multiplexer) eqn:HbeqSh1Mult.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Mult. rewrite HbeqSh1Mult in *. rewrite HlookupSh1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END multiplexerIsPDT *)
  }
  assert(HcurrEq: currentPartition s = currentPartition s4).
  {
    rewrite Hs. simpl. reflexivity.
  }
  assert(HgetPartsInclss4: forall part, In part (getPartitions multiplexer s)
            -> In part (newPDBlockStartAddr::getPartitions multiplexer s4)).
  {
    rewrite Hs. intro part.
    apply getPartitionsEqSHEPDflagTrue with blockInCurrentPartitionAddr sh1entry; try(assumption).
    - intuition.
    - unfold sh1entryAddr. assert(blockInCurrentPartitionAddr = idBlock) by intuition. subst idBlock.
      rewrite HlookupBlocks4. reflexivity.
    - assert(blockInCurrentPartitionAddr = idBlock) by intuition. subst idBlock.
      assert(bentryStartAddr blockInCurrentPartitionAddr newPDBlockStartAddr s0) by intuition.
      unfold bentryStartAddr in *. rewrite HlookupBlocks0 in *. rewrite HlookupBlocks4. rewrite HnewBentry. simpl.
      assumption.
    - simpl. reflexivity.
    - intuition.
    - unfold getChildren. rewrite <-Hs. rewrite HlookupNews. unfold getMappedBlocks. unfold getKSEntries.
      rewrite HlookupNews. rewrite HnewPDentry. simpl. unfold getPDs. simpl. reflexivity.
    - intuition.
  }
  assert(HgetPartsIncls4s: forall part, In part (getPartitions multiplexer s4)
            -> In part (getPartitions multiplexer s)).
  {
    rewrite Hs. intro part.
    apply getPartitionsEqSHEPDflagTrueRev with blockInCurrentPartitionAddr newPDBlockStartAddr sh1entry;
      try(rewrite <-Hs); try(assumption).
    - intuition.
    - unfold sh1entryAddr. assert(blockInCurrentPartitionAddr = idBlock) by intuition. subst idBlock.
      rewrite HlookupBlocks4. reflexivity.
    - assert(blockInCurrentPartitionAddr = idBlock) by intuition. subst idBlock.
      assert(bentryStartAddr blockInCurrentPartitionAddr newPDBlockStartAddr s0) by intuition.
      unfold bentryStartAddr in *. rewrite HlookupBlocks0 in *. rewrite HlookupBlocks4. rewrite HnewBentry. simpl.
      assumption.
    - simpl. reflexivity.
    - unfold getChildren. rewrite HlookupNews4. unfold getMappedBlocks. unfold getKSEntries.
      rewrite HlookupNews4. rewrite HnewPDentry. simpl. unfold getPDs. simpl. reflexivity.
    - intuition.
  }
  assert(currentPartitionInPartitionsList s).
  { (* BEGIN currentPartitionInPartitionsList s *)
    assert(Hcons0: currentPartitionInPartitionsList s4) by intuition.
    unfold currentPartitionInPartitionsList in *.
    rewrite HcurrEq. apply HgetPartsIncls4s. assumption.
    (* END currentPartitionInPartitionsList *)
  }
  assert(wellFormedShadowCutIfBlockEntry s).
  { (* BEGIN wellFormedShadowCutIfBlockEntry s*)
    assert(Hcons0: wellFormedShadowCutIfBlockEntry s4) by intuition. intros block HblockIsBE.
    unfold isBE in *. rewrite Hs in HblockIsBE. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqSh1BlockBis;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
    specialize(Hcons0 block HblockIsBE). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)].
    exists scentryaddr. split; try(assumption). unfold isSCE in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) scentryaddr) eqn:HbeqSh1Sce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. rewrite HlookupSh1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END wellFormedShadowCutIfBlockEntry *)
  }
  assert(BlocksRangeFromKernelStartIsBE s).
  { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
    assert(Hcons0: BlocksRangeFromKernelStartIsBE s4) by intuition.
    intros kernel blockidx HkernIsKS Hblockidx.
    assert(HkernIsKSs0: isKS kernel s4).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) kernel) eqn:HbeqSh1Kern;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 kernel blockidx HkernIsKSs0 Hblockidx). unfold isBE in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (CPaddr (kernel + blockidx)))
      eqn:HbeqSh1KernIdx.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1KernIdx. rewrite <-HbeqSh1KernIdx in *. rewrite HlookupSh1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END BlocksRangeFromKernelStartIsBE *)
  }
  assert(KernelStructureStartFromBlockEntryAddrIsKS s).
  { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
    assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s4) by intuition.
    intros block blockidx HblockIsBE HblockIdx.
    assert(Hblock: isBE block s4 /\ bentryBlockIndex block blockidx s4).
    {
      unfold isBE. unfold bentryBlockIndex in *. rewrite Hs in HblockIdx. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqSh1BlockBis;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIdx; try(apply not_eq_sym; assumption).
      split; try(assumption).
      destruct (lookup block (memory s4) beqAddr); try(congruence). destruct v; try(congruence). trivial.
    }
    destruct Hblock as (HblockIsBEs4 & HblockIdxs4). specialize(Hcons0 block blockidx HblockIsBEs4 HblockIdxs4).
    unfold isKS in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (CPaddr (block - blockidx))) eqn:HbeqSh1Kern.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Kern. rewrite <-HbeqSh1Kern in *. rewrite HlookupSh1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (*END KernelStructureStartFromBlockEntryAddrIsKS *)
  }
  assert(sh1InChildLocationIsBE s).
  { (* BEGIN sh1InChildLocationIsBE s *)
    assert(Hcons0: sh1InChildLocationIsBE s4) by intuition.
    intros sh1entryaddr sh1entryBis HlookupSh1Bis HbeqChildLocNull. rewrite Hs in HlookupSh1Bis. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
    - injection HlookupSh1Bis as Hsh1entriesEq. subst sh1entryBis. simpl in *.
      specialize(Hcons0 (CPaddr (blockInCurrentPartitionAddr + sh1offset)) sh1entry HlookupSh1 HbeqChildLocNull).
      unfold isBE in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (inChildLocation sh1entry))
        eqn:HbeqSh1ChildLoc.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1ChildLoc. rewrite HbeqSh1ChildLoc in *. rewrite HlookupSh1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupSh1Bis; try(apply not_eq_sym; assumption).
      specialize(Hcons0 sh1entryaddr sh1entryBis HlookupSh1Bis HbeqChildLocNull). unfold isBE in *. rewrite Hs.
      simpl. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (inChildLocation sh1entryBis))
        eqn:HbeqSh1ChildLoc.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1ChildLoc. rewrite <-HbeqSh1ChildLoc in *. rewrite HlookupSh1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END sh1InChildLocationIsBE *)
  }
  assert(StructurePointerIsKS s).
  { (* BEGIN StructurePointerIsKS s *)
    assert(Hcons0: StructurePointerIsKS s4) by intuition.
    intros partition pdentryPart HlookupPart HbeqStructNull.
    assert(HlookupParts4: lookup partition (memory s4) beqAddr = Some (PDT pdentryPart)).
    {
      rewrite Hs in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
      assumption.
    }
    specialize(Hcons0 partition pdentryPart HlookupParts4 HbeqStructNull). unfold isKS in *. rewrite Hs.
    simpl. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (structure pdentryPart))
      eqn:HbeqSh1Struct.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Struct. rewrite <-HbeqSh1Struct in *. rewrite HlookupSh1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END StructurePointerIsKS *)
  }
  assert(NextKSIsKS s).
  { (* BEGIN NextKSIsKS s *)
    assert(Hcons0: NextKSIsKS s4) by intuition.
    intros kernel nextKSaddr nextKS HkernIsKS HnextAddr HnextKS HbeqNextNull.
    assert(Hkernel: isKS kernel s4 /\ nextKSAddr kernel nextKSaddr s4).
    {
      unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) kernel) eqn:HbeqSh1Kern;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HnextAddr; try(apply not_eq_sym; assumption).
      split; assumption.
    }
    destruct Hkernel as (HkernIsKSs4 & HnextAddrs4).
    assert(HnextKSs4: nextKSentry nextKSaddr nextKS s4).
    {
      unfold nextKSentry in *. rewrite Hs in HnextKS. simpl in HnextKS.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) nextKSaddr) eqn:HbeqSh1Next;
        try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HnextKS; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKSs4 HnextAddrs4 HnextKSs4 HbeqNextNull).
    unfold isKS in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) nextKS) eqn:HbeqSh1Next.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Next. subst nextKS. rewrite HlookupSh1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END NextKSIsKS *)
  }
  assert(NextKSOffsetIsPADDR s).
  { (* BEGIN NextKSOffsetIsPADDR s *)
    assert(Hcons0: NextKSOffsetIsPADDR s4) by intuition.
    intros kernel nextKSaddr HkernIsKS HnextAddr.
    assert(Hkernel: isKS kernel s4 /\ nextKSAddr kernel nextKSaddr s4).
    {
      unfold isKS in *. unfold nextKSAddr in *. rewrite Hs in HkernIsKS. rewrite Hs in HnextAddr. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) kernel) eqn:HbeqSh1Kern;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HnextAddr; try(apply not_eq_sym; assumption).
      split; assumption.
    }
    destruct Hkernel as (HkernIsKSs4 & HnextAddrs4). specialize(Hcons0 kernel nextKSaddr HkernIsKSs4 HnextAddrs4).
    destruct Hcons0 as (HnextIsPADDR & HbeqNextNull). split; try(assumption). unfold isPADDR in *. rewrite Hs.
    simpl. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) nextKSaddr) eqn:HbeqSh1Next.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Next. subst nextKSaddr. rewrite HlookupSh1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END NextKSOffsetIsPADDR *)
  }
  assert(NoDupInFreeSlotsList s).
  { (* BEGIN NoDupInFreeSlotsList s *)
    assert(Hcons0: NoDupInFreeSlotsList s4) by intuition.
    intros partition pdentryPart HlookupPart.
    assert(HlookupPartCopy: lookup partition (memory s) beqAddr = Some (PDT pdentryPart)) by assumption.
    rewrite Hs in HlookupPart. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqSh1Part;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
    specialize(Hcons0 partition pdentryPart HlookupPart).
    destruct Hcons0 as [optionfreeslotslist (Hlist & Hwell & HnoDup)]. exists optionfreeslotslist.
    split; try(split; assumption). rewrite Hlist. apply eq_sym. unfold getFreeSlotsList in *.
    rewrite HlookupPart in *. rewrite HlookupPartCopy.
    destruct (beqAddr (firstfreeslot pdentryPart) nullAddr) eqn:HbeqFirstNull; try(reflexivity).
    rewrite Hs. apply getFreeSlotsListRecEqSHE.
    - assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s4) by intuition.
      rewrite <-beqAddrFalse in HbeqFirstNull.
      specialize(HfirstIsBE partition pdentryPart HlookupPart HbeqFirstNull).
      destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. intro Hcontra.
      rewrite <-Hcontra in *. rewrite HlookupSh1 in *. congruence.
    - unfold isBE. rewrite HlookupSh1. congruence.
    - unfold isPADDR. rewrite HlookupSh1. congruence.
    (* END NoDupInFreeSlotsList *)
  }

  assert(HgetFreeSlotsListEq: forall part, isPDT part s -> getFreeSlotsList part s = getFreeSlotsList part s4).
  {
    intros part HpartIsPDT. unfold getFreeSlotsList.
    assert(HlookupPartEq: lookup part (memory s) beqAddr = lookup part (memory s4) beqAddr).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    unfold isPDT in *. rewrite HlookupPartEq in *.
    destruct (lookup part (memory s4) beqAddr) eqn:HlookupParts4; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; try(reflexivity). rewrite Hs.
    apply getFreeSlotsListRecEqSHE.
    - assert(HfirstIsBE: FirstFreeSlotPointerIsBEAndFreeSlot s4) by intuition.
      rewrite <-beqAddrFalse in HbeqFirstNull. specialize(HfirstIsBE part p HlookupParts4 HbeqFirstNull).
      destruct HfirstIsBE as (HfirstIsBE & _). unfold isBE in HfirstIsBE. intro Hcontra. rewrite <-Hcontra in *.
      rewrite HlookupSh1 in *. congruence.
    - unfold isBE. rewrite HlookupSh1. congruence.
    - unfold isPADDR. rewrite HlookupSh1. congruence.
  }
  assert(HgetKSEntriesEq: forall part, isPDT part s
          -> getKSEntries part s = getKSEntries part s4).
  {
    intros part HpartIsPDT.
    assert(HlookupPartEq: lookup part (memory s) beqAddr = lookup part (memory s4) beqAddr).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. rewrite Hs. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    rewrite Hs. unfold isPDT in *. rewrite HlookupPartEq in *.
    destruct (lookup part (memory s4) beqAddr) eqn:HlookupParts4; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). apply getKSEntriesEqSHE with p; try(assumption).
    unfold isSHE. rewrite HlookupSh1. trivial.
  }
  assert(HgetMappedBlocksEq: forall part, isPDT part s
          -> getMappedBlocks part s = getMappedBlocks part s4).
  {
    intros part HpartIsPDT. unfold getMappedBlocks. rewrite HgetKSEntriesEq; try(assumption). rewrite Hs.
    apply filterPresentEqSHE. unfold isSHE. rewrite HlookupSh1. trivial.
  }
  assert(HgetMappedPaddrEq: forall part, isPDT part s
          -> getMappedPaddr part s = getMappedPaddr part s4).
  {
    intros part HpartIsPDT. unfold getMappedPaddr. rewrite HgetMappedBlocksEq; try(assumption). rewrite Hs.
    apply getAllPaddrAuxEqSHE. unfold isSHE. rewrite HlookupSh1. trivial.
  }
  assert(HgetConfigPaddrEq: forall part, isPDT part s4
          -> getConfigPaddr part s = getConfigPaddr part s4).
  {
    intros part HpartIsPDTs4. rewrite Hs. apply getConfigPaddrEqSHE. assumption. unfold isSHE. rewrite HlookupSh1.
    trivial.
  }
  assert(blockInCurrentPartitionAddr = idBlock) by intuition. subst idBlock.
  assert(HgetChildrenEq: forall part, isPDT part s4 ->
          (forall addr, In addr (getChildren part s) -> In addr (newPDBlockStartAddr::getChildren part s4))).
  {
    intros part HpartIsPart addr. rewrite Hs.
    apply getChildrenEqSHEPDflagTrue with blockInCurrentPartitionAddr sh1entry; try(assumption).
    - intuition.
    - unfold sh1entryAddr. rewrite HlookupBlocks4. reflexivity.
    - assert(bentryStartAddr blockInCurrentPartitionAddr newPDBlockStartAddr s0) by intuition.
      unfold bentryStartAddr in *. rewrite HlookupBlocks4. rewrite HlookupBlocks0 in *. rewrite HnewBentry. simpl.
      assumption.
    - simpl. reflexivity.
  }

  assert(freeSlotsListIsFreeSlot s).
  { (* BEGIN freeSlotsListIsFreeSlot s *)
    assert(Hcons0: freeSlotsListIsFreeSlot s4) by intuition.
    intros partition freeslotaddr optionfreeslotslist freeslotslist HpartIsPDT (HoptList & Hwell)
      (Hlist & HaddrIn) HbeqAddrNull.
    (*destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getFreeSlotsList in HoptList.
      rewrite HlookupNews in HoptList. rewrite HnewPD in HoptList. simpl in HoptList.
      rewrite HoptList in Hlist. simpl in Hlist. rewrite Hlist in HaddrIn. contradict HaddrIn.
    }*)
    assert(HgetFreeEq: getFreeSlotsList partition s = getFreeSlotsList partition s4).
    { apply HgetFreeSlotsListEq; assumption. }
    rewrite HgetFreeEq in HoptList.
    assert(HpartIsPDTs4: isPDT partition s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym); assumption.
    }
    assert(HoptListWells4: optionfreeslotslist = getFreeSlotsList partition s4 /\
       wellFormedFreeSlotsList optionfreeslotslist <> False) by (split; assumption).
    assert(HlistIn: freeslotslist = filterOptionPaddr optionfreeslotslist /\ In freeslotaddr freeslotslist).
    { split; assumption. }
    specialize(Hcons0 partition freeslotaddr optionfreeslotslist freeslotslist HpartIsPDTs4 HoptListWells4
      HlistIn HbeqAddrNull). unfold isFreeSlot in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) freeslotaddr) eqn:HbeqSh1Slot.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1Slot. rewrite HbeqSh1Slot in *. rewrite HlookupSh1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup freeslotaddr (memory s4) beqAddr) eqn:HlookupFree; try(congruence). destruct v; try(congruence).
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (CPaddr (freeslotaddr + sh1offset)))
      eqn:HbeqSh1s.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1s. rewrite <-HbeqSh1s in *. exfalso. unfold CPaddr in HbeqSh1s.
      assert(Hnull: nullAddrExists s4) by intuition. unfold nullAddrExists in Hnull. unfold isPADDR in *.
      unfold CPaddr in HlookupSh1. destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr).
      - destruct (le_dec (freeslotaddr + sh1offset) maxAddr).
        + injection HbeqSh1s as Heq. apply PeanoNat.Nat.add_cancel_r in Heq. apply paddrEqNatEqEquiv in Heq.
          subst freeslotaddr. rewrite HlookupBlocks4 in HlookupFree. injection HlookupFree as HbentriesEq. subst b.
          assert(HfreeIsFrees0: freeSlotsListIsFreeSlot s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
          * rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getFreeSlotsList in *.
            rewrite HlookupNews4 in HoptList. rewrite HnewPDentry in HoptList. simpl in *. subst optionfreeslotslist.
            simpl in *. subst freeslotslist. simpl in *. congruence.
          * assert(HpartIsPDTs0: isPDT partition s0).
            {
              unfold isPDT in *. rewrite Hs4 in HpartIsPDTs4. rewrite Hs3 in HpartIsPDTs4. simpl in *.
              destruct (beqAddr currentPart partition) eqn:HbeqCurrPart.
              - rewrite <-DTL.beqAddrTrue in HbeqCurrPart. subst partition. rewrite HlookupCurrs0. trivial.
              - rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr in *. simpl in *.
                destruct (beqAddr blockInCurrentPartitionAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
                rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HpartIsPDTs4;
                  try(apply not_eq_sym; assumption).
                rewrite removeDupIdentity in HpartIsPDTs4; try(apply not_eq_sym; assumption).
                rewrite HlookupEqs2s0 in HpartIsPDTs4; assumption.
            }
            assert(HgetFreeEqs0: forall part, isPDT part s4 -> beqAddr newPDBlockStartAddr part = false
                    -> getFreeSlotsList part s4 = getFreeSlotsList part s0) by intuition.
            specialize(HgetFreeEqs0 partition HpartIsPDTs4 HbeqStartPart). rewrite HgetFreeEqs0 in HoptListWells4.
            specialize(HfreeIsFrees0 partition blockInCurrentPartitionAddr optionfreeslotslist freeslotslist
              HpartIsPDTs0 HoptListWells4 HlistIn HbeqAddrNull).
            assert(~ isFreeSlot blockInCurrentPartitionAddr s0) by intuition. congruence.
        + rewrite HbeqSh1s in *.
          assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (p freeslotaddr + i sh1offset) n |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (p blockInCurrentPartitionAddr + i sh1offset) n |}
                          = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
          apply proof_irrelevance.
        }
        rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
    destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s4) beqAddr); try(congruence).
    destruct v; try(congruence).
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (CPaddr (freeslotaddr + scoffset)))
      eqn:HbeqSh1FreeSce.
    {
      rewrite <-DTL.beqAddrTrue in HbeqSh1FreeSce. rewrite <-HbeqSh1FreeSce in *. rewrite HlookupSh1 in *.
      congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END freeSlotsListIsFreeSlot *)
  }
  assert(DisjointFreeSlotsLists s).
  { (* BEGIN DisjointFreeSlotsLists s *)
    assert(Hcons0: DisjointFreeSlotsLists s4) by intuition.
    intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
    assert(Hpart1IsPDTs4: isPDT part1 s4).
    {
      unfold isPDT in *. rewrite Hs in Hpart1IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part1) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in Hpart1IsPDT; try(apply not_eq_sym); assumption.
    }
    assert(Hpart2IsPDTs4: isPDT part2 s4).
    {
      unfold isPDT in *. rewrite Hs in Hpart2IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part2) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in Hpart2IsPDT; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 part1 part2 Hpart1IsPDTs4 Hpart2IsPDTs4 HbeqParts).
    assert(HgetFree1Eq: getFreeSlotsList part1 s = getFreeSlotsList part1 s4).
    { apply HgetFreeSlotsListEq; assumption. }
    assert(HgetFree2Eq: getFreeSlotsList part2 s = getFreeSlotsList part2 s4).
    { apply HgetFreeSlotsListEq; assumption. }
    rewrite HgetFree1Eq. rewrite HgetFree2Eq. assumption.
    (* END DisjointFreeSlotsLists *)
  }
  assert(inclFreeSlotsBlockEntries s).
  { (* BEGIN inclFreeSlotsBlockEntries s *)
    assert(Hcons0: inclFreeSlotsBlockEntries s4) by intuition.
    intros partition HpartIsPDT.
    assert(HpartIsPDTs4: isPDT partition s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym); assumption.
    }
    assert(HgetFreePartEq: getFreeSlotsList partition s = getFreeSlotsList partition s4).
    { apply HgetFreeSlotsListEq; assumption. }
    rewrite HgetFreePartEq. rewrite HgetKSEntriesEq; try(assumption).
    specialize(Hcons0 partition HpartIsPDTs4). assumption.
    (* END inclFreeSlotsBlockEntries *)
  }
  assert(DisjointKSEntries s).
  { (* BEGIN DisjointKSEntries s *)
    assert(Hcons0: DisjointKSEntries s4) by intuition.
    intros part1 part2 Hpart1IsPDT Hpart2IsPDT HbeqParts.
    assert(HgetKSPart1Eq: getKSEntries part1 s = getKSEntries part1 s4).
    { apply HgetKSEntriesEq; assumption. }
    rewrite HgetKSPart1Eq.
    assert(Hpart1IsPDTs4: isPDT part1 s4).
    {
      unfold isPDT in *. rewrite Hs in Hpart1IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part1) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in Hpart1IsPDT; try(apply not_eq_sym); assumption.
    }
    assert(HgetKSPart2Eq: getKSEntries part2 s = getKSEntries part2 s4).
    { apply HgetKSEntriesEq; assumption. }
    assert(Hpart2IsPDTs4: isPDT part2 s4).
    {
      unfold isPDT in *. rewrite Hs in Hpart2IsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part2) eqn:HbeqSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in Hpart2IsPDT; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 part1 part2 Hpart1IsPDTs4 Hpart2IsPDTs4 HbeqParts). rewrite HgetKSPart2Eq.
    assumption.
    (* END DisjointKSEntries *)
  }
  assert(HgetMappedBlocksCurrEqs4s0: getMappedBlocks currentPart s4 = getMappedBlocks currentPart s0).
  {
    assert(HbeqStartCurr: beqAddr newPDBlockStartAddr currentPart = false) by (rewrite beqAddrSym; intuition).
    assert(HlookupCurrs4: lookup currentPart (memory s4) beqAddr = Some (PDT newPDCurr)) by intuition.
    assert(Hres: forall part, isPDT part s4 -> beqAddr newPDBlockStartAddr part = false
                  -> getMappedBlocks part s4 = getMappedBlocks part s0) by intuition.
    apply Hres; try(assumption). unfold isPDT. rewrite HlookupCurrs4. trivial.
  }
  assert(Hstart: bentryStartAddr blockInCurrentPartitionAddr newPDBlockStartAddr s0) by intuition.
  assert(HgetPartsEqs4s0: getPartitions multiplexer s4 = getPartitions multiplexer s0) by intuition.
  assert(Hs2: s2 = {|
                     currentPartition := currentPartition s1;
                     memory := add newPDBlockStartAddr (PDT newPDentry) (memory s1) beqAddr
                   |}) by intuition.
  assert(Hs1: s1 = {|
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
  assert(HcurrIsCurr: currentPart = currentPartition s4).
  {
    rewrite Hs4. simpl. rewrite Hs3. simpl. rewrite Hs2. simpl. rewrite Hs1. simpl. intuition.
  }
  assert(HcurrIsParts4: In currentPart (getPartitions multiplexer s4)).
  {
    subst currentPart. intuition.
  }
  assert(HbeqStartBlock: beqAddr newPDBlockStartAddr blockInCurrentPartitionAddr = false) by intuition.
  assert(HlookupCurrs4: lookup currentPart (memory s4) beqAddr = Some (PDT newPDCurr)) by intuition.
  assert(HlookupNews0: lookup newPDBlockStartAddr (memory s0) beqAddr = None) by intuition.
  assert(HPDFlags4: PDflag sh1entry = false).
  {
    assert(HAFlags0: bentryAFlag blockInCurrentPartitionAddr true s0) by intuition.
    assert(HaccessNoPD: AccessibleNoPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HblockIsBEs0: isBE blockInCurrentPartitionAddr s0).
    { unfold isBE. rewrite HlookupBlocks0. trivial. }
    assert(Hsh1s0: sh1entryAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr+sh1offset)) s0).
    { apply lookupSh1EntryAddr with bentry; assumption. }
    specialize(HaccessNoPD blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr+sh1offset))
      HblockIsBEs0 Hsh1s0 HAFlags0). rewrite Hs4 in HlookupSh1. rewrite Hs3 in HlookupSh1.
    rewrite Hs2 in HlookupSh1. rewrite Hs1 in HlookupSh1. simpl in HlookupSh1.
    destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1;
      try(exfalso; congruence). rewrite HbeqBlockCurr in *. simpl in HlookupSh1.
    destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
      eqn:HbeqBlockBlockSh1; try(exfalso; congruence). rewrite beqAddrTrue in *. rewrite HbeqStartBlock in *.
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
    simpl in HlookupSh1. destruct (beqAddr newPDBlockStartAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
      eqn:HbeqStartBlockSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption). unfold sh1entryPDflag in *.
    rewrite HlookupSh1 in *. apply eq_sym. assumption.
  }
  assert(HgetPartsEq: exists list1 list2, getPartitions multiplexer s4 = list1 ++ list2
                  /\ getPartitions multiplexer s = list1 ++ newPDBlockStartAddr :: list2).
  {
    assert(HmultIsParts4: In multiplexer (getPartitions multiplexer s4)).
    {
      unfold getPartitions. replace (maxAddr + 2) with (S (maxAddr + 1)); try(lia). simpl. left. reflexivity.
    }
    rewrite Hs. apply getPartitionsEqSHEPDflagTrueVal with blockInCurrentPartitionAddr currentPart sh1entry;
      try(assumption).
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - intuition.
    - apply lookupSh1EntryAddr with newBentry; assumption.
    - unfold bentryStartAddr in *. rewrite HlookupBlocks4. rewrite HlookupBlocks0 in *. rewrite HnewBentry. simpl.
      assumption.
    - rewrite HgetMappedBlocksCurrEqs4s0. intuition.
    - simpl. reflexivity.
    - intuition.
    - intuition.
    - assert(Hress4: getChildren newPDBlockStartAddr s4 = []).
      {
        unfold getChildren. rewrite HlookupNews4. unfold getMappedBlocks. unfold getKSEntries. rewrite HlookupNews4.
        rewrite HnewPDentry. simpl. unfold getPDs. simpl. reflexivity.
      }
      rewrite <-Hress4. apply getChildrenEqSHENotInList with blockInCurrentPartitionAddr.
      + intuition.
      + unfold isPDT. rewrite HlookupNews4. trivial.
      + unfold isSHE. rewrite HlookupSh1. trivial.
      + apply lookupSh1EntryAddr with newBentry; assumption.
      + intros block Hcontra. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupNews4 in *.
        rewrite HnewPDentry in *. simpl in *. exfalso; congruence.
    - simpl. destruct (beqAddr currentPart multiplexer) eqn:HbeqCurrMult.
      + left. rewrite <-DTL.beqAddrTrue in HbeqCurrMult. assumption.
      + right. rewrite beqAddrSym in *. rewrite <-beqAddrFalse in *.
        apply getPartitionsGivesAncestor with (maxAddr + 2); try(assumption);
          try(unfold isPDT; rewrite HlookupCurrs4; trivial); intuition.
    - unfold getPartitions in HcurrIsParts4. replace (maxAddr + 2) with (S (maxAddr + 1)) in *; try(lia).
      simpl in HcurrIsParts4. unfold isPDT. destruct HcurrIsParts4 as [HmultIsCurr | HcurrIsParts4].
      + rewrite HmultIsCurr. rewrite HlookupCurrs4. trivial.
      + unfold getChildren in HcurrIsParts4. destruct (lookup multiplexer (memory s4) beqAddr); trivial.
        destruct v; trivial.
  }
  destruct HgetPartsEq as [leftList [rightList (HgetPartsEqs4 & HgetPartsEqs)]].
  assert(noDupPartitionTree s).
  { (* BEGIN noDupPartitionTree s*)
    assert(Hcons0: noDupPartitionTree s4) by intuition.
    unfold noDupPartitionTree. unfold noDupPartitionTree in Hcons0.
    assert(HstartNotParts4: ~In newPDBlockStartAddr (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4s0. intro Hcontra. assert(HstartIsPDTs0: isPDT newPDBlockStartAddr s0).
      { apply partitionsArePDT; try(assumption); unfold consistency in *; unfold consistency1 in *; intuition. }
      unfold isPDT in HstartIsPDTs0. rewrite HlookupNews0 in *. congruence.
    }
    rewrite HgetPartsEqs. rewrite HgetPartsEqs4 in *. apply Lib.NoDupSplitInclIff in Hcons0.
    apply Lib.NoDupSplitInclIff. destruct Hcons0 as ((HnoDupLeft & HnoDupRight) & HdisjointLeftRight).
    apply Lib.in_app_or_neg in HstartNotParts4. destruct HstartNotParts4 as (HstartNotInLeft & HstartNotInRight).
    split; try(split; try(assumption)).
    - apply NoDup_cons; assumption.
    - intros part HpartInLeft. simpl. apply Classical_Prop.and_not_or.
      specialize(HdisjointLeftRight part HpartInLeft). split; try(assumption). intro Hcontra. subst part.
      congruence.
    (* END noDupPartitionTree *)
  }
  assert(HblockMappedCurrs0: In blockInCurrentPartitionAddr (getMappedBlocks currentPart s0)) by intuition.
  assert(HcurrIsPDTs4: isPDT currentPart s4).
  { unfold isPDT. rewrite HlookupCurrs4. trivial. }
  assert(HgetChildrenEqs: forall part, In part (getPartitions multiplexer s0)
              -> part <> currentPart
              -> getChildren part s = getChildren part s0).
  {
    assert(HgetChildrenEqs4s0: forall part, In part (getPartitions multiplexer s0)
              -> getChildren part s4 = getChildren part s0) by intuition.
    intros part HpartIsPart HbeqPartCurr. specialize(HgetChildrenEqs4s0 part HpartIsPart).
    rewrite <-HgetChildrenEqs4s0. rewrite Hs. apply getChildrenEqSHENotInList with blockInCurrentPartitionAddr.
    - intuition.
    - apply partitionsArePDT; try(rewrite HgetPartsEqs4s0; assumption); intuition.
    - unfold isSHE. rewrite HlookupSh1. trivial.
    - apply lookupSh1EntryAddr with newBentry; assumption.
    - intros block HblockMappedPart Hsh1. unfold sh1entryAddr in Hsh1.
      destruct (lookup block (memory s4) beqAddr); try(congruence). destruct v; try(congruence).
      unfold CPaddr in Hsh1. unfold CPaddr in HlookupSh1. assert(Hnulls4: nullAddrExists s4) by intuition.
      unfold nullAddrExists in *. unfold isPADDR in *.
      destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr).
      + destruct (le_dec (block + sh1offset) maxAddr).
        * injection Hsh1 as HblocksEq. apply PeanoNat.Nat.add_cancel_r in HblocksEq.
          apply paddrEqNatEqEquiv in HblocksEq. subst block. rewrite <-HgetMappedBlocksCurrEqs4s0 in *.
          assert(HpartsEq: part = currentPart).
          {
            destruct (beqAddr part currentPart) eqn:HbeqParts; try(rewrite DTL.beqAddrTrue; assumption). exfalso.
            rewrite <-beqAddrFalse in HbeqParts. unfold getMappedBlocks in *.
            apply InFilterPresentInList in HblockMappedCurrs0. apply InFilterPresentInList in HblockMappedPart.
            assert(Hdisjoint: DisjointKSEntries s4) by intuition.
            assert(HpartIsPDT: isPDT part s4).
            {
              unfold getKSEntries in HblockMappedPart. unfold isPDT.
              destruct (lookup part (memory s4) beqAddr); try(simpl in *; congruence).
              destruct v; try(simpl in *; congruence). trivial.
            }
            specialize(Hdisjoint part currentPart HpartIsPDT HcurrIsPDTs4 HbeqParts).
            destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
            specialize(Hdisjoint blockInCurrentPartitionAddr HblockMappedPart). congruence.
          }
          congruence.
        * rewrite Hsh1 in *.
          assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      + assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockInCurrentPartitionAddr + sh1offset) n |}
                          = nullAddr).
        {
          unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
        }
        rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
  }
  assert(HgetChildrenCurrEq: exists list1 list2,
           getChildren currentPart s4 = list1 ++ list2
           /\ getChildren currentPart s = list1 ++ newPDBlockStartAddr::list2).
  {
    rewrite Hs. apply getChildrenEqSHEPDflagTrueVal with blockInCurrentPartitionAddr sh1entry; try(assumption).
    - intuition.
    - intuition.
    - apply lookupSh1EntryAddr with newBentry; assumption.
    - unfold bentryStartAddr in *. rewrite HlookupBlocks4. rewrite HlookupBlocks0 in *. rewrite HnewBentry. simpl.
      assumption.
    - rewrite HgetMappedBlocksCurrEqs4s0. assumption.
    - simpl. reflexivity.
  }
  destruct HgetChildrenCurrEq as [leftChildren [rightChildren (HgetChildCurrs4 & HgetChildCurrs)]].
  assert(isParent s).
  { (* BEGIN isParent s *)
    assert(Hcons0: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros child pdparent HparentIsPart HchildIsChild.
    assert(HparentIsParts0: In pdparent (getPartitions multiplexer s0)).
    {
      rewrite HgetPartsEqs in HparentIsPart. rewrite <-HgetPartsEqs4s0. rewrite HgetPartsEqs4. apply in_or_app.
      apply in_app_or in HparentIsPart. destruct HparentIsPart as [Hleft | HparentIsPartR]; try(left; assumption).
      simpl in HparentIsPartR. destruct HparentIsPartR as [Hcontra | Hright]; try(right; assumption). exfalso.
      subst pdparent. unfold getChildren in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
      rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *. congruence.
    }
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    - rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child.
      assert(HpartsEq: pdparent = currentPart).
      {
        destruct (beqAddr pdparent currentPart) eqn:HbeqParentCurr; try(rewrite DTL.beqAddrTrue; assumption).
        exfalso. rewrite <-beqAddrFalse in HbeqParentCurr. rewrite HgetChildrenEqs in HchildIsChild; try(assumption).
        specialize(Hcons0 newPDBlockStartAddr pdparent HparentIsParts0 HchildIsChild). unfold pdentryParent in *.
        rewrite HlookupNews0 in *. congruence.
      }
      subst pdparent. unfold pdentryParent. rewrite HlookupNews. rewrite HnewPDentry. simpl. reflexivity.
    - rewrite <-beqAddrFalse in HbeqStartChild.
      assert(HchildIsChilds0: In child (getChildren pdparent s0)).
      {
        assert(HgetChildrenEqs4s0: forall part, In part (getPartitions multiplexer s0)
              -> getChildren part s4 = getChildren part s0) by intuition.
        rewrite <-HgetChildrenEqs4s0; try(assumption). destruct (beqAddr pdparent currentPart) eqn:HbeqParentCurr.
        - rewrite <-DTL.beqAddrTrue in HbeqParentCurr. subst pdparent. rewrite HgetChildCurrs in *.
          rewrite HgetChildCurrs4. apply in_or_app. apply in_app_or in HchildIsChild.
          destruct HchildIsChild as [HleftChildren | HchildIsChildR]; try(left; assumption). right. simpl in *.
          destruct HchildIsChildR as [Hcontra | HrightChildren]; try(assumption). exfalso; congruence.
        - rewrite <-beqAddrFalse in *. rewrite HgetChildrenEqs in HchildIsChild; try(assumption).
          rewrite HgetChildrenEqs4s0; assumption.
      }
      specialize(Hcons0 child pdparent HparentIsParts0 HchildIsChilds0).
      unfold pdentryParent in *. rewrite Hs. rewrite Hs4. rewrite Hs3. simpl.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child) eqn:HbeqBlockSh1Child.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Child. subst child. rewrite Hs4 in HlookupSh1.
        rewrite Hs3 in HlookupSh1. simpl in HlookupSh1.
        destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1;
          try(congruence). rewrite HbeqBlockCurr in *. simpl in HlookupSh1.
        destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1; try(congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
        rewrite HlookupEqs2s0 in HlookupSh1; try(assumption). rewrite HlookupSh1 in *. congruence.
      }
      destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite <-HbeqCurrBlockSh1 in *. exfalso; congruence.
      }
      rewrite HbeqBlockCurr. simpl. destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
      + rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. rewrite HnewPDCurr. rewrite HlookupCurrs0 in *.
        simpl. assumption.
      + destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
        {
          exfalso. rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *. congruence.
        }
        simpl. destruct (beqAddr blockInCurrentPartitionAddr child) eqn:HbeqBlockChild.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockChild. subst child. rewrite HlookupBlocks0 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; assumption.
    (* END isParent *)
  }
  assert(isChild s).
  { (* BEGIN isChild s *)
    assert(Hcons0: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros child pdparent HchildIsPart HparentIsParent HbeqChildRoot.
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    - rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child. unfold pdentryParent in *. rewrite HlookupNews in *.
      rewrite HnewPDentry in *. simpl in *. subst pdparent. rewrite HgetChildCurrs. apply in_or_app. right. simpl.
      left. reflexivity.
    - rewrite <-beqAddrFalse in HbeqStartChild. assert(HchildIsParts0: In child (getPartitions multiplexer s0)).
      {
        rewrite <-HgetPartsEqs4s0. rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HchildIsPart. apply in_or_app.
        apply in_app_or in HchildIsPart. simpl in *.
        destruct HchildIsPart as [HchildIsLeft | HchildIsPartR]; try(left; assumption).
        destruct HchildIsPartR as [Hcontra | HchildIsRight]; try(right; assumption). subst child. exfalso; congruence.
      }
      assert(HparentIsParents0: pdentryParent child pdparent s0).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. rewrite Hs4 in HparentIsParent.
        rewrite Hs3 in HparentIsParent. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child) eqn:HbeqBlockSh1Child;
          try(exfalso; congruence).
        destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite <-HbeqCurrBlockSh1 in *. exfalso; congruence.
        }
        rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. rewrite HlookupCurrs0. rewrite HnewPDCurr in *.
          simpl in *. assumption.
        - destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
          {
            exfalso. rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *. congruence.
          }
          simpl in *.
          destruct (beqAddr blockInCurrentPartitionAddr child) eqn:HbeqBlockChild; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in HparentIsParent; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HparentIsParent; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HparentIsParent; try(apply not_eq_sym; assumption).
          rewrite <-HlookupEqs2s0; assumption.
      }
      specialize(Hcons0 child pdparent HchildIsParts0 HparentIsParents0 HbeqChildRoot).
      destruct (beqAddr pdparent currentPart) eqn:HbeqParentCurr.
      + rewrite <-DTL.beqAddrTrue in HbeqParentCurr. subst pdparent. rewrite HgetChildCurrs.
        assert(HgetChildrenEqs4s0: forall part, In part (getPartitions multiplexer s0)
                -> getChildren part s4 = getChildren part s0) by intuition.
        rewrite <-HgetChildrenEqs4s0 in Hcons0; try(rewrite <-HgetPartsEqs4s0; assumption).
        rewrite HgetChildCurrs4 in Hcons0. apply in_or_app. apply in_app_or in Hcons0.
        destruct Hcons0 as [Hleft | Hright]; try(left; assumption). right. simpl. right. assumption.
      + assert(HgetChildrenParentEq: getChildren pdparent s = getChildren pdparent s0).
        {
          rewrite <-beqAddrFalse in *. apply HgetChildrenEqs; try(assumption).
          assert(HparentOfPart: parentOfPartitionIsPartition s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          apply partitionsArePDT in HchildIsParts0; try(unfold consistency in *; unfold consistency1 in *; intuition;
            congruence). unfold isPDT in *.
          destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). specialize(HparentOfPart child p HlookupChild).
          destruct HparentOfPart as (HparentIsPart & _ & _). specialize(HparentIsPart HbeqChildRoot).
          destruct HparentIsPart as (_ & HparentIsPart). unfold pdentryParent in *. rewrite HlookupChild in *.
          subst pdparent. assumption.
        }
        rewrite HgetChildrenParentEq. assumption.
    (* END isChild *)
  }
  assert(noDupKSEntriesList s).
  { (* BEGIN noDupKSEntriesList s *)
    assert(Hcons0: noDupKSEntriesList s4) by intuition.
    intros partition HpartIsPDT.
    assert(HpartIsPDTs0: isPDT partition s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 partition HpartIsPDTs0). rewrite HgetKSEntriesEq; assumption.
    (* END noDupKSEntriesList *)
  }
  assert(noDupMappedBlocksList s).
  { (* BEGIN noDupMappedBlocksList s *)
    assert(Hcons0: noDupMappedBlocksList s4) by intuition.
    intros partition HpartIsPDT.
    assert(HpartIsPDTs0: isPDT partition s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 partition HpartIsPDTs0). rewrite HgetMappedBlocksEq; assumption.
    (* END noDupMappedBlocksList *)
  }
  assert(wellFormedBlock s).
  { (* BEGIN wellFormedBlock s *)
    assert(Hcons0: wellFormedBlock s4) by intuition.
    intros block startaddr endaddr HPFlag HstartBis HendBis. unfold bentryPFlag in *. unfold bentryStartAddr in *.
    unfold bentryEndAddr in *. rewrite Hs in HPFlag. rewrite Hs in HstartBis. rewrite Hs in HendBis. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqCurBlockBis;
      try(exfalso; congruence).
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HPFlag; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HstartBis; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HendBis; try(apply not_eq_sym; assumption).
    specialize(Hcons0 block startaddr endaddr HPFlag HstartBis HendBis). assumption.
    (* END wellFormedBlock *)
  }
  assert(parentOfPartitionIsPartition s).
  { (* BEGIN parentOfPartitionIsPartition s *)
    assert(Hcons0: parentOfPartitionIsPartition s4) by intuition.
    intros partition pdentryPart HlookupPart. rewrite Hs in HlookupPart. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqBlockSh1Part;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption).
    specialize(Hcons0 partition pdentryPart HlookupPart).
    destruct Hcons0 as (HparentIsPart & HparentOfRoot & HbeqParentPart). split; try(split; assumption).
    intro HbeqPartRoot. specialize(HparentIsPart HbeqPartRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). rewrite HgetPartsEqs.
    split.
    - rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (parent pdentryPart))
        eqn:HbeqBlockSh1Parent.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Parent. rewrite <-HbeqBlockSh1Parent in *. exfalso; congruence.
      }
      exists parentEntry. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
    - rewrite HgetPartsEqs4 in HparentIsPart. apply in_or_app. simpl. apply in_app_or in HparentIsPart.
      destruct HparentIsPart as [HparentIsLeft | HparentIsRight]; try(left; assumption). right. right. assumption.
    (* END parentOfPartitionIsPartition *)
  }
  assert(NbFreeSlotsISNbFreeSlotsInList s).
  { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
    assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s4) by intuition. intros partition nbfree HpartIsPDT HnbFree.
    assert(Hparts0: isPDT partition s4 /\ pdentryNbFreeSlots partition nbfree s4).
    {
      unfold isPDT in *. unfold pdentryNbFreeSlots in *. rewrite Hs in HpartIsPDT. rewrite Hs in HnbFree. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HnbFree; try(apply not_eq_sym; assumption). split; assumption.
    }
    destruct Hparts0 as (HpartIsPDTs0 & HnbFrees0). specialize(Hcons0 partition nbfree HpartIsPDTs0 HnbFrees0).
    rewrite HgetFreeSlotsListEq; assumption.
    (* END NbFreeSlotsISNbFreeSlotsInList *)
  }
  assert(HisListOfKernelsEq: forall part kernList, isListOfKernels kernList part s
    -> isListOfKernels kernList part s4).
  {
    intros part kernList. rewrite Hs. apply isListOfKernelsEqSHE; try(assumption).
  }
  assert(maxNbPrepareIsMaxNbKernels s).
  { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
    assert(Hcons0: maxNbPrepareIsMaxNbKernels s4) by intuition.
    intros partition kernList HkernList.
    assert(HkernLists0: isListOfKernels kernList partition s4).
    { apply HisListOfKernelsEq; assumption. }
    specialize(Hcons0 partition kernList HkernLists0). assumption.
    (* END maxNbPrepareIsMaxNbKernels *)
  }
  assert(blockInChildHasAtLeastEquivalentBlockInParent s).
  { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
    assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s4) by intuition.
    intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild
      HendChild HPFlagChild.
    assert(HparentIsParts0: In pdparent (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs in HparentIsPart. rewrite HgetPartsEqs4. apply in_or_app.
      apply in_app_or in HparentIsPart. destruct HparentIsPart as [Hleft | HparentIsPartR]; try(left; assumption).
      simpl in HparentIsPartR. destruct HparentIsPartR as [Hcontra | Hright]; try(right; assumption). exfalso.
      subst pdparent. unfold getChildren in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
      rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *. congruence.
    }
    assert(HparentIsPDTs: isPDT pdparent s).
    { apply partitionsArePDT; assumption. }
    assert(HchildIsPDTs: isPDT child s).
    { apply childrenArePDT with pdparent; assumption. }
    rewrite HgetMappedBlocksEq in HblockMappedChild; try(assumption). rewrite HgetMappedBlocksEq; try(assumption).
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s4) beqAddr).
    {
      rewrite Hs. unfold bentryStartAddr in HstartChild. rewrite Hs in HstartChild. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqBlockSh1Block;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite HlookupBlockEq in *.
    assert(HchildIsChilds0: In child (getChildren pdparent s4)).
    {
      apply HgetChildrenEq in HchildIsChild.
      - simpl in *. destruct HchildIsChild as [Hcontra | Hres]; try(assumption). subst child.
        unfold getMappedBlocks in HblockMappedChild. unfold getKSEntries in HblockMappedChild.
        rewrite HlookupNews4 in *. rewrite HnewPDentry in *. simpl in *. exfalso; congruence.
      - unfold isPDT in *. rewrite Hs in HparentIsPDTs. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) pdparent) eqn:HbeqBlockSh1Parent;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HparentIsPDTs; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 pdparent child block startChild endChild HparentIsParts0 HchildIsChilds0 HblockMappedChild
      HstartChild HendChild HPFlagChild).
    destruct Hcons0 as [blockParent [startParent [endParent (HblockParentMapped & HstartParent & HendParent &
      Hbounds)]]]. exists blockParent. exists startParent. exists endParent. split. assumption.
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockParent) eqn:HbeqBlockSh1Block.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Block. subst blockParent. rewrite HlookupSh1 in *.
      exfalso; congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). intuition.
    (* END blockInChildHasAtLeastEquivalentBlockInParent *)
  }
  assert(partitionTreeIsTree s).
  { (* BEGIN partitionTreeIsTree s *)
    assert(Hcons0: partitionTreeIsTree s4) by intuition.
    intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
    assert(HparentsLists4: isParentsList s4 parentsList pdparent).
    {
      rewrite Hs in HparentsList. apply isParentsListEqSHERev with (CPaddr (blockInCurrentPartitionAddr + sh1offset))
        {| PDchild := PDchild sh1entry; PDflag := true; inChildLocation := inChildLocation sh1entry |} sh1entry;
        try(assumption).
      - assert(HparentOfPart: parentOfPartitionIsPartition s) by assumption. unfold pdentryParent in HparentIsParent.
        destruct (lookup child (memory s) beqAddr) eqn:HlookupChilds; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst pdparent. specialize(HparentOfPart child p HlookupChilds).
        destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqChildRoot).
        destruct HparentIsPart as (Hres & _). destruct Hres as [pdentryPdparent HlookupParent].
        exists pdentryPdparent. rewrite Hs in HlookupParent. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (parent p)) eqn:HbeqBlockSh1Parent;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HlookupParent; try(apply not_eq_sym; assumption). assumption.
      - intuition.
    }
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    - rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child.
      assert(HparentsListCons: forall parentsList part, beqAddr newPDBlockStartAddr part = false
              -> isParentsList s4 parentsList part
              -> isParentsList s0 parentsList part) by intuition.
      assert(HbeqStartParent: beqAddr newPDBlockStartAddr pdparent = false).
      {
        rewrite <-beqAddrFalse. assert(HparentOfPart: parentOfPartitionIsPartition s) by assumption.
        unfold pdentryParent in HparentIsParent. rewrite HlookupNews in *. subst pdparent.
        specialize(HparentOfPart newPDBlockStartAddr newPDentry HlookupNews). apply not_eq_sym. apply HparentOfPart.
      }
      specialize(HparentsListCons parentsList pdparent HbeqStartParent HparentsLists4). clear HparentsList.
      clear HparentsLists4. clear HparentIsParent. revert pdparent HbeqStartParent HparentsListCons.
      induction parentsList; intros.
      + simpl. congruence.
      + simpl in *. apply Classical_Prop.and_not_or.
        destruct (lookup a5 (memory s0) beqAddr) eqn:HlookupA; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). destruct HparentsListCons as (_ & _ & HparentsListCons).
        destruct (beqAddr newPDBlockStartAddr a5) eqn:HbeqStartA.
        {
          rewrite <-DTL.beqAddrTrue in HbeqStartA. subst a5. exfalso; congruence.
        }
        specialize(IHparentsList a5 HbeqStartA HparentsListCons). rewrite beqAddrSym in *.
        rewrite <-beqAddrFalse in *. split; assumption.
    - assert(HchildIsParts0: In child (getPartitions multiplexer s4)).
      {
        rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HchildIsPart. apply in_app_or in HchildIsPart. apply in_or_app.
        simpl in *. destruct HchildIsPart as [HchildIsLeft | HchildIsPartR]; try(left; assumption).
        destruct HchildIsPartR as [Hcontra | HchildIsRight]; try(right; assumption). rewrite <-beqAddrFalse in *.
        exfalso; congruence.
      }
      assert(HparentIsParents0: pdentryParent child pdparent s4).
      {
        unfold pdentryParent in *. rewrite Hs in HparentIsParent. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child) eqn:HbeqBlockSh1Child;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HparentIsParent; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsParts0 HparentIsParents0 HparentsLists4).
      assumption.
    (* END partitionTreeIsTree *)
  }
  assert(kernelEntriesAreValid s).
  { (* BEGIN kernelEntriesAreValid s *)
    assert(Hcons0: kernelEntriesAreValid s4) by intuition. intros kernel idx HkernIsKS Hindex.
    assert(HkernIsKSs0: isKS kernel s4).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) kernel) eqn:HbeqBlockSh1Kern;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym; assumption). assumption.
    }
    specialize(Hcons0 kernel idx HkernIsKSs0 Hindex). unfold isBE in *. rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (CPaddr (kernel + idx)))
      eqn:HbeqBlockSh1KernIdx.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockSh1KernIdx. rewrite HbeqBlockSh1KernIdx in *. rewrite HlookupSh1 in *.
      congruence.
    }
    simpl. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
    (* END kernelEntriesAreValid *)
  }
  assert(nextKernelIsValid s).
  { (* BEGIN nextKernelIsValid s *)
    assert(Hcons0: nextKernelIsValid s4) by intuition. intros kernel HkernIsKS.
    assert(HkernIsKSs0: isKS kernel s4).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) kernel) eqn:HbeqBlockSh1Kern;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 kernel HkernIsKSs0).
    destruct Hcons0 as (HnewtBounded & [nextAddr (HlookupNext & HnextIsKS)]). split. assumption. exists nextAddr.
    split.
    - intro Hp. specialize(HlookupNext Hp). rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) {| p := kernel + nextoffset; Hp := Hp |})
        eqn:HbeqBlockSh1Next.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Next. rewrite <-HbeqBlockSh1Next in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). assumption.
    - destruct HnextIsKS as [HnextIsKS | HnextIsNull]; try(right; assumption). left. unfold isKS in *.
      rewrite Hs. simpl. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) nextAddr)
        eqn:HbeqBlockSh1Next.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Next. rewrite <-HbeqBlockSh1Next in *. rewrite HlookupSh1 in *.
        congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END nextKernelIsValid *)
  }
  assert(noDupListOfKerns s).
  { (* BEGIN noDupListOfKerns s *)
    assert(Hcons0: noDupListOfKerns s4) by intuition.
    intros partition kernList HkernList.
    assert(HkernLists0: isListOfKernels kernList partition s4).
    { apply HisListOfKernelsEq; assumption. }
    specialize(Hcons0 partition kernList HkernLists0). assumption.
    (* END noDupListOfKerns *)
  }
  assert(MPUsizeIsBelowMax s).
  { (* BEGIN MPUsizeIsBelowMax s *)
    assert(Hcons0: MPUsizeIsBelowMax s4) by intuition. intros partition MPUlist HMPUPart.
    assert(HMPUParts0: pdentryMPU partition MPUlist s4).
    {
      unfold pdentryMPU in *. rewrite Hs in HMPUPart. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HMPUPart; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 partition MPUlist HMPUParts0). assumption.
    (* END MPUsizeIsBelowMax *)
  }
  assert(originIsParentBlocksStart s).
  { (* BEGIN originIsParentBlocksStart s *)
    assert(Hcons0: originIsParentBlocksStart s4) by intuition.
    intros partition pdentryPart block scentryaddr scorigin HpartIsPart HlookupPart HblockMappedPart Hsce
      Horigin.
    destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getMappedBlocks in HblockMappedPart.
      unfold getKSEntries in HblockMappedPart. rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *.
      exfalso; congruence.
    }
    assert(HpartIsParts0: In partition (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HpartIsPart. apply in_or_app. apply in_app_or in HpartIsPart.
      simpl in *. destruct HpartIsPart as [HlartIsLeft | HpartIsPartR]; try(left; assumption).
      rewrite <-beqAddrFalse in *. destruct HpartIsPartR as [Hcontra | HpartIsRight]; try(right; assumption).
      exfalso; congruence.
    }
    assert(Horigins0: scentryOrigin scentryaddr scorigin s4).
    {
      unfold scentryOrigin in *. rewrite Hs in Horigin. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) scentryaddr) eqn:HbeqBlockSh1Sce;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in Horigin; try(apply not_eq_sym); assumption.
    }
    assert(HlookupParts0: lookup partition (memory s4) beqAddr = Some (PDT pdentryPart)).
    {
      rewrite Hs in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
    }
    assert(HpartIsPDT: isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial).
    rewrite HgetMappedBlocksEq in HblockMappedPart; try(assumption).
    specialize(Hcons0 partition pdentryPart block scentryaddr scorigin HpartIsParts0 HlookupParts0
      HblockMappedPart Hsce Horigins0). destruct Hcons0 as (HblockParent & HstartAbove).
    assert(HlookupBlocksEq: forall blockBis, isBE blockBis s
            -> lookup blockBis (memory s) beqAddr = lookup blockBis (memory s4) beqAddr).
    {
      intros blockBis HblockIsBE. unfold isBE in HblockIsBE. rewrite Hs. rewrite Hs in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockBis) eqn:HbeqBlockSh1BlockBis;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    assert(HblockIsBE: isBE block s).
    {
      rewrite <-HgetMappedBlocksEq in HblockMappedPart; try(assumption).
      apply mappedBlockIsBE in HblockMappedPart. destruct HblockMappedPart as [bentryBlock (HlookupBlock & _)].
      unfold isBE. rewrite HlookupBlock. trivial.
    }
    split.
    - intro HbeqPartRoot. specialize(HblockParent HbeqPartRoot).
      destruct HblockParent as [blockParent (HblockParentMapped & HstartParent & Hincl)]. exists blockParent.
      assert(HparentIsPDT: isPDT (parent pdentryPart) s).
      {
        assert(HparentOfPart: parentOfPartitionIsPartition s) by assumption.
        specialize(HparentOfPart partition pdentryPart HlookupPart).
        destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HbeqPartRoot).
        destruct HparentIsPart as ([parentEntry HlookupParent] & _). unfold isPDT.
        rewrite HlookupParent. trivial.
      }
      assert(HblockPIsBE: isBE blockParent s).
      {
        rewrite <-HgetMappedBlocksEq in HblockParentMapped; try(assumption).
        apply mappedBlockIsBE in HblockParentMapped.
        destruct HblockParentMapped as [bentryBlock (HlookupBlock & _)].
        unfold isBE. rewrite HlookupBlock. trivial.
      }
      rewrite HgetMappedBlocksEq; try(assumption). split. assumption. unfold bentryStartAddr. simpl.
      rewrite HlookupBlocksEq; try(assumption). split. assumption. rewrite HlookupBlocksEq; assumption.
    - unfold bentryStartAddr. rewrite HlookupBlocksEq; assumption.
    (* END originIsParentBlocksStart *)
  }
  assert(HlookupBlocksEq: forall blockBis, isBE blockBis s
          -> lookup blockBis (memory s) beqAddr = lookup blockBis (memory s4) beqAddr).
  {
    intros blockBis HblockIsBE. unfold isBE in HblockIsBE. rewrite Hs. rewrite Hs in HblockIsBE. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockBis) eqn:HbeqBlockSh1BlockBis;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
  }
  assert(nextImpliesBlockWasCut s).
  { (* BEGIN nextImpliesBlockWasCut s *)
    assert(Hcons0: nextImpliesBlockWasCut s4) by intuition.
    intros partition pdentryPart block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMappedPart
      Hend Hsce HbeqNextNull Hnext HbeqPartRoot.
    destruct (beqAddr newPDBlockStartAddr partition) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst partition. unfold getMappedBlocks in HblockMappedPart.
      unfold getKSEntries in HblockMappedPart. rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *.
      exfalso; congruence.
    }
    assert(HpartIsPDT: isPDT partition s) by (unfold isPDT; rewrite HlookupPart; trivial).
    rewrite HgetMappedBlocksEq in HblockMappedPart; try(assumption).
    assert(HpartIsParts4: In partition (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HpartIsPart. apply in_or_app. apply in_app_or in HpartIsPart.
      simpl in *. destruct HpartIsPart as [HpartIsLeft | HpartIsPartR]; try(left; assumption).
      destruct HpartIsPartR as [Hcontra | HpartIsRight]; try(right; assumption). rewrite <-beqAddrFalse in *.
      congruence.
    }
    assert(HlookupParts0: lookup partition (memory s4) beqAddr = Some (PDT pdentryPart)).
    {
      rewrite Hs in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) partition) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym; assumption). assumption.
    }
    assert(Hnexts0: scentryNext scentryaddr scnext s4).
    {
      unfold scentryNext in *. rewrite Hs in Hnext. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) scentryaddr) eqn:HbeqBlockSh1Sce;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in Hnext; try(apply not_eq_sym); assumption.
    }
    assert(HparentOfPart: parentOfPartitionIsPartition s) by assumption.
    specialize(HparentOfPart partition pdentryPart HlookupPart).
    destruct HparentOfPart as (HparentIsPart & _ & HbeqParentPart). specialize(HparentIsPart HbeqPartRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
    assert(HblockIsBE: isBE block s).
    {
      rewrite <-HgetMappedBlocksEq in HblockMappedPart; try(assumption).
      apply mappedBlockIsBE in HblockMappedPart. destruct HblockMappedPart as [bentryBlock (HlookupBlock & _)].
      unfold isBE. rewrite HlookupBlock. trivial.
    }
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s4) beqAddr).
    { apply HlookupBlocksEq; assumption. }
    unfold bentryEndAddr in Hend. rewrite HlookupBlockEq in Hend.
    specialize(Hcons0 partition pdentryPart block scentryaddr scnext endaddr HpartIsParts4 HlookupParts0
      HblockMappedPart Hend Hsce HbeqNextNull Hnexts0 HbeqPartRoot).
    destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & HendBounded & Hincl)]].
    exists blockParent. exists endParent.
    assert(HparentIsPDT: isPDT (parent pdentryPart) s) by (unfold isPDT; rewrite HlookupParent; trivial).
    assert(HblockPIsBE: isBE blockParent s).
    {
      rewrite <-HgetMappedBlocksEq in HblockParentMapped; try(assumption).
      apply mappedBlockIsBE in HblockParentMapped.
      destruct HblockParentMapped as [bentryBlock (HlookupBlock & _)].
      unfold isBE. rewrite HlookupBlock. trivial.
    }
    rewrite HgetMappedBlocksEq; try(assumption). split. assumption. simpl in *. rewrite HlookupBlockEq.
    assert(HlookupBlockPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s4) beqAddr).
    { apply HlookupBlocksEq; assumption. }
    unfold bentryEndAddr. rewrite HlookupBlockPEq. split. assumption. split; assumption.
    (* END nextImpliesBlockWasCut *)
  }
  assert(blocksAddressesTypes s).
  { (* BEGIN blocksAddressesTypes s *)
    assert(Hcons0: blocksAddressesTypes s4) by intuition. intros block startaddr endaddr HstartBis HendBis HPDchild.
    assert(Hblock: bentryStartAddr block startaddr s4 /\ bentryEndAddr block endaddr s4).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. 
      assert(isBE block s).
      {
        unfold isBE. unfold bentryStartAddr in *. destruct (lookup block (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      rewrite HlookupBlocksEq in HstartBis; try(assumption). rewrite HlookupBlocksEq in HendBis; try(assumption).
      split; assumption.
    }
    assert(HPDchilds0: sh1entryPDchild (CPaddr (block + sh1offset)) nullAddr s4).
    {
      unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in *.
      assert(Hnull: nullAddrExists s4) by intuition. unfold nullAddrExists in *. unfold isPADDR in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (CPaddr (block + sh1offset)))
        eqn:HbeqBlockSh1Sh1.
      - rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Sh1. unfold CPaddr in HbeqBlockSh1Sh1. unfold CPaddr in HlookupSh1.
        destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr) eqn:HleBlockSh1.
        + destruct (le_dec (block + sh1offset) maxAddr).
          * injection HbeqBlockSh1Sh1 as HblocksEq. apply PeanoNat.Nat.add_cancel_r in HblocksEq.
            apply paddrEqNatEqEquiv in HblocksEq. subst block. unfold CPaddr. rewrite HleBlockSh1. rewrite HlookupSh1.
            simpl in *. assumption.
          * rewrite HbeqBlockSh1Sh1 in *.
            assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            exfalso. rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
        + assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockInCurrentPartitionAddr + sh1offset) n |}
                  = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          exfalso. rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym); assumption.
    }
    destruct Hblock as (Hstarts0 & Hends0). specialize(Hcons0 block startaddr endaddr Hstarts0 Hends0 HPDchilds0).
    destruct Hcons0 as [(HKS & HotherAddr) | [(HPDT & HotherAddr) | Hnull]].
    - left. split.
      + unfold isKS in *. rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) startaddr) eqn:HbeqBlockSh1StartBis.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSh1StartBis. subst startaddr. rewrite HlookupSh1 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      + intros addr HaddrInRange. specialize(HotherAddr addr HaddrInRange).
        destruct HotherAddr as [HBE | [HSHE | HSCE]].
        * left. unfold isBE in *. rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) addr) eqn:HbeqBlockSh1Addr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Addr. subst addr. rewrite HlookupSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
        * right. left. unfold isSHE in *. rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) addr) eqn:HbeqBlockSh1Addr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Addr. subst addr. rewrite HlookupSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
        * right. right. unfold isSCE in *. rewrite Hs. simpl.
          destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) addr) eqn:HbeqBlockSh1Addr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Addr. subst addr. rewrite HlookupSh1 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    - right. left. split.
      + unfold isPDT in *. rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) startaddr) eqn:HbeqBlockSh1StartBis.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSh1StartBis. subst startaddr. rewrite HlookupSh1 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
      + intros addr HaddrInRange. specialize(HotherAddr addr HaddrInRange).
        destruct HaddrInRange as (HaddrInRange & HbeqAddrStart). rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) addr) eqn:HbeqBlockSh1Addr.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Addr. subst addr. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    - right. right. intros addr HaddrInRange. specialize(Hnull addr HaddrInRange). rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) addr) eqn:HbeqBlockSh1Addr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Addr. subst addr. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END blocksAddressesTypes *)
  }
  assert(HlookupSh1s0: lookup (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (memory s0) beqAddr
          = Some (SHE sh1entry)).
  {
    assert(HbeqStartBlockSh1: newPDBlockStartAddr <> CPaddr (blockInCurrentPartitionAddr + sh1offset)).
    { intro Hcontra. rewrite <-Hcontra in *. congruence. }
    rewrite Hs4 in HlookupSh1. rewrite Hs3 in HlookupSh1. simpl in *.
    destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1;
      try(exfalso; congruence). rewrite HbeqBlockCurr in *. simpl in *.
    destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
      eqn:HbeqBlockBlockSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
    rewrite removeDupIdentity in HlookupSh1; try(apply not_eq_sym; assumption).
    rewrite HlookupEqs2s0 in HlookupSh1; assumption.
  }
  assert(HlookupNewPDs2: lookup newPDBlockStartAddr (memory s2) beqAddr = Some (PDT newPDentry)) by intuition.
  assert(notPDTIfNotPDflag s).
  { (* BEGIN notPDTIfNotPDflag s *)
    assert(Hcons0: notPDTIfNotPDflag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block startaddr sh1entryaddr HstartBis Hsh1Bis HPDflag HPDchild.
    assert(Hblocks0: bentryStartAddr block startaddr s0 /\ sh1entryAddr block sh1entryaddr s0).
    {
      destruct (beqAddr blockInCurrentPartitionAddr block) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold bentryStartAddr in *.
        unfold sh1entryAddr in *. rewrite HlookupBlocks in *. rewrite HlookupBlocks0. rewrite HnewBentry in *.
        simpl in *. split; assumption.
      - unfold bentryStartAddr in *. unfold sh1entryAddr in *.
        assert(HblockIsBEs: isBE block s).
        {
          unfold isBE. unfold bentryStartAddr in *. destruct (lookup block (memory s) beqAddr); try(congruence).
          destruct v; try(congruence). trivial.
        }
        specialize(HlookupBlocksEq block HblockIsBEs). unfold isBE in *. rewrite HlookupBlocksEq in *.
        assert(HlookupBlocksEqs4s0: forall blockBis, beqAddr blockInCurrentPartitionAddr blockBis = false
                -> isBE blockBis s4
                -> lookup blockBis (memory s4) beqAddr = lookup blockBis (memory s0) beqAddr) by intuition.
        specialize(HlookupBlocksEqs4s0 block HbeqBlocks HblockIsBEs). rewrite HlookupBlocksEqs4s0 in *.
        split; assumption.
    }
    destruct Hblocks0 as (Hstarts0 & Hsh1Biss0).
    assert(HPDss0: sh1entryPDflag sh1entryaddr false s0 /\ sh1entryPDchild sh1entryaddr nullAddr s0).
    {
      unfold sh1entryPDflag in *. unfold sh1entryPDchild in *. rewrite Hs in HPDflag. rewrite Hs4 in HPDflag.
      rewrite Hs3 in HPDflag. rewrite Hs in HPDchild. rewrite Hs4 in HPDchild. rewrite Hs3 in HPDchild. simpl in *.
      assert(Hnull: nullAddrExists s4) by intuition. unfold nullAddrExists. unfold isPADDR in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
      - simpl in *. exfalso; congruence.
      - destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1.
        { rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite HbeqCurrBlockSh1 in *. exfalso; congruence. }
        rewrite HbeqBlockCurr in *. simpl in *.
        destruct (beqAddr currentPart sh1entryaddr) eqn:HbeqCurrSh1; try(exfalso; congruence).
        destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite HbeqBlockBlockSh1 in *. exfalso; congruence. }
        simpl in *.
        destruct (beqAddr blockInCurrentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HPDflag; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPDflag; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPDflag; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym; assumption).
        assert(HbeqStartSh1: newPDBlockStartAddr <> sh1entryaddr).
        {
          intro Hcontra. rewrite <-Hcontra in *. intuition. rewrite HlookupNewPDs2 in *. congruence.
        }
        split.
        rewrite HlookupEqs2s0 in HPDflag; assumption.
        rewrite HlookupEqs2s0 in HPDchild; assumption.
    }
    destruct HPDss0 as (HPDflags0 & HPDchilds0).
    specialize(Hcons0 block startaddr sh1entryaddr Hstarts0 Hsh1Biss0 HPDflags0 HPDchilds0). contradict Hcons0.
    unfold isPDT in *. rewrite Hs in Hcons0. rewrite Hs4 in Hcons0. rewrite Hs3 in Hcons0. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) startaddr) eqn:HbeqBlockSh1StartA;
      try(exfalso; congruence).
    destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1.
    { rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite HbeqCurrBlockSh1 in *. exfalso; congruence. }
    rewrite HbeqBlockCurr in *. simpl in *. destruct (beqAddr currentPart startaddr) eqn:HbeqCurrStartA.
    - rewrite <-DTL.beqAddrTrue in HbeqCurrStartA. subst startaddr. rewrite HlookupCurrs0. trivial.
    - destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
        eqn:HbeqBlockBlockSh1.
      { rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite HbeqBlockBlockSh1 in *. exfalso; congruence. }
      simpl in *. destruct (beqAddr blockInCurrentPartitionAddr startaddr) eqn:HbeqBlockStartA;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in Hcons0; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hcons0; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in Hcons0; try(apply not_eq_sym; assumption).
      assert(HbeqStartStartA: newPDBlockStartAddr <> startaddr).
      {
        intro Hcontra. subst startaddr. destruct (beqAddr blockInCurrentPartitionAddr block) eqn:HbeqBlocks.
        - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold sh1entryAddr in *. rewrite HlookupBlocks in *.
          subst sh1entryaddr. unfold sh1entryPDflag in *. rewrite Hs in HPDflag. simpl in *.
          rewrite beqAddrTrue in HPDflag. simpl in *. congruence.
        - (*newPDBlockStartAddr is mapped in two different blocks in an incompatible way*)
          rewrite <-beqAddrFalse in HbeqBlocks.
          assert(HwellFormed: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HPFlagBlocks0: bentryPFlag blockInCurrentPartitionAddr true s0) by intuition.
          assert(In newPDBlockStartAddr (getAllPaddrAux [blockInCurrentPartitionAddr] s0)).
          {
            assert(Hend: bentryEndAddr blockInCurrentPartitionAddr (endAddr (blockrange bentry)) s0).
            { apply lookupBEntryEndAddr. assumption. }
            specialize(HwellFormed blockInCurrentPartitionAddr newPDBlockStartAddr (endAddr (blockrange bentry))
              HPFlagBlocks0 Hstart Hend). destruct HwellFormed as (HwellFormed & _). simpl.
            unfold bentryStartAddr in *. rewrite HlookupBlocks0 in *. rewrite app_nil_r. subst newPDBlockStartAddr.
            apply getAllPaddrBlockIncl; lia.
          }
          assert(HstartInBlock: In newPDBlockStartAddr (getMappedPaddr currentPart s0)).
          {
            apply addrInBlockIsMapped with blockInCurrentPartitionAddr; assumption.
          }
          assert(HblockInPart: blockBelongsToAPart s0)
            by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HblockIsBE: isBE block s0).
          {
            unfold isBE. unfold bentryStartAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). trivial.
          }
          specialize(HblockInPart block HblockIsBE). destruct HblockInPart as [part (HpartIsPart & HblockMappedPart)].
          unfold isBE in HblockIsBE.
          destruct (lookup block (memory s0) beqAddr) eqn:HlookupBlockBis; try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          assert(HPFlags0: bentryPFlag block true s0).
          {
            apply mappedBlockIsBE in HblockMappedPart.
            destruct HblockMappedPart as [bentryBis (HlookupBlockBis' & Hpresent)]. unfold bentryPFlag.
            rewrite HlookupBlockBis'. apply eq_sym. assumption.
          }
          assert(In newPDBlockStartAddr (getAllPaddrAux [block] s0)).
          {
            assert(Hend: bentryEndAddr block (endAddr (blockrange b)) s0).
            { apply lookupBEntryEndAddr. assumption. }
            specialize(HwellFormed block newPDBlockStartAddr (endAddr (blockrange b)) HPFlags0 Hstarts0 Hend).
            destruct HwellFormed as (HwellFormed & _). simpl. unfold bentryStartAddr in *.
            rewrite HlookupBlockBis in *. rewrite app_nil_r. subst newPDBlockStartAddr.
            apply getAllPaddrBlockIncl; lia.
          }
          assert(HstartInBlockBis: In newPDBlockStartAddr (getMappedPaddr part s0)).
          {
            apply addrInBlockIsMapped with block; assumption.
          }
          assert(In currentPart (getPartitions multiplexer s0)).
          {
            assert(Hcurr: currentPart = currentPartition s0) by intuition. rewrite Hcurr in *.
            unfold consistency in *; unfold consistency1 in *; intuition.
          }
          assert(HsameBloodline: In currentPart (part::filterOptionPaddr (completeParentsList part s0))).
          {
            unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *.
            unfold sh1entryAddr in *. rewrite HlookupBlockBis in *. subst sh1entryaddr.
            apply addressesBloodlineIfNotShared with newPDBlockStartAddr block; try(assumption); intuition.
          }
          simpl in HsameBloodline. destruct (beqAddr part currentPart) eqn:HbeqParts.
          {
            rewrite <-DTL.beqAddrTrue in HbeqParts. subst part. assert(blockInCurrentPartitionAddr = block).
            {
              apply mappedBlocksEqStartEq with currentPart newPDBlockStartAddr s0; try(assumption).
              unfold consistency in *; unfold consistency2 in *; intuition.
              unfold isPDT. rewrite HlookupCurrs0. trivial.
            }
            congruence.
          }
          rewrite <-beqAddrFalse in HbeqParts. destruct HsameBloodline as [HpartsEq | HsameBloodline];
            try(congruence).
          (*blockInCurrentPartitionAddr cannot be shared either*)
          assert(HPDchildBlocks0: exists sh1entry sh1entryaddr,
                  lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
                  /\ sh1entryPDchild sh1entryaddr nullAddr s0
                  /\ sh1entryAddr blockInCurrentPartitionAddr sh1entryaddr s0) by intuition.
          destruct HPDchildBlocks0 as [sh1entryBlock [sh1entryaddrBlock (_ & HPDchildBlocks0 & Hsh1Blocks0)]].
          assert(HsameBloodlineBis: In part (currentPart::filterOptionPaddr (completeParentsList currentPart s0))).
          {
            unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *.
            unfold sh1entryAddr in *. rewrite HlookupBlocks0 in *. subst sh1entryaddrBlock.
            apply addressesBloodlineIfNotShared with newPDBlockStartAddr blockInCurrentPartitionAddr; try(assumption);
              intuition.
          }
          simpl in HsameBloodlineBis. destruct HsameBloodlineBis as [Hcontra | HsameBloodlineBis]; try(congruence).
          contradict HsameBloodlineBis. apply completeParentsListOrientation; try(assumption).
          unfold consistency in *; unfold consistency1 in *; intuition.
          unfold consistency in *; unfold consistency1 in *; intuition.
      }
      rewrite HlookupEqs2s0 in Hcons0; assumption.
    (* END notPDTIfNotPDflag *)
  }
  assert(nextKernAddrIsInSameBlock s).
  { (* BEGIN nextKernAddrIsInSameBlock s *)
    assert(Hcons0: nextKernAddrIsInSameBlock s4) by intuition.
    intros block kernel startaddr endaddr HstartBis HendBis HkernIsKS.
    assert(Hblock: bentryStartAddr block startaddr s4 /\ bentryEndAddr block endaddr s4).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      assert(isBE block s).
      {
        unfold isBE. unfold bentryStartAddr in *. destruct (lookup block (memory s) beqAddr); try(congruence).
        destruct v; try(congruence). trivial.
      }
      rewrite HlookupBlocksEq in HstartBis; try(assumption). rewrite HlookupBlocksEq in HendBis; try(assumption).
      split; assumption.
    }
    destruct Hblock as (Hstarts0 & Hends0).
    assert(HkernIsKSs0: isKS kernel s4).
    {
      unfold isKS in *. rewrite Hs in HkernIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) kernel) eqn:HbeqBlockSh1Kern;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HkernIsKS; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 block kernel startaddr endaddr Hstarts0 Hends0 HkernIsKSs0). assumption.
    (* END nextKernAddrIsInSameBlock *)
  }
  assert(noDupUsedPaddrList s).
  { (* BEGIN noDupUsedPaddrList s*)
    assert(Hcons0: noDupUsedPaddrList s4) by intuition. intros part HpartIsPDT.
    assert(HpartIsPDTs0: isPDT part s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym); assumption.
    }
    unfold getUsedPaddr. rewrite HgetConfigPaddrEq; try(assumption).
    rewrite HgetMappedPaddrEq; try(assumption). specialize(Hcons0 part HpartIsPDTs0). assumption.
    (* END noDupUsedPaddrList *)
  }
  assert(adressesRangePreservedIfOriginAndNextOk s).
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s*)
    assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s4) by intuition.
    intros part pdentryPart block scentryaddr startaddr endaddr HpartIsPart HblockMappedPart HblockIsBE
      HstartBis HendBis HPFlag Hsce Horigin Hnext HlookupPart HbeqPartRoot.
    destruct (beqAddr newPDBlockStartAddr part) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst part. unfold getMappedBlocks in HblockMappedPart.
      unfold getKSEntries in HblockMappedPart. rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *.
      exfalso; congruence.
    }
    assert(HpartIsPDT: isPDT part s) by (unfold isPDT; rewrite HlookupPart; trivial).
    rewrite HgetMappedBlocksEq in HblockMappedPart; try(assumption). rewrite <-beqAddrFalse in HbeqStartPart.
    assert(HpartIsParts0: In part (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HpartIsPart. apply in_or_app. apply in_app_or in HpartIsPart.
      simpl in *. destruct HpartIsPart as [HpartIsLeft | HpartIsPartR]; try(left; assumption).
      destruct HpartIsPartR as [Hcontra | HpartIsRight]; try(right; assumption). exfalso; congruence.
    }
    assert(Hblocks0: isBE block s4 /\ bentryStartAddr block startaddr s4 /\ bentryEndAddr block endaddr s4
            /\ bentryPFlag block true s4).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartBis.
      rewrite Hs in HendBis. rewrite Hs in HPFlag. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqBlockSh1BlockBis;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HstartBis; try(apply not_eq_sym; assumption). split.
      unfold isBE. destruct (lookup block (memory s4) beqAddr); try(congruence). destruct v; try(congruence). trivial.
      split. assumption. split.
      rewrite removeDupIdentity in HendBis; try(apply not_eq_sym); assumption.
      rewrite removeDupIdentity in HPFlag; try(apply not_eq_sym); assumption.
    }
    destruct Hblocks0 as (HblockIsBEs0 & Hstarts0 & Hends0 & HPFlags0).
    assert(Hsces0: scentryOrigin scentryaddr startaddr s4 /\ scentryNext scentryaddr nullAddr s4).
    {
      unfold scentryOrigin in *. unfold scentryNext in *. rewrite Hs in Horigin. rewrite Hs in Hnext. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) scentryaddr) eqn:HbeqBlockSh1Sce;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. split.
      rewrite removeDupIdentity in Horigin; try(apply not_eq_sym); assumption.
      rewrite removeDupIdentity in Hnext; try(apply not_eq_sym); assumption.
    }
    destruct Hsces0 as (Horigins0 & Hnexts0).
    assert(HlookupParts0: lookup part (memory s4) beqAddr = Some (PDT pdentryPart)).
    {
      rewrite Hs in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 part pdentryPart block scentryaddr startaddr endaddr HpartIsParts0 HblockMappedPart
      HblockIsBEs0 Hstarts0 Hends0 HPFlags0 Hsce Horigins0 Hnexts0 HlookupParts0 HbeqPartRoot).
    destruct Hcons0 as [blockParent (HblockParentMapped & HblockParentIsBE & HstartParent & HendParent)].
    exists blockParent.
    assert(HparentOfPart: parentOfPartitionIsPartition s4) by intuition.
    specialize(HparentOfPart part pdentryPart HlookupParts0). destruct HparentOfPart as (HparentIsPart & _).
    specialize(HparentIsPart HbeqPartRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
    rewrite HgetMappedBlocksEq; try(assumption); try(apply partitionsArePDT; try(assumption)).
    - split. assumption.
      unfold isBE. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs. simpl.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockParent) eqn:HbeqBlockSh1BlockP.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockSh1BlockP. subst blockParent. rewrite HlookupSh1 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      destruct (lookup blockParent (memory s4) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split. trivial. split; assumption.
    - rewrite HgetPartsEqs. rewrite HgetPartsEqs4 in HparentIsPart. apply in_or_app. apply in_app_or in HparentIsPart.
      simpl. destruct HparentIsPart as [HparentIsLeft | HparentIsRight]; try(left; assumption).
      right; right; assumption.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }
  assert(childsBlocksPropsInParent s).
  { (* BEGIN childsBlocksPropsInParent s*)
    assert(Hcons0: childsBlocksPropsInParent s4) by intuition.
    intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
      HchildIsChild HblockChildMapped HstartChild HendChild HPFlagChild HblockParentMapped HstartParent
      HendParent HPFlagParent HlebStart HgebEnd.
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child. unfold getMappedBlocks in HblockChildMapped.
      unfold getKSEntries in HblockChildMapped. rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *.
      exfalso; congruence.
    }
    destruct (beqAddr newPDBlockStartAddr pdparent) eqn:HbeqStartParent.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartParent. subst pdparent. unfold getMappedBlocks in HblockParentMapped.
      unfold getKSEntries in HblockParentMapped. rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *.
      exfalso; congruence.
    }
    assert(HchildIsPDT: isPDT child s).
    { apply childrenArePDT with pdparent; assumption. }
    assert(HparentIsPDT: isPDT pdparent s).
    { apply partitionsArePDT; assumption. }
    rewrite <-beqAddrFalse in *.
    assert(HparentIsParts4: In pdparent (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HparentIsPart. apply in_or_app. apply in_app_or in HparentIsPart.
      simpl in *. destruct HparentIsPart as [HparentIsLeft | HparentIsPartR]; try(left; assumption).
      destruct HparentIsPartR as [Hcontra | HparentIsRight]; try(right; assumption). congruence.
    }
    rewrite HgetMappedBlocksEq in HblockChildMapped; try(assumption).
    rewrite HgetMappedBlocksEq in HblockParentMapped; try(assumption).
    apply HgetChildrenEq in HchildIsChild; try(assumption); try(apply partitionsArePDT; intuition; congruence).
    simpl in HchildIsChild. destruct HchildIsChild as [Hcontra | HchildIsChild]; try(exfalso; congruence).
    assert(Hchilds0: bentryStartAddr blockChild startChild s4 /\ bentryEndAddr blockChild endChild s4
            /\ bentryPFlag blockChild true s4).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartChild.
      rewrite Hs in HendChild. rewrite Hs in HPFlagChild. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockChild) eqn:HbeqBlockSh1Child;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. split.
      rewrite removeDupIdentity in HstartChild; try(apply not_eq_sym); assumption. split.
      rewrite removeDupIdentity in HendChild; try(apply not_eq_sym); assumption.
      rewrite removeDupIdentity in HPFlagChild; try(apply not_eq_sym); assumption.
    }
    destruct Hchilds0 as (HstartChilds0 & HendChilds0 & HPFlagChilds0).
    assert(Hparents0: bentryStartAddr blockParent startParent s4 /\ bentryEndAddr blockParent endParent s4
            /\ bentryPFlag blockParent true s4).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. rewrite Hs in HstartParent.
      rewrite Hs in HendParent. rewrite Hs in HPFlagParent. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockParent) eqn:HbeqBlockSh1Parent;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *. split.
      rewrite removeDupIdentity in HstartParent; try(apply not_eq_sym); assumption. split.
      rewrite removeDupIdentity in HendParent; try(apply not_eq_sym); assumption.
      rewrite removeDupIdentity in HPFlagParent; try(apply not_eq_sym); assumption.
    }
    destruct Hparents0 as (HstartParents0 & HendParents0 & HPFlagParents0).
    specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent endParent
      HparentIsParts4 HchildIsChild HblockChildMapped HstartChilds0 HendChilds0 HPFlagChilds0 HblockParentMapped
      HstartParents0 HendParents0 HPFlagParents0 HlebStart HgebEnd).
    destruct Hcons0 as (HcheckChild & HPDchild & HInChildLoc & Haccess). unfold checkChild in *.
    destruct (beqAddr blockInCurrentPartitionAddr blockParent) eqn:HbeqBlockBlockP.
    {
      rewrite <-DTL.beqAddrTrue in HbeqBlockBlockP. subst blockParent. exfalso.
      assert(HPDchildBlocks0: exists sh1entry sh1entryaddr,
        lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
        /\ sh1entryPDchild sh1entryaddr nullAddr s0
        /\ sh1entryAddr blockInCurrentPartitionAddr sh1entryaddr s0) by intuition.
      destruct HPDchildBlocks0 as [sh1entryBlock [sh1entryaddrBlock (_ & HPDchildBlocks0 & Hsh1Blocks0)]].
      unfold sh1entryAddr in Hsh1Blocks0. rewrite HlookupBlocks0 in *. subst sh1entryaddrBlock.
      assert(HPDchildBlocks4: sh1entryPDchild (CPaddr (blockInCurrentPartitionAddr + sh1offset)) nullAddr s4).
      {
        unfold sh1entryPDchild in *. rewrite Hs4. rewrite Hs3. simpl.
        destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite <-HbeqCurrBlockSh1 in *. rewrite HlookupCurrs0 in *.
          congruence.
        }
        rewrite beqAddrFalse in HbeqBlockCurr. rewrite HbeqBlockCurr. simpl.
        destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)))
          eqn:HbeqBlockBlockSh1.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity; try(apply not_eq_sym; assumption). rewrite HlookupEqs2s0; try(assumption).
        intro Hcontra. subst newPDBlockStartAddr. rewrite HlookupNews0 in *. congruence.
      }
      specialize(HPDchild nullAddr HPDchildBlocks4). congruence.
    }
    rewrite <-beqAddrFalse in HbeqBlockBlockP.
    assert(HlookupSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                          = lookup (CPaddr (blockParent + sh1offset)) (memory s4) beqAddr).
    {
      rewrite Hs. simpl. assert(Hnull: nullAddrExists s4) by intuition. unfold nullAddrExists in *.
      unfold isPADDR in *. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset))
        (CPaddr (blockParent + sh1offset))) eqn:HbeqSh1s.
      {
        rewrite <-DTL.beqAddrTrue in HbeqSh1s. unfold CPaddr in HbeqSh1s. unfold CPaddr in HlookupSh1. exfalso.
        destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr).
        - destruct (le_dec (blockParent + sh1offset) maxAddr).
          + injection HbeqSh1s as HblocksEq. apply PeanoNat.Nat.add_cancel_r in HblocksEq.
            apply paddrEqNatEqEquiv in HblocksEq. congruence.
          + rewrite HbeqSh1s in *.
            assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockParent + sh1offset) n |} = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
            }
            rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
        - assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockInCurrentPartitionAddr + sh1offset) n |}
              = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal. apply proof_irrelevance.
          }
          rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption). reflexivity.
    }
    unfold sh1entryPDchild. unfold sh1entryInChildLocation. rewrite HlookupSh1Eq.
    unfold bentryAFlag in *. unfold bentryStartAddr in HstartParent. rewrite Hs. rewrite Hs in HstartParent.
    simpl in *. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockParent)
      eqn:HbeqBlockSh1BlockP; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym; assumption). split; try(split; try(split)); try(assumption).
    intros blockIDInChild HchildLocs. apply HInChildLoc. unfold sh1entryInChildLocation.
    destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s4) beqAddr); try(congruence).
    destruct v; try(congruence). destruct HchildLocs as (HchildLocs & HlocNotNull). split. assumption.
    intro HbeqLocNull. specialize(HlocNotNull HbeqLocNull). unfold isBE in *. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockIDInChild) eqn:HbeqBlockSh1Loc;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity in HlocNotNull; try(apply not_eq_sym); assumption.
    (* END childsBlocksPropsInParent *)
  }
  assert(noChildImpliesAddressesNotShared s).
  { (* BEGIN noChildImpliesAddressesNotShared s*)
    assert(Hcons0: noChildImpliesAddressesNotShared s4) by intuition.
    intros part pdentryPart block sh1entryaddr HpartIsPart HlookupPart HblockMappedPart Hsh1Bis HPDchild
      child addr HchildIsChild HaddrInBlock.
    destruct (beqAddr newPDBlockStartAddr part) eqn:HbeqStartPart.
    {
      rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst part. unfold getMappedBlocks in *.
      unfold getKSEntries in *. rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *. exfalso; congruence.
    }
    assert(HpartIsPDT: isPDT part s).
    { unfold isPDT. rewrite HlookupPart. trivial. }
    assert(HchildIsPDT: isPDT child s).
    { apply childrenArePDT with part; assumption. }
    assert(HpartIsParts4: In part (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HpartIsPart. apply in_or_app. apply in_app_or in HpartIsPart.
      simpl in *. destruct HpartIsPart as [HpartIsLeft | HpartIsPartR]; try(left; assumption).
      destruct HpartIsPartR as [Hcontra | HpartIsRight]; try(right; assumption). rewrite <-beqAddrFalse in *.
      exfalso; congruence.
    }
    rewrite HgetMappedBlocksEq in HblockMappedPart; try(assumption).
    assert(isPDT part s4).
    { apply partitionsArePDT; intuition. }
    apply HgetChildrenEq in HchildIsChild; try(assumption). simpl in HchildIsChild.
    destruct HchildIsChild as [HchildIsStart | HchildIsChild].
    - subst child. unfold getMappedPaddr. unfold getMappedBlocks. unfold getKSEntries. rewrite HlookupNews.
      rewrite HnewPDentry. simpl. intro Hcontra. congruence.
    - assert(HlookupParts0: lookup part (memory s4) beqAddr = Some (PDT pdentryPart)).
      {
        rewrite Hs in HlookupPart. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part) eqn:HbeqBlockSh1Part;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HlookupPart; try(apply not_eq_sym); assumption.
      }
      assert(HPDchilds0: sh1entryPDchild sh1entryaddr nullAddr s4).
      {
        unfold sh1entryPDchild in *. rewrite Hs in HPDchild. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) sh1entryaddr) eqn:HbeqSh1s.
        - rewrite <-DTL.beqAddrTrue in HbeqSh1s. subst sh1entryaddr.
          assert(Hnull: nullAddrExists s4) by intuition. unfold nullAddrExists in *. unfold isPADDR in *.
          unfold CPaddr in HbeqSh1s. unfold CPaddr in HlookupSh1.
          destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr) eqn:HleBlock.
          + destruct (le_dec (block + sh1offset) maxAddr).
            * injection HbeqSh1s as HblocksEq. apply PeanoNat.Nat.add_cancel_r in HblocksEq.
              apply paddrEqNatEqEquiv in HblocksEq. subst block. unfold CPaddr. rewrite HleBlock. rewrite HlookupSh1.
              simpl. assumption.
            * rewrite HbeqSh1s in *. exfalso.
              assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n |} = nullAddr).
              {
                unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
                apply proof_irrelevance.
              }
              rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
          + assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockInCurrentPartitionAddr + sh1offset) n |}
              = nullAddr).
            {
              unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
              apply proof_irrelevance.
            }
            rewrite HnullEq in *. rewrite HlookupSh1 in *. exfalso. congruence.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HPDchild; try(apply not_eq_sym); assumption.
      }
      assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s4)).
      {
        rewrite Hs in HaddrInBlock. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqBlockSh1BlockBis;
          try(simpl in *; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HaddrInBlock; try(apply not_eq_sym); assumption.
      }
      specialize(Hcons0 part pdentryPart block sh1entryaddr HpartIsParts4 HlookupParts0 HblockMappedPart Hsh1Bis
        HPDchilds0 child addr HchildIsChild HaddrInBlocks0).
      rewrite HgetMappedPaddrEq; assumption.
    (* END noChildImpliesAddressesNotShared *)
  }
  assert(kernelsAreNotAccessible s).
  { (* BEGIN kernelsAreNotAccessible s*)
    assert(Hcons0: kernelsAreNotAccessible s4) by intuition. intros block startaddr HstartBis HstartIsKS.
    assert(Hstarts0: bentryStartAddr block startaddr s4).
    {
      unfold bentryStartAddr in *. rewrite Hs in HstartBis. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqBlockSh1BlockBis;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HstartBis; try(apply not_eq_sym); assumption.
    }
    assert(HstartIsKSs0: isKS startaddr s4).
    {
      unfold isKS in *. rewrite Hs in HstartIsKS. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) startaddr) eqn:HbeqBlockSh1StartBis;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HstartIsKS; try(apply not_eq_sym); assumption.
    }
    specialize(Hcons0 block startaddr Hstarts0 HstartIsKSs0). unfold bentryAFlag in *. rewrite Hs.
    unfold bentryStartAddr in *. rewrite Hs in HstartBis. simpl in *.
    destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block) eqn:HbeqBlockSh1BlockBis;
      try(exfalso; congruence). rewrite <-beqAddrFalse in *.
    rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END kernelsAreNotAccessible *)
  }
  assert(HgetMappedBlocksEqs4s0: forall part, isPDT part s4 -> beqAddr newPDBlockStartAddr part = false
    -> getMappedBlocks part s4 = getMappedBlocks part s0) by intuition.
  assert(blockBelongsToAPart s).
  { (* BEGIN blockBelongsToAPart s *)
    assert(Hcons0: blockBelongsToAPart s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block HblockIsBE.
    destruct (beqAddr blockInCurrentPartitionAddr block) eqn:HbeqBlocks.
    - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. exists currentPart. split.
      + rewrite HgetPartsEqs. rewrite HgetPartsEqs4 in HcurrIsParts4. apply in_app_or in HcurrIsParts4.
        apply in_or_app. simpl. destruct HcurrIsParts4 as [Hleft | Hright]; try(left; assumption). right. right.
        assumption.
      + rewrite <-HgetMappedBlocksCurrEqs4s0 in HblockMappedCurrs0. rewrite HgetMappedBlocksEq; try(assumption).
        rewrite Hs. unfold isPDT. simpl.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) currentPart) eqn:HbeqBlockSh1Curr.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Curr. rewrite HbeqBlockSh1Curr in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    - unfold isBE in HblockIsBE. rewrite Hs in HblockIsBE. rewrite Hs4 in HblockIsBE. rewrite Hs3 in HblockIsBE.
      simpl in *. destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) block)
        eqn:HbeqBlockSh1BlockBis; try(exfalso; congruence).
      destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite HbeqCurrBlockSh1 in *. exfalso; congruence.
      }
      simpl in *. destruct (beqAddr currentPart block) eqn:HbeqCurBlockBis; try(exfalso; congruence).
      rewrite HbeqBlockCurr in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption). simpl in *.
      rewrite beqAddrFalse in HbeqBlocks. rewrite HbeqBlocks in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HblockIsBE; try(apply not_eq_sym; assumption).
      assert(HbeqStartBlockBis: newPDBlockStartAddr <> block).
      { intro Hcontra. subst block. rewrite HlookupNewPDs2 in *. congruence. }
      rewrite HlookupEqs2s0 in HblockIsBE; try(assumption). specialize(Hcons0 block HblockIsBE).
      destruct Hcons0 as [part (HpartIsPart & HblockMappedParts0)]. exists part.
      rewrite <-HgetPartsEqs4s0 in HpartIsPart. split.
      + rewrite HgetPartsEqs. rewrite HgetPartsEqs4 in HpartIsPart. apply in_or_app. apply in_app_or in HpartIsPart.
        simpl. destruct HpartIsPart as [Hleft | Hright]; try(left; assumption). right. right. assumption.
      + assert(HpartIsPDTs4: isPDT part s4).
        { apply partitionsArePDT; intuition. }
        destruct (beqAddr newPDBlockStartAddr part) eqn:HbeqStartPart.
        {
          rewrite <-DTL.beqAddrTrue in HbeqStartPart. subst part. rewrite HgetPartsEqs4s0 in HpartIsPart. exfalso.
          assert(Hcontra: isPDT newPDBlockStartAddr s0).
          {
            apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
          }
          unfold isPDT in *. rewrite HlookupNews0 in *. congruence.
        }
        specialize(HgetMappedBlocksEqs4s0 part HpartIsPDTs4 HbeqStartPart).
        rewrite <-HgetMappedBlocksEqs4s0 in HblockMappedParts0. rewrite HgetMappedBlocksEq; try(assumption).
        unfold isPDT in *. rewrite Hs. simpl.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part) eqn:HbeqBlockSh1Part.
        { rewrite <-DTL.beqAddrTrue in HbeqBlockSh1Part. subst part. rewrite HlookupSh1 in *. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    (* END blockBelongsToAPart *)
  }
  assert(HaccMappedEqCurrs4s0: forall addr, In addr (getAccessibleMappedPaddr currentPart s0)
      <-> In addr (getAllPaddrAux [blockInCurrentPartitionAddr] s4 ++ getAccessibleMappedPaddr currentPart s4))
    by intuition.
  assert(HaccMappedEqs4s0: forall part, isPDT part s4 -> isPDT part s0 -> beqAddr newPDBlockStartAddr part = false
    -> part <> currentPart -> getAccessibleMappedPaddr part s0 = getAccessibleMappedPaddr part s4) by intuition.
  assert(HgetMappedPaddrEqs4s0: forall part, isPDT part s4 -> beqAddr newPDBlockStartAddr part = false
    -> getMappedPaddr part s4 = getMappedPaddr part s0) by intuition.
  assert(HgetAccMappedPaddrEq: forall part, isPDT part s
    -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s4).
  {
    intros part HpartIsPDT. unfold getAccessibleMappedPaddr. unfold getAccessibleMappedBlocks.
    assert(HpartIsPDTs4: isPDT part s4).
    {
      unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) part) eqn:HbeqBlockSh1Part;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HpartIsPDT; try(apply not_eq_sym); assumption.
    }
    rewrite HgetMappedBlocksEq; try(assumption). unfold isPDT in *.
    destruct (lookup part (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    destruct (lookup part (memory s4) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
    assert(Hacc: filterAccessible (getMappedBlocks part s4) s = filterAccessible (getMappedBlocks part s4) s4).
    { rewrite Hs. apply filterAccessibleEqSHE. unfold isSHE. rewrite HlookupSh1. trivial. }
    rewrite Hacc. rewrite Hs. apply getAllPaddrAuxEqSHE. unfold isSHE. rewrite HlookupSh1. trivial.
  }
  assert(HgetChildrenEqs4s0: forall part, In part (getPartitions multiplexer s0)
    -> getChildren part s4 = getChildren part s0) by intuition.
  (*assert(accessibleParentPaddrIsAccessibleIntoChild s).
  { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
    assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s0)
      by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros pdparent child addr HparentIsPart HchildIsChild HaddrIsAccMappedParent HaddrMappedChild.
    destruct (beqAddr newPDBlockStartAddr pdparent) eqn:HbeqStartParent.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqStartParent. subst pdparent. unfold getChildren in HchildIsChild.
      unfold getMappedBlocks in HchildIsChild. unfold getKSEntries in HchildIsChild. rewrite HlookupNews in *.
      rewrite HnewPDentry in HchildIsChild. simpl in *. congruence.
    }
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child. unfold getMappedPaddr in HaddrMappedChild.
      unfold getMappedBlocks in HaddrMappedChild. unfold getKSEntries in HaddrMappedChild. rewrite HlookupNews in *.
      rewrite HnewPDentry in HaddrMappedChild. simpl in *. congruence.
    }
    assert(HparentIsParts0: In pdparent (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HparentIsPart. apply in_app_or in HparentIsPart. apply in_or_app.
      simpl in HparentIsPart. rewrite <-beqAddrFalse in *. simpl in *.
      destruct HparentIsPart as [HparentIsLeft | HparentIsPartR]; try(left; assumption). right.
      destruct HparentIsPartR as [Hcontra | HparentIsRight]; try(exfalso; congruence). assumption.
    }
    assert(HparentIsPDTs: isPDT pdparent s).
    { apply partitionsArePDT; intuition. }
    assert(HparentIsPDTs4: isPDT pdparent s4).
    { apply partitionsArePDT; intuition. }
    rewrite HgetPartsEqs4s0 in HparentIsParts0. specialize(HaccMappedEqCurrs4s0 addr).
    assert(HparentIsPDTs0: isPDT pdparent s0).
    { apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition. }
    rewrite HgetAccMappedPaddrEq in HaddrIsAccMappedParent; try(assumption).
    assert(HaddrIsAccMappedParents0: In addr (getAccessibleMappedPaddr pdparent s0)).
    {
      destruct (beqAddr pdparent currentPart) eqn:HbeqParentCurr.
      - rewrite <-DTL.beqAddrTrue in HbeqParentCurr. subst pdparent. apply HaccMappedEqCurrs4s0. apply in_or_app.
        right. assumption.
      - rewrite <-beqAddrFalse in HbeqParentCurr. rewrite HaccMappedEqs4s0; assumption.
    }
    assert(HchildIsChilds0: In child (getChildren pdparent s0)).
    {
      apply HgetChildrenEq in HchildIsChild; try(assumption). simpl in *. rewrite <-beqAddrFalse in *.
      destruct HchildIsChild as [Hcontra | HchildIsChild]; try(exfalso; congruence).
      rewrite <-HgetChildrenEqs4s0; assumption.
    }
    assert(HchildIsPDT: isPDT child s).
    { apply childrenArePDT with pdparent; assumption. }
    rewrite HgetMappedPaddrEq in HaddrMappedChild; try(assumption).
    assert(HchildIsPDTs4: isPDT child s4).
    {
      unfold isPDT in *. rewrite Hs in HchildIsPDT. simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child) eqn:HbeqBlockSh1Child;
        try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in HchildIsPDT; try(apply not_eq_sym); assumption.
    }
    assert(HaddrMappedChilds0: In addr (getMappedPaddr child s0)).
    {
      rewrite HgetMappedPaddrEqs4s0 in HaddrMappedChild; assumption.
    }
    specialize(Hcons0 pdparent child addr HparentIsParts0 HchildIsChilds0 HaddrIsAccMappedParents0
      HaddrMappedChilds0). rewrite HgetAccMappedPaddrEq; try(assumption).
    destruct (beqAddr child currentPart) eqn:HbeqChildCurr.
    - rewrite <-DTL.beqAddrTrue in HbeqChildCurr. subst child. apply HaccMappedEqCurrs4s0 in Hcons0.
      apply in_app_or in Hcons0. destruct Hcons0 as [HaddrInBlock | Hres]; try(assumption).
      (*TODO that prop is false*)
    - 
    (* END accessibleParentPaddrIsAccessibleIntoChild *)
  }*)
  assert(sharedBlockPointsToChild s).
  { (* BEGIN sharedBlockPointsToChild s *)
    assert(Hcons0: sharedBlockPointsToChild s0) by (unfold consistency in *; unfold consistency2 in *; intuition).
    intros pdparent child addr blockParent sh1entryaddr HparentIsPart HchildIsChild HaddrUsedChild HaddrInBlockParent
      HblockParentMapped Hsh1Parent.
    destruct (beqAddr newPDBlockStartAddr pdparent) eqn:HbeqStartParent.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqStartParent. subst pdparent. unfold getChildren in HchildIsChild.
      unfold getMappedBlocks in HchildIsChild. unfold getKSEntries in HchildIsChild. rewrite HlookupNews in *.
      rewrite HnewPDentry in HchildIsChild. simpl in *. congruence.
    }
    assert(HparentIsParts0: In pdparent (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HparentIsPart. apply in_app_or in HparentIsPart. apply in_or_app.
      simpl in HparentIsPart. rewrite <-beqAddrFalse in *. simpl in *.
      destruct HparentIsPart as [HparentIsLeft | HparentIsPartR]; try(left; assumption). right.
      destruct HparentIsPartR as [Hcontra | HparentIsRight]; try(exfalso; congruence). assumption.
    }
    assert(HgetConfigEqs4s0: forall part, isPDT part s0 -> beqAddr newPDBlockStartAddr part = false
      -> getConfigPaddr part s4 = getConfigPaddr part s0) by intuition.
    assert(HparentIsPDTs: isPDT pdparent s).
    { apply partitionsArePDT; intuition. }
    assert(HparentIsPDTs4: isPDT pdparent s4).
    { apply partitionsArePDT; intuition. }
    rewrite HgetPartsEqs4s0 in HparentIsParts0. rewrite HgetMappedBlocksEq in HblockParentMapped; try(assumption).
    rewrite HgetMappedBlocksEqs4s0 in HblockParentMapped; try(assumption).
    assert(Hblocks0: In addr (getAllPaddrAux [blockParent] s0) /\ sh1entryAddr blockParent sh1entryaddr s0).
    {
      rewrite Hs in HaddrInBlockParent. rewrite Hs4 in HaddrInBlockParent. rewrite Hs3 in HaddrInBlockParent.
      unfold sh1entryAddr in *. rewrite Hs in Hsh1Parent. rewrite Hs4 in Hsh1Parent. rewrite Hs3 in Hsh1Parent.
      simpl in *.
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) blockParent) eqn:HbeqBlockSh1BlockP;
        try(exfalso; congruence).
      destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1.
      {
        rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite HbeqCurrBlockSh1 in *. exfalso; congruence.
      }
      simpl in *. destruct (beqAddr currentPart blockParent) eqn:HbeqCurrBlockP; try(exfalso; simpl in *; congruence).
      rewrite HbeqBlockCurr in *. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in Hsh1Parent; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity in HaddrInBlockParent; try(apply not_eq_sym; assumption). simpl in *.
      destruct (beqAddr blockInCurrentPartitionAddr blockParent) eqn:HbeqBlocks.
      - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0. rewrite HnewBentry in *.
        simpl in *. split; assumption.
      - rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HaddrInBlockParent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in HaddrInBlockParent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hsh1Parent; try(apply not_eq_sym; assumption).
        rewrite removeDupIdentity in Hsh1Parent; try(apply not_eq_sym; assumption).
        assert(newPDBlockStartAddr <> blockParent).
        {
          intro Hcontra. subst blockParent. rewrite HlookupNewPDs2 in *. simpl in *. congruence.
        }
        rewrite <-HlookupEqs2s0; try(split); assumption.
    }
    destruct Hblocks0 as (HaddrInBlockParents0 & Hsh1Parents0).
    assert(HparentIsParent: isParent s) by assumption.
    specialize(HparentIsParent child pdparent HparentIsPart HchildIsChild).
    assert(HchildIsPDTs: isPDT child s).
    { apply childrenArePDT with pdparent; assumption. }
    apply HgetChildrenEq in HchildIsChild; try(assumption). simpl in HchildIsChild.
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    - rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child. unfold getUsedPaddr in HaddrUsedChild.
      unfold getMappedPaddr in HaddrUsedChild. unfold getMappedBlocks in HaddrUsedChild.
      unfold getKSEntries in HaddrUsedChild. rewrite HlookupNews in *. rewrite HnewPDentry in HaddrUsedChild.
      simpl in HaddrUsedChild. rewrite app_nil_r in HaddrUsedChild. unfold getConfigPaddr in HaddrUsedChild.
      assert(HnoConfigAddr: getAllPaddrConfigAux (getConfigBlocks newPDBlockStartAddr s) s = []).
      {
        unfold getConfigBlocks in *. simpl in *. rewrite HlookupNews in *. rewrite HnewPDentry in *. simpl in *.
        replace (maxIdx + 1) with (S maxIdx) in *; try(lia). simpl in *. unfold nullAddrExists in *.
        unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). destruct (beqAddr p nullAddr); simpl; reflexivity.
      }
      rewrite HnoConfigAddr in HaddrUsedChild. rewrite app_nil_r in HaddrUsedChild. simpl in HaddrUsedChild.
      rewrite HlookupNews in *. rewrite app_nil_r in HaddrUsedChild.
      assert(HaddrInBlock: In addr (getAllPaddrAux [blockInCurrentPartitionAddr] s0)).
      {
        simpl. rewrite HlookupBlocks0. rewrite app_nil_r.
        assert(HendBlocks0: bentryEndAddr blockInCurrentPartitionAddr newPDBlockEndAddr s0) by intuition.
        assert(HwellFormed: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HPFlags0: bentryPFlag blockInCurrentPartitionAddr true s0) by intuition.
        specialize(HwellFormed blockInCurrentPartitionAddr newPDBlockStartAddr newPDBlockEndAddr HPFlags0 Hstart
          HendBlocks0). destruct HwellFormed as (HwellFormed & _).
        assert(HblockSize: i blockSize = newPDBlockEndAddr - newPDBlockStartAddr) by intuition.
        assert(HltBlockSizeLen: false = indexLt blockSize PDStructureTotalLength) by intuition.
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *. rewrite <-HendBlocks0.
        rewrite <-Hstart. unfold indexLt in HltBlockSizeLen. apply eq_sym in HltBlockSizeLen.
        apply PeanoNat.Nat.ltb_ge in HltBlockSizeLen. rewrite HblockSize in HltBlockSizeLen.
        assert(PDStructureTotalLength = Constants.PDStructureTotalLength) by intuition. subst PDStructureTotalLength.
        assert(p newPDBlockStartAddr + i Constants.PDStructureTotalLength <= p newPDBlockEndAddr).
        {
          assert(Hres: i Constants.PDStructureTotalLength + p newPDBlockStartAddr
                  <= p newPDBlockEndAddr - p newPDBlockStartAddr + p newPDBlockStartAddr) by lia.
          rewrite PeanoNat.Nat.sub_add in Hres; lia.
        }
        apply getAllPaddrBlockInclRevAux in HaddrUsedChild.
        destruct HaddrUsedChild as (HlebStartAddr & HltAddrMinEnd & HsizeIsPos). apply getAllPaddrBlockIncl; lia.
      }
      right. unfold pdentryParent in *. rewrite HlookupNews in *. rewrite HnewPDentry in HparentIsParent.
      simpl in HparentIsParent. subst pdparent.
      assert(blockParent = blockInCurrentPartitionAddr).
      {
        destruct (beqAddr blockParent blockInCurrentPartitionAddr) eqn:HbeqBlocks;
          try(apply DTL.beqAddrTrue; assumption). exfalso. rewrite <-beqAddrFalse in HbeqBlocks.
        assert(~ In addr (getAllPaddrAux [blockInCurrentPartitionAddr] s0)).
        {
          apply DisjointPaddrInPart with currentPart blockParent; try(assumption).
          - unfold consistency in *; unfold consistency2 in *; intuition.
          - apply partitionsArePDT; try(assumption); unfold consistency in *; unfold consistency1 in *; intuition.
        }
        congruence.
      }
      subst blockParent. unfold sh1entryPDflag. rewrite Hs. simpl. rewrite beqAddrTrue. simpl. reflexivity.
    - destruct HchildIsChild as [Hcontra | HchildIsChilds4]; try(rewrite <-beqAddrFalse in *; exfalso; congruence).
      assert(HchildIsChilds0: In child (getChildren pdparent s0)).
      {
        rewrite <-HgetChildrenEqs4s0; assumption.
      }
      specialize(HgetMappedPaddrEq child HchildIsPDTs). unfold getUsedPaddr in *. rewrite HgetMappedPaddrEq in *.
      assert(HchildIsPDTs4: isPDT child s4).
      { apply childrenArePDT with pdparent; try(assumption). intuition. }
      specialize(HgetMappedPaddrEqs4s0 child HchildIsPDTs4 HbeqStartChild). rewrite HgetMappedPaddrEqs4s0 in *.
      assert(HchildIsPDTs0: isPDT child s0).
      {
        apply childrenArePDT with pdparent; try(assumption).
        unfold consistency in *; unfold consistency1 in *; intuition.
      }
      specialize(HgetConfigPaddrEq child HchildIsPDTs4). rewrite HgetConfigPaddrEq in *.
      specialize(HgetConfigEqs4s0 child HchildIsPDTs0 HbeqStartChild). rewrite HgetConfigEqs4s0 in *.
      specialize(Hcons0 pdparent child addr blockParent sh1entryaddr HparentIsParts0 HchildIsChilds0 HaddrUsedChild
        HaddrInBlockParents0 HblockParentMapped Hsh1Parents0).
      destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (CPaddr (blockParent + sh1offset)))
        eqn:HbeqSh1s.
      + rewrite <-DTL.beqAddrTrue in HbeqSh1s. unfold CPaddr in HbeqSh1s. unfold CPaddr in HlookupSh1.
        assert(Hnull: nullAddrExists s4) by intuition. unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (le_dec (blockInCurrentPartitionAddr + sh1offset) maxAddr).
        * destruct (le_dec (blockParent + sh1offset) maxAddr).
          -- injection HbeqSh1s as HbeqBlocks. apply PeanoNat.Nat.add_cancel_r in HbeqBlocks.
             apply paddrEqNatEqEquiv in HbeqBlocks. subst blockParent. unfold sh1entryPDchild. unfold sh1entryPDflag.
             rewrite Hs. simpl. rewrite beqAddrTrue. simpl. right. reflexivity.
          -- rewrite HbeqSh1s in *. exfalso.
             assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockParent + sh1offset) n |} = nullAddr).
             {
               unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
               apply proof_irrelevance.
             }
             rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
        * assert(HnullEq: {| p := 0; Hp := ADT.CPaddr_obligation_2 (blockInCurrentPartitionAddr + sh1offset) n |}
              = nullAddr).
          {
            unfold nullAddr. unfold CPaddr. destruct (le_dec 0 maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          exfalso. rewrite HnullEq in *. rewrite HlookupSh1 in *. congruence.
      + assert(HlookupSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s) beqAddr
                = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
        {
          assert(Hsh1IsSHE: isSHE (CPaddr (blockParent + sh1offset)) s0).
          {
            unfold isSHE. destruct Hcons0 as [Hchild | Hflag].
            - unfold sh1entryPDchild in *.
              destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). trivial.
            - unfold sh1entryPDflag in *.
              destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). trivial.
          }
          unfold isSHE in Hsh1IsSHE. rewrite Hs. rewrite Hs4. rewrite Hs3. simpl. rewrite HbeqSh1s.
          destruct (beqAddr currentPart (CPaddr (blockInCurrentPartitionAddr + sh1offset))) eqn:HbeqCurrBlockSh1.
          { rewrite <-DTL.beqAddrTrue in HbeqCurrBlockSh1. rewrite HbeqCurrBlockSh1 in *. exfalso; congruence. }
          simpl. destruct (beqAddr currentPart (CPaddr (blockParent + sh1offset))) eqn:HbeqCurrBlockBisSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqCurrBlockBisSh1. rewrite HbeqCurrBlockBisSh1 in *.
            rewrite HlookupCurrs0 in *. exfalso; congruence.
          }
          rewrite HbeqBlockCurr. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). simpl.
          destruct (beqAddr blockInCurrentPartitionAddr (CPaddr (blockParent + sh1offset))) eqn:HbeqBlockBlockBisSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockBlockBisSh1. rewrite HbeqBlockBlockBisSh1 in *.
            rewrite HlookupBlocks0 in *. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity; try(apply not_eq_sym; assumption). apply HlookupEqs2s0. intro Hcontra.
          subst newPDBlockStartAddr. rewrite HlookupNews0 in *. congruence.
        }
        unfold sh1entryPDchild. unfold sh1entryPDflag. rewrite HlookupSh1Eq. assumption.
    (* END sharedBlockPointsToChild *)
  }
  assert(partitionsIsolation s).
  { (* BEGIN partitionsIsolation s *)
    assert(Hcons0: partitionsIsolation s0) by intuition. intros pdparent child1 child2 HparentIsPart Hchild1IsChild
      Hchild2IsChild HbeqChildren.
    assert(HisParent1: isParent s) by assumption. specialize(HisParent1 child1 pdparent HparentIsPart Hchild1IsChild).
    assert(HisParent2: isParent s) by assumption. specialize(HisParent2 child2 pdparent HparentIsPart Hchild2IsChild).
    destruct (beqAddr newPDBlockStartAddr pdparent) eqn:HbeqStartParent.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqStartParent. subst pdparent. unfold getChildren in Hchild1IsChild.
      unfold getMappedBlocks in Hchild1IsChild. unfold getKSEntries in Hchild1IsChild. rewrite HlookupNews in *.
      rewrite HnewPDentry in Hchild1IsChild. simpl in *. congruence.
    }
    assert(HparentIsParts0: In pdparent (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HparentIsPart. apply in_app_or in HparentIsPart. apply in_or_app.
      simpl in HparentIsPart. rewrite <-beqAddrFalse in *. simpl in *.
      destruct HparentIsPart as [HparentIsLeft | HparentIsPartR]; try(left; assumption). right.
      destruct HparentIsPartR as [Hcontra | HparentIsRight]; try(exfalso; congruence). assumption.
    }
    assert(Hchild1IsPDT: isPDT child1 s).
    { apply childrenArePDT with pdparent; assumption. }
    assert(Hchild2IsPDT: isPDT child2 s).
    { apply childrenArePDT with pdparent; assumption. }
    destruct (beqAddr newPDBlockStartAddr child1) eqn:HbeqStartChild1.
    - rewrite <-DTL.beqAddrTrue in HbeqStartChild1. subst child1. rewrite beqAddrFalse in HbeqChildren.
      intros addr HaddrUsedStart. unfold getUsedPaddr in HaddrUsedStart. unfold getConfigPaddr in HaddrUsedStart.
      unfold getMappedPaddr in HaddrUsedStart. unfold getConfigBlocks in *. unfold getMappedBlocks in *.
      unfold getKSEntries in *. simpl in HaddrUsedStart. rewrite HlookupNews in *. rewrite HnewPDentry in *.
      simpl in HaddrUsedStart.
      assert(HnoConfig: (filterOptionPaddr (getConfigBlocksAux (maxIdx + 1) nullAddr s (CIndex maxNbPrepare)))
                        = []).
      {
        rewrite MaxIdxNextEq. simpl. unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (beqAddr p nullAddr); try(simpl; reflexivity).
      }
      rewrite HnoConfig in *. simpl in HaddrUsedStart. repeat rewrite app_nil_r in HaddrUsedStart.
      assert(HaddrInBlock: In addr (getAllPaddrAux [blockInCurrentPartitionAddr] s0)).
      {
        simpl. rewrite HlookupBlocks0. rewrite app_nil_r.
        assert(HendBlocks0: bentryEndAddr blockInCurrentPartitionAddr newPDBlockEndAddr s0) by intuition.
        assert(HwellFormed: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HPFlags0: bentryPFlag blockInCurrentPartitionAddr true s0) by intuition.
        specialize(HwellFormed blockInCurrentPartitionAddr newPDBlockStartAddr newPDBlockEndAddr HPFlags0 Hstart
          HendBlocks0). destruct HwellFormed as (HwellFormed & _).
        assert(HblockSize: i blockSize = newPDBlockEndAddr - newPDBlockStartAddr) by intuition.
        assert(HltBlockSizeLen: false = indexLt blockSize PDStructureTotalLength) by intuition.
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *. rewrite <-HendBlocks0.
        rewrite <-Hstart. unfold indexLt in HltBlockSizeLen. apply eq_sym in HltBlockSizeLen.
        apply PeanoNat.Nat.ltb_ge in HltBlockSizeLen. rewrite HblockSize in HltBlockSizeLen.
        assert(PDStructureTotalLength = Constants.PDStructureTotalLength) by intuition. subst PDStructureTotalLength.
        assert(p newPDBlockStartAddr + i Constants.PDStructureTotalLength <= p newPDBlockEndAddr).
        {
          assert(Hres: i Constants.PDStructureTotalLength + p newPDBlockStartAddr
                  <= p newPDBlockEndAddr - p newPDBlockStartAddr + p newPDBlockStartAddr) by lia.
          rewrite PeanoNat.Nat.sub_add in Hres; lia.
        }
        apply getAllPaddrBlockInclRevAux in HaddrUsedStart.
        destruct HaddrUsedStart as (HlebStartAddr & HltAddrMinEnd & HsizeIsPos). apply getAllPaddrBlockIncl; lia.
      }
      unfold getUsedPaddr. specialize(HgetMappedPaddrEq child2 Hchild2IsPDT). rewrite HgetMappedPaddrEq.
      assert(Hchild2IsPDTs4: isPDT child2 s4).
      {
        unfold isPDT in *. rewrite Hs in Hchild2IsPDT. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child2) eqn:HbeqBlockSh1Child2;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in Hchild2IsPDT; try(apply not_eq_sym); assumption.
      }
      rewrite HgetMappedPaddrEqs4s0; try(assumption). rewrite HgetConfigPaddrEq; try(assumption).
      assert(HgetConfigEqs4s0: forall part, isPDT part s0 -> beqAddr newPDBlockStartAddr part = false
        -> getConfigPaddr part s4 = getConfigPaddr part s0) by intuition.
      assert(Hchild2IsPDTs0: isPDT child2 s0).
      {
        unfold isPDT in *. rewrite Hs4 in Hchild2IsPDTs4. rewrite Hs3 in Hchild2IsPDTs4. simpl in *.
        destruct (beqAddr currentPart child2) eqn:HbeqCurrChild2.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrChild2. subst child2. rewrite HlookupCurrs0. trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr blockInCurrentPartitionAddr child2) eqn:HbeqBlockChild2; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hchild2IsPDTs4; try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in Hchild2IsPDTs4; try(apply not_eq_sym; assumption).
          rewrite <-HlookupEqs2s0; assumption.
      }
      rewrite HgetConfigEqs4s0; try(assumption).
      assert(HPDchild: exists sh1entry sh1entryaddr, lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
              /\ sh1entryPDchild sh1entryaddr nullAddr s0 /\ sh1entryAddr blockInCurrentPartitionAddr sh1entryaddr s0)
        by intuition.
      assert(HparentIsPDT: isPDT pdparent s4).
      { apply partitionsArePDT; try(assumption); intuition. }
      destruct HPDchild as [_ [sh1entryaddr (_ & HPDchild & Hsh1)]]. rewrite HgetPartsEqs4s0 in HparentIsParts0.
      assert(Hchild2IsParts0: In child2 (getPartitions multiplexer s0)).
      {
        apply childrenPartitionInPartitionList with pdparent; try(assumption).
        unfold consistency in *; unfold consistency1 in *; intuition.
        apply HgetChildrenEq in Hchild2IsChild; try(assumption). simpl in Hchild2IsChild. rewrite <-beqAddrFalse in *.
        destruct Hchild2IsChild as [Hcontra | Hchild2IsChild]; try(exfalso; congruence).
        rewrite HgetChildrenEqs4s0 in Hchild2IsChild; assumption.
      }
      unfold pdentryParent in HisParent1. rewrite HlookupNews in *. simpl in HisParent1. subst pdparent.
      assert(HKDIs0: kernelDataIsolation s0) by intuition. apply Lib.in_or_app_neg.
      assert(HaddrAccMappedParent: In addr (getAccessibleMappedPaddr currentPart s0)).
      {
        apply addrInAccessibleBlockIsAccessibleMapped with blockInCurrentPartitionAddr; try(assumption). intuition.
      }
      specialize(HKDIs0 currentPart child2 HparentIsParts0 Hchild2IsParts0 addr HaddrAccMappedParent). split.
      assumption. assert(HnoChild: noChildImpliesAddressesNotShared s0)
        by (unfold consistency in *; unfold consistency2 in *; intuition). unfold sh1entryAddr in *.
      rewrite HlookupBlocks0 in *. apply HgetChildrenEq in Hchild2IsChild; try(assumption). simpl in Hchild2IsChild.
      rewrite <-beqAddrFalse in *. destruct Hchild2IsChild as [Hcontra | Hchild2IsChild]; try(exfalso; congruence).
      rewrite HgetChildrenEqs4s0 in Hchild2IsChild; try(assumption).
      specialize(HnoChild currentPart pdentry blockInCurrentPartitionAddr sh1entryaddr HparentIsParts0 HlookupCurrs0
        HblockMappedCurrs0 Hsh1 HPDchild child2 addr Hchild2IsChild HaddrInBlock). assumption.
    - destruct (beqAddr newPDBlockStartAddr child2) eqn:HbeqStartChild2.
      + rewrite <-DTL.beqAddrTrue in HbeqStartChild2. subst child2. rewrite beqAddrFalse in HbeqChildren.
        rewrite beqAddrSym in HbeqChildren. intros addr HaddrUsedChild1. unfold getUsedPaddr in *.
        unfold getConfigPaddr. unfold getMappedPaddr. unfold getConfigBlocks. unfold getMappedBlocks.
        unfold getKSEntries. simpl. rewrite HlookupNews. rewrite HnewPDentry. simpl.
        assert(HnoConfig: (filterOptionPaddr (getConfigBlocksAux (maxIdx + 1) nullAddr s (CIndex maxNbPrepare)))
                          = []).
        {
          rewrite MaxIdxNextEq. simpl. unfold nullAddrExists in *. unfold isPADDR in *.
          destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          destruct (beqAddr p nullAddr); try(simpl; reflexivity).
        }
        rewrite HnoConfig. simpl. repeat rewrite app_nil_r. unfold pdentryParent in HisParent2.
        rewrite HlookupNews in *. rewrite HnewPDentry in HisParent2. simpl in *. subst pdparent.
        rewrite HgetPartsEqs4s0 in *.
        assert(HaddrNotInBlock: ~In addr (getAllPaddrAux [blockInCurrentPartitionAddr] s0)).
        {
          intro Hcontra. assert(HnoChild: noChildImpliesAddressesNotShared s0)
            by (unfold consistency in *; unfold consistency2 in *; intuition).
          assert(HPDchild: exists sh1entry sh1entryaddr, lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
                  /\ sh1entryPDchild sh1entryaddr nullAddr s0
                  /\ sh1entryAddr blockInCurrentPartitionAddr sh1entryaddr s0)
            by intuition. destruct HPDchild as [_ [sh1entryaddr (_ & HPDchild & Hsh1)]]. unfold sh1entryAddr in *.
          rewrite HlookupBlocks0 in *. apply HgetChildrenEq in Hchild1IsChild; try(assumption).
          simpl in Hchild1IsChild. rewrite <-beqAddrFalse in *.
          destruct Hchild1IsChild as [HcontraBis | Hchild1IsChild]; try(exfalso; congruence).
          rewrite HgetChildrenEqs4s0 in Hchild1IsChild; try(assumption).
          specialize(HnoChild currentPart pdentry blockInCurrentPartitionAddr sh1entryaddr HcurrIsParts4
            HlookupCurrs0 HblockMappedCurrs0 Hsh1 HPDchild child1 addr Hchild1IsChild Hcontra).
          apply in_app_or in HaddrUsedChild1. rewrite HgetMappedPaddrEq in HaddrUsedChild1; try(assumption).
          assert(Hchild1IsPDTs4: isPDT child1 s4).
          {
            unfold isPDT in *. rewrite Hs in Hchild1IsPDT. simpl in *.
            destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child1) eqn:HbeqBlockSh1Child1;
              try(exfalso; congruence). rewrite <-beqAddrFalse in *.
            rewrite removeDupIdentity in Hchild1IsPDT; try(apply not_eq_sym); assumption.
          }
          rewrite beqAddrFalse in *. rewrite HgetMappedPaddrEqs4s0 in HaddrUsedChild1; try(assumption).
          destruct HaddrUsedChild1 as [HaddrConfigChild1 | HcontraBis]; try(congruence).
          assert(HKDIs0: kernelDataIsolation s0) by intuition.
          assert(HaddrAccMappedParent: In addr (getAccessibleMappedPaddr currentPart s0)).
          {
            apply addrInAccessibleBlockIsAccessibleMapped with blockInCurrentPartitionAddr; try(assumption).
            intuition.
          }
          assert(Hchild1IsParts0: In child1 (getPartitions multiplexer s0)).
          {
            apply childrenPartitionInPartitionList with currentPart; try(assumption).
            unfold consistency in *; unfold consistency1 in *; intuition.
          }
          specialize(HKDIs0 currentPart child1 HparentIsParts0 Hchild1IsParts0 addr HaddrAccMappedParent).
          rewrite HgetConfigPaddrEq in HaddrConfigChild1; try(assumption).
          assert(HgetConfigEqs4s0: forall part, isPDT part s0 -> beqAddr newPDBlockStartAddr part = false
            -> getConfigPaddr part s4 = getConfigPaddr part s0) by intuition.
          assert(Hchild1IsPDTs0: isPDT child1 s0).
          {
            unfold isPDT in *. rewrite Hs4 in Hchild1IsPDTs4. rewrite Hs3 in Hchild1IsPDTs4. simpl in *.
            destruct (beqAddr currentPart child1) eqn:HbeqCurrChild1.
            - rewrite <-DTL.beqAddrTrue in HbeqCurrChild1. subst child1. rewrite HlookupCurrs0. trivial.
            - rewrite HbeqBlockCurr in *. simpl in *.
              destruct (beqAddr blockInCurrentPartitionAddr child1) eqn:HbeqBlockChild1; try(exfalso; congruence).
              rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hchild1IsPDTs4;
                try(apply not_eq_sym; assumption).
              rewrite removeDupIdentity in Hchild1IsPDTs4; try(apply not_eq_sym; assumption).
              rewrite <-HlookupEqs2s0; assumption.
          }
          rewrite HgetConfigEqs4s0 in HaddrConfigChild1; try(assumption). congruence.
        }
        assert(HendBlocks0: bentryEndAddr blockInCurrentPartitionAddr newPDBlockEndAddr s0) by intuition.
        contradict HaddrNotInBlock. simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        rewrite HlookupBlocks0 in *. rewrite <-Hstart. rewrite <-HendBlocks0. rewrite app_nil_r.
        apply getAllPaddrBlockInclRevAux in HaddrNotInBlock.
        destruct HaddrNotInBlock as (HlebStartAddr & HltAddrEndMin & HblockNotEmpty).
        assert(HblockSize: i blockSize = newPDBlockEndAddr - newPDBlockStartAddr) by intuition.
        assert(HltBlockSizeLen: false = indexLt blockSize PDStructureTotalLength) by intuition.
        assert(PDStructureTotalLength = Constants.PDStructureTotalLength) by intuition. subst PDStructureTotalLength.
        unfold indexLt in HltBlockSizeLen. apply eq_sym in HltBlockSizeLen.
        apply PeanoNat.Nat.ltb_ge in HltBlockSizeLen. rewrite HblockSize in HltBlockSizeLen.
        assert(p newPDBlockStartAddr + i Constants.PDStructureTotalLength <= p newPDBlockEndAddr).
        {
          assert(Hres: i Constants.PDStructureTotalLength + p newPDBlockStartAddr
                  <= p newPDBlockEndAddr - p newPDBlockStartAddr + p newPDBlockStartAddr) by lia.
          rewrite PeanoNat.Nat.sub_add in Hres; lia.
        }
        apply getAllPaddrBlockIncl; lia.
      + assert(Hchild1IsPDTs4: isPDT child1 s4).
        {
          unfold isPDT in *. rewrite Hs in Hchild1IsPDT. simpl in *.
          destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child1) eqn:HbeqBlockSh1Child1;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in Hchild1IsPDT; try(apply not_eq_sym); assumption.
        }
        assert(Hchild2IsPDTs4: isPDT child2 s4).
        {
          unfold isPDT in *. rewrite Hs in Hchild2IsPDT. simpl in *.
          destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child2) eqn:HbeqBlockSh1Child2;
            try(exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in Hchild2IsPDT; try(apply not_eq_sym); assumption.
        }
        assert(HparentIsPDTs4: isPDT pdparent s4).
        {
          apply partitionsArePDT; try(assumption); intuition.
        }
        apply HgetChildrenEq in Hchild1IsChild; try(assumption). simpl in Hchild1IsChild.
        apply HgetChildrenEq in Hchild2IsChild; try(assumption). simpl in Hchild2IsChild.
        destruct Hchild1IsChild as [Hcontra | Hchild1IsChild]; try(exfalso; rewrite <-beqAddrFalse in *; congruence).
        destruct Hchild2IsChild as [Hcontra | Hchild2IsChild]; try(exfalso; rewrite <-beqAddrFalse in *; congruence).
        rewrite HgetPartsEqs4s0 in HparentIsParts0. rewrite HgetChildrenEqs4s0 in Hchild1IsChild; try(assumption).
        rewrite HgetChildrenEqs4s0 in Hchild2IsChild; try(assumption).
        specialize(Hcons0 pdparent child1 child2 HparentIsParts0 Hchild1IsChild Hchild2IsChild HbeqChildren).
        unfold getUsedPaddr in *. rewrite HgetMappedPaddrEq; try(assumption).
        rewrite HgetMappedPaddrEq; try(assumption). rewrite HgetMappedPaddrEqs4s0; try(assumption).
        rewrite HgetMappedPaddrEqs4s0; try(assumption). rewrite HgetConfigPaddrEq; try(assumption).
        rewrite HgetConfigPaddrEq; try(assumption).
        assert(HgetConfigEqs4s0: forall part, isPDT part s0 -> beqAddr newPDBlockStartAddr part = false
          -> getConfigPaddr part s4 = getConfigPaddr part s0) by intuition.
        assert(Hchild1IsPDTs0: isPDT child1 s0).
        {
          unfold isPDT in *. rewrite Hs4 in Hchild1IsPDTs4. rewrite Hs3 in Hchild1IsPDTs4. simpl in *.
          destruct (beqAddr currentPart child1) eqn:HbeqCurrChild1.
          - rewrite <-DTL.beqAddrTrue in HbeqCurrChild1. subst child1. rewrite HlookupCurrs0. trivial.
          - rewrite HbeqBlockCurr in *. simpl in *.
            destruct (beqAddr blockInCurrentPartitionAddr child1) eqn:HbeqBlockChild1; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hchild1IsPDTs4;
              try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hchild1IsPDTs4; try(apply not_eq_sym; assumption).
            rewrite <-HlookupEqs2s0; assumption.
        }
        assert(Hchild2IsPDTs0: isPDT child2 s0).
        {
          unfold isPDT in *. rewrite Hs4 in Hchild2IsPDTs4. rewrite Hs3 in Hchild2IsPDTs4. simpl in *.
          destruct (beqAddr currentPart child2) eqn:HbeqCurrChild2.
          - rewrite <-DTL.beqAddrTrue in HbeqCurrChild2. subst child2. rewrite HlookupCurrs0. trivial.
          - rewrite HbeqBlockCurr in *. simpl in *.
            destruct (beqAddr blockInCurrentPartitionAddr child2) eqn:HbeqBlockChild2; try(exfalso; congruence).
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in Hchild2IsPDTs4;
              try(apply not_eq_sym; assumption).
            rewrite removeDupIdentity in Hchild2IsPDTs4; try(apply not_eq_sym; assumption).
            rewrite <-HlookupEqs2s0; assumption.
        }
        rewrite HgetConfigEqs4s0; try(assumption). rewrite HgetConfigEqs4s0; assumption.
    (* END partitionsIsolation *)
  }
  assert(verticalSharing s).
  { (* BEGIN verticalSharing s *)
    assert(Hcons0: verticalSharing s0) by intuition. intros pdparent child HparentIsPart HchildIsChild.
    assert(HisParent: isParent s) by assumption. specialize(HisParent child pdparent HparentIsPart HchildIsChild).
    destruct (beqAddr newPDBlockStartAddr pdparent) eqn:HbeqStartParent.
    {
      exfalso. rewrite <-DTL.beqAddrTrue in HbeqStartParent. subst pdparent. unfold getChildren in HchildIsChild.
      unfold getMappedBlocks in HchildIsChild. unfold getKSEntries in HchildIsChild. rewrite HlookupNews in *.
      rewrite HnewPDentry in HchildIsChild. simpl in *. congruence.
    }
    assert(HparentIsParts0: In pdparent (getPartitions multiplexer s4)).
    {
      rewrite HgetPartsEqs4. rewrite HgetPartsEqs in HparentIsPart. apply in_app_or in HparentIsPart. apply in_or_app.
      simpl in HparentIsPart. rewrite <-beqAddrFalse in *. simpl in *.
      destruct HparentIsPart as [HparentIsLeft | HparentIsPartR]; try(left; assumption). right.
      destruct HparentIsPartR as [Hcontra | HparentIsRight]; try(exfalso; congruence). assumption.
    }
    assert(HchildIsPDT: isPDT child s).
    { apply childrenArePDT with pdparent; assumption. }
    destruct (beqAddr newPDBlockStartAddr child) eqn:HbeqStartChild.
    - rewrite <-DTL.beqAddrTrue in HbeqStartChild. subst child. unfold pdentryParent in *. rewrite HlookupNews in *.
      rewrite HnewPDentry in HisParent. simpl in *. subst pdparent. intros addr HaddrInNew. unfold getUsedPaddr in *.
      unfold getConfigPaddr in HaddrInNew. unfold getMappedPaddr in HaddrInNew. unfold getConfigBlocks in *.
      unfold getMappedBlocks in HaddrInNew. unfold getKSEntries in HaddrInNew. simpl in *. rewrite HlookupNews in *.
      rewrite HnewPDentry in HaddrInNew. simpl in *.
      assert(HnoConfig: (filterOptionPaddr (getConfigBlocksAux (maxIdx + 1) nullAddr s (CIndex maxNbPrepare)))
                        = []).
      {
        rewrite MaxIdxNextEq. simpl. unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (beqAddr p nullAddr); try(simpl; reflexivity).
      }
      rewrite HnoConfig in HaddrInNew. simpl in *. repeat rewrite app_nil_r in HaddrInNew.
      assert(HaddrInBlock: In addr (getAllPaddrAux [blockInCurrentPartitionAddr] s)).
      {
        simpl. rewrite HlookupBlocks. rewrite HnewBentry. simpl. rewrite app_nil_r.
        assert(HendBlocks0: bentryEndAddr blockInCurrentPartitionAddr newPDBlockEndAddr s0) by intuition.
        assert(HwellFormed: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        assert(HPFlags0: bentryPFlag blockInCurrentPartitionAddr true s0) by intuition.
        specialize(HwellFormed blockInCurrentPartitionAddr newPDBlockStartAddr newPDBlockEndAddr HPFlags0 Hstart
          HendBlocks0). destruct HwellFormed as (HwellFormed & _).
        assert(HblockSize: i blockSize = newPDBlockEndAddr - newPDBlockStartAddr) by intuition.
        assert(HltBlockSizeLen: false = indexLt blockSize PDStructureTotalLength) by intuition.
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBlocks0 in *. rewrite <-HendBlocks0.
        rewrite <-Hstart. unfold indexLt in HltBlockSizeLen. apply eq_sym in HltBlockSizeLen.
        apply PeanoNat.Nat.ltb_ge in HltBlockSizeLen. rewrite HblockSize in HltBlockSizeLen.
        assert(PDStructureTotalLength = Constants.PDStructureTotalLength) by intuition. subst PDStructureTotalLength.
        assert(p newPDBlockStartAddr + i Constants.PDStructureTotalLength <= p newPDBlockEndAddr).
        {
          assert(Hres: i Constants.PDStructureTotalLength + p newPDBlockStartAddr
                  <= p newPDBlockEndAddr - p newPDBlockStartAddr + p newPDBlockStartAddr) by lia.
          rewrite PeanoNat.Nat.sub_add in Hres; lia.
        }
        apply getAllPaddrBlockInclRevAux in HaddrInNew.
        destruct HaddrInNew as (HlebStartAddr & HltAddrMinEnd & HsizeIsPos). apply getAllPaddrBlockIncl; lia.
      }
      apply addrInBlockIsMapped with blockInCurrentPartitionAddr; try(assumption).
      rewrite HgetMappedBlocksEq; try(apply partitionsArePDT; assumption). rewrite HgetMappedBlocksCurrEqs4s0.
      assumption.
    - assert(HparentIsPDTs4: isPDT pdparent s4).
      {
        apply partitionsArePDT; try(assumption); intuition.
      }
      apply HgetChildrenEq in HchildIsChild; try(assumption). simpl in HchildIsChild.
      destruct HchildIsChild as [Hcontra | HchildIsChild]; try(exfalso; rewrite <-beqAddrFalse in *; congruence).
      rewrite HgetPartsEqs4s0 in HparentIsParts0. rewrite HgetChildrenEqs4s0 in HchildIsChild; try(assumption).
      specialize(Hcons0 pdparent child HparentIsParts0 HchildIsChild). unfold getUsedPaddr in *.
      assert(HchildIsPDTs4: isPDT child s4).
      {
        unfold isPDT in *. rewrite Hs in HchildIsPDT. simpl in *.
        destruct (beqAddr (CPaddr (blockInCurrentPartitionAddr + sh1offset)) child) eqn:HbeqBlockSh1Child;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in HchildIsPDT; try(apply not_eq_sym); assumption.
      }
      assert(HgetConfigEqs4s0: forall part, isPDT part s0 -> beqAddr newPDBlockStartAddr part = false
        -> getConfigPaddr part s4 = getConfigPaddr part s0) by intuition.
      assert(HchildIsPDTs0: isPDT child s0).
      {
        unfold isPDT in *. rewrite Hs4 in HchildIsPDTs4. rewrite Hs3 in HchildIsPDTs4. simpl in *.
        destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
        - rewrite <-DTL.beqAddrTrue in HbeqCurrChild. subst child. rewrite HlookupCurrs0. trivial.
        - rewrite HbeqBlockCurr in *. simpl in *.
          destruct (beqAddr blockInCurrentPartitionAddr child) eqn:HbeqBlockChild; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HchildIsPDTs4;
            try(apply not_eq_sym; assumption).
          rewrite removeDupIdentity in HchildIsPDTs4; try(apply not_eq_sym; assumption).
          rewrite <-HlookupEqs2s0; assumption.
      }
      rewrite HgetConfigPaddrEq; try(assumption). rewrite HgetConfigEqs4s0; try(assumption).
      rewrite HgetMappedPaddrEq; try(assumption). rewrite HgetMappedPaddrEq; try(assumption).
      rewrite HgetMappedPaddrEqs4s0; try(assumption). rewrite HgetMappedPaddrEqs4s0; try(assumption).
      apply partitionsArePDT; assumption.
    (* END verticalSharing *)
  }
  (*assert(consistency s). { unfold consistency. unfold consistency1. unfold consistency2. intuition. }*)
  instantiate(1 := fun s =>
    consistency1 s
    /\ noDupUsedPaddrList s
    /\ sharedBlockPointsToChild s
    /\ adressesRangePreservedIfOriginAndNextOk s
    /\ childsBlocksPropsInParent s
    /\ noChildImpliesAddressesNotShared s
    /\ kernelsAreNotAccessible s
    /\ partitionsIsolation s
    /\ verticalSharing s
    /\ exists s4 s3 s2 s0 newBentry bentry newPDCurr pdentryCurr newPDentry newSh1entry sh1entry realMPU,
        (* properties of s *)
        s = {|
              currentPartition := currentPartition s4;
              memory :=
                add (CPaddr (blockInCurrentPartitionAddr + sh1offset))
                  (SHE newSh1entry) (memory s4) beqAddr
            |}
        /\ (forall part, isPDT part s -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s4)
        /\ (forall part, isPDT part s -> getMappedPaddr part s = getMappedPaddr part s4)
        /\ (forall part, In part (getPartitions multiplexer s)
              -> In part (newPDBlockStartAddr :: getPartitions multiplexer s4))
        /\ (forall part, isPDT part s4 -> forall addr, In addr (getChildren part s)
              -> In addr (newPDBlockStartAddr :: getChildren part s4))
        /\ (forall part, In part (getPartitions multiplexer s0) -> part <> currentPart
              -> getChildren part s = getChildren part s0)
        /\ lookup blockInCurrentPartitionAddr (memory s) beqAddr = Some (BE newBentry)
        /\ lookup newPDBlockStartAddr (memory s) beqAddr = Some (PDT newPDentry)
        (* properties of s4 *)
        /\ s4 = {|
                  currentPartition := currentPartition s3;
                  memory := add currentPart (PDT newPDCurr) (memory s3) beqAddr
                |}
        /\ getPartitions multiplexer s4 = getPartitions multiplexer s0
        /\ In currentPart (getPartitions multiplexer s4)
        /\ lookup blockInCurrentPartitionAddr (memory s4) beqAddr = Some (BE newBentry)
        /\ lookup currentPart (memory s4) beqAddr = Some (PDT newPDCurr)
        /\ lookup newPDBlockStartAddr (memory s4) beqAddr = Some (PDT newPDentry)
        /\ lookup (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (memory s4) beqAddr = Some (SHE sh1entry)
        /\ currentPart = currentPartition s4
        /\ (forall part, In part (getPartitions multiplexer s0) -> getChildren part s4 = getChildren part s0)
        /\ (forall addr, In addr (getAccessibleMappedPaddr currentPart s0)
            <-> In addr (getAllPaddrAux [blockInCurrentPartitionAddr] s4 ++ getAccessibleMappedPaddr currentPart s4))
        /\ (forall part, isPDT part s4 -> isPDT part s0 -> beqAddr newPDBlockStartAddr part = false
            -> part <> currentPart -> getAccessibleMappedPaddr part s0 = getAccessibleMappedPaddr part s4)
        /\ (forall part, isPDT part s4 -> beqAddr newPDBlockStartAddr part = false
            -> getMappedPaddr part s4 = getMappedPaddr part s0)
        (* properties of s3 *)
        /\ s3 = {|
                  currentPartition := currentPartition s2;
                  memory := add blockInCurrentPartitionAddr (BE newBentry) (memory s2) beqAddr
                |}
        /\ lookup currentPart (memory s3) beqAddr = Some (PDT pdentryCurr)
        /\ lookup blockInCurrentPartitionAddr (memory s3) beqAddr = Some (BE newBentry)
        (* properties of s2 *)
        /\ lookup blockInCurrentPartitionAddr (memory s2) beqAddr = Some (BE bentry)
        /\ lookup currentPart (memory s2) beqAddr = Some (PDT pdentryCurr)
        /\ lookup newPDBlockStartAddr (memory s2) beqAddr = Some (PDT newPDentry)
        /\ (forall addr, newPDBlockStartAddr <> addr
            -> lookup addr (memory s2) beqAddr = lookup addr (memory s0) beqAddr)
        (* properties of s0 *)
        /\ lookup blockInCurrentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
        /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentryCurr)
        /\ lookup (CPaddr (blockInCurrentPartitionAddr + sh1offset)) (memory s0) beqAddr = Some (SHE sh1entry)
        /\ consistency s0
        /\ kernelDataIsolation s0
        /\ verticalSharing s0
        /\ partitionsIsolation s0
        /\ bentryStartAddr blockInCurrentPartitionAddr newPDBlockStartAddr s0
        /\ bentryEndAddr blockInCurrentPartitionAddr newPDBlockEndAddr s0
        /\ bentryAFlag blockInCurrentPartitionAddr true s0
        /\ bentryPFlag blockInCurrentPartitionAddr true s0
        /\ currentPart = currentPartition s0
        /\ In blockInCurrentPartitionAddr (getMappedBlocks currentPart s0)
        /\ lookup newPDBlockStartAddr (memory s0) beqAddr = None
        /\ (exists sh1entry sh1entryaddr, lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
            /\ sh1entryPDchild sh1entryaddr nullAddr s0 /\ sh1entryAddr blockInCurrentPartitionAddr sh1entryaddr s0)
        (* other properties *)
        /\ newSh1entry =
            {| PDchild := PDchild sh1entry; PDflag := true; inChildLocation := inChildLocation sh1entry |}
        /\ newPDCurr =
            {|
              structure := structure pdentryCurr;
              firstfreeslot := firstfreeslot pdentryCurr;
              nbfreeslots := nbfreeslots pdentryCurr;
              nbprepare := nbprepare pdentryCurr;
              parent := parent pdentryCurr;
              MPU := MAL.removeBlockFromPhysicalMPUAux blockInCurrentPartitionAddr realMPU;
              vidtAddr := vidtAddr pdentryCurr
            |}
        /\ (exists l,
              newBentry =
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
        /\ newPDentry =
            {|
              structure := nullAddr;
              firstfreeslot := nullAddr;
              nbfreeslots := zero;
              nbprepare := zero;
              parent := currentPart;
              MPU := [];
              vidtAddr := nullAddr
            |}
        /\ PDflag sh1entry = false
        (*/\ idBlock = blockInCurrentPartitionAddr*)
        /\ beqAddr newPDBlockStartAddr blockInCurrentPartitionAddr = false
        /\ beqAddr nullAddr blockInCurrentPartitionAddr = false
        /\ minBlockSize = Constants.minBlockSize
        /\ false = indexLt blockSize minBlockSize
        /\ PDStructureTotalLength = Constants.PDStructureTotalLength
        /\ false = indexLt blockSize PDStructureTotalLength
        /\ i blockSize = newPDBlockEndAddr - newPDBlockStartAddr
        /\ beqAddr blockInCurrentPartitionAddr currentPart = false
        /\ beqAddr currentPart newPDBlockStartAddr = false). simpl. unfold consistency1. intuition.
  - exists s4. exists s3. exists s2. exists s0. exists newBentry. exists bentry. exists newPDCurr. exists pdentry.
    exists newPDentry. exists {|
                                PDchild := PDchild sh1entry;
                                PDflag := true;
                                inChildLocation := inChildLocation sh1entry
                              |}. exists sh1entry. exists realMPU. intuition.
  - exists newBentry. assumption.
}
intro blockOrigin. eapply bindRev.
{ (* MAL.readBlockStartFromBlockEntryAddr *)
  eapply weaken. apply readBlockStartFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as ((_ & _ & _ & _ & _ & _ & _ & _ & _ & [_ [_ [_ [_ [newBentry [_ [_ [_ [_ [_ [_ [_ (_ & _ & _
    & _ & _ & _ & HlookupBlock & _)]]]]]]]]]]]]) & _). unfold isBE. rewrite HlookupBlock. trivial.
}
intro blockStart. eapply bindRev.
{ (* MAL.readBlockEndFromBlockEntryAddr *)
  eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as (_ & Hstart). unfold isBE. unfold bentryStartAddr in Hstart.
  destruct (lookup blockInCurrentPartitionAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  trivial.
}
intro blockEnd. eapply bindRev.
{ (* MAL.readSCNextFromBlockEntryAddr *)
  eapply weaken. apply readSCNextFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as ((((Hcons & _ & _ & _ & _ & _ & _ & _ & _ & [_ [_ [_ [_ [newBentry [_ [_ [_ [_ [_ [_ [_ (_ & _ &
    _ & _ & _ & _ & HlookupBlock & _)]]]]]]]]]]]]) & _) & _) & _). unfold consistency1 in *. intuition.
  exists newBentry. assumption.
}
intro blockNext. destruct (beqAddr blockOrigin blockStart && beqAddr blockNext nullAddr) eqn:HisBlockCut.
- eapply bindRev.
  { (* Internal.writeAccessibleRec *)
    admit. (*eapply weaken. apply ?. intros s Hprops. simpl. apply Hprops.*)
  }
  intro. eapply weaken. apply WP.ret. intros s Hprops. simpl.
- eapply weaken. apply WP.ret. intros s Hprops. simpl.
  (*TODO if the block has been cut before, it was already inaccessible in the ancestors*)


(*TODO modify writeAccessibleRecAuxFalse*)
Qed.

