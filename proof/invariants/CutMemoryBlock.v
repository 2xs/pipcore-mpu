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

Require Import Model.ADT Model.Lib Model.MAL.
Require Import Core.Services.

Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.InternalLemmas Proof.DependentTypeLemmas.

Require Import Invariants (*GetTableAddr UpdateShadow2Structure UpdateShadow1Structure
               PropagatedProperties MapMMUPage*) Proof.invariants.findBlockInKSWithAddr.

Require Import isBuiltFromWriteAccessibleRec writeAccessibleToAncestorsIfNotCutRec insertNewEntry.

Require Import Bool List EqNat Lia.

Require Import Model.Monad.

Module WP := WeakestPreconditions.

(*Lemma filterPresentIsPresent block s l:
In block (filterPresent l s)
-> In block l
   /\ exists blockBentry : BlockEntry,
      lookup block (memory s) beqAddr = Some (BE blockBentry) /\ present blockBentry = true.
Proof.
induction l.
- simpl. intuition.
- intro HisInFilter. simpl in HisInFilter. destruct (lookup a (memory s) beqAddr) eqn:Hlookupa.
  + destruct v eqn:Hlookupa2.
    * destruct (present b) eqn:Hpresentb.
      -- simpl in HisInFilter. destruct HisInFilter as [HisBlock | HisNotBlock].
         ++ split. simpl. left. assumption. exists b. subst a. intuition.
         ++ split. simpl. right. apply IHl. intuition. apply IHl. intuition.
      -- split. simpl. right. apply IHl. intuition. apply IHl. intuition.
    * split. simpl. right. apply IHl. intuition. apply IHl. intuition.
    * split. simpl. right. apply IHl. intuition. apply IHl. intuition.
    * split. simpl. right. apply IHl. intuition. apply IHl. intuition.
    * split. simpl. right. apply IHl. intuition. apply IHl. intuition.
  + split. simpl. right. apply IHl. intuition. apply IHl. intuition.
Qed.

Lemma presentIsInFilterPresent block s l :
In block l
-> (exists blockBentry : BlockEntry,
      lookup block (memory s) beqAddr = Some (BE blockBentry) /\ present blockBentry = true)
-> In block (filterPresent l s).
Proof.
induction l.
- simpl. intuition.
- intros HinList Hbentry. simpl in HinList.
  destruct HinList as [HisBlock | HinList].
  + subst a. simpl. destruct Hbentry as [blockBentry (HlookupBlock & HisPresent)]. rewrite HlookupBlock.
    rewrite HisPresent. intuition.
  + simpl. destruct (lookup a (memory s) beqAddr).
    * destruct v; try(apply IHl; assumption).
      destruct (present b); try(apply IHl; assumption).
      simpl. right. apply IHl; assumption.
    * apply IHl; assumption.
Qed.*)


(*Require Import insertNewEntry.*)

(** * Summary 
    This file contains the invariant of [addVaddr]. 
    We prove that this PIP service preserves the isolation property *)

Lemma cutMemoryBlock (idBlockToCut cutAddr : paddr) (MPURegionNb : index) :
{{fun s => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }} 
cutMemoryBlock idBlockToCut cutAddr MPURegionNb
{{fun _ s  => partitionsIsolation s   /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold cutMemoryBlock.
(** getCurPartition **)
eapply WP.bindRev.
eapply WP.weaken. 
eapply Invariants.getCurPartition.
cbn.
intros.
(*destruct H as (HI&KI&VS&HC). apply (conj HI (conj KI VS)).*) apply H.
intro currentPart.
(** readPDNbFreeSlots *)
eapply WP.bindRev.
{
	eapply weaken.
-	apply Invariants.readPDNbFreeSlots.
- intros. simpl. split. apply H. intuition.
  unfold consistency in H4. unfold consistency1 in H4.
  subst currentPart. apply currentPartIsPDT; intuition.
}
	intro nbFreeSlots.
	eapply WP.bindRev. apply Invariants.Index.zero.

	intro zero.

	eapply bindRev.
{ (*MALInternal.Index.leb nbfreeslots zero *)
	eapply weaken. apply Invariants.Index.leb.
	intros. simpl. apply H.
}
	intro isFull.
	case_eq (isFull).
	{ (*case_eq isFull = false *)
		intros. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
	}
	(*case_eq isFull = true *)
	intros.

(** findBlockInKSWithAddr **)
eapply WP.bindRev.
{
  eapply weaken.
  eapply findBlockInKSWithAddr.
  intros s Hprops.
  simpl. split. apply Hprops. (* ? *)
  intuition. unfold consistency in H8. unfold consistency1 in H8.
  subst currentPart. apply currentPartIsPDT; intuition.
}
intro blockToShareInCurrPartAddr.
(** compareAddrToNull **)
eapply WP.bindRev.
eapply Invariants.compareAddrToNull.
intro addrIsNull.
case_eq addrIsNull.
{intros. eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition. }

	intros. eapply bindRev.
{
	eapply weaken. apply readBlockAccessibleFromBlockEntryAddr. 
	intros. simpl. split. apply H1.
	unfold isBE. intuition.
  rewrite <-beqAddrFalse in H3. apply not_eq_sym in H3. contradiction.
  destruct H11. intuition.
	rewrite -> H11. trivial.

}
	intro addrIsAccessible.
	case_eq (addrIsAccessible).
	2 : { (*case_eq addrIsAccessible = false *)
		intros. simpl. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
	}
	(*case_eq addrIsAccessible = true *)
	intros. simpl. eapply bindRev.
		{ eapply weaken. apply Invariants.readSh1PDChildFromBlockEntryAddr. intros.
			intros. simpl. split. apply H2. 
			intros. simpl.

			split. apply H2. destruct H2 ; destruct H2. destruct H2 ; destruct H5.
      intuition. rewrite <-beqAddrFalse in H4. apply not_eq_sym in H4. contradiction.
      destruct H13.

	 		exists x. apply H6.
 		}
		intro PDChildAddr.
(** compareAddrToNull **)
eapply WP.bindRev.
{ eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H2.
}
intro PDChildAddrIsNull.
case_eq PDChildAddrIsNull.
2 : {	(* PDChildAddrIsNull = false -> shared *) 
	intros. simpl. eapply WP.weaken.
  eapply WP.ret.
  simpl. intros.
  intuition.
}

	intros. simpl.
	(** readBlockStartFromBlockEntryAddr **)
	eapply bindRev.
{	eapply weaken. apply readBlockStartFromBlockEntryAddr.
	intros. simpl. split. apply H3.
	unfold isBE. intuition. rewrite <-beqAddrFalse in H8. apply not_eq_sym in H8. contradiction.
  destruct H16. intuition.
	rewrite -> H16. trivial.
}
	intro blockToCutStartAddr.
	eapply WP.bindRev.
{ eapply weaken. apply Invariants.Paddr.leb.
	intros. simpl. apply H3.
}
	intro isCutAddrBelowStart.
	case_eq (isCutAddrBelowStart).
{ (*case_eq isCutAddrBelowStart = true *)
		intros. simpl. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
}
	(*case_eq isCutAddrBelowStart = false *)
	intros. simpl.
	eapply bindRev.
{	eapply weaken. apply readBlockEndFromBlockEntryAddr.
	intros. simpl. split. apply H4.
	unfold isBE. intuition.
  rewrite <-beqAddrFalse in H11. apply not_eq_sym in H11. contradiction.
  destruct H19. intuition. rewrite -> H19. trivial.
}
	intro blockToCutEndAddr.
	(* leb *)
	eapply WP.bindRev.
{ eapply weaken. apply Invariants.Paddr.leb.
	intros. simpl. apply H4.
}
	intro isCutAddrAboveEnd.
	case_eq (isCutAddrAboveEnd).
{ (*case_eq isCutAddrAboveEnd = true *)
		intros. simpl. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
}
	(*case_eq isCutAddrAboveEnd = false *)
	intros. simpl.
	(** Paddr.subPaddr cutAddr blockToCutStartAddr **)
	eapply bindRev.
{	eapply weaken. apply Invariants.Paddr.subPaddr.
	intros. simpl. split. apply H5.
	intuition;
	(* cutAddr and blockToCutAddr can't be > maxAddr, so sub is OK *)
	rewrite maxIdxEqualMaxAddr.
  rewrite <-beqAddrFalse in H14. apply not_eq_sym in H14. contradiction.
	destruct cutAddr. destruct blockToCutStartAddr. simpl.
  destruct H22 as [entry H22]. intuition.
	unfold StateLib.Paddr.leb in H7. simpl in *. apply eq_sym in H7.
  assert (Hinf: p < blockToCutEndAddr). { apply Compare_dec.leb_complete_conv. exact H7. }
  unfold bentryEndAddr in H8.
  destruct (lookup blockToShareInCurrPartAddr (memory s) beqAddr); intuition. destruct v; intuition.
  assert (HpBis: forall p': paddr, p' <= maxAddr).
  { intro p'. destruct p'. simpl. apply Hp1. }
  assert (Hinter: blockToCutEndAddr <= maxAddr) by apply HpBis.
  lia.
}	
	intro subblock1Size.

	(** Paddr.subPaddr blockToCutEndAddr cutAddr **)
	eapply bindRev.
{	eapply weaken. apply Invariants.Paddr.subPaddr.
	intros. simpl. split. apply H5.
	intuition.
  rewrite <-beqAddrFalse in H15. apply not_eq_sym in H15. contradiction.
	(* cutAddr and blockToCutAddr can't be > maxAddr, so sub is OK *)
	rewrite maxIdxEqualMaxAddr.
	destruct cutAddr. destruct blockToCutEndAddr.	simpl.
  destruct H23 as [entry H23]. intuition.
	unfold StateLib.Paddr.leb in H10. simpl in *. apply eq_sym in H10.
  assert (Hinf: blockToCutStartAddr < p). { apply Compare_dec.leb_complete_conv. exact H10. }
  (*unfold bentryStartAddr in H11.
  destruct (lookup blockToShareInCurrPartAddr (memory s) beqAddr); intuition. destruct v; intuition.*)
  assert (HpBis: forall p': paddr, 0 <= p').
  { intro p'. destruct p'. simpl. apply PeanoNat.Nat.le_0_l. }
  assert (Hinter: 0 <= blockToCutStartAddr) by apply HpBis.
  lia.
}	
	intro subblock2Size.
	(** getMinBlockSize **)
	eapply bindRev.
{	eapply weaken. apply Invariants.getMinBlockSize.
	intros. simpl. apply H5.
}
	intro minBlockSize.
	(* MALInternal.Index.ltb *)
	eapply bindRev.
{ eapply weaken. apply Invariants.Index.ltb.
	intros. simpl. apply H5.
}
	intro isBlock1TooSmall.
	(* MALInternal.Index.ltb *)
	eapply bindRev.
{ eapply weaken. apply Invariants.Index.ltb.
	intros. simpl. apply H5.
}
	intro isBlock2TooSmall.
	case_eq (isBlock1TooSmall || isBlock2TooSmall).
{	(* case_eq isBlock1TooSmall || isBlock2TooSmall = true *)
		intros. simpl. eapply weaken. apply WP.ret.
		intros. simpl. intuition.
}
	(*case_eq isCutAddrAboveEnd = false *)
	intros. simpl.
	(*check32Aligned *)
	eapply bindRev.
{ eapply weaken. apply check32Aligned.
	intros. simpl.
	split. apply H6. intuition.
}
	intro isCutAddrValid.
	case_eq(negb isCutAddrValid).
{ (* case_eq negb isCutAddrValid = true *)
	intros. simpl. eapply weaken. apply WP.ret.
	intros. simpl. intuition.
}
	(*case_eq negb isCutAddrValid = false *)
	intros. simpl.
	eapply bindRev.
{ (* Internal.writeAccessibleToAncestorsIfNotCutRec *)
  eapply weaken. eapply writeAccessibleToAncestorsIfNotCutRec.
	intros s Hprops. simpl.
  assert(HcurrentPart: currentPartitionInPartitionsList s)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HPDflag: PDTIfPDFlag s)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HmultiPDT: multiplexerIsPDT s)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HcurrentIsPDT: isPDT (currentPartition s) s) by (apply currentPartIsPDT; intuition).
  assert(HcurrEq: currentPart = currentPartition s) by intuition.
  rewrite <- HcurrEq in *.
  assert(HpropsPlus: partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
                    /\ currentPart = currentPartition s /\ pdentryNbFreeSlots currentPart nbFreeSlots s
                    /\ zero = CIndex 0 /\ false = StateLib.Index.leb nbFreeSlots zero
                    /\ (exists entry : BlockEntry,
                           lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry))
                    /\ blockToShareInCurrPartAddr = idBlockToCut
                    /\ bentryPFlag blockToShareInCurrPartAddr true s
                    /\ In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)
                    /\ bentryAFlag blockToShareInCurrPartAddr true s
                    /\ (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
                         lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) /\
                         sh1entryPDchild sh1entryaddr PDChildAddr s /\
                         sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s)
                    /\ beqAddr nullAddr PDChildAddr = true
                    /\ bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s
                    /\ false = StateLib.Paddr.leb cutAddr blockToCutStartAddr
                    /\ bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s
                    /\ false = StateLib.Paddr.leb blockToCutEndAddr cutAddr
                    /\ StateLib.Paddr.subPaddr cutAddr blockToCutStartAddr = Some subblock1Size
                    /\ StateLib.Paddr.subPaddr blockToCutEndAddr cutAddr = Some subblock2Size
                    /\ minBlockSize = Constants.minBlockSize
                    /\ isBlock1TooSmall = StateLib.Index.ltb subblock1Size minBlockSize
                    /\ isBlock2TooSmall = StateLib.Index.ltb subblock2Size minBlockSize
                    /\ isCutAddrValid = is32Aligned cutAddr
                    /\ isPDT currentPart s).
  {
    rewrite <-beqAddrFalse in *.
    assert(HBE: exists entry,
                     lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry) /\
                     blockToShareInCurrPartAddr = idBlockToCut /\
                     bentryPFlag blockToShareInCurrPartAddr true s /\
                     In blockToShareInCurrPartAddr (getMappedBlocks currentPart s)) by intuition.
    destruct HBE as [bentry HpropsBE]. intuition; try(congruence). exists bentry. assumption.
  }
  split. intuition. split. intuition. split. intuition.
  split. apply HpropsPlus. split. intuition. apply isPDTLookupEq in HcurrentIsPDT.
  rewrite <-beqAddrFalse in *. intuition; try(congruence).
  assert(HcurrIsPart: currentPartitionInPartitionsList s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
  unfold currentPartitionInPartitionsList in HcurrIsPart. rewrite <-HcurrEq in HcurrIsPart. assumption.
}
	intro writeAccessibleToAncestorsIfNotCutRecCompleted. simpl.
	eapply bindRev.
{ (* MAL.readBlockEndFromBlockEntryAddr *)
	eapply weaken. apply readBlockEndFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops. apply isBELookupEq.
  destruct Hprops as (HPI & HKDI & HVS & Hconsist & [s0 [pdentry [pdbasepart [blokOrigin [blockStart [blockEnd
          [blockNext [parentsList [statesList Hprops]]]]]]]]]).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  assert(HBEs: isBE blockToShareInCurrPartAddr s).
  {
    apply stableBEIsBuilt with statesList s0 parentsList pdbasepart blockStart blockEnd false; intuition.
  }
  apply isBELookupEq. assumption.
}
	intro blockEndAddr.
	eapply bindRev.
{ (* readSCOriginFromBlockEntryAddr *)
	eapply weaken. apply readSCOriginFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops. split. intuition.
  destruct Hprops as ((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [pdbasepart [blokOrigin [blockStart [blockEnd
          [blockNext [parentsList [statesList Hprops]]]]]]]]]) & _).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  assert(HBEs: isBE blockToShareInCurrPartAddr s).
  {
    apply stableBEIsBuilt with statesList s0 parentsList pdbasepart blockStart blockEnd false; intuition.
  }
  apply isBELookupEq. assumption.
}
	intro blockOrigin.
	eapply bindRev.
{ (* MAL.readBlockRFromBlockEntryAddr *)
	eapply weaken. apply readBlockRFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as (((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [pdbasepart [blokOrigin [blockStart [blockEnd
          [blockNext [parentsList [statesList Hprops]]]]]]]]]) & _) & _).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  apply stableBEIsBuilt with statesList s0 parentsList pdbasepart blockStart blockEnd false; intuition.
}
	intro blockR.
	eapply bindRev.
{ (*MAL.readBlockWFromBlockEntryAddr *)
	eapply weaken. apply readBlockWFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as ((((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [pdbasepart [blokOrigin [blockStart [blockEnd
          [blockNext [parentsList [statesList Hprops]]]]]]]]]) & _) & _) & _).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  apply stableBEIsBuilt with statesList s0 parentsList pdbasepart blockStart blockEnd false; intuition.
}
	intro blockW.
	eapply bindRev.
{ (* MAL.readBlockXFromBlockEntryAddr *)
	eapply weaken. apply readBlockXFromBlockEntryAddr.
	intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as (((((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [pdbasepart [blokOrigin [blockStart
          [blockEnd [blockNext [parentsList [statesList Hprops]]]]]]]]]) & _) & _) & _) & _).
  assert(HBE: exists entry, lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE entry)) by intuition.
  destruct HBE as [bentry Hlookup].
  assert(HBE: isBE blockToShareInCurrPartAddr s0) by (unfold isBE; rewrite Hlookup; trivial).
  apply stableBEIsBuilt with statesList s0 parentsList pdbasepart blockStart blockEnd false; intuition.
}
	intro blockX.
	eapply bindRev.
{ (* Internal.insertNewEntry *)
	eapply weaken. apply insertNewEntry.
	intros s Hprops. simpl. pose proof Hprops as HpropsCopy.
  destruct Hprops as ((((((HPI & HKDI & HVS & Hconsist & [s0 [pdentry [pdbasepart [blockOriginBis [blockStart
      [blockEnd [blockNext [parentsList [statesList Hprops]]]]]]]]]) & HendBlock) & Hscentry) & HRFlag) & HWFlag)
      & HXFlag). split. assumption. split.
  {
    assert(HlookupCurr: lookup currentPart (memory s) beqAddr = Some (PDT pdentry)) by intuition. exists pdentry.
    split. assumption. intro HcurrNotRoot.
    assert(HparentOfPart: parentOfPartitionIsPartition s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(HparentOfPart currentPart pdentry HlookupCurr). destruct HparentOfPart as (HparentIsPart & _).
    specialize(HparentIsPart HcurrNotRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart). split. unfold isPDT.
    rewrite HlookupParent. trivial.
    assert(HblockEquivParent: blockInChildHasAtLeastEquivalentBlockInParent s)
        by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HwellFormed: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
    split.
    - intros addr HaddrInRange.
      assert(HaddrInParent: childPaddrIsIntoParent s) by (apply blockInclImpliesAddrIncl; assumption).
      unfold childPaddrIsIntoParent in HaddrInParent. apply HaddrInParent with currentPart. assumption.
      assert(HisChild: isChild s) by (unfold consistency in *; unfold consistency1 in *; intuition).
      unfold isChild in HisChild. apply HisChild.
      + assert(In currentPart (getPartitions multiplexer s0)) by intuition.
        assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
        { (*TODO HERE probably needs an update of isBuiltFromWriteAccessibleRec...*)
          apply getPartitionsEqBuiltWithWriteAccInter with statesList parentsList blockStart blockEnd pdbasepart
false blockBase, bentryBase.
        }
      + 
      + 
    - 
  }
  - unfold StateLib.Index.leb in H19. apply eq_sym in H19. apply Compare_dec.leb_iff_conv in H19. lia.
  - apply isPDTLookupEq in H35. destruct H35 as [pdentry Hlookup].
    assert(pdentryFirstFreeSlot currentPart (firstfreeslot pdentry) s)
            by (apply lookupPDEntryFirstFreeSlot; intuition).
    exists (firstfreeslot pdentry). split. assumption.
    admit.
  (*TODO we know that there are free slots, so the first one cannot be null, but how to prove that ?*)
  - unfold bentryEndAddr in *. destruct H20 as [bentry (Hlookupb & Hbentry)]. rewrite Hlookupb in *.
    subst blockEndAddr. subst blockToCutEndAddr. unfold StateLib.Paddr.leb in H27.
    apply eq_sym in H27. apply Compare_dec.leb_iff_conv in H27. lia.
  - subst minBlockSize. unfold bentryEndAddr in *. destruct H20 as [bentry (Hlookupb & Hbentry)].
    rewrite Hlookupb in *. subst blockEndAddr. subst blockToCutEndAddr. unfold StateLib.Paddr.subPaddr in H29.
    destruct (Compare_dec.le_dec (endAddr (blockrange bentry) - cutAddr) maxIdx) eqn:HcompEndCut; try(congruence).
    injection H29. intro HsubBlock2. rewrite <-HsubBlock2 in H32.
    assert(Hblock2NotTooSmall: isBlock2TooSmall = false)
                by (eapply orb_false_elim with isBlock1TooSmall; assumption).
    rewrite Hblock2NotTooSmall in *.
    unfold StateLib.Index.ltb in H32. apply eq_sym in H32. apply PeanoNat.Nat.ltb_ge in H32. (*lia.*)
    (*TODO change the check for isBlock1TooSmall and isBlock2TooSmall ?*)
    admit.
  - assert(Hprops: partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s
      /\ currentPart = currentPartition s
      /\ isPDT currentPart s
      /\ zero = CIndex 0
      /\ pdentryNbFreeSlots currentPart nbFreeSlots s
      /\ false = StateLib.Index.leb nbFreeSlots zero
      /\ bentryXFlag blockToShareInCurrPartAddr blockX s
      /\ bentryWFlag blockToShareInCurrPartAddr blockW s
      /\ bentryRFlag blockToShareInCurrPartAddr blockR s
      /\ (exists (scentry : SCEntry) (scentryaddr : paddr),
            lookup scentryaddr (memory s) beqAddr = Some (SCE scentry) /\
            scentryOrigin scentryaddr blockOrigin s)
      /\ bentryEndAddr blockToShareInCurrPartAddr blockEndAddr s
      /\ (exists entry : BlockEntry,
            lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE entry) /\
            blockToShareInCurrPartAddr = idBlockToCut /\
            bentryPFlag blockToShareInCurrPartAddr true s /\
            In blockToShareInCurrPartAddr (getMappedBlocks currentPart s))
      /\ bentryAFlag blockToShareInCurrPartAddr true s
      /\ (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
            lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry) /\
            sh1entryPDchild sh1entryaddr PDChildAddr s /\
            sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s)
      /\ beqAddr nullAddr PDChildAddr = true
      /\ bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s
      /\ false = StateLib.Paddr.leb cutAddr blockToCutStartAddr
      /\ bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s
      /\ false = StateLib.Paddr.leb blockToCutEndAddr cutAddr
      /\ StateLib.Paddr.subPaddr cutAddr blockToCutStartAddr = Some subblock1Size
      /\ StateLib.Paddr.subPaddr blockToCutEndAddr cutAddr = Some subblock2Size
      /\ minBlockSize = Constants.minBlockSize
      /\ isBlock1TooSmall = StateLib.Index.ltb subblock1Size minBlockSize
      /\ isBlock2TooSmall = StateLib.Index.ltb subblock2Size minBlockSize
      /\ isCutAddrValid = is32Aligned cutAddr) by intuition.
    apply Hprops.
}
	intro idNewSubblock.
	(* MALInternal.Paddr.pred *)
	eapply bindRev.
{ eapply weaken. apply Paddr.pred.
	intros s Hprops. simpl. split. apply Hprops. destruct Hprops as [s0 Hprops]. intuition.
  unfold StateLib.Paddr.leb in H28. apply eq_sym in H28. apply Compare_dec.leb_iff_conv in H28. lia.
}
	intro predCutAddr. simpl.
	(* MAL.writeBlockEndFromBlockEntryAddr *)
	eapply bindRev.
{	eapply weaken. apply writeBlockEndFromBlockEntryAddr.
	intros s Hprops. simpl. destruct Hprops as [Hprops HpredCutAddr]. destruct Hprops as [s0 Hprops]. intuition.
  destruct H11 as [pdentry Hprops]. destruct Hprops as [pdentry0 Hprops]. destruct Hprops as [pdentry1 Hprops].
  destruct Hprops as [bentry Hprops]. destruct Hprops as [bentry0 Hprops]. destruct Hprops as [bentry1 Hprops].
  destruct Hprops as [bentry2 Hprops]. destruct Hprops as [bentry3 Hprops]. destruct Hprops as [bentry4 Hprops].
  destruct Hprops as [bentry5 Hprops]. destruct Hprops as [bentry6 Hprops]. destruct Hprops as [sceaddr Hprops].
  destruct Hprops as [scentry Hprops]. destruct Hprops as [newBlockEntryAddr Hprops].
  destruct Hprops as [newFirstFreeSlotAddr Hprops]. destruct Hprops as [predCurrentNbFreeSlots Hprops].
  destruct Hprops as [Hs Hprops].
  destruct H23 as [bentryShare (Hlookupb & HbentryShare)]. exists bentryShare.
  assert(HblockToShareNotNull: blockToShareInCurrPartAddr <> nullAddr).
  {
    assert(Hnull: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
    intro HcontraEq. rewrite HcontraEq in *. rewrite Hlookupb in *. congruence.
  }
	assert(HnewBlockToShareEq : newBlockEntryAddr <> blockToShareInCurrPartAddr).
	{
		(* at s0, newBlockEntryAddr is a free slot, which is not the case of
				blockToShareInCurrPartAddr *)
		assert(HFirstFreeSlotPointerIsBEAndFreeSlot : FirstFreeSlotPointerIsBEAndFreeSlot s0)
				by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
		assert(HlookupcurrParts0 : lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)) by intuition.
		specialize(HFirstFreeSlotPointerIsBEAndFreeSlot currentPart pdentry HlookupcurrParts0).
    intro HcontraEq.
		assert(HfirstfreeNotNull : firstfreeslot pdentry <> nullAddr).
		{
			assert(HfirstfreecurrParts0 : pdentryFirstFreeSlot currentPart newBlockEntryAddr s0 /\
             beqAddr nullAddr newBlockEntryAddr = false).
      {
        split. intuition. rewrite HcontraEq. rewrite <-beqAddrFalse. apply not_eq_sym. intuition.
      }
			unfold pdentryFirstFreeSlot in *. rewrite HlookupcurrParts0 in *.
			rewrite <- beqAddrFalse in *.
			destruct HfirstfreecurrParts0 as [HfirstfreeEq HfirstFreeNotNull].
			subst newBlockEntryAddr. congruence.
		}
		specialize (HFirstFreeSlotPointerIsBEAndFreeSlot HfirstfreeNotNull).
		assert(HnewBEq : firstfreeslot pdentry = newBlockEntryAddr)
		      by (apply eq_sym; intuition).
		rewrite HnewBEq in *.
		subst blockToShareInCurrPartAddr.
		assert(HwellFormedsh1newBs0 : wellFormedFstShadowIfBlockEntry s0)
			  by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold wellFormedFstShadowIfBlockEntry in *.
		assert(HwellFormedSCnewBs0 : wellFormedShadowCutIfBlockEntry s0)
		    by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		unfold wellFormedShadowCutIfBlockEntry in *.
		assert(HBEs0 : isBE newBlockEntryAddr s0) by intuition.
		specialize (HwellFormedsh1newBs0 newBlockEntryAddr HBEs0).
		specialize (HwellFormedSCnewBs0 newBlockEntryAddr HBEs0).
		unfold isBE in *. unfold isSHE in *. unfold isSCE in *.
		unfold isFreeSlot in *.
		unfold bentryAFlag in *.
		destruct (lookup newBlockEntryAddr (memory s0) beqAddr) eqn:Hbe ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
		destruct (lookup (CPaddr (newBlockEntryAddr + sh1offset)) (memory s0) beqAddr) eqn:Hsh1
            ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
		destruct HwellFormedSCnewBs0 as [scentryaddr (HSCEs0 & HscentryEq)].
		subst scentryaddr.
		destruct (lookup (CPaddr (newBlockEntryAddr + scoffset))  (memory s0) beqAddr) eqn:Hsce
            ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence). rewrite <-H24 in *. intuition.
	}
	assert(HnewFirstFreeBlockToShareEq : newFirstFreeSlotAddr <> blockToShareInCurrPartAddr).
	{
		(* at s0, newFirstFreeSlotAddr is a free slot, which is not the case of
				blockToShareInCurrPartAddr *)
		assert(HFirstFreeSlotPointerIsBEAndFreeSlot : FirstFreeSlotPointerIsBEAndFreeSlot s)
				by (unfold consistency1 in * ; intuition).
		unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
		assert(HlookupcurrParts : lookup currentPart (memory s) beqAddr = Some (PDT pdentry1)) by intuition.
		specialize(HFirstFreeSlotPointerIsBEAndFreeSlot currentPart pdentry1 HlookupcurrParts).
    intro HcontraEq.
		assert(HfirstfreeNotNull : firstfreeslot pdentry1 <> nullAddr).
		{
			assert(HfirstfreecurrParts : pdentryFirstFreeSlot currentPart newFirstFreeSlotAddr s /\
             beqAddr nullAddr newFirstFreeSlotAddr = false).
      {
        split. unfold pdentryFirstFreeSlot. rewrite HlookupcurrParts. intuition. rewrite <-beqAddrFalse.
        rewrite HcontraEq. apply not_eq_sym. assumption.
      }
			unfold pdentryFirstFreeSlot in *. rewrite HlookupcurrParts in *.
			rewrite <- beqAddrFalse in *.
			destruct HfirstfreecurrParts as [HfirstfreeEq HfirstFreeNotNull].
			subst newFirstFreeSlotAddr. congruence.
		}
		specialize (HFirstFreeSlotPointerIsBEAndFreeSlot HfirstfreeNotNull).
		assert(HnewBEq : firstfreeslot pdentry1 = newFirstFreeSlotAddr)
		      by (apply eq_sym; intuition).
		rewrite HnewBEq in *.
		(* newB is a free slot, so its accessible flag is false
				blockToShareInCurrPartAddr is not a free slot,
				so the equality is a constradiction*)
		subst blockToShareInCurrPartAddr.
		assert(HwellFormedsh1newBs : wellFormedFstShadowIfBlockEntry s)
			  by (unfold consistency1 in * ; intuition).
		unfold wellFormedFstShadowIfBlockEntry in *.
		assert(HwellFormedSCnewBs : wellFormedShadowCutIfBlockEntry s)
		    by (unfold consistency1 in * ; intuition).
		unfold wellFormedShadowCutIfBlockEntry in *.
		assert(HBEs : isBE newFirstFreeSlotAddr s) by intuition.
		specialize (HwellFormedsh1newBs newFirstFreeSlotAddr HBEs).
		specialize (HwellFormedSCnewBs newFirstFreeSlotAddr HBEs).
		unfold isBE in *. unfold isSHE in *. unfold isSCE in *.
		unfold isFreeSlot in *.
		unfold bentryAFlag in *.
		destruct (lookup newFirstFreeSlotAddr (memory s) beqAddr) eqn:Hbe ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
		destruct (lookup (CPaddr (newFirstFreeSlotAddr + sh1offset)) (memory s) beqAddr) eqn:Hsh1
              ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
		destruct HwellFormedSCnewBs as [scentryaddr (HSCEs0 & HscentryEq)].
		subst scentryaddr.
		destruct (lookup (CPaddr (newFirstFreeSlotAddr + scoffset))  (memory s) beqAddr) eqn:Hsce
              ; try(exfalso ; congruence).
		destruct v ; try(exfalso ; congruence).
    assert(HlookupnewFirstEq: lookup newFirstFreeSlotAddr (memory s) beqAddr
                              = lookup newFirstFreeSlotAddr (memory s0) beqAddr).
    {
      rewrite Hs. simpl. rewrite InternalLemmas.beqAddrTrue.
      destruct (beqAddr sceaddr newFirstFreeSlotAddr) eqn:HbeqSceaddrNewFirstFree.
      {
        rewrite <-beqAddrTrue in HbeqSceaddrNewFirstFree. rewrite HbeqSceaddrNewFirstFree in *.
        unfold isSCE in *. rewrite Hbe in *. intuition.
      }
      rewrite <-beqAddrFalse in HbeqSceaddrNewFirstFree.
      destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HbeqnewBlockSceaddr.
      {
        rewrite <-beqAddrTrue in HbeqnewBlockSceaddr. rewrite HbeqnewBlockSceaddr in *.
        unfold isSCE in *. intuition.
      }
      rewrite <-beqAddrFalse in HbeqnewBlockSceaddr. simpl.
      destruct (beqAddr newBlockEntryAddr newFirstFreeSlotAddr) eqn:HbeqNewBlockNewFirstFree.
      rewrite <-beqAddrTrue in HbeqNewBlockNewFirstFree. congruence.
      destruct (beqAddr currentPart newBlockEntryAddr) eqn: HbeqCurrPartNewBlock.
      rewrite <-beqAddrTrue in HbeqCurrPartNewBlock. intuition.
      simpl. repeat rewrite removeDupIdentity; intuition. rewrite HbeqCurrPartNewBlock. simpl.
      destruct (beqAddr currentPart newFirstFreeSlotAddr) eqn:HbeqCurrPartNewFirstFree.
      rewrite <-beqAddrTrue in HbeqCurrPartNewFirstFree. intuition.
      rewrite InternalLemmas.beqAddrTrue. repeat rewrite removeDupIdentity; intuition.
    }
    rewrite <-HlookupnewFirstEq in H24. rewrite Hbe in H24. rewrite <-H24 in *. intuition.
	}
  assert(HblockToShareCurrPartEq: blockToShareInCurrPartAddr <> currentPart).
  {
    intro HbeqBlockToShareCurrPart. rewrite HbeqBlockToShareCurrPart in *. unfold isPDT in *.
    rewrite Hlookupb in *. congruence.
  }
  assert(blockToShareInCurrPartAddr <> sceaddr).
  {
    intro HcontraEq. rewrite HcontraEq in *. unfold isSCE in *. rewrite Hlookupb in *. intuition.
  }
  split.
  - rewrite Hs. simpl. rewrite InternalLemmas.beqAddrTrue.
    (* check all possible equalities *)
    destruct (beqAddr sceaddr blockToShareInCurrPartAddr) eqn:HbeqSceBlock.
    { rewrite <-beqAddrTrue in HbeqSceBlock. intuition. }
    destruct Hprops as [HnewBlockIdEq (HlookupNew0 & Hprops)].
    destruct (beqAddr newBlockEntryAddr sceaddr) eqn:HbeqnewBlockSce.
    { rewrite <-beqAddrTrue in HbeqnewBlockSce. intuition. }
    rewrite <-beqAddrFalse in HbeqnewBlockSce. simpl.
    destruct (beqAddr newBlockEntryAddr blockToShareInCurrPartAddr) eqn:HbeqNewBlockToShare.
    + rewrite <-beqAddrTrue in HbeqNewBlockToShare. congruence.
    + rewrite <-beqAddrFalse in HbeqNewBlockToShare.
      repeat rewrite removeDupIdentity; intuition.
      destruct (beqAddr currentPart newBlockEntryAddr) eqn:HbeqCurrNewBlock.
      {
        rewrite <-beqAddrTrue in HbeqCurrNewBlock. rewrite HbeqCurrNewBlock in *. unfold isPDT in *.
        rewrite HlookupNew0 in *. congruence.
      }
      rewrite <-beqAddrFalse in HbeqCurrNewBlock. simpl.
      destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrBlockToShare.
      {
        rewrite <-beqAddrTrue in HbeqCurrBlockToShare. rewrite HbeqCurrBlockToShare in *. unfold isPDT in *.
        rewrite Hlookupb in *. congruence.
      }
      rewrite <-beqAddrFalse in HbeqCurrBlockToShare. rewrite InternalLemmas.beqAddrTrue.
      repeat rewrite removeDupIdentity; intuition.
  - instantiate(1:= fun _ s => isBE idNewSubblock s
        /\ StateLib.Paddr.pred cutAddr = Some predCutAddr
        /\ zero = CIndex 0
        /\ false = StateLib.Index.leb nbFreeSlots zero
        /\ beqAddr nullAddr PDChildAddr = true
        /\ false = StateLib.Paddr.leb cutAddr blockToCutStartAddr
        /\ false = StateLib.Paddr.leb blockToCutEndAddr cutAddr
        /\ StateLib.Paddr.subPaddr cutAddr blockToCutStartAddr = Some subblock1Size
        /\ StateLib.Paddr.subPaddr blockToCutEndAddr cutAddr = Some subblock2Size
        /\ minBlockSize = Constants.minBlockSize
        /\ isBlock1TooSmall = StateLib.Index.ltb subblock1Size minBlockSize
        /\ isBlock2TooSmall = StateLib.Index.ltb subblock2Size minBlockSize
        /\ isCutAddrValid = is32Aligned cutAddr
        /\ exists s0 s1, exists pdentry pdentryInter0 pdentryInter1 newpdentry: PDTable,
           exists bentry bentry0 bentry1 bentry2 bentry3 bentry4 bentry5 bentry6 bentryShare bentry7: BlockEntry,
           exists scentry: SCEntry, exists predCurrentNbFreeSlots: index,
           exists sceaddr newFirstFreeSlotAddr: paddr,
           s =
           {|
             currentPartition := currentPartition s0;
             memory :=
               add blockToShareInCurrPartAddr
               (BE
                  (CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                    (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                    (CBlock (startAddr (blockrange bentryShare)) predCutAddr)))
                      (memory s1) beqAddr
           |}
           /\ lookup idNewSubblock (memory s0) beqAddr = Some (BE bentry)
           /\ lookup idNewSubblock (memory s) beqAddr = Some (BE bentry6)
           /\ lookup blockToShareInCurrPartAddr (memory s0) beqAddr = Some (BE bentryShare)
           /\ lookup blockToShareInCurrPartAddr (memory s) beqAddr = Some (BE bentry7)
           /\ bentry7 = CBlockEntry (read bentryShare) (write bentryShare) (exec bentryShare)
                        (present bentryShare) (accessible bentryShare) (blockindex bentryShare)
                        (CBlock (startAddr (blockrange bentryShare)) predCutAddr)
           /\ bentry6 = CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                        (accessible bentry5) (blockindex bentry5) (blockrange bentry5)
           /\ bentry5 = CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                        (accessible bentry4) (blockindex bentry4) (blockrange bentry4)
           /\ bentry4 = CBlockEntry blockR (write bentry3) (exec bentry3) (present bentry3)
                        (accessible bentry3) (blockindex bentry3) (blockrange bentry3)
           /\ bentry3 = CBlockEntry (read bentry2) (write bentry2) (exec bentry2) (present bentry2) true
                        (blockindex bentry2) (blockrange bentry2)
           /\ bentry2 = CBlockEntry (read bentry1) (write bentry1) (exec bentry1) true (accessible bentry1)
                        (blockindex bentry1) (blockrange bentry1)
           /\ bentry1 = CBlockEntry (read bentry0) (write bentry0) (exec bentry0) (present bentry0)
                        (accessible bentry0) (blockindex bentry0)
                        (CBlock (startAddr (blockrange bentry0)) blockEndAddr)
           /\ bentry0 = CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) 
                        (accessible bentry) (blockindex bentry) (CBlock cutAddr (endAddr (blockrange bentry)))
           /\ sceaddr = CPaddr ((firstfreeslot pdentry) + scoffset)
           /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentry)
           /\ lookup currentPart (memory s) beqAddr = Some (PDT newpdentry)
           /\ newpdentry = pdentryInter1
           /\ pdentryInter1 =
              {|
                structure := structure pdentryInter0;
                firstfreeslot := firstfreeslot pdentryInter0;
                nbfreeslots := predCurrentNbFreeSlots;
                nbprepare := nbprepare pdentryInter0;
                parent := parent pdentryInter0;
                MPU := MPU pdentryInter0;
                vidtAddr := vidtAddr pdentryInter0
              |}
           /\ pdentryInter0 =
              {|
                structure := structure pdentry;
                firstfreeslot := newFirstFreeSlotAddr;
                nbfreeslots := nbfreeslots pdentry;
                nbprepare := nbprepare pdentry;
                parent := parent pdentry;
                MPU := MPU pdentry;
                vidtAddr := vidtAddr pdentry
              |}
           /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ consistency s0 /\ currentPart = currentPartition s0
           /\ isPDT currentPart s0
           /\ consistency1 s1 /\ isPDT currentPart s
           /\ pdentryNbFreeSlots currentPart nbFreeSlots s0
           /\ bentryXFlag blockToShareInCurrPartAddr blockX s0
           /\ bentryWFlag blockToShareInCurrPartAddr blockW s0
           /\ bentryRFlag blockToShareInCurrPartAddr blockR s0
           /\ (exists (scentry : SCEntry) (scentryaddr : paddr),
                lookup scentryaddr (memory s0) beqAddr = Some (SCE scentry) /\
                scentryOrigin scentryaddr blockOrigin s0)
           /\ bentryEndAddr blockToShareInCurrPartAddr blockEndAddr s0
           /\ bentryAFlag blockToShareInCurrPartAddr true s0
           /\ (exists (sh1entry : Sh1Entry) (sh1entryaddr : paddr),
                lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry) /\
                sh1entryPDchild sh1entryaddr PDChildAddr s0 /\
                sh1entryAddr blockToShareInCurrPartAddr sh1entryaddr s0)
           /\ beqAddr nullAddr PDChildAddr = true
           /\ bentryStartAddr blockToShareInCurrPartAddr blockToCutStartAddr s0
           /\ bentryEndAddr blockToShareInCurrPartAddr blockToCutEndAddr s0
           /\ bentryPFlag blockToShareInCurrPartAddr true s0
           /\ In blockToShareInCurrPartAddr (getMappedBlocks currentPart s0)
           /\ pdentryFirstFreeSlot currentPart (firstfreeslot pdentry) s0
           /\ bentryEndAddr (firstfreeslot pdentry) newFirstFreeSlotAddr s0
           /\ pdentryNbFreeSlots currentPart predCurrentNbFreeSlots s
           /\ StateLib.Index.pred nbFreeSlots = Some predCurrentNbFreeSlots
           /\ blockindex bentry6 = blockindex bentry5
           /\ blockindex bentry5 = blockindex bentry4
           /\ blockindex bentry4 = blockindex bentry3
           /\ blockindex bentry3 = blockindex bentry2
           /\ blockindex bentry2 = blockindex bentry1
           /\ blockindex bentry1 = blockindex bentry0
           /\ blockindex bentry0 = blockindex bentry
           /\ isBE (firstfreeslot pdentry) s0
           /\ isBE (firstfreeslot pdentry) s
           /\ isSCE sceaddr s0
           /\ isSCE sceaddr s
           /\ firstfreeslot newpdentry = newFirstFreeSlotAddr
           /\ (newFirstFreeSlotAddr = currentPart -> False)
           /\ (currentPart = (firstfreeslot pdentry) -> False)
           /\ (newFirstFreeSlotAddr = (firstfreeslot pdentry) -> False)
           /\ (sceaddr = (firstfreeslot pdentry) -> False)
           /\ (sceaddr = currentPart -> False)
           /\ (sceaddr = newFirstFreeSlotAddr -> False)
           /\ ((firstfreeslot pdentry) = blockToShareInCurrPartAddr -> False)
           /\ (blockToShareInCurrPartAddr = currentPart -> False)
           (* intermediate steps *)
           /\ s1 =
              {|
                currentPartition := currentPartition s0;
                memory :=
                    add sceaddr (SCE {| origin := blockOrigin; next := next scentry |})
                       (add idNewSubblock
                          (BE
                             (CBlockEntry (read bentry5) (write bentry5) blockX (present bentry5)
                                (accessible bentry5) (blockindex bentry5) (blockrange bentry5)))
                          (add idNewSubblock
                             (BE
                                (CBlockEntry (read bentry4) blockW (exec bentry4) (present bentry4)
                                   (accessible bentry4) (blockindex bentry4) (blockrange bentry4)))
                             (add idNewSubblock
                                (BE
                                   (CBlockEntry blockR (write bentry3) (exec bentry3) 
                                      (present bentry3) (accessible bentry3) (blockindex bentry3)
                                      (blockrange bentry3)))
                                (add idNewSubblock
                                   (BE
                                      (CBlockEntry (read bentry2) (write bentry2) (exec bentry2)
                                         (present bentry2) true (blockindex bentry2) 
                                         (blockrange bentry2)))
                                   (add idNewSubblock
                                      (BE
                                         (CBlockEntry (read bentry1) (write bentry1) 
                                            (exec bentry1) true (accessible bentry1) 
                                            (blockindex bentry1) (blockrange bentry1)))
                                      (add idNewSubblock
                                         (BE
                                            (CBlockEntry (read bentry0) (write bentry0) 
                                               (exec bentry0) (present bentry0) (accessible bentry0)
                                               (blockindex bentry0)
                                               (CBlock (startAddr (blockrange bentry0)) blockEndAddr)))
                                         (add idNewSubblock
                                            (BE
                                               (CBlockEntry (read bentry) (write bentry) 
                                                  (exec bentry) (present bentry) (accessible bentry)
                                                  (blockindex bentry)
                                                  (CBlock cutAddr (endAddr (blockrange bentry)))))
                                            (add currentPart
                                               (PDT
                                                  {|
                                                    structure := structure pdentryInter0;
                                                    firstfreeslot := firstfreeslot pdentryInter0;
                                                    nbfreeslots := predCurrentNbFreeSlots;
                                                    nbprepare := nbprepare pdentryInter0;
                                                    parent := parent pdentryInter0;
                                                    MPU := MPU pdentryInter0;
                                                    vidtAddr := vidtAddr pdentryInter0
                                                  |})
                                               (add currentPart
                                                  (PDT
                                                     {|
                                                       structure := structure pdentry;
                                                       firstfreeslot := newFirstFreeSlotAddr;
                                                       nbfreeslots := nbfreeslots pdentry;
                                                       nbprepare := nbprepare pdentry;
                                                       parent := parent pdentry;
                                                       MPU := MPU pdentry;
                                                       vidtAddr := vidtAddr pdentry
                                                     |}) (memory s0) beqAddr) beqAddr) beqAddr) beqAddr) beqAddr)
                             beqAddr) beqAddr) beqAddr) beqAddr) beqAddr
              |}
           /\ exists (optionfreeslotslist : list optionPaddr) (s2 : state) (n0 n1 n2 : nat) (nbleft : index),
                nbleft = CIndex (nbFreeSlots - 1) /\ nbleft < maxIdx
                /\ s1 =
                  {|
                    currentPartition := currentPartition s0;
                    memory :=
                      add sceaddr (SCE {| origin := blockOrigin; next := next scentry |}) 
                        (memory s2) beqAddr
                  |}
                /\ optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft
                (*/\ getFreeSlotsListRec n2 newFirstFreeSlotAddr s nbleft = optionfreeslotslist*)
                /\ getFreeSlotsListRec n2 newFirstFreeSlotAddr s1 nbleft = optionfreeslotslist
                /\ optionfreeslotslist = getFreeSlotsListRec n0 newFirstFreeSlotAddr s0 nbleft
                /\ n0 <= n1 /\ nbleft < n0 /\ n1 <= n2 /\ nbleft < n2 /\ n2 <= maxIdx + 1
                /\ (wellFormedFreeSlotsList optionfreeslotslist = False -> False)
                /\ NoDup (filterOptionPaddr optionfreeslotslist)
                /\ (In (firstfreeslot pdentry) (filterOptionPaddr optionfreeslotslist) -> False)
                /\ (exists optionentrieslist : list optionPaddr,
                      optionentrieslist = getKSEntries currentPart s2 /\
                      getKSEntries currentPart s = optionentrieslist /\
                      optionentrieslist = getKSEntries currentPart s0 /\
                      In (firstfreeslot pdentry) (filterOptionPaddr optionentrieslist))
                /\ isPDT multiplexer s
                /\ getPartitions multiplexer s2 = getPartitions multiplexer s0
                /\ getPartitions multiplexer s1 = getPartitions multiplexer s2
                /\ getChildren currentPart s2 = getChildren currentPart s0
                /\ getChildren currentPart s1 = getChildren currentPart s2
                /\ getConfigBlocks currentPart s2 = getConfigBlocks currentPart s0
                /\ getConfigBlocks currentPart s1 = getConfigBlocks currentPart s2
                /\ getConfigPaddr currentPart s2 = getConfigPaddr currentPart s0
                /\ getConfigPaddr currentPart s1 = getConfigPaddr currentPart s2
                /\ (forall block : paddr,
                    In block (getMappedBlocks currentPart s) <->
                    (firstfreeslot pdentry) = block \/ In block (getMappedBlocks currentPart s0))
                /\ ((forall addr : paddr,
                     In addr (getMappedPaddr currentPart s) <->
                     In addr
                       (getAllPaddrBlock (startAddr (blockrange bentry6))
                          (endAddr (blockrange bentry6)) ++ getMappedPaddr currentPart s0)) /\
                    length (getMappedPaddr currentPart s) =
                    length
                      (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6)) ++
                       getMappedPaddr currentPart s0))
                /\ (forall block : paddr,
                    In block (getAccessibleMappedBlocks currentPart s) <->
                    (firstfreeslot pdentry) = block \/ In block (getAccessibleMappedBlocks currentPart s0))
                /\ (forall addr : paddr,
                    In addr (getAccessibleMappedPaddr currentPart s) <->
                    In addr
                      (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6)) ++
                       getAccessibleMappedPaddr currentPart s0))
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getKSEntries partition s = getKSEntries partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getMappedPaddr partition s = getMappedPaddr partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getConfigPaddr partition s = getConfigPaddr partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getPartitions partition s = getPartitions partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getChildren partition s = getChildren partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 -> getMappedBlocks partition s = getMappedBlocks partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 ->
                    getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0)
                /\ (forall partition : paddr,
                    (partition = currentPart -> False) ->
                    isPDT partition s0 ->
                    getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)
                /\ (forall partition : paddr, isPDT partition s = isPDT partition s0)
          ).
    simpl. intuition; subst newBlockEntryAddr.
    + (* isBE idNewSubblock news *)
      unfold isBE in *. simpl.
      destruct (beqAddr blockToShareInCurrPartAddr idNewSubblock) eqn:HbeqBlockToShareIdNew. trivial.
      rewrite <-beqAddrFalse in HbeqBlockToShareIdNew.
      rewrite removeDupIdentity; intuition.
    + (* exists (s1 s2 : state) ... *)
      exists s0. exists s. exists pdentry. exists pdentry0. exists pdentry1. eexists. exists bentry.
      exists bentry0. exists bentry1. exists bentry2. exists bentry3. exists bentry4. exists bentry5.
      exists bentry6. exists bentryShare. eexists. exists scentry. exists predCurrentNbFreeSlots. exists sceaddr.
      exists newFirstFreeSlotAddr. intuition.
      * assert(HcurrPartEq: currentPartition s = currentPartition s0) by (subst s; simpl; reflexivity).
        rewrite HcurrPartEq. reflexivity.
      * destruct (beqAddr blockToShareInCurrPartAddr idNewSubblock) eqn:HbeqBlockToShareIdNew.
        -- rewrite <-beqAddrTrue in HbeqBlockToShareIdNew. congruence.
        -- rewrite removeDupIdentity; intuition.
      * (* lookup blockToShareInCurrPartAddr *)
        rewrite InternalLemmas.beqAddrTrue. reflexivity.
      * (* sceaddr = CPaddr (firstfreeslot pdentry + scoffset) *)
        subst idNewSubblock. intuition.
      * (* lookup currentPart *)
        destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockToShareCurrPart.
        -- rewrite <-beqAddrTrue in HbeqBlockToShareCurrPart. congruence.
        -- rewrite <-beqAddrFalse in HbeqBlockToShareCurrPart. rewrite removeDupIdentity; intuition.
      * (* isPDT currentPart *)
        unfold isPDT in *. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockToShareCurrPart.
        rewrite <-beqAddrTrue in HbeqBlockToShareCurrPart. congruence.
        rewrite <-beqAddrFalse in HbeqBlockToShareCurrPart. rewrite removeDupIdentity; intuition.
      * (* pdentryFirstFreeSlot currentPart (firstfreeslot pdentry) s0 *)
        subst idNewSubblock. intuition.
      * (* bentryEndAddr (firstfreeslot pdentry) newFirstFreeSlotAddr s0 *)
        subst idNewSubblock. intuition.
      * (* pdentryNbFreeSlots currentPart *)
        unfold pdentryNbFreeSlots in *. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr currentPart) eqn:HbeqBlockToShareCurrPart.
        rewrite <-beqAddrTrue in HbeqBlockToShareCurrPart. congruence.
        rewrite <-beqAddrFalse in HbeqBlockToShareCurrPart. rewrite removeDupIdentity; intuition.
      * (* isBE (firstfreeslot pdentry) s0 *)
        subst idNewSubblock. intuition.
      * (* isBE (firstfreeslot pdentry) news *)
        unfold isBE in *. simpl. subst idNewSubblock.
        destruct (beqAddr blockToShareInCurrPartAddr (firstfreeslot pdentry)) eqn:HbeqBlockToShareIdNew.
        rewrite <-beqAddrTrue in HbeqBlockToShareIdNew. congruence.
        rewrite <-beqAddrFalse in HbeqBlockToShareIdNew. rewrite removeDupIdentity; intuition.
      * (* isSCE sceaddr news *)
        unfold isSCE in *. simpl.
        destruct (beqAddr blockToShareInCurrPartAddr sceaddr) eqn:HbeqBlockToShareSceaddr.
        -- rewrite <-beqAddrTrue in HbeqBlockToShareSceaddr. rewrite HbeqBlockToShareSceaddr in *.
           rewrite Hlookupb in *. congruence.
        -- rewrite <-beqAddrFalse in HbeqBlockToShareSceaddr. rewrite removeDupIdentity; intuition.
      * subst idNewSubblock. congruence.
      * subst idNewSubblock. congruence.
      * subst idNewSubblock. congruence.
      * subst idNewSubblock. congruence.
      * (* exists (optionfreeslotslist : list optionPaddr) (s2 : state) ... *)
        destruct H80 as [optionfreeslotslist HoptionProps]. exists optionfreeslotslist.
        destruct HoptionProps as [s2' HoptionProps]. exists s2'.
        destruct HoptionProps as [n0 HoptionProps]. exists n0.
        destruct HoptionProps as [n1 HoptionProps]. exists n1.
        destruct HoptionProps as [n2 HoptionProps]. exists n2.
        destruct HoptionProps as [nbleft HoptionProps]. exists nbleft.
        assert(HBEBlockToShare0: isBE blockToShareInCurrPartAddr s0)
            by (unfold isBE; rewrite Hlookupb; intuition).
        assert(HBEBlockToShare: isBE blockToShareInCurrPartAddr s).
        {
          unfold isBE in *. rewrite Hs. simpl. rewrite InternalLemmas.beqAddrTrue.
          destruct (beqAddr sceaddr blockToShareInCurrPartAddr) eqn:HbeqSceaddrBlockToShare.
          { rewrite <-beqAddrTrue in HbeqSceaddrBlockToShare. intuition. }
          destruct (beqAddr idNewSubblock sceaddr) eqn:HbeqIdNewSceaddr.
          { rewrite <-beqAddrTrue in HbeqIdNewSceaddr. intuition. }
          simpl. destruct (beqAddr idNewSubblock blockToShareInCurrPartAddr) eqn:HbeqIdNewBlockToShare.
          { rewrite <-beqAddrTrue in HbeqIdNewBlockToShare. intuition. }
          destruct (beqAddr currentPart idNewSubblock) eqn:HbeqCurrPartIdNew.
          { rewrite <-beqAddrTrue in HbeqCurrPartIdNew. intuition. }
          repeat rewrite removeDupIdentity; intuition. simpl.
          destruct (beqAddr currentPart blockToShareInCurrPartAddr) eqn:HbeqCurrPartBlockToShare.
          { rewrite <-beqAddrTrue in HbeqCurrPartBlockToShare. intuition. }
          rewrite InternalLemmas.beqAddrTrue. repeat rewrite removeDupIdentity; intuition.
        }
        destruct H82 as [s1 HinterStates]. destruct HinterStates as [s2 HinterStates].
        destruct HinterStates as [s3 HinterStates]. destruct HinterStates as [s4 HinterStates].
        destruct HinterStates as [s5 HinterStates]. destruct HinterStates as [s6 HinterStates].
        destruct HinterStates as [s7 HinterStates]. destruct HinterStates as [s8 HinterStates].
        destruct HinterStates as [s9 HinterStates]. destruct HinterStates as [s10 HinterStates].
        destruct HinterStates as [Hs1 (Hs2 & (Hs3 & (Hs4 & (Hs5 & (Hs6 & (Hs7 & (Hs8 & (Hs9 & Hs10))))))))].
        assert(Hs10sEq: s10 = s).
        {
          subst s10. subst s9. subst s8. subst s7. subst s6. subst s5. subst s4. subst s3. subst s2. subst s1.
          simpl. rewrite Hs. f_equal.
        }
        rewrite Hs10sEq in *. subst idNewSubblock.
        set(s':= {|
                   currentPartition := currentPartition s;
                   memory := _
                 |}).
        intuition.
        -- destruct H104 as [optionentrieslist Hoptionentrieslist]. exists optionentrieslist. intuition.
           subst optionentrieslist. rewrite <-H117.
           apply getKSEntriesEqBE; intuition.
        -- apply isPDTMultiplexerEqBE; intuition.
        -- specialize(H102 block). apply H102. unfold getMappedBlocks in *.
           assert(HgetKSEq: getKSEntries currentPart s' = getKSEntries currentPart s)
                by (apply getKSEntriesEqBE; intuition).
           rewrite HgetKSEq in *.
           assert(HlookupBlock: exists blockBentry, lookup block (memory s') beqAddr = Some(BE blockBentry)
                                                    /\ present blockBentry = true).
           { apply filterPresentIsPresent; intuition. }
        -- 
        -- 
        -- 
        -- 

}
  intro.
  eapply bindRev.
{ eapply weaken. eapply getKernelStructureEntriesNb.
  intros. simpl. admit.
}
  intro kernelentriesnb.
  eapply bindRev.
{ eapply weaken. eapply Invariants.Index.succ. simpl. intros s Hprops. split.
    * eapply Hprops.
    * assert (HleqIdx: CIndex (kernelentriesnb + 1) <= maxIdx) by apply IdxLtMaxIdx.
      unfold CIndex in HleqIdx.
      destruct (Compare_dec.le_dec (kernelentriesnb + 1) maxIdx).
      -- exact l.
      -- destruct Hprops as [Hprops Hkern]. subst kernelentriesnb.
         unfold CIndex in *.
         assert(kernelStructureEntriesNb < maxIdx-1) by apply KSEntriesNbLessThanMaxIdx.
         destruct (Compare_dec.le_dec kernelStructureEntriesNb maxIdx) ; simpl in * ; try lia.
         assert (HBigEnough: maxIdx > kernelStructureEntriesNb) by apply maxIdxBiggerThanNbOfKernels.
         apply Gt.gt_le_S. apply HBigEnough.
}
  intro defaultidx. eapply bindRev.
{ (** MAL.findBlockIdxInPhysicalMPU **)
  eapply weaken. admit. (*eapply findBlockIdxInPhysicalMPU.*)
  intros s Hprops. eapply Hprops. (*?*)
}
  intro blockMPURegionNb. eapply bindRev.
{ (** Internal.enableBlockInMPU **)
  eapply weaken. admit.
  intros s Hprops. eapply Hprops. (*?*)
}
  intro blockToShareEnabled. eapply bindRev.
{ (** readSCNextFromBlockEntryAddr **)
  eapply weaken. eapply readSCNextFromBlockEntryAddr.
  intros s Hprops. simpl. split.
  eapply Hprops. (*?*)
  admit. (* intuition *)
}
  intro originalNextSubblock. eapply bindRev.
{ (** writeSCNextFromBlockEntryAddr **)
  eapply weaken. admit. admit.
}
  intro. eapply bindRev.
{ (** writeSCNextFromBlockEntryAddr **)
  eapply weaken. admit. admit.
}
  intro. eapply bindRev.
{ (** Internal.enableBlockInMPU **)
  eapply weaken. admit.
  intros s Hprops. eapply Hprops. (*?*)
}
  intro newSubEnabled. eapply weaken.
  admit. admit.
Admitted.

(*(** compareVAddrToNull **) 
eapply WP.bindRev.
eapply Invariants.compareVAddrToNull.
intro vaInCurrentPartitionIsnull. simpl.
case_eq vaInCurrentPartitionIsnull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret .
  simpl. intros.
  intuition. }
intros HvaInCurrentPartition. 
subst.
  (** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.compareVAddrToNull.
intro descChildIsnull. simpl.
case_eq descChildIsnull.
{ intros.
  eapply WP.weaken.
  eapply WP.ret .
  simpl. intros.
  intuition. }
intros HdescChildIsnull. 
subst.  
(** checkKernelMap *)
eapply WP.bindRev.
eapply WP.weaken.   
eapply Invariants.checkKernelMap.
intros. simpl. pattern s in H. eexact H. 
intro.
repeat (eapply WP.bindRev; [ eapply WP.weaken ; 
              [ apply Invariants.checkKernelMap | intros; simpl; pattern s in H; eexact H ]
                                | simpl; intro ]).
                                simpl.
case_eq (negb a && negb a0 );[|intros;eapply weaken;[ eapply WP.ret;trivial|
  intros;simpl;intuition]].
intro Hkmap.
repeat rewrite andb_true_iff in Hkmap.
try repeat rewrite and_assoc in Hkmap.
repeat rewrite negb_true_iff in Hkmap. 
intuition.
subst.*)
(** checkRights **)

eapply WP.bindRev.
{
eapply weaken.
eapply Invariants.checkRights.
simpl.
intros.
split.
apply H0.
intuition.
destruct H3 ; destruct H3. exists x. apply H3.
}


(*destruct H1.
simpl in *.
 eexact H.
intros right.
case_eq right; intros Hright;[|intros;eapply weaken;[ eapply WP.ret;trivial|
  intros;simpl;intuition]].
subst.
(** getCurPartition **)
eapply WP.bindRev.
eapply WP.weaken. 
eapply Invariants.getCurPartition .
cbn. 
intros. 
pattern s in H. 
eexact H.
intro currentPart.
(** getNbLevel **)
eapply WP.bindRev.
eapply weaken.
eapply Invariants.getNbLevel.
simpl. intros.
pattern s in H.
eexact H.
intros level.
simpl.*)
intro rcheck.
destruct rcheck.
2 : {
simpl.
eapply weaken. eapply WP.ret;trivial. intuition.
}

simpl in *.
(** checkChildOfCurrPart **)
eapply WP.bindRev.
{ eapply weaken.
 	apply checkChildOfCurrPart.checkChildOfCurrPart.
	intros. simpl. split. apply H0. apply H0. (* destruct H0 as (HP & HcurrPart). destruct HP as (Hblock & HH).
	destruct Hblock as (HA & Hbeq). destruct HA as (HQ&Hc).
	apply HQ.*)
	(*split. apply HQ. split. unfold consistency in HQ. intuition.
 intuition.*)
}

intro isChildCurrPart. simpl.
destruct isChildCurrPart.
2 : { simpl. eapply weaken. apply WP.ret. intros. simpl. apply H0. }
(** readBlockStartFromBlockEntryAddr*)
eapply WP.bindRev.
{
	eapply weaken.
-	apply Invariants.readBlockStartFromBlockEntryAddr.
-	intros. simpl. split. apply H0.
	unfold isBE. destruct H0. destruct H1. destruct H2. destruct H2. destruct H3.
	destruct H3.
	rewrite -> H3. trivial.
	(*unfold checkChild in H2.
	Search (true = _).
	apply Is_true_eq_right in H2. unfold Is_true in H2.
	
	assert(H'' := 

destruct H2. destruct H3. destruct H3.  rewrite -> H3. trivial.*)
}

intro globalIdPDChild. simpl.




unfold entryStartAddr in *. unfold entryPDT in *. rewrite -> H14 in H16.
rewrite H14 in H2. rewrite <- H2 in H16.
destruct (lookup globalIdPDChild (memory s) beqAddr) eqn:Hlookup.
	destruct v eqn:Hv. repeat trivial. trivial. repeat trivial. trivial.
	trivial. trivial.
}



(* Start of structure modifications *)
	
eapply weaken.

(* 1) traiter les instructions de modifications en paquet *)


	intro blockToShareChildEntryAddr.




 now exists a.  }
  rewrite assoc.
  eapply bindRev.
  (** getFstShadow **)
  eapply WP.weaken. 
  eapply Invariants.getFstShadow. cbn.
  intros s H.
  split.
  pattern s in H.
  eexact H.
  unfold consistency in *.
  unfold partitionDescriptorEntry in *.
  intuition.
  simpl.
  intros currentShadow1.
  rewrite assoc.
  (** StateLib.getIndexOfAddr **)                
  eapply WP.bindRev.
  eapply WP.weaken.
  eapply Invariants.getIndexOfAddr.
  { simpl. intros.
    pattern s in H.
    eexact H.  }
  intro idxDescChild. simpl.
  rewrite assoc.
  (** getTableAddr **)
  eapply WP.bindRev.
  eapply WP.weaken. 
  apply getTableAddr.
  simpl.
  intros s H.
  split.
  pattern s in H. 
  eexact H. subst.
  split. 
  intuition.
  split. 
  instantiate (1:= currentPart).
  intuition. 
  subst.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *. 
  intuition.
  instantiate (1:= sh1idx).
  split. intuition.
  assert(Hcons : consistency s) by intuition.
  assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
  assert(Hcp : currentPart = currentPartition s) by intuition.
  assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow1 s) by intuition.
  exists currentShadow1.
  split. intuition.
  
  unfold consistency in *.
  destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
  unfold partitionDescriptorEntry in Hpd.
  assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
  \/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
  by auto.
      generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
  generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
  destruct Hpd as (Hidxpd & _& Hentry). 
  destruct Hentry as (page1 & Hpd & Hnotnull).
  subst.
  split.
  unfold nextEntryIsPP in *.
  destruct (StateLib.Index.succ sh1idx); try now contradict H0.
  destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex);
  try now contradict H0.
  destruct v ; try now contradict H0.
  subst; assumption.
  subst. left. split;intuition.
  intro ptDescChild. simpl.
  (** simplify the new precondition **)     
  eapply WP.weaken.
  intros.
  2: {
  intros.
  destruct H as (H0 & H1).
  assert ( (getTableAddrRoot' ptDescChild sh1idx currentPart descChild s /\ ptDescChild = defaultPage) \/
  (forall idx : index,
  StateLib.getIndexOfAddr descChild fstLevel = idx ->
  isVE ptDescChild idx s /\ getTableAddrRoot ptDescChild sh1idx currentPart descChild s  )).
  { destruct H1 as [H1 |(Hi & Hi1 & H1)].
    + left. trivial. 
    + right. intros idx Hidx.
      generalize (H1 idx Hidx);clear H1;intros H1.
      destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
      - split; assumption.
      - contradict Hfalse. 
        symmetrynot. 
        apply idxSh2idxSh1notEq.
      - contradict Hfalse. 
        symmetrynot. apply idxPDidxSh1notEq.  }
  assert (HP := conj H0 H).
  pattern s in HP.
  eapply HP. }
  rewrite assoc.
  (** comparePageToNull **) 
  eapply WP.bindRev.
  eapply Invariants.comparePageToNull.
  intro ptDescChildIsnull. simpl.
  case_eq ptDescChildIsnull.
  { intros.
    eapply WP.weaken.
    eapply WP.ret .
    simpl. intros.
    intuition. }
  intros HptDescChildIsnull. 
  subst.
  (* readPDflag *)
  eapply bindRev.
  eapply weaken.
  eapply Invariants.readPDflag.
  simpl;intros.
  split.
  destruct H as (((Ha1 & Ha2) & Ha3) & Ha4).
  assert (Hnewget : isVE ptDescChild (StateLib.getIndexOfAddr descChild fstLevel) s /\
       getTableAddrRoot ptDescChild sh1idx currentPart descChild s /\ 
       (Nat.eqb defaultPage ptDescChild) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr descChild fstLevel);trivial.
      intuition. }
  assert (HP := conj (conj Ha1 Ha2) Hnewget).
  pattern s in HP.
  eexact HP.
  destruct H as (H & Htrue).
  destruct H as (H & Hor).
  destruct Hor as [(Hor & Hfalse) | Hor].
  subst.
  apply beq_nat_false in Htrue.
  now contradict Htrue.
  destruct H as (H & Hidx).
  subst.
  destruct Hor with (StateLib.getIndexOfAddr descChild fstLevel);
  trivial.
  intros ischild;simpl in *.
  intros.
  case_eq ischild; intros Hischild;[|intros;eapply weaken;[ eapply WP.ret;trivial|
  intros;simpl;intuition]].
  subst.
(** end checkChild *)
(** getFstShadow **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getFstShadow. cbn.
intros s H.
split.
pattern s in H.
eexact H.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
intros currentShadow.
(** getTableAddr **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
assert(Hsh1eq : currentShadow = currentShadow1).
apply getSh1NextEntryIsPPEq with currentPart s;trivial.
intuition.
apply nextEntryIsPPgetFstShadow;intuition.
subst currentShadow1.
destruct H as (H & _).
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= sh1idx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart sh1idx currentShadow s) by intuition.
exists currentShadow.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (sh1idx = PDidx \/ sh1idx = sh1idx \/ sh1idx = sh2idx \/  sh1idx  = sh3idx
\/  sh1idx  = PPRidx \/  sh1idx = PRidx) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd sh1idx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *.
destruct (StateLib.Index.succ sh1idx); try now contradict H0.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex);
try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaInCurPart. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaInCurPart sh1idx currentPart vaInCurrentPartition s
      /\ ptVaInCurPart = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isVE ptVaInCurPart idx s /\ getTableAddrRoot ptVaInCurPart sh1idx currentPart vaInCurrentPartition s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (_& Hfalse) | (_&Hfalse) ]].
    - split; assumption.
    - contradict Hfalse. 
      symmetrynot. 
      apply idxSh2idxSh1notEq.
    - contradict Hfalse. 
      symmetrynot. apply idxPDidxSh1notEq.  }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro childListSh1Isnull. simpl.
case_eq childListSh1Isnull.
{ intros. eapply WP.weaken.  eapply WP.ret . simpl. intros.
 pattern false, s in H0.
 eapply H0. }
intros HptVaInCurPartNotNull. clear HptVaInCurPartNotNull.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
    destruct H as ((Ha1  & Ha3) & Ha4).
  assert (Hnewget : isVE ptVaInCurPart (
  StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) s /\
       getTableAddrRoot ptVaInCurPart sh1idx currentPart vaInCurrentPartition s /\ 
       (Nat.eqb defaultPage ptVaInCurPart) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP.  }
intro idxvaInCurPart.
simpl. 
(** checkDerivation **)
unfold Internal.checkDerivation.
rewrite assoc.
(** readVirEntry **)
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.readVirEntry. 
{ simpl. intros.
  split.
  pattern s in H.
  eexact H.
  intuition. subst;trivial. }
intros vainve.
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.compareVAddrToNull.
intro isnotderiv. simpl.
(** getPd **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getPd.
cbn.
intros s H.
split.
pattern s in H.
eexact H.
split.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
intros currentPD.
(** getTableAddr **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
exists currentPD.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *.
destruct (StateLib.Index.succ PDidx); try now contradict H0.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex);
try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaInCurPartpd. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaInCurPartpd PDidx currentPart vaInCurrentPartition s
        /\ ptVaInCurPartpd = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr vaInCurrentPartition fstLevel = idx ->
isPE ptVaInCurPartpd idx s /\ getTableAddrRoot ptVaInCurPartpd PDidx currentPart vaInCurrentPartition s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
eapply HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptVaInCurPartpdIsnull. simpl.
case_eq ptVaInCurPartpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptVaInCurPartpdNotNull. subst.
(** readAccessible **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readAccessible. simpl.
  intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptVaInCurPartpd (
  StateLib.getIndexOfAddr vaInCurrentPartition fstLevel) s /\
       getTableAddrRoot ptVaInCurPartpd PDidx currentPart
         vaInCurrentPartition s /\ 
       (Nat.eqb defaultPage ptVaInCurPartpd) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaInCurrentPartition fstLevel);trivial.
      intuition. }
   subst.
 split.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. clear Ha3. 
  intuition. subst;trivial. }
intros accessiblesrc. simpl.
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros presentmap. simpl.
(** getTableAddr : to return the physical page of the descChild   **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
split. 
instantiate (1:= currentPart).
unfold consistency in *. 
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
intuition.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP currentPart PDidx currentPD s) by intuition.
exists currentPD.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
    generalize (Hpd  (currentPartition s)  Hpr); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *.
destruct (StateLib.Index.succ PDidx); try now contradict H0.
destruct (lookup (currentPartition s) i (memory s) beqPage beqIndex);
try now contradict H0.
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptDescChildpd. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptDescChildpd PDidx currentPart descChild s /\ ptDescChildpd = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr descChild fstLevel = idx ->
isPE ptDescChildpd idx s /\ getTableAddrRoot ptDescChildpd PDidx currentPart descChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptDescChildpdIsnull. simpl.
case_eq ptDescChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptDescChildpdNotNull. subst.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptDescChildpd 
  (StateLib.getIndexOfAddr descChild fstLevel) s /\
       getTableAddrRoot ptDescChildpd PDidx currentPart descChild s /\ 
       (Nat.eqb defaultPage ptDescChildpd) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr descChild fstLevel);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. }
intro idxDescChild1.
simpl. 
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros presentDescPhy. simpl.
case_eq (negb presentDescPhy);intros Hlegit;subst.
eapply weaken. eapply WP.ret. 
simpl. intros;intuition.
(** readPhyEntry **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPhyEntry. simpl.
  intros.
  split.
  pattern s in H.
  eapply H. 
  subst.
  intuition;subst;trivial. }
intros phyDescChild. simpl.
(** getPd **)
eapply bindRev.
eapply WP.weaken. 
eapply Invariants.getPd.
cbn.
intros s H.
(** descChild is a child *)
assert(Hchildren : In phyDescChild (getChildren (currentPartition s) s)).
{ 
 apply inGetChildren with level currentPD ptDescChildpd ptDescChild currentShadow descChild;
  intuition;subst;trivial.
      apply negb_false_iff in Hlegit.
  subst;trivial.
   }
  

split. 
assert(Hnew := conj H Hchildren).  
pattern s in Hnew.
eexact Hnew.
split.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros pdChildphy.
simpl.
(** getTableAddr : to check if the virtual address is available to map a new page  **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
assert(Hchildpart : In phyDescChild (getPartitions multiplexer s)). 
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
split. 
instantiate (1:= phyDescChild );trivial.
instantiate (1:= PDidx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP phyDescChild PDidx pdChildphy s) by intuition.
exists pdChildphy.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (PDidx = PDidx \/ PDidx = sh1idx \/ PDidx = sh2idx \/  PDidx  = sh3idx
\/  PDidx  = PPRidx \/  PDidx = PRidx) as Htmp 
by auto.
    generalize (Hpd  phyDescChild  Hchildpart); clear Hpd; intros Hpd.
generalize (Hpd PDidx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *; destruct (StateLib.Index.succ PDidx); [|now contradict H0];
destruct (lookup phyDescChild i (memory s) beqPage beqIndex) ; [|now contradict H0];
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaChildpd. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaChildpd PDidx phyDescChild vaChild s /\ ptVaChildpd = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr vaChild fstLevel = idx ->
isPE ptVaChildpd idx s /\ getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxPDidxSh1notEq.
    - contradict Hfalse.
      apply idxPDidxSh2notEq.
    - split;trivial. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }

(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptVaChildpdIsnull. simpl.
case_eq ptVaChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptVaChildpdIsnull. subst.
(** StateLib.getIndexOfAddr **)                
eapply WP.bindRev.
eapply WP.weaken.
eapply Invariants.getIndexOfAddr.
{ simpl. intros.
  destruct H as ((Ha1 & Ha3) & Ha4).
  assert (Hnewget : isPE ptVaChildpd 
  (StateLib.getIndexOfAddr vaChild fstLevel) s /\
       getTableAddrRoot ptVaChildpd PDidx phyDescChild vaChild s /\ 
       (Nat.eqb defaultPage ptVaChildpd) = false).
  { destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
    + subst.
      apply beq_nat_false in Ha4.
      now contradict Ha4.
    + destruct Ha3 with (StateLib.getIndexOfAddr vaChild fstLevel);trivial.
      intuition. }
   subst.
  assert (HP := conj Ha1 Hnewget).
  pattern s in HP.
  eexact HP. }
intro idxvaChild.
simpl. 
(** readPresent **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPresent. simpl.
  intros.
  split.
  pattern s in H.
  eexact H. 
  intuition. subst;trivial. }
intros presentvaChild. simpl.
case_eq (isnotderiv && accessiblesrc && presentmap && negb presentvaChild);intros Hlegit1;subst
        ;[|intros;eapply weaken;[ eapply WP.ret;trivial|
  intros;simpl;intuition]].
(** readPhyEntry **)
eapply WP.bindRev.
{ eapply WP.weaken.
  eapply Invariants.readPhyEntry. simpl.
  intros.
  split.
  pattern s in H.
  eapply H. 
  subst.
  intuition;subst;trivial. }
intros phyVaChild. simpl.
(** getSndShadow **)
eapply bindRev.
eapply weaken.
eapply Invariants.getSndShadow.
simpl;intros.
split. 

pattern s in H. 
exact H.
split. trivial.
unfold consistency in *.
unfold partitionDescriptorEntry in *.
intuition.
simpl.
unfold consistency in *.
unfold  currentPartitionInPartitionsList in *.
assert( currentPart = currentPartition s) by intuition.
subst.
apply childrenPartitionInPartitionList with (currentPartition s); intuition.
intros sh2Childphy.
simpl.
(** getTableAddr : to access to the second shadow page table  **)
eapply WP.bindRev.
eapply WP.weaken. 
apply getTableAddr.
simpl.
intros s H.  
split. 
pattern s in H. 
eexact H. subst.
split. 
intuition.
assert(Hchildpart : In phyDescChild (getPartitions multiplexer s)). 
{ unfold consistency in *. 
  apply childrenPartitionInPartitionList with currentPart; intuition.
  unfold consistency in *. 
  unfold  currentPartitionInPartitionsList in *.
  assert( currentPart = currentPartition s) by intuition.
  subst.
  intuition.
  subst;trivial. }
split. 
instantiate (1:= phyDescChild );trivial.
instantiate (1:= sh2idx).
split. intuition.
assert(Hcons : consistency s) by intuition.
assert(Hlevel : Some level = StateLib.getNbLevel) by intuition. 
assert(Hcp : currentPart = currentPartition s) by intuition.
assert (H0 : nextEntryIsPP phyDescChild sh2idx sh2Childphy s) by intuition.
exists sh2Childphy.
split. intuition.
unfold consistency in *.
destruct Hcons as (Hpd & _ & _ &_  & Hpr & _). 
unfold partitionDescriptorEntry in Hpd.
assert (sh2idx = PDidx \/ sh2idx = sh1idx \/ sh2idx = sh2idx \/  sh2idx  = sh3idx
\/  sh2idx  = PPRidx \/  sh2idx = PRidx) as Htmp 
by auto.
generalize (Hpd  phyDescChild  Hchildpart); clear Hpd; intros Hpd.
generalize (Hpd sh2idx Htmp); clear Hpd; intros Hpd.
destruct Hpd as (Hidxpd & _& Hentry). 
destruct Hentry as (page1 & Hpd & Hnotnull).
subst.
split.
unfold nextEntryIsPP in *;
destruct (StateLib.Index.succ sh2idx); [|now contradict H0];
destruct (lookup phyDescChild i (memory s) beqPage beqIndex); [|now contradict H0];
destruct v ; try now contradict H0.
subst; assumption.
subst. left. split;intuition.
intro ptVaChildsh2. simpl.
(** simplify the new precondition **)     
eapply WP.weaken.
intros.
2: {
intros.
destruct H as (H0 & H1).
assert ( (getTableAddrRoot' ptVaChildsh2 sh2idx phyDescChild vaChild s /\ ptVaChildsh2 = defaultPage) \/
(forall idx : index,
StateLib.getIndexOfAddr vaChild fstLevel = idx ->
isVA ptVaChildsh2 idx s /\ getTableAddrRoot ptVaChildsh2 sh2idx phyDescChild vaChild s  )).
{ destruct H1 as [H1 |(Hi & Hi1 & H1)].
  + left. trivial. 
  + right. intros idx Hidx.
    generalize (H1 idx Hidx);clear H1;intros H1.
    destruct H1 as [(Hpe &Htrue) |[ (Hpe& Hfalse) | (Hpe&Hfalse) ]].
    - (*  split; assumption.
    - *) contradict Htrue.
      apply idxSh2idxSh1notEq.
    - split;trivial.
    - contradict Hfalse.
      symmetrynot.
      apply idxPDidxSh2notEq. }
assert (HP := conj H0 H).
pattern s in HP.
exact HP. }
(** comparePageToNull **) 
eapply WP.bindRev.
eapply Invariants.comparePageToNull.
intro ptVaChildpdIsnull. simpl.
case_eq ptVaChildpdIsnull.
{ intros. eapply WP.weaken.
  eapply WP.ret . simpl.
  intros. intuition. }
intros HptVaChildpdIsnull. subst.
(** write virtual **)
eapply WP.bindRev.
eapply WP.weaken.
eapply writeVirtualInv.
intros.
exact Hlegit1.
exact Hlegit.
intros.
destruct H as ((Ha1 & Ha3) & Ha4).
try repeat rewrite and_assoc in Ha1.
unfold propagatedPropertiesAddVaddr.
split.
exact Ha1.
{ destruct Ha3 as [(Ha3 & Hfalse) | Ha3].
  subst.
  apply beq_nat_false in Ha4.
  now contradict Ha4.
  destruct Ha3 with (StateLib.getIndexOfAddr vaChild fstLevel);trivial.
  intuition. } 
intros [].
(** writeVirEntry **)
eapply bindRev.
eapply weaken.
eapply writeVirEntryAddVaddr;trivial.
intros.
exact Hlegit1.
exact Hlegit.
intros.
simpl.
exact H.
intros [].
(** writeVirEntry **)
eapply bindRev.
eapply weaken.
apply writePhyEntryMapMMUPage.
instantiate (1:= presentDescPhy);trivial.
instantiate (1:= presentvaChild);trivial.
  try repeat rewrite andb_true_iff in *. 
  intuition.
  eapply Hlegit1.
  intros;simpl.
  eapply H.
  intros. eapply weaken.
  eapply WP.ret;trivial.
  intros;trivial.
Qed.
