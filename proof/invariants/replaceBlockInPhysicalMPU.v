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

Require Import Model.ADT Model.Monad Model.MALInternal Model.Lib.
Require Import Core.Internal.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.StateLib Proof.WeakestPreconditions.
Require Import Proof.InternalLemmas Proof.DependentTypeLemmas.
Require Import Invariants.

Require Import Lia Classical List.

Module WP := WeakestPreconditions.

Lemma addElemGeneralCase (s: state) (MPUentry : list paddr) (globalIdPD blockToEnableAddr block: paddr)
                  (MPURegionNb: index) :
   block <> blockToEnableAddr
   -> block <> nullAddr
   -> In block (addElementAt MPURegionNb blockToEnableAddr (MPUentry) nullAddr)
   -> In block (MPUentry).
Proof.
intros HnotEnabled HnotNull. revert MPUentry.
destruct MPURegionNb. induction i.
- simpl. intros MPUentry HinBlock. destruct (MPUentry) eqn:HMPU.
  + simpl in *. destruct HinBlock eqn:Hin; try(exfalso; congruence).
  + simpl in HinBlock. apply not_eq_sym in HnotEnabled. destruct HinBlock eqn:Hin; try(exfalso; congruence).
    simpl. right. assumption.
- intros MPUentry HinBlock. set(l:= MPUentry).
  destruct (MPUentry) eqn:HMPU.
  + simpl in HinBlock. apply not_eq_sym in HnotNull.
    destruct HinBlock as [Hcontra | HinBlock]; try(exfalso; congruence).
    assert (Hpredi: i <= maxIdx) by intuition. specialize (IHi Hpredi MPUentry). rewrite HMPU in IHi.
    specialize (IHi HinBlock). subst l. assumption.
  + simpl in HinBlock. simpl.
    destruct HinBlock as [Hcontra | HinBlock].
    * left. assumption.
    * right.
    assert (Hpredi: i <= maxIdx) by intuition.
    specialize (IHi Hpredi l0). specialize (IHi HinBlock). assumption.
Qed.


(* TODO: put back in removeBlockFromPhysicalMPUIfAlreadyMapped*)
Lemma replaceBlockInPhysicalMPU (globalIdPD blockToEnableAddr: paddr) 
    (MPURegionNb maxRegionNb: index) (P: state -> Prop) :
{{ fun s : state =>
   P s /\ consistency s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s
   (*/\ (exists firstfreepointer, pdentryFirstFreeSlot globalIdPD firstfreepointer s /\
    firstfreepointer <> nullAddr)*)
   /\ StateLib.Index.ltb MPURegionNb zero = false
   /\ StateLib.Index.leb maxRegionNb MPURegionNb = false
   (*/\ maxRegionNb = MALInternal.getMPURegionsNb*)
   /\ (blockToEnableAddr <> nullAddr
      -> (In blockToEnableAddr (getAccessibleMappedBlocks globalIdPD s)))
}}
MAL.replaceBlockInPhysicalMPU globalIdPD blockToEnableAddr MPURegionNb
{{ fun (_: unit) (s : state)=>
  exists s0, P s0 /\ consistency s0 /\ isPDT globalIdPD s0
  /\ consistency s
  /\ globalIdPD <> nullAddr
  /\ (exists pdentry : PDTable, exists pdentry1: PDTable,
     (*exists bentry: BlockEntry,*)
    s = {|
    currentPartition := currentPartition s0;
    memory := add globalIdPD
	              (PDT
		             {|
		             structure := structure pdentry;
		             firstfreeslot := firstfreeslot pdentry;
		             nbfreeslots := nbfreeslots pdentry;
		             nbprepare := nbprepare pdentry;
		             parent := parent pdentry;
		             MPU := addElementAt MPURegionNb blockToEnableAddr (MPU pdentry) nullAddr;
							       vidtAddr := vidtAddr pdentry |}) (memory s0) beqAddr |}
    (*/\ lookup (firstfreeslot pdentry) (memory s0) beqAddr = Some (BE bentry)
    /\ lookup (firstfreeslot pdentry) (memory s) beqAddr = Some (BE bentry)*)
    /\ lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry)
    /\ lookup globalIdPD (memory s) beqAddr = Some (PDT pdentry1) /\
    pdentry1 = {|     structure := structure pdentry;
			         firstfreeslot := firstfreeslot pdentry;
			         nbfreeslots := nbfreeslots pdentry;
			         nbprepare := nbprepare pdentry;
			         parent := parent pdentry;
			         MPU := addElementAt MPURegionNb blockToEnableAddr (MPU pdentry) nullAddr;
								       vidtAddr := vidtAddr pdentry |}
    (* propagate new properties (copied from last step) *)
    /\ pdentryNbFreeSlots globalIdPD (nbfreeslots pdentry) s
    /\ isPDT globalIdPD s0
    /\ isPDT globalIdPD s
    (* globalIdPD's new free slots list and relation with list at s0 *)
    /\ ((*exists (optionfreeslotslist : list optionPaddr),*)
		       (*(n0 n1 : nat) (nbleft : index),
     nbleft = nbfreeslots pdentry /\
     nbleft < n1 /\
    n1 <= maxIdx + 1 /\*)
     s =
     {|
       currentPartition := currentPartition s0;
       memory := add globalIdPD
	              (PDT
		             {|
		             structure := structure pdentry;
		             firstfreeslot := firstfreeslot pdentry;
		             nbfreeslots := nbfreeslots pdentry;
		             nbprepare := nbprepare pdentry;
		             parent := parent pdentry;
		             MPU := addElementAt MPURegionNb blockToEnableAddr (MPU pdentry) nullAddr;
							       vidtAddr := vidtAddr pdentry |}) (memory s0) beqAddr
     |} /\
       ( (*optionfreeslotslist = getFreeSlotsListRec n1 newFirstFreeSlotAddr s2 nbleft /\*)
	         (*getFreeSlotsListRec n1 (firstfreeslot pdentry) s nbleft = optionfreeslotslist /\
	         optionfreeslotslist = getFreeSlotsListRec n0 (firstfreeslot pdentry) s0 nbleft /\
	         n0 <= n1 /\
	         nbleft < n0 /\
	         (wellFormedFreeSlotsList optionfreeslotslist = False -> False) /\
	         NoDup (filterOptionPaddr optionfreeslotslist)  /\*)
	         getKSEntries globalIdPD s = getKSEntries globalIdPD s
	       )

       /\ (	isPDT multiplexer s
		       (*/\ ((forall addr, In addr (getMappedPaddr globalIdPD s) <->
					       In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
						        ++ getMappedPaddr globalIdPD s0)) /\
					       length (getMappedPaddr globalIdPD s) =
					       length (getAllPaddrBlock (startAddr (blockrange bentry6))
							        (endAddr (blockrange bentry6)) ++ getMappedPaddr globalIdPD s0))
		       /\ (forall addr, In addr (getAccessibleMappedPaddr globalIdPD s) <->
					       In addr (getAllPaddrBlock (startAddr (blockrange bentry6)) (endAddr (blockrange bentry6))
						        ++ getAccessibleMappedPaddr globalIdPD s0))*)

		       /\ (* if not concerned *)
			       (forall partition : paddr,
					       partition <> globalIdPD ->
					       isPDT partition s0 ->
					       getKSEntries partition s = getKSEntries partition s0)
		       /\ (forall partition : paddr,
					       partition <> globalIdPD ->
					       isPDT partition s0 ->
					        getMappedPaddr partition s = getMappedPaddr partition s0)
		       /\ (forall partition : paddr,
					       partition <> globalIdPD ->
					       isPDT partition s0 ->
					       getConfigPaddr partition s = getConfigPaddr partition s0)
		       /\ (forall partition : paddr,
												       partition <> globalIdPD ->
												       isPDT partition s0 ->
												       getPartitions partition s = getPartitions partition s0)
		       /\ (forall partition : paddr,
												       partition <> globalIdPD ->
												       isPDT partition s0 ->
												       getChildren partition s = getChildren partition s0)
		       /\ (forall partition : paddr,
												       partition <> globalIdPD ->
												       isPDT partition s0 ->
												       getMappedBlocks partition s = getMappedBlocks partition s0)
		       /\ (forall partition : paddr,
												       partition <> globalIdPD ->
												       isPDT partition s0 ->
												       getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0)
		       /\ (forall partition : paddr,
					       partition <> globalIdPD ->
					       isPDT partition s0 ->
					        getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)

	       )
       /\ (forall partition : paddr,
			       isPDT partition s = isPDT partition s0
		       )
     ))
}}.
Proof.
unfold MAL.replaceBlockInPhysicalMPU.
eapply bindRev.
- (** MAL.readPDMPU **)
  eapply weaken. eapply readPDMPU.
  simpl. intros s H. split.
  eapply H. intuition.
- intro realMPU. eapply bindRev.
  + (** MAL.writePDMPU **)
    eapply weaken. eapply writePDMPU.
    intros s Hprops. simpl. intuition.
    assert (HlookupGlob: exists entry : PDTable, lookup globalIdPD (memory s) beqAddr = Some (PDT entry)).
    { apply isPDTLookupEq. assumption. }
    destruct HlookupGlob as [entry Hlookup].
    exists entry. split.
    apply Hlookup.
    (*assert (isBE (firstfreeslot entry) s).
    {
      unfold consistency in *. unfold consistency1 in *. unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
      intuition. specialize (H12 globalIdPD entry Hlookup).
      destruct H4 as [firstfreepointer HfirstFreeProps].
      destruct HfirstFreeProps as [HfirstFree HfirstNotNull].
      unfold pdentryFirstFreeSlot in HfirstFree.
      rewrite Hlookup in HfirstFree.
      subst firstfreepointer. intuition.
    }*)
    (* Important part *)
    instantiate (1:= fun _ s =>
    globalIdPD <> nullAddr /\
    (*/\ StateLib.Index.pred currnbfreeslots = Some predCurrentNbFreeSlots*)
    (exists s0, exists pdentry newpdentry: PDTable,
    (*exists bentry: BlockEntry,*)
     s = {|
    currentPartition := currentPartition s0;
    memory := add globalIdPD
		            (PDT
			           {|
			           structure := structure pdentry;
			           firstfreeslot := firstfreeslot pdentry;
			           nbfreeslots := nbfreeslots pdentry;
			           nbprepare := nbprepare pdentry;
			           parent := parent pdentry;
			           MPU := addElementAt MPURegionNb blockToEnableAddr (MPU pdentry) nullAddr;
								     vidtAddr := vidtAddr pdentry |}) (memory s0) beqAddr |}
    /\ StateLib.Index.ltb MPURegionNb zero = false
    /\ StateLib.Index.leb maxRegionNb MPURegionNb = false
    (*/\ maxRegionNb = MALInternal.getMPURegionsNb*)
    /\ (blockToEnableAddr <> nullAddr
        -> (In blockToEnableAddr (getAccessibleMappedBlocks globalIdPD s0)))
    (*/\ lookup (firstfreeslot pdentry) (memory s0) beqAddr = Some (BE bentry)
    /\ lookup (firstfreeslot pdentry) (memory s) beqAddr = Some (BE bentry)*)
    /\ lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry)
    /\ lookup globalIdPD (memory s) beqAddr = Some (PDT newpdentry) /\
    newpdentry = {|    structure := structure pdentry;
			     firstfreeslot := firstfreeslot pdentry;
			     nbfreeslots := nbfreeslots pdentry;
			     nbprepare := nbprepare pdentry;
			     parent := parent pdentry;
			     MPU := addElementAt MPURegionNb blockToEnableAddr (MPU pdentry) nullAddr;
								     vidtAddr := vidtAddr pdentry|}
    /\ P s0 /\ consistency s0
    /\ isPDT globalIdPD s0
    (*/\ (pdentryNbFreeSlots globalIdPD currnbfreeslots s0 /\ currnbfreeslots > 0)*)
    (*/\ (exists firstfreepointer, pdentryFirstFreeSlot globalIdPD firstfreepointer s0 /\
    firstfreepointer <> nullAddr)*)
    /\ (exists s1, (*exists optionfreeslotslist s1 n0 n1 nbleft,
    nbleft = (nbfreeslots pdentry) /\*)
    s1 = {|
    currentPartition := currentPartition s0;
    memory := add globalIdPD
		            (PDT
			           {|
			           structure := structure pdentry;
			           firstfreeslot := firstfreeslot pdentry;
			           nbfreeslots := nbfreeslots pdentry;
			           nbprepare := nbprepare pdentry;
			           parent := parent pdentry;
			           MPU := addElementAt MPURegionNb blockToEnableAddr (MPU pdentry) nullAddr;
								     vidtAddr := vidtAddr pdentry |}) (memory s0) beqAddr |} /\
    (*optionfreeslotslist = getFreeSlotsListRec n0 (firstfreeslot pdentry) s0 nbleft /\
    getFreeSlotsListRec n1 (firstfreeslot pdentry) s1 nbleft = optionfreeslotslist /\
    n0 <= n1 /\ nbleft < n0 /\
    nbleft < n1 /\
    n1 <= maxIdx +1 /\
    wellFormedFreeSlotsList optionfreeslotslist <> False /\
    NoDup (filterOptionPaddr (optionfreeslotslist))
    /\ (exists optionentrieslist,
	     optionentrieslist = getKSEntries globalIdPD s0 /\
	     getKSEntries globalIdPD s1 = optionentrieslist
     )
    /\*) (		isPDT multiplexer s
			     /\ getPartitions multiplexer s = getPartitions multiplexer s0
			     /\ getChildren globalIdPD s = getChildren globalIdPD s0
			     /\ getConfigBlocks globalIdPD s = getConfigBlocks globalIdPD s0
			     /\ getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s0
			     /\ getMappedBlocks globalIdPD s = getMappedBlocks globalIdPD s0
			     /\ getMappedPaddr globalIdPD s = getMappedPaddr globalIdPD s0
			     /\ getAccessibleMappedBlocks globalIdPD s = getAccessibleMappedBlocks globalIdPD s0
			     /\ getAccessibleMappedPaddr globalIdPD s = getAccessibleMappedPaddr globalIdPD s0
			     /\ (* if not concerned *)
			     (forall partition : paddr,
						     partition <> globalIdPD ->
						     isPDT partition s0 ->
						     getKSEntries partition s = getKSEntries partition s0)
			     /\ (forall partition : paddr,
						     partition <> globalIdPD ->
						     isPDT partition s0 ->
						      getMappedPaddr partition s = getMappedPaddr partition s0)
			     /\ (forall partition : paddr,
						     partition <> globalIdPD ->
						     isPDT partition s0 ->
						     getConfigPaddr partition s = getConfigPaddr partition s0)
			     /\ (forall partition : paddr,
													     partition <> globalIdPD ->
													     isPDT partition s0 ->
													     getPartitions partition s = getPartitions partition s0)
			     /\ (forall partition : paddr,
													     partition <> globalIdPD ->
													     isPDT partition s0 ->
													     getChildren partition s = getChildren partition s0)
			     /\ (forall partition : paddr,
													     partition <> globalIdPD ->
													     isPDT partition s0 ->
													     getMappedBlocks partition s = getMappedBlocks partition s0)
			     /\ (forall partition : paddr,
													     partition <> globalIdPD ->
													     isPDT partition s0 ->
													     getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0)
			     /\ (forall partition : paddr,
						     partition <> globalIdPD ->
						     isPDT partition s0 ->
						      getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)
		     )
    )
    )).
    simpl.
    assert (Hfirst: pdentryFirstFreeSlot globalIdPD (firstfreeslot entry) s)
               by (apply lookupPDEntryFirstFreeSlot; intuition).
    (*assert (HlookupFirsts: exists b, lookup (firstfreeslot entry) (memory s) beqAddr = Some (BE b)).
    {
      unfold isBE in *. destruct (lookup (firstfreeslot entry) (memory s) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists b. reflexivity.
    }
    destruct HlookupFirsts as [bentryFirst HlookupFirsts].*)
    split. intuition.
    exists s. exists entry. eexists.
    intuition.
    * unfold pdentryMPU in *. rewrite Hlookup in *. rewrite H0. reflexivity.
   (* * eapply HlookupFirsts.
    * assert (HglobNotFree: beqAddr globalIdPD (firstfreeslot entry) = false).
      {
        rewrite <-beqAddrFalse. apply not_eq_sym. apply firstBlockPDNotEq with entry s; intuition.
      }
      rewrite HglobNotFree. rewrite removeDupIdentity; intuition. rewrite <-beqAddrFalse in HglobNotFree.
      apply not_eq_sym in HglobNotFree. contradiction.*)
    * rewrite InternalLemmas.beqAddrTrue. unfold pdentryMPU in *. rewrite Hlookup in *. rewrite H0. reflexivity.
    * eexists ?[s1]. (*eexists. eexists ?[n0]. eexists ?[n1]. eexists ?[nbleft].*)
		  split. intuition.
      assert(StructurePointerIsKS s) by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(PDTIfPDFlag s) by (unfold consistency in *; unfold consistency1 in *; intuition).
      intuition.
      -- assert(multiplexerIsPDT s) by (unfold consistency in *; unfold consistency1 in *; intuition).
         unfold multiplexerIsPDT in *. unfold isPDT in *. simpl.
         destruct (beqAddr globalIdPD multiplexer) eqn:HbeqGlobMulti; try(trivial).
         rewrite <-beqAddrFalse in *.
         rewrite removeDupIdentity; intuition.
      -- unfold getPartitions.
         apply getPartitionsAuxEqPDT with entry; intuition.
      -- apply getChildrenEqPDT with entry; intuition.
      -- apply getConfigBlocksEqPDT with entry; intuition.
      -- apply getConfigPaddrEqPDT with entry; intuition.
      -- apply getMappedBlocksEqPDT with entry; intuition.
      -- apply getMappedPaddrEqPDT with entry; intuition.
      -- apply getAccessibleMappedBlocksEqPDT with entry; intuition.
      -- apply getAccessibleMappedPaddrEqPDT with entry; intuition.
      -- apply getKSEntriesEqPDT with entry; intuition.
      -- apply getMappedPaddrEqPDT with entry; intuition.
      -- apply getConfigPaddrEqPDT with entry; intuition.
      -- apply getPartitionsEqPDT with entry; intuition.
      -- apply getChildrenEqPDT with entry; intuition.
      -- apply getMappedBlocksEqPDT with entry; intuition.
      -- apply getAccessibleMappedBlocksEqPDT with entry; intuition.
      -- apply getAccessibleMappedPaddrEqPDT with entry; intuition.
  + intro. eapply weaken. eapply WP.ret.
    intros s Hprops. simpl. destruct Hprops as [HglobNotNull Hprops].
    destruct Hprops as [s0 Hprops]. destruct Hprops as [pdentry Hprops]. destruct Hprops as [newpdentry Hprops].
    destruct Hprops as [Hs Hprops].
    destruct Hprops as [HregionPos Hprops]. destruct Hprops as [HregionLowerThanMax Hprops].
    destruct Hprops as [HblockProps Hprops].
    exists s0. destruct Hprops as [Hlookups0 Hprops]. destruct Hprops as [Hlookups Hprops].
    destruct Hprops as [HnewPd Hprops].

    assert(HnullAddrExists : nullAddrExists s).
    { (* nullAddrExists s *)
     assert(Hcons0 : nullAddrExists s0) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
     unfold nullAddrExists in Hcons0.
     unfold isPADDR in Hcons0.
     unfold nullAddrExists.
     unfold isPADDR.
     destruct (lookup nullAddr (memory s0) beqAddr) eqn:Hlookup ; try (exfalso ; congruence).
     destruct v eqn:Hv ; try (exfalso ; congruence).
     (* check all possible values of nullAddr in s -> nothing changed a PADDR
		     so nullAddrExists at s0 prevales *)
     destruct (beqAddr globalIdPD nullAddr) eqn:HbeqGlobNull; try(exfalso ; congruence).
     * (* globalIdPD = nullAddr *)
	     rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobNull.
	     rewrite HbeqGlobNull in *.
	     unfold isPDT in *.
	     rewrite Hlookup in *.
	     exfalso ; congruence.
     * (* globalIdPD <> nullAddr *)
	     rewrite Hs.
	     simpl.
	     rewrite HbeqGlobNull. rewrite removeDupIdentity ; intuition.
	     rewrite Hlookup. trivial.
    } (* end of nullAddrExists *)
    intuition.
    * (* consistency s *)
      unfold consistency. unfold consistency1. unfold consistency2.
      (* prove all properties outside to reuse them *)
      assert(StructurePointerIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).

			destruct H3 as [s' (Hstate & Hlists)].
      assert(HsEq: s' = s) by (subst; reflexivity). subst s'. rewrite HsEq in *.

      assert(HwellFormedFstShadowIfBlockEntrys : wellFormedFstShadowIfBlockEntry s).
      { (* BEGIN wellFormedFstShadowIfBlockEntry *)
	      unfold wellFormedFstShadowIfBlockEntry.
	      intros pa HBEaddrs.

	      (* 1) isBE pa s in hypothesis: eliminate impossible values for pa *)
	      destruct (beqAddr globalIdPD pa) eqn:beqpdpa in HBEaddrs ; try(exfalso ; congruence).
	      -- (* globalIdPD = pa *)
		       rewrite <- DependentTypeLemmas.beqAddrTrue in beqpdpa.
		       rewrite <- beqpdpa in *.
		       unfold isPDT in *. unfold isBE in *. rewrite Hlookups in *. exfalso ; congruence.
	      -- (* globalIdPD <> pa: pa is not equal to any modified entry *)
		       apply isBELookupEq in HBEaddrs. rewrite <-HsEq in HBEaddrs. cbn in HBEaddrs.
           destruct HBEaddrs as [entry HBEaddrs].
		       rewrite beqpdpa in HBEaddrs. rewrite removeDupIdentity in HBEaddrs; intuition.
					 (* no modifictions of SHE so what is true at s0 is still true at s *)
					 assert(HSHEEq : isSHE (CPaddr (pa + sh1offset)) s = isSHE (CPaddr (pa + sh1offset)) s0).
           {
					    assert(HSHE : wellFormedFstShadowIfBlockEntry s0) by 
                  (unfold consistency in * ; unfold consistency1 in *; intuition).
						  specialize(HSHE pa).
						  unfold isBE in HSHE.
						  assert(HwellFormedSHE : wellFormedShadowCutIfBlockEntry s0)
													 by (unfold consistency in * ; unfold consistency1 in *; intuition).
						  specialize(HwellFormedSHE pa).
						  unfold isBE in HwellFormedSHE.
              rewrite HBEaddrs in *.
							destruct HwellFormedSHE as [scentryaddr HwellFormedSHEs0] ; trivial.
              intuition. subst scentryaddr. rewrite <-HsEq. unfold isSHE. cbn.
							(* eliminate impossible values for (CPaddr (pa + sh1offset)) *)
							destruct (beqAddr globalIdPD (CPaddr (pa + sh1offset))) eqn:Hscesh1offset.
              - apply beqAddrTrue in Hscesh1offset. rewrite <- Hscesh1offset. rewrite Hlookups0. reflexivity.
              - rewrite removeDupIdentity; intuition. rewrite <-beqAddrFalse in Hscesh1offset.
                apply not_eq_sym in Hscesh1offset. contradiction.
           }
					 rewrite HSHEEq.
					 assert(HwellFormedSHE : wellFormedFstShadowIfBlockEntry s0)
												 by (unfold consistency in * ; unfold consistency1 in *; intuition).
					 specialize(HwellFormedSHE pa).
					 unfold isBE in HwellFormedSHE.
					 rewrite HBEaddrs in *. intuition.
           rewrite <-beqAddrFalse in beqpdpa. apply not_eq_sym in beqpdpa. contradiction.
           (* END wellFormedFstShadowIfBlockEntry *)
      }

      assert(HPDTIfPDFlags : PDTIfPDFlag s).
      { (* BEGIN PDTIfPDFlag s *)
        assert(Hcons0 : PDTIfPDFlag s0) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
	      unfold PDTIfPDFlag.
	      intros idPDchild sh1entryaddr HcheckChilds.
	      destruct HcheckChilds as [HcheckChilds Hsh1entryaddr].
	      (* develop idPDchild *)
	      unfold checkChild in HcheckChilds.
	      unfold entryPDT.
	      unfold bentryStartAddr.

	     (* Force BE type for idPDchild*)
	     destruct(lookup idPDchild (memory s) beqAddr) eqn:Hlookup in HcheckChilds ; try(exfalso ; congruence).
	     destruct v eqn:Hv ; try(exfalso ; congruence).
	     rewrite Hlookup.
       destruct (beqAddr globalIdPD idPDchild) eqn: HbeqGlobChild; try(exfalso; congruence).
       - rewrite <- beqAddrTrue in HbeqGlobChild.
         rewrite HbeqGlobChild in *. congruence.
	     (* - lookup idPDchild s == lookup idPDchild s0
		      - we didn't change the pdflag
		      - explore all possible values of idPdchild's startaddr which must be a PDT
				     - only possible match is with globalIdPD -> ok in this case, it means
					     another entry in s0 points to globalIdPD
				     - for the rest, PDTIfPDFlag at s0 prevales *)
			 - assert(HidPDchildEq : lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s0) beqAddr).
			   {
			     rewrite <-HsEq. cbn. rewrite HbeqGlobChild. rewrite removeDupIdentity ; intuition.
           rewrite <-beqAddrFalse in HbeqGlobChild. apply not_eq_sym in HbeqGlobChild. contradiction.
		     }
         specialize(Hcons0 idPDchild sh1entryaddr).
				 unfold checkChild in Hcons0.
         destruct Hcons0 as [HAFlag (HPflag & HPDflag)]. (* extract the flag information at s0 *)
         {
           rewrite <-HsEq in HcheckChilds.
					 cbn in HcheckChilds.
           destruct (beqAddr globalIdPD sh1entryaddr) eqn: HbeqGlobSh1; try(exfalso; congruence).
           rewrite <-HidPDchildEq. rewrite Hlookup.
           rewrite removeDupIdentity in HcheckChilds; intuition.
           + unfold sh1entryAddr in *. rewrite <-HidPDchildEq. apply Hsh1entryaddr.
           + rewrite <- beqAddrFalse in HbeqGlobSh1.
             apply not_eq_sym in HbeqGlobSh1. contradiction.
         }
				 (* A & P flags *)
				 unfold bentryAFlag in *.
				 unfold bentryPFlag in *.
				 rewrite HidPDchildEq.
				 rewrite HidPDchildEq in *. intuition.
				 (* PDflag *)
				 eexists. intuition.
				 unfold bentryStartAddr in *. unfold entryPDT in *.
         destruct HPDflag as [startaddr HPDflag].
				 rewrite Hlookup in *. intuition.
         rewrite <-HsEq. cbn.
         destruct (beqAddr globalIdPD (startAddr (blockrange b))) eqn: HbeqGlobStart. reflexivity.
         rewrite removeDupIdentity; intuition.
         subst startaddr. assumption.
         rewrite <-beqAddrFalse in HbeqGlobStart. apply not_eq_sym in HbeqGlobStart. contradiction.
         (* END PDTIfPDFlag s *)
      }

      assert(HAccessibleNoPDFlags : AccessibleNoPDFlag s).
      { (* BEGIN AccessibleNoPDFlag s *)
        assert(Hcons0 : AccessibleNoPDFlag s0)
                     by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold AccessibleNoPDFlag.
        intros block sh1entryaddr HBEblocks Hsh1entryAddr HAflag.
        unfold sh1entryPDflag.
        unfold sh1entryAddr in Hsh1entryAddr.
        unfold isBE in HBEblocks.
        (* Force BE type for block*)
        destruct(lookup block (memory s) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
        destruct v eqn:Hv ; try(exfalso ; congruence).
        (* check all possible values of block in s -> 
			         - lookup block s == lookup block s0
			         - we didn't change the pdflag
			         - explore all possible values of sh1entryaddr which didn't change
					         - AccessibleNoPDFlag at s0 prevales depends on the A flag
						         -- we never modified the A flag, so what holds at s0 holds at s *)
        destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock; try(exfalso ; congruence).
        -	(* globalIdPD = block *)
          rewrite <-beqAddrTrue in HbeqGlobBlock.
		      rewrite HbeqGlobBlock in *.
		      congruence.
        - (* globalIdPD <> block *)
          assert(HBEblocks0 : isBE block s0).
          {
            rewrite <-HsEq in Hlookup. cbn in Hlookup.
            rewrite HbeqGlobBlock in Hlookup.
            rewrite removeDupIdentity in Hlookup; intuition.
            unfold isBE. rewrite Hlookup ; trivial.
            rewrite <-beqAddrFalse in HbeqGlobBlock. apply not_eq_sym in HbeqGlobBlock. contradiction.
           }
          (* sh1entryaddr existed at s0 *)
          assert(HwellFormedSh1 : wellFormedFstShadowIfBlockEntry s0)
							           by (unfold consistency in * ; unfold consistency1 in *; intuition).
          unfold wellFormedFstShadowIfBlockEntry in *.
          specialize (HwellFormedSh1 block HBEblocks0).

          assert(Hsh1s0 : isSHE sh1entryaddr s0).
          { rewrite Hsh1entryAddr in *. assumption. }

				  destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1; try(exfalso ; congruence).
          + rewrite <-beqAddrTrue in HbeqGlobSh1.
            rewrite HbeqGlobSh1 in *.
            unfold isSHE in *. unfold isPDT in *.
            destruct (lookup sh1entryaddr (memory s0) beqAddr) ; try(exfalso ; congruence).
            destruct v0 ; try(exfalso ; congruence).
          + assert(Hsh1entryaddrEq : lookup sh1entryaddr (memory s) beqAddr
                                  = lookup sh1entryaddr (memory s0) beqAddr).
            {
              rewrite <-HsEq. cbn.
              rewrite HbeqGlobSh1.
              rewrite removeDupIdentity; intuition.
              rewrite <-beqAddrFalse in HbeqGlobSh1. apply not_eq_sym in HbeqGlobSh1. contradiction.
            }
            rewrite Hsh1entryaddrEq.
					  assert(HSHEsh1s0 : isSHE sh1entryaddr s0) by (exact Hsh1s0).
            unfold isSHE in Hsh1s0.
            destruct (lookup sh1entryaddr (memory s0) beqAddr) eqn:Hlookupsh1 ; try(exfalso ; congruence).
						destruct v0  ; try (exfalso ; congruence).
            assert(Hsh1entryaddrs0 : sh1entryAddr block sh1entryaddr s0).
            {
              unfold sh1entryAddr.
              unfold isBE in HBEblocks0.
              destruct (lookup block (memory s0) beqAddr) ; try(exfalso ; congruence).
              destruct v0 ; try(exfalso ; congruence).
              assumption.
            }
            unfold AccessibleNoPDFlag in *.
            specialize(Hcons0 block sh1entryaddr HBEblocks0 Hsh1entryaddrs0).
            unfold sh1entryPDflag in *.
            rewrite Hlookupsh1 in *.
            destruct Hcons0 ; trivial.
            unfold bentryAFlag in *.
						assert(HblockEq : lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
            {
					    rewrite <-HsEq. cbn.
              rewrite HbeqGlobBlock.
              rewrite removeDupIdentity; intuition.
              rewrite <-beqAddrFalse in HbeqGlobBlock. apply not_eq_sym in HbeqGlobBlock. contradiction.
            }
            rewrite <- HblockEq.
            destruct (lookup block (memory s) beqAddr) ; try(exfalso ; congruence).
            destruct v0 ; try(exfalso ; congruence).
            assumption.
            (* END AccessibleNoPDFlag s *)
      }

      assert(HFirstFreeIsBEAndFreeSlots : FirstFreeSlotPointerIsBEAndFreeSlot s).
      { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
        assert(Hcons0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
            by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold FirstFreeSlotPointerIsBEAndFreeSlot in Hcons0.
        unfold FirstFreeSlotPointerIsBEAndFreeSlot.
        intros entryaddrpd entrypd Hentrypd Hfirstfreeslotentrypd.
        destruct (beqAddr globalIdPD entryaddrpd) eqn:beqpdentry; try(exfalso ; congruence).
        - (* globalIdPD = entryaddrpd *)
          rewrite <-beqAddrTrue in beqpdentry.
          rewrite <- beqpdentry in *.
          specialize (Hcons0 globalIdPD pdentry Hlookups0).
          assert (HeqPdeEpd: newpdentry = entrypd).
          { rewrite Hlookups in Hentrypd. injection Hentrypd. intro Htriv. exact Htriv. }
          assert (HeqFirstFree: firstfreeslot pdentry = firstfreeslot newpdentry).
          { rewrite HnewPd. simpl. reflexivity. }
          destruct Hcons0 as [HRR HHH].
          + congruence.
          + rewrite <-HeqPdeEpd. rewrite <-HeqFirstFree.
            assert(HfirstfreeEq : lookup (firstfreeslot pdentry) (memory s) beqAddr = 
                                  lookup (firstfreeslot pdentry) (memory s0) beqAddr).
            {
              rewrite <-HsEq. cbn.
              destruct (beqAddr globalIdPD (firstfreeslot pdentry)) eqn:HbeqPdentryF
                                                ; try(exfalso ; congruence).
              * rewrite <- beqAddrTrue in HbeqPdentryF.
                apply isBELookupEq in HRR. destruct HRR as [entry HRR]. congruence.
              * rewrite <- beqAddrFalse in HbeqPdentryF. rewrite removeDupIdentity; intuition.
            }
            split.
            * (* isBE *)
              unfold isBE. rewrite HfirstfreeEq.
              unfold isFreeSlot in HHH.
              destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr) eqn:Hlookupfirst
                       ; try(exfalso ; congruence).
              destruct v eqn:Hv ; try(exfalso ; congruence).
              trivial.
            * (* isFreeSlot *)
              unfold isFreeSlot. rewrite HfirstfreeEq.
              unfold isFreeSlot in HHH.
              destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr) eqn:Hlookupfirst
                       ; try(exfalso ; congruence).
              destruct v eqn:Hv ; try(exfalso ; congruence).
              assert(HnewFirstFreeSh1 : lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s) beqAddr
                       = lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr).
						  {
                rewrite <-HsEq. cbn.
                destruct (beqAddr globalIdPD (CPaddr (firstfreeslot pdentry + sh1offset))) eqn: HbeqGlobSh1
                           ; try(exfalso ; congruence).
                - rewrite <-beqAddrTrue in HbeqGlobSh1. rewrite <-HbeqGlobSh1 in *. unfold isPDT in *.
                  destruct (lookup globalIdPD (memory s0) beqAddr) eqn:Hf; try(exfalso ; congruence).
							    destruct v0 eqn:Hv0 ; try(exfalso ; congruence).
                - rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
              }
              rewrite HnewFirstFreeSh1.
              destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr)
                          eqn:Hlookupfirstsh1
                         ; try(exfalso ; congruence).
              destruct v0 eqn:Hv0 ; try(exfalso ; congruence).
              assert(HnewFirstFreeSCE : lookup (CPaddr (firstfreeslot pdentry + scoffset)) (memory s) beqAddr
                         = lookup (CPaddr (firstfreeslot pdentry + scoffset)) (memory s0) beqAddr).
						  {
                rewrite <-HsEq. cbn.
                destruct (beqAddr globalIdPD (CPaddr (firstfreeslot pdentry + scoffset))) eqn:HbeqGlobSh1
                         ; try(exfalso ; congruence).
                - rewrite <-beqAddrTrue in HbeqGlobSh1. rewrite <-HbeqGlobSh1 in *. unfold isPDT in *.
                  destruct (lookup globalIdPD (memory s0) beqAddr) eqn: Hf; try(exfalso ; congruence).
								  destruct v1 eqn:Hv1 ; try(exfalso ; congruence).
                - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; intuition.
              }
              rewrite HnewFirstFreeSCE. apply HHH.
        - (* globalIdPD <> entryaddrpd *)
          rewrite <-beqAddrFalse in beqpdentry.
          assert(HlookupEq : lookup entryaddrpd (memory s) beqAddr = lookup entryaddrpd (memory s0) beqAddr).
          {
            rewrite <-HsEq. cbn.
            destruct (beqAddr globalIdPD entryaddrpd) eqn:HbeqGlobEntry ; try(exfalso ; congruence).
            rewrite <- beqAddrTrue in HbeqGlobEntry.
            rewrite <- HbeqGlobEntry in *. congruence.
            rewrite removeDupIdentity ; intuition.
          }
          assert(Hentrypds0 : lookup entryaddrpd (memory s0) beqAddr = Some (PDT entrypd)).
          { rewrite <- HlookupEq. intuition. }
          specialize (Hcons0 entryaddrpd entrypd Hentrypds0 Hfirstfreeslotentrypd).
          destruct (beqAddr globalIdPD (firstfreeslot entrypd)) eqn:HbeqGlobFirstfree
                                                    ; try(exfalso ; congruence).
				  + (* globalIdPD = firstfreeslot entrypd *)
            rewrite <-beqAddrTrue in HbeqGlobFirstfree.
            rewrite HbeqGlobFirstfree in *. unfold isBE in Hcons0. apply isPDTLookupEq in H0.
            destruct H0 as [Hpdaddr Hpdlookup]. rewrite Hpdlookup in *. intuition.
          + (* globalIdPD <> firstfreeslot entrypd *)
            assert(HfirstfreeEq : lookup (firstfreeslot entrypd) (memory s) beqAddr
                                 = lookup (firstfreeslot entrypd) (memory s0) beqAddr).
            {
              rewrite <-HsEq. cbn. rewrite HbeqGlobFirstfree. rewrite <-beqAddrFalse in HbeqGlobFirstfree.
              rewrite removeDupIdentity; intuition.
            }
            split.
            * (* isBE *)
              unfold isBE. rewrite HfirstfreeEq. intuition.
            * (* isFreeSlot *)
              unfold isFreeSlot. rewrite HfirstfreeEq.
						  unfold isFreeSlot in Hcons0. destruct Hcons0.
						  destruct (lookup (firstfreeslot entrypd) (memory s0) beqAddr) eqn:Hlookupfirst
                       ; try(exfalso ; congruence).
						  destruct v eqn:Hv ; try(exfalso ; congruence).
              assert(HnewFirstFreeSh1 :
                    lookup (CPaddr (firstfreeslot entrypd + sh1offset)) (memory s) beqAddr
                    = lookup (CPaddr (firstfreeslot entrypd + sh1offset)) (memory s0) beqAddr).
						  {
                rewrite <-HsEq. cbn.
                destruct (beqAddr globalIdPD (CPaddr (firstfreeslot entrypd + sh1offset)))
                        eqn:HbeqGlobFirstfreesh1
                       ; try(exfalso ; congruence).
							  - (* globalIdPD = (CPaddr (newFirstFreeSlotAddr + sh1offset)) *)
                  rewrite <-beqAddrTrue in HbeqGlobFirstfreesh1.
								  rewrite <-HbeqGlobFirstfreesh1 in *.
								  unfold isPDT in *.
								  destruct (lookup globalIdPD (memory s0) beqAddr) eqn:Hf; try(exfalso ; congruence).
								  destruct v0 eqn:Hv0 ; try(exfalso ; congruence).
                - (* globalIdPD <> (CPaddr (newFirstFreeSlotAddr + sh1offset)) *)
                  rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
              }
              rewrite HnewFirstFreeSh1.
						  destruct (lookup (CPaddr (firstfreeslot entrypd + sh1offset)) (memory s0) beqAddr)
                          eqn:Hlookupfirstsh1
                         ; try(exfalso ; congruence).
						  destruct v0 eqn:Hv0 ; try(exfalso ; congruence).
              assert(HnewFirstFreeSCE :
                      lookup (CPaddr (firstfreeslot entrypd + scoffset)) (memory s) beqAddr
                     = lookup (CPaddr (firstfreeslot entrypd + scoffset)) (memory s0) beqAddr).
						  {
                rewrite <-HsEq. cbn.
                destruct (beqAddr globalIdPD (CPaddr (firstfreeslot entrypd + scoffset)))
                          eqn:HbeqGlobFirstfreesc
                         ; try(exfalso ; congruence).
							  - (* globalIdPD = (CPaddr (newFirstFreeSlotAddr + scoffset)) *)
									 rewrite <-beqAddrTrue in HbeqGlobFirstfreesc.
									 rewrite <-HbeqGlobFirstfreesc in *.
									 unfold isPDT in *.
									 destruct (lookup globalIdPD (memory s0) beqAddr) eqn:Hf; try(exfalso ; congruence).
									 destruct v1 eqn:Hv1 ; try(exfalso ; congruence).
							  - (* globalIdPD <> (CPaddr (newFirstFreeSlotAddr + scoffset)) *)
									 rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; intuition.
              }
              rewrite HnewFirstFreeSCE.
						  destruct (lookup (CPaddr (firstfreeslot entrypd + scoffset))
											 (memory s0) beqAddr) eqn:Hlookupfirstsc ; try(exfalso ; congruence).
						  destruct v1 eqn:Hv1 ; try(exfalso ; congruence).
						  intuition.
        (* END FirstFreeSlotPointerIsBEAndFreeSlot s *)
      }

      assert(HcurrentPartitionInPartitionsLists : currentPartitionInPartitionsList s).
      { (* BEGIN currentPartitionInPartitionsList s *)
        assert(Hcons0 : currentPartitionInPartitionsList s0)
	                    by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold currentPartitionInPartitionsList in Hcons0.
        unfold currentPartitionInPartitionsList.
        assert(HcurrPartEq : currentPartition s = currentPartition s0).
        { rewrite <-HsEq. simpl. trivial. }
        rewrite HcurrPartEq in *.
        assert(HgetPartitionspdEq1 : getPartitions multiplexer s = getPartitions multiplexer s0).
        { rewrite <-HsEq. apply getPartitionsEqPDT with pdentry; intuition. }
        rewrite HgetPartitionspdEq1. intuition.
        (* END currentPartitionInPartitionsList s *)
      }

      assert(HwellFormedShadowCutIfBlockEntry : wellFormedShadowCutIfBlockEntry s).
      { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      unfold wellFormedShadowCutIfBlockEntry.
      intros pa HBEaddrs.
      (* Check all possible values for pa
	       -> only possible is newBlockEntryAddr
	       2) if pa == newBlockEntryAddr :
			       -> exists scentryaddr in modified state -> OK
	       3) if pa <> newBlockEntryAddr :
			       - relates to another bentry than newBlockentryAddr
				       that was not modified
				       (either in the same structure or another)
			       - pa + scoffset either is
						       - scentryaddr -> newBlockEntryAddr = pa -> contradiction
						       - some other entry -> leads to s0 -> OK
      *)
      (* 1) isBE pa s in hypothesis: eliminate impossible values for pa *)
      destruct (beqAddr globalIdPD pa) eqn:HbeqGlobPa in HBEaddrs ; try(exfalso ; congruence).
      - (* globalIdPD = pa *)
       rewrite <-beqAddrTrue in HbeqGlobPa.
       rewrite <-HbeqGlobPa in *.
       unfold isPDT in *. unfold isBE in *. rewrite Hlookups in *.
       exfalso ; congruence.
      - (* globalIdPD <> pa *)
        assert(Hcons0 : wellFormedShadowCutIfBlockEntry s0)
		       by (unfold consistency in * ; unfold consistency1 in *; intuition).
        unfold wellFormedShadowCutIfBlockEntry in *.
        assert(HBEeq : isBE pa s = isBE pa s0).
        {
          unfold isBE. rewrite <-HsEq. cbn. rewrite HbeqGlobPa.
          rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
        }
        assert(HBEaddrs0 : isBE pa s0).
        { rewrite <- HBEeq. assumption. }
        specialize(Hcons0 pa HBEaddrs0).
        destruct Hcons0 as [scentryaddr (HSCEs0' & Hsceq)].
				destruct (beqAddr globalIdPD (CPaddr (pa + scoffset))) eqn:HbeqGlobScoffset.
        + (* globalIdPD = (CPaddr (pa + sh1offset))*)
          rewrite <-beqAddrTrue in *.
          rewrite <-HbeqGlobScoffset in *.
          unfold isSCE in *. unfold isPDT in *.
          rewrite Hsceq in *.
          destruct (lookup globalIdPD (memory s0) beqAddr) eqn:Hlookup ; try(exfalso ; congruence).
          destruct v eqn:Hv ; try(exfalso ; congruence).
        + (* globalIdPD <> (CPaddr (pa + sh1offset))*)
          (* resolve the only true case *)
          exists scentryaddr. intuition.
          assert(HSCEeq : isSCE scentryaddr s = isSCE scentryaddr s0).
          {
            unfold isSCE. rewrite <-HsEq. cbn. rewrite <-Hsceq in HbeqGlobScoffset.
            rewrite HbeqGlobScoffset. rewrite <- beqAddrFalse in *.
            rewrite removeDupIdentity ; intuition.
          }
          rewrite HSCEeq. assumption.
        (* END wellFormedShadowCutIfBlockEntry *)
      }

      assert(HBlocksRangeFromKernelStartIsBEs : BlocksRangeFromKernelStartIsBE s).
      { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
        unfold BlocksRangeFromKernelStartIsBE.
        intros kernelentryaddr blockidx HKSs Hblockidx.
        assert(Hcons0 : BlocksRangeFromKernelStartIsBE s0)
                   by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold BlocksRangeFromKernelStartIsBE in Hcons0.
        (* check all possible values for bentryaddr in the modified state s *)
        destruct (beqAddr globalIdPD kernelentryaddr) eqn:HbeqGlobEntry; try(exfalso ; congruence).
        - (* globalIdPD = kernelentryaddr *)
          rewrite <-beqAddrTrue in HbeqGlobEntry.
          rewrite <- HbeqGlobEntry in *.
          unfold isPDT in *.
          unfold isKS in *.
          destruct (lookup globalIdPD (memory s) beqAddr) ; try(exfalso ; congruence).
          destruct v ; try(exfalso ; congruence).
        - (* globalIdPD <> kernelentryaddr *)
          assert(HKSeq : isKS kernelentryaddr s = isKS kernelentryaddr s0).
          {
            unfold isKS. rewrite <-HsEq. cbn.
            rewrite HbeqGlobEntry. rewrite <- beqAddrFalse in *.
            rewrite removeDupIdentity; intuition.
          }
          assert(HKSs0 : isKS kernelentryaddr s0).
          { rewrite <- HKSeq. assumption. }
          specialize(Hcons0 kernelentryaddr blockidx HKSs0 Hblockidx).
          destruct (beqAddr globalIdPD (CPaddr (kernelentryaddr + blockidx))) eqn:HbeqGlobIdx
                        ; try(exfalso ; congruence).
				 + (* globalIdPD = (CPaddr (kernelentryaddr + blockidx) *)
					 rewrite <-beqAddrTrue in HbeqGlobIdx. rewrite <- HbeqGlobIdx in *.
					 unfold isPDT in *. unfold isBE in *.
					 destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
					 destruct v ; try(exfalso ; congruence).
				 + (* globalIdPD <> (CPaddr (kernelentryaddr + blockidx) *)
					 unfold isBE. rewrite <-HsEq. cbn. rewrite HbeqGlobIdx. rewrite <- beqAddrFalse in *.
					 rewrite removeDupIdentity ; intuition.
        (* END BlockEntryAddrInBlocksRangeIsBE *)
      }

      assert(HKernelStructureStartFromBlockEntryAddrIsKSs : KernelStructureStartFromBlockEntryAddrIsKS s).
      { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
        unfold KernelStructureStartFromBlockEntryAddrIsKS.
        intros bentryaddr blockidx Hlookup Hblockidx.
        assert(Hcons0 : KernelStructureStartFromBlockEntryAddrIsKS s0)
                   by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold KernelStructureStartFromBlockEntryAddrIsKS in Hcons0.
        (* check all possible values for bentryaddr in the modified state s *)
        destruct (beqAddr globalIdPD bentryaddr) eqn:HbeqGlobBentry; try(exfalso ; congruence).
        - (* globalIdPD = bentryaddr *)
	        rewrite <-beqAddrTrue in HbeqGlobBentry. rewrite <- HbeqGlobBentry in *.
	        unfold isPDT in *. unfold isBE in *.
	        destruct (lookup globalIdPD (memory s) beqAddr) ; try(exfalso ; congruence).
	        destruct v ; try(exfalso ; congruence).
        - (* globalIdPD <> bentryaddr *)
	        assert(HblockEq : isBE bentryaddr s = isBE bentryaddr s0).
          {
            unfold isBE. rewrite <-HsEq. cbn. rewrite HbeqGlobBentry.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
          }
          assert(Hblocks0 : isBE bentryaddr s0) by (rewrite HblockEq in * ; intuition).
          apply isBELookupEq in Hlookup. destruct Hlookup as [blockentry Hlookup].
          unfold bentryBlockIndex in *. rewrite Hlookup in *.
          specialize(Hcons0 bentryaddr blockidx Hblocks0).
          apply isBELookupEq in Hblocks0. destruct Hblocks0 as [blockentrys0 Hblocks0].
          rewrite Hblocks0 in *. intuition.
          assert(HlookupEq : lookup bentryaddr (memory s) beqAddr = lookup bentryaddr (memory s0) beqAddr).
          {
            rewrite <-HsEq. cbn. rewrite HbeqGlobBentry.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
          }
          assert(HlookupEq' : lookup bentryaddr (memory s0) beqAddr = Some (BE blockentry)).
          { rewrite <- HlookupEq. intuition. }
            rewrite HlookupEq' in *. inversion Hblocks0.
            subst blockentrys0. intuition.
            (* Check all values *)
			      destruct (beqAddr globalIdPD (CPaddr (bentryaddr - blockidx))) eqn:HbeqGlobKs
                                                        ; try(exfalso ; congruence).
				    + (* globalIdPD = (CPaddr (bentryaddr - blockidx)) *)
			         rewrite <-beqAddrTrue in HbeqGlobKs. rewrite <-HbeqGlobKs in *.
			         unfold isPDT in *. unfold isKS in *.
			         destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
			         destruct v ; try(exfalso ; congruence).
			      + (* globalIdPD <> (CPaddr (bentryaddr - blockidx)) *)
              unfold isKS. rewrite <-HsEq. cbn. rewrite HbeqGlobKs.
              rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
        (* END KernelStructureStartFromBlockEntryAddrIsKS *)
      }

      assert(Hsh1InChildLocationIsBEs : sh1InChildLocationIsBE s).
      { (* BEGIN sh1InChildLocationIsBE s *)
        unfold sh1InChildLocationIsBE.
        intros sh1entryaddr sh1entry Hlookup Hsh1entryNotNull.

        assert(Hcons0 : sh1InChildLocationIsBE s0)
                   by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold sh1InChildLocationIsBE in Hcons0.

      (* check all possible values for sh1entryaddr in the modified state s
	       -> no entry modifications correspond to SH1Entry type
	       (inChildLocation sh1entry) only possible value is NewBlockEntryAddr
	       - = NewBlockEntryAddr -> isBE at s so OK
	       - <> NewBlockEntryAddr -> leads to s0 -> OK
      *)
      (* Check all values *)
      destruct (beqAddr globalIdPD sh1entryaddr) eqn:HbeqGlobSh1entry; try(exfalso ; congruence).
      - (* globalIdPD = sh1entryaddr *)
	      rewrite <-beqAddrTrue in HbeqGlobSh1entry.
	      rewrite <-HbeqGlobSh1entry in *.
	      destruct (lookup globalIdPD (memory s) beqAddr) ; try(exfalso ; congruence).
      - (* globalIdPD <> sh1entryaddr *)
	      assert(HSHEEq : lookup sh1entryaddr (memory s) beqAddr = lookup sh1entryaddr (memory s0) beqAddr).
        {
          rewrite <-HsEq. cbn. rewrite HbeqGlobSh1entry.
          rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
        }
        assert(Hlookupsh1 : lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry))
                by (rewrite HSHEEq in * ; intuition).
        specialize(Hcons0 sh1entryaddr sh1entry Hlookupsh1 Hsh1entryNotNull).
        (* Check all values *)
			  destruct (beqAddr globalIdPD (inChildLocation sh1entry)) eqn:HbeqGlobSh1; try(exfalso ; congruence).
				+ (* globalIdPD = (inChildLocation sh1entry) *)
          rewrite <-beqAddrTrue in HbeqGlobSh1.
          rewrite <-HbeqGlobSh1 in *.
          unfold isPDT in *.
          unfold isBE in *.
          destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
          destruct v ; try(exfalso ; congruence).
			  + (* globalIdPD <> (inChildLocation sh1entry) *)
					unfold isBE. rewrite <-HsEq. cbn. rewrite HbeqGlobSh1.
					rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
        (* END sh1InChildLocationIsBE *)
      }

      assert(HStructurePointerIsKSs : StructurePointerIsKS s).
      { (* BEGIN StructurePointerIsKS s *)
        unfold StructurePointerIsKS.
        intros pdentryaddr pdentry' Hlookup HstructureNotNull.

        assert(Hcons0 : StructurePointerIsKS s0)
               by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold StructurePointerIsKS in Hcons0.
        (* check all possible values for pdentryaddr in the modified state s
	         -> only possible is globalIdPD
         1) if pdentryaddr == globalIdPD :
		         - the structure pointer cannot be modified -> leads to s0 -> OK
         2) if pdentryaddr <> globalIdPD :
		         - relates to another PD than globalIdPD,
			         the structure pointer cannot be modified -> leads to s0 -> OK
        *)
        (* Check all values except globalIdPD *)
        destruct (beqAddr globalIdPD pdentryaddr) eqn:HbeqGlobPdentry; try(exfalso ; congruence).
		    - (* globalIdPD = pdentryaddr *)
          rewrite <-beqAddrTrue in HbeqGlobPdentry.
          rewrite <-HbeqGlobPdentry in *.
          assert(HpdentryEq : newpdentry = pdentry').
			    { rewrite Hlookups in Hlookup. inversion Hlookup. trivial. }
			    subst pdentry'.
			    assert(HstructureEq : (structure newpdentry) = (structure pdentry)).
			    { subst newpdentry. simpl. trivial. }
			    rewrite HstructureEq in *.
			    specialize(Hcons0 globalIdPD pdentry Hlookups0 HstructureNotNull).
			    (* Check all values for structure pdentry *)
			    destruct (beqAddr globalIdPD (structure pdentry)) eqn:HbeqGlobPtn; try(exfalso ; congruence).
				  + (* globalIdPD = (structure pdentry) *)
            rewrite <-beqAddrTrue in HbeqGlobPtn.
            rewrite <-HbeqGlobPtn in *.
            unfold isPDT in *.
            unfold isKS in *.
            destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
            destruct v ; try(exfalso ; congruence).
				  + (* globalIdPD <> (structure pdentry) *)
					  unfold isKS. rewrite <-HsEq. cbn. rewrite HbeqGlobPtn.
						rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
		    - (* globalIdPD <> pdentryaddr *)
				  assert(HPDEq : lookup pdentryaddr (memory s) beqAddr = lookup pdentryaddr (memory s0) beqAddr).
				  {
            rewrite <-HsEq. cbn. rewrite HbeqGlobPdentry.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
				  }
				  assert(Hlookuppd : lookup pdentryaddr (memory s0) beqAddr = Some (PDT pdentry'))
					       by (rewrite HPDEq in * ; intuition).
				  specialize(Hcons0 pdentryaddr pdentry' Hlookuppd HstructureNotNull).
				  (* Check all values *)
				  destruct (beqAddr globalIdPD (structure pdentry')) eqn:HbeqGlobPtn ; try(exfalso ; congruence).
					+ (* globalIdPD = (inChildLocation sh1entry) *)
            rewrite <-beqAddrTrue in HbeqGlobPtn.
            rewrite <-HbeqGlobPtn in *.
            unfold isPDT in *.
            unfold isKS in *.
            destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
            destruct v ; try(exfalso ; congruence).
				 + (* globalIdPD <> (structure pdentry') *)
					 unfold isKS. rewrite <-HsEq. cbn. rewrite HbeqGlobPtn.
					 rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
        (* END StructurePointerIsKS *)
      }

      assert(HNextKSIsKSs : NextKSIsKS s).
      { (* NextKSIsKS s *)
        unfold NextKSIsKS.
        intros ksaddr nextksaddr next HKS Hnextksaddr Hnext HnextNotNull.
        assert(Hcons0 : NextKSIsKS s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold NextKSIsKS in Hcons0.
        (* check all possible values for ksaddr in the modified state s
	         -> nextks and nextksaddr never modified
	         -> leads to s0, even if nextksaddr == newB -> OK
        *)
        destruct (beqAddr globalIdPD ksaddr) eqn:HbeqGlobKs; try(exfalso ; congruence).
        - (* globalIdPD = ksaddr *)
	        rewrite <-beqAddrTrue in HbeqGlobKs.
	        rewrite <-HbeqGlobKs in *.
	        unfold isPDT in *.
	        unfold isKS in *.
	        destruct (lookup globalIdPD (memory s) beqAddr) ; try(exfalso ; congruence).
	        destruct v ; try(exfalso ; congruence).
        - (* globalIdPD <> ksaddr *)
		       (* COPY from BlocksRangeFromKernelStartIsBE *)
		       assert(HKSEq : isKS ksaddr s = isKS ksaddr s0).
		       {
			       unfold isKS.
			       rewrite <-HsEq. cbn. rewrite HbeqGlobKs.
					   rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
		       }
		       assert(HKSs0 : isKS ksaddr s0) by (rewrite HKSEq in * ; intuition).
		       assert(HnextaddrEq : nextKSAddr ksaddr nextksaddr s = nextKSAddr ksaddr nextksaddr s0).
		       {
			       unfold nextKSAddr.
			       rewrite <-HsEq. cbn. rewrite HbeqGlobKs.
					   rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
		       }
		       assert(Hnextaddrs0 : nextKSAddr ksaddr nextksaddr s0) by (rewrite HnextaddrEq in * ; intuition).
		       assert(Hnextaddr : nextksaddr = CPaddr (ksaddr + nextoffset)).
		       {
			       unfold nextKSAddr in *. unfold isKS in *.
			       destruct (lookup ksaddr (memory s) beqAddr) eqn:Hks ; try(exfalso ; congruence).
			       destruct v eqn:Hv ; try(exfalso ; congruence).
			       intuition.
		       }
		       assert(HnextEq : nextKSentry nextksaddr next s = nextKSentry nextksaddr next s0).
		       {
			       unfold nextKSentry.
			       rewrite <-HsEq. cbn.
					   assert(Hcons1 : NextKSOffsetIsPADDR s0) 
                      by (unfold consistency in * ; unfold consistency1 in * ; intuition).
			       unfold NextKSOffsetIsPADDR in *.
			       specialize(Hcons1 ksaddr nextksaddr HKSs0 Hnextaddrs0).
						 destruct (beqAddr globalIdPD nextksaddr) eqn:HbeqGlobNextaddr ; try(exfalso;congruence).
						 -	rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobNextaddr.
                rewrite HbeqGlobNextaddr in *.
                unfold isPDT in *.
                unfold isPADDR in *.
                destruct(lookup nextksaddr (memory s0) beqAddr) eqn:Hf ; try(exfalso ; congruence).
                destruct v eqn:Hv ; try(exfalso ; congruence). reflexivity.
						 -	rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
		       }
		       assert(Hnexts0 : nextKSentry nextksaddr next s0) by (rewrite HnextEq in * ; intuition).
		       (* specialize for ksaddr *)
		       specialize(Hcons0 ksaddr nextksaddr next HKSs0 Hnextaddrs0 Hnexts0 HnextNotNull).
		       (* check all values *)
		       destruct (beqAddr globalIdPD next) eqn:HbeqGlobNext; try(exfalso ; congruence).
			     + (* globalIdPD = nextksaddr *)
			       rewrite <-beqAddrTrue in HbeqGlobNext.
			       rewrite <-HbeqGlobNext in *.
			       unfold isPDT in *.
			       unfold isKS in *.
			       destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
			       destruct v ; try(exfalso ; congruence).
			    + (* globalIdPD <> nextksaddr *)
				    unfold isKS. rewrite <-HsEq. cbn. rewrite HbeqGlobNext.
		        rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
        (* END NextKSIsKS *)
      }

      assert(HNextKSOffsetIsPADDRs: NextKSOffsetIsPADDR s).
      { (* BEGIN NextKSOffsetIsPADDR s *)
        unfold NextKSOffsetIsPADDR.
        intros ksaddr nextksaddr HKS Hnextksaddr.
        assert(Hcons0 : NextKSOffsetIsPADDR s0)
                     by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold NextKSOffsetIsPADDR in Hcons0.
        (* check all possible values for ksaddr in the modified state s
	         -> nextks and nextksaddr never modified
	         -> values for nextksaddr leads to s0 cause nothing matches -> OK
        *)
        (* Check all values *)
        destruct (beqAddr globalIdPD ksaddr) eqn:HbeqGlobKs; try(exfalso ; congruence).
        - (* globalIdPD = ksaddr *)
          rewrite <-beqAddrTrue in HbeqGlobKs.
          rewrite <-HbeqGlobKs in *.
          unfold isPDT in *.
          unfold isKS in *.
          destruct (lookup globalIdPD (memory s) beqAddr) ; try(exfalso ; congruence).
          destruct v ; try(exfalso ; congruence).
        - (* globalIdPD <> ksaddr *)
		      assert(HKSEq : isKS ksaddr s = isKS ksaddr s0).
		      {
			      unfold isKS. rewrite <-HsEq. cbn.
					  rewrite HbeqGlobKs. rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
					}
		      assert(HKSs0 : isKS ksaddr s0) by (rewrite HKSEq in * ; intuition).
		      assert(HnextaddrEq : nextKSAddr ksaddr nextksaddr s = nextKSAddr ksaddr nextksaddr s0).
		      {
			      unfold nextKSAddr. rewrite <-HsEq. cbn. rewrite HbeqGlobKs.
					  rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
		      }
		      assert(Hnextaddrs0 : nextKSAddr ksaddr nextksaddr s0) by (rewrite HnextaddrEq in * ; intuition).
		      assert(Hnextaddr : nextksaddr = CPaddr (ksaddr + nextoffset)).
		      {
			      unfold nextKSAddr in *. unfold isKS in *.
			      destruct (lookup ksaddr (memory s) beqAddr) eqn:Hks ; try(exfalso ; congruence).
			      destruct v eqn:Hv ; try(exfalso ; congruence).
			      intuition.
		      }
		      (* specialize for ksaddr *)
		      specialize(Hcons0 ksaddr nextksaddr HKSs0 Hnextaddrs0).
		      (* check all values *)
		      destruct (beqAddr globalIdPD nextksaddr) eqn:HbeqGlobNext; try(exfalso ; congruence).
			    + (* globalIdPD = nextksaddr *)
					  rewrite <-beqAddrTrue in HbeqGlobNext.
					  rewrite <-HbeqGlobNext in *.
            unfold isPDT in *.
            unfold isPADDR in *.
            destruct (lookup globalIdPD (memory s0) beqAddr) ; intuition ;  try(exfalso ; congruence).
            destruct v ; try(exfalso ; congruence).
			    + (* globalIdPD <> nextksaddr *)
				    unfold isPADDR. rewrite <-HsEq. cbn. rewrite HbeqGlobNext.
						rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
        (* END NextKSOffsetIsPADDR *)
      }

      assert(HNoDupInFreeSlotsLists : NoDupInFreeSlotsList s).
      { (* BEGIN NoDupInFreeSlotsList s *)
        unfold NoDupInFreeSlotsList.
        intros pd entrypd Hlookuppd.
        assert(Hcons0 : NoDupInFreeSlotsList s0) 
                by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold NoDupInFreeSlotsList in Hcons0.
        (* check all possible values for pd in the modified state s
	         -> only possible is globalIdPD, we already proved we had no Dup
         if it is another pd, we must prove there are still noDup in that list
	         by showing this list was never modified
	         -> compute the list at each modified state and check not changed from s0 -> OK
        *)
        destruct (beqAddr globalIdPD pd) eqn:HbeqGlobPd; try(exfalso ; congruence).
        - (* globalIdPD = pd *)
          (* case already proved step by step *)
          rewrite <-beqAddrTrue in HbeqGlobPd.
          rewrite <-HbeqGlobPd in *.
          specialize(Hcons0 globalIdPD pdentry Hlookups0).
          destruct Hcons0 as [listoption (Hoptionlist & (Hwellformed & HNoDup))].
          exists listoption. intuition. rewrite Hoptionlist.
          unfold getFreeSlotsList. rewrite Hlookups0. rewrite Hlookups.
          rewrite HnewPd. simpl.
          destruct (beqAddr (firstfreeslot pdentry) nullAddr) eqn:HbeqFirstNull; try(exfalso ; congruence).
          + (* firstfreeslot pdentry = nullAddr *)
            reflexivity.
          + (* firstfreeslot pdentry <> nullAddr *)
            assert(pdentryFirstFreeSlot globalIdPD (firstfreeslot pdentry) s0)
                by (apply lookupPDEntryFirstFreeSlot; intuition).
            rewrite <-HsEq. apply eq_sym.
            apply getFreeSlotsListRecEqPDT.
            apply firstBlockPDNotEq with pdentry s0; intuition.
            exists (firstfreeslot pdentry). rewrite <-beqAddrFalse in *. intuition.
            unfold isBE. rewrite Hlookups0. intuition.
            unfold isPADDR. rewrite Hlookups0. intuition.
        - (* globalIdPD <> pd *)
          specialize(Hcons0 pd).
          unfold getFreeSlotsList.
          destruct (lookup pd (memory s) beqAddr) eqn:Hpdentry ; try(exfalso ; congruence).
          destruct v eqn:Hv ; try(exfalso ; congruence).
          assert(HlookupEq : lookup pd (memory s) beqAddr = lookup pd (memory s0) beqAddr).
          {	(* check all values *)
            destruct (beqAddr globalIdPD pd) eqn:HbeqGlobPdentry; try(exfalso ; congruence).
            (* globalIdPD <> pd *)
            rewrite <-HsEq.
            cbn. rewrite HbeqGlobPdentry. rewrite removeDupIdentity ; intuition.
            rewrite <- beqAddrFalse in *. apply not_eq_sym in HbeqGlobPdentry. contradiction.
          }
          assert(HlookupPds0: lookup pd (memory s0) beqAddr = Some (PDT p)).
          rewrite <- HlookupEq. intuition.
          specialize (Hcons0 p HlookupPds0).
          unfold getFreeSlotsList in *. rewrite HlookupPds0 in *.
          destruct (beqAddr (firstfreeslot p) nullAddr) ; try(exfalso ; congruence).
          + (* optionfreeslotslist = NIL *) 
		        destruct Hcons0 as [optionfreeslotslist (Hnil & HwellFormed & HNoDup)].
		        exists optionfreeslotslist. intuition.
          + (* optionfreeslotslist <> NIL *)
		        (* show list equality between s0 and s*)
            assert(HfreeslotsEqn: getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s (nbfreeslots p)
                               = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
            {
              rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
               + intro Hfirstpdeq.
		             assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
			               by (unfold consistency in * ; unfold consistency1 in * ; intuition).
	               unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
	               specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p HlookupPds0).
	               destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
		             * intro HfirstfreeNull.
		               assert(HnullAddrExistss0 : nullAddrExists s0)
			               by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		               unfold nullAddrExists in *.
		               unfold isPADDR in *.
		               rewrite HfirstfreeNull in *. rewrite <- Hfirstpdeq in *. congruence.
		             * rewrite Hfirstpdeq in *.
		               unfold isBE in *.
		               destruct (lookup globalIdPD (memory s0) beqAddr) ; try (exfalso ; congruence).
		               destruct v0 ; try(exfalso ; congruence).
               + unfold isBE. rewrite Hlookups0. intuition.
               + unfold isPADDR. rewrite Hlookups0. intuition.
            }
            rewrite HfreeslotsEqn. assumption.
        (* END NoDupInFreeSlotsList *)
      }

      assert(HfreeSlotsListIsFreeSlots : freeSlotsListIsFreeSlot s).
      { (* BEGIN freeSlotsListIsFreeSlot s *)
        unfold freeSlotsListIsFreeSlot.
        intros pd freeslotaddr optionfreeslotslist freeslotslist HPDTpds.
        intros (HoptionfreeSlotsList & HwellFormedFreeSlots) (HfreeSlotsList & HfreeSlotInList).
        intro HfreeSlotNotNull.
        assert(Hcons0 : freeSlotsListIsFreeSlot s0)
                 by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold freeSlotsListIsFreeSlot in Hcons0.
        (* check all possible values for freeslotaddr in the modified state s
            -> leads to s0 -> OK
        *)
        (* Check all values for pd *)
        destruct (beqAddr globalIdPD pd) eqn:HbeqGlobPd; try(exfalso ; congruence).
		    - (* globalIdPD = pd *)
				  rewrite <- beqAddrTrue in HbeqGlobPd.
				  rewrite <- HbeqGlobPd in *.
				  specialize (Hcons0 globalIdPD freeslotaddr optionfreeslotslist freeslotslist H0).
				  assert(HslotslistEqs0 : optionfreeslotslist = getFreeSlotsList globalIdPD s0 /\
									  wellFormedFreeSlotsList optionfreeslotslist <> False).
				  {
            split.
            + unfold getFreeSlotsList in *. rewrite Hlookups0 in *. rewrite Hlookups in *. rewrite HnewPd in *.
              simpl in *.
					    destruct (beqAddr (firstfreeslot pdentry) nullAddr) eqn:Hf ; try(exfalso ; congruence).
              assumption.
              rewrite <-beqAddrFalse in Hf.
              assert(HfreeslotsEqn:
                      getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s (nbfreeslots pdentry)
                     = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
              {
                rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
                 + intro Hfirstpdeq.
		               assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
			                 by (unfold consistency in * ; unfold consistency1 in * ; intuition).
	                 unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
	                 specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 globalIdPD pdentry Hlookups0 Hf).
	                 destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                   unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                 + unfold isBE. rewrite Hlookups0. intuition.
                 + unfold isPADDR. rewrite Hlookups0. intuition.
              }
              rewrite HfreeslotsEqn in *. assumption.
					  + assumption.
          }
          specialize (Hcons0 HslotslistEqs0).
					 (* continue to break Hcons0 1) globalIdPD -> go to s0 show isFreeSlot @ s0 is false
																			 2) newB -> show not in free slots list so NOK *)
					assert(HslotsListEqs : freeslotslist = filterOptionPaddr optionfreeslotslist /\
														  In freeslotaddr freeslotslist) by intuition.
					specialize (Hcons0 HslotsListEqs HfreeSlotNotNull).
					(* 1) dismiss all impossible values for freeslotaddr except newB *)
					destruct (beqAddr globalIdPD freeslotaddr) eqn:HbeqGlobFree; try(exfalso ; congruence).
					+ (* globalIdPD = freeslotaddr *)
					  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobFree.
					  rewrite <- HbeqGlobFree in *.
					  unfold isPDT in *.
					  unfold isFreeSlot in *.
					  destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
					  destruct v ; try(exfalso ; congruence).
					+ (* globalIdPD <> freeslotaddr *)
            (* no entry left to try out -> leads to s0 *)
            rewrite <-HsEq. unfold isFreeSlot.
            cbn. rewrite HbeqGlobFree. rewrite <-beqAddrFalse in HbeqGlobFree.
            rewrite removeDupIdentity ; try congruence.
            unfold isFreeSlot in *.
            destruct (lookup freeslotaddr (memory s0) beqAddr) eqn:HfreeSlots0 ; try(exfalso ; congruence).
            destruct v ; try(exfalso ; congruence).
            destruct (beqAddr globalIdPD (CPaddr (freeslotaddr + sh1offset))) eqn:HbeqGlobFreesh1
                       ; try(exfalso ; congruence).
            * rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobFreesh1.
              rewrite <- HbeqGlobFreesh1 in *.
              unfold isPDT in *.
              destruct (lookup globalIdPD (memory s0)) eqn:HlookupGlobF0
                     ; try(exfalso ; congruence).
              destruct v ; try(exfalso ; congruence).
            * rewrite <- DependentTypeLemmas.beqAddrFalse in HbeqGlobFreesh1.
              rewrite removeDupIdentity ; try congruence. 
              assert (isBE freeslotaddr s0) by (apply isBELookupEq; exists b; assumption).
              assert (HwellFormed: wellFormedFstShadowIfBlockEntry s0)
                       by (unfold consistency in *; unfold consistency1 in *; intuition).
              unfold wellFormedFstShadowIfBlockEntry in HwellFormed.
              assert (HsheFree: isSHE (CPaddr (freeslotaddr + sh1offset)) s0)
                             by (apply HwellFormed; intuition).
              unfold isSHE in *.
              destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s0) beqAddr) eqn:HlookupFreesh1
                         ; try(exfalso ; congruence).
              destruct v ; try(exfalso ; congruence).
              destruct (beqAddr globalIdPD (CPaddr (freeslotaddr + scoffset))) eqn: HbeqGlobFreesce
                    ; try(exfalso ; congruence).
              -- rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobFreesce.
                 rewrite <- HbeqGlobFreesce in *.
                 unfold isPDT in *.
                 destruct (lookup globalIdPD (memory s0)) eqn:HlookupGlobF0
                     ; try(exfalso ; congruence).
                 destruct v ; try(exfalso ; congruence).
              -- rewrite <-beqAddrFalse in HbeqGlobFreesce.
                 rewrite removeDupIdentity ; try congruence.
                 destruct (lookup (CPaddr (freeslotaddr + scoffset)) (memory s0) beqAddr) eqn:HlookupFreesce
                         ; try(exfalso ; congruence).
                 destruct v ; try(exfalso ; congruence).
                 intuition.
	      - (* globalIdPD <> pd *)
			    (* similarly, we must prove the list has not changed by recomputing each
					   intermediate steps and check at that time *)
			    (* show leads to s0 -> OK *)
          assert(HlookupEq : lookup pd (memory s) beqAddr = lookup pd (memory s0) beqAddr).
          {
            rewrite <-HsEq. cbn. rewrite HbeqGlobPd. rewrite <-beqAddrFalse in HbeqGlobPd.
            rewrite removeDupIdentity ; intuition.
          }
          assert(HPDTpds0: isPDT pd s0).
          { unfold isPDT in *. rewrite <- HlookupEq. intuition. }
          specialize(Hcons0 pd freeslotaddr ). (*optionfreeslotslist freeslotslist HPDTpds0).*)
          assert(HfreeSlotsListEq : optionfreeslotslist = getFreeSlotsList pd s0 /\
	              wellFormedFreeSlotsList optionfreeslotslist <> False).
          {
            unfold getFreeSlotsList in *.
            assert(HlookupPds0: isPDT pd s0) by intuition.
            apply isPDTLookupEq in HlookupPds0. destruct HlookupPds0 as [p HlookupPds0].
            rewrite HlookupEq in *. rewrite HlookupPds0 in *.
            destruct (beqAddr (firstfreeslot p) nullAddr) eqn: HpNotNull ; try(exfalso ; congruence).
            + (* optionfreeslotslist = NIL *)
	            intuition.
            + (* optionfreeslotslist <> NIL *)
	            (* show list equality between s0 and s*)
              split.
              * rewrite HoptionfreeSlotsList. rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
                -- intro Hfirstpdeq.
	                 assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
		                   by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                   unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
                   rewrite <-beqAddrFalse in *.
                   specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p HlookupPds0 HpNotNull).
                   destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                   unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                -- unfold isBE. rewrite Hlookups0. intuition.
                -- unfold isPADDR. rewrite Hlookups0. intuition.
					    * assumption.
          }
          specialize (Hcons0 optionfreeslotslist freeslotslist HPDTpds0 HfreeSlotsListEq).
          assert(HInfreeSlot : freeslotslist = filterOptionPaddr optionfreeslotslist /\
                              In freeslotaddr freeslotslist) by intuition.
          specialize (Hcons0 HInfreeSlot HfreeSlotNotNull).
          (* dismiss all impossible values for freeslotaddr except newB *)
          destruct (beqAddr globalIdPD freeslotaddr) eqn:HbeqGlobFree; try(exfalso ; congruence).
		      * (* globalIdPD = freeslotaddr *)
					  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobFree.
					  rewrite <- HbeqGlobFree in *.
					  unfold isPDT in *.
					  unfold isFreeSlot in *.
					  destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
					  destruct v ; try(exfalso ; congruence).
		      * (* globalIdPD <> freeslotaddr *)
            rewrite <-HsEq. unfold isFreeSlot. cbn. rewrite HbeqGlobFree.
						rewrite <-beqAddrFalse in *. rewrite removeDupIdentity ; try congruence.
            unfold isFreeSlot in Hcons0.
						destruct (lookup freeslotaddr (memory s0) beqAddr) eqn:HlookfreeSlots0
                                                              ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						destruct (beqAddr globalIdPD (CPaddr (freeslotaddr + sh1offset))) eqn:HbeqGlobFreesh1
                     ; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobFreesh1.
					  rewrite <- HbeqGlobFreesh1 in *.
					  unfold isFreeSlot in *.
					  unfold isPDT in *.
            destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
            rewrite <-beqAddrFalse in HbeqGlobFreesh1.
						rewrite removeDupIdentity ; try congruence.
            destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s0) beqAddr)
                                                                  ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
            destruct (beqAddr globalIdPD (CPaddr (freeslotaddr + scoffset))) eqn:HbeqGlobFreesce
                   ; try (exfalso ; congruence).
						-- (* globalIdPD = (CPaddr (freeslotaddr + scoffset)) *)
							 rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobFreesce.
							 rewrite <- HbeqGlobFreesce in *.
							 destruct (lookup globalIdPD (memory s0) beqAddr) ; try(exfalso ; congruence).
							 destruct v ; try(exfalso ; congruence).
			      -- (* globalIdPD <> (CPaddr (freeslotaddr + scoffset)) *)
							 rewrite <- beqAddrFalse in *.
							 rewrite removeDupIdentity ; try congruence.
							 destruct (lookup (CPaddr (freeslotaddr + scoffset)) (memory s0) beqAddr) eqn:Hlookupsc
                     ; try(exfalso ; congruence).
							 destruct v ; try(exfalso ; congruence).
							 intuition.
        (* END freeSlotsListIsFreeSlot *)
      }

      assert(HDisjointFreeSlotsListss : DisjointFreeSlotsLists s).
      { (* BEGIN DisjointFreeSlotsLists s *)
        unfold DisjointFreeSlotsLists.
        intros pd1 pd2 HPDTpd1 HPDTpd2 Hpd1pd2NotEq.
        assert(Hcons0 : DisjointFreeSlotsLists s0)
                       by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold DisjointFreeSlotsLists in Hcons0.
        (* we must show all free slots list are disjoint
         check all possible values for pd1 AND pd2 in the modified state s
	         -> only possible is globalIdPD
		         1) - if pd1 = globalIdPD:
				         -> show the pd1's new free slots list is a subset of the initial free slots list
						         and that pd2's free slots list is identical at s and s0,
					         -> if they were disjoint at s0, they are still disjoint at s -> OK
		         2) - if pd1 <> globalIdPD, it is another pd, but pd2 could be globalIdPD
				         3) - if pd2 = globalIdPD:
						         same proof as with pd1
				         4) - if pd2 <> globalIdPD: prove pd1's free slots list and pd2's free slot list
						         have NOT changed in the modified state, so they are still disjoint
							         -> compute the list at each modified state and check not changed from s0 -> OK
        *)
        (* Check all values for pd1 and pd2 *)
        destruct (beqAddr globalIdPD pd1) eqn:HbeqGlobPd1; try(exfalso ; congruence).
				- (* 1) globalIdPD = pd1 *)
          rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd1.
          rewrite <- HbeqGlobPd1 in *.
          destruct (beqAddr globalIdPD pd2) eqn:HbeqGlobPd2; try(exfalso ; congruence).
          rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd2. congruence.
          (* DUP *)
          assert(Hlookuppd2Eq : lookup pd2 (memory s) beqAddr = lookup pd2 (memory s0) beqAddr).
          {
            rewrite <-HsEq. unfold isPDT. cbn. rewrite HbeqGlobPd2.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
          }
          assert(HPDTpd2Eq : isPDT pd2 s = isPDT pd2 s0).
				  { unfold isPDT. rewrite Hlookuppd2Eq. intuition. }
				  assert(HPDTpd2s0 : isPDT pd2 s0) by (rewrite HPDTpd2Eq in * ; assumption).
				  specialize(Hcons0 globalIdPD pd2 H0 HPDTpd2s0 Hpd1pd2NotEq).
          destruct Hcons0 as [listoption1 (listoption2 & (Hoptionlist1s0 & (Hwellformed1s0
                                  & (Hoptionlist2s0 & (Hwellformed2s0 & HDisjoints0)))))].
          (* Show equality for pd2's free slot list
										 so between listoption2 at s and listoption2 at s0 *)
          unfold getFreeSlotsList in Hoptionlist2s0.
				  apply isPDTLookupEq in HPDTpd2s0. destruct HPDTpd2s0 as [pd2entry Hlookuppd2s0].
				  rewrite Hlookuppd2s0 in *.
          destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					+ (* listoption2 = NIL *)
            exists listoption1.
            exists listoption2.
            assert(Hlistoption2s : getFreeSlotsList pd2 s = nil).
            {
              unfold getFreeSlotsList.
              rewrite Hlookuppd2Eq. rewrite Hpd2Null. reflexivity.
            }
            rewrite Hlistoption2s in *.
            intuition. rewrite Hoptionlist1s0. apply eq_sym.
            unfold getFreeSlotsList. rewrite Hlookups. rewrite Hlookups0.
            rewrite HnewPd. simpl.
            assert(HfreeslotsEqn:
                    getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s (nbfreeslots pdentry)
                   = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
            {
              rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
               + intro Hfirstpdeq.
	               assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
		                 by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                 unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                 specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 (firstfreeslot pdentry) pdentry
                                                                            Hlookups0 HglobNotNull).
                 destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                 unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
               + unfold isBE. rewrite Hlookups0. intuition.
               + unfold isPADDR. rewrite Hlookups0. intuition.
            }
            rewrite HfreeslotsEqn. reflexivity.
          + (* listoption2 <> NIL *)
					  (* show equality between listoption2 at s and s0 
							 + if listoption2 has NOT changed, listoption1 at s is
							 just a subset of listoption1 at s0 so they are
							 still disjoint *)
            exists listoption1.
            exists listoption2. intuition.
            * rewrite Hoptionlist1s0. apply eq_sym.
              unfold getFreeSlotsList. rewrite Hlookups. rewrite Hlookups0.
              rewrite HnewPd. simpl.
              assert(HfreeslotsEqn:
                      getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s (nbfreeslots pdentry)
                     = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
              {
                rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
                 + intro Hfirstpdeq.
	                 assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
		                   by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                   unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                   specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 (firstfreeslot pdentry) pdentry
                                                                              Hlookups0 HglobNotNull).
                   destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                   unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                 + unfold isBE. rewrite Hlookups0. intuition.
                 + unfold isPADDR. rewrite Hlookups0. intuition.
              }
              rewrite HfreeslotsEqn. reflexivity.
            * rewrite Hoptionlist2s0. apply eq_sym.
              unfold getFreeSlotsList. rewrite Hlookuppd2Eq. rewrite Hpd2Null.
              rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
               -- intro Hfirstpdeq. rewrite Hfirstpdeq in *.
                  assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
	                    by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                  unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                  specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry Hlookuppd2s0 HglobNotNull).
                  destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                  unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
               -- unfold isBE. rewrite Hlookups0. intuition.
               -- unfold isPADDR. rewrite Hlookups0. intuition.
				- (* 2) globalIdPD <> pd1 *)
				  (* similarly, we must prove optionfreeslotslist1 is strictly
						 the same at s than at s0 by recomputing each
						 intermediate steps and check at that time *)
          assert(Hlookuppd1Eq : lookup pd1 (memory s) beqAddr = lookup pd1 (memory s0) beqAddr).
          {
            rewrite <-HsEq. cbn. rewrite HbeqGlobPd1.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
          }
          assert(HPDTpd1Eq : isPDT pd1 s = isPDT pd1 s0).
			    { unfold isPDT. rewrite Hlookuppd1Eq. intuition. }
			    assert(HPDTpd1s0 : isPDT pd1 s0) by (rewrite HPDTpd1Eq in * ; assumption).
				    (* DUP of previous steps to show strict equality of listoption2
				 	   at s and s0 *)
			    destruct (beqAddr globalIdPD pd2) eqn:HbeqGlobPd2; try(exfalso ; congruence).
          + (* 2) 1. globalIdPD = pd2 *)
					  (* DUP of globalIdPD = pd1 *)
					  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd2.
					  rewrite <- HbeqGlobPd2 in *.
            (* DUP with pd1 instead of pd2 *)
            assert(Hpd1pd2NotEq' : globalIdPD <> pd1 ) by intuition.
            specialize(Hcons0 globalIdPD pd1 H0 HPDTpd1s0 Hpd1pd2NotEq').
            destruct Hcons0 as [listoption1 (listoption2 & (Hoptionlist1s0 & (Hwellformed1s0 & 
                                      (Hoptionlist2s0 & (Hwellformed2s0 & HDisjoints0)))))].
            (* Show equality between listoption2 at s and listoption2 at s0 *)
            unfold getFreeSlotsList in Hoptionlist2s0.
            apply isPDTLookupEq in HPDTpd1s0. destruct HPDTpd1s0 as [pd1entry Hlookuppd1s0].
            rewrite Hlookuppd1s0 in *.
            destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:Hpd1Null ; try(exfalso ; congruence).
            * (* listoption2 = NIL *)
              exists listoption2. exists listoption1.
              assert(Hlistoption2s : getFreeSlotsList pd1 s = nil).
              {
                unfold getFreeSlotsList.
                rewrite Hlookuppd1Eq. rewrite Hpd1Null. reflexivity.
              }
              rewrite Hlistoption2s in *. intuition.
              rewrite Hoptionlist1s0. unfold getFreeSlotsList. rewrite Hlookups. rewrite Hlookups0.
              rewrite HnewPd. simpl.
              assert(HfreeslotsEqn:
                      getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s (nbfreeslots pdentry)
                     = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
              {
                rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
                + intro Hfirstpdeq.
	                assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
		                  by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                  unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                  specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 (firstfreeslot pdentry) pdentry
                                                                             Hlookups0 HglobNotNull).
                  destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                  unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                + unfold isBE. rewrite Hlookups0. intuition.
                + unfold isPADDR. rewrite Hlookups0. intuition.
              }
              rewrite HfreeslotsEqn. reflexivity.
              subst listoption2. cbn. unfold Lib.disjoint. intuition.
            * (* listoption2 <> NIL *)
              (* show equality between listoption2 at s and s0 
								 + if listoption2 has NOT changed, listoption1 at s is
								 just a subset of listoption1 at s0 so they are
								 still disjoint *)
							exists listoption2. exists listoption1. intuition.
              -- rewrite Hoptionlist2s0. unfold getFreeSlotsList. rewrite Hlookuppd1Eq.
                 destruct(beqAddr (firstfreeslot pd1entry) nullAddr) eqn:Hff ; try(exfalso ; congruence).
                 rewrite <-HsEq. apply eq_sym. apply getFreeSlotsListRecEqPDT.
                 ++ intro Hfirstpdeq.
	                  assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
		                    by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                    unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                    specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd1 pd1entry
                                                                               Hlookuppd1s0 HglobNotNull).
                    destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                    unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                 ++ unfold isBE. rewrite Hlookups0. intuition.
                 ++ unfold isPADDR. rewrite Hlookups0. intuition.
              -- rewrite Hoptionlist1s0. unfold getFreeSlotsList. rewrite Hlookups. rewrite Hlookups0.
                 rewrite HnewPd. simpl.
                 assert(HfreeslotsEqn:
                         getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s (nbfreeslots pdentry)
                        = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
                 {
                   rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
                   + intro Hfirstpdeq.
	                   assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
		                     by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                     unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                     specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 (firstfreeslot pdentry) pdentry
                                                                                Hlookups0 HglobNotNull).
                     destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                     unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                   + unfold isBE. rewrite Hlookups0. intuition.
                   + unfold isPADDR. rewrite Hlookups0. intuition.
                 }
                 rewrite HfreeslotsEqn. reflexivity.
              -- apply Lib.disjointPermut. assumption.
          + (* 2) 2. globalIdPD <> pd2 *)
            (* show strict equality of listoption1 at s and s0
               and listoption2 at s and s0 because no list changed 
	               as only globalIdPD's free slots list changed *)
            (* DUP *)
            (* show list equality between s0 and s*)
            (* similarly, we must prove optionfreeslotslist1 
             and optionfreeslotslist2 are strictly
             the same at s than at s0 by recomputing each
             intermediate steps and check at that time *)
            assert(Hlookuppd2Eq : lookup pd2 (memory s) beqAddr = lookup pd2 (memory s0) beqAddr).
            {
              rewrite <-HsEq. cbn. rewrite HbeqGlobPd2.
              rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
            }
            assert(HPDTpd2Eq : isPDT pd2 s = isPDT pd2 s0).
            { unfold isPDT. rewrite Hlookuppd2Eq. intuition. }
            assert(HPDTpd2s0 : isPDT pd2 s0) by (rewrite HPDTpd2Eq in * ; assumption).
             (* DUP of previous steps to show strict equality of listoption2 at s and s0 *)
            specialize (Hcons0 pd1 pd2 HPDTpd1s0 HPDTpd2s0 Hpd1pd2NotEq).
            destruct Hcons0 as [listoption1 (listoption2 & (Hoptionlist1s0 & (Hwellformed1s0
                                            & (Hoptionlist2s0 & (Hwellformed2s0 & HDisjoints0)))))].
            assert(Hpdpd1NotEq : globalIdPD <> pd1) by (rewrite <- beqAddrFalse in * ; intuition).
            assert(Hpdpd2NotEq : globalIdPD <> pd2) by (rewrite <- beqAddrFalse in * ; intuition).
            assert(HDisjointpdpd1s0 : DisjointFreeSlotsLists s0)
                        by (unfold consistency in * ; unfold consistency1 in * ; intuition).
            unfold DisjointFreeSlotsLists in *.
            specialize (HDisjointpdpd1s0 globalIdPD pd1 H0 HPDTpd1s0 Hpdpd1NotEq).
            assert(HDisjointpdpd2s0 : DisjointFreeSlotsLists s0)
                        by (unfold consistency in * ; unfold consistency1 in * ; intuition).
            unfold DisjointFreeSlotsLists in *.
            specialize (HDisjointpdpd2s0 globalIdPD pd2 H0 HPDTpd2s0 Hpdpd2NotEq).
            (* Show equality between listoption1 at s and listoption1 at s0 *)
            unfold getFreeSlotsList in Hoptionlist1s0.
            apply isPDTLookupEq in HPDTpd1s0. destruct HPDTpd1s0 as [pd1entry Hlookuppd1s0].
            rewrite Hlookuppd1s0 in *.
            destruct (beqAddr (firstfreeslot pd1entry) nullAddr) eqn:Hpd1Null ; try(exfalso ; congruence).
            * (* listoption1 = NIL *)
              exists listoption1. exists listoption2.
              assert(Hlistoption1s : getFreeSlotsList pd1 s = nil).
              {
                unfold getFreeSlotsList.
                rewrite Hlookuppd1Eq. rewrite Hpd1Null. reflexivity.
              }
              rewrite Hlistoption1s in *. intuition.
              unfold getFreeSlotsList in *. rewrite Hlookuppd2Eq in *.
              apply isPDTLookupEq in HPDTpd2s0. destruct HPDTpd2s0 as [pd2entry Hlookuppd2s0].
              rewrite Hlookuppd2s0 in *.
              destruct (beqAddr (firstfreeslot pd2entry) nullAddr) eqn:HbeqFirstNull; try(exfalso ; congruence).
              -- (* (firstfreeslot pd2entry) = nullAddr *) intuition.
              -- (* (firstfreeslot pd2entry) <> nullAddr *)
                 (* show equality between listoption2 at s and s0
		               -> if listoption2 has NOT changed, they are
		               still disjoint at s because lisoption1 is NIL *)
                 rewrite Hoptionlist2s0. apply eq_sym.
                 rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
                 ++ intro Hfirstpdeq.
                    assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
	                      by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                    unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                    specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry
                                                                               Hlookuppd2s0 HglobNotNull).
                    destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                    unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                 ++ unfold isBE. rewrite Hlookups0. intuition.
                 ++ unfold isPADDR. rewrite Hlookups0. intuition.
            * (* listoption1 <> NIL *)
						  (* show equality beween listoption1 at s0 and at s
								 -> if equality, then show listoption2 has not changed either
										 -> if listoption1 and listoption2 stayed the same
												 and they were disjoint at s0, then they
												 are still disjoint at s*)
              (* specialize disjoint for pd1 and pd2 at s0 *)
              assert(HDisjointpd1pd2s0 : DisjointFreeSlotsLists s0)
                    by (unfold consistency in * ; unfold consistency1 in * ; intuition).
              unfold DisjointFreeSlotsLists in *.
              assert(HPDTpd1s0 : isPDT pd1 s0) by (unfold isPDT ; rewrite Hlookuppd1s0 ; intuition).
              specialize (HDisjointpd1pd2s0 pd1 pd2 HPDTpd1s0 HPDTpd2s0 Hpd1pd2NotEq).
              apply isPDTLookupEq in HPDTpd2s0. destruct HPDTpd2s0 as [pd2entry Hlookuppd2s0].

              destruct HDisjointpd1pd2s0 as [optionfreeslotslistpd1 (optionfreeslotslistpd2
                         & (Hoptionfreeslotslistpd1 & (Hwellformedpd1s0 & (Hoptionfreeslotslistpd2
                         & (Hwellformedpd2s0 & HDisjointpd1pd2s0)))))].
              (* we expect identical lists at s0 and s *)
              exists optionfreeslotslistpd1. exists optionfreeslotslistpd2. intuition.
              -- subst optionfreeslotslistpd1. unfold getFreeSlotsList.
                 rewrite Hlookuppd1Eq. rewrite Hlookuppd1s0.
                 assert(HfreeslotsEqn:
                         getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s (nbfreeslots pd1entry)
                        = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd1entry) s0 (nbfreeslots pd1entry)).
                 {
                   rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
                   + intro Hfirstpdeq.
	                   assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
		                     by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                     unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                     specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd1 pd1entry
                                                                               Hlookuppd1s0 HglobNotNull).
                     destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                     unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                   + unfold isBE. rewrite Hlookups0. intuition.
                   + unfold isPADDR. rewrite Hlookups0. intuition.
                 }
                 rewrite HfreeslotsEqn. reflexivity.
              -- subst optionfreeslotslistpd2. unfold getFreeSlotsList.
                 rewrite Hlookuppd2Eq. rewrite Hlookuppd2s0.
                 assert(HfreeslotsEqn:
                         getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s (nbfreeslots pd2entry)
                        = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pd2entry) s0 (nbfreeslots pd2entry)).
                 {
                   rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
                   + intro Hfirstpdeq.
	                   assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
		                     by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                     unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                     specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd2 pd2entry
                                                                               Hlookuppd2s0 HglobNotNull).
                     destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                     unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
                   + unfold isBE. rewrite Hlookups0. intuition.
                   + unfold isPADDR. rewrite Hlookups0. intuition.
                 }
                 rewrite HfreeslotsEqn. reflexivity.
        (* END DisjointFreeSlotsLists *)
      }

      assert(HinclFreeSlotsBlockEntriess : inclFreeSlotsBlockEntries s).
      { (* BEGIN inclFreeSlotsBlockEntries s *)
        unfold inclFreeSlotsBlockEntries.
        intros pd HPDT.
        assert(Hcons0 : inclFreeSlotsBlockEntries s0) 
            by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold inclFreeSlotsBlockEntries in Hcons0.
        (* we must show the free slots list is included in the ks entries list of the same pd
         check all possible values for pd in the modified state s
	         -> only possible is globalIdPD
		         1) - if pd = globalIdPD:
				         -> show the pd1's new free slots list is equal to the initial free slots list
						         and that ks entries list is identical at s and s0,
					         -> if the free slots list was included at s0,
							         then the sublist is still included at s -> OK
		         2) - if pd <> globalIdPD, it is another pd
				         -> prove pd's free slots list and ksentries list have NOT changed
						         in the modified state, so the free slots list is still included
							         -> compute the lists at each modified state and check not changed from s0 -> OK
        *)
        destruct (beqAddr globalIdPD pd) eqn:HbeqGlobPd; try(exfalso ; congruence).
		    - (* 1) globalIdPD = pd *)
          rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd.
          rewrite <- HbeqGlobPd in *.
          specialize (Hcons0 globalIdPD H0).
          (* develop getFreeSlotsList *)
          unfold getFreeSlotsList.
          rewrite Hlookups. rewrite HnewPd. simpl.
          destruct (beqAddr (firstfreeslot pdentry) nullAddr) eqn:HnewFNull.
          + (* getFreeSlots = nil *)
           apply incl_nil_l.
          + (* getFreeSlots <> nil *)
            unfold getFreeSlotsList in *. rewrite Hlookups0 in *. rewrite HnewFNull in *.
            assert(HfreeslotsEqn:
                    getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s (nbfreeslots pdentry)
                   = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot pdentry) s0 (nbfreeslots pdentry)).
            {
              rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
              + intro Hfirstpdeq.
                assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
                    by (unfold consistency in * ; unfold consistency1 in * ; intuition).
                unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
                specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 (firstfreeslot pdentry) pdentry
                                                                          Hlookups0 HglobNotNull).
                destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
                unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
              + unfold isBE. rewrite Hlookups0. intuition.
              + unfold isPADDR. rewrite Hlookups0. intuition.
            }
            assert(HKSEntriesEqn: getKSEntries globalIdPD s = getKSEntries globalIdPD s0).
            {
              rewrite <-HsEq. apply getKSEntriesEqPDT with pdentry; intuition.
            }
            rewrite HfreeslotsEqn. rewrite HKSEntriesEqn.
            assumption.
        - (* globalIdPD <> pd *)
          specialize(Hcons0 pd).
          assert(HPDT0: isPDT pd s0).
          {
            unfold isPDT in *. rewrite <-HsEq in HPDT. simpl in HPDT. rewrite HbeqGlobPd in *.
            rewrite removeDupIdentity in *; try congruence. rewrite <-beqAddrFalse in HbeqGlobPd.
            apply not_eq_sym. assumption.
          }
          specialize(Hcons0 HPDT0).
          unfold getFreeSlotsList in *. rewrite <-HsEq. simpl. rewrite HbeqGlobPd. rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity; try congruence.
          destruct (lookup pd (memory s0) beqAddr) eqn: HlookupPds0; try(apply incl_nil_l).
          destruct v; try(apply incl_nil_l).
          destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; try(apply incl_nil_l).
          rewrite HsEq.
          assert(HfreeslotsEqn:
                  getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s (nbfreeslots p)
                 = getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
          {
            rewrite <-HsEq. apply getFreeSlotsListRecEqPDT.
            + intro Hfirstpdeq.
              assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
                  by (unfold consistency in * ; unfold consistency1 in * ; intuition).
              unfold FirstFreeSlotPointerIsBEAndFreeSlot in *. rewrite <-Hfirstpdeq in *.
              specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p HlookupPds0 HglobNotNull).
              destruct HFirstFreeSlotPointerIsBEAndFreeSlots0. rewrite Hfirstpdeq in *.
              unfold isBE in *. unfold isPDT in *. rewrite Hlookups0 in *. congruence.
            + unfold isBE. rewrite Hlookups0. intuition.
            + unfold isPADDR. rewrite Hlookups0. intuition.
          }
          assert(HKSEntriesEqn: getKSEntries pd s = getKSEntries pd s0).
          {
            rewrite <-HsEq. apply getKSEntriesEqPDT with pdentry; intuition.
          }
          rewrite HfreeslotsEqn. rewrite HKSEntriesEqn.
          assumption.
        (* END inclFreeSlotsBlockEntries *)
      }

      assert(HDisjointKSEntriess : DisjointKSEntries s).
      { (* BEGIN DisjointKSEntries s *)
        unfold DisjointKSEntries.
        intros pd1 pd2 HPDTpd1 HPDTpd2 Hpd1pd2NotEq.
        assert(Hcons0 : DisjointKSEntries s0)
                       by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold DisjointKSEntries in Hcons0.
        (* we must show all KSEntries lists are disjoint
         check all possible values for pd1 AND pd2 in the modified state s
	         -> only possible is globalIdPD
		         1) - if pd1 = globalIdPD:
				         -> show the pd1's new free slots list is equal to the initial free slots list
						         and that pd2's free slots list is identical at s and s0,
					         -> if they were disjoint at s0, they are still disjoint at s -> OK
		         2) - if pd1 <> globalIdPD, it is another pd, but pd2 could be globalIdPD
				         3) - if pd2 = globalIdPD:
						         same proof as with pd1
				         4) - if pd2 <> globalIdPD: prove pd1's free slots list and pd2's free slot list
						         have NOT changed in the modified state, so they are still disjoint
							         -> compute the list at each modified state and check not changed from s0 -> OK
        *)
        (* Check all values for pd1 and pd2 *)
        destruct (beqAddr globalIdPD pd1) eqn:HbeqGlobPd1; try(exfalso ; congruence).
				- (* 1) globalIdPD = pd1 *)
          rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd1.
          rewrite <- HbeqGlobPd1 in *.
          destruct (beqAddr globalIdPD pd2) eqn:HbeqGlobPd2; try(exfalso ; congruence).
          rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd2. congruence.
          (* DUP *)
          assert(Hlookuppd2Eq : lookup pd2 (memory s) beqAddr = lookup pd2 (memory s0) beqAddr).
          {
            rewrite <-HsEq. unfold isPDT.
            cbn. rewrite HbeqGlobPd2.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
          }
          assert(HPDTpd2Eq : isPDT pd2 s = isPDT pd2 s0).
          { unfold isPDT. rewrite Hlookuppd2Eq. intuition. }
          assert(HPDTpd2s0 : isPDT pd2 s0) by (rewrite HPDTpd2Eq in * ; assumption).
				  specialize(Hcons0 globalIdPD pd2 H0 HPDTpd2s0 Hpd1pd2NotEq).
				  destruct Hcons0 as [optionentrieslist1 (optionentrieslist2 & (Hoptionlist1s0
                                                                 & (Hoptionlist2s0 & HDisjoints0)))].
				  (* Show equality for pd2's free slot list
						 so between listoption2 at s and listoption2 at s0 *)
				  unfold getKSEntries in Hoptionlist2s0.
				  apply isPDTLookupEq in HPDTpd2s0. destruct HPDTpd2s0 as [pd2entry Hlookuppd2s0].
				  rewrite Hlookuppd2s0 in *.
          destruct (beqAddr (structure pd2entry) nullAddr) eqn:Hpd2Null ; try(exfalso ; congruence).
					+ (* listoption2 = NIL *)
            exists optionentrieslist1. exists optionentrieslist2.
            assert(Hlistoption2s : getKSEntries pd2 s = nil).
            { unfold getKSEntries. rewrite Hlookuppd2Eq. rewrite Hpd2Null. reflexivity. }
            rewrite Hlistoption2s in *.
            intuition. rewrite Hoptionlist2s0 in *.
            rewrite Hoptionlist1s0. apply eq_sym. rewrite <-HsEq. apply getKSEntriesEqPDT with pdentry; intuition.
          + (* listoption2 <> NIL *)
            (* show equality between listoption2 at s and s0 
	             + if listoption2 has NOT changed, listoption1 at s is
	             just a subset of listoption1 at s0 so they are
	             still disjoint *)
            exists optionentrieslist1. exists optionentrieslist2. intuition.
            * rewrite Hoptionlist1s0. apply eq_sym. rewrite <-HsEq.
              apply getKSEntriesEqPDT with pdentry; intuition.
            * rewrite Hoptionlist2s0. unfold getKSEntries. rewrite Hlookuppd2Eq.
              rewrite Hpd2Null. apply eq_sym. rewrite <-HsEq. apply getKSEntriesAuxEqPDT.
              -- intro HeqStructGlob.
                 assert(HStructurePointerIsKSs0 : StructurePointerIsKS s0)
			                  by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		             unfold StructurePointerIsKS in *.
		             specialize (HStructurePointerIsKSs0 pd2 pd2entry Hlookuppd2s0).
		             rewrite <- beqAddrFalse in Hpd2Null.
		             unfold isKS in *. rewrite HeqStructGlob in *.
		             rewrite Hlookups0 in *. intuition.
              -- assumption.
				- (* 2) globalIdPD <> pd1 *)
          (* similarly, we must prove optionfreeslotslist1 is strictly
	           the same at s than at s0 by recomputing each
	           intermediate steps and check at that time *)
          assert(Hlookuppd1Eq : lookup pd1 (memory s) beqAddr = lookup pd1 (memory s0) beqAddr).
          {
            rewrite <-HsEq. cbn. rewrite HbeqGlobPd1.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
          }
          assert(HPDTpd1Eq : isPDT pd1 s = isPDT pd1 s0).
          { unfold isPDT. rewrite Hlookuppd1Eq. intuition. }
          assert(HPDTpd1s0 : isPDT pd1 s0) by (rewrite HPDTpd1Eq in * ; assumption).
           (* DUP of previous steps to show strict equality of listoption2
	           at s and s0 *)
          destruct (beqAddr globalIdPD pd2) eqn:HbeqGlobPd2; try(exfalso ; congruence).
          + (* 2) 1. globalIdPD = pd2 *)
            rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd2.
            rewrite <- HbeqGlobPd2 in *.
						(* DUP with pd1 instead of pd2 *)
					  assert(Hpd1pd2NotEq': globalIdPD <> pd1 ) by intuition.
            assert(HPDTpd2Eq : isPDT pd1 s = isPDT pd1 s0).
            { unfold isPDT. rewrite Hlookuppd1Eq. intuition. }
				    specialize(Hcons0 globalIdPD pd1 H0 HPDTpd1s0 Hpd1pd2NotEq').
				    destruct Hcons0 as [optionentrieslist1 (optionentrieslist2 & (Hoptionlist1s0
                                                                 & (Hoptionlist2s0 & HDisjoints0)))].
				    (* Show equality between listoption1 at s and listoption1 at s0 *)
            exists optionentrieslist2.
            exists optionentrieslist1.
					  unfold getKSEntries at 1.
					  rewrite Hlookuppd1Eq.
					  unfold getKSEntries in Hoptionlist2s0.
					  apply isPDTLookupEq in HPDTpd1s0. destruct HPDTpd1s0 as [pd1entry Hlookuppd1s0].
					  rewrite Hlookuppd1s0 in *.
            destruct (beqAddr (structure pd1entry) nullAddr) eqn:Hpd1Null ; try(exfalso ; congruence).
            * (* listoption2 = NIL *)
						  rewrite Hoptionlist2s0 in *.
						  intuition.
						  rewrite Hoptionlist1s0. apply eq_sym. rewrite <-HsEq. apply getKSEntriesEqPDT with pdentry; intuition.
						  apply Lib.disjointPermut. intuition.
            * (* listoption2 <> NIL *)
              (* show equality between listoption2 at s and s0 
	               + if listoption2 has NOT changed, listoption1 at s is
	               just a subset of listoption1 at s0 so they are
	               still disjoint *)
              (* listoption2 didn't change *)
						  assert(HKSEntries : getKSEntries globalIdPD s0 = getKSEntries globalIdPD s).
						  { apply eq_sym. rewrite <-HsEq. apply getKSEntriesEqPDT with pdentry; intuition. }
              subst optionentrieslist1.
						  intuition.
              rewrite Hoptionlist2s0. apply eq_sym. rewrite <-HsEq. apply getKSEntriesAuxEqPDT.
              -- intro HeqStructGlob.
                 assert(HStructurePointerIsKSs0 : StructurePointerIsKS s0)
			                  by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		             unfold StructurePointerIsKS in *.
		             specialize (HStructurePointerIsKSs0 pd1 pd1entry Hlookuppd1s0).
		             rewrite <- beqAddrFalse in Hpd1Null.
		             unfold isKS in *. rewrite HeqStructGlob in *.
		             rewrite Hlookups0 in *. intuition.
              -- assumption.
              -- apply Lib.disjointPermut. intuition.
          + (* 2) 2. globalIdPD <> pd2 *)
					  (* show strict equality of listoption1 at s and s0
							 and listoption2 at s and s0 because no list changed 
								 as only pdinsertion's free slots list changed *)
					  (* DUP *)
					  (* show list equality between s0 and s*)
					  (* similarly, we must prove optionfreeslotslist1 
						  and optionfreeslotslist2 are strictly
						  the same at s than at s0 by recomputing each
						  intermediate steps and check at that time *)
					  assert(Hlookuppd2Eq : lookup pd2 (memory s) beqAddr = lookup pd2 (memory s0) beqAddr).
					  {
              rewrite <-HsEq. cbn. rewrite HbeqGlobPd2.
              rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
					  }
					  assert(HPDTpd2Eq : isPDT pd2 s = isPDT pd2 s0).
					  { unfold isPDT. rewrite Hlookuppd2Eq. intuition. }
					  assert(HPDTpd2s0 : isPDT pd2 s0) by (rewrite HPDTpd2Eq in * ; assumption).
						 (* DUP of previous steps to show strict equality of listoption2
							 at s and s0 *)
					  specialize (Hcons0 pd1 pd2 HPDTpd1s0 HPDTpd2s0 Hpd1pd2NotEq).
					  destruct Hcons0 as [optionentrieslist1 (optionentrieslist2 & (Hoptionlist1s0
                                                                & (Hoptionlist2s0 & HDisjoints0)))].
					  assert(Hpdpd1NotEq : globalIdPD <> pd1) by (rewrite <- beqAddrFalse in * ; intuition).
					  assert(Hpdpd2NotEq : globalIdPD <> pd2) by (rewrite <- beqAddrFalse in * ; intuition).
            exists optionentrieslist1.
					  exists optionentrieslist2.
					  (* Show equality between listoption1 at s and listoption1 at s0 *)
					  unfold getKSEntries at 1.
					  rewrite Hlookuppd1Eq. unfold getKSEntries in Hoptionlist1s0.
            unfold isPDT in HPDTpd1s0.
            destruct (lookup pd1 (memory s0) beqAddr) eqn:HlookupPd1s0; try(exfalso ; congruence).
            destruct v; try(exfalso ; congruence).
					  destruct (beqAddr (structure p) nullAddr) eqn:Hpd1Null ; try(exfalso ; congruence).
					  * (* listoption1 = NIL *)
              intuition.
						  subst optionentrieslist2. apply eq_sym. rewrite <-HsEq.
              apply getKSEntriesEqPDT with pdentry; intuition.
					  * (* listoption1 <> NIL *)
						  (* show equality beween listoption1 at s0 and at s
								 -> if equality, then show listoption2 has not changed either
										 -> if listoption1 and listoption2 stayed the same
												 and they were disjoint at s0, then they
												 are still disjoint at s*)
              (* specialize disjoint for pd1 and pd2 at s0 *)
              intuition.
              -- subst optionentrieslist1. apply eq_sym. rewrite <-HsEq. apply getKSEntriesAuxEqPDT; intuition.
                 assert(HStructurePointerIsKSs0 : StructurePointerIsKS s0)
			                  by (unfold consistency in * ; unfold consistency1 in * ; intuition).
		             unfold StructurePointerIsKS in *.
		             specialize (HStructurePointerIsKSs0 pd1 p HlookupPd1s0).
		             rewrite <- beqAddrFalse in Hpd1Null.
		             unfold isKS in *. rewrite H20 in *.
		             rewrite Hlookups0 in *. intuition.
              -- subst optionentrieslist2. apply eq_sym. rewrite <-HsEq.
                 apply getKSEntriesEqPDT with pdentry; intuition.
        (* END DisjointKSEntries *)
      }

      assert(HnoDupPartitionTrees : noDupPartitionTree s).
      { (* BEGIN noDupPartitionTree s *)
        (* equality of list getPartitions already proven so immediate proof *)
        assert(Hcons0 : noDupPartitionTree s0)
	        by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold noDupPartitionTree.
        assert(HgetPartitionspdEq : getPartitions multiplexer s = getPartitions multiplexer s0)
	        by intuition.
        rewrite HgetPartitionspdEq. intuition.
        (* END noDupPartitionTree *)
      }

      assert(HmultiIsPDT : multiplexerIsPDT s).
      { (* BEGIN multiplexerIsPDT s *)
        (* already proven by propagation *)
        unfold multiplexerIsPDT.
        intuition.
        (* END multiplexerIsPDT *)
      }

		  assert(HmappedparentEq : forall partition : paddr,
														  partition <> globalIdPD ->
														  isPDT partition s0 ->
														   getMappedPaddr partition s = getMappedPaddr partition s0)
			  by intuition.

		  assert(HconfigpaddrEq : forall partition : paddr,
		      partition <> globalIdPD ->
		      isPDT partition s0 ->
		      getConfigPaddr partition s = getConfigPaddr partition s0) by intuition.

		  assert(HusedpaddrEq : forall partition : paddr,
		  partition <> globalIdPD ->
		  isPDT partition s0 ->
		  getUsedPaddr partition s = getUsedPaddr partition s0).
		  {
			  intros part HpartidpdNotEq HPDTparts0.
			  unfold getUsedPaddr. f_equal.
			  apply HconfigpaddrEq ; intuition.
			  apply HmappedparentEq ; intuition.
		  }

      assert(HgetPartitionspdEq : getPartitions multiplexer s = getPartitions multiplexer s0)
           by intuition.

		  assert(HpartNotIn : (forall partition : paddr,
												  (partition = globalIdPD -> False) ->
												  isPDT partition s0 ->
												  getChildren partition s = getChildren partition s0))
			  by intuition.

		  assert(HAmappedblocksEq : forall partition : paddr,
				  partition <> globalIdPD ->
				  isPDT partition s0 ->
				  (getAccessibleMappedBlocks partition s) = getAccessibleMappedBlocks partition s0) by intuition.

		  assert(HmappedblocksEq : forall partition : paddr,
				  partition <> globalIdPD ->
				  isPDT partition s0 ->
				  (getMappedBlocks partition s) = getMappedBlocks partition s0) by intuition.

      assert(HchildrenEq: forall partition : paddr,
           partition <> globalIdPD ->
           isPDT partition s0 -> getChildren partition s = getChildren partition s0) by intuition.

		  assert(Hidpdchildmapped: getMappedPaddr globalIdPD s = getMappedPaddr globalIdPD s0) by intuition.

      assert(HisParents : isParent s).
      { (* BEGIN isParent s *)
        (* equality of lists getPartitions and getChildren for any partition already proven
	       + no change of pdentry so immediate proof *)
	      assert(Hcons0 : isParent s0) by (unfold consistency in * ; unfold consistency1 in * ; intuition).
	      unfold isParent.
	      intros pd parent HparentInPartTree HpartChild.
	      assert(HpdPDT : isPDT pd s).
	      {
		      apply childrenArePDT with parent; intuition.
	      }
	      unfold pdentryParent.
	      apply isPDTLookupEq in HpdPDT. destruct HpdPDT as [partpdentry Hlookuppds].
	      rewrite Hlookuppds.
				assert(HPDTEq: isPDT parent s = isPDT parent s0).
				{
          unfold isPDT.
          rewrite <-HsEq. simpl.
		      destruct (beqAddr globalIdPD parent) eqn:HbeqGlobParent; try(exfalso ; congruence).
		      - (* globalIdPD = parent *)
				     rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParent.
				     subst parent.
				     rewrite Hlookups0.
				     trivial.
		      - (* globalIdPD <> parent *)
				    rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
				}
				assert(HPDTparent : isPDT parent s).
				{ eapply partitionsArePDT ; intuition. }
				destruct (beqAddr globalIdPD pd) eqn:HbeqGlobPd; try(exfalso ; congruence).
        - (* globalIdPD = pd *)
          rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd.
          subst pd.
          assert(HpdentryEq : partpdentry = newpdentry).
          {
           rewrite Hlookuppds in *. inversion Hlookups. trivial.
          }
          rewrite HpdentryEq.
          subst newpdentry. cbn.
          assert(HparentInPartTrees0 : In parent (getPartitions multiplexer s0))
              by (rewrite HgetPartitionspdEq in * ; assumption). (* after lists propagation*)
          assert(HpdparentNotEq : parent <> globalIdPD).
          { eapply childparentNotEq with s; intuition. }
          assert(HgetChildrenEq : getChildren parent s = getChildren parent s0).
          {
            rewrite HPDTEq in *.
            eapply HpartNotIn ; intuition.
          }
          assert(HpartChilds0 : In globalIdPD (getChildren parent s0))
                  by (rewrite HgetChildrenEq in * ; assumption). (* after lists propagation*)
          unfold isParent in *.
          specialize (Hcons0 globalIdPD parent HparentInPartTrees0 HpartChilds0).
          unfold pdentryParent in *.
          rewrite Hlookups0 in *.
          assumption.
        - (* globalIdPD <> pd *)
          assert(HlookuppsEq : lookup pd (memory s) beqAddr = lookup pd (memory s0) beqAddr).
          {
            rewrite <-HsEq. simpl. rewrite HbeqGlobPd.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
          }
          assert(HparentInPartTrees0 : In parent (getPartitions multiplexer s0))
                by (rewrite HgetPartitionspdEq in * ; intuition). (* after lists propagation*)
          assert(HgetChildrenEq : getChildren parent s = getChildren parent s0).
          {
            (* 2 cases: either parent is globalIdPD or it is not *)
            destruct (beqAddr globalIdPD parent) eqn:HbeqGlobParent.
            - (* globalIdPD = parent *)
	            rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParent.
	            subst parent.
	            assert(HgetChildrenEq : getChildren globalIdPD s = getChildren globalIdPD s0)
			            by intuition.
	            rewrite HgetChildrenEq. reflexivity.
            - (* pdinsertion <> parent *)
	            rewrite <- beqAddrFalse in *.
	            rewrite HPDTEq in *.
	            eapply HpartNotIn ; intuition.
          }

          assert(HpartChilds0 : In pd (getChildren parent s0))
           by (rewrite HgetChildrenEq in * ; assumption).
          unfold isParent in *.
          specialize (Hcons0 pd parent HparentInPartTrees0 HpartChilds0).
          unfold pdentryParent in *.
          rewrite HlookuppsEq in *.
          rewrite Hlookuppds in *.
          assumption.
        (* END isParent *)
      }

      assert(HisChilds : isChild s).
      { (* BEGIN isChild s *)
        (* equality of lists getPartitions and getChildren for any partition already proven
	        + no change of pdentry so immediate proof *)
        assert(Hcons0 : isChild s0)
	        by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold isChild.
        intros pd parent HparentInPartTree Hparententry.
        assert(HpdPDT : isPDT pd s).
        {
	        apply partitionsArePDT ; intuition.
        }
        apply isPDTLookupEq in HpdPDT. destruct HpdPDT as [partpdentry Hlookuppds].
        assert(HpdInPartTrees0 : In pd (getPartitions multiplexer s0))
	              by (rewrite HgetPartitionspdEq in * ; assumption).
        assert(HPDTEq: isPDT parent s = isPDT parent s0).
        {
				  unfold isPDT. rewrite <-HsEq. simpl.
				  destruct (beqAddr globalIdPD parent) eqn:HbeqGlobParent; try(exfalso ; congruence).
				  - (* globalIdPD = parent *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParent.
						subst parent.
						rewrite Hlookups0.
						trivial.
				  - (* globalIdPD <> parent *)
						rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
			  }
			  destruct (beqAddr globalIdPD pd) eqn:HbeqGlobPd; try(exfalso ; congruence).
			  + (* globalIdPD = pd *)
					rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPd.
					subst pd.
					assert(HparententryEq : pdentryParent globalIdPD parent s
                                = pdentryParent globalIdPD parent s0).
					{
					  unfold pdentryParent.
						rewrite Hlookups. rewrite HnewPd. simpl.
						rewrite Hlookups0.
						reflexivity.
					}
          assert(Hparententrys0 : pdentryParent globalIdPD parent s0)
						 by (rewrite HparententryEq in * ; assumption).
					specialize (Hcons0 globalIdPD parent HpdInPartTrees0 Hparententrys0).
					assert(HPDTparents : isPDT parent s0).
					{
						unfold getChildren in *.
						unfold isPDT.
						destruct (lookup parent (memory s0) beqAddr) eqn:Hlookupparent ; intuition.
						destruct v ; intuition.
					}
					(* 2 cases: either parent is globalIdPD or it is not *)
					destruct (beqAddr globalIdPD parent) eqn:HbeqGlobParent.
					* (* globalIdPD = parent *)
					  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParent.
					  subst parent.
						assert(HgetChildrenEq : getChildren globalIdPD s = getChildren globalIdPD s0)
										 by intuition.
						rewrite HgetChildrenEq. intuition.
					* (* globalIdPD <> parent *)
						rewrite <- beqAddrFalse in *.
						assert(HparentEq : getChildren parent s = getChildren parent s0).
						{ eapply HpartNotIn ; intuition. }
						rewrite HparentEq in *. intuition.
	      + (* globalIdPD <> pd *)
					assert(HlookuppsEq : lookup pd (memory s) beqAddr = lookup pd (memory s0) beqAddr).
					{
					  rewrite <-HsEq. simpl. rewrite HbeqGlobPd.
						rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
					}
					assert(HparententryEq : pdentryParent pd parent s = pdentryParent pd parent s0).
					{
					  unfold pdentryParent.
						rewrite HlookuppsEq.
						reflexivity.
					}
					assert(Hparententrys0 : pdentryParent pd parent s0)
						 by (rewrite HparententryEq in * ; assumption).
					specialize (Hcons0 pd parent HpdInPartTrees0 Hparententrys0).
					assert(HPDTparents : isPDT parent s0).
					{
					  unfold getChildren in *.
						unfold isPDT.
						destruct (lookup parent (memory s0) beqAddr) eqn:Hlookupparent ; intuition.
						destruct v ; intuition.
					}
				  assert(HgetChildrenEq : getChildren parent s = getChildren parent s0).
					{
						(* 2 cases: either parent is globalIdPD or it is not *)
						destruct (beqAddr globalIdPD parent) eqn:HbeqGlobParent.
						- (* globalIdPD = parent *)
							rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParent.
							subst parent.
							assert(HgetChildrenEq : getChildren globalIdPD s = getChildren globalIdPD s0)
									 by intuition.
							rewrite HgetChildrenEq. reflexivity.
						- (* globalIdPD <> parent *)
							rewrite <- beqAddrFalse in *.
							eapply HpartNotIn ; intuition.
					}
					rewrite HgetChildrenEq in *.
					assumption.
        (* END isChild *)
      }


      assert(HnoDupKSEntriesLists : noDupKSEntriesList s).
      { (* BEGIN noDupKSEntriesList s *)
        assert(Hcons0 : noDupKSEntriesList s0)
	         by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold noDupKSEntriesList.
        intros part HPDTpds.
	      destruct (beqAddr globalIdPD part) eqn:HbeqGlobPart ; try(exfalso ; congruence).
	      - (* globalIdPD =  part *)
		      rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPart.
		      rewrite <- HbeqGlobPart in *.
		      assert(HKSEntriesEq : (getKSEntries globalIdPD s) = (getKSEntries globalIdPD s0)).
		      {
			      rewrite <-HsEq. apply getKSEntriesEqPDT with pdentry; intuition.
		      }
		      rewrite HKSEntriesEq.
		      unfold noDupKSEntriesList in *.
		      assert(HPDTpdinsertions0 : isPDT globalIdPD s0) by intuition.
		      specialize (Hcons0 globalIdPD HPDTpdinsertions0).
		      assumption.
	      - (* globalIdPD <> part *)
		      assert(HPDTEq : isPDT part s = isPDT part s0).
		      {
		        unfold isPDT in *. simpl.
			      rewrite <-HsEq. simpl. rewrite HbeqGlobPart.
			      rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
		      }
		      assert(HKSEntriesEq : (getKSEntries part s) = (getKSEntries part s0)).
		      {
			      assert(HKSEntriesEqNotInPart : forall partition : paddr,
																		       (partition = globalIdPD -> False) ->
																		       isPDT partition s0 ->
																		       getKSEntries partition s = getKSEntries partition s0)
				            by intuition.
			      rewrite beqAddrSym in HbeqGlobPart.
			      rewrite <- beqAddrFalse in HbeqGlobPart.
			      rewrite HPDTEq in HPDTpds.
			      specialize (HKSEntriesEqNotInPart part HbeqGlobPart HPDTpds).
			      assumption.
		      }
		      rewrite HKSEntriesEq.
		      unfold noDupKSEntriesList in *.
		      rewrite HPDTEq in HPDTpds.
		      specialize (Hcons0 part HPDTpds).
		      assumption.
        (* END noDupKSEntriesList *)
      }

      assert(HnoDupMappedBlocksLists : noDupMappedBlocksList s).
      { (* BEGIN noDupMappedBlocksList s *)
        (* DUP *)
        unfold noDupMappedBlocksList.
        unfold getMappedBlocks.
        intros part HPDTparts.
        eapply NoDupListNoDupFilterPresent ; intuition.
        (* END noDupMappedBlocksList *)
      }

      assert(HwellFormedBlock : wellFormedBlock s).
      { (* BEGIN wellFormedBlock s*)
        unfold wellFormedBlock.
        intros block blockstart blockend HPflags HStarts Hends.
        (* Check all possible values for block
           -> only possible is newBlockEntryAddr
           2) if block == newBlockEntryAddr :
               -> block params = blockstart and blockend and
		               we know blockstart < blockend -> OK
           3) if block <> newBlockEntryAddr :
               - relates to another bentry than newBlockentryAddr
	               that was not modified
	               (either in the same structure or another)
               -> leads to s0 -> OK
        *)
        (* 1) lookup block s in hypothesis: eliminate impossible values for block *)
        unfold bentryPFlag in *.
        unfold bentryStartAddr in *.
        unfold bentryEndAddr in *.
        destruct (beqAddr globalIdPD block) eqn:HbeqGlobBlock ; try(exfalso ; congruence).
        * (* globalIdPD = block *)
          rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobBlock.
          rewrite <- HbeqGlobBlock in *.
          unfold isPDT in *.
          destruct (lookup globalIdPD (memory s) beqAddr) ; try(exfalso ; congruence).
          destruct v ; try(exfalso ; congruence).
        * (* globalIdPD <> block *)
          (* leads to s0 *)
          assert(Hcons0 : wellFormedBlock s0)
             by (unfold consistency in * ; unfold consistency1 in *; intuition).
          unfold wellFormedBlock in *.
          assert(HBEeq : lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
          {
            rewrite <-HsEq. cbn. rewrite HbeqGlobBlock.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity; intuition.
          }
          rewrite HBEeq in *.
          specialize(Hcons0 block blockstart blockend HPflags HStarts Hends).
          trivial.
        (* END wellFormedBlock *)
      }

      assert(HMPUFromAccessibleBlocks : MPUFromAccessibleBlocks s).
      { (* BEGIN MPUFromAccessibleBlocks s *)
        (* check all possible values for partition in the modified state s
         -> only possible is globalIdPD
        1) if partition == globalIdPD :
           - MPU list not changed
           - accessible list augmented
             -> MPU list still in initial accessible list -> OK
        2) if pdentryaddr <> globalIdPD :
           - relates to another PD than globalIdPD
             - MPU and accessible lists not changed
               -> leads to s0 -> OK
        *)
        assert(Hcons0 : MPUFromAccessibleBlocks s0)
         by (unfold consistency in * ; unfold consistency1 in * ; intuition).
        unfold MPUFromAccessibleBlocks in *.
        intros partition block MPU HMPU HblockInMPU HblockNotNull.
        unfold pdentryMPU in *.
        destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPartition; try(exfalso ; congruence).
        - (* globalIdPD = partition *)
          rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPartition.
          rewrite <- HbeqGlobPartition in *.

          rewrite Hlookups in *. rewrite HMPU in *. rewrite HnewPd in *. simpl in *.
          (* block is either
             - equal to blockToEnableAddr -> ?
             - in the MPU at state s0 -> the property still holds *)
          assert (HMPU0: pdentryMPU globalIdPD (ADT.MPU pdentry) s0).
          { unfold pdentryMPU. rewrite Hlookups0. reflexivity. }
          unfold MPUFromAccessibleBlocks in *. specialize(Hcons0 globalIdPD block (ADT.MPU pdentry) HMPU0).

          (* The accessible mapped blocks are unchanged *)
          assert(HmappedBlocksEq: getAccessibleMappedBlocks globalIdPD s
                                 = getAccessibleMappedBlocks globalIdPD s0) by intuition.
          rewrite HmappedBlocksEq.

          destruct (beqAddr block blockToEnableAddr) eqn:HbeqBlockBlockToEnable.
          + (* block = blockToEnableAddr *)
            rewrite <-beqAddrTrue in HbeqBlockBlockToEnable.
            rewrite HbeqBlockBlockToEnable in *. apply HblockProps; intuition.
          + (* block <> blockToEnableAddr *)
            rewrite <-beqAddrFalse in HbeqBlockBlockToEnable.
            assert(HblockInMPUs0: In block (ADT.MPU pdentry)).
            { apply addElemGeneralCase with blockToEnableAddr MPURegionNb; intuition. }
            specialize (Hcons0 HblockInMPUs0 HblockNotNull).
            assumption.
        - (* globalIdPD <> partition *)
					 (* DUP *)
          assert(HMPUEq : pdentryMPU partition MPU s = pdentryMPU partition MPU s0).
          { 	unfold pdentryMPU.
            rewrite <-HsEq. cbn. rewrite HbeqGlobPartition.
            rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
          }
          unfold pdentryMPU in HMPUEq.
          rewrite HMPUEq in *.
          specialize(Hcons0 partition block MPU HMPU HblockInMPU HblockNotNull).
          assert(HMappedBlocksEq : (forall partition : paddr,
                (partition = globalIdPD -> False) ->
                isPDT partition s0 ->
                getAccessibleMappedBlocks partition s = getAccessibleMappedBlocks partition s0))
           by intuition.
          destruct (lookup partition (memory s) beqAddr) eqn:Hlookuppd ; try(exfalso ; congruence).
          destruct v ; try (exfalso ; congruence).
          rewrite beqAddrSym in HbeqGlobPartition.
          rewrite <- beqAddrFalse in HbeqGlobPartition.
          assert(HPDTparts0 : isPDT partition s0).
          {
            unfold isPDT.
            destruct (lookup partition (memory s0) beqAddr) ; try (exfalso ; congruence).
            destruct v ; try (exfalso ; congruence).
            trivial.
          }
          specialize (HMappedBlocksEq partition HbeqGlobPartition HPDTparts0).
          rewrite HMappedBlocksEq.
          trivial.
        (* END MPUFromAccessibleBlocks *)
      }

      assert(noDupUsedPaddrList : noDupUsedPaddrList s).
      { (* BEGIN noDupUsedPaddrList s *)
		    assert(Hcons0 : noDupUsedPaddrList s0)
			        by (unfold consistency in * ; unfold consistency2 in * ; intuition).
		    unfold noDupUsedPaddrList.
		    intros part HPDTpds.
		    unfold getUsedPaddr.
		    assert(HPDTEq : isPDT part s = isPDT part s0).
		    {
			    unfold isPDT in *. simpl.
			    rewrite <-HsEq. simpl.
					destruct (beqAddr globalIdPD part) eqn:HbeqGlobPart ; try(exfalso ; congruence).
					- (* globalIdPD = part *)
						rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPart.
						rewrite HbeqGlobPart in *.
						rewrite Hlookups0 in *.
						trivial.
					- (* globalIdPD <> part *)
							rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
        }
		    assert(HconfigPadrEq : getConfigPaddr part s = getConfigPaddr part s0).
		    {
			    destruct (beqAddr globalIdPD part) eqn:HbeqGlobPart ; try(exfalso ; congruence).
			    - (* globalIdPD =  part *)
				    rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPart.
				    rewrite <- HbeqGlobPart in *.
				    intuition.
			    - (* globalIdPD <> part *)
				    rewrite <- beqAddrFalse in *.
				    intuition.
				    assert(HconfigEq : forall partition : paddr,
									    (partition = globalIdPD -> False) ->
									    isPDT partition s0 ->
									    getConfigPaddr partition s = getConfigPaddr partition s0)
						    by intuition.
				    rewrite HPDTEq in *.
				    eapply HconfigEq ; intuition.
		    }
		    apply Lib.NoDupSplitInclIff.
		    unfold noDupUsedPaddrList in *.
		    rewrite HPDTEq in *.
		    specialize (Hcons0 part HPDTpds).
		    unfold getUsedPaddr in *.
		    rewrite Lib.NoDupSplitInclIff in Hcons0.
		    assert(Hcons0' : noDupUsedPaddrList s0)
			          by (unfold consistency in * ; unfold consistency2 in * ; intuition).
		    specialize (Hcons0' part HPDTpds).
		    unfold getUsedPaddr in *.
		    rewrite Lib.NoDupSplitInclIff in Hcons0'.
		    split. split.
		    - (* getConfigPaddr *)
			    rewrite HconfigPadrEq in *. intuition.
		    - (* getMappedPaddr *)
			    + destruct (beqAddr globalIdPD part) eqn:HbeqGlobPart ; try(exfalso ; congruence).
			      * (* globalIdPD = part *)
					    rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPart.
					    rewrite <- HbeqGlobPart in *.
              assert(HmappedPaddrEq: getMappedPaddr globalIdPD s = getMappedPaddr globalIdPD s0) by intuition.
              rewrite HmappedPaddrEq. intuition.
            * (* globalIdPD = part *)
					    rewrite <- DependentTypeLemmas.beqAddrFalse in HbeqGlobPart.
					    assert(HconfigmappedEq : (forall partition : paddr,
									     (partition = globalIdPD -> False) ->
									     isPDT partition s0 ->
									     getMappedPaddr partition s = getMappedPaddr partition s0))
						    by intuition.
              assert(HmappedPaddrEq: getMappedPaddr part s = getMappedPaddr part s0).
              { eapply HconfigmappedEq ; intuition. }
					    rewrite HmappedPaddrEq. intuition.
		    - (* Lib.disjoint (getConfigPaddr part s) (getMappedPaddr part s) *)
			    destruct (beqAddr globalIdPD part) eqn:HbeqGlobPart ; try(exfalso ; congruence).
				  + (* globalIdPD = part *)
					  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobPart.
					  rewrite <- HbeqGlobPart in *.
					  rewrite HconfigPadrEq.
					  intros addr HaddrInConfigs0.
					  rewrite Hidpdchildmapped.
					  intro HaddrInMappeds.
            assert(Hdisjoint: Lib.disjoint (getConfigPaddr globalIdPD s0) (getMappedPaddr globalIdPD s0))
                  by intuition.
            unfold Lib.disjoint in Hdisjoint.
            specialize (Hdisjoint addr HaddrInConfigs0).
					  contradiction.
				  + (* globalIdPD <> part *)
						rewrite HconfigPadrEq.
						rewrite <- beqAddrFalse in *.
						assert(HconfigmappedEq : (forall partition : paddr,
										 (partition = globalIdPD -> False) ->
										 isPDT partition s0 ->
										 getMappedPaddr partition s = getMappedPaddr partition s0))
							by intuition.
						assert(HmappedEq : getMappedPaddr part s = getMappedPaddr part s0).
						{ eapply HconfigmappedEq ; intuition. }
						rewrite HmappedEq. intuition.
        (* END noDupUsedPaddrList *)
      }

      assert(HaccessibleChildPaddrIsAccessibleIntoParents : accessibleChildPaddrIsAccessibleIntoParent s).
	    { (* BEGIN accessibleChildPaddrIsAccessibleIntoParent s *)
        assert(Hcons0: accessibleChildPaddrIsAccessibleIntoParent s0)
	        by (unfold consistency in * ; unfold consistency2 in * ; intuition).
        unfold accessibleChildPaddrIsAccessibleIntoParent in *.
        intros parent child addr HparentInPartTree HchildInChildList HaddrInAccessibleMappedChilds.
        assert(HPDTparents : isPDT parent s).
        {
	        apply partitionsArePDT ; intuition.
        }
		    assert(HPDTchilds : isPDT child s).
		    {
			    eapply childrenArePDT with parent ; intuition.
		    }
		    assert(HaccessiblemappedEq : getAccessibleMappedPaddr globalIdPD s
                                  = getAccessibleMappedPaddr globalIdPD s0)
            by intuition.
		    rewrite HgetPartitionspdEq in *.
		    assert(HsameAccessibleMapped: getAccessibleMappedBlocks globalIdPD s
                                    = getAccessibleMappedBlocks globalIdPD s0)
				    by intuition.
        destruct (beqAddr child globalIdPD) eqn:HbeqChildGlob ; try(exfalso ; congruence).
        - (* child = globalIdPD *)
          rewrite <-beqAddrTrue in HbeqChildGlob. rewrite HbeqChildGlob in *.
          rewrite HsameAccessibleMapped in *.
				  assert(HparentidpdNotEq : parent <> globalIdPD). (* child not currentPart *)
				  {
					  eapply childparentNotEq with s0; intuition.
					  unfold consistency in * ; unfold consistency1 in * ; intuition.
					  assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
					  { destruct (beqAddr parent globalIdPD) eqn:HbeqParentGlob ; try(exfalso ; congruence).
						  - (* parent = globalIdPDChild *)
							  (* even in the false case, the children did not change for any partition *)
							  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqParentGlob.
							  rewrite HbeqParentGlob in *.
							  intuition.
						  - (* parent <> globalIdPD *)
							  assert(HChildrenEqNotInParts0 : forall partition : paddr,
												  (partition = globalIdPD -> False) ->
												  isPDT partition s0 ->
												  getChildren partition s = getChildren partition s0)
								  by intuition.
							  rewrite <- beqAddrFalse in *.
							  eapply HChildrenEqNotInParts0 ; intuition.
							  assert(HlookuppsEq : lookup parent (memory s) beqAddr = lookup parent (memory s0) beqAddr).
							  {
								  (* check all values *)
								  apply isPDTLookupEq in HPDTparents. destruct HPDTparents as [parententry Hlookupparents].
								  destruct (beqAddr globalIdPD parent) eqn:HbeqGlobParent; try(exfalso ; congruence).
								  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParent.
								  rewrite HbeqGlobParent in *. congruence.
								  (* globalIdPD <> parent *)
								  rewrite <-HsEq. cbn. rewrite HbeqGlobParent.
								  rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
							  }
							  unfold isPDT in *.
							  rewrite HlookuppsEq in *.
							  destruct (lookup parent (memory s0) beqAddr) ; intuition.
					  }
					  rewrite HchildrenparentEq in *. trivial.
				  }
				  assert(HPDTparents0 : isPDT parent s0).
				  { eapply partitionsArePDT ; intuition.
					  unfold consistency in * ; unfold consistency1 in * ; intuition.
				  }
				  assert(HchildrenparentEq : getChildren parent s = getChildren parent s0).
				  {
            assert(HChildrenEqNotInParts0 : forall partition : paddr,
												  (partition = globalIdPD -> False) ->
												  isPDT partition s0 ->
												  getChildren partition s = getChildren partition s0)
								  by intuition.
					  eapply HChildrenEqNotInParts0 ; intuition.
				  }
				  rewrite HchildrenparentEq in *.
				  assert(HAmappedparentEq : getAccessibleMappedPaddr parent s = getAccessibleMappedPaddr parent s0).
				  {
					  assert(HAMappedPaddrEqNotInParts0 : (forall partition : paddr,
											  (partition = globalIdPD -> False) ->
											  isPDT partition s0 ->
											  getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0))
						  by intuition.
					  eapply HAMappedPaddrEqNotInParts0 ; intuition.
				  }
				  rewrite HAmappedparentEq in *.
				  rewrite HaccessiblemappedEq in *.
          specialize(Hcons0 parent globalIdPD addr HparentInPartTree HchildInChildList 
                                                                  HaddrInAccessibleMappedChilds).
          assumption.
        - (* child <> globalIdPD *)
			    destruct (beqAddr parent globalIdPD) eqn:HbeqParentGlob ; try(exfalso ; congruence).
			    + (* parent = globalIdPDChild *)
					  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqParentGlob.
					  rewrite HbeqParentGlob in *.
            assert(HpdchildrenEq : getChildren globalIdPD s = getChildren globalIdPD s0) by intuition.
					  rewrite HpdchildrenEq in *.
					  assert(HNoDupPartTree : noDupPartitionTree s0)
							  by (unfold consistency in * ; unfold consistency1 in * ; intuition). (* consistency s*)
					  assert(HglobalChildNotEq : child <> globalIdPD).
					  { apply not_eq_sym. eapply childparentNotEq with s0 ; try (rewrite HparentEq in *) ; intuition. }
						specialize (Hcons0 globalIdPD child addr HparentInPartTree HchildInChildList).
						rewrite HaccessiblemappedEq.
						assert(HaccessibleMappedEq : getAccessibleMappedPaddr child s = getAccessibleMappedPaddr child s0).
            {
              assert (H': forall partition : paddr,
                        (partition = globalIdPD -> False) ->
                        isPDT partition s0 ->
                        getAccessibleMappedPaddr partition s = getAccessibleMappedPaddr partition s0)
                  by intuition.
              specialize (H' child HglobalChildNotEq).
						  assert(HPDTEq : isPDT child s = isPDT child s0).
						  {
							  unfold isPDT.
							  rewrite <-HsEq. simpl.
                assert (HbeqGlobChild: beqAddr globalIdPD child = false).
                { rewrite <-beqAddrFalse. intuition. }
                rewrite HbeqGlobChild.
							  rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
						  }
              rewrite HPDTEq in *. specialize (H' HPDTchilds). assumption.
            }
						rewrite HaccessibleMappedEq in *.
            specialize (Hcons0 HaddrInAccessibleMappedChilds). assumption.
			    + (* parent <> globalIdPDChild *)
						rewrite <- beqAddrFalse in *.
						assert(HPDTparents0 : isPDT parent s0).
						{
              unfold consistency in * ; unfold consistency1 in * ; eapply partitionsArePDT ; intuition.
						}
						assert(HchildrenparentEq : getChildren parent s = getChildren parent s0) by intuition.
						assert(Hchild : isPDT child s0).
						{
              unfold consistency in * ; unfold consistency1 in * ; eapply childrenArePDT with parent ; intuition.
							rewrite HchildrenparentEq in * ; intuition.
						}
						assert(HAccessibleMappedparentEq : getAccessibleMappedPaddr parent s =
																			getAccessibleMappedPaddr parent s0)
							by intuition.
						rewrite HAccessibleMappedparentEq in *.
						rewrite HchildrenparentEq in*.
						specialize (Hcons0 parent child addr HparentInPartTree HchildInChildList).
						assert(HAccessibleMappedchildEq : getAccessibleMappedPaddr child s =
																			getAccessibleMappedPaddr child s0)
							by intuition.
						rewrite HAccessibleMappedchildEq in *. intuition.
				(* END accessibleChildPaddrIsAccessibleIntoParent *)
      }

	    assert(HsharedBlockPointsToChilds : sharedBlockPointsToChild s).
	    { (* BEGIN sharedBlockPointsToChild s *)
			  unfold sharedBlockPointsToChild.
			  intros parent child addr parentblock sh1entryaddr HparentPartTree HchildIsChild
						   HaddrIsUsed HaddrInParentBlock HParentBlockIsMapped Hsh1entryAddr.
			  assert(HsharedToChilds0 : sharedBlockPointsToChild s0)
					  by (unfold consistency in * ; unfold consistency2 in * ; intuition). (* consistency2 s0 *)
			  destruct (beqAddr parent globalIdPD) eqn:HbeqParentGlob ; try(exfalso ; congruence).
        assert(HpdchildrenEq : getChildren globalIdPD s = getChildren globalIdPD s0) by intuition.
			  - (* parent = globalIdPD *)
				  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqParentGlob.
				  rewrite HbeqParentGlob in *.
				  assert(HglobalChildNotEq : globalIdPD <> child)
					      by (eapply childparentNotEq with s; intuition).
				  assert(HChildGlobalNotEq : child <> globalIdPD)
					      by (intro Hf ; apply eq_sym in Hf ; intuition).
				  assert(HusedblocksEq : getUsedPaddr child s = getUsedPaddr child s0).
				  {
            unfold consistency in * ; unfold consistency1 in *.
            eapply HusedpaddrEq ; intuition.
					  eapply childrenArePDT with globalIdPD ; intuition.
					  rewrite HpdchildrenEq in *. intuition.
				  }
				  rewrite HusedblocksEq in *. rewrite HpdchildrenEq in *. rewrite HgetPartitionspdEq in *.
				  specialize (HsharedToChilds0 globalIdPD child addr parentblock sh1entryaddr
														  HparentPartTree HchildIsChild HaddrIsUsed).
					assert(HBEparentblock : isBE parentblock s).
					{ eapply addrInBlockisBE with addr ; intuition. }
					assert(HlookupparentEq : lookup parentblock (memory s) beqAddr
                                  = lookup parentblock (memory s0) beqAddr).
					{ (* check all values *)
						apply isBELookupEq in HBEparentblock.
						destruct HBEparentblock as [parentblockentry Hlookupparents].
						destruct (beqAddr globalIdPD parentblock) eqn:HbeqGlobParentBlock; try(exfalso ; congruence).
						rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParentBlock.
						rewrite HbeqGlobParentBlock in *. congruence.
						(* globalIdPD <> parent *)
						rewrite <-HsEq.	cbn. rewrite HbeqGlobParentBlock.
						rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
					} (*no entry change so s0*)
					unfold sh1entryAddr. unfold sh1entryPDchild. unfold sh1entryPDflag.

					assert(HaddrInBlocks0 : In addr (getAllPaddrAux (parentblock::nil) s0)).
					{
						simpl.
						unfold getAllPaddrAux in HaddrInParentBlock.
						rewrite HlookupparentEq in *.
						assumption.
					} (* block not changed*)
          assert(HpdchildMappedBlocks: getMappedBlocks globalIdPD s = getMappedBlocks globalIdPD s0)
                  by intuition.
          rewrite HpdchildMappedBlocks in HParentBlockIsMapped. (*HpdchildMappedBlocks*)
					assert(Hlookupsh1Eq : lookup (CPaddr (parentblock + sh1offset)) (memory s) beqAddr =
										lookup (CPaddr (parentblock + sh1offset)) (memory s0) beqAddr).
					{
							assert(HSHEparents : isSHE (CPaddr (parentblock + sh1offset)) s).
							{
								unfold wellFormedFstShadowIfBlockEntry in *.
								specialize (HwellFormedFstShadowIfBlockEntrys parentblock
																															HBEparentblock).
								assumption.
							}
							apply isSHELookupEq in HSHEparents.
							destruct HSHEparents as [parentsh1entry Hlookupparentsh1].
							(* check all values *)
							apply isBELookupEq in HBEparentblock.
							destruct HBEparentblock as [parentblockentry Hlookupparents].
							rewrite <-HsEq. cbn.
							destruct (beqAddr globalIdPD (CPaddr (parentblock + sh1offset))) eqn:HbeqGlobParentSh1
                                                                        ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParentSh1.
							rewrite HbeqGlobParentSh1 in *. congruence.
							(* globalIdPD <> (CPaddr (parentblock + sh1offset)) *)
							rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
					} (* only possible match is sh1eaddr -> bts -> not in globalIdPD *)
					rewrite Hlookupsh1Eq in *.
					unfold sh1entryAddr in *. rewrite HlookupparentEq in *.
					specialize (HsharedToChilds0 HaddrInBlocks0 HParentBlockIsMapped).
					apply HsharedToChilds0 ; trivial.
			  - (* parent <> globalIdPD *)
				  destruct (beqAddr child globalIdPD) eqn:HbeqChildGlob ; try(exfalso ; congruence).
				  + (* child = globalIdPD *)
					  rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqChildGlob.
					  rewrite HbeqChildGlob in *.
					  rewrite <- beqAddrFalse in *.
						assert(HBEparentblock : isBE parentblock s).
						{ eapply addrInBlockisBE with addr ; intuition. }
						assert(HlookupparentEq : lookup parentblock (memory s) beqAddr =
																	lookup parentblock (memory s0) beqAddr).
						{ (* DUP *)
							(* check all values *)
							apply isBELookupEq in HBEparentblock.
							destruct HBEparentblock as [parentblockentry Hlookupparents].
							destruct (beqAddr globalIdPD parentblock) eqn:HbeqGlobParentBlock; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParentBlock.
							rewrite HbeqGlobParentBlock in *. congruence.
							(* globalIdPD <> parent *)
							rewrite <-HsEq. cbn. rewrite HbeqGlobParentBlock.
							rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
						} (*no entry change so s0*)
						unfold sh1entryAddr in *. unfold sh1entryPDchild. unfold sh1entryPDflag.
						rewrite HlookupparentEq in *.
						assert(HaddrInBlocks0 : In addr (getAllPaddrAux (parentblock::nil) s0)).
						{
							simpl.
							unfold getAllPaddrAux in HaddrInParentBlock.
							rewrite HlookupparentEq in *.
							assumption.
						} (* block not changed*)
						assert(HaddrInBlockisBE : isBE parentblock s0).
						{
							apply addrInBlockisBE with addr ; intuition.
						}
						apply isBELookupEq in HaddrInBlockisBE.
						destruct HaddrInBlockisBE as [bentryparent Hlookupparents0].
						assert(Hsh1Eq : lookup (CPaddr (parentblock + sh1offset)) (memory s) beqAddr =
										lookup (CPaddr (parentblock + sh1offset)) (memory s0) beqAddr).
						{ (* DUP *)
							assert(HSHEparents : isSHE (CPaddr (parentblock + sh1offset)) s).
							{
								unfold wellFormedFstShadowIfBlockEntry in *.
								specialize (HwellFormedFstShadowIfBlockEntrys parentblock
																															HBEparentblock).
								assumption.
							}
							apply isSHELookupEq in HSHEparents.
							destruct HSHEparents as [parentsh1entry Hlookupparentsh1].
							(* check all values *)
							rewrite <-HsEq.	cbn.
							destruct (beqAddr globalIdPD (CPaddr (parentblock + sh1offset))) eqn:HbeqGlobParentSh1
                                                                      ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParentSh1.
							rewrite HbeqGlobParentSh1 in *. congruence.
							(* globalIdPD <> (CPaddr (parentblock + sh1offset)) *)
							rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
						}
						rewrite Hsh1Eq.
						rewrite HgetPartitionspdEq in *.
						assert(isPDT parent s0).
						{ unfold consistency in * ; unfold consistency1 in * ; eapply partitionsArePDT ; intuition. }
						assert(HparentchildrenEq : getChildren parent s = getChildren parent s0)
							    by (apply HpartNotIn ; intuition).
						rewrite HparentchildrenEq in *.
						assert(HparentMappedBlocksEq : (getMappedBlocks parent s) = getMappedBlocks parent s0)
							    by (apply HmappedblocksEq ; intuition).
						rewrite HparentMappedBlocksEq in *.
            assert(HusedPaddrEq: getUsedPaddr globalIdPD s = getUsedPaddr globalIdPD s0).
            {
              unfold getUsedPaddr.
              assert(HconfigEq: getConfigPaddr globalIdPD s = getConfigPaddr globalIdPD s0) by intuition.
              assert(HmappedEq: getMappedPaddr globalIdPD s = getMappedPaddr globalIdPD s0) by intuition.
              rewrite HconfigEq. rewrite HmappedEq. reflexivity.
            }
            rewrite HusedPaddrEq in HaddrIsUsed.
            specialize (HsharedToChilds0 parent globalIdPD addr parentblock sh1entryaddr
																				HparentPartTree HchildIsChild
																				HaddrIsUsed HaddrInBlocks0
																				HParentBlockIsMapped Hsh1entryAddr).
						rewrite Hlookupparents0 in *.
						unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
						subst sh1entryaddr. assumption.
				  + (* child <> globalIdPD *)
						assert(HBEparentblock : isBE parentblock s).
						{ eapply addrInBlockisBE with addr ; intuition. }
						assert(HlookupparentEq : lookup parentblock (memory s) beqAddr
                                  = lookup parentblock (memory s0) beqAddr).
						{ (* DUP *)
							(* check all values *)
							apply isBELookupEq in HBEparentblock.
							destruct HBEparentblock as [parentblockentry Hlookupparents].
							destruct (beqAddr globalIdPD parentblock) eqn:HbeqGlobParentBlock; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParentBlock.
							rewrite HbeqGlobParentBlock in *. congruence.
							(* globalIdPDChild <> parent *)
							rewrite <-HsEq. cbn. rewrite HbeqGlobParentBlock.
							rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
						} (*no entry change so s0*)
						unfold sh1entryAddr in *. unfold sh1entryPDchild. unfold sh1entryPDflag.
						rewrite HlookupparentEq in *.
						assert(HaddrInBlocks0 : In addr (getAllPaddrAux (parentblock::nil) s0)).
						{
							simpl.
							unfold getAllPaddrAux in HaddrInParentBlock.
							rewrite HlookupparentEq in *.
							assumption.
						} (* block not changed*)
						assert(Hsh1Eq : lookup (CPaddr (parentblock + sh1offset)) (memory s) beqAddr =
													lookup (CPaddr (parentblock + sh1offset)) (memory s0) beqAddr).
						{ (* DUP *)
							assert(HSHEparents : isSHE (CPaddr (parentblock + sh1offset)) s).
							{
								unfold wellFormedFstShadowIfBlockEntry in *.
								specialize (HwellFormedFstShadowIfBlockEntrys parentblock HBEparentblock).
								assumption.
							}
							apply isSHELookupEq in HSHEparents.
							destruct HSHEparents as [parentsh1entry Hlookupparentsh1].
							(* check all values *)
							apply isBELookupEq in HBEparentblock.
							destruct HBEparentblock as [parentblockentry Hlookupparents].
							rewrite <-HsEq.	cbn.
							destruct (beqAddr globalIdPD (CPaddr (parentblock + sh1offset))) eqn:HbeqGlobParentBlockSh1
                                                                              ; try(exfalso ; congruence).
							rewrite <- DependentTypeLemmas.beqAddrTrue in HbeqGlobParentBlockSh1.
							rewrite HbeqGlobParentBlockSh1 in *. congruence.
							(* globalIdPD <> (CPaddr (parentblock + sh1offset)) *)
							rewrite <- beqAddrFalse in *. rewrite removeDupIdentity ; intuition.
						}
						rewrite Hsh1Eq. rewrite HgetPartitionspdEq in *.
						rewrite <- beqAddrFalse in *.
						assert(isPDT parent s0).
						{ unfold consistency in * ; unfold consistency1 in * ; eapply partitionsArePDT ; intuition. }
						assert(HparentchildrenEq : getChildren parent s = getChildren parent s0)
								by (apply HchildrenEq ; intuition).
						rewrite HparentchildrenEq in *.
						assert(HparentMappedBlocks : (getMappedBlocks parent s) = getMappedBlocks parent s0).
						{	eapply HmappedblocksEq ; intuition. }
						rewrite HparentMappedBlocks in *.
						assert(HchildusedBlocksEq : (getUsedPaddr child s) = getUsedPaddr child s0).
						{
              unfold consistency in * ; unfold consistency1 in * ; eapply HusedpaddrEq ; intuition.
							eapply childrenArePDT with parent ; intuition.
						}
						rewrite HchildusedBlocksEq in *.
						specialize (HsharedToChilds0 parent child addr parentblock sh1entryaddr
												HparentPartTree HchildIsChild HaddrIsUsed HaddrInBlocks0
												HParentBlockIsMapped Hsh1entryAddr).
						unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
						destruct (lookup parentblock (memory s0) beqAddr) ; try(exfalso ; congruence).
						destruct v ; try(exfalso ; congruence).
						subst sh1entryaddr. assumption.
        (* END sharedBlockPointsToChild *)
      }

      assert(HNbFreeSlotsISNbFreeSlotsInList: NbFreeSlotsISNbFreeSlotsInList s).
      { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
        assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold NbFreeSlotsISNbFreeSlotsInList in *. intros pd nbfreeslots HisPDTPd HnbFreeSlots.
        destruct (beqAddr globalIdPD pd) eqn:HbeqGlobPd.
        - (* globalIdPD = pd *)
          rewrite <-beqAddrTrue in HbeqGlobPd. rewrite <-HbeqGlobPd in *.
          assert(HnbFreeSlotsEq: pdentryNbFreeSlots globalIdPD nbfreeslots s
                                = pdentryNbFreeSlots globalIdPD nbfreeslots s0).
          {
            unfold pdentryNbFreeSlots. rewrite <-HsEq. simpl. rewrite InternalLemmas.beqAddrTrue.
            rewrite Hlookups0. simpl. f_equal.
          }
          rewrite HnbFreeSlotsEq in HnbFreeSlots.
          specialize(Hcons0 globalIdPD nbfreeslots H0 HnbFreeSlots). destruct Hcons0 as [optionfreeslotslist Hcons0].
          exists optionfreeslotslist. intuition. subst optionfreeslotslist. rewrite <-HsEq. apply eq_sym.
          unfold getFreeSlotsList. simpl. rewrite InternalLemmas.beqAddrTrue. simpl. rewrite Hlookups0.
          destruct (beqAddr (firstfreeslot pdentry) nullAddr); try(reflexivity).
          apply getFreeSlotsListRecEqPDT.
          + intro HfirstFreeIsGlob.
            assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
			              by (unfold consistency in * ; unfold consistency1 in * ; intuition).
            unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
            specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 globalIdPD pdentry Hlookups0).
            destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
            * intro HfirstfreeNull.
              assert(HnullAddrExistss0 : nullAddrExists s0)
                      by (unfold consistency in * ; unfold consistency1 in * ; intuition).
              unfold nullAddrExists in *. unfold isPADDR in *.
              rewrite HfirstfreeNull in *. destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso ; congruence).
            * rewrite HfirstFreeIsGlob in *. unfold isBE in *.
              destruct (lookup globalIdPD (memory s0) beqAddr) ; try (exfalso ; congruence).
              destruct v ; try(exfalso ; congruence).
          + unfold isBE. rewrite Hlookups0. intuition.
          + unfold isPADDR. rewrite Hlookups0. intuition.
        - (* globalIdPD <> pd *)
          assert(HisPDTEq: isPDT pd s = isPDT pd s0).
          {
            rewrite <-HsEq. unfold isPDT. simpl. rewrite HbeqGlobPd. rewrite <-beqAddrFalse in HbeqGlobPd.
            rewrite removeDupIdentity; intuition.
          }
          rewrite HisPDTEq in HisPDTPd.
          assert(HnbFreeSlotsEq: pdentryNbFreeSlots pd nbfreeslots s
                                = pdentryNbFreeSlots pd nbfreeslots s0).
          {
            unfold pdentryNbFreeSlots. rewrite <-HsEq. simpl. rewrite HbeqGlobPd.
            rewrite <-beqAddrFalse in HbeqGlobPd. rewrite removeDupIdentity; intuition.
          }
          rewrite HnbFreeSlotsEq in HnbFreeSlots. specialize(Hcons0 pd nbfreeslots HisPDTPd HnbFreeSlots).
          destruct Hcons0 as [optionfreeslotslist Hcons0]. exists optionfreeslotslist. intuition.
          subst optionfreeslotslist. rewrite <-HsEq. apply eq_sym. unfold getFreeSlotsList. simpl.
          rewrite HbeqGlobPd. simpl. rewrite <-beqAddrFalse in HbeqGlobPd.
          rewrite removeDupIdentity; intuition. assert(isPDT pd s0) by intuition. unfold isPDT in HisPDTPd.
          destruct (lookup pd (memory s0) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
          destruct v; try(exfalso; congruence).
          destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HfirstIsNull; try(reflexivity).
          apply getFreeSlotsListRecEqPDT.
          + intro HfirstFreeIsGlob.
            assert(HFirstFreeSlotPointerIsBEAndFreeSlots0 : FirstFreeSlotPointerIsBEAndFreeSlot s0)
			              by (unfold consistency in * ; unfold consistency1 in * ; intuition).
            unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
            specialize (HFirstFreeSlotPointerIsBEAndFreeSlots0 pd p HlookupPd).
            destruct HFirstFreeSlotPointerIsBEAndFreeSlots0.
            * intro HfirstfreeNull.
              assert(HnullAddrExistss0 : nullAddrExists s0)
                      by (unfold consistency in * ; unfold consistency1 in * ; intuition).
              unfold nullAddrExists in *. unfold isPADDR in *.
              rewrite HfirstfreeNull in *. destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
            * rewrite HfirstFreeIsGlob in *. unfold isBE in *.
              destruct (lookup globalIdPD (memory s0) beqAddr); try (exfalso ; congruence).
              destruct v; try(exfalso ; congruence).
          + unfold isBE. rewrite Hlookups0. intuition.
          + unfold isPADDR. rewrite Hlookups0. intuition.
        (* END NbFreeSlotsISNbFreeSlotsInList *)
      }

      assert(HparentOfPartitionIsPartition: parentOfPartitionIsPartition s).
      { (* BEGIN parentOfPartitionIsPartition s *)
        assert(Hcons0: parentOfPartitionIsPartition s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
        unfold parentOfPartitionIsPartition in *. intros partition entry Hlookup.
        destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
        - (* globalIdPD = partition *)
          rewrite <-beqAddrTrue in HbeqGlobPart. rewrite HbeqGlobPart in *.
          assert(HparentEq: parent pdentry = parent entry).
          {
            rewrite Hlookups in Hlookup. injection Hlookup as HentryEq. rewrite <-HentryEq. rewrite HnewPd.
            simpl. reflexivity.
          }
          destruct (beqAddr partition (parent entry)) eqn:HbeqPartParent.
          + (* partition = parent entry *)
            rewrite <-beqAddrTrue in HbeqPartParent. rewrite <-HbeqPartParent in *.
            specialize(Hcons0 partition pdentry Hlookups0). destruct Hcons0 as [HparentIsPart HparentOfRoot]. split.
            * intro HpartNotRoot. exists entry. assumption.
            * intro HpartIsRoot. specialize(HparentOfRoot HpartIsRoot).
              rewrite HparentEq in HparentOfRoot. assumption.
          + (* partition <> parent entry *)
            specialize(Hcons0 partition pdentry Hlookups0). destruct Hcons0 as [HparentIsPart HparentOfRoot]. split.
            * intro HpartNotRoot. specialize(HparentIsPart HpartNotRoot).
              destruct HparentIsPart as [parentEntry HlookupParent].
              exists parentEntry. rewrite <-HlookupParent.
              rewrite <-HsEq. simpl. rewrite HbeqPartParent.
              rewrite <-beqAddrFalse in HbeqPartParent.
              rewrite removeDupIdentity; intuition.
              rewrite Hlookups in *. injection Hlookup. intro HentryEq. rewrite <-HentryEq.
              rewrite HnewPd. simpl. reflexivity.
            * intro HpartIsRoot. specialize(HparentOfRoot HpartIsRoot).
              rewrite HparentEq in HparentOfRoot. assumption.
        - (* globalIdPD <> partition *)
          assert(HlookupEq: lookup partition (memory s) beqAddr = lookup partition (memory s0) beqAddr).
          {
            rewrite <-HsEq. simpl. rewrite HbeqGlobPart.
            rewrite <-beqAddrFalse in HbeqGlobPart. rewrite removeDupIdentity; intuition.
          }
          rewrite HlookupEq in Hlookup.
          destruct (beqAddr globalIdPD (parent entry)) eqn:HbeqGlobParent.
          + (* partition = parent entry *)
            rewrite <-beqAddrTrue in HbeqGlobParent. rewrite <-HbeqGlobParent in *. split.
            * intro. exists newpdentry. assumption.
            * intro HpartIsRoot. specialize(Hcons0 partition entry Hlookup).
              destruct Hcons0 as [HparentIsPart HparentOfRoot]. specialize(HparentOfRoot HpartIsRoot).
              rewrite HbeqGlobParent. assumption.
          + (* partition <> parent entry *)
            specialize(Hcons0 partition entry Hlookup).
            destruct Hcons0 as [HparentIsPart HparentOfRoot]. split.
            * intro HpartNotRoot. specialize(HparentIsPart HpartNotRoot).
              destruct HparentIsPart as [parentEntry HlookupParent]. exists parentEntry.
              rewrite <-HsEq. simpl. rewrite HbeqGlobParent.
              rewrite <-beqAddrFalse in HbeqGlobParent. rewrite removeDupIdentity; intuition.
            * intro HpartIsRoot. specialize(HparentOfRoot HpartIsRoot). assumption.
        (* END parentOfPartitionIsPartition *)
      }

      intuition.

    * (* Final state *)
      exists pdentry. exists newpdentry. destruct H3 as [s1 (Hstate & Hprops)].
      assert(HsEq: s1 = s) by (subst; reflexivity). subst s1. rewrite HsEq in *. intuition.
      -- (* pdentryNbFreeSlots *)
         assert(HnbFree: pdentryNbFreeSlots globalIdPD (nbfreeslots newpdentry) s).
         { apply lookupPDEntryNbFreeSlots. assumption. }
         rewrite HnewPd in HnbFree. simpl in HnbFree. assumption.
      -- (* isPDT *)
         unfold isPDT. rewrite Hlookups. trivial.
      -- unfold isPDT. rewrite <-HsEq. simpl.
         destruct (beqAddr globalIdPD partition) eqn:HbeqGlobPart.
         ++ rewrite <-beqAddrTrue in HbeqGlobPart. rewrite <-HbeqGlobPart. rewrite Hlookups0. reflexivity.
         ++ rewrite <-beqAddrFalse in HbeqGlobPart.
            rewrite removeDupIdentity. reflexivity. apply not_eq_sym. assumption.
Qed.