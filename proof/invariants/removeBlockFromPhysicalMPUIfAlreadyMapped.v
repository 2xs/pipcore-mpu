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

(*Temporary*)
Require Import replaceBlockInPhysicalMPU Invariants.

Require Import Lia Classical List.

Module WP := WeakestPreconditions.

Lemma findBlockIdxInPhysicalMPU (defaultidx: index) (globalIdPD blockToEnableAddr currentPart: paddr)
  (P: state -> Prop):
{{ fun s : state =>
   P s /\ consistency s /\
   currentPart = currentPartition s /\ globalIdPD <> nullAddr /\
   isPDT globalIdPD s }}
MAL.findBlockIdxInPhysicalMPU globalIdPD blockToEnableAddr defaultidx
{{ fun _ (s: state) => (((P s /\ consistency s)
                         /\ currentPart = currentPartition s)
                        /\ globalIdPD <> nullAddr)
                       /\ isPDT globalIdPD s }}.
Proof.
unfold MAL.findBlockIdxInPhysicalMPU. eapply bindRev.
- eapply weaken. eapply readPDMPU.
  intros s Hprops. simpl. split.
  + eapply Hprops.
  + intuition.
- intro realMPU. eapply bindRev.
  + eapply Index.zero.
  + intro zero. simpl. eapply weaken. eapply ret.
    intros s Hprops. intuition.
Qed.

(* Comes from Internal -> TODO put in InternalLemmas? *)
Lemma enableBlockInMPU (globalIdPD blockToEnableAddr: paddr) (MPURegionNb: index) (P: state -> Prop) :
{{ fun (s : state) =>
    P s /\ consistency s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s
   /\ (blockToEnableAddr <> nullAddr
      -> (In blockToEnableAddr (getAccessibleMappedBlocks globalIdPD s))) }}
Internal.enableBlockInMPU globalIdPD blockToEnableAddr MPURegionNb 
{{fun (enabled: bool) (s : state) =>
   exists s0, P s0 /\ consistency s0 /\ isPDT globalIdPD s0
    /\ consistency s
    /\ globalIdPD <> nullAddr
    /\ isPDT globalIdPD s0
    /\ isPDT globalIdPD s
    /\ exists pdentry : PDTable,
      (lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry) 
       /\ getKSEntries globalIdPD s = getKSEntries globalIdPD s0
       /\ (	isPDT multiplexer s
		       /\
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
       /\ (is_true enabled -> (exists pdentry1: PDTable,
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
          /\ lookup globalIdPD (memory s) beqAddr = Some (PDT pdentry1) /\
          pdentry1 = {|     structure := structure pdentry;
			               firstfreeslot := firstfreeslot pdentry;
			               nbfreeslots := nbfreeslots pdentry;
			               nbprepare := nbprepare pdentry;
			               parent := parent pdentry;
			               MPU := addElementAt MPURegionNb blockToEnableAddr (MPU pdentry) nullAddr;
								             vidtAddr := vidtAddr pdentry |}
          (* propagate new properties *)
          /\ pdentryNbFreeSlots globalIdPD (nbfreeslots pdentry) s
       ))
       /\ (~ is_true enabled -> s = s0)
    )
}}.
Proof.
unfold enableBlockInMPU. eapply bindRev.
- eapply Index.zero.
- intro zero. eapply bindRev.
  + eapply weaken. eapply Invariants.Index.ltb.
    simpl. intros s H. apply H.
  + intro isBelowZero. eapply bindRev.
    * eapply getMPURegionsNb.
    * intro maxMPURegions. eapply bindRev.
      -- eapply weaken. eapply Invariants.Index.leb.
         simpl. intros s H. eapply H. (*?*)
      -- intro isAboveMPURegionsNb. destruct (isBelowZero || isAboveMPURegionsNb)%bool eqn: Ha.
         { (** case (isBelowZero || isAboveMPURegionsNb) = true **)
           eapply weaken. eapply WP.ret.
           intros s HQ. simpl. exists s. intuition.
           assert(Hlookups: exists entry:PDTable, lookup globalIdPD (memory s) beqAddr = Some (PDT entry))
                by (apply isPDTLookupEq; assumption).
           destruct Hlookups as [pdentry Hlookups]. exists pdentry.
           split. assumption. split. reflexivity. split. intuition.
           unfold consistency in *; unfold consistency1 in *; intuition.
           split. intro. reflexivity. split. unfold is_true. intro. exfalso; congruence.
           intro. reflexivity.
         }
         { (** case (isBelowZero || isAboveMPURegionsNb) = false **)
           eapply bindRev.
           ++ (** MAL.replaceBlockInPhysicalMPU **)
              eapply weaken.
              eapply replaceBlockInPhysicalMPU.
              intros s Hprops. simpl. split. eapply Hprops. intuition.
              ** destruct isAboveMPURegionsNb eqn:HisAbove.
                 --- rewrite Bool.orb_true_r in Ha.
                     assert(true <> false) by (apply Bool.diff_true_false; trivial). contradiction.
                 --- apply eq_sym. eapply H0.
              ** unfold CIndex in *. assert(MPURegionsNb <= maxIdx) by (apply MPURegionsNbBelowMaxIdx).
                 destruct (Compare_dec.le_dec MPURegionsNb maxIdx); try(lia). subst maxMPURegions. simpl.
                 lia.
           ++ intro. eapply weaken. eapply WP.ret.
              intros s Hprops. simpl. destruct Hprops as [s0 Hprops]. exists s0. intuition.
              destruct H9 as [pdentry1 Hprops]. destruct Hprops as [pdentry2 Hprops]. intuition.
              destruct H9 as [pdentry1 Hprops]. destruct Hprops as [pdentry2 Hprops]. exists pdentry1.
              destruct Hprops as (Hs & HlookupGlobs0 & HlookupGlobs & Hprops).
              split. assumption. split.
              {
                rewrite Hs.
                apply getKSEntriesEqPDT with pdentry1; unfold consistency in *; unfold consistency1 in *;
                  intuition.
              }
              split. intuition. split. intuition. split. intro. exists pdentry2. intuition.
              unfold is_true. intro. exfalso; congruence.
         }
Qed.

(* Comes from Internal -> TODO put in InternalLemmas? *)
Lemma enableBlockInMPUconsist1 (globalIdPD blockToEnableAddr: paddr) (MPURegionNb: index) (P: state -> Prop) :
{{ fun (s : state) =>
    P s /\ consistency1 s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s
   /\ (blockToEnableAddr <> nullAddr
      -> (In blockToEnableAddr (getAccessibleMappedBlocks globalIdPD s))) }}
Internal.enableBlockInMPU globalIdPD blockToEnableAddr MPURegionNb 
{{fun (enabled: bool) (s : state) =>
   exists s0, P s0 /\ consistency1 s0 /\ isPDT globalIdPD s0
    /\ consistency1 s
    /\ globalIdPD <> nullAddr
    /\ isPDT globalIdPD s0
    /\ isPDT globalIdPD s
    /\ exists pdentry : PDTable,
      (lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry) 
       /\ getKSEntries globalIdPD s = getKSEntries globalIdPD s0
       /\ (	isPDT multiplexer s
		       /\
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
       /\ (is_true enabled -> (exists pdentry1: PDTable,
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
          /\ lookup globalIdPD (memory s) beqAddr = Some (PDT pdentry1) /\
          pdentry1 = {|     structure := structure pdentry;
			               firstfreeslot := firstfreeslot pdentry;
			               nbfreeslots := nbfreeslots pdentry;
			               nbprepare := nbprepare pdentry;
			               parent := parent pdentry;
			               MPU := addElementAt MPURegionNb blockToEnableAddr (MPU pdentry) nullAddr;
								             vidtAddr := vidtAddr pdentry |}
          (* propagate new properties *)
          /\ pdentryNbFreeSlots globalIdPD (nbfreeslots pdentry) s
       ))
       /\ (~ is_true enabled -> s = s0)
    )
}}.
Proof.
unfold Internal.enableBlockInMPU. eapply bindRev.
- eapply Index.zero.
- intro zero. eapply bindRev.
  + eapply weaken. eapply Invariants.Index.ltb.
    simpl. intros s H. apply H.
  + intro isBelowZero. eapply bindRev.
    * eapply getMPURegionsNb.
    * intro maxMPURegions. eapply bindRev.
      -- eapply weaken. eapply Invariants.Index.leb.
         simpl. intros s H. eapply H. (*?*)
      -- intro isAboveMPURegionsNb. destruct (isBelowZero || isAboveMPURegionsNb)%bool eqn: Ha.
         { (** case (isBelowZero || isAboveMPURegionsNb) = true **)
           eapply weaken. eapply WP.ret.
           intros s HQ. simpl. exists s. intuition.
           assert(Hlookups: exists entry:PDTable, lookup globalIdPD (memory s) beqAddr = Some (PDT entry))
                by (apply isPDTLookupEq; assumption).
           destruct Hlookups as [pdentry Hlookups]. exists pdentry.
           split. assumption. split. reflexivity. split. intuition. unfold consistency1 in *; intuition.
           split. intro. reflexivity. split. unfold is_true. intro. exfalso; congruence.
           intro. reflexivity.
         }
         { (** case (isBelowZero || isAboveMPURegionsNb) = false **)
           eapply bindRev.
           ++ (** MAL.replaceBlockInPhysicalMPU **)
              eapply weaken.
              eapply replaceBlockInPhysicalMPUconsist1.
              intros s Hprops. simpl. split. eapply Hprops. intuition.
              ** destruct isAboveMPURegionsNb eqn:HisAbove.
                 --- rewrite Bool.orb_true_r in Ha.
                     assert(true <> false) by (apply Bool.diff_true_false; trivial). contradiction.
                 --- apply eq_sym. eapply H0.
              ** subst maxMPURegions. unfold CIndex.
                 assert(MPURegionsNb <= maxIdx) by (apply MPURegionsNbBelowMaxIdx).
                 destruct (Compare_dec.le_dec MPURegionsNb maxIdx); try(lia). simpl. lia.
           ++ intro. eapply weaken. eapply WP.ret.
              intros s Hprops. simpl. destruct Hprops as [s0 Hprops]. exists s0. intuition.
              destruct H9 as [pdentry1 Hprops]. destruct Hprops as [pdentry2 Hprops]. intuition.
              destruct H9 as [pdentry1 Hprops]. destruct Hprops as [pdentry2 Hprops]. exists pdentry1.
              destruct Hprops as (Hs & HlookupGlobs0 & Hprops).
              split. assumption. split.
              {
                rewrite Hs.
                apply getKSEntriesEqPDT with pdentry1; unfold consistency in *; unfold consistency1 in *;
                    intuition.
              }
              split. intuition. split. intuition. split. intuition. exists pdentry2. intuition. unfold is_true. intro.
              exfalso; congruence.
         }
Qed.

(* Comes from Internal -> TODO put in InternalLemmas? *)
Lemma removeBlockFromPhysicalMPUIfAlreadyMapped (globalIdPD blockToEnableAddr currentPart: paddr)
                                                (P: state -> Prop) :
{{fun s =>
  P s /\ consistency s
  /\ currentPart = currentPartition s
  /\ globalIdPD <> nullAddr
  /\ isPDT globalIdPD s}}
Internal.removeBlockFromPhysicalMPUIfAlreadyMapped globalIdPD blockToEnableAddr
{{fun _ s  => 
  exists s0, P s0 /\ consistency s0 /\ isPDT globalIdPD s0
      /\ (exists pdentry : PDTable,
        (lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry)
        /\ (s = s0
            \/ exists MPURegionNb,
               (*MPURegionNb =
                indexOf blockToEnableAddr (CIndex 0) (MPU pdentry) beqAddr (S (CIndex kernelStructureEntriesNb))
               /\*) s = {|
                  currentPartition := currentPartition s0;
                  memory := add globalIdPD
                          (PDT
                           {|
                           structure := structure pdentry;
                           firstfreeslot := firstfreeslot pdentry;
                           nbfreeslots := nbfreeslots pdentry;
                           nbprepare := nbprepare pdentry;
                           parent := parent pdentry;
                           MPU := addElementAt MPURegionNb nullAddr (MPU pdentry) nullAddr;
					                     vidtAddr := vidtAddr pdentry |}) (memory s0) beqAddr |})))
  /\ consistency s
  /\ globalIdPD <> nullAddr
  /\ isPDT globalIdPD s}}.
Proof.
unfold Internal.removeBlockFromPhysicalMPUIfAlreadyMapped.
eapply bindRev.
- eapply getKernelStructureEntriesNb.
- intro kernelentriesnb. eapply bindRev.
  + eapply weaken. eapply Invariants.Index.succ. simpl. intros s Hprops. split.
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
         unfold kernelStructureEntriesNb in *. simpl in *. lia.
  + intro defaultidx. eapply bindRev.
    { (** MAL.findBlockIdxInPhysicalMPU **)
      eapply weaken. apply findBlockIdxInPhysicalMPU. intros s Hprops. simpl.
      split. eapply Hprops. intuition.
      * eapply H3.
    }
    {
      intro oldMPURegionNb. destruct (indexEq oldMPURegionNb defaultidx) eqn: HindexEq.
      -- (** case HindexEq : indexEq oldMPURegionNb defaultidx = true **)
         eapply weaken. eapply WP.ret. intros. simpl. exists s. intuition. apply isPDTLookupEq in H10.
         destruct H10 as [entry Hlookup]. exists entry. intuition.
      -- (** case HindexEq : indexEq oldMPURegionNb defaultidx = false **)
         eapply bindRev.
        ++ (** enableBlockInMPU **)
           set(block:= nullAddr).
           assert(Hweak: forall s : state,
               (((P s /\ consistency s) /\ currentPart = currentPartition s) /\ globalIdPD <> nullAddr)
                  /\ isPDT globalIdPD s
             -> P s /\ consistency s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s
                /\ (block <> nullAddr -> (In block (getAccessibleMappedBlocks globalIdPD s)))).
           { intros s Hprops. intuition. }
           apply weaken with (Q:= fun s:state => P s /\ consistency s /\ globalIdPD <> nullAddr
                /\ isPDT globalIdPD s
                /\ (block <> nullAddr -> (In block (getAccessibleMappedBlocks globalIdPD s)))).
           apply enableBlockInMPU. intros s Hprops. intuition.
        ++ intro is_mapped. eapply weaken. eapply WP.ret.
           intros s Hprops. simpl. destruct Hprops as [s0 Hprops]. exists s0. intuition.
           destruct H7 as [entry Hprops].
           exists entry. intuition. destruct is_mapped eqn:Hmapped.
           ** right. exists oldMPURegionNb. assert(Htrue: is_true true) by intuition. apply H11 in Htrue.
              destruct Htrue as [pdentry1 Hprops]. intuition.
           ** left. assert(Htrue: is_true false -> False) by (unfold is_true; intro; congruence).
              apply H14 in Htrue. assumption.
    }
Qed.

