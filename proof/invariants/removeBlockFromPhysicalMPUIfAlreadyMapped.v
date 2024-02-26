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
Require Import Invariants MapMPUSecProps.

(*Temporary*)
Require Import replaceBlockInPhysicalMPU.

Require Import Lia Classical List.

Module WP := WeakestPreconditions.

Lemma findBlockIdxInPhysicalMPU (kernelentriesnb defaultidx: index)
    (globalIdPD blockToEnableAddr idBlockToEnable currentPart: paddr) :
{{ fun s : state =>
   ((((((((((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s) /\
            currentPart = currentPartition s) /\
           consistency s /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s)) /\
          beqAddr nullAddr globalIdPD = false) /\ beqAddr nullAddr idBlockToEnable = false) /\
        consistency s /\
        (blockToEnableAddr = nullAddr \/
         (exists entry : BlockEntry,
            lookup blockToEnableAddr (memory s) beqAddr = Some (BE entry) /\
            blockToEnableAddr = idBlockToEnable /\
            bentryPFlag blockToEnableAddr true s /\
            List.In blockToEnableAddr (getMappedBlocks globalIdPD s)))) /\
       beqAddr nullAddr blockToEnableAddr = false) /\ bentryAFlag blockToEnableAddr true s) /\
     bentryPFlag blockToEnableAddr true s) /\ kernelentriesnb = CIndex kernelStructureEntriesNb) /\
   StateLib.Index.succ kernelentriesnb = Some defaultidx }} 
MAL.findBlockIdxInPhysicalMPU globalIdPD blockToEnableAddr defaultidx
{{ fun _ (s: state) => (((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s)
                         /\ currentPart = currentPartition s)
                        /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s))
                       /\ beqAddr nullAddr globalIdPD = false }}.
Proof.
unfold MAL.findBlockIdxInPhysicalMPU. eapply bindRev.
- eapply weaken. eapply readPDMPU.
  intros s Hprops. simpl. split.
  + eapply Hprops.
  + destruct Hprops as [Hprops Hsucc]. destruct Hprops as [Hprops Hkentries]. destruct Hprops as [Hprops HP].
    destruct Hprops as [Hprops HA]. destruct Hprops as [Hprops HaddrNotNull]. destruct Hprops as [Hprops1 Hprops2].
    destruct Hprops1 as [Hprops1 HidNotNull]. destruct Hprops1 as [Hprops1 HglobIdNotNull].
    destruct Hprops1 as [Hprops1 Hprops3]. destruct Hprops3 as [Hconst HisPDT].
    apply HisPDT. apply beqAddrFalse in HglobIdNotNull. apply not_eq_sym. exact HglobIdNotNull.
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
   exists s0, P s0 /\ consistency s
    /\ globalIdPD <> nullAddr
    /\ (is_true enabled -> (exists pdentry : PDTable, exists pdentry1: PDTable,
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
    /\ lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry)
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
    /\ isPDT globalIdPD s0
    /\ isPDT globalIdPD s
    (* globalIdPD's new free slots list and relation with list at s0 *)
    /\ (
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
     |} /\ getKSEntries globalIdPD s = getKSEntries globalIdPD s0

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
     )))
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
           ++ intro. eapply weaken. eapply WP.ret.
              intros s Hprops. simpl. destruct Hprops as [s0 Hprops]. exists s0. intuition.
              destruct H3 as [pdentry1 Hprops]. destruct Hprops as [pdentry2 Hprops].
              exists pdentry1. exists pdentry2. intuition.
              rewrite H17. apply getKSEntriesEqPDT with pdentry1; intuition.
              unfold consistency in *; unfold consistency1 in *; intuition.
         }
Qed.


(* Comes from Internal -> TODO put in InternalLemmas? *)
Lemma removeBlockFromPhysicalMPUIfAlreadyMapped (globalIdPD blockToEnableAddr idBlockToEnable currentPart: paddr) : 
{{fun s =>
  ((((((((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s)
          /\ currentPart = currentPartition s)
        /\ consistency s /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s)) 
      /\ beqAddr nullAddr globalIdPD = false) /\ beqAddr nullAddr idBlockToEnable = false)
     /\ consistency s /\
          (blockToEnableAddr = nullAddr \/
           (exists entry : BlockEntry,
              lookup blockToEnableAddr (memory s) beqAddr = Some (BE entry)
             /\ blockToEnableAddr = idBlockToEnable
             /\ bentryPFlag blockToEnableAddr true s
             /\ List.In blockToEnableAddr (getMappedBlocks globalIdPD s))))
    /\ beqAddr nullAddr blockToEnableAddr = false)
   /\ bentryAFlag blockToEnableAddr true s)
  /\ bentryPFlag blockToEnableAddr true s}}
Internal.removeBlockFromPhysicalMPUIfAlreadyMapped globalIdPD blockToEnableAddr
{{fun _ s  => 
  (((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s) 
    /\ currentPart = currentPartition s) 
   /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s)) 
  /\ beqAddr nullAddr globalIdPD = false}}.
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
         apply Gt.gt_le_S. apply HBigEnough.
  + intro defaultidx. eapply bindRev.
    { (** MAL.findBlockIdxInPhysicalMPU **)
      eapply findBlockIdxInPhysicalMPU.
    }
    {
      intro oldMPURegionNb. destruct (indexEq oldMPURegionNb defaultidx) eqn: HindexEq.
      -- (** case HindexEq : indexEq a1 a0 = false **)
         eapply weaken. eapply WP.ret. intros. simpl. exact H.
      -- (** case HindexEq : indexEq a1 a0 = true **)
         eapply bindRev.
        ++ (** enableBlockInMPU **)
           eapply weaken. eapply enableBlockInMPU.
           simpl. intros s Hprops. exact Hprops.
        ++ intro a2. eapply weaken. eapply WP.ret.
           intros. simpl. exact H.
    }
Qed.

