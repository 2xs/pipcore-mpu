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

Require Import Lia Classical.

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

(* Comes from MAL -> TODO find where to put that *)
Lemma replaceBlockInPhysicalMPU (currentPart globalIdPD blockToEnableAddr: paddr) (MPURegionNb: index) :
{{ fun (s : state) =>
   (((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s)
    /\ currentPart = currentPartition s)
   /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s))
  /\ beqAddr nullAddr globalIdPD = false }} 
MAL.replaceBlockInPhysicalMPU globalIdPD blockToEnableAddr MPURegionNb
{{ fun (_: unit) (s : state) =>
   (((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s)
    /\ currentPart = currentPartition s)
   /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s))
  /\ beqAddr nullAddr globalIdPD = false }}.
Proof.
unfold MAL.replaceBlockInPhysicalMPU.
eapply bindRev.
- (** MAL.readPDMPU **)
  eapply weaken. eapply readPDMPU.
  simpl. intros s H.
  assert (Hprops: (partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s /\
    currentPart = currentPartition s /\ isPDT globalIdPD s) /\ isPDT globalIdPD s).
  {
    destruct H as [H1 HglobNotNull]. destruct H1 as [H1 Himpl].
    assert (HisPDT: isPDT globalIdPD s).
    {
      apply Himpl. apply beqAddrFalse in HglobNotNull. apply not_eq_sym. exact HglobNotNull.
    }
    intuition.
  }
  exact Hprops.
- intro realMPU. simpl. eapply bindRev.
  + (** MAL.writePDMPU **)
    eapply weaken. eapply writePDMPU.
    intros. simpl.
    assert (Htable: exists entry : PDTable, lookup globalIdPD (memory s) beqAddr = Some (PDT entry)).
    { apply isPDTLookupEq. intuition. }
    destruct Htable as [entry Hlookup].
    exists entry. split.
    * exact Hlookup.
    * set (fun (a:unit) (s1:state) =>
          ((((partitionsIsolation s1 /\ kernelDataIsolation s1 /\ verticalSharing s1 /\ consistency s1)
             /\ currentPart = currentPartition s1)
            /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s1))
           /\ beqAddr nullAddr globalIdPD = false)).
      set (s' := {|
       currentPartition := currentPartition s;
       memory := _ |}).
      assert (Hgoal: P tt s').
      {
        unfold P. intuition.
        -- unfold partitionsIsolation in *.
           intros parent child1 child2 HInParent HInChild1 HInChild2 HDifChildren.
	         unfold Lib.disjoint. intros x HInX. unfold getUsedPaddr. unfold getConfigPaddr.
	         unfold getMappedPaddr.
            admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
        -- admit.
      }
      exact Hgoal.
  + intro a0. eapply weaken. eapply WP.ret.
    intros s HQ. exact HQ.
Admitted.

(* Comes from Internal -> TODO put in InternalLemmas? *)
Lemma enableBlockInMPU (globalIdPD blockToEnableAddr currentPart: paddr) (MPURegionNb: index) :
{{ fun (s : state) =>
    (((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s)
      /\ currentPart = currentPartition s) 
     /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s)) 
    /\ beqAddr nullAddr globalIdPD = false }} 
Internal.enableBlockInMPU globalIdPD blockToEnableAddr MPURegionNb 
{{fun _ (s : state) => (((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
                                   /\ consistency s)
                                 /\ currentPart = currentPartition s)
                                /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s))
                               /\ beqAddr nullAddr globalIdPD = false }}.
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
         simpl. intros s H. eapply H.
      -- intro isAboveMPURegionsNb. destruct (isBelowZero || isAboveMPURegionsNb)%bool eqn: Ha.
         { (** case (isBelowZero || isAboveMPURegionsNb) = true **)
           eapply weaken. eapply WP.ret.
           intros s HQ. simpl. intuition.
         }
         { (** case (isBelowZero || isAboveMPURegionsNb) = false **)
           eapply bindRev.
           ++ (** MAL.replaceBlockInPhysicalMPU **)
              eapply weaken.
              eapply replaceBlockInPhysicalMPU.
              intros. simpl. intuition. eapply H7.
           ++ intro a3. eapply weaken. eapply WP.ret.
              intros s HQ. exact HQ.
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
         Search (?a > ?b). apply Gt.gt_le_S. apply HBigEnough.
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

