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
    This file contains the invariant of [mapMPU].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas.
Require Import Invariants getGlobalIdPDCurrentOrChild findBlockInKS removeBlockFromPhysicalMPUIfAlreadyMapped.
Require Import MapMPUSecProps.
Require Import Compare_dec Bool FunctionalExtensionality List.

Require Import Model.Monad Model.MALInternal Model.Lib (* for visibility *).

Module WP := WeakestPreconditions.

Lemma mapMPU 	(idPD idBlockToEnable : paddr) (MPURegionNb : index) :
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
Services.mapMPU idPD idBlockToEnable MPURegionNb
{{fun _ s  => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold Services.mapMPU.
eapply bindRev.
{ (** getCurPartition **)
	eapply weaken. apply getCurPartition.
	intros. simpl. apply H.
}
intro currentPart.
eapply bindRev.
{ (** Internal.getGlobalIdPDCurrentOrChild **)
	eapply weaken. apply getGlobalIdPDCurrentOrChild.
	intros s HsecProp. simpl. split. apply HsecProp. intuition. subst currentPart.
  unfold consistency in * ; unfold consistency1 in *.
		eapply currentPartIsPDT ; intuition.
}
intro globalIdPD.
eapply bindRev.
{ (** compareAddrToNull **)
	eapply weaken. apply Invariants.compareAddrToNull.
	intros. simpl. apply H.
}
intro addrIsNull.
case_eq addrIsNull.
- (* case_eq addrIsNull = true *)
	intros.
	{ (** ret *)
	eapply weaken. apply WP.ret.
  simpl. intros. intuition.
	}
- (* case_eq addrIsNull = false *)
	intros.
	eapply bindRev.
	{ (** compareAddrToNull **)
		eapply weaken. apply Invariants.compareAddrToNull.
		intros. simpl.
    assert (HglobNotNull: globalIdPD <> nullAddr).
    { rewrite <- beqAddrFalse in *. intuition. }
    assert (HisPDT: isPDT globalIdPD s) by intuition.
    pose (Hconj := conj (conj H0 HglobNotNull) HisPDT).
    apply Hconj.
	}
	intro blockIsNull.
	case_eq blockIsNull.
	+ (* case_eq blockIsNull = true *)
		intros. set(Psep:= fun s:state => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s).
    set(blockToEnableAddr:= nullAddr).
    assert(Hweak: forall s : state,
        ((((((partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s) /\
            currentPart = currentPartition s) /\
           consistency s /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s)) /\
          beqAddr nullAddr globalIdPD = false) /\ globalIdPD <> nullAddr) /\
        isPDT globalIdPD s) /\ beqAddr nullAddr idBlockToEnable = true
      -> Psep s /\ consistency s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s
         /\ (blockToEnableAddr <> nullAddr
            -> (In blockToEnableAddr (getAccessibleMappedBlocks globalIdPD s)))).
    { intros s Hprops. subst Psep. simpl. intuition. }
    apply weaken with (Q:= fun s:state => Psep s /\ consistency s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s
         /\ (blockToEnableAddr <> nullAddr
            -> (In blockToEnableAddr (getAccessibleMappedBlocks globalIdPD s)))).
		eapply strengthen. apply enableBlockInMPU.
    * simpl. intros s is_mapped. intro Hprops. destruct Hprops as [s0 Hprops]. clear Hweak. subst Psep.
      simpl in Hprops.
      destruct Hprops as [HsecProps (Hconsts0 & (HPDTs0 & (Hconsts & (HGlobNotNull & (HPDTs0Bis & (HPDTs
                        & Hprops))))))].
      destruct Hprops as [entry0 Hprops].
      intuition.
      -- (* partitionsIsolation s *)
         apply MapMPUHI with globalIdPD blockToEnableAddr MPURegionNb is_mapped s0 s0 entry0 entry0.
         unfold MapMPUPropagatedProperties; intuition.
      -- (* kernelDataIsolation s *)
         apply MapMPUKI with globalIdPD blockToEnableAddr MPURegionNb is_mapped s0 s0 entry0 entry0.
         unfold MapMPUPropagatedProperties; intuition.
      -- (* verticalSharing s *)
         apply MapMPUVS with globalIdPD blockToEnableAddr MPURegionNb is_mapped s0 s0 entry0 entry0.
         unfold MapMPUPropagatedProperties; intuition.
    * simpl. intros s Hprops. subst Psep. intuition.
	+ (* case_eq blockIsNull = false *)
		intros.
		eapply WP.bindRev.
		{ (** findBlockInKSWithAddr **)
			eapply weaken. apply findBlockInKSWithAddr.findBlockInKSWithAddr.
			intros. simpl. split. apply H1. intuition.
		}
		intro blockToEnableAddr.
		eapply WP.bindRev.
		{ (** compareAddrToNull **)
			eapply weaken. apply Invariants.compareAddrToNull.
			intros. simpl. apply H1.
		}
		intro addrIsNull0.
		case_eq addrIsNull0.
		{ (* case_eq addrIsNull0 = true *)
			intros. eapply WP.weaken.
			eapply WP.ret.
			simpl. intros.
			intuition.
		}
		(* case_eq addrIsNull0 = false *)
		intros.
		eapply bindRev.
		{ (** MAL.readBlockAccessibleFromBlockEntryAddr **)
			eapply weaken. apply readBlockAccessibleFromBlockEntryAddr.
			intros. simpl. split. apply H2.
			repeat rewrite <- beqAddrFalse in *.
      assert(Hres: blockToEnableAddr = nullAddr \/ (exists entry,
          lookup blockToEnableAddr (memory s) beqAddr = Some (BE entry) /\
          blockToEnableAddr = idBlockToEnable /\
          bentryPFlag blockToEnableAddr true s /\ In blockToEnableAddr (getMappedBlocks globalIdPD s)))
        by intuition.
      assert(HbeqNullBlock: nullAddr <> blockToEnableAddr) by intuition.
      destruct Hres as [Hcontra | Hres]; try(exfalso; congruence).
			apply isBELookupEq. destruct Hres as [entry Hres]. exists entry. intuition.
		}
		intro addrIsAccessible.
		case_eq (negb addrIsAccessible).
		{ (* case_eq negb addrIsAccessible = true *)
			intros. eapply WP.weaken.
			eapply WP.ret.
			simpl. intros.
			intuition.
		}
		(* case_eq negb addrIsAccessible = false *)
		intros.
		eapply bindRev.
		{ (** MAL.readBlockPresentFromBlockEntryAddr **)
			eapply weaken. apply readBlockPresentFromBlockEntryAddr.
			intros. simpl. split. apply H3.
			repeat rewrite <- beqAddrFalse in *.
      assert(Hres: blockToEnableAddr = nullAddr \/ (exists entry,
          lookup blockToEnableAddr (memory s) beqAddr = Some (BE entry) /\
          blockToEnableAddr = idBlockToEnable /\
          bentryPFlag blockToEnableAddr true s /\ In blockToEnableAddr (getMappedBlocks globalIdPD s)))
        by intuition.
      assert(HbeqNullBlock: nullAddr <> blockToEnableAddr) by intuition.
      destruct Hres as [Hcontra | Hres]; try(exfalso; congruence).
			apply isBELookupEq. destruct Hres as [entry Hres]. exists entry. intuition.
		}
		intro addrIsPresent.
		case_eq (negb addrIsPresent).
		{ (* case_eq negb addrIsPresent = true *)
			intros. eapply WP.weaken.
			eapply WP.ret.
			simpl. intros.
			intuition.
		}
		(* case_eq negb addrIsPresent = false *)
		intros. eapply bindRev.
    { (** Internal.removeBlockFromPhysicalMPUIfAlreadyMapped **)
      set(P:= fun s:state => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
              /\ beqAddr nullAddr idBlockToEnable = false
              /\ (blockToEnableAddr = nullAddr \/
                   (exists entry : BlockEntry,
                      lookup blockToEnableAddr (memory s) beqAddr = Some (BE entry)
                     /\ blockToEnableAddr = idBlockToEnable
                     /\ bentryPFlag blockToEnableAddr true s
                     /\ List.In blockToEnableAddr (getMappedBlocks globalIdPD s)))
              /\ beqAddr nullAddr blockToEnableAddr = false
              /\ bentryAFlag blockToEnableAddr true s
              /\ bentryPFlag blockToEnableAddr true s).
      assert(Hweak: forall s : state,
          ((((((((((partitionsIsolation s /\
                   kernelDataIsolation s /\ verticalSharing s /\ consistency s) /\
                  currentPart = currentPartition s) /\
                 consistency s /\ (globalIdPD <> nullAddr -> isPDT globalIdPD s)) /\
                beqAddr nullAddr globalIdPD = false) /\ globalIdPD <> nullAddr) /\
              isPDT globalIdPD s) /\ beqAddr nullAddr idBlockToEnable = false) /\
              consistency s /\
              (blockToEnableAddr = nullAddr \/
               (exists entry : BlockEntry,
                  lookup blockToEnableAddr (memory s) beqAddr = Some (BE entry) /\
                  blockToEnableAddr = idBlockToEnable /\
                  bentryPFlag blockToEnableAddr true s /\
                  In blockToEnableAddr (getMappedBlocks globalIdPD s)))) /\
             beqAddr nullAddr blockToEnableAddr = false) /\
             bentryAFlag blockToEnableAddr addrIsAccessible s) /\
             bentryPFlag blockToEnableAddr addrIsPresent s
        -> P s /\ consistency s /\ currentPart = currentPartition s /\ globalIdPD <> nullAddr
                /\ isPDT globalIdPD s).
      {
        intros s Hprops. subst P. simpl.
        rewrite negb_false_iff in H2; subst addrIsAccessible; rewrite negb_false_iff in H3;
            subst addrIsPresent; intuition.
      }
      apply weaken with (Q:= fun s:state => P s /\ consistency s /\ currentPart = currentPartition s
                                            /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s).
      * eapply removeBlockFromPhysicalMPUIfAlreadyMapped.
      * intros s Hprops. apply Hweak. intuition.
    }
    { (** Internal.enableBlockInMPU **)
      intros. simpl.
      set(Psep:= fun s:state => exists s0 : state,
                 partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ consistency s0
                  /\ beqAddr nullAddr idBlockToEnable = false
                  /\ (blockToEnableAddr = nullAddr \/
                     (exists entry : BlockEntry,
                        lookup blockToEnableAddr (memory s0) beqAddr = Some (BE entry) /\
                        blockToEnableAddr = idBlockToEnable))
                  /\ beqAddr nullAddr blockToEnableAddr = false
                  /\
                   (exists pdentry : PDTable,
                      lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry) /\
                       (s = s0 \/
                        (exists MPURegionNb0 : nat,
                           s =
                           {|
                             currentPartition := currentPartition s0;
                             memory :=
                               add globalIdPD
                                 (PDT
                                    {|
                                      structure := structure pdentry;
                                      firstfreeslot := firstfreeslot pdentry;
                                      nbfreeslots := nbfreeslots pdentry;
                                      nbprepare := nbprepare pdentry;
                                      parent := parent pdentry;
                                      MPU := addElementAt MPURegionNb0 nullAddr (MPU pdentry) nullAddr;
                                      vidtAddr := vidtAddr pdentry
                                    |}) (memory s0) beqAddr
                           |})))).
      assert(Hweak: forall s:state,
                (exists s0 : state,
                 (partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0
                  /\ beqAddr nullAddr idBlockToEnable = false
                  /\ (blockToEnableAddr = nullAddr \/
                     (exists entry : BlockEntry,
                        lookup blockToEnableAddr (memory s0) beqAddr = Some (BE entry) /\
                        blockToEnableAddr = idBlockToEnable /\
                        bentryPFlag blockToEnableAddr true s0 /\
                        In blockToEnableAddr (getMappedBlocks globalIdPD s0)))
                  /\ beqAddr nullAddr blockToEnableAddr = false /\ bentryAFlag blockToEnableAddr true s0
                  /\ bentryPFlag blockToEnableAddr true s0)
                  /\ consistency s0
                  /\ isPDT globalIdPD s0
                  /\ (exists pdentry : PDTable,
                      lookup globalIdPD (memory s0) beqAddr = Some (PDT pdentry) /\
                       (s = s0 \/
                        (exists MPURegionNb0 : nat,
                           s =
                           {|
                             currentPartition := currentPartition s0;
                             memory :=
                               add globalIdPD
                                 (PDT
                                    {|
                                      structure := structure pdentry;
                                      firstfreeslot := firstfreeslot pdentry;
                                      nbfreeslots := nbfreeslots pdentry;
                                      nbprepare := nbprepare pdentry;
                                      parent := parent pdentry;
                                      MPU := addElementAt MPURegionNb0 nullAddr (MPU pdentry) nullAddr;
                                      vidtAddr := vidtAddr pdentry
                                    |}) (memory s0) beqAddr
                           |})))
                  /\ consistency s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s)
              -> Psep s /\ consistency s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s
                /\ (blockToEnableAddr <> nullAddr
                      -> In blockToEnableAddr (getAccessibleMappedBlocks globalIdPD s))).
      {
        intros s Hprops. subst Psep. simpl.
        destruct Hprops as [s0 Hprops]. split.
        * exists s0. intuition. right. destruct H17 as [bentry Hprops]. exists bentry. intuition.
        * intuition.
          unfold getAccessibleMappedBlocks. apply isPDTLookupEq in H16. destruct H16 as [entry Hlookups].
          rewrite Hlookups.
          destruct H17 as [bentry (HlookupBentry & (HblockEq & (HisPresent & HinMappedBlocks)))].
          destruct H9 as [pdentry (Hlookups0 & Hprops)].
          assert(HmappedBlocksEq: getMappedBlocks globalIdPD s = getMappedBlocks globalIdPD s0).
          {
            destruct Hprops as [Hunchanged | HnewState].
            -- rewrite Hunchanged. reflexivity.
            -- destruct HnewState as [MPURegionNb0 Hs]. rewrite Hs.
               unfold consistency in *; unfold consistency1 in *; apply getMappedBlocksEqPDT with pdentry
               ; intuition.
          }
          rewrite HmappedBlocksEq in *.
          assert(HfilterEq: filterAccessible (getMappedBlocks globalIdPD s0) s
                            = filterAccessible (getMappedBlocks globalIdPD s0) s0).
          {
            destruct Hprops as [Hunchanged | HnewState].
            -- rewrite Hunchanged. reflexivity.
            -- destruct HnewState as [MPURegionNb0 Hs]. rewrite Hs. apply filterAccessibleEqPDT; intuition.
          }
          rewrite HfilterEq. clear HmappedBlocksEq. clear HfilterEq.
          induction (getMappedBlocks globalIdPD s0).
          -- assert(~In blockToEnableAddr nil) by apply in_nil. congruence.
          -- destruct (beqAddr blockToEnableAddr a0) eqn:HbeqBlockA.
             ++ rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqBlockA. subst a0. simpl.
                unfold bentryAFlag in *. rewrite HlookupBentry in *. rewrite <-H15. apply in_eq.
             ++ apply in_inv in HinMappedBlocks. rewrite <-beqAddrFalse in HbeqBlockA.
                destruct HinMappedBlocks as [Hcontra | HinMappedBlocks]; try(exfalso; congruence).
                apply IHl in HinMappedBlocks. simpl.
                destruct (lookup a0 (memory s0) beqAddr). destruct v; try(apply HinMappedBlocks).
                ** destruct (accessible b); try(apply HinMappedBlocks). apply in_cons. assumption.
                ** assumption.
      }
      apply weaken with (Q:= fun s => Psep s /\ consistency s /\ globalIdPD <> nullAddr /\ isPDT globalIdPD s
                                      /\ (blockToEnableAddr <> nullAddr
                                          -> In blockToEnableAddr (getAccessibleMappedBlocks globalIdPD s))).
      eapply strengthen. apply enableBlockInMPU.
      * intros s is_mapped. simpl. intro Hprops. destruct Hprops as [s1 Hprops]. clear Hweak.
        destruct Hprops as [Hlinks0s1 Hprops]. subst Psep. simpl in Hlinks0s1.
        destruct Hlinks0s1 as [s0 Hlinks0s1].
        destruct Hlinks0s1 as [HPIs0 (HKIs0 & (HVSs0 & (Hconsts0 & (HidBlockNotNull & (Hbentry & (HblockNotNull
                                & Hlinks0s1))))))].
        rewrite <-beqAddrFalse in *. destruct Hbentry as [Hcontra | Hbentry]; try(congruence).
        destruct Hbentry as [bentry0 Hbentry].
        destruct Hlinks0s1 as [entry0 Hlinks0s1].
        destruct Hprops as [Hconsts1 (HPDTs1 & (Hconsts & (HGlobNotNull & (HPDTs1Bis & (HPDTs & Hprops)))))].
        destruct Hprops as [entry1 Hprops].
        assert(isPDT globalIdPD s0).
        { unfold isPDT. destruct Hlinks0s1 as [Hlookups0 Hlinks0s1]. rewrite Hlookups0. trivial. }
        split; try(split; try(split)).
        -- (* partitionsIsolation s *)
           apply MapMPUHI with globalIdPD blockToEnableAddr MPURegionNb is_mapped s0 s1 entry0 entry1.
           unfold MapMPUPropagatedProperties; intuition.
        -- (* kernelDataIsolation s *)
           apply MapMPUKI with globalIdPD blockToEnableAddr MPURegionNb is_mapped s0 s1 entry0 entry1.
           unfold MapMPUPropagatedProperties; intuition.
        -- (* verticalSharing s *)
           apply MapMPUVS with globalIdPD blockToEnableAddr MPURegionNb is_mapped s0 s1 entry0 entry1.
           unfold MapMPUPropagatedProperties; intuition.
        -- intuition.
      * intro s. simpl. intro Hprops. apply Hweak. apply Hprops.
    }
Qed.
