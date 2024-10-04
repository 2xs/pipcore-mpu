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

Require Import Model.ADT Model.Monad Model.Lib Model.MALInternal.
Require Import Core.Internal.
Require Import Proof.WeakestPreconditions Proof.Consistency Proof.StateLib Proof.DependentTypeLemmas
              Proof.InternalLemmas Proof.Isolation.
Require Import Hoare Invariants findBlockInKS isBuiltFromWriteAccessibleRec.
Require Import FunctionalExtensionality List Lia Coq.Logic.ProofIrrelevance Coq.Bool.Bool Coq.Bool.BoolEq.
Import List.ListNotations.

Module WP := WeakestPreconditions.
Module DTL := DependentTypeLemmas.

Global Set Primitive Projections.
Global Set Printing Primitive Projection Parameters.

Lemma removeBlockFromPhysicalMPU (pd : paddr) (blockentryaddr : paddr) (P : state -> Prop) :
{{ fun s => P s /\ isPDT pd s	}}
MAL.removeBlockFromPhysicalMPU pd blockentryaddr
{{fun (_ : unit) (s : state) =>
      exists s0 pdentry realMPU,
          pdentryMPU pd realMPU s0
          /\ P s0
          /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
          /\ s = {|
                    currentPartition := currentPartition s0;
                    memory :=
                      add pd
                        (PDT
                           {|
                             structure := structure pdentry;
                             firstfreeslot := firstfreeslot pdentry;
                             nbfreeslots := nbfreeslots pdentry;
                             nbprepare := nbprepare pdentry;
                             parent := parent pdentry;
                             MPU := MAL.removeBlockFromPhysicalMPUAux blockentryaddr realMPU;
                             vidtAddr := vidtAddr pdentry
                           |}) (memory s0) beqAddr
                  |}
}}.
Proof.
unfold MAL.removeBlockFromPhysicalMPU. eapply bindRev.
{
  eapply weaken. apply readPDMPU. intros s Hprops. simpl. split. apply Hprops. intuition.
}
intro realMPU. eapply bindRev.
- eapply weaken. apply writePDMPU.
  intros s Hprops. simpl. destruct Hprops as [(HPs & HPDT) Hpdentry]. unfold isPDT in HPDT.
  destruct (lookup pd (memory s) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists p. split. reflexivity.
  instantiate(1:= fun (_:unit) (s:state) =>
              exists s0 pdentry,
                pdentryMPU pd realMPU s0
                /\ P s0
                /\ lookup pd (memory s0) beqAddr = Some (PDT pdentry)
                /\ s = {|
                          currentPartition := currentPartition s0;
                          memory :=
                            add pd
                              (PDT
                                 {|
                                   structure := structure pdentry;
                                   firstfreeslot := firstfreeslot pdentry;
                                   nbfreeslots := nbfreeslots pdentry;
                                   nbprepare := nbprepare pdentry;
                                   parent := parent pdentry;
                                   MPU := MAL.removeBlockFromPhysicalMPUAux blockentryaddr realMPU;
                                   vidtAddr := vidtAddr pdentry
                                 |}) (memory s0) beqAddr
                        |}
  ).
  simpl. exists s. exists p. intuition.
- intro. simpl. eapply weaken. apply WP.ret.
  simpl. intros s Hprops. destruct Hprops as [s0 (pdentry & Hprops)].
  exists s0. exists pdentry. exists realMPU. intuition.
Qed.

Lemma writeAccessibleRecAux (timeout : nat) (pdbasepartition partition startaddr endaddr : paddr) (flag : bool)
                          (P : state -> Prop):
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency1 s
           /\ noDupUsedPaddrList s
           /\ sharedBlockPointsToChild s
           /\ adressesRangePreservedIfOriginAndNextOk s
           /\ childsBlocksPropsInParent s
           /\ noChildImpliesAddressesNotShared s
           /\ (forall parentsList, isParentsList s parentsList partition
                                    (*-> constantRootPartM = last parentsList partition*)
                                    -> length parentsList < timeout)
           /\ In startaddr (getMappedPaddr partition s)
           /\ (exists s0 pdparent statesList parentsList,
                  partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ P s0
                  /\ consistency s0
                  /\ isParentsList s0 parentsList pdbasepartition
                  /\ s = last statesList s0
                  /\ partition = last parentsList pdbasepartition
                  /\ (exists pdentryBase, lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase)
                                        /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase))
                  /\ (exists ancestorEntry, lookup partition (memory s) beqAddr = Some (PDT ancestorEntry)
                                            /\ (partition <> constantRootPartM /\ pdparent = parent ancestorEntry
                                                \/ partition = constantRootPartM /\ pdparent = nullAddr))
                  /\ In pdbasepartition (getPartitions multiplexer s0)
                  /\ In partition (getPartitions multiplexer s0)
                  /\ (exists blockBase bentryBase bentryBases0,
                        lookup blockBase (memory s0) beqAddr = Some (BE bentryBases0)
                        /\ bentryPFlag blockBase true s0
                        /\ bentryAFlag blockBase true s0
                        /\ In blockBase (getMappedBlocks pdbasepartition s0)
                        /\ In blockBase (getAccessibleMappedBlocks pdbasepartition s0)
                        /\ bentryStartAddr blockBase startaddr s0
                        /\ bentryEndAddr blockBase endaddr s0
                        /\ false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
                        /\ lookup blockBase (memory s) beqAddr = Some (BE bentryBase)
                        /\ bentryPFlag blockBase true s
                        /\ bentryAFlag blockBase true s
                        /\ In blockBase (getMappedBlocks pdbasepartition s)
                        /\ bentryStartAddr blockBase startaddr s
                        /\ bentryEndAddr blockBase endaddr s
                        /\ false = checkChild blockBase s (CPaddr (blockBase + sh1offset)))
                  /\ (exists blockPart bentryPart,
                        lookup blockPart (memory s) beqAddr = Some (BE bentryPart)
                        /\ bentryPFlag blockPart true s
                        /\ In blockPart (getMappedBlocks partition s)
                        /\ bentryStartAddr blockPart startaddr s
                        /\ bentryEndAddr blockPart endaddr s
                        /\ false = checkChild blockPart s (CPaddr (blockPart + sh1offset)))
                  /\ (exists blockaddr bentry,
                        lookup blockaddr (memory s) beqAddr = Some (BE bentry)
                        /\ bentryPFlag blockaddr true s
                        /\ (flag = true -> bentryAFlag blockaddr true s)
                        /\ In blockaddr (getMappedBlocks partition s)
                        /\ bentryStartAddr blockaddr startaddr s
                        /\ bentryEndAddr blockaddr endaddr s
                        /\ (s = s0 \/
                                (forall parent child addr,
                                        ((child <> partition /\ child <> pdbasepartition)
                                          \/ ~ In addr (getAllPaddrAux [blockaddr] s))
                                        -> In parent (getPartitions multiplexer s)
                                        -> In child (getChildren parent s)
                                        -> In addr (getAccessibleMappedPaddr parent s)
                                        -> In addr (getMappedPaddr child s)
                                        -> In addr (getAccessibleMappedPaddr child s))))
                  /\ isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition startaddr endaddr
                          flag
                  /\ accessibleParentPaddrIsAccessibleIntoChild s0)
}}
writeAccessibleRecAux timeout partition startaddr endaddr flag
{{fun writeSucceded s =>
      partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\
      exists s0 pdentryBase statesList parentsList,
        (* Common properties *)
        partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ P s0 /\ consistency s0
        /\ isParentsList s0 parentsList pdbasepartition
        /\ s = last statesList s0
        /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase)
        /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase)
        /\ In pdbasepartition (getPartitions multiplexer s0)
        /\ consistency1 s
        /\ noDupUsedPaddrList s
        /\ sharedBlockPointsToChild s
        /\ adressesRangePreservedIfOriginAndNextOk s
        /\ childsBlocksPropsInParent s
        /\ noChildImpliesAddressesNotShared s
        (*Propagation properties*)
        /\ (exists blockBase bentryBase bentryBases0,
              lookup blockBase (memory s0) beqAddr = Some (BE bentryBases0)
              /\ bentryPFlag blockBase true s0
              /\ bentryAFlag blockBase true s0
              /\ In blockBase (getMappedBlocks pdbasepartition s0)
              /\ In blockBase (getAccessibleMappedBlocks pdbasepartition s0)
              /\ bentryStartAddr blockBase startaddr s0
              /\ bentryEndAddr blockBase endaddr s0
              /\ false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
              /\ lookup blockBase (memory s) beqAddr = Some (BE bentryBase)
              /\ bentryPFlag blockBase true s
              /\ bentryAFlag blockBase true s
              /\ In blockBase (getMappedBlocks pdbasepartition s)
              /\ bentryStartAddr blockBase startaddr s
              /\ bentryEndAddr blockBase endaddr s
              /\ false = checkChild blockBase s (CPaddr (blockBase + sh1offset)))
        /\ accessibleParentPaddrIsAccessibleIntoChild s
        /\ (exists lastPart pdentryLast, lastPart = last parentsList pdbasepartition
              /\ lookup lastPart (memory s) beqAddr = Some (PDT pdentryLast)
              /\ (parent pdentryLast = nullAddr
                  \/ (forall block, In block (getMappedBlocks (parent pdentryLast) s)
                        -> ~ (bentryStartAddr block startaddr s /\ bentryEndAddr block endaddr s))))
        /\ isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition startaddr endaddr flag}}.
Proof.
assert(Htriv: true = true) by reflexivity.
assert(HtrivFalse: false = false) by reflexivity.
revert partition. revert P. induction timeout.
{
  simpl. intros P partition. eapply weaken. eapply WP.ret.
  intros s Hprops. simpl.
  destruct Hprops as (HPI & HKDI & HVS & Hconsist & (HnoDup & Hshared & HaddrRange & HchildBlockProps & _ &
                      HparentsListLength & Hprops)).
  assert(HemptyIsParentsList: isParentsList s [] partition).
  {
    simpl. trivial.
  }
  specialize(HparentsListLength [] HemptyIsParentsList). simpl in HparentsListLength. exfalso; lia.
}
(* N <> 0 *)
intros P partition. simpl. destruct (beqAddr partition constantRootPartM) eqn:HbeqBaseRoot.
- rewrite <-DTL.beqAddrTrue in HbeqBaseRoot. rewrite HbeqBaseRoot in *. eapply weaken. apply WP.ret.
  intros s Hprops. simpl.
  destruct Hprops as (HPI & HKDI & HVS & Hconsist & HnoDup & Hshared & HaddrRange & HchildBlockProps &
                      HnoChild & HparentsListLength & HstartIsMappedRoot & Hprops).
  destruct Hprops as [s0 (pdparent & (statesList & (parentsList & (HPIs0 & HKDIs0 & HVSs0 &
                      HPs0 & Hconsists0 & HisParentsList & HsIsLast & HpartIsLast & HbaseIsPDT & HpartIsPDT &
                      HbaseIsPart & HpartIsPart & HblockBase & HblockPart & HpartialAccessChild & HisBuilt &
                      Haccesss0))))].
  destruct HbaseIsPDT as [pdentryBase (HlookupBases0 & HlookupBase)].
  destruct HpartIsPDT as [pdentryPart (HlookupPart & HpropsOrParent)].
  split. assumption. split. assumption. split. assumption.
  exists s0. exists pdentryBase. exists statesList.
  exists parentsList. split. assumption. split. assumption. split. assumption. split. assumption.
  split. assumption. split. assumption. split. assumption. split. assumption. split. assumption.
  split. assumption. split. assumption. split. assumption. split. assumption.
  split. assumption. split. assumption. split. assumption. split. assumption. split; try(split; try(assumption)).
  + destruct HpartialAccessChild as [blockaddr (bentry & HpropsBlockAddr)].
    destruct HblockBase as [blockBase [bentryBase [bentryBases0 HblockBase]]].
    destruct HpropsBlockAddr as (HlookupBlockAddr & HPFlagBlockAddr & HAFlagBlockAddr &
        HblockAddrMapped & HstartBlockAddr & HendBlockAddr & HpartialAccessChild).
    (* accessibleParentPaddrIsAccessibleIntoChild s *)
    destruct HpartialAccessChild as [Hss0Eq | HpartialAccess].
    { rewrite Hss0Eq in *. assumption. }
    assert(HAFlags: s <> s0 -> bentryAFlag blockaddr flag s).
    {
      assert(HisBuiltCopy: isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition
                          startaddr endaddr flag) by assumption.
      intro HsNotEqs0. destruct statesList.
      - (* statesList = [] *)
        simpl in HisBuilt. destruct HisBuilt as [_ Hss0Eq]. exfalso; congruence.
      - (* statesList = a::l *)
        simpl in HisBuilt.
        destruct HisBuilt as [pdAddr (newPdEntriesList & (HparentsList & (realMPU & (pdentryBaseBis &
                              (pdentryPdAddr & (blockInParentPartitionAddr & (bentryBlock & (newBentry & (s1'
                              & (Hs1 & HpropsOr & HnewB & HlookupBlocks0 & HlookupBlocks1 &
                              HPFlagBlock & HstartBlock & HblockMappedPdAddr & HlookupBases0' & HlookupBases1
                              & HlookupPdAddrs0 & HlookupPdAddrs1 & HpdAddr & HisBuilt))))))))))].
        apply parentsAccSetToFlagIfIsBuiltFromWriteAccessibleRec with pdbasepartition constantRootPartM
              startaddr endaddr s0 (s1::statesList) parentsList blockBase bentryBases0;
          try(unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *; intuition; congruence).
        assert(Hlast: parentsList = removelast parentsList ++ [constantRootPartM]).
        {
          rewrite HpartIsLast. apply app_removelast_last. rewrite HparentsList. intro Hcontra.
          assert(Hcontra': length (pdAddr::newPdEntriesList) = 0) by (apply length_zero_iff_nil; assumption).
          simpl in Hcontra'. lia.
        }
        rewrite Hlast. apply in_or_app. right. simpl. left. reflexivity.
    }
    unfold accessibleParentPaddrIsAccessibleIntoChild.
    intros parent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
    rewrite HlookupBlockAddr in HpartialAccess. rewrite app_nil_r in HpartialAccess.
    destruct (beqAddr child constantRootPartM) eqn:HbeqChildRoot.
    {
      rewrite <-DTL.beqAddrTrue in HbeqChildRoot. subst child.
      assert(Hparent: isParent s) by (unfold consistency1 in *; intuition).
      specialize(Hparent constantRootPartM parent HparentIsPart HchildIsChild). unfold pdentryParent in Hparent.
      assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
      specialize(HparentOfPart constantRootPartM pdentryPart HlookupPart).
      rewrite HlookupPart in Hparent. destruct HparentOfPart as (_ & HparentOfRoot & _).
      assert(Htrue: constantRootPartM = constantRootPartM) by reflexivity. specialize(HparentOfRoot Htrue).
      rewrite HparentOfRoot in Hparent. rewrite Hparent in *.
      assert(isPDT nullAddr s).
      {
        unfold consistency1 in *; apply partitionsArePDT; intuition.
      }
      assert(isPADDR nullAddr s).
      {
        assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
        assumption.
      }
      unfold isPDT in *. unfold isPADDR in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
      destruct v; exfalso; congruence.
    }
    rewrite <-beqAddrFalse in HbeqChildRoot.
    destruct (beqAddr child pdbasepartition) eqn:HbeqChildBase.
    * (* child = pdbasepartition *)
      rewrite <-DTL.beqAddrTrue in HbeqChildBase. subst child.
      assert(HaddrInBlock:
             In addr (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry)))
              \/ ~In addr (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry))))
            by (apply Classical_Prop.classic).
      destruct HaddrInBlock as [HaddrInBlock | HaddrNotInBlock].
      -- destruct HblockBase as (HlookupBlockBase & HPFlagBase & HAFlagBase & HblockBaseMapped &
                                 HblockBaseAccMapped & HstartBase & HendBase & HnoPDFlagBase & HlookupBlockBases &
                                 HPFlagBases & HAFlagBases & HblockBaseMappeds & HstartBases & HendBases &
                                 HnoPDFlagBases).
         assert(HaddrInBlockBase: In addr (getAllPaddrAux [blockBase] s)).
         {
           simpl. rewrite HlookupBlockBases. rewrite app_nil_r.
           unfold bentryStartAddr in HstartBases. unfold bentryEndAddr in HendBases.
           rewrite HlookupBlockBases in *. rewrite <-HstartBases. rewrite <-HendBases.
           unfold bentryStartAddr in HstartBlockAddr. unfold bentryEndAddr in HendBlockAddr.
           rewrite HlookupBlockAddr in *. rewrite <-HstartBlockAddr in HaddrInBlock.
           rewrite <-HendBlockAddr in HaddrInBlock. assumption.
         }
         apply addrInAccessibleBlockIsAccessibleMapped with blockBase; assumption.
      -- assert(HnotEdgeCase: pdbasepartition <> constantRootPartM /\ pdbasepartition <> pdbasepartition
             \/ ~In addr (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry))))
         by intuition.
         specialize(HpartialAccess parent pdbasepartition addr HnotEdgeCase HparentIsPart HchildIsChild
                     HaddrAccMappedParent HaddrMappedChild).
         assumption.
    * (* child <> pdbasepartition *)
      rewrite <-beqAddrFalse in HbeqChildBase.
      assert(HnotEdgeCase: child <> constantRootPartM /\ child <> pdbasepartition
          \/ ~In addr (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry))))
      by intuition.
      specialize(HpartialAccess parent child addr HnotEdgeCase HparentIsPart HchildIsChild
                  HaddrAccMappedParent HaddrMappedChild).
      assumption.
  (*lastPart properties*)
  + exists constantRootPartM. exists pdentryPart. split. assumption. split. assumption. left.
    assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    specialize(HparentOfPart constantRootPartM pdentryPart HlookupPart).
    destruct HparentOfPart as (_ & HparentOfRoot & _).
    assert(HeqTriv: constantRootPartM = constantRootPartM) by reflexivity. specialize(HparentOfRoot HeqTriv).
    assumption.
- rewrite <-beqAddrFalse in HbeqBaseRoot. eapply bindRev.
  { (** MAL.readPDParent and MAL.getPDTRecordField **)
    unfold MAL.readPDParent. eapply weaken. eapply getPDTRecordField.
    intros s Hprops. simpl.
    destruct Hprops as (HPI & HKDI & HVS & Hconsist1 & HnoDup & Hshared & HaddrRange & HchildBlockProps &
                        HnoChild & HparentsListLength & HstartMappedPart & (s0 & (pdparent & (statesList &
                        (parentsList & (HPIs0 & HKDIs0 & HVSs0 & HPs0 & Hconsists0 & HisParentsList & HsIsLast &
                        HpartIsLast & HPDBase & HlookupPart & HbaseIsPart & HpartIsPart & HblockBase & HblockPart
                        & HpartialAccess & HisBuilt & Haccesss0)))))).
    destruct HlookupPart as [entry (HlookupPart & HpropsOrPart)]. exists entry.
    split. assumption.
    instantiate(1:= fun (parentEntry: paddr) (s: state) =>
                    partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency1 s
                    /\ noDupUsedPaddrList s
                    /\ sharedBlockPointsToChild s
                    /\ adressesRangePreservedIfOriginAndNextOk s
                    /\ childsBlocksPropsInParent s
                    /\ noChildImpliesAddressesNotShared s
                    /\ (forall parentsList, isParentsList s parentsList partition
                                             -> length parentsList < S timeout)
                    /\ In startaddr (getMappedPaddr parentEntry s)
                    /\ exists s0 pdparent statesList parentsList pdentryBase pdentry,
                          partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\ P s0
                          /\ consistency s0
                          /\ isParentsList s0 parentsList pdbasepartition
                          /\ s = last statesList s0
                          /\ partition = last parentsList pdbasepartition
                          /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase)
                          /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase)
                          /\ In pdbasepartition (getPartitions multiplexer s0)
                          /\ parentEntry = pdentry.(parent)
                          /\ lookup partition (memory s) beqAddr = Some (PDT pdentry)
                          /\ In partition (getPartitions multiplexer s0)
                          /\ partition <> constantRootPartM
                          /\ pdparent = parent pdentry
                          /\ (exists blockBase bentryBase bentryBases0,
                                  lookup blockBase (memory s0) beqAddr = Some (BE bentryBases0)
                                  /\ bentryPFlag blockBase true s0
                                  /\ bentryAFlag blockBase true s0
                                  /\ In blockBase (getMappedBlocks pdbasepartition s0)
                                  /\ In blockBase (getAccessibleMappedBlocks pdbasepartition s0)
                                  /\ bentryStartAddr blockBase startaddr s0
                                  /\ bentryEndAddr blockBase endaddr s0
                                  /\ false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
                                  /\ lookup blockBase (memory s) beqAddr = Some (BE bentryBase)
                                  /\ bentryPFlag blockBase true s
                                  /\ bentryAFlag blockBase true s
                                  /\ In blockBase (getMappedBlocks pdbasepartition s)
                                  /\ bentryStartAddr blockBase startaddr s
                                  /\ bentryEndAddr blockBase endaddr s
                                  /\ false = checkChild blockBase s (CPaddr (blockBase + sh1offset)))
                          /\ (exists blockPart bentryPart,
                                  lookup blockPart (memory s) beqAddr = Some (BE bentryPart)
                                  /\ bentryPFlag blockPart true s
                                  /\ In blockPart (getMappedBlocks partition s)
                                  /\ bentryStartAddr blockPart startaddr s
                                  /\ bentryEndAddr blockPart endaddr s
                                  /\ false = checkChild blockPart s (CPaddr (blockPart + sh1offset)))
                          /\ (exists blockaddr bentry,
                                lookup blockaddr (memory s) beqAddr = Some (BE bentry)
                                /\ bentryPFlag blockaddr true s
                                /\ (flag = true -> bentryAFlag blockaddr true s)
                                /\ In blockaddr (getMappedBlocks partition s)
                                /\ bentryStartAddr blockaddr startaddr s
                                /\ bentryEndAddr blockaddr endaddr s
                                /\ (s = s0 \/
                                    (forall parent child addr,
                                            ((child <> partition /\ child <> pdbasepartition)
                                                \/ ~ In addr (getAllPaddrAux [blockaddr] s))
                                            -> In parent (getPartitions multiplexer s)
                                            -> In child (getChildren parent s)
                                            -> In addr (getAccessibleMappedPaddr parent s)
                                            -> In addr (getMappedPaddr child s)
                                            -> In addr (getAccessibleMappedPaddr child s))))
                          /\ isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition startaddr
                                endaddr flag
                          /\ accessibleParentPaddrIsAccessibleIntoChild s0).
    simpl.
    assert(In startaddr (getMappedPaddr (parent entry) s)).
    {
      assert(HchildPaddr: childPaddrIsIntoParent s).
      { apply blockInclImpliesAddrIncl; unfold consistency1 in *; intuition. }
      assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
      specialize(HparentOfPart partition entry HlookupPart).
      destruct HparentOfPart as (HparentIsPart & _ & HparentNotPart). specialize(HparentIsPart HbeqBaseRoot).
      destruct HparentIsPart as (HlookupParent & HparentIsPart).
      assert(In partition (getChildren (parent entry) s)).
      {
        assert(HisChild: isChild s) by (unfold consistency1 in *; intuition). unfold isChild in HisChild.
        apply HisChild.
        assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
        {
          destruct HblockBase as [blockBase [bentryBase [bentryBases0 HblockBase]]]. unfold consistency in *.
          unfold consistency1 in Hconsists0. unfold consistency2 in Hconsists0.
          apply getPartitionsEqBuiltWithWriteAcc with statesList parentsList startaddr endaddr pdbasepartition
              flag blockBase bentryBases0; intuition.
        }
        rewrite HgetPartsEq. assumption.
        unfold pdentryParent. rewrite HlookupPart. reflexivity.
      }
      unfold childPaddrIsIntoParent in HchildPaddr. apply HchildPaddr with partition; assumption.
    }
    intuition. exists s0. exists pdparent. exists statesList. exists parentsList.
    destruct HPDBase as [pdentryBase (HlookupBases & HlookupBases0)].
    exists pdentryBase. exists entry. intuition.
  }
  intro pdParent. eapply bindRev.
  { (** Internal.findBlockInKS **)
    eapply weaken. eapply findExactBlockInKS.
    simpl. intros s Hprops. split. eapply Hprops.
    destruct Hprops as (HPI & HKDI & HVS & Hconsist1 & HnoDup & Hshared & HaddrRange & HchildBlockProps &
                        HnoChild & HparentsListLength & HstartMappedParent & (s0 &
                        (pdparent & (statesList & (parentsList & (pdentryBase & (pdentry &
                        (HPIs0 & HKDIs0 & HVSs0 & HPs0 & Hconsists0 & HisParentsList & HsIsLast & HpartIsLast &
                        HlookupBases & HlookupBases0 & HbaseIsPart & Hparent & HlookupPart & HpartIsPart &
                        HpartNotRoot & HpdparentIsParent & HblockBase & HblockPart & HpartialAccess & HisBuilt &
                        Haccesss0)))))))).
    split. assumption. split. assumption. unfold isPDT. rewrite Hparent.
    assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    unfold parentOfPartitionIsPartition in HparentOfPart.
    specialize(HparentOfPart partition pdentry HlookupPart).
    destruct HparentOfPart as [HparentOfPart HparentRoot].
    specialize(HparentOfPart HbeqBaseRoot).
    destruct HparentOfPart as ([childEntry HlookupParent] & _).
    rewrite HlookupParent. split. trivial. unfold getMappedPaddr in HstartMappedParent.
    unfold getMappedBlocks in HstartMappedParent. rewrite <-Hparent. assumption.
  }
  intro blockInParentPartitionAddr. simpl. eapply bindRev.
  { apply compareAddrToNull. }
  intro addrIsNull. destruct addrIsNull eqn:HaddrIsNull.
  * (* addrIsNull = true *)
    eapply weaken. eapply WP.ret.
    simpl. intros s Hprops.
    destruct Hprops as [((HPI & HKDI & HVS & Hconsist1Copy & HnoDup & Hshared & HaddrRange & HchildBlockProps &
                        HnoChild & HparentsListLength & HstartMappedPart & Hpropss0) & Hconsist1 & HblockProps)
                        HbeqNullBlock].
    destruct Hpropss0 as [s0 (pdparent & (statesList & (parentsList & (pdentryBase & (pdentry &
                          (HPIs0 & HKDIs0 & HVSs0 & HPs0 & Hconsists0 & HisParentsList & HsIsLast & HpartIsLast &
                          HlookupBases & HlookupBases0 & HbaseIsPart & Hparent & HlookupPart & HpartIsPart &
                          HpartNotRoot & HpdparentIsParent & HbaseBlock & HblockPart & HpartialAccess & HisBuilt
                          & Haccesss0))))))]. rewrite <-DTL.beqAddrTrue in HbeqNullBlock.
    split. assumption. split. assumption. split. assumption.
    exists s0. exists pdentryBase. exists statesList. exists parentsList.
    intuition.
    + destruct HpartialAccess as [blockaddr [bentryAddr (HlookupBlockaddr & HPFlagAddr & HAFlagAddr &
            HblockaddrIsMappedPart & HstartAddr & HendAddr & HpartialAccess)]].
      destruct HblockProps as [block [blockstart [blockend (Hstart & Hend & HPFlag & HblockIsMappedParent &
            HpropsOrFoundBlock)]]].
      assert(nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in *.
      unfold isPADDR in *.
      destruct HpropsOrFoundBlock as [HpropsFoundBlock | (Hcontra & _)]; try(exfalso; subst block;
            subst blockInParentPartitionAddr; unfold bentryPFlag in HPFlag;
            destruct (lookup nullAddr (memory s) beqAddr); try(congruence); destruct v; congruence).
      destruct HpropsFoundBlock as (_ & HstartInBlock & HboundsWrong). apply andb_false_iff in HboundsWrong.
      rewrite <-beqAddrFalse in HboundsWrong. rewrite <-beqAddrFalse in HboundsWrong.
      assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
      specialize(HparentOfPart partition pdentry HlookupPart).
      destruct HparentOfPart as (HparentIsPart & _ & HparentNotPart). specialize(HparentIsPart HpartNotRoot).
      destruct HparentIsPart as (HlookupParent & HparentIsPart).
      assert(HisChild: isChild s) by (unfold consistency1 in *; intuition).
      assert(HgetPartsEq: getPartitions multiplexer s = getPartitions multiplexer s0).
      {
        destruct HbaseBlock as [blockBase [bentryBase [bentryBases0 HbaseBlock]]]. unfold consistency in *.
        unfold consistency1 in Hconsists0. unfold consistency2 in Hconsists0.
        apply getPartitionsEqBuiltWithWriteAcc with statesList parentsList startaddr endaddr pdbasepartition
              flag blockBase bentryBases0; intuition.
      }
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s)).
      {
        unfold isChild in HisChild. apply HisChild.
        rewrite HgetPartsEq. assumption.
        unfold pdentryParent. rewrite HlookupPart. reflexivity.
      }
      assert(HblockEquiv: blockInChildHasAtLeastEquivalentBlockInParent s)
          by (unfold consistency1 in *; intuition).
      rewrite <-Hparent in *. specialize(HblockEquiv pdParent partition blockaddr startaddr endaddr HparentIsPart
          HpartIsChild HblockaddrIsMappedPart HstartAddr HendAddr HPFlagAddr).
      destruct HblockEquiv as [blockParent [startParent [endParent (HblockParentMapped & HstartParent &
          HendParent & HstartOk & HendOk)]]].
      assert(Heq: blockParent = block).
      {
        assert(HPDT: isPDT pdParent s) by (unfold isPDT; destruct HlookupParent as (parentEntry & HlookupParent);
            rewrite HlookupParent; trivial).
        specialize(HnoDup pdParent HPDT). unfold getUsedPaddr in HnoDup. apply Lib.NoDupSplit in HnoDup.
        destruct HnoDup as (_ & HnoDup).
        apply NoDupAddrImpliesEq with startaddr (getMappedBlocks pdParent s) s; try(assumption); simpl.
        assert(HwellFormedBlock: wellFormedBlock s) by (unfold consistency1 in *; intuition).
        unfold getMappedBlocks in HblockParentMapped.
        apply InFilterPresentInListAndPresent in HblockParentMapped.
        destruct HblockParentMapped as (_ & HPFlagParent).
        specialize(HwellFormedBlock blockParent startParent endParent HPFlagParent HstartParent HendParent).
        destruct HwellFormedBlock as (HstartWell & _).
        assert(HwellFormedBlock: wellFormedBlock s) by (unfold consistency1 in *; intuition).
        unfold getMappedBlocks in HblockIsMappedParent.
        apply InFilterPresentInListAndPresent in HblockIsMappedParent.
        destruct HblockIsMappedParent as (_ & HPFlagParentBis).
        specialize(HwellFormedBlock blockaddr startaddr endaddr HPFlagAddr HstartAddr HendAddr).
        destruct HwellFormedBlock as (HendWell & _).
        unfold bentryStartAddr in HstartParent. unfold bentryEndAddr in HendParent.
        destruct (lookup blockParent (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite app_nil_r. rewrite <-HstartParent. rewrite <-HendParent.
        apply getAllPaddrBlockIncl; try(assumption). lia.
        unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend.
        destruct (lookup block (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend.
        assumption.
      }
      subst blockParent.
      assert(HboundsEq: startParent = blockstart /\ endParent = blockend).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        destruct (lookup block (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). subst blockstart. subst blockend. subst startParent.
        subst endParent. split; reflexivity.
      }
      destruct HboundsEq. subst startParent. subst endParent.
      specialize(HchildBlockProps partition pdParent blockaddr startaddr endaddr block blockstart blockend
          HparentIsPart HpartIsChild HblockaddrIsMappedPart HstartAddr HendAddr HPFlagAddr HblockIsMappedParent
          Hstart Hend HPFlag HstartOk HendOk).
      destruct HchildBlockProps as (_ & _ & _ & HAFlag). specialize(HAFlag HboundsWrong).
      destruct HpartialAccess as [HstatesEq | HpartialAccess]; try(rewrite HstatesEq; assumption).
      intros parentPart child addr HparentPartIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
      specialize(HpartialAccess parentPart child addr). rewrite HlookupBlockaddr in HpartialAccess.
      assert(HboundsBlock: startaddr = startAddr (blockrange bentryAddr)
                          /\ endaddr = endAddr (blockrange bentryAddr)).
      {
        unfold bentryStartAddr in HstartAddr. unfold bentryEndAddr in HendAddr. rewrite HlookupBlockaddr in *.
        split; assumption.
      }
      destruct HboundsBlock as (HstartBlock & HendBlock). rewrite <-HstartBlock in HpartialAccess.
      rewrite <-HendBlock in HpartialAccess. rewrite app_nil_r in HpartialAccess.
      set(Q:= In addr (getAllPaddrBlock startaddr endaddr)).
      assert(HpropsOrAddr: Q \/ ~Q) by (apply Classical_Prop.classic). subst Q.
      destruct (beqAddr child pdbasepartition) eqn:HbeqChildBase.
      --- rewrite <-DTL.beqAddrTrue in HbeqChildBase. subst child.
          destruct HpropsOrAddr as [HaddrInBlock | HaddrNotInBlock].
          -- destruct HbaseBlock as [baseBlock [bentryBase [bentryBases0 (_ & _ & _ & _ & _ & _ & _ & _ &
                HlookupBlockBases & HPFlagBase & HAFlagBase & HblockBaseMapped & HstartBase & HendBase & _)]]].
             apply addrInAccessibleBlockIsAccessibleMapped with baseBlock; try(assumption). simpl.
             unfold bentryStartAddr in HstartBase. unfold bentryEndAddr in HendBase.
             rewrite HlookupBlockBases in *. rewrite app_nil_r. rewrite <-HstartBase. rewrite <-HendBase.
             assumption.
          -- assert(HnotEdgeCase: (pdbasepartition = partition -> False)
                                    /\ (pdbasepartition = pdbasepartition -> False)
                                  \/ (In addr (getAllPaddrBlock startaddr endaddr) -> False))
                by (right; intuition).
             specialize(HpartialAccess HnotEdgeCase HparentPartIsPart HchildIsChild HaddrAccMappedParent
                  HaddrMappedChild). assumption.
      --- rewrite <-beqAddrFalse in HbeqChildBase. destruct (beqAddr child partition) eqn:HbeqChildPart.
          -- rewrite <-DTL.beqAddrTrue in HbeqChildPart. subst child.
             destruct HpropsOrAddr as [HaddrInBlock | HaddrNotInBlock].
             ++ assert(HsameParent: pdParent = parentPart).
                {
                  apply uniqueParent with partition s; try(assumption). unfold consistency1 in *; intuition.
                  rewrite HgetPartsEq. assumption.
                }
                subst parentPart. assert(bentryAFlag block true s).
                {
                  apply addrInAccessibleMappedIsAccessible with pdParent addr; try(assumption). simpl.
                  unfold bentryStartAddr in Hstart. unfold bentryEndAddr in Hend.
                  destruct (lookup block (memory s) beqAddr); try(exfalso; congruence).
                  destruct v; try(exfalso; congruence). rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend.
                  pose proof (getAllPaddrBlockInclRev addr startaddr endaddr HaddrInBlock) as HtmpRes.
                  destruct HtmpRes as (HleftBound & HrightBound & HrangePos).
                  apply getAllPaddrBlockIncl; lia.
                }
                unfold bentryAFlag in *. exfalso. destruct (lookup block (memory s) beqAddr); try(congruence).
                destruct v; congruence.
             ++ assert(HnotEdgeCase: (partition = partition -> False)
                                      /\ (partition = pdbasepartition -> False)
                                    \/ (In addr (getAllPaddrBlock startaddr endaddr) -> False))
                    by (right; intuition).
                 specialize(HpartialAccess HnotEdgeCase HparentPartIsPart HchildIsChild HaddrAccMappedParent
                      HaddrMappedChild). assumption.
          -- rewrite <-beqAddrFalse in HbeqChildPart.
             assert(HnotEdgeCase: (child = partition -> False) /\ (child = pdbasepartition -> False)
                                    \/ (In addr (getAllPaddrBlock startaddr endaddr) -> False))
                by (left; intuition).
             specialize(HpartialAccess HnotEdgeCase HparentPartIsPart HchildIsChild HaddrAccMappedParent
                  HaddrMappedChild). assumption.
    + exists partition. exists pdentry. split. assumption. split. assumption. right. rewrite <-Hparent.
      intros block HblockMappedParent HblockBounds. destruct HblockBounds as (HstartBlock & HendBlock).
      destruct HblockProps as [blockParent [startParent [endParent (HstartParent & HendParent & HPFlagParent &
        HblockParentMapped & HblockParentPropsOr)]]].
      assert(HbeqBlocks: blockParent <> blockInParentPartitionAddr).
      {
        intro Hcontra. rewrite <-HbeqNullBlock in Hcontra. subst blockParent.
        assert(Hnull: nullAddrExists s) by (unfold consistency1 in *; intuition). unfold nullAddrExists in Hnull.
        unfold isPADDR in Hnull. unfold bentryStartAddr in HstartParent.
        destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
      }
      destruct HblockParentPropsOr as [(_ & HstartInBlockParent & HboundsWrong) | Hcontra];
        try(destruct Hcontra; congruence).
      assert(HstartInBlockParentAddr: In startaddr (getAllPaddrAux [blockParent] s)).
      {
        simpl. unfold bentryStartAddr in HstartParent. unfold bentryEndAddr in HendParent.
        destruct (lookup blockParent (memory s) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartParent. rewrite <-HendParent.
        assumption.
      }
      assert(HstartInBlock: In startaddr (getAllPaddrAux [block] s)).
      {
        assert(HPFlagBlock: bentryPFlag block true s).
        {
          pose proof (mappedBlockIsBE block pdParent s HblockMappedParent) as Hres.
          destruct Hres as [bentry (HlookupBlock & Hpresent)]. unfold bentryPFlag. rewrite HlookupBlock.
          apply eq_sym. assumption.
        }
        assert(HwellFormed: wellFormedBlock s) by (unfold consistency1 in *; intuition).
        specialize(HwellFormed block startaddr endaddr HPFlagBlock HstartBlock HendBlock).
        destruct HwellFormed as (HwellFormed & _). simpl. unfold bentryStartAddr in HstartBlock.
        unfold bentryEndAddr in HendBlock. destruct (lookup block (memory s) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-HstartBlock. rewrite <-HendBlock.
        apply getAllPaddrBlockIncl; lia.
      }
      assert(HparentIsPDT: isPDT pdParent s).
      {
        unfold isPDT. unfold getMappedBlocks in HblockMappedParent. unfold getKSEntries in HblockMappedParent.
        destruct (lookup pdParent (memory s) beqAddr); try(simpl in HblockMappedParent; congruence).
        destruct v; try(simpl in HblockMappedParent; congruence). trivial.
      }
      pose proof (DisjointPaddrInPart pdParent blockParent block startaddr s HnoDup HparentIsPDT
        HblockParentMapped HblockMappedParent) as Hcontra.
      destruct (beqAddr blockParent block) eqn:HbeqBlockParentBlock.
      -- rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlock. subst block. apply andb_false_iff in HboundsWrong.
         rewrite <-beqAddrFalse in HboundsWrong. rewrite <-beqAddrFalse in HboundsWrong.
         destruct HboundsWrong as [HstartWrong | HendWrong].
         ++ unfold bentryStartAddr in *. destruct (lookup blockParent (memory s) beqAddr); try(congruence).
            destruct v; congruence.
         ++ unfold bentryEndAddr in *. destruct (lookup blockParent (memory s) beqAddr); try(congruence).
            destruct v; congruence.
      -- rewrite <-beqAddrFalse in HbeqBlockParentBlock.
         specialize(Hcontra HbeqBlockParentBlock HstartInBlockParentAddr). congruence.
  * (* addrIsNull = false *)
    eapply bindRev.
    { (** MAL.writeBlockAccessibleFromBlockEntryAddr **)
      eapply weaken. eapply writeBlockAccessibleFromBlockEntryAddr.
      simpl. intros s Hprops.
      destruct Hprops as [((HPI & HKDI & HVS & Hconsist1Copy & HnoDup & Hshared & HaddrRange & HchildBlockProps &
                          HnoChild & HparentsListLength & HstartIsMappedParent & Hpropss0) & Hconsis1 &
                          HblockProps) HbeqNullBlock].
      destruct Hpropss0 as [s0 (pdparent & (statesList & (parentsList & (pdentryBase & (pdentry
                            & (HPIs0 & HKDIs0 & HVSs0 & HPs0 & Hconsists0 & HisParentsList & HsIsLast &
                            HpartIsLast & HlookupBases & HlookupBases0 & HbaseIsPart & Hparent & HlookupPart &
                            HpartIsPart & HpartNotRoot & HpdparentIsParent & HbaseBlock & HblockPart &
                            HpartialAccess & HisBuilt & Haccesss0))))))].
      rewrite <-beqAddrFalse in HbeqNullBlock. apply not_eq_sym in HbeqNullBlock.
      destruct HblockProps as [block [blockstart [blockend (Hstart & Hend & HPFlag & HblockIsMappedParent &
            HblockProps)]]].
      destruct HblockProps as [(Hcontra & _) | HblockProps]; try(exfalso; congruence).
      destruct HblockProps as (HblocksEq & HstartsEq & HendsEq & _). subst block. rewrite <-DTL.beqAddrTrue in *.
      subst blockstart. subst blockend.
      assert(HlookupBlock: exists bentry, lookup blockInParentPartitionAddr (memory s) beqAddr
                                          = Some (BE bentry)).
      {
        unfold bentryPFlag in HPFlag.
        destruct (lookup blockInParentPartitionAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists b. reflexivity.
      }
      destruct HlookupBlock as [bentry HlookupBlock]. exists bentry. split. assumption.
      assert(HgetPartEq: getPartitions multiplexer s = getPartitions multiplexer s0).
      {
        destruct HbaseBlock as [blockBase [bentryBase [bentryBases0 (HlookupBlockBases0 & HPFlagBases0 &
                                HAFlagBases0 & HblockBaseIsMappeds0 & HblockBaseAccMappeds0 & HstartBases0 &
                                HendBases0 & HcheckBases0 & HlookupBlockBase & HPFlagBase & HAFlagBase &
                                HblockBaseIsMapped & HstartBase & HendBase & HcheckBases)]]].
        unfold consistency in Hconsists0. unfold consistency1 in Hconsists0. unfold consistency2 in Hconsists0.
        apply getPartitionsEqBuiltWithWriteAcc with statesList parentsList startaddr endaddr pdbasepartition
              flag blockBase bentryBases0; intuition.
      }
      assert(HbaseIsParts: In pdbasepartition (getPartitions multiplexer s)).
      { rewrite <-HgetPartEq in HbaseIsPart. assumption. }
      instantiate(1:= fun _ s =>
          (forall parentsList, isParentsList s parentsList partition
                                -> length parentsList < S timeout)
          /\ In startaddr (getMappedPaddr pdParent s)
          /\ exists sInit s0, exists pdentry pdentryBase, exists pdparent statesList parentsList,
              partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\
              exists bentry newBentry: BlockEntry,
                s = {|
                      currentPartition := currentPartition s0;
                      memory :=
                        add blockInParentPartitionAddr
                          (BE
                             (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                                (blockindex bentry) (blockrange bentry))) (memory s0) beqAddr
                    |}
                /\ pdParent = parent pdentry
                /\ pdparent = pdParent
                /\ lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
                /\ lookup blockInParentPartitionAddr (memory s) beqAddr = Some (BE newBentry)
                /\ bentryPFlag blockInParentPartitionAddr true s0
                /\ In blockInParentPartitionAddr (getMappedBlocks pdparent s0)
                /\ bentryStartAddr blockInParentPartitionAddr startaddr s0
                /\ bentryEndAddr blockInParentPartitionAddr endaddr s0
                /\ bentryPFlag blockInParentPartitionAddr true s
                /\ bentryAFlag blockInParentPartitionAddr flag s
                /\ In blockInParentPartitionAddr (getMappedBlocks pdparent s)
                /\ bentryStartAddr blockInParentPartitionAddr startaddr s
                /\ bentryEndAddr blockInParentPartitionAddr endaddr s
                /\ newBentry = CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                                (blockindex bentry) (blockrange bentry)
                /\ lookup pdbasepartition (memory sInit) beqAddr = Some (PDT pdentryBase)
                /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase)
                /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase)
                /\ getPartitions multiplexer s0 = getPartitions multiplexer sInit
                /\ In pdbasepartition (getPartitions multiplexer s0)
                /\ lookup partition (memory s0) beqAddr = Some (PDT pdentry)
                /\ lookup partition (memory s) beqAddr = Some (PDT pdentry)
                /\ In partition (getPartitions multiplexer s0)
                /\ getPartitions multiplexer s = getPartitions multiplexer s0
                /\ partition <> constantRootPartM
                /\ consistency1 s0
                /\ noDupUsedPaddrList s0
                /\ sharedBlockPointsToChild s0
                /\ adressesRangePreservedIfOriginAndNextOk s0
                /\ childsBlocksPropsInParent s0
                /\ noChildImpliesAddressesNotShared s0
                /\ isParentsList sInit parentsList pdbasepartition
                /\ s0 = last statesList sInit
                /\ partition = last parentsList pdbasepartition
                /\ (exists blockBase bentryBase bentryBases0,
                        lookup blockBase (memory sInit) beqAddr = Some (BE bentryBases0)
                        /\ bentryPFlag blockBase true sInit
                        /\ bentryAFlag blockBase true sInit
                        /\ In blockBase (getMappedBlocks pdbasepartition sInit)
                        /\ In blockBase (getAccessibleMappedBlocks pdbasepartition sInit)
                        /\ bentryStartAddr blockBase startaddr sInit
                        /\ bentryEndAddr blockBase endaddr sInit
                        /\ false = checkChild blockBase sInit (CPaddr (blockBase + sh1offset))
                        /\ lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
                        /\ bentryPFlag blockBase true s0
                        /\ bentryAFlag blockBase true s0
                        /\ In blockBase (getMappedBlocks pdbasepartition s0)
                        /\ bentryStartAddr blockBase startaddr s0
                        /\ bentryEndAddr blockBase endaddr s0
                        /\ false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset)))
                /\ (exists blockPart bentryPart,
                        lookup blockPart (memory s) beqAddr = Some (BE bentryPart)
                        /\ bentryPFlag blockPart true s
                        /\ In blockPart (getMappedBlocks partition s)
                        /\ bentryStartAddr blockPart startaddr s
                        /\ bentryEndAddr blockPart endaddr s
                        /\ false = checkChild blockPart s (CPaddr (blockPart + sh1offset)))
                /\ (exists (blockaddr : paddr) (bentry : BlockEntry),
                        lookup blockaddr (memory s) beqAddr = Some (BE bentry) /\
                        bentryPFlag blockaddr true s /\
                        bentryAFlag blockaddr flag s /\
                        In blockaddr (getMappedBlocks pdparent s) /\
                        bentryStartAddr blockaddr startaddr s /\
                        bentryEndAddr blockaddr endaddr s /\
                        (forall parent child addr : paddr,
                             ((child <> pdparent /\ child <> pdbasepartition)
                                \/ ~ In addr (getAllPaddrAux [blockaddr] s))
                             -> In parent (getPartitions multiplexer s)
                             -> In child (getChildren parent s)
                             -> In addr (getAccessibleMappedPaddr parent s)
                             -> In addr (getMappedPaddr child s)
                             -> In addr (getAccessibleMappedPaddr child s)))
                /\ partitionsIsolation sInit /\ kernelDataIsolation sInit /\ verticalSharing sInit /\ P sInit
                /\ consistency sInit
                /\ isBuiltFromWriteAccessibleRec sInit s0 statesList parentsList pdbasepartition startaddr endaddr
                      flag
                /\ accessibleParentPaddrIsAccessibleIntoChild sInit
      ).
      simpl. set (s' := {| currentPartition :=  _|}).
      set(newBentry := CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                            (blockindex bentry) (blockrange bentry)).
      destruct (beqAddr blockInParentPartitionAddr pdbasepartition) eqn:HbeqBlockBase.
      {
        rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqBlockBase. rewrite HbeqBlockBase in *.
        congruence.
      }
      destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart.
      {
        rewrite <-DependentTypeLemmas.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *.
        congruence.
      }
      assert(HlookupBlocks': lookup blockInParentPartitionAddr (memory s') beqAddr = Some (BE newBentry)).
      { simpl. rewrite beqAddrTrue. subst newBentry. reflexivity. }
      assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
      assert(HgetMappedEq: getMappedBlocks pdparent s' = getMappedBlocks pdparent s).
      {
        subst s'. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
        reflexivity.
      }
      assert(HgetPartitionsEq: getPartitions multiplexer s' = getPartitions multiplexer s).
      {
        subst s'. apply getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange
                      with bentry (CPaddr (blockInParentPartitionAddr + sh1offset));
                    try(unfold consistency1 in Hconsis1; intuition; congruence).
        - unfold sh1entryAddr. rewrite HlookupBlock. reflexivity.
        - simpl.
          destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
                   eqn:HbeqBlocBlockSh1.
          {
            assert(HwellFormed: wellFormedFstShadowIfBlockEntry s) by (unfold consistency1 in *; intuition).
            unfold wellFormedFstShadowIfBlockEntry in HwellFormed.
            assert(Hsh1IsSHE: isSHE (CPaddr (blockInParentPartitionAddr + sh1offset)) s).
            { apply HwellFormed. unfold isBE. rewrite HlookupBlock. trivial. }
            rewrite <-DTL.beqAddrTrue in HbeqBlocBlockSh1. rewrite <-HbeqBlocBlockSh1 in *.
            unfold isSHE in Hsh1IsSHE. rewrite HlookupBlock in Hsh1IsSHE. exfalso; congruence.
           }
          rewrite <-beqAddrFalse in HbeqBlocBlockSh1. rewrite removeDupIdentity; intuition.
        - unfold CBlockEntry.
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
          reflexivity.
        - unfold CBlockEntry.
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
          reflexivity.
      }
      assert(HparentsEq: pdparent = pdParent).
      { rewrite HpdparentIsParent. rewrite Hparent. reflexivity. }
      rewrite <-HparentsEq in *.
      assert(HlookupParent: exists pdentryParent, lookup pdparent (memory s) beqAddr = Some(PDT pdentryParent)).
      {
        assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
        specialize(HparentOfPart partition pdentry HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
        specialize(HparentIsPart HpartNotRoot). rewrite Hparent. destruct HparentIsPart. assumption.
      }
      destruct HlookupParent as [pdentryPdparent HlookupParent].
      destruct HbaseBlock as [blockBase [bentryBase [bentryBases0 (HlookupBlockBases0 & HPFlagBases0 &
                              HAFlagBases0 & HblockBaseIsMappeds0 & HblockBaseAccMappeds0 & HstartBases0 &
                              HendBases0 & HcheckBases0 & HlookupBlockBase & HPFlagBase & HAFlagBase &
                              HblockBaseIsMapped & HstartBase & HendBase & HcheckBases)]]].
      assert(HparentNotInParentsList: ~In pdparent parentsList).
      {
        assert(HparentsLists: isParentsList s parentsList pdbasepartition).
        {
          unfold consistency in Hconsists0. unfold consistency1 in Hconsists0. unfold consistency2 in Hconsists0.
          apply listWithIsBuiltIsParentsList with s0 statesList startaddr endaddr flag blockBase bentryBases0;
              intuition.
        }
        assert(HparentsListRec: isParentsList s (parentsList++[pdparent]) pdbasepartition).
        {
          apply isParentsListRec with partition pdentryPdparent pdentry; assumption.
        }
        assert(HnoDupList: NoDup (parentsList++[pdparent])).
        {
          unfold consistency1 in Hconsis1.
          apply parentOfPartNotInParentsListsTail with pdbasepartition s; intuition.
        }
        apply NoDup_remove in HnoDupList. rewrite app_nil_r in HnoDupList. destruct HnoDupList. assumption.
      }
      assert(HlookupParentEq: lookup pdparent (memory s) beqAddr = lookup pdparent (memory s0) beqAddr).
      {
        apply lookupPDTEqWriteAccess with statesList parentsList startaddr endaddr flag pdbasepartition;
              try(assumption).
        unfold isPDT. rewrite HlookupBases0. trivial.
        pose proof (stablePDTParentIsBuiltRev statesList s0 parentsList pdbasepartition pdentryPdparent startaddr
                    endaddr flag s pdparent HisBuilt HlookupParent) as HlookupParents0.
        destruct HlookupParents0 as [pdentryParents0 (HlookupParents0 & _)]. unfold isPDT.
        rewrite HlookupParents0. trivial.
      }
      assert(HisBuiltBis: isBuiltFromWriteAccessibleRec s0 s' (statesList++[s']) (parentsList++[pdparent])
                              pdbasepartition startaddr endaddr flag).
      {
        unfold consistency in Hconsists0. unfold consistency1 in Hconsists0. unfold consistency2 in Hconsists0.
        apply isBuiltFromWriteAccessibleRecRec with s s' partition pdentry pdentryPdparent pdentryBase
              blockInParentPartitionAddr bentry newBentry (MPU pdentryPdparent) blockBase; intuition.
        rewrite <-HlookupParentEq. assumption.
      }
      assert(HnoPDFlagA: false = checkChild blockBase s' (CPaddr (blockBase + sh1offset))).
      {
        unfold checkChild in *.
        assert(HblockBaseIsBE: isBE blockBase s) by (unfold isBE; rewrite HlookupBlockBase; trivial).
        assert(HlookupSh1Eq: lookup (CPaddr (blockBase + sh1offset)) (memory s') beqAddr
                              = lookup (CPaddr (blockBase + sh1offset)) (memory s) beqAddr).
        {
          assert(HwellFormedShadow: wellFormedFstShadowIfBlockEntry s) by (unfold consistency1 in *; intuition).
          specialize(HwellFormedShadow blockBase HblockBaseIsBE). unfold isSHE in HwellFormedShadow.
          subst s'. simpl.
          destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockBase + sh1offset)))
              eqn:HbeqBlockBlockSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
            rewrite HlookupBlock in HwellFormedShadow. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
        }
        rewrite HlookupSh1Eq. subst s'. simpl.
        destruct (beqAddr blockInParentPartitionAddr blockBase) eqn:HbeqBlockBlockBase.
        - rewrite HlookupBlockBase in HcheckBases. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockBlockBase. rewrite removeDupIdentity; intuition.
      }
      split.
      {
        intros parentsList2 HparentsList.
        assert(HparentsLists: isParentsList s parentsList2 partition).
        {
          apply isParentsListEqBERev with blockInParentPartitionAddr newBentry bentry; try(subst s'; assumption).
          exists pdentry. assumption.
          unfold consistency1 in *; intuition.
        }
        specialize(HparentsListLength parentsList2 HparentsLists). assumption.
      }
      split.
      {
        assert(HgetMappedPaddrEq: getMappedPaddr pdparent s' = getMappedPaddr pdparent s).
        {
          assert(blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
          subst s'. apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
                try(assumption);
                try(unfold CBlockEntry;
                    destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia); simpl;
                    reflexivity).
          unfold isPDT. rewrite HlookupParent. trivial.
        }
        rewrite HgetMappedPaddrEq. assumption.
      }
      exists s0. exists s. exists pdentry. exists pdentryBase. exists pdparent.
      exists statesList. exists parentsList. split. assumption. split. assumption. split. assumption.
      exists bentry. rewrite HgetMappedEq.
      exists newBentry. rewrite beqAddrTrue. rewrite <-beqAddrFalse in HbeqBlockBase.
      rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; try(apply not_eq_sym; assumption).
      rewrite removeDupIdentity; try(apply not_eq_sym; assumption). intuition.
      unfold bentryPFlag in *. rewrite HlookupBlocks'. rewrite HlookupBlock in HPFlag.
      subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption.
      unfold bentryAFlag in *. rewrite HlookupBlocks'. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      reflexivity.
      unfold bentryStartAddr in *. rewrite HlookupBlocks'. rewrite HlookupBlock in Hstart. subst newBentry.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. intuition.
      unfold bentryEndAddr in *. rewrite HlookupBlocks'. rewrite HlookupBlock in Hend. subst newBentry.
      unfold CBlockEntry. destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
      simpl. intuition.
      rewrite HgetPartEq. assumption.
      assert(HlookupParents0: lookup pdparent (memory s0) beqAddr = Some (PDT pdentryPdparent)).
      {
        rewrite HlookupParentEq in HlookupParent. assumption.
      }
      destruct (beqAddr blockInParentPartitionAddr blockBase) eqn:HbeqBlockBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
        assert(HbeqBaseParent: pdbasepartition <> pdparent).
        {
          assert(Htree: partitionTreeIsTree s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
          assert(HparentOfPart: parentOfPartitionIsPartition s0)
                      by (unfold consistency in *; unfold consistency1 in *; intuition).
          apply basePartNotLastInParentsLists with (parentsList++[pdparent]) s0; try(assumption).
          - apply parentsListCons with partition; try(assumption). simpl. rewrite HlookupParents0. split.
            assumption. split; trivial. rewrite Hparent. apply stablePDTParentIsBuiltRev with statesList
                  parentsList pdbasepartition startaddr endaddr flag s; assumption.
          - apply eq_sym. apply last_last.
          - intro Hcontra. apply app_eq_nil in Hcontra. destruct Hcontra. congruence.
        }
        assert(HbaseIsPDT: isPDT pdbasepartition s).
        { unfold isPDT. rewrite HlookupBases. trivial. }
        assert(HpdparentIsPDT: isPDT pdparent s).
        {
          unfold getMappedBlocks in HblockIsMappedParent. unfold getKSEntries in HblockIsMappedParent.
          unfold isPDT.
          destruct (lookup pdparent (memory s) beqAddr); try(simpl in HblockIsMappedParent; congruence).
          destruct v; try(simpl in HblockIsMappedParent; congruence).
          trivial.
        }
        specialize(Hdisjoint pdbasepartition pdparent HbaseIsPDT HpdparentIsPDT HbeqBaseParent).
        destruct Hdisjoint as [entriesList1 [entriesList2 (Hlist1 & Hlist2 & Hdisjoint)]].
        subst entriesList1. subst entriesList2.
        unfold getMappedBlocks in *. apply InFilterPresentInList in HblockIsMappedParent.
        apply InFilterPresentInList in HblockBaseIsMapped. specialize(Hdisjoint blockBase HblockBaseIsMapped).
        exfalso; congruence.
      }
      assert(HlookupBlockBases': lookup blockBase (memory s') beqAddr = Some(BE bentryBase)).
      {
        subst s'. simpl. rewrite HbeqBlockBlock. rewrite <-beqAddrFalse in HbeqBlockBlock.
        rewrite removeDupIdentity; intuition.
      }
      assert(HPFlagBases': bentryPFlag blockBase true s').
      {
        unfold bentryPFlag in *. rewrite HlookupBlockBases'. rewrite HlookupBlockBase in HPFlagBase.
        assumption.
      }
      assert(HAFlagBases': bentryAFlag blockBase true s').
      {
        unfold bentryAFlag in *. rewrite HlookupBlockBases'. rewrite HlookupBlockBase in HAFlagBase.
        assumption.
      }
      assert(HblockBaseIsMappeds': In blockBase (getMappedBlocks pdbasepartition s')).
      {
        assert(HgetMappedBaseEq: getMappedBlocks pdbasepartition s' = getMappedBlocks pdbasepartition s).
        {
          subst s'. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
          reflexivity.
        }
        rewrite HgetMappedBaseEq. assumption.
      }
      assert(HstartBases': bentryStartAddr blockBase startaddr s').
      {
        unfold bentryStartAddr in *. rewrite HlookupBlockBases'. rewrite HlookupBlockBase in HstartBase.
        assumption.
      }
      assert(HendBases': bentryEndAddr blockBase endaddr s').
      {
        unfold bentryEndAddr in *. rewrite HlookupBlockBases'. rewrite HlookupBlockBase in HendBase.
        assumption.
      }
      exists blockBase. exists bentryBase. exists bentryBases0. intuition.
      destruct HblockPart as [blockPart [bentryPart (HlookupBlockPart & HPFlagPart & HblockPartMapped &
              HstartPart & HendPart & HcheckPart)]].
      destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
      {
        rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *.
        assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
        assert(HbeqPartParent: partition <> pdparent).
        {
          assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
          specialize(HparentOfPart partition pdentry HlookupPart). rewrite Hparent. intuition.
        }
        assert(HpartIsPDT: isPDT partition s).
        { unfold isPDT. rewrite HlookupPart. trivial. }
        assert(HpdparentIsPDT: isPDT pdparent s).
        {
          unfold getMappedBlocks in HblockIsMappedParent. unfold getKSEntries in HblockIsMappedParent.
          unfold isPDT.
          destruct (lookup pdparent (memory s) beqAddr); try(simpl in HblockIsMappedParent; congruence).
          destruct v; try(simpl in HblockIsMappedParent; congruence).
          trivial.
        }
        specialize(Hdisjoint partition pdparent HpartIsPDT HpdparentIsPDT HbeqPartParent).
        destruct Hdisjoint as [entriesList1 [entriesList2 (Hlist1 & Hlist2 & Hdisjoint)]].
        subst entriesList1. subst entriesList2.
        unfold getMappedBlocks in *. apply InFilterPresentInList in HblockIsMappedParent.
        apply InFilterPresentInList in HblockPartMapped. specialize(Hdisjoint blockPart HblockPartMapped).
        exfalso; congruence.
      }
      assert(HlookupBlockParts': lookup blockPart (memory s') beqAddr = Some(BE bentryPart)).
      {
        subst s'. simpl. rewrite HbeqBlockBlock. rewrite <-beqAddrFalse in HbeqBlockBlock.
        rewrite removeDupIdentity; intuition.
      }
      assert(HPFlagParts': bentryPFlag blockPart true s').
      {
        unfold bentryPFlag in *. rewrite HlookupBlockParts'. rewrite HlookupBlockPart in HPFlagPart.
        assumption.
      }
      assert(HblockPartMappeds': In blockPart (getMappedBlocks partition s')).
      {
        assert(HgetMappedBaseEq: getMappedBlocks partition s' = getMappedBlocks partition s).
        {
          subst s'. apply getMappedBlocksEqBENoChange with bentry. assumption. unfold CBlockEntry.
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
          reflexivity.
        }
        rewrite HgetMappedBaseEq. assumption.
      }
      assert(HstartParts': bentryStartAddr blockPart startaddr s').
      {
        unfold bentryStartAddr in *. rewrite HlookupBlockParts'. rewrite HlookupBlockPart in HstartPart.
        assumption.
      }
      assert(HendParts': bentryEndAddr blockPart endaddr s').
      {
        unfold bentryEndAddr in *. rewrite HlookupBlockParts'. rewrite HlookupBlockPart in HendPart.
        assumption.
      }
      assert(HcheckParts': false = checkChild blockPart s' (CPaddr (blockPart + sh1offset))).
      {
        unfold checkChild in *.
        assert(HblockPartIsBE: isBE blockPart s) by (unfold isBE; rewrite HlookupBlockPart; trivial).
        assert(HlookupSh1Eq: lookup (CPaddr (blockPart + sh1offset)) (memory s') beqAddr
                              = lookup (CPaddr (blockPart + sh1offset)) (memory s) beqAddr).
        {
          assert(HwellFormedShadow: wellFormedFstShadowIfBlockEntry s) by (unfold consistency1 in *; intuition).
          specialize(HwellFormedShadow blockPart HblockPartIsBE). unfold isSHE in HwellFormedShadow.
          subst s'. simpl.
          destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockPart + sh1offset)))
              eqn:HbeqBlockBlockSh1.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in *.
            rewrite HlookupBlock in HwellFormedShadow. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
        }
        rewrite HlookupSh1Eq. subst s'. simpl.
        destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlockPart.
        - rewrite HlookupBlockPart in HcheckPart. assumption.
        - rewrite <-beqAddrFalse in HbeqBlockBlockPart. rewrite removeDupIdentity; intuition.
      }
      exists blockPart. exists bentryPart. rewrite HbeqBlockBlock.
      rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
      exists blockInParentPartitionAddr. exists newBentry. rewrite beqAddrTrue. split. reflexivity. split.
      unfold bentryPFlag in *. rewrite HlookupBlocks'.
      rewrite HlookupBlock in HPFlag. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption. split. unfold bentryAFlag. rewrite HlookupBlocks'. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl. reflexivity.
      split. assumption. split. unfold bentryStartAddr in *. rewrite HlookupBlocks'.
      rewrite HlookupBlock in Hstart. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption. split. unfold bentryEndAddr in *. rewrite HlookupBlocks'.
      rewrite HlookupBlock in Hend. subst newBentry. unfold CBlockEntry.
      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
      assumption.
      intros parent child addr HnotEdgeCase HparentIsPart HchildIsChild HaddrIsMappedAccInParent
            HaddrIsMappedInChild.
      rewrite HgetPartitionsEq in HparentIsPart.
      assert(HgetChildrenEq: getChildren parent s' = getChildren parent s).
      {
        subst s'. apply getChildrenEqBENoStartNoPresentChange with bentry;
                   try(assumption);
                   try(unfold CBlockEntry;
                       destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                       simpl; reflexivity).
        apply partitionsArePDT; try(unfold consistency1 in *; intuition; congruence).
      }
      rewrite HgetChildrenEq in HchildIsChild.
      assert(HpdparentIsPDT: isPDT pdparent s).
      {
        unfold getMappedBlocks in HblockIsMappedParent. unfold getKSEntries in HblockIsMappedParent.
        unfold isPDT.
        destruct (lookup pdparent (memory s) beqAddr); try(simpl in HblockIsMappedParent; congruence).
        destruct v; try(simpl in HblockIsMappedParent; congruence).
        trivial.
      }
      assert(HnewB: exists l,
                    newBentry = {|
                                  read := read bentry;
                                  write := write bentry;
                                  exec := exec bentry;
                                  present := present bentry;
                                  accessible := flag;
                                  blockindex := blockindex bentry;
                                  blockrange := blockrange bentry;
                                  Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                                |}).
      {
        simpl in HlookupBlocks'. rewrite beqAddrTrue in HlookupBlocks'. unfold CBlockEntry in HlookupBlocks'.
        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
        injection HlookupBlocks' as HbentriesEq. exists l. apply eq_sym. assumption.
      }
      destruct HnewB as [l HnewB].
      assert(HgetAccEq: forall partition, partition <> pdparent
                            -> isPDT partition s
                            -> getAccessibleMappedPaddr partition s' = getAccessibleMappedPaddr partition s).
      {
        intros part HpartNotParent HpartIsPDT. subst s'. apply getAccessibleMappedPaddrEqBENotInPart.
        - assumption.
        - unfold isBE. rewrite HlookupBlock. trivial.
        - intro Hcontra. assert(Hdisjoint: DisjointKSEntries s) by (unfold consistency1 in *; intuition).
          unfold DisjointKSEntries in Hdisjoint.
          specialize(Hdisjoint part pdparent HpartIsPDT HpdparentIsPDT HpartNotParent).
          destruct Hdisjoint as [optionEntriesList1 (optionEntriesList2 & (Hlist1 & Hlist2 & Hdisjoint))].
          subst optionEntriesList1. subst optionEntriesList2. unfold Lib.disjoint in Hdisjoint.
          specialize(Hdisjoint blockInParentPartitionAddr Hcontra).
          unfold getMappedBlocks in HblockIsMappedParent.
          induction (filterOptionPaddr (getKSEntries pdparent s)); try(simpl in HblockIsMappedParent; congruence).
          simpl in HblockIsMappedParent. simpl in Hdisjoint. apply Decidable.not_or in Hdisjoint.
          destruct Hdisjoint as [HbeqABlock HdisjointRec]. apply IHl0; try(assumption).
          destruct (lookup a (memory s) beqAddr); try(assumption). destruct v; try(assumption).
          destruct (present b); try(assumption). simpl in HblockIsMappedParent.
          destruct HblockIsMappedParent as [HaIsBlock | Hgoal]; try(exfalso; congruence).
          assumption.
      }
      assert(HchildIsPDT: isPDT child s).
      { apply childrenArePDT with parent; try(unfold consistency1 in *; intuition; congruence). }
      assert(HgetMappedChild: getMappedPaddr child s' = getMappedPaddr child s).
      {
        subst s'. apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
              try(assumption); unfold CBlockEntry;
              destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia); simpl;
              reflexivity.
      }
      rewrite HgetMappedChild in HaddrIsMappedInChild.
      assert(HgetAccMappedParentEq: In addr (getAccessibleMappedPaddr pdparent s') ->
                In addr (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry))
                          ++ (getAccessibleMappedPaddr pdparent s))
                /\ (flag = accessible bentry -> In addr (getAccessibleMappedPaddr pdparent s))
                /\ (flag = false -> ~ In addr (getAllPaddrBlock (startAddr (blockrange bentry))
                                                                (endAddr (blockrange bentry))))).
      {
        intro HaddrIsMapped.
        assert(Heq: forall l flag,
              getAccessibleMappedPaddr pdparent
                 {|
                   currentPartition := currentPartition s;
                   memory :=
                     add blockInParentPartitionAddr
                       (BE
                          (CBlockEntry (read bentry) (write bentry) 
                             (exec bentry) (present bentry) flag (blockindex bentry)
                             (blockrange bentry))) (memory s) beqAddr
                 |} = getAccessibleMappedPaddr pdparent
                         {|
                           currentPartition := currentPartition s;
                           memory :=
                             add blockInParentPartitionAddr
                               (BE
                                  {|
                                    read := read bentry;
                                    write := write bentry;
                                    exec := exec bentry;
                                    present := present bentry;
                                    accessible := flag;
                                    blockindex := blockindex bentry;
                                    blockrange := blockrange bentry;
                                    Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                                  |}) (memory s) beqAddr
                         |}).
        {
          intros l0 flag'. unfold CBlockEntry.
          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
          f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. apply proof_irrelevance.
        }
        destruct (eqb flag (accessible bentry)) eqn:HbeqFlagOldAcc.
        - (* flag = accessible bentry *)
          apply eqb_prop in HbeqFlagOldAcc. subst flag.
          assert(HgetAccMappedEq: getAccessibleMappedPaddr pdparent s' = getAccessibleMappedPaddr pdparent s).
          {
            subst s'. apply getAccessibleMappedPaddrEqBEPresentAccessibleNoChange with bentry;
                  try(assumption);
                  try(unfold CBlockEntry;
                      destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                      simpl; reflexivity).
          }
          rewrite HgetAccMappedEq in HaddrIsMapped. split. apply in_or_app. right. assumption. split. intro.
          assumption. intros HaccessFalse Hcontra.
          assert(HaccessTrue: bentryAFlag blockInParentPartitionAddr true s).
          {
            apply addrInAccessibleMappedIsAccessible with pdparent addr; try(assumption).
            simpl. rewrite HlookupBlock. rewrite app_nil_r. assumption.
          }
          unfold bentryAFlag in HaccessTrue. rewrite HlookupBlock in HaccessTrue. congruence.
        - (* flag <> accessible bentry *)
          apply eqb_false_iff in HbeqFlagOldAcc. split. destruct flag.
          + (* flag = true *)
            subst s'. apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence
                          with blockInParentPartitionAddr newBentry;
                      try(subst newBentry; unfold CBlockEntry;
                        destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                        simpl);
                    try(unfold consistency1 in *; intuition; congruence).
            { unfold bentryPFlag in HPFlag. rewrite HlookupBlock in HPFlag. intuition. }
            {
              unfold getMappedBlocks in HblockIsMappedParent.
              apply DTL.InFilterPresentInList in HblockIsMappedParent. assumption.
            }
          + (* flag = false *)
            destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                  HAFlagBlockAddr & HblockAddrMappedBase & HstartBlockAddr & HendBlockAddr & HpartialAccess))].
            unfold consistency1 in Hconsis1. unfold bentryStartAddr in Hstart.
            unfold bentryEndAddr in Hend. rewrite HlookupBlock in *.
            apply getAccessibleMappedPaddrEqBuiltWithWriteAccFlagFalse with s' [s'] [pdparent] partition blockaddr
                  bentryBlockAddr; try(intuition; congruence).
            assert(Hres: exists partition,
                           partition = last parentsList pdbasepartition
                           /\ (forall blockPart bentryPart,
                                lookup blockPart (memory s) beqAddr = Some (BE bentryPart) ->
                                bentryPFlag blockPart true s ->
                                In blockPart (getMappedBlocks partition s) ->
                                bentryStartAddr blockPart startaddr s ->
                                bentryEndAddr blockPart endaddr s ->
                                false = checkChild blockPart s (CPaddr (blockPart + sh1offset)))).
            {
              unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
              unfold consistency2 in Hconsists0.
              apply baseBlockAccessibleImpliesNoPDWithIsBuilt with s0 statesList false blockBase bentryBases0
                    pdentryBase; try(assumption); intuition.
            }
            destruct Hres as [lastPart (HlastPartIsLast & Hres)]. rewrite <-HpartIsLast in HlastPartIsLast.
            subst lastPart. apply Hres with bentryBlockAddr; assumption.
            simpl. exists pdparent. exists []. split. reflexivity. exists (MPU pdentryPdparent). exists pdentry.
            exists pdentryPdparent. exists blockInParentPartitionAddr. exists bentry. exists newBentry.
            exists s'. split. subst s'. reflexivity. split. left. reflexivity. split. unfold CBlockEntry.
            destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). rewrite HnewB.
            f_equal. f_equal. apply proof_irrelevance. split. assumption. split. assumption. split. assumption.
            split. unfold bentryStartAddr. rewrite HlookupBlock. reflexivity. split. unfold bentryEndAddr.
            rewrite HlookupBlock. reflexivity. split. assumption. split. assumption. split. subst s'. simpl.
            assert(HbeqBlockPartBis: beqAddr blockInParentPartitionAddr partition = false).
            { rewrite <-beqAddrFalse. intuition. }
            rewrite HbeqBlockPartBis. rewrite removeDupIdentity; intuition. split. assumption. split. subst s'.
            simpl. destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
            {
              rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
              rewrite HlookupBlock in HlookupParent. exfalso; congruence.
            }
            rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
            intuition.
          + split; try(intro; exfalso; congruence). intro HflagFalse. subst flag.
            intro Hcontra. rewrite <-HgetMappedEq in *.
            assert(HaccessTrue: bentryAFlag blockInParentPartitionAddr true s').
            {
              apply addrInAccessibleMappedIsAccessible with pdparent addr; try(assumption).
              {
                unfold noDupUsedPaddrList in *. intros part HpartIsPDT.
                destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart'.
                {
                  rewrite <-DTL.beqAddrTrue in HbeqBlockPart'. subst part.
                  unfold isPDT in HpartIsPDT. rewrite HlookupBlocks' in HpartIsPDT. exfalso; congruence.
                }
                assert(HpartIsPDTs: isPDT part s).
                {
                  unfold isPDT in *. subst s'. simpl in HpartIsPDT. rewrite HbeqBlockPart' in HpartIsPDT.
                  rewrite <-beqAddrFalse in HbeqBlockPart'. rewrite removeDupIdentity in HpartIsPDT; intuition.
                }
                specialize(HnoDup part HpartIsPDTs).
                assert(HgetUsedEq: getUsedPaddr part s' = getUsedPaddr part s).
                {
                  unfold getUsedPaddr.
                  assert(Hconfig: getConfigPaddr part s' = getConfigPaddr part s).
                  {
                    subst s'. apply getConfigPaddrEqBE; try(assumption).
                    unfold isBE. rewrite HlookupBlock. trivial.
                  }
                  assert(Hmapped: getMappedPaddr part s' = getMappedPaddr part s).
                  {
                    subst s'.
                    apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
                          try(assumption);
                          unfold CBlockEntry;
                            destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb);
                            try(lia); simpl; reflexivity.
                  }
                  rewrite Hconfig. rewrite Hmapped. reflexivity.
                }
                rewrite HgetUsedEq. assumption.
              }
              simpl. rewrite beqAddrTrue. rewrite app_nil_r. unfold CBlockEntry.
              destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
              simpl. assumption.
            }
            unfold bentryAFlag in HaccessTrue. rewrite HlookupBlocks' in HaccessTrue.
            rewrite HnewB in HaccessTrue. simpl in HaccessTrue. congruence.
      }
      destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                HAFlagBlockAddr & HblockAddrMappedBase & HstartBlockAddr & HendBlockAddr & HpartialAccess))].
      destruct (beqAddr parent pdparent) eqn:HbeqParentPdParent.
      - (* parent = pdparent *)
        rewrite <-DTL.beqAddrTrue in HbeqParentPdParent. subst parent.
        assert(HaddrIsMappedAccInParents: In addr 
                        (getAllPaddrBlock (startAddr (blockrange bentry)) (endAddr (blockrange bentry))
                        ++ getAccessibleMappedPaddr pdparent s)) by intuition.
        apply in_app_or in HaddrIsMappedAccInParents.
        assert(HchildNotPdparent: pdparent <> child).
        {
          unfold consistency1 in *; apply childparentNotEq with s; intuition.
        }
        apply not_eq_sym in HchildNotPdparent.
        rewrite HgetAccEq; try(assumption).
        specialize(HgetAccMappedParentEq HaddrIsMappedAccInParent).
        destruct HgetAccMappedParentEq as (HgetAccMappedParentEq & HgetAccMappedParentEqFlagEq &
                                            HnotEdgeCaseIfNotFlag).
        destruct (beqAddr child pdbasepartition) eqn:HbeqChildBase.
        + (* child = pdbasepartition *)
          rewrite <-DTL.beqAddrTrue in HbeqChildBase. subst child. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. rewrite HlookupBlockAddr in *. rewrite HlookupBlock in *.
          rewrite HstartBlockAddr in Hstart. rewrite HendBlockAddr in Hend.
          specialize(HnoDup pdbasepartition HchildIsPDT).
          unfold getUsedPaddr in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
          destruct HnoDup as [(Hconf & HnoDupMapped) Hdis]. unfold getMappedPaddr in HnoDupMapped.
          destruct HaddrIsMappedAccInParents as [HedgeCase | HaddrAccMappedParents].
          * rewrite HstartBlockAddr in HstartBase. rewrite HendBlockAddr in HendBase.
            rewrite HlookupBlockBase in *. rewrite HstartBase in Hstart. rewrite HendBase in Hend.
            rewrite <-Hstart in HedgeCase. rewrite <-Hend in HedgeCase.
            apply addrInAccessibleBlockIsAccessibleMapped with blockBase; try(assumption). simpl.
            rewrite HlookupBlockBase. rewrite app_nil_r. assumption.
          * destruct HpartialAccess as [Hss0Eq | HpartialAccess].
            -- rewrite Hss0Eq in *.
               specialize(Haccesss0 pdparent pdbasepartition addr HparentIsPart HchildIsChild
                           HaddrAccMappedParents HaddrIsMappedInChild). assumption.
            -- rewrite app_nil_r in HpartialAccess. rewrite Hstart in HpartialAccess.
               rewrite Hend in HpartialAccess.
               assert(HnotEdgeCasePrev: (pdbasepartition = partition -> False)
                                          /\ (pdbasepartition = pdbasepartition -> False)
                                        \/ (In addr
                                             (getAllPaddrBlock (startAddr (blockrange bentry))
                                                (endAddr (blockrange bentry))) -> False)).
               {
                 right. destruct HnotEdgeCase as [Hcontra | Hresult].
                 { exfalso. destruct Hcontra as [_ Hcontra]. contradict Hcontra. reflexivity. }
                 rewrite app_nil_r in Hresult. rewrite HnewB in Hresult. simpl in Hresult. assumption.
               }
               specialize(HpartialAccess pdparent pdbasepartition addr HnotEdgeCasePrev HparentIsPart
                           HchildIsChild HaddrAccMappedParents HaddrIsMappedInChild). assumption.
        + (* child <> pdbasepartition *)
          rewrite <-beqAddrFalse in HbeqChildBase. destruct HpartialAccess as [Hss0Eq | HpartialAccess].
          * (* s = s0 *)
            rewrite Hss0Eq in *. destruct HaddrIsMappedAccInParents as [HedgeCase | HaddrAccMappedParents].
            {
              assert(HaddrInBlockaddr: In addr (getAllPaddrAux [blockaddr] s0)).
              {
                simpl. rewrite HlookupBlockAddr. rewrite app_nil_r. unfold bentryStartAddr in *.
                unfold bentryEndAddr in *. rewrite HlookupBlockAddr in *. rewrite HlookupBlock in *.
                rewrite <-HstartBlockAddr. rewrite <-HendBlockAddr. rewrite Hstart. rewrite Hend.
                assumption.
              }
              assert(HchildIsPartition: child = partition).
              {
                destruct (beqAddr child partition) eqn:HbeqChildPart.
                { rewrite <-DTL.beqAddrTrue in HbeqChildPart. assumption. }
                rewrite <-beqAddrFalse in HbeqChildPart. exfalso.
                assert(HpartIsChild: In partition (getChildren pdparent s0)).
                {
                  assert(HisChild: isChild s0) by (unfold consistency1 in *; intuition).
                  apply HisChild. assumption. unfold pdentryParent. rewrite HlookupPart. assumption.
                }
                specialize(HPI pdparent child partition HparentIsPart HchildIsChild HpartIsChild HbeqChildPart).
                assert(HaddrUsedChild: In addr (getUsedPaddr child s0)).
                {
                  unfold getUsedPaddr. apply in_or_app. right. assumption.
                }
                specialize(HPI addr HaddrUsedChild). unfold getUsedPaddr in HPI. contradict HPI. apply in_or_app.
                right. apply addrInBlockIsMapped with blockaddr; assumption.
              }
              subst child. destruct flag.
              - specialize(HAFlagBlockAddr Htriv).
                apply addrInAccessibleBlockIsAccessibleMapped with blockaddr; assumption.
              - specialize(HnotEdgeCaseIfNotFlag HtrivFalse); intuition.
            }
            {
              specialize(Haccesss0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParents
                      HaddrIsMappedInChild). assumption.
            }
          * (* s <> s0 *)
            destruct HaddrIsMappedAccInParents as [HedgeCase | HaddrAccMappedParents].
            {
              assert(HaddrInBlockaddr: In addr (getAllPaddrAux [blockaddr] s)).
              {
                simpl. rewrite HlookupBlockAddr. rewrite app_nil_r. unfold bentryStartAddr in *.
                unfold bentryEndAddr in *. rewrite HlookupBlockAddr in *. rewrite HlookupBlock in *.
                rewrite <-HstartBlockAddr. rewrite <-HendBlockAddr. rewrite Hstart. rewrite Hend.
                assumption.
              }
              assert(HchildIsPartition: child = partition).
              {
                destruct (beqAddr child partition) eqn:HbeqChildPart.
                { rewrite <-DTL.beqAddrTrue in HbeqChildPart. assumption. }
                rewrite <-beqAddrFalse in HbeqChildPart. exfalso.
                assert(HpartIsChild: In partition (getChildren pdparent s)).
                {
                  assert(HisChild: isChild s) by (unfold consistency1 in *; intuition).
                  apply HisChild. rewrite HgetPartEq. assumption. unfold pdentryParent. rewrite HlookupPart.
                  assumption.
                }
                specialize(HPI pdparent child partition HparentIsPart HchildIsChild HpartIsChild HbeqChildPart).
                assert(HaddrUsedChild: In addr (getUsedPaddr child s)).
                {
                  unfold getUsedPaddr. apply in_or_app. right. assumption.
                }
                specialize(HPI addr HaddrUsedChild). unfold getUsedPaddr in HPI. contradict HPI. apply in_or_app.
                right. apply addrInBlockIsMapped with blockaddr; assumption.
              }
              subst child. destruct flag.
              - specialize(HAFlagBlockAddr Htriv).
                apply addrInAccessibleBlockIsAccessibleMapped with blockaddr; assumption.
              - specialize(HnotEdgeCaseIfNotFlag HtrivFalse); intuition.
            }
            {
              assert(isPDT pdparent s0).
              { unfold isPDT. rewrite <-HlookupParentEq. rewrite HlookupParent. trivial. }
              assert(HgetAccMappedParentEqss0: getAccessibleMappedPaddr pdparent s
                                                = getAccessibleMappedPaddr pdparent s0).
              {
                unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
                unfold consistency2 in Hconsists0.
                apply getAccessibleMappedPaddrEqBuiltWithWriteAccNotInParents with statesList parentsList
                        startaddr endaddr pdbasepartition flag blockBase bentryBases0; intuition.
              }
              rewrite HgetAccMappedParentEqss0 in HaddrAccMappedParents. rewrite HgetPartEq in HparentIsPart.
              assert(HgetChildrenEqss0: getChildren pdparent s = getChildren pdparent s0).
              {
                unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
                unfold consistency2 in Hconsists0.
                apply getChildrenEqBuiltWithWriteAcc with statesList parentsList startaddr endaddr
                        pdbasepartition flag; intuition.
              }
              rewrite HgetChildrenEqss0 in HchildIsChild.
              assert(isPDT child s0).
              {
                unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
                apply childrenArePDT with pdparent; intuition.
              }
              assert(HgetMappedEqss0: getMappedPaddr child s = getMappedPaddr child s0).
              {
                unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
                unfold consistency2 in Hconsists0.
                apply getMappedPaddrEqBuiltWithWriteAcc with statesList parentsList startaddr endaddr
                        pdbasepartition flag blockBase bentryBases0; intuition.
              }
              rewrite HgetMappedEqss0 in HaddrIsMappedInChild.
              specialize(Haccesss0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParents
                      HaddrIsMappedInChild).
              destruct flag.
              - unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
                unfold consistency2 in Hconsists0.
                apply getAccessibleMappedPaddrEqBuiltWithWriteAccFlagTrueRev with s0 statesList parentsList
                      startaddr endaddr pdbasepartition blockBase bentryBases0; try(assumption); intuition.
              - assert(Haccesss: In addr (getAllPaddrBlock startaddr endaddr
                                          ++ getAccessibleMappedPaddr child s)).
                {
                  unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
                  unfold consistency2 in Hconsists0.
                  apply getAccessibleMappedPaddrEqBuiltWithWriteAccFlagFalseRev with s0 statesList parentsList
                        pdbasepartition blockBase bentryBases0; try(assumption); intuition.
                }
                apply in_app_or in Haccesss. destruct Haccesss as [Hcontra | Hres]; try(assumption).
                exfalso. assert(HfalseTriv: false = false) by assumption.
                specialize(HnotEdgeCaseIfNotFlag HfalseTriv). unfold bentryStartAddr in Hstart.
                unfold bentryEndAddr in Hend. rewrite HlookupBlock in *. subst startaddr. subst endaddr.
                congruence.
            }
      - (* parent <> pdparent *)
        assert(HparentsNotEq: parent <> pdparent) by (rewrite beqAddrFalse; assumption).
        assert(HgetAccMappedChildsParentEq: getAccessibleMappedPaddr parent s'
                                              = getAccessibleMappedPaddr parent s).
        {
          apply HgetAccEq. assumption. unfold consistency1 in Hconsis1. apply partitionsArePDT; intuition.
        }
        rewrite HgetAccMappedChildsParentEq in HaddrIsMappedAccInParent.
        assert(HparentIsPDT: isPDT parent s).
        {
          unfold consistency1 in *; apply partitionsArePDT; intuition.
        }
        assert(HchildNotPart: child <> partition).
        {
          rewrite <-beqAddrFalse in HbeqParentPdParent.
          intro Hcontra. subst child.
          assert(HpdparentParentEq: parent = pdparent).
          {
            apply uniqueParent with partition s; try(unfold consistency1 in *; intuition; congruence).
            assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
            specialize(HparentOfPart partition pdentry HlookupPart).
            destruct HparentOfPart as (HpdparentIsPart & _). specialize(HpdparentIsPart HpartNotRoot).
            rewrite Hparent. intuition.
            assert(HisChilds: isChild s) by (unfold consistency1 in *; intuition).
            apply HisChilds. rewrite HgetPartEq. assumption.
            unfold pdentryParent. rewrite HlookupPart. assumption.
          }
          congruence.
        }
        assert(HpdparentNotBase: pdparent <> pdbasepartition).
        {
          assert(isParentsList s0 (parentsList++[pdparent]) pdbasepartition).
          {
            apply parentsListCons with partition; try(assumption).
            unfold consistency in Hconsists0. unfold consistency1 in Hconsists0. intuition.
            simpl. rewrite <-HlookupParentEq. rewrite HlookupParent. split. assumption. split; trivial.
            rewrite Hparent. apply stablePDTParentIsBuiltRev with statesList parentsList pdbasepartition
                  startaddr endaddr flag s; assumption.
          }
          apply not_eq_sym. unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
          apply basePartNotLastInParentsLists with (parentsList++[pdparent]) s0; try(intuition; congruence).
          apply eq_sym. apply last_last.
          intro Hcontra. apply app_eq_nil in Hcontra. destruct Hcontra as (_ & Hcontra). congruence.
        }
        destruct (beqAddr child pdparent) eqn:HbeqChildPdParent.
        + (* child = pdparent *)
          rewrite <-DTL.beqAddrTrue in HbeqChildPdParent. subst child.
          assert(HbeqPdparentPart: pdparent <> partition).
          {
            assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
            specialize(HparentOfPart partition pdentry HlookupPart). rewrite Hparent. intuition.
          }
          assert(HaddrInAccMappedIf: In addr (getAllPaddrBlock (startAddr (blockrange bentry))
                                      (endAddr (blockrange bentry)) ++ getAccessibleMappedPaddr pdparent s)
                                    -> In addr (getAccessibleMappedPaddr pdparent s')).
          {
            intro Haddr. apply in_app_or in Haddr.
            assert(Heq: forall l flag,
                  getAccessibleMappedPaddr pdparent
                     {|
                       currentPartition := currentPartition s;
                       memory :=
                         add blockInParentPartitionAddr
                           (BE
                              (CBlockEntry (read bentry) (write bentry) 
                                 (exec bentry) (present bentry) flag (blockindex bentry)
                                 (blockrange bentry))) (memory s) beqAddr
                     |} = getAccessibleMappedPaddr pdparent
                             {|
                               currentPartition := currentPartition s;
                               memory :=
                                 add blockInParentPartitionAddr
                                   (BE
                                      {|
                                        read := read bentry;
                                        write := write bentry;
                                        exec := exec bentry;
                                        present := present bentry;
                                        accessible := flag;
                                        blockindex := blockindex bentry;
                                        blockrange := blockrange bentry;
                                        Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                                      |}) (memory s) beqAddr
                             |}).
            {
              intros l0 flag'. unfold CBlockEntry.
              destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
              f_equal. f_equal. f_equal. f_equal. f_equal. f_equal. apply proof_irrelevance.
            }
            destruct Haddr as [HaddrInBentry | HaddrInAccMappeds].
            { (* addr is in the mofified entry *)
              rewrite app_nil_r in HnotEdgeCase. destruct HnotEdgeCase as [Hfalse | Hcontra].
              exfalso; intuition.
              contradict Hcontra. rewrite HnewB; simpl; assumption.
            }
            (* addr is not in the mofified entry *)
            destruct (eqb flag (accessible bentry)) eqn:HbeqFlagOldAcc.
            - (* flag = accessible bentry *)
              apply eqb_prop in HbeqFlagOldAcc. subst flag.
              assert(HgetAccMappedEq: getAccessibleMappedPaddr pdparent s'
                                      = getAccessibleMappedPaddr pdparent s).
              {
                subst s'. apply getAccessibleMappedPaddrEqBEPresentAccessibleNoChange with bentry;
                      try(assumption);
                      try(unfold CBlockEntry;
                          destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                          simpl; reflexivity).
              }
              rewrite HgetAccMappedEq. assumption.
            - (* flag <> accessible bentry *)
              apply eqb_false_iff in HbeqFlagOldAcc. destruct flag.
              + (* flag = true *)
                subst s'. apply <-getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence;
                          try(subst newBentry; unfold CBlockEntry;
                            destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                            simpl); try(reflexivity); try(assumption).
                * apply in_or_app. right. assumption.
                * unfold getMappedBlocks in HblockIsMappedParent.
                  apply DTL.InFilterPresentInList in HblockIsMappedParent. assumption.
                * unfold consistency1 in *; intuition; congruence.
                * unfold bentryPFlag in HPFlag. rewrite HlookupBlock in HPFlag. intuition.
              + (* flag = false *)
                assert(HaddrAccMappedOrInBlock:
                        In addr (getAccessibleMappedPaddr pdparent s')
                        \/ In addr (getAllPaddrBlock (startAddr (blockrange newBentry))
                                                     (endAddr (blockrange newBentry)))).
                {
                  subst s'.
                  apply getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleFalseChangeInclusionRev with
                          bentry;
                            try(rewrite HnewB; simpl);
                        try(unfold consistency1 in *; intuition; congruence).
                  unfold bentryPFlag in HPFlag. rewrite HlookupBlock in HPFlag. intuition.
                  unfold getMappedBlocks in HblockIsMappedParent. apply InFilterPresentInList with s. assumption.
                }
                destruct HaddrAccMappedOrInBlock as [HaddrAccMapped | Hcontra].
                assumption.
                destruct HnotEdgeCase as [Hfalse | HaddrNotInBlock]; try(rewrite app_nil_r in HaddrNotInBlock);
                    exfalso; intuition.
          }
          apply HaddrInAccMappedIf. apply in_or_app. right. rewrite <-beqAddrFalse in HbeqParentPdParent.
          destruct HpartialAccess as [Hss0Eq | HpartialAccess].
          { (* s = s0 *)
            rewrite Hss0Eq in *. specialize(Haccesss0 parent pdparent addr HparentIsPart HchildIsChild
                  HaddrIsMappedAccInParent HaddrIsMappedInChild). assumption.
          }
          (* s <> s0 *)
          rewrite HlookupBlockAddr in HpartialAccess.
          rewrite app_nil_r in HpartialAccess.
          assert(HnotPrevEdgeCase: pdparent <> partition /\ (pdparent <> pdbasepartition)
                                   \/ ~ In addr (getAllPaddrBlock (startAddr (blockrange bentryBlockAddr))
                                                                  (endAddr (blockrange bentryBlockAddr)))).
          { left. intuition. }
          specialize(HpartialAccess parent pdparent addr HnotPrevEdgeCase HparentIsPart HchildIsChild
                  HaddrIsMappedAccInParent HaddrIsMappedInChild). assumption.
        + (* child <> pdparent *)
          rewrite <-beqAddrFalse in *.
          assert(HgetAccChildEq: getAccessibleMappedPaddr child s' = getAccessibleMappedPaddr child s).
          { apply HgetAccEq; intuition. }
          rewrite HgetAccChildEq.
          destruct HpartialAccess as [Hss0Eq | HpartialAccess].
          { (* s = s0 *)
            rewrite Hss0Eq in *. specialize(Haccesss0 parent child addr HparentIsPart HchildIsChild
                  HaddrIsMappedAccInParent HaddrIsMappedInChild). assumption.
          }
          (* s <> s0 *)
          rewrite HlookupBlockAddr in HpartialAccess.
          rewrite app_nil_r in HpartialAccess.
          assert(HnotPrevEdgeCase: child <> partition /\ child <> pdbasepartition
                                   \/ ~ In addr (getAllPaddrBlock (startAddr (blockrange bentryBlockAddr))
                                                                  (endAddr (blockrange bentryBlockAddr)))).
          {
            destruct HnotEdgeCase as [HchildNotEqs | HchildNotInBlock].
            - left. intuition.
            - right. rewrite HnewB in HchildNotInBlock. simpl in HchildNotInBlock. unfold bentryStartAddr in *.
              unfold bentryEndAddr in *. rewrite HlookupBlock in *. rewrite <-Hstart in HchildNotInBlock.
              rewrite <-Hend in HchildNotInBlock. rewrite app_nil_r in HchildNotInBlock.
              rewrite HlookupBlockAddr in *. rewrite <-HstartBlockAddr. rewrite <-HendBlockAddr.
              assumption.
          }
          specialize(HpartialAccess parent child addr HnotPrevEdgeCase HparentIsPart HchildIsChild
                  HaddrIsMappedAccInParent HaddrIsMappedInChild). assumption.
    }
    intro a. simpl. eapply bindRev.
    { (** MAL.removeBlockFromPhysicalMPUIfNotAccessible and MAL.removeBlockFromPhysicalMPU **)
      unfold MAL.removeBlockFromPhysicalMPUIfNotAccessible.
      destruct (negb flag) eqn:HflagFalse.
      - apply Bool.negb_true_iff in HflagFalse. rewrite HflagFalse in *.
        eapply bindRev.
        {
          eapply weaken. apply removeBlockFromPhysicalMPU.
          intros s Hprops. simpl. split. apply Hprops.
          destruct Hprops as (Hlength & HstartMappedParent & Hprops).
          destruct Hprops as [sInit (s0 & (pdentry & (pdentryBase & (pdparent & (statesList &
                               (parentsList & (HPIs0 & HKDIs0 & HVSs0 & bentry & (newBentry & (Hs & (Hparent &
                                HparentsEq & (HlookupBlocks0 & (HlookupBlocks & (HPFlag & (HAFlag &
                                 (HblockInMappedBlocks & (HstartAddr & HendAddr & HPFlags0 &
                                  HblockInMappedBlocks0 & HstartAddrs0 & HendAddrs0 & (HnewB & (HlookupBasesInit
                                   & HlookupBases0 & (HlookupBases & HgetPartEqsInit & HbaseIsPart &
                                    (HlookupParts0 & HlookupPart & HpartIsPart & HgetPartEq & HpartNotRoot &
                                     Hconsists0 & HnoDup & Hshared & Hrange & HchildBlockProps & HnoChild &
                                      HisParentsList & Hs0IsLast & HpartitionIsLast & HbaseBlock & HblockPart &
                                       HpartialAccess & HPIsInit & HKDIsInit & HVSsInit & HPinit & HconsistInit &
                                        HisBuilt & Haccess))))))))))))))))))))].
          rewrite <-HparentsEq in *.
          assert(HparentIsPart: parentOfPartitionIsPartition s0) by (unfold consistency1 in *; intuition).
          unfold parentOfPartitionIsPartition in HparentIsPart.
          rewrite Hs in HlookupPart. simpl in HlookupPart.
          destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
          rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPart; intuition.
          specialize(HparentIsPart partition pdentry HlookupPart).
          destruct HparentIsPart as [HparentIsPart (HparentOfRoot & HpartNotParent)].
          specialize(HparentIsPart HbeqBaseRoot).
          destruct HparentIsPart as ([parentEntry HlookupParent] & _).
          unfold isPDT. rewrite Hs. simpl.
          destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
          {
            rewrite <-DTL.beqAddrTrue in HbeqBlockParent. rewrite HbeqBlockParent in *.
            rewrite <- Hparent in HlookupParent. rewrite HlookupParent in *. congruence.
          }
          rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
          subst pdparent. rewrite HlookupParent. trivial.
        }
        intro. eapply weaken. apply WP.ret. intros s Hprops.
        instantiate(1:= fun _ s =>
          exists (sInit s0 s1: state) (realMPU : list paddr) (pdentryParent pdentryBase pdentryPart: PDTable)
                  (bentry newBentry: BlockEntry) statesList parentsList pdparent,
            (forall parentsList, isParentsList s1 parentsList partition -> length parentsList < S timeout)
            /\ In startaddr (getMappedPaddr pdparent s1) /\
            partitionsIsolation s0 /\ kernelDataIsolation s0 /\ verticalSharing s0 /\
            s1 =
                {|
                  currentPartition := currentPartition s0;
                  memory :=
                    add blockInParentPartitionAddr
                      (BE
                         (CBlockEntry (read bentry) (write bentry) (exec bentry)
                            (present bentry) flag (blockindex bentry) (blockrange bentry)))
                      (memory s0) beqAddr
                |}
            /\ newBentry =
                         CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) flag
                           (blockindex bentry) (blockrange bentry)
            /\ lookup pdbasepartition (memory sInit) beqAddr = Some (PDT pdentryBase)
            /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase)
            /\ lookup pdbasepartition (memory s1) beqAddr = Some (PDT pdentryBase)
            /\ In pdbasepartition (getPartitions multiplexer s0)
            /\ getPartitions multiplexer s0 = getPartitions multiplexer sInit
            /\ lookup partition (memory s0) beqAddr = Some (PDT pdentryPart)
            /\ lookup partition (memory s1) beqAddr = Some (PDT pdentryPart)
            /\ In partition (getPartitions multiplexer s0)
            /\ lookup pdparent (memory s1) beqAddr = Some (PDT pdentryParent)
            /\ getPartitions multiplexer s1 = getPartitions multiplexer s0
            /\ partition <> constantRootPartM
            /\ bentryPFlag blockInParentPartitionAddr true s0
            /\ In blockInParentPartitionAddr (getMappedBlocks pdparent s0)
            /\ bentryStartAddr blockInParentPartitionAddr startaddr s0
            /\ bentryEndAddr blockInParentPartitionAddr endaddr s0
            /\ bentryAFlag blockInParentPartitionAddr flag s1
            /\ bentryPFlag blockInParentPartitionAddr true s1
            /\ In blockInParentPartitionAddr (getMappedBlocks pdparent s1)
            /\ bentryStartAddr blockInParentPartitionAddr startaddr s1
            /\ bentryEndAddr blockInParentPartitionAddr endaddr s1
            /\ lookup blockInParentPartitionAddr (memory s0) beqAddr = Some (BE bentry)
            /\ lookup blockInParentPartitionAddr (memory s1) beqAddr = Some (BE newBentry)
            /\ consistency1 s0
            /\ pdentryMPU pdparent realMPU s1
            /\ pdparent = parent pdentryPart
            /\ pdparent = pdParent
            /\ noDupUsedPaddrList s0
            /\ sharedBlockPointsToChild s0
            /\ adressesRangePreservedIfOriginAndNextOk s0
            /\ childsBlocksPropsInParent s0
            /\ noChildImpliesAddressesNotShared s0
            /\ partitionsIsolation sInit
            /\ kernelDataIsolation sInit
            /\ verticalSharing sInit
            /\ P sInit
            /\ consistency sInit
            /\ isParentsList sInit parentsList pdbasepartition
            /\ s0 = last statesList sInit
            /\ partition = last parentsList pdbasepartition
            /\ isBuiltFromWriteAccessibleRec sInit s0 statesList parentsList pdbasepartition startaddr endaddr
                  flag
            /\ (exists blockBase bentryBase bentryBasesInit,
                 lookup blockBase (memory sInit) beqAddr = Some (BE bentryBasesInit)
                 /\ bentryPFlag blockBase true sInit
                 /\ bentryAFlag blockBase true sInit
                 /\ In blockBase (getMappedBlocks pdbasepartition sInit)
                 /\ In blockBase (getAccessibleMappedBlocks pdbasepartition sInit)
                 /\ bentryStartAddr blockBase startaddr sInit
                 /\ bentryEndAddr blockBase endaddr sInit
                 /\ false = checkChild blockBase sInit (CPaddr (blockBase + sh1offset))
                 /\ lookup blockBase (memory s0) beqAddr = Some (BE bentryBase)
                 /\ bentryPFlag blockBase true s0
                 /\ bentryAFlag blockBase true s0
                 /\ In blockBase (getMappedBlocks pdbasepartition s0)
                 /\ bentryStartAddr blockBase startaddr s0
                 /\ bentryEndAddr blockBase endaddr s0
                 /\ false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset)))
            /\ (exists blockPart bentryPart,
                 lookup blockPart (memory s1) beqAddr = Some (BE bentryPart)
                 /\ bentryPFlag blockPart true s1
                 /\ In blockPart (getMappedBlocks partition s1)
                 /\ bentryStartAddr blockPart startaddr s1
                 /\ bentryEndAddr blockPart endaddr s1
                 /\ false = checkChild blockPart s1 (CPaddr (blockPart + sh1offset)))
            /\ (exists (blockaddr : paddr) (bentry0 : BlockEntry),
                       lookup blockaddr (memory s1) beqAddr = Some (BE bentry0) /\
                       bentryPFlag blockaddr true s1 /\
                       bentryAFlag blockaddr flag s1 /\
                       In blockaddr (getMappedBlocks pdparent s1) /\
                       bentryStartAddr blockaddr startaddr s1 /\
                       bentryEndAddr blockaddr endaddr s1 /\
                       (forall parent child addr : paddr,
                          child <> pdparent /\ child <> pdbasepartition
                          \/ ~In addr (getAllPaddrAux [blockaddr] s)
                          -> In parent (getPartitions multiplexer s1)
                          -> In child (getChildren parent s1)
                          -> In addr (getAccessibleMappedPaddr parent s1)
                          -> In addr (getMappedPaddr child s1)
                          -> In addr (getAccessibleMappedPaddr child s1)))
              /\ (s = s1 \/
                    s =
                     {|
                       currentPartition := currentPartition s1;
                       memory :=
                         add pdparent
                           (PDT
                              {|
                                structure := structure pdentryParent;
                                firstfreeslot := firstfreeslot pdentryParent;
                                nbfreeslots := nbfreeslots pdentryParent;
                                nbprepare := nbprepare pdentryParent;
                                parent := parent pdentryParent;
                                MPU :=
                                  MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                                vidtAddr := vidtAddr pdentryParent
                              |}) (memory s1) beqAddr
                     |})).
        simpl. destruct Hprops as [s1 (pdentryParent & (realMPU & (HpdentryMPU & ((Hlength & HstartMappedParent &
                                      Hprops) & (HlookupParent & Hs)))))].
        destruct Hprops as [sInit (s0 & (pdentryPart & (pdentryBase & (pdparent & (statesList &
                             (parentsList & (HPIs0 & HKDIs0 & HVSs0 & bentry & (newBentry & (Hs1 & (Hparent &
                              HparentsEq & (HlookupBlocks0 & (HlookupBlocks1 & (HPFlags0 & HblockInMappedBlocks0
                               & HstartAddrs0 & HendAddrs0 & HPFlag & (HAFlag & (HblockInMappedBlocks1 &
                                (HstartAddr & HendAddr & (HnewB & (HlookupBasesInit & (HlookupBases0 &
                                 (HlookupBases1 & HgetPartEqsInit & HbaseIsPart & HlookupParts0 & HlookupParts1 &
                                  HpartIsPart & HgetPartEq & HpartNotRoot & (Hconsists0 & HnoDup & Hshared &
                                   Hrange & HchildBlockProps & HnoChild & HisParentsList & Hs0IsLast & HpartIsLast
                                    & HbaseBlock & HblockPart & HpartialAccess & HPIsInit & HKDIsInit & HVSsInit
                                     & HPinit & HconsistInit & HisBuilt & Haccess)))))))))))))))))))))].
        rewrite <-HparentsEq in *.
        exists sInit. exists s0. exists s1. exists realMPU. exists pdentryParent. exists pdentryBase.
        exists pdentryPart. exists bentry. exists newBentry. exists statesList. exists parentsList.
        exists pdparent. intuition.
        destruct HpartialAccess as [blockaddr (bentryAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                                    HAFlagBlockAddr & HblockAddrMappedParent & HstartBlockAddr & HendBlockAddr &
                                    HpartialAccess))].
        exists blockaddr. exists bentryAddr. rewrite HlookupBlockAddr in HpartialAccess.
        rewrite app_nil_r in HpartialAccess.
        assert(HlookupBlockAddrEq: lookup blockaddr (memory s) beqAddr = lookup blockaddr (memory s1) beqAddr).
        {
          rewrite Hs. simpl. destruct (beqAddr pdparent blockaddr) eqn:HbeqParentBlockAddr.
          {
            rewrite <-DTL.beqAddrTrue in HbeqParentBlockAddr. subst blockaddr.
            rewrite HlookupParent in HlookupBlockAddr. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in HbeqParentBlockAddr. rewrite removeDupIdentity; intuition.
        }
        rewrite HlookupBlockAddrEq. rewrite HlookupBlockAddr. rewrite app_nil_r. intuition.
      - eapply weaken. apply WP.ret. intros s Hprops. simpl.
        destruct Hprops as (Hlength & HstartMappedParent & Hprops).
        destruct Hprops as [sInit (s0 & (pdentry & (pdentryBase & (pdparent & (statesList &
                             (parentsList & (HPIs0 & HKDIs0 & HVSs0 & bentry & (newBentry & (Hs & (Hparent &
                              HparentsEq & (HlookupBlocks0 & (HlookupBlocks & (HPFlags0 & HblockInMappedBlocks0 &
                               HstartAddrs0 & HendAddrs0 & HPFlag & (HAFlag & (HblockInMappedBlocks &
                               (HstartAddr & HendAddr & (HnewB & (HlookupBasesInit & HlookupBases0 &
                                (HlookupBases & HgetPartEqsInit & HbaseIsPart & (HlookupParts0 & HlookupPart &
                                 HpartIsPart & HgetPartEq & HpartNotRoot & Hconsists0 & HnoDup & Hshared & Hrange
                                  & HchildBlockProps & HnoChild & HisParentsList & Hs0IsLast & HpartitionIsLast &
                                   HbaseBlock & HblockPart & HpartialAccess & HPIsInit & HKDIsInit & HVSsInit &
                                    HPinit & HconsistInit & HisBuilt & Haccess))))))))))))))))))))].
        rewrite <-HparentsEq in *.
        assert(HparentIsPart: parentOfPartitionIsPartition s0) by (unfold consistency1 in Hconsists0; intuition).
        specialize(HparentIsPart partition pdentry HlookupParts0).
        destruct HparentIsPart as [HparentOfPart (HparentOfRoot & HparentPartNotEq)].
        specialize(HparentOfPart HbeqBaseRoot).
        destruct HparentOfPart as ([parentEntry HlookupPdparent] & _). rewrite <-Hparent in *.
        destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
        {
          rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
          rewrite HlookupPdparent in HlookupBlocks0. exfalso; congruence.
        }
        assert(HlookupPdparents: lookup pdparent (memory s) beqAddr = Some (PDT parentEntry)).
        {
          rewrite Hs. simpl. rewrite HbeqBlockParent. rewrite <-beqAddrFalse in HbeqBlockParent.
          rewrite removeDupIdentity; intuition.
        }
        exists sInit. exists s0. exists s. exists (MPU parentEntry). exists parentEntry. exists pdentryBase.
        exists pdentry. exists bentry. exists newBentry. exists statesList. exists parentsList.
        exists pdparent.
        apply Bool.negb_false_iff in HflagFalse. rewrite HflagFalse in *. intuition.
        unfold pdentryMPU. rewrite HlookupPdparents. reflexivity.
    }
    intro. simpl.
    eapply strengthen. eapply weaken. apply IHtimeout.
    -- intros s Hprops. simpl.
       destruct Hprops as [sInit (s0 & (s1 & realMPU & pdentryParent & pdentryBase & pdentryPart & (bentry &
                            (newBentry & statesList & parentsList & pdparent & (Hlength &
                             HstartMappedParent & HPIs0 & HKDIs0
                             & HVSs0 & Hs1 & HnewB & HlookupBasesInit & HlookupBases0 & HlookupBases1 &
                              HbaseIsPart & HgetPartEqsInit & HlookupParts0 & HlookupParts1 & HpartIsPart &
                               HlookupParent & HgetPartEq & HpartNotRoot & HPFlags0 & HblockInMappedBlocks0 &
                                HstartAddrs0 & HendAddrs0 & HAFlag & HPFlag & HblockInMappedBlocks & HstartAddr &
                                 HendAddr & HlookupBlocks0 & HlookupBlocks1 & Hconsists0 & HMPU & HparentEq &
                                  HuniqueParent & HnoDup & Hshared & Hrange & HchildBlockProps & HnoChild &
                                   HPIsInit & HKDIsInit & HVSsInit & HPsInit & HconsistInit & HisParentsList &
                                    Hs0IsLast & HpartIsLast & HisBuilt & HbaseBlock & HblockPart & HpartialAccess
                                     & HpropsOr)))))].
       rewrite <-HuniqueParent.
       destruct (beqAddr blockInParentPartitionAddr nullAddr) eqn:HbeqBlockNull.
       {
         assert(HnullExists: nullAddrExists s0) by (unfold consistency1 in Hconsists0; intuition).
         unfold nullAddrExists in HnullExists. unfold isPADDR in HnullExists.
         rewrite <-DTL.beqAddrTrue in HbeqBlockNull. rewrite HbeqBlockNull in *.
         destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
         destruct v; try(exfalso; congruence).
       }
       assert(HblockInMappedBlocksEqs1: getMappedBlocks pdparent s1 = getMappedBlocks pdparent s0).
       {
         rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. intuition. unfold CBlockEntry.
         assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
         destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
         reflexivity.
       }
       assert(HlowerThanMax: blockindex bentry < kernelStructureEntriesNb) by (apply Hidx).
       assert(HnewBentry: exists l, newBentry =
                      {|
                        read := read bentry;
                        write := write bentry;
                        exec := exec bentry;
                        present := present bentry;
                        accessible := flag;
                        blockindex := blockindex bentry;
                        blockrange := blockrange bentry;
                        Hidx := ADT.CBlockEntry_obligation_1 (blockindex bentry) l
                      |}).
       {
         rewrite HnewB. unfold CBlockEntry.
         destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
         exists l. reflexivity.
       }
       destruct HnewBentry as [lbentry HnewBentry].
       assert(HblockIsNotFree: ~isFreeSlot blockInParentPartitionAddr s0).
       {
         unfold isFreeSlot. rewrite HlookupBlocks0.
         assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
               by (unfold consistency in *; unfold consistency1 in *; intuition).
         unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
         assert(HblockIsBE: isBE blockInParentPartitionAddr s0).
         { unfold isBE. rewrite HlookupBlocks0. trivial. }
         specialize(HwellFormeds0 blockInParentPartitionAddr HblockIsBE).
         unfold isSHE in HwellFormeds0.
         destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr);
               try(exfalso; congruence).
         destruct v; try(exfalso; congruence).
         assert(HwellFormedCuts0: wellFormedShadowCutIfBlockEntry s0)
               by (unfold consistency in *; unfold consistency1 in *; intuition).
         unfold wellFormedShadowCutIfBlockEntry in HwellFormedCuts0.
         specialize(HwellFormedCuts0 blockInParentPartitionAddr HblockIsBE).
         destruct HwellFormedCuts0 as [scentryaddr (HwellFormedCuts0 & HsceValue)].
         subst scentryaddr. unfold isSCE in HwellFormedCuts0.
         destruct (lookup (CPaddr (blockInParentPartitionAddr + scoffset)) (memory s0) beqAddr);
               try(exfalso; congruence).
         destruct v; try(exfalso; congruence).
         unfold bentryPFlag in HPFlag. rewrite HlookupBlocks1 in HPFlag.
         rewrite HnewBentry in HPFlag. simpl in HPFlag. rewrite <-HPFlag. intro Hcontra.
         destruct Hcontra as (_ & _ & _ & _ & Hcontra & _). congruence.
       }
       assert(HgetFreeSlotsListEq: forall pd, isPDT pd s0
                                             -> lookup pd (memory s1) beqAddr = lookup pd (memory s0) beqAddr
                                               -> getFreeSlotsList pd s1 = getFreeSlotsList pd s0).
       {
         intros pd HisPDT HlookupPdEq. unfold isPDT in HisPDT. unfold getFreeSlotsList in *.
         rewrite HlookupPdEq in *.
         destruct (lookup pd (memory s0) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
         destruct v; try(exfalso; congruence).
         destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull.
         + (* firstfreeslot p = nullAddr *)
           reflexivity.
         + (* firstfreeslot p <> nullAddr *)
           assert(HbeqFirstFreeBlock: firstfreeslot p <> blockInParentPartitionAddr).
           {
             assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold FirstFreeSlotPointerIsBEAndFreeSlot in HfirstFree.
             rewrite <-beqAddrFalse in HbeqFirstFreeNull.
             specialize(HfirstFree pd p HlookupPd HbeqFirstFreeNull).
             destruct HfirstFree as [HfirstIsBE HfirstIsFree].
             intro Hcontra. rewrite Hcontra in HfirstIsFree. congruence.
           }
           assert(HnoDups0: NoDupInFreeSlotsList s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NoDupInFreeSlotsList in HnoDups0.
           specialize(HnoDups0 pd p HlookupPd).
           destruct HnoDups0 as [optionFreeSlotsList (HoptionList & (HwellFormedList & HnoDupList))].
           unfold getFreeSlotsList in HoptionList. rewrite HlookupPd in HoptionList.
           rewrite HbeqFirstFreeNull in HoptionList. subst optionFreeSlotsList.
           rewrite Hs1. apply getFreeSlotsListRecEqBE; try(intuition; congruence).
           * unfold isBE. rewrite HlookupBlocks0. trivial.
           * intro Hcontra.
             set(optionFreeSlotsList:= getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (nbfreeslots p)).
             assert(HisInGetFree: optionFreeSlotsList = getFreeSlotsList pd s0
                                   /\ wellFormedFreeSlotsList optionFreeSlotsList <> False).
             {
               split.
               - unfold getFreeSlotsList. rewrite HlookupPd. rewrite HbeqFirstFreeNull. intuition.
               - intuition.
             }
             assert(HfreeSlotsAreFree: freeSlotsListIsFreeSlot s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold freeSlotsListIsFreeSlot in HfreeSlotsAreFree.
             assert(HisPDTCopy: isPDT pd s0) by (unfold isPDT; rewrite HlookupPd; trivial).
             assert(HinList: filterOptionPaddr optionFreeSlotsList = filterOptionPaddr optionFreeSlotsList
                     /\ In blockInParentPartitionAddr (filterOptionPaddr optionFreeSlotsList)).
             { intuition. }
             rewrite <-beqAddrFalse in HbeqBlockNull.
             specialize(HfreeSlotsAreFree pd blockInParentPartitionAddr optionFreeSlotsList
                       (filterOptionPaddr optionFreeSlotsList) HisPDTCopy HisInGetFree HinList HbeqBlockNull).
             congruence.
       }

       destruct (beqAddr blockInParentPartitionAddr pdparent) eqn:HbeqBlockParent.
       { (* blockInParentPartitionAddr = pdparent *)
         rewrite <-DTL.beqAddrTrue in HbeqBlockParent. subst blockInParentPartitionAddr.
         rewrite HlookupParent in HlookupBlocks1. exfalso; congruence.
       }

       assert(HlookupParents0: lookup pdparent (memory s0) beqAddr = Some (PDT pdentryParent)).
       {
         rewrite Hs1 in HlookupParent. simpl in HlookupParent. rewrite HbeqBlockParent in HlookupParent.
         rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity in HlookupParent; intuition.
       }

       assert(HparentWasPDTsInit: exists pdentryParentsInit,
                      lookup pdparent (memory sInit) beqAddr = Some (PDT pdentryParentsInit)
                      /\ parent pdentryParent = parent pdentryParentsInit).
       {
         apply stablePDTParentIsBuiltRev with statesList parentsList pdbasepartition startaddr endaddr flag
               s0; assumption.
       }

       assert(HpartWasPDTsInit: exists pdentryPartsInit,
                      lookup partition (memory sInit) beqAddr = Some (PDT pdentryPartsInit)
                      /\ parent pdentryPart = parent pdentryPartsInit).
       {
         apply stablePDTParentIsBuiltRev with statesList parentsList pdbasepartition startaddr endaddr flag
               s0; assumption.
       }

       assert(HisParentsListRec: isParentsList sInit (parentsList++[pdparent]) pdbasepartition).
       {
         destruct HparentWasPDTsInit as [entry (HlookupParentsInit & _)].
         destruct HpartWasPDTsInit as [pdentryPartsInit (HlookupPartsInit & HparentEqsInit)].
         apply isParentsListRec with partition entry pdentryPartsInit; try(assumption).
         rewrite HparentEq. rewrite HparentEqsInit. reflexivity.
       }

       assert(HnoDupParentsList: NoDup (parentsList++[pdparent])).
       {
         unfold consistency in HconsistInit. unfold consistency1 in HconsistInit.
         apply parentOfPartNotInParentsListsTail with pdbasepartition sInit; intuition.
       }
       apply NoDup_remove_2 in HnoDupParentsList. rewrite app_nil_r in HnoDupParentsList.
       assert(HcurrPartEqsInit: currentPartition s0 = currentPartition sInit).
       { apply currentPartitionEqIsBuilt with pdbasepartition statesList parentsList startaddr endaddr flag;
              assumption. }

       assert(HisBuiltRec: isBuiltFromWriteAccessibleRec sInit s (statesList++[s]) (parentsList++[pdparent])
                                  pdbasepartition startaddr endaddr flag).
       {
         unfold consistency in HconsistInit. unfold consistency1 in HconsistInit.
         unfold consistency2 in HconsistInit. rewrite HgetPartEqsInit in *.
         destruct HbaseBlock as [blockBase [bentryBase [bentryBasesInit HbaseBlock]]].
         destruct HparentWasPDTsInit as [entry (HlookupParentsInit & _)].
         apply isBuiltFromWriteAccessibleRecRec with s0 s1 partition pdentryPart pdentryParent pdentryBase
                    blockInParentPartitionAddr bentry newBentry realMPU blockBase; try(intuition; congruence).
         - rewrite <-HlookupParents0. apply eq_sym. apply lookupPDTEqWriteAccess with statesList parentsList
                startaddr endaddr flag pdbasepartition. unfold isPDT. rewrite HlookupBasesInit. trivial.
           unfold isPDT. rewrite HlookupParentsInit. trivial.
           assumption. assumption.
         - assert(HcurrPartEqs0: currentPartition s1 = currentPartition s0).
           { rewrite Hs1. simpl. reflexivity. }
           rewrite <-HcurrPartEqsInit. rewrite <-HcurrPartEqs0. intuition.
       }

       assert(HisBuiltRecs1: isBuiltFromWriteAccessibleRec sInit s1 (statesList++[s1]) (parentsList++[pdparent])
                                  pdbasepartition startaddr endaddr flag).
       {
         unfold consistency in HconsistInit. unfold consistency1 in HconsistInit.
         unfold consistency2 in HconsistInit. rewrite HgetPartEqsInit in *.
         destruct HbaseBlock as [blockBase [bentryBase [bentryBasesInit HbaseBlock]]].
         destruct HparentWasPDTsInit as [entry (HlookupParentsInit & _)].
         apply isBuiltFromWriteAccessibleRecRec with s0 s1 partition pdentryPart pdentryParent pdentryBase
                    blockInParentPartitionAddr bentry newBentry realMPU blockBase; try(intuition; congruence).
         rewrite <-HlookupParents0. apply eq_sym. apply lookupPDTEqWriteAccess with statesList parentsList
              startaddr endaddr flag pdbasepartition. unfold isPDT. rewrite HlookupBasesInit. trivial.
         unfold isPDT. rewrite HlookupParentsInit. trivial.
         assumption. assumption.
       }

       assert(HlookupBlocks: lookup blockInParentPartitionAddr (memory s) beqAddr = Some (BE newBentry)).
       {
         destruct HpropsOr as [Hss0Eq | Hs].
         - subst s. assumption.
         - rewrite Hs. simpl. rewrite beqAddrSym in HbeqBlockParent. rewrite HbeqBlockParent.
           rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity; intuition.
       }

       destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockInParentPartitionAddr + sh1offset)))
            eqn:HbeqBlockBlockSh1.
       {
         assert(HwellFormed: wellFormedFstShadowIfBlockEntry s0)
                by (unfold consistency1 in Hconsists0; intuition).
         assert(HblockIsBEs0: isBE blockInParentPartitionAddr s0)
                by (unfold isBE; rewrite HlookupBlocks0; trivial).
         specialize(HwellFormed blockInParentPartitionAddr HblockIsBEs0).
         rewrite <-DTL.beqAddrTrue in HbeqBlockBlockSh1. rewrite <-HbeqBlockBlockSh1 in HwellFormed.
         unfold isSHE in HwellFormed. rewrite HlookupBlocks0 in HwellFormed. exfalso; congruence.
       }

       assert(HnoPDFlagBlock: false = checkChild blockInParentPartitionAddr s0
                                          (CPaddr (blockInParentPartitionAddr + sh1offset))).
       {
         unfold consistency in HconsistInit. unfold consistency1 in HconsistInit.
         unfold consistency2 in HconsistInit.
         destruct HbaseBlock as [blockBase [bentryBase [bentryBasesInit HbaseBlock]]].
         assert(Hres: exists part,
                       part = last (parentsList++[pdparent]) pdbasepartition /\
                       (forall blockPart bentryPart,
                        lookup blockPart (memory s1) beqAddr = Some (BE bentryPart) ->
                        bentryPFlag blockPart true s1 ->
                        In blockPart (getMappedBlocks part s1) ->
                        bentryStartAddr blockPart startaddr s1 ->
                        bentryEndAddr blockPart endaddr s1 ->
                        false = checkChild blockPart s1 (CPaddr (blockPart + sh1offset)))).
         {
           apply baseBlockAccessibleImpliesNoPDWithIsBuilt with sInit (statesList++[s1]) flag blockBase
                 bentryBasesInit pdentryBase; intuition; congruence.
         }
         destruct Hres as [part (Hpart & Hres)]. rewrite last_last in Hpart. subst part.
         specialize(Hres blockInParentPartitionAddr newBentry HlookupBlocks1 HPFlag HblockInMappedBlocks
                       HstartAddr HendAddr). unfold checkChild. unfold checkChild in Hres.
         rewrite HlookupBlocks0. rewrite HlookupBlocks1 in Hres. rewrite Hs1 in Hres. simpl in Hres.
         rewrite HbeqBlockBlockSh1 in Hres. rewrite <-beqAddrFalse in HbeqBlockBlockSh1.
         rewrite removeDupIdentity in Hres; intuition.
       }

       assert(HparentIsPart: In pdparent (getPartitions multiplexer s0)).
       {
         assert(HparentOfPart: parentOfPartitionIsPartition s0)
               by (unfold consistency in *; unfold consistency1 in *; intuition).
         specialize(HparentOfPart partition pdentryPart HlookupParts0).
         destruct HparentOfPart as (HparentIsPart & _). specialize(HparentIsPart HpartNotRoot).
         destruct HparentIsPart. subst pdparent. assumption.
       }

       split.
       {
         unfold consistency in *. unfold consistency1 in *.
         apply partitionsIsolationPreservedIsBuilt with s1 s0 pdparent pdentryParent
              blockInParentPartitionAddr bentry
              (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
       }

       split.
       {
         unfold consistency in *. unfold consistency1 in *.
         destruct HbaseBlock as [blockBase [bentryBase [bentryBasesInit HbaseBlock]]].
         apply kernelDataIsolationPreservedIsBuilt with s1 s0 pdparent pdentryParent
              blockInParentPartitionAddr bentry
              (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag pdbasepartition
              blockBase bentryBase; try(intuition; congruence).
         - unfold getAccessibleMappedBlocks. rewrite HlookupBases0.
           apply accessibleIsInFilterAccessible with bentryBase; try(intuition; congruence).
           destruct HbaseBlock as (_ & _ & _ & _ & _ & _ & _ & _ & HlookupBlockBase & _ & HaccessBlock & _).
           unfold bentryAFlag in HaccessBlock. rewrite HlookupBlockBase in HaccessBlock. intuition.
         - destruct HbaseBlock as (_ & _ & _ & _ & _ & _ & _ & _ & HlookupBlockBase & _ & _ & _ & HstartBase &
                       _ & _).
           unfold bentryStartAddr in *. rewrite HlookupBlocks0 in HstartAddrs0.
           rewrite HlookupBlockBase in HstartBase. rewrite HstartBase in HstartAddrs0. assumption.
         - destruct HbaseBlock as (_ & _ & _ & _ & _ & _ & _ & _ & HlookupBlockBase & _ & _ & _ & _ &
                       HendBase & _).
           unfold bentryEndAddr in *. rewrite HlookupBlocks0 in HendAddrs0.
           rewrite HlookupBlockBase in HendBase. rewrite HendBase in HendAddrs0. assumption.
       }

       split.
       {
         unfold consistency in *. unfold consistency1 in *.
         apply verticalSharingPreservedIsBuilt with s1 s0 pdparent pdentryParent
              blockInParentPartitionAddr bentry
              (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
       }

       assert(Hconss1: consistency1 s1).
       {
         assert(HnullExists: nullAddrExists s1).
         { (* BEGIN nullAddrExists s1 *)
           assert(Hcons0: nullAddrExists s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold nullAddrExists in *. unfold isPADDR in *.
           rewrite Hs1. simpl. rewrite HbeqBlockNull.
           rewrite <-beqAddrFalse in HbeqBlockNull. rewrite removeDupIdentity; intuition.
           (* END nullAddrExists *)
         }

         assert(HwellFormed: wellFormedFstShadowIfBlockEntry s1).
         { (* BEGIN wellFormedFstShadowIfBlockEntry s1 *)
           assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
           (* END wellFormedFstShadowIfBlockEntry*)
         }

         assert(Haccessible: AccessibleNoPDFlag s1).
         { (* BEGIN AccessibleNoPDFlag s1 *)
           unfold consistency in *. unfold consistency1 in *.
           apply AccessibleNoPDFlagPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
           (* END AccessibleNoPDFlag *)
         }

         assert(HPDTI: PDTIfPDFlag s1).
         { (* BEGIN PDTIfPDFlag s1 *)
           assert(Hcons0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
           (* END PDTIfPDFlag *)
         }

         assert(HfirstFreeSlotIsBEFree: FirstFreeSlotPointerIsBEAndFreeSlot s1).
         { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s1 *)
           assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
           intros pdentryaddr pdentry HlookupPdentryAddr HfirstFreeNotNull.
           assert(HlookupPdEq: lookup pdentryaddr (memory s1) beqAddr
                                = lookup pdentryaddr (memory s0) beqAddr).
           {
             rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr pdentryaddr) eqn:HbeqBlockPdentry.
             - (* blockInParentPartitionAddr = pdentryaddr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPdentry. rewrite HbeqBlockPdentry in *.
               rewrite HlookupPdentryAddr in *. exfalso; congruence.
             - (* blockInParentPartitionAddr <> pdentryaddr *)
               rewrite <-beqAddrFalse in HbeqBlockPdentry. rewrite removeDupIdentity; intuition.
           }
           rewrite HlookupPdEq in *.
           specialize(Hcons0 pdentryaddr pdentry HlookupPdentryAddr HfirstFreeNotNull).
           assert(HBEfirsts: isBE (firstfreeslot pdentry) s1).
           {
             unfold isBE in *. rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr (firstfreeslot pdentry)) eqn:HbeqBlockFirstFree.
             - (* blockInParentPartitionAddr = firstfreeslot pdentry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockFirstFree. rewrite HbeqBlockFirstFree in *. trivial.
             - (* blockInParentPartitionAddr <> firstfreeslot pdentry *)
               rewrite <-beqAddrFalse in HbeqBlockFirstFree. rewrite removeDupIdentity; intuition.
           }
           split. assumption. destruct Hcons0 as [HBE Hfree]. unfold isFreeSlot in *. rewrite Hs1. simpl.
           assert(HSHE: isSHE (CPaddr (firstfreeslot pdentry + sh1offset)) s0).
           {
             assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
             specialize(HwellFormeds0 (firstfreeslot pdentry) HBE). assumption.
           }
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (firstfreeslot pdentry + sh1offset)))
                      eqn:HbeqFirstFreeFirstPlusSh1.
           { (* firstfreeslot pdentry = CPaddr (firstfreeslot pdentry + sh1offset) *)
             rewrite <-DTL.beqAddrTrue in HbeqFirstFreeFirstPlusSh1.
             rewrite <-HbeqFirstFreeFirstPlusSh1 in *. unfold isSHE in HSHE. rewrite HlookupBlocks0 in HSHE.
             exfalso; congruence.
           }
           (* firstfreeslot pdentry <> CPaddr (firstfreeslot pdentry + sh1offset) *)
           assert(HSCE: isSCE (CPaddr (firstfreeslot pdentry + scoffset)) s0).
           {
             assert(HwellFormedCuts0: wellFormedShadowCutIfBlockEntry s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold wellFormedShadowCutIfBlockEntry in HwellFormedCuts0.
             specialize(HwellFormedCuts0 (firstfreeslot pdentry) HBE).
             destruct HwellFormedCuts0 as [scentryaddr (HSCE & Hvalue)]. subst scentryaddr. assumption.
           }
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (firstfreeslot pdentry + scoffset)))
                      eqn:HbeqFirstFreeFirstPlusSco.
           { (* firstfreeslot pdentry = CPaddr (firstfreeslot pdentry + scoffset) *)
             rewrite <-DTL.beqAddrTrue in HbeqFirstFreeFirstPlusSco.
             rewrite <-HbeqFirstFreeFirstPlusSco in *. unfold isSCE in HSCE. rewrite HlookupBlocks0 in HSCE.
             exfalso; congruence.
           }
           (* firstfreeslot pdentry <> CPaddr (firstfreeslot pdentry + scoffset) *)
           destruct (beqAddr blockInParentPartitionAddr (firstfreeslot pdentry)) eqn:HbeqBlockFirstFree.
           - (* blockInParentPartitionAddr = firstfreeslot pdentry *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockFirstFree. rewrite HbeqBlockFirstFree in *.
             rewrite <-beqAddrFalse in HbeqFirstFreeFirstPlusSh1.
             rewrite removeDupIdentity; try(intuition; congruence).
           - (* blockInParentPartitionAddr <> firstfreeslot pdentry *)
             rewrite <-beqAddrFalse in HbeqBlockFirstFree.
             rewrite removeDupIdentity; try(intuition; congruence).
             destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqFirstFreeFirstPlusSh1.
             rewrite removeDupIdentity; try(intuition; congruence).
             destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr);
                   try(intuition; congruence).
             destruct v; try(intuition; congruence).
             rewrite <-beqAddrFalse in HbeqFirstFreeFirstPlusSco.
             rewrite removeDupIdentity; try(intuition; congruence).
           (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
         }

         assert(multiplexerIsPDT s1).
         { (* BEGIN multiplexerIsPDT s1 *)
           assert(Hcons0: multiplexerIsPDT s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold multiplexerIsPDT in *.
           unfold isPDT in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr multiplexer) eqn:HbeqBlockMultip.
           - (* blockInParentPartitionAddr = multiplexer *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockMultip. rewrite HbeqBlockMultip in *.
             rewrite HlookupBlocks0 in Hcons0. congruence.
           - (* blockInParentPartitionAddr <> multiplexer *)
             rewrite <-beqAddrFalse in HbeqBlockMultip. rewrite removeDupIdentity; intuition.
          (* END multiplexerIsPDT *)
         }

         assert(currentPartitionInPartitionsList s1).
         { (* BEGIN currentPartitionInPartitionsList s1 *)
           assert(Hcons0: currentPartitionInPartitionsList s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold currentPartitionInPartitionsList in *.
           assert(HcurrPartEq: currentPartition s1 = currentPartition s0)
                 by (rewrite Hs1; simpl; reflexivity).
           rewrite HcurrPartEq. rewrite HgetPartEq. assumption.
           (* END currentPartitionInPartitionsList *)
         }

         assert(wellFormedShadowCutIfBlockEntry s1).
         { (* BEGIN wellFormedShadowCutIfBlockEntry s1 *)
           assert(Hcons0: wellFormedShadowCutIfBlockEntry s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold wellFormedShadowCutIfBlockEntry in *.
           intros pa HisBEpa.
           assert(HisBEs0: isBE pa s0).
           {
             unfold isBE in *. rewrite Hs1 in HisBEpa. simpl in HisBEpa.
             destruct (beqAddr blockInParentPartitionAddr pa) eqn:HbeqBlockPa.
             - (* blockInParentPartitionAddr = pa *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPa. rewrite HbeqBlockPa in *.
               rewrite HlookupBlocks0. trivial.
             - (* blockInParentPartitionAddr <> pa *)
               rewrite <-beqAddrFalse in HbeqBlockPa. rewrite removeDupIdentity in HisBEpa; intuition.
           }
           specialize(Hcons0 pa HisBEs0). destruct Hcons0 as [scentryaddr (HisSCE & HvalueSCE)].
           exists scentryaddr. split; try(assumption). unfold isSCE in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr scentryaddr) eqn:HbeqBlockSce.
           { (* blockInParentPartitionAddr = scentryaddr *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockSce. rewrite HbeqBlockSce in *.
             rewrite HlookupBlocks0 in HisSCE. congruence.
           }
           (* blockInParentPartitionAddr <> scentryaddr *)
           rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity; intuition.
           (* END wellFormedShadowCutIfBlockEntry *)
         }

         assert(BlocksRangeFromKernelStartIsBE s1).
         { (* BEGIN BlocksRangeFromKernelStartIsBE s1 *)
           assert(Hcons0: BlocksRangeFromKernelStartIsBE s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold BlocksRangeFromKernelStartIsBE in *.
           intros kernelEntry blockIdx HisKS HblockInfNbEntries.
           assert(HisKSs0: isKS kernelEntry s0).
           {
             unfold isKS in *. rewrite Hs1 in HisKS. simpl in HisKS.
             destruct (beqAddr blockInParentPartitionAddr kernelEntry) eqn:HbeqBlockKernEntry.
             { (* blockInParentPartitionAddr = kernelEntry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockKernEntry. rewrite HbeqBlockKernEntry in *.
               rewrite HlookupBlocks0. unfold CBlockEntry in HisKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HisKS. assumption.
             }
             (* blockInParentPartitionAddr <> kernelEntry *)
             rewrite <-beqAddrFalse in HbeqBlockKernEntry. rewrite removeDupIdentity in HisKS; intuition.
           }
           specialize(Hcons0 kernelEntry blockIdx HisKSs0 HblockInfNbEntries).
           unfold isBE in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (kernelEntry + blockIdx))) eqn:HbeqBlockKern.
           trivial.
           rewrite <-beqAddrFalse in HbeqBlockKern. rewrite removeDupIdentity; intuition.
           (* END BlocksRangeFromKernelStartIsBE *)
         }

         assert(KernelStructureStartFromBlockEntryAddrIsKS s1).
         { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s1 *)
           assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0)
                 by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold KernelStructureStartFromBlockEntryAddrIsKS in *.
           intros blockEntry blockIdx HisBE HblockIndex.
           assert(HisBEs0: isBE blockEntry s0).
           {
             unfold isBE in *. rewrite Hs1 in HisBE. simpl in HisBE.
             destruct (beqAddr blockInParentPartitionAddr blockEntry) eqn:HbeqBlockEntry.
             - (* blockInParentPartitionAddr = blockEntry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockEntry. rewrite HbeqBlockEntry in *.
               rewrite HlookupBlocks0. trivial.
             - (* blockInParentPartitionAddr <> blockEntry *)
               rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HisBE; intuition.
           }
           assert(HblockIndexs0: bentryBlockIndex blockEntry blockIdx s0).
           {
             unfold bentryBlockIndex in *. rewrite Hs1 in HblockIndex. simpl in HblockIndex.
             destruct (beqAddr blockInParentPartitionAddr blockEntry) eqn:HbeqBlockEntry.
             - (* blockInParentPartitionAddr = blockEntry *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockEntry. rewrite HbeqBlockEntry in *.
               rewrite HlookupBlocks0. unfold CBlockEntry in HblockIndex.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HblockIndex. assumption.
             - (* blockInParentPartitionAddr <> blockEntry *)
               rewrite <-beqAddrFalse in HbeqBlockEntry. rewrite removeDupIdentity in HblockIndex; intuition.
           }
           specialize(Hcons0 blockEntry blockIdx HisBEs0 HblockIndexs0). unfold isKS in *.
           rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockEntry-blockIdx)))
                   eqn: HbeqBlockBlockIdx.
           - (* blockInParentPartitionAddr = CPaddr (blockEntry-blockIdx) *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockBlockIdx. rewrite <-HbeqBlockBlockIdx in *.
             rewrite HlookupBlocks0 in Hcons0. unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
             assumption.
           - (* blockInParentPartitionAddr <> CPaddr (blockEntry-blockIdx) *)
             rewrite <- beqAddrFalse in HbeqBlockBlockIdx. rewrite removeDupIdentity; intuition.
            (* END KernelStructureStartFromBlockEntryAddrIsKS *)
         }

         assert(sh1InChildLocationIsBE s1).
         { (* BEGIN sh1InChildLocationIsBE s1 *)
           assert(Hcons0: sh1InChildLocationIsBE s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold sh1InChildLocationIsBE in *.
           intros sh1entryaddr sh1entry Hlookupsh1 HinChildLocNotNull.
           assert(Hlookupsh1s0: lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)).
           {
             rewrite Hs1 in Hlookupsh1. simpl in Hlookupsh1.
             destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1;
                   try(exfalso; congruence).
             (* blockInParentPartitionAddr <> sh1entryaddr *)
             rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity in Hlookupsh1; intuition.
           }
           specialize(Hcons0 sh1entryaddr sh1entry Hlookupsh1s0 HinChildLocNotNull).
           unfold isBE in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (inChildLocation sh1entry)) eqn:HbeqBlockInChild.
           - (* blockInParentPartitionAddr = inChildLocation sh1entry *)
             trivial.
           - (* blockInParentPartitionAddr <> inChildLocation sh1entry *)
             rewrite <-beqAddrFalse in HbeqBlockInChild. rewrite removeDupIdentity; intuition.
             (* END sh1InChildLocationIsBE *)
         }

         assert(StructurePointerIsKS s1).
         { (* BEGIN StructurePointerIsKS s1 *)
           assert(Hcons0: StructurePointerIsKS s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
             (* END StructurePointerIsKS *)
         }

         assert(NextKSIsKS s1).
         { (* BEGIN NextKSIsKS s1 *)
           assert(Hcons0: NextKSIsKS s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NextKSIsKS in *.
           intros addr nextKSAddr nextKS HisKS HnextKSAddr HnextKSentry HnextKSNotNull.
           assert(HisKSs0: isKS addr s0).
           {
             unfold isKS in *. rewrite Hs1 in HisKS. simpl in HisKS.
             destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockAddr.
             - (* blockInParentPartitionAddr = addr *)
               unfold CBlockEntry in HisKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HisKS. rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. rewrite HbeqBlockAddr in *.
               rewrite HlookupBlocks0. assumption.
             - (* blockInParentPartitionAddr <> addr *)
               rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HisKS; intuition.
           }
           assert(HnextKSAddrs0: StateLib.nextKSAddr addr nextKSAddr s0).
           {
             unfold StateLib.nextKSAddr in *. rewrite Hs1 in HnextKSAddr. simpl in HnextKSAddr.
             destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockAddr.
             - (* blockInParentPartitionAddr = addr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. rewrite HbeqBlockAddr in *.
               rewrite HlookupBlocks0. assumption.
             - (* blockInParentPartitionAddr <> addr *)
               rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HnextKSAddr; intuition.
           }
           assert(HnextKSentrys0: nextKSentry nextKSAddr nextKS s0).
           {
             unfold nextKSentry in *. rewrite Hs1 in HnextKSentry. simpl in HnextKSentry.
             destruct (beqAddr blockInParentPartitionAddr nextKSAddr) eqn:HbeqBlockNextAddr;
                   try(exfalso; congruence).
             (* blockInParentPartitionAddr <> nextKSAddr *)
             rewrite <-beqAddrFalse in HbeqBlockNextAddr.
             rewrite removeDupIdentity in HnextKSentry; intuition.
           }
           specialize(Hcons0 addr nextKSAddr nextKS HisKSs0 HnextKSAddrs0 HnextKSentrys0 HnextKSNotNull).
           unfold isKS in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr nextKS) eqn:HbeqBlockNextKS.
           - (* blockInParentPartitionAddr = nextKS *)
             unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia). simpl.
             rewrite <-DTL.beqAddrTrue in HbeqBlockNextKS. rewrite HbeqBlockNextKS in *.
             rewrite HlookupBlocks0 in Hcons0. assumption.
           - (* blockInParentPartitionAddr <> nextKS *)
             rewrite <-beqAddrFalse in HbeqBlockNextKS. rewrite removeDupIdentity; intuition.
           (* END NextKSIsKS *)
         }

         assert(NextKSOffsetIsPADDR s1).
         { (* BEGIN NextKSOffsetIsPADDR s1 *)
           assert(Hcons0: NextKSOffsetIsPADDR s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NextKSOffsetIsPADDR in *.
           intros addr nextKSaddr HisKS HnextKSAddr.
           assert(HisKSs0: isKS addr s0).
           {
             unfold isKS in *. rewrite Hs1 in HisKS. simpl in HisKS.
             destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockAddr.
             - (* blockInParentPartitionAddr = addr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. rewrite HbeqBlockAddr in *.
               unfold CBlockEntry in HisKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HisKS. rewrite HlookupBlocks0. assumption.
             - (* blockInParentPartitionAddr <> addr *)
               rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HisKS; intuition.
           }
           assert(HnextKSAddrs0: nextKSAddr addr nextKSaddr s0).
           {
             unfold nextKSAddr in *. rewrite Hs1 in HnextKSAddr. simpl in HnextKSAddr.
             destruct (beqAddr blockInParentPartitionAddr addr) eqn:HbeqBlockAddr.
             - (* blockInParentPartitionAddr = addr *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockAddr. rewrite HbeqBlockAddr in *.
               unfold CBlockEntry in HisKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HisKS. rewrite HlookupBlocks0. assumption.
             - (* blockInParentPartitionAddr <> addr *)
               rewrite <-beqAddrFalse in HbeqBlockAddr. rewrite removeDupIdentity in HnextKSAddr; intuition.
           }
           specialize(Hcons0 addr nextKSaddr HisKSs0 HnextKSAddrs0). unfold isPADDR in *.
           rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr nextKSaddr) eqn:HbeqBlockNextKS.
           { (* blockInParentPartitionAddr = nextKSaddr *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockNextKS. rewrite HbeqBlockNextKS in *.
             destruct (lookup nextKSaddr (memory s0) beqAddr); try(exfalso; intuition; congruence).
             destruct v; try(exfalso; intuition; congruence).
           }
           (* blockInParentPartitionAddr <> nextKSaddr *)
           rewrite <-beqAddrFalse in HbeqBlockNextKS. rewrite removeDupIdentity; intuition.
           (* END NextKSOffsetIsPADDR *)
         }

         assert(NoDupInFreeSlotsList s1).
         { (* BEGIN NoDupInFreeSlotsList s1 *)
           assert(Hcons0: NoDupInFreeSlotsList s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NoDupInFreeSlotsList in *.
           intros pd pdentry HlookupPd.
           assert(HlookupPds0: lookup pd (memory s0) beqAddr = Some (PDT pdentry)).
           {
             rewrite Hs1 in HlookupPd. simpl in HlookupPd.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity in HlookupPd; intuition.
           }
           specialize(Hcons0 pd pdentry HlookupPds0). destruct Hcons0 as [optionFreeSlotsList Hcons0].
           exists optionFreeSlotsList. split.
           - destruct Hcons0 as [HgetFree Hcons0]. subst optionFreeSlotsList. apply eq_sym.
             apply HgetFreeSlotsListEq.
             + unfold isPDT. rewrite HlookupPds0. trivial.
             + rewrite HlookupPd. rewrite HlookupPds0. reflexivity.
           - intuition.
           (* END NoDupInFreeSlotsList *)
         }

         assert(freeSlotsListIsFreeSlot s1).
         { (* BEGIN freeSlotsListIsFreeSlot s1 *)
           assert(Hcons0: freeSlotsListIsFreeSlot s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold freeSlotsListIsFreeSlot in *.
           intros pd freeSlotAddr optionFreeSlotsList freeSlotsList HisPDT HoptionList HfreeSlotsList
               HaddNotNull.
           assert(HlookupPdEq: lookup pd (memory s1) beqAddr = lookup pd (memory s0) beqAddr).
           {
             unfold isPDT in HisPDT. rewrite Hs1 in *. simpl in *.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd.
             { (* blockInParentPartitionAddr = pd *)
               exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> pd *)
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; intuition.
           }
           assert(HisPDTs0: isPDT pd s0).
           {
             unfold isPDT in *. rewrite HlookupPdEq in HisPDT. assumption.
           }
           assert(HoptionLists0: optionFreeSlotsList = getFreeSlotsList pd s0
                                 /\ wellFormedFreeSlotsList optionFreeSlotsList <> False).
           {
             split.
             - destruct HoptionList as [HoptionList HwellFormedList]. subst optionFreeSlotsList.
               apply HgetFreeSlotsListEq; assumption.
             - intuition.
           }
           specialize(Hcons0 pd freeSlotAddr optionFreeSlotsList freeSlotsList HisPDTs0 HoptionLists0
                       HfreeSlotsList HaddNotNull).
           unfold isFreeSlot in *. rewrite Hs1. simpl.
           assert(HisBE: isBE freeSlotAddr s0).
           {
             unfold isBE. destruct (lookup freeSlotAddr (memory s0) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence). trivial.
           }
           assert(HwellFormeds0: wellFormedFstShadowIfBlockEntry s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold wellFormedFstShadowIfBlockEntry in HwellFormeds0.
           specialize(HwellFormeds0 freeSlotAddr HisBE).
           assert(HwellFormedCuts0: wellFormedShadowCutIfBlockEntry s0)
                   by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold wellFormedShadowCutIfBlockEntry in HwellFormedCuts0.
           specialize(HwellFormedCuts0 freeSlotAddr HisBE).
           destruct HwellFormedCuts0 as [scentryaddr (HwellFormedCuts0 & HsceValue)].
           subst scentryaddr.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (freeSlotAddr + sh1offset))) eqn:HbeqBlockSh1.
           { (* blockInParentPartitionAddr = CPaddr (freeSlotAddr + sh1offset) *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockSh1. rewrite <-HbeqBlockSh1 in *.
             unfold isSHE in HwellFormeds0. rewrite HlookupBlocks0 in HwellFormeds0.
             exfalso; congruence.
           }
           (* blockInParentPartitionAddr = CPaddr (freeSlotAddr + sh1offset) *)
           destruct (beqAddr blockInParentPartitionAddr freeSlotAddr) eqn:HbeqBlockFreeSlot.
           - (* blockInParentPartitionAddr = freeSlotAddr *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockFreeSlot. rewrite HbeqBlockFreeSlot in *.
             rewrite <-beqAddrFalse in HbeqBlockSh1. rewrite removeDupIdentity; intuition; congruence.
           - (* blockInParentPartitionAddr <> freeSlotAddr *)
             rewrite <-beqAddrFalse in HbeqBlockFreeSlot.
             rewrite removeDupIdentity; try(intuition;congruence).
             destruct (lookup freeSlotAddr (memory s0) beqAddr); try(exfalso; congruence).
             destruct v; try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSh1.
             rewrite removeDupIdentity; try(intuition; congruence).
             unfold isSHE in HwellFormeds0.
             destruct (lookup (CPaddr (freeSlotAddr + sh1offset)) (memory s0) beqAddr);
                 try(exfalso; congruence).
             destruct v; try(exfalso; congruence).
             destruct (beqAddr blockInParentPartitionAddr (CPaddr (freeSlotAddr + scoffset)))
                 eqn:HbeqBlockFreeSco.
             { (* blockInParentPartitionAddr = CPaddr (freeSlotAddr + scoffset) *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockFreeSco. rewrite <-HbeqBlockFreeSco in *.
               unfold isSCE in HwellFormedCuts0. rewrite HlookupBlocks0 in HwellFormedCuts0. congruence.
             }
             (* blockInParentPartitionAddr <> CPaddr (freeSlotAddr + scoffset) *)
             rewrite <-beqAddrFalse in HbeqBlockFreeSco. rewrite removeDupIdentity; intuition.
           (* END freeSlotsListIsFreeSlot *)
         }

         assert(DisjointFreeSlotsLists s1).
         { (* BEGIN DisjointFreeSlotsLists s1 *)
           assert(Hcons0: DisjointFreeSlotsLists s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold DisjointFreeSlotsLists in *.
           intros pd1 pd2 HisPDTpd1 HisPDTpd2 HpdNotEq.
           assert(HisPDTpd1s0: isPDT pd1 s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDTpd1. simpl in HisPDTpd1.
             destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity in HisPDTpd1; intuition.
           }
           assert(HisPDTpd2s0: isPDT pd2 s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDTpd2. simpl in HisPDTpd2.
             destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity in HisPDTpd2; intuition.
           }
           specialize(Hcons0 pd1 pd2 HisPDTpd1s0 HisPDTpd2s0 HpdNotEq).
           destruct Hcons0 as [optionFreeSlotsList1 (optionFreeSlotsList2 & (HoptionFreeSlotsList1 &
                     (HwellFormed1 & (HoptionFreeSlotsList2 & (HwellFormed2 & Hdisjoint)))))].
           exists optionFreeSlotsList1. exists optionFreeSlotsList2.
           assert(HgetFrees1: optionFreeSlotsList1 = getFreeSlotsList pd1 s1).
           {
             subst optionFreeSlotsList1. apply eq_sym. apply HgetFreeSlotsListEq. assumption.
             rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr pd1) eqn:HbeqBlockPd1.
             - (* blockInParentPartitionAddr = pd1 *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPd1. rewrite HbeqBlockPd1 in *.
               unfold isPDT in HisPDTpd1s0. rewrite HlookupBlocks0 in HisPDTpd1s0. exfalso;congruence.
             - (* blockInParentPartitionAddr <> pd1 *)
               rewrite <-beqAddrFalse in HbeqBlockPd1. rewrite removeDupIdentity; intuition.
           }
           assert(HgetFrees2: optionFreeSlotsList2 = getFreeSlotsList pd2 s1).
           {
             subst optionFreeSlotsList2. apply eq_sym. apply HgetFreeSlotsListEq. assumption.
             rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr pd2) eqn:HbeqBlockPd2.
             - (* blockInParentPartitionAddr = pd2 *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPd2. rewrite HbeqBlockPd2 in *.
               unfold isPDT in HisPDTpd2s0. rewrite HlookupBlocks0 in HisPDTpd2s0. exfalso; congruence.
             - (* blockInParentPartitionAddr <> pd2 *)
               rewrite <-beqAddrFalse in HbeqBlockPd2. rewrite removeDupIdentity; intuition.
           }
           intuition.
           (* END DisjointFreeSlotsLists *)
         }

         assert(inclFreeSlotsBlockEntries s1).
         { (* BEGIN inclFreeSlotsBlockEntries s1 *)
           assert(Hcons0: inclFreeSlotsBlockEntries s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold inclFreeSlotsBlockEntries in *.
           intros pd HisPDT.
           assert(HlookupPdEq: lookup pd (memory s1) beqAddr = lookup pd (memory s0) beqAddr).
           {
             rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd.
             { (* blockInParentPartitionAddr = pd *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPd. rewrite HbeqBlockPd in *. unfold isPDT in HisPDT.
               rewrite HlookupBlocks1 in HisPDT. exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> pd *)
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; intuition.
           }
           assert(HisPDTs0: isPDT pd s0).
           {
             unfold isPDT in *. rewrite HlookupPdEq in HisPDT. assumption.
           }
           specialize(Hcons0 pd HisPDTs0).
           assert(HgetFreeEq: getFreeSlotsList pd s1 = getFreeSlotsList pd s0).
           { apply HgetFreeSlotsListEq; assumption. }
           rewrite HgetFreeEq.
           assert(HgetKSEq: getKSEntries pd s1 = getKSEntries pd s0).
           {
             rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           rewrite HgetKSEq. assumption.
           (* END inclFreeSlotsBlockEntries *)
         }

         assert(DisjointKSEntries s1).
         { (* BEGIN DisjointKSEntries s1 *)
           assert(Hcons0: DisjointKSEntries s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           assert(Hstructs0: StructurePointerIsKS s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
           (* END DisjointKSEntries *)
         }

         assert(noDupPartitionTree s1).
         { (* BEGIN noDupPartitionTree s1 *)
           assert(Hcons0: noDupPartitionTree s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold noDupPartitionTree in *.
           rewrite HgetPartEq. assumption.
           (* END noDupPartitionTree *)
         }

         assert(isParent s1).
         { (* BEGIN isParent s1 *)
           assert(Hcons0: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold isParent in *.
           intros part parent Hparent'IsPart HpartitionIsChild.
           rewrite HgetPartEq in Hparent'IsPart.
           assert(HgetChildrenEq: getChildren parent s1 = getChildren parent s0).
           {
             rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry.
             - apply partitionsArePDT; try(unfold consistency in *; unfold consistency1 in *; intuition).
             - assumption.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
           }
           rewrite HgetChildrenEq in HpartitionIsChild.
           specialize(Hcons0 part parent Hparent'IsPart HpartitionIsChild).
           unfold StateLib.pdentryParent in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart.
           { (* blockInParentPartitionAddr = partition *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *.
             rewrite HlookupBlocks0 in Hcons0. congruence.
           }
           (* blockInParentPartitionAddr <> partition *)
           rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity; intuition.
           (* END isParent *)
         }

         assert(isChild s1).
         { (* BEGIN isChild s1 *)
           assert(Hcons0: isChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold isChild in *.
           intros part parent HpartIsPartition HparentIsParent.
           rewrite HgetPartEq in HpartIsPartition.
           assert(HparentIsParents0: StateLib.pdentryParent part parent s0).
           {
             unfold StateLib.pdentryParent in *. rewrite Hs1 in HparentIsParent. simpl in HparentIsParent.
             destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart.
             { (* blockInParentPartitionAddr = part *)
               rewrite <-DTL.beqAddrTrue in HbeqBlockPart. rewrite HbeqBlockPart in *.
               exfalso; congruence.
             }
             (* blockInParentPartitionAddr <> part *)
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HparentIsParent; intuition.
           }
           specialize(Hcons0 part parent HpartIsPartition HparentIsParents0).
           assert(HgetChildrenEq: getChildren parent s1 = getChildren parent s0).
           {
             rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry.
             - unfold isPDT. unfold StateLib.pdentryParent in HparentIsParents0.
               destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               assert(HparentOfPart: parentOfPartitionIsPartition s0)
                     by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold parentOfPartitionIsPartition in HparentOfPart.
               specialize(HparentOfPart part p HlookupPart).
               destruct HparentOfPart as [Hparent'IsPart (HparentOfRoot & HparentPartNotEq)].
               destruct (beqAddr part constantRootPartM) eqn:HbeqPartRoot.
               { (* part = constantRootPartM *)
                 rewrite <-DTL.beqAddrTrue in HbeqPartRoot. specialize(HparentOfRoot HbeqPartRoot).
                 rewrite HparentOfRoot in *. subst parent.
                 assert(Hnull: nullAddrExists s0)
                      by (unfold consistency in *; unfold consistency1 in *; intuition).
                 unfold nullAddrExists in Hnull. unfold isPADDR in Hnull.
                 unfold getChildren in Hcons0.
                 assert(Hcontra: ~In part []) by (apply in_nil).
                 destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
                 destruct v; try(exfalso; congruence).
               }
               (* part <> constantRootPartM *)
               rewrite <-beqAddrFalse in HbeqPartRoot. specialize(Hparent'IsPart HbeqPartRoot).
               destruct Hparent'IsPart as ([parentEntry Hparent'IsPart] & _). subst parent.
               rewrite Hparent'IsPart. trivial.
             - assumption.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
             - unfold CBlockEntry.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl. reflexivity.
           }
           rewrite HgetChildrenEq. assumption.
           (* END isChild *)
         }

         assert(noDupKSEntriesList s1).
         { (* BEGIN noDupKSEntriesList s1 *)
           assert(Hcons0: noDupKSEntriesList s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold noDupKSEntriesList in *.
           intros part HisPDT.
           assert(HisPDTs0: isPDT part s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDT. simpl in HisPDT.
             destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart;
                   try(exfalso; congruence).
             (* blockInParentPartitionAddr <> part *)
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HisPDT; intuition.
           }
           specialize(Hcons0 part HisPDTs0).
           assert(HgetKSEq: getKSEntries part s1 = getKSEntries part s0).
           {
             rewrite Hs1. apply getKSEntriesEqBE. unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           rewrite HgetKSEq. assumption.
           (* END noDupKSEntriesList *)
         }

         assert(noDupMappedBlocksList s1).
         { (* BEGIN noDupMappedBlocksList s1 *)
           assert(Hcons0: noDupMappedBlocksList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold noDupMappedBlocksList in *.
           intros part HisPDT.
           assert(HisPDTs0: isPDT part s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDT. simpl in HisPDT.
             destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart;
                   try(exfalso; congruence).
             (* blockInParentPartitionAddr <> partition *)
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HisPDT; intuition.
           }
           specialize(Hcons0 part HisPDTs0).
           assert(HgetMappedEq: getMappedBlocks part s1 = getMappedBlocks part s0).
           {
             rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
             unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
             simpl. reflexivity.
           }
           rewrite HgetMappedEq. assumption.
           (* END noDupMappedBlocksList *)
         }

         assert(wellFormedBlock s1).
         { (* BEGIN wellFormedBlock s1 *)
           assert(bentryPFlag blockInParentPartitionAddr true s0).
           {
             unfold bentryPFlag in *. rewrite HlookupBlocks0. rewrite HlookupBlocks1 in HPFlag.
             rewrite HnewBentry in HPFlag. simpl in HPFlag. assumption.
           }
           assert(Hcons0: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
           apply wellFormedBlockPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
           (* END wellFormedBlock *)
         }

         assert(parentOfPartitionIsPartition s1).
         { (* BEGIN parentOfPartitionIsPartition s1 *)
           unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
           apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
           (* END parentOfPartitionIsPartition *)
         }

         assert(NbFreeSlotsISNbFreeSlotsInList s1).
         { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s1 *)
           assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold NbFreeSlotsISNbFreeSlotsInList in *.
           intros pd nbfreeslots HisPDT HnbFreeSlots.
           assert(HisPDTs0: isPDT pd s0).
           {
             unfold isPDT in *. rewrite Hs1 in HisPDT. simpl in HisPDT.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity in HisPDT; intuition.
           }
           assert(HnbFreeSlotss0: pdentryNbFreeSlots pd nbfreeslots s0).
           {
             unfold pdentryNbFreeSlots in *. rewrite Hs1 in HnbFreeSlots. simpl in HnbFreeSlots.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity in HnbFreeSlots; intuition.
           }
           specialize(Hcons0 pd nbfreeslots HisPDTs0 HnbFreeSlotss0).
           destruct Hcons0 as [optionFreeSlotsList (HgetFreeSlots & (HwellFormedList &
                   HnbFreeSlotsIsLength))].
           exists optionFreeSlotsList. split.
           - unfold getFreeSlotsList in *. rewrite Hs1. simpl. unfold isPDT in HisPDT. rewrite Hs1 in HisPDT.
             simpl in HisPDT.
             destruct (beqAddr blockInParentPartitionAddr pd) eqn:HbeqBlockPd; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPd. rewrite removeDupIdentity; try(intuition; congruence).
             destruct (lookup pd (memory s0) beqAddr) eqn:HlookupPds0; try(assumption).
             destruct v; try(assumption).
             destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull; try(assumption).
             assert(HbeqFirstFreeBlock: firstfreeslot p <> blockInParentPartitionAddr).
             {
               assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s0)
                     by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold FirstFreeSlotPointerIsBEAndFreeSlot in HfirstFree.
               rewrite <-beqAddrFalse in HbeqFirstFreeNull.
               specialize(HfirstFree pd p HlookupPds0 HbeqFirstFreeNull).
               destruct HfirstFree as [HfirstIsBE HfirstIsFree].
               intro Hcontra. rewrite Hcontra in HfirstIsFree. congruence.
             }
             assert(HnoDups0: NoDupInFreeSlotsList s0)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
             unfold NoDupInFreeSlotsList in HnoDups0.
             specialize(HnoDups0 pd p HlookupPds0).
             destruct HnoDups0 as [optionFreeSlotsListCopy (HoptionListCopy & (HwellFormedListCopy &
                                                 HnoDupListCopy))].
             unfold getFreeSlotsList in HoptionListCopy. rewrite HlookupPds0 in HoptionListCopy.
             rewrite HbeqFirstFreeNull in HoptionListCopy. subst optionFreeSlotsListCopy.
             subst optionFreeSlotsList. apply eq_sym.
             apply getFreeSlotsListRecEqBE; try(intuition; congruence).
             + unfold isBE. rewrite HlookupBlocks0. trivial.
             + intro Hcontra.
               set(optionFreeSlotsList:=
                         getFreeSlotsListRec (maxIdx + 1) (firstfreeslot p) s0 (ADT.nbfreeslots p)).
               assert(HisInGetFree: optionFreeSlotsList = getFreeSlotsList pd s0
                                     /\ wellFormedFreeSlotsList optionFreeSlotsList <> False).
               {
                 split.
                 - unfold getFreeSlotsList. rewrite HlookupPds0. rewrite HbeqFirstFreeNull. intuition.
                 - intuition.
               }
               assert(HfreeSlotsAreFree: freeSlotsListIsFreeSlot s0)
                     by (unfold consistency in *; unfold consistency1 in *; intuition).
               unfold freeSlotsListIsFreeSlot in HfreeSlotsAreFree.
               assert(HisPDTCopy: isPDT pd s0) by (unfold isPDT; rewrite HlookupPds0; trivial).
               assert(HinList: filterOptionPaddr optionFreeSlotsList = filterOptionPaddr optionFreeSlotsList
                       /\ In blockInParentPartitionAddr (filterOptionPaddr optionFreeSlotsList)).
               { intuition. }
               rewrite <-beqAddrFalse in HbeqBlockNull.
               specialize(HfreeSlotsAreFree pd blockInParentPartitionAddr optionFreeSlotsList
                         (filterOptionPaddr optionFreeSlotsList) HisPDTCopy HisInGetFree HinList 
                         HbeqBlockNull).
               congruence.
           - intuition.
           (* END NbFreeSlotsISNbFreeSlotsInList *)
         }

         assert(maxNbPrepareIsMaxNbKernels s1).
         { (* BEGIN maxNbPrepareIsMaxNbKernels s1 *)
           assert(Hcons0: maxNbPrepareIsMaxNbKernels s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold maxNbPrepareIsMaxNbKernels in *.
           intros part kernList HisKernList.
           assert(HisKernLists0: isListOfKernels kernList part s0).
           {
             apply isListOfKernelsEqBE with blockInParentPartitionAddr newBentry; try(intuition; congruence).
           }
           specialize(Hcons0 part kernList HisKernLists0). assumption.
           (* END maxNbPrepareIsMaxNbKernels *)
         }

         assert(blockInChildHasAtLeastEquivalentBlockInParent s1).
         { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s1 *)
           assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0)
                  by (unfold consistency in *; unfold consistency1 in *; intuition).
           unfold blockInChildHasAtLeastEquivalentBlockInParent in *.
           intros parentPart child block startChild endChild Hparent'IsPart HchildIsChild HblockMapped HstartChild
                HendChild HPFlagChild. rewrite HgetPartEq in Hparent'IsPart.
           assert(HparentIsPDT: isPDT parentPart s0).
           {
             unfold consistency in Hconsists0. unfold consistency1 in Hconsists0. apply partitionsArePDT;
                    intuition.
           }
           assert(HgetChildrenEq: getChildren parentPart s1 = getChildren parentPart s0).
           {
             rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry; try(assumption);
                  rewrite <-HnewB; rewrite HnewBentry; simpl; reflexivity.
           }
           rewrite HgetChildrenEq in HchildIsChild.
           assert(HgetMappedEq: getMappedBlocks child s1 = getMappedBlocks child s0).
           {
             rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
             rewrite <-HnewB; rewrite HnewBentry; simpl; reflexivity.
           }
           rewrite HgetMappedEq in HblockMapped.
           assert(Hprops: bentryStartAddr block startChild s0 /\ bentryEndAddr block endChild s0
                          /\ bentryPFlag block true s0).
           {
             unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
             rewrite Hs1 in HstartChild. rewrite Hs1 in HendChild. rewrite Hs1 in HPFlagChild. simpl in *.
             rewrite <-HnewB in *. rewrite HnewBentry in *.
             destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
             - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block. simpl in *. rewrite HlookupBlocks0.
               intuition.
             - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in *; intuition.
           }
           destruct Hprops as (HstartChilds0 & HendChilds0 & HPFlagChilds0).
           specialize(Hcons0 parentPart child block startChild endChild Hparent'IsPart HchildIsChild HblockMapped
                HstartChilds0 HendChilds0 HPFlagChilds0).
           assert(HgetMappedParentEq: getMappedBlocks parentPart s1 = getMappedBlocks parentPart s0).
           {
             rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
             rewrite <-HnewB; rewrite HnewBentry; simpl; reflexivity.
           }
           rewrite HgetMappedParentEq. destruct Hcons0 as [blockParent [startParent [endParent
                (HblockParentMapped & HstartParent & HendParent & HstartProp & HendProp)]]].
           exists blockParent. exists startParent. exists endParent. split. assumption.
           unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr blockParent) eqn:HbeqBlockBlock.
           - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockParent. rewrite HlookupBlocks0 in *.
             rewrite <-HnewB. rewrite HnewBentry. simpl. intuition.
           - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in *; intuition.
           (* END blockInChildHasAtLeastEquivalentBlockInParent *)
         }

         assert(partitionTreeIsTree s1).
         { (* BEGIN partitionTreeIsTree s1 *)
           unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
           apply partitionTreeIsTreePreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
             try(intuition; congruence).
           (* END partitionTreeIsTree *)
         }

         assert(kernelEntriesAreValid s1).
         { (* BEGIN kernelEntriesAreValid s1 *)
           assert(Hcons0: kernelEntriesAreValid s0) by (unfold consistency in *; unfold consistency1 in *;
                intuition).
           intros kernel index HKS HidxBounded.
           assert(HKSs0: isKS kernel s0).
           {
             unfold isKS in *. rewrite Hs1 in HKS. simpl in HKS.
             destruct (beqAddr blockInParentPartitionAddr kernel) eqn:HbeqBlockKern.
             - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0.
               unfold CBlockEntry in HKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HKS. assumption.
             - rewrite <-beqAddrFalse in HbeqBlockKern. rewrite removeDupIdentity in HKS; intuition.
           }
           specialize(Hcons0 kernel index HKSs0 HidxBounded). unfold isBE. unfold isBE in Hcons0.
           rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (kernel + index))) eqn:HbeqBlockKernIdx;
                try(trivial). rewrite <-beqAddrFalse in HbeqBlockKernIdx. rewrite removeDupIdentity; intuition.
           (* END kernelEntriesAreValid *)
         }

         assert(nextKernelIsValid s1).
         { (* BEGIN nextKernelIsValid s1 *)
           assert(Hcons0: nextKernelIsValid s0) by (unfold consistency in *; unfold consistency1 in *;
                intuition).
           intros kernel HKS.
           assert(HKSs0: isKS kernel s0).
           {
             unfold isKS in *. rewrite Hs1 in HKS. simpl in HKS.
             destruct (beqAddr blockInParentPartitionAddr kernel) eqn:HbeqBlockKern.
             - rewrite <-DTL.beqAddrTrue in HbeqBlockKern. subst kernel. rewrite HlookupBlocks0.
               unfold CBlockEntry in HKS.
               destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
               simpl in HKS. assumption.
             - rewrite <-beqAddrFalse in HbeqBlockKern. rewrite removeDupIdentity in HKS; intuition.
           }
           specialize(Hcons0 kernel HKSs0).
           destruct Hcons0 as (HnextOffValid & [nextAddr (HlookupNext & HnextType)]). split. assumption.
           exists nextAddr. split.
           intro Hp. specialize(HlookupNext Hp). rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr {| p:= kernel+nextoffset; Hp:= Hp |}) eqn:HbeqBlockNext.
           {
             rewrite <-DTL.beqAddrTrue in HbeqBlockNext. rewrite <-HbeqBlockNext in HlookupNext.
             exfalso; congruence.
           }
           rewrite <-beqAddrFalse in HbeqBlockNext. rewrite removeDupIdentity; intuition.
           destruct HnextType as [HnextIsKS | Hnull]; try(right; assumption). left. unfold isKS.
           unfold isKS in HnextIsKS. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr nextAddr) eqn:HbeqBlockNextKern.
           - rewrite <-DTL.beqAddrTrue in HbeqBlockNextKern. subst nextAddr. rewrite HlookupBlocks0 in HnextIsKS.
             unfold CBlockEntry.
             destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia).
             simpl. assumption.
           - rewrite <-beqAddrFalse in HbeqBlockNextKern. rewrite removeDupIdentity; intuition.
           (* END nextKernelIsValid *)
         }

         assert(noDupListOfKerns s1).
         { (* BEGIN noDupListOfKerns s1 *)
           assert(Hcons0: noDupListOfKerns s0) by (unfold consistency in *; unfold consistency1 in *;
                intuition).
           intros part kernList HkernList.
           assert(HkernLists0: isListOfKernels kernList part s0).
           {
             apply isListOfKernelsEqBE with blockInParentPartitionAddr newBentry; try(assumption).
             rewrite Hs1 in HkernList. rewrite <-HnewB in HkernList. assumption.
           }
           specialize(Hcons0 part kernList HkernLists0). assumption.
           (* END noDupListOfKerns *)
         }

         assert(MPUsizeIsBelowMax s1).
         { (* BEGIN MPUsizeIsBelowMax s1 *)
           assert(Hcons0: MPUsizeIsBelowMax s0)
                by (unfold consistency in *; unfold consistency1 in *; intuition).
           intros part MPUlist HMPUpart.
           assert(HMPUs0: pdentryMPU part MPUlist s0).
           {
             unfold pdentryMPU in *. rewrite Hs1 in HMPUpart. simpl in HMPUpart.
             destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HMPUpart; intuition.
           }
           specialize(Hcons0 part MPUlist HMPUs0). assumption.
           (* END MPUsizeIsBelowMax *)
         }

         assert(HoriginProp: originIsParentBlocksStart s1).
         { (* BEGIN originIsParentBlocksStart s1 *)
           assert(Hcons0: originIsParentBlocksStart s0) by (unfold consistency1 in *; intuition).
           intros part pdentry block scentryaddr scorigin HpartBisIsPart HlookupPartBis HblockMapped Hsce
              Horigin. rewrite HgetPartEq in HpartBisIsPart.
           assert(HlookupPartBiss0: lookup part (memory s0) beqAddr = Some (PDT pdentry)).
           {
             rewrite Hs1 in HlookupPartBis. simpl in HlookupPartBis.
             destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPartBis; intuition.
           }
           assert(HgetBlocksEq: getMappedBlocks part s1 = getMappedBlocks part s0).
           {
             destruct (beqAddr part pdparent) eqn:HbeqPartParent.
             - rewrite <-DTL.beqAddrTrue in HbeqPartParent. subst part. assumption.
             - rewrite <-beqAddrFalse in HbeqPartParent. rewrite Hs1.
               apply getMappedBlocksEqBENoChange with bentry. assumption. rewrite <-HnewB. rewrite HnewBentry.
               simpl. reflexivity.
           }
           rewrite HgetBlocksEq in HblockMapped.
           assert(Horigins0: scentryOrigin scentryaddr scorigin s0).
           {
             unfold scentryOrigin in *. rewrite Hs1 in Horigin. simpl in Horigin.
             destruct (beqAddr blockInParentPartitionAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity in Horigin; intuition.
           }
           specialize(Hcons0 part pdentry block scentryaddr scorigin HpartBisIsPart HlookupPartBiss0 HblockMapped
              Hsce Horigins0). destruct Hcons0 as (Hcons0 & HstartAbove). split.
           - intro HbeqPartRoot. specialize(Hcons0 HbeqPartRoot).
             destruct Hcons0 as [blockParent (HblockParentMapped & HstartParent & Hincl)]. exists blockParent.
             assert(HgetBlocksParentEq: getMappedBlocks (parent pdentry) s1 = getMappedBlocks (parent pdentry) s0).
             {
               destruct (beqAddr (parent pdentry) pdparent) eqn:HbeqPartParent.
               - rewrite <-DTL.beqAddrTrue in HbeqPartParent. rewrite HbeqPartParent in *. assumption.
               - rewrite <-beqAddrFalse in HbeqPartParent. rewrite Hs1.
                 apply getMappedBlocksEqBENoChange with bentry. assumption. rewrite <-HnewB. rewrite HnewBentry.
                 simpl. reflexivity.
             }
             rewrite HgetBlocksParentEq. split. assumption. split.
             + unfold bentryStartAddr in *. rewrite Hs1. simpl.
               destruct (beqAddr blockInParentPartitionAddr blockParent) eqn:HbeqBlocks.
               * rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0 in HstartParent.
                 rewrite <-HnewB. rewrite HnewBentry. simpl. assumption.
               * rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; intuition.
             + intros addr HaddrInBlock.
               assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
               {
                 simpl. simpl in HaddrInBlock. rewrite Hs1 in HaddrInBlock. simpl in HaddrInBlock.
                 destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
                 * rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0.
                   rewrite <-HnewB in HaddrInBlock. rewrite HnewBentry in HaddrInBlock. simpl in HaddrInBlock.
                   assumption.
                 * rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity in HaddrInBlock; intuition.
               }
               specialize(Hincl addr HaddrInBlocks0). simpl. simpl in Hincl. rewrite Hs1. simpl.
               destruct (beqAddr blockInParentPartitionAddr blockParent) eqn:HbeqBlocks.
               * rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0 in Hincl.
                 rewrite <-HnewB. rewrite HnewBentry. simpl. assumption.
               * rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; intuition.
           - intros startBlock HstartBlock. apply HstartAbove. unfold bentryStartAddr in HstartBlock.
             rewrite Hs1 in HstartBlock. simpl in HstartBlock.
             destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
             + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. unfold bentryStartAddr. rewrite HlookupBlocks0.
               rewrite <-HnewB in HstartBlock. rewrite HnewBentry in HstartBlock. simpl in HstartBlock. assumption.
             + rewrite <-beqAddrFalse in HbeqBlocks.
               rewrite removeDupIdentity in HstartBlock; try(apply not_eq_sym); assumption.
           (* END originIsParentBlocksStart *)
         }

         assert(HnextProp: nextImpliesBlockWasCut s1).
         { (* BEGIN nextImpliesBlockWasCut s1 *)
           assert(Hcons0: nextImpliesBlockWasCut s0) by (unfold consistency1 in *; intuition).
           intros part pdentry block scentryaddr scnext endBlock HpartBisIsPart HlookupPartBis HblockMapped
              HendBlock Hsce HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartEq in HpartBisIsPart.
           assert(HlookupPartBiss0: lookup part (memory s0) beqAddr = Some (PDT pdentry)).
           {
             rewrite Hs1 in HlookupPartBis. simpl in HlookupPartBis.
             destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPartBis; intuition.
           }
           assert(HgetBlocksEq: getMappedBlocks part s1 = getMappedBlocks part s0).
           {
             destruct (beqAddr part pdparent) eqn:HbeqPartParent.
             - rewrite <-DTL.beqAddrTrue in HbeqPartParent. subst part. assumption.
             - rewrite <-beqAddrFalse in HbeqPartParent. rewrite Hs1.
               apply getMappedBlocksEqBENoChange with bentry. assumption. rewrite <-HnewB. rewrite HnewBentry.
               simpl. reflexivity.
           }
           rewrite HgetBlocksEq in HblockMapped.
           assert(HendBlocks0: bentryEndAddr block endBlock s0).
           {
             unfold bentryEndAddr in *. rewrite Hs1 in HendBlock. simpl in HendBlock.
             destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
             - rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0.
               rewrite <-HnewB in HendBlock. rewrite HnewBentry in HendBlock. simpl in HendBlock. assumption.
             - rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity in HendBlock; intuition.
           }
           assert(Hnexts0: scentryNext scentryaddr scnext s0).
           {
             unfold scentryNext in *. rewrite Hs1 in Hnext. simpl in Hnext.
             destruct (beqAddr blockInParentPartitionAddr scentryaddr) eqn:HbeqBlockSce; try(exfalso; congruence).
             rewrite <-beqAddrFalse in HbeqBlockSce. rewrite removeDupIdentity in Hnext; intuition.
           }
           specialize(Hcons0 part pdentry block scentryaddr scnext endBlock HpartBisIsPart HlookupPartBiss0
              HblockMapped HendBlocks0 Hsce HbeqNextNull Hnexts0 HbeqPartRoot).
           destruct Hcons0 as [blockParent [endParent (HblockParentmapped & HendParent & Hends & Hincl)]].
           exists blockParent. exists endParent.
           assert(HgetBlocksParentEq: getMappedBlocks (parent pdentry) s1 = getMappedBlocks (parent pdentry) s0).
           {
             destruct (beqAddr (parent pdentry) pdparent) eqn:HbeqPartParent.
             - rewrite <-DTL.beqAddrTrue in HbeqPartParent. rewrite HbeqPartParent in *. assumption.
             - rewrite <-beqAddrFalse in HbeqPartParent. rewrite Hs1.
               apply getMappedBlocksEqBENoChange with bentry. assumption. rewrite <-HnewB. rewrite HnewBentry.
               simpl. reflexivity.
           }
           rewrite HgetBlocksParentEq. split. assumption. split; try(split; try(assumption)).
           - unfold bentryEndAddr in *. rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr blockParent) eqn:HbeqBlocks.
             + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0 in HendParent.
               rewrite <-HnewB. rewrite HnewBentry. simpl. assumption.
             + rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; intuition.
           - intros addr HaddrInBlock.
             assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
             {
               simpl. simpl in HaddrInBlock. rewrite Hs1 in HaddrInBlock. simpl in HaddrInBlock.
               destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
               + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0.
                 rewrite <-HnewB in HaddrInBlock. rewrite HnewBentry in HaddrInBlock. simpl in HaddrInBlock.
                 assumption.
               + rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity in HaddrInBlock; intuition.
             }
             specialize(Hincl addr HaddrInBlocks0). simpl. simpl in Hincl. rewrite Hs1. simpl.
             destruct (beqAddr blockInParentPartitionAddr blockParent) eqn:HbeqBlocks.
             + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HlookupBlocks0 in Hincl.
               rewrite <-HnewB. rewrite HnewBentry. simpl. assumption.
             + rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity; intuition.
           (* END nextImpliesBlockWasCut *)
         }
         unfold consistency1. intuition.
       }

       assert(HnoDups1: noDupUsedPaddrList s1).
       { (* BEGIN noDupUsedPaddrList s1 *)
           unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
           apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
         (* END noDupUsedPaddrList *)
       }

       assert(Hshareds1: sharedBlockPointsToChild s1).
       { (* BEGIN sharedBlockPointsToChild s1 *)
         assert(Hcons0: sharedBlockPointsToChild s0)
              by (unfold consistency in *; unfold consistency2 in *; intuition).
         unfold sharedBlockPointsToChild in *.
         intros parent child addr parentblock sh1entryaddr Hparent'IsPart HchildIsChild HaddrIsInChild
             HaddrIsInParentBlock HparentBlockIsMappedInParent Hsh1ParentBlock.
         rewrite HgetPartEq in Hparent'IsPart.
         assert(HgetChildrenEq: getChildren parent s1 = getChildren parent s0).
         {
           rewrite Hs1.
           apply getChildrenEqBENoStartNoPresentChange with bentry;
                 try(assumption);
                 try(unfold CBlockEntry;
                     destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                     simpl; reflexivity).
           apply partitionsArePDT; unfold consistency in *; unfold consistency1 in *; intuition.
         }
         rewrite HgetChildrenEq in HchildIsChild.
         assert(HgetUsedPaddrEq: getUsedPaddr child s1 = getUsedPaddr child s0).
         {
           unfold getUsedPaddr.
           assert(isPDT child s0).
           {
             apply childrenArePDT with parent; unfold consistency in *; unfold consistency1 in *; intuition.
           }
           assert(HgetConfigEq: getConfigPaddr child s1 = getConfigPaddr child s0).
           {
             rewrite Hs1. apply getConfigPaddrEqBE; try(assumption).
             unfold isBE. rewrite HlookupBlocks0. trivial.
           }
           assert(HgetMappedPaddrEq: getMappedPaddr child s1 = getMappedPaddr child s0).
           {
             rewrite Hs1.
             apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
                 try(assumption);
                 try(unfold CBlockEntry;
                     destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                     simpl; reflexivity).
           }
           rewrite HgetConfigEq. rewrite HgetMappedPaddrEq. reflexivity.
         }
         rewrite HgetUsedPaddrEq in HaddrIsInChild.
         assert(HgetPaddrEq: getAllPaddrAux [parentblock] s1 = getAllPaddrAux [parentblock] s0).
         {
           rewrite Hs1. apply getAllPaddrAuxEqBEStartEndNoChange with bentry;
                 try(assumption);
                 try(unfold CBlockEntry;
                     destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                     simpl; reflexivity).
         }
         rewrite HgetPaddrEq in HaddrIsInParentBlock.
         assert(HgetMappedEq: getMappedBlocks parent s1 = getMappedBlocks parent s0).
         {
           rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry;
                 try(assumption);
                 try(unfold CBlockEntry;
                     destruct (Compare_dec.lt_dec (blockindex bentry) kernelStructureEntriesNb); try(lia);
                     simpl; reflexivity).
         }
         rewrite HgetMappedEq in HparentBlockIsMappedInParent.
         assert(Hsh1ParentBlocks0: sh1entryAddr parentblock sh1entryaddr s0).
         {
           unfold sh1entryAddr in *. rewrite Hs1 in Hsh1ParentBlock. simpl in Hsh1ParentBlock.
           destruct (beqAddr blockInParentPartitionAddr parentblock) eqn:HbeqBlockParentBlock.
           - (* blockInParentPartitionAddr = parentblock *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlock. rewrite HbeqBlockParentBlock in *.
             rewrite HlookupBlocks0. assumption.
           - (* blockInParentPartitionAddr <> parentblock *)
             rewrite <-beqAddrFalse in HbeqBlockParentBlock.
             rewrite removeDupIdentity in Hsh1ParentBlock; intuition.
         }
         specialize(Hcons0 parent child addr parentblock sh1entryaddr Hparent'IsPart HchildIsChild HaddrIsInChild
                      HaddrIsInParentBlock HparentBlockIsMappedInParent Hsh1ParentBlocks0).
         destruct Hcons0 as [HPDchild | HPDflag].
         - left. unfold sh1entryPDchild in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (parentblock + sh1offset)))
                   eqn:HbeqBlockParentBlocksh1.
           { (* blockInParentPartitionAddr = CPaddr (parentblock + sh1offset) *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlocksh1. rewrite <-HbeqBlockParentBlocksh1 in *.
             rewrite HlookupBlocks0 in HPDchild. congruence.
           }
           (* blockInParentPartitionAddr <> CPaddr (parentblock + sh1offset) *)
           rewrite <-beqAddrFalse in HbeqBlockParentBlocksh1. rewrite removeDupIdentity; intuition.
         - right. unfold sh1entryPDflag in *. rewrite Hs1. simpl.
           destruct (beqAddr blockInParentPartitionAddr (CPaddr (parentblock + sh1offset)))
                   eqn:HbeqBlockParentBlocksh1.
           { (* blockInParentPartitionAddr = CPaddr (parentblock + sh1offset) *)
             rewrite <-DTL.beqAddrTrue in HbeqBlockParentBlocksh1. rewrite <-HbeqBlockParentBlocksh1 in *.
             rewrite HlookupBlocks0 in HPDflag. congruence.
           }
           (* blockInParentPartitionAddr <> CPaddr (parentblock + sh1offset) *)
           rewrite <-beqAddrFalse in HbeqBlockParentBlocksh1. rewrite removeDupIdentity; intuition.
         (* END sharedBlockPointsToChild *)
       }

       assert(Hranges1: adressesRangePreservedIfOriginAndNextOk s1).
       { (* BEGIN adressesRangePreservedIfOriginAndNextOk s1 *)
         unfold adressesRangePreservedIfOriginAndNextOk in *. intros part pdentry block scentryaddr startBlock
             endBlock HpartBisIsPart HblockMappedPart HblockIsBE HstartBlock HendBlock HPFlagBlock Hscentryaddr
             Horigin Hnext HlookupPart HpartNotEqRoot.
         rewrite HgetPartEq in HpartBisIsPart.
         assert(HgetMappedPartEq: getMappedBlocks part s1 = getMappedBlocks part s0).
         {
           rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
           rewrite <-HnewB; rewrite HnewBentry; simpl; reflexivity.
         }
         rewrite HgetMappedPartEq in HblockMappedPart.
         assert(HblockIsBEs0: isBE block s0).
         {
           unfold isBE in *. rewrite Hs1 in HblockIsBE. simpl in HblockIsBE.
           destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
           - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block. rewrite HlookupBlocks0. trivial.
           - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HblockIsBE; intuition.
         }
         assert(Hblocks0: bentryStartAddr block startBlock s0 /\ bentryEndAddr block endBlock s0
                          /\ bentryPFlag block true s0).
         {
           unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
           rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock. rewrite Hs1 in HPFlagBlock. simpl in *.
           destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlockBlock.
           - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst block. rewrite HlookupBlocks0.
             rewrite <-HnewB in *. rewrite HnewBentry in *. simpl in *. split. assumption. split. assumption.
             assumption.
           - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in *; intuition.
         }
         destruct Hblocks0 as (HstartBlocks0 & HendBlocks0 & HPFlagBlocks0).
         assert(HlookupSCEEq: lookup scentryaddr (memory s1) beqAddr = lookup scentryaddr (memory s0) beqAddr).
         {
           unfold scentryOrigin in Horigin. rewrite Hs1. rewrite Hs1 in Horigin. simpl in *.
           destruct (beqAddr blockInParentPartitionAddr scentryaddr) eqn:HbeqBlockSCE; try(exfalso; congruence).
           rewrite <-beqAddrFalse in HbeqBlockSCE. rewrite removeDupIdentity; intuition.
         }
         unfold scentryOrigin in *. unfold scentryNext in *. rewrite HlookupSCEEq in *.
         rewrite Hs1 in HlookupPart. simpl in HlookupPart.
         destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
         rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPart;
               try(apply not_eq_sym; assumption).
         specialize(Hrange part pdentry block scentryaddr startBlock endBlock HpartBisIsPart HblockMappedPart
                    HblockIsBEs0 HstartBlocks0 HendBlocks0 HPFlagBlocks0 Hscentryaddr Horigin Hnext HlookupPart
                    HpartNotEqRoot).
         destruct Hrange as [blockParent (HblockParentMapped & HblockParentIsBE & HstartParent & HendParent)].
         exists blockParent.
         assert(HgetMappedEq: getMappedBlocks (parent pdentry) s1 = getMappedBlocks (parent pdentry) s0).
         {
           rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
           rewrite <-HnewB; rewrite HnewBentry; simpl; reflexivity.
         }
         rewrite HgetMappedEq. split. assumption. unfold isBE in *. unfold bentryStartAddr in *.
         unfold bentryEndAddr in *. rewrite Hs1. simpl.
         destruct (beqAddr blockInParentPartitionAddr blockParent) eqn:HbeqBlockBlock.
         - rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockParent. rewrite HlookupBlocks0 in *.
           rewrite <-HnewB in *. rewrite HnewBentry in *. simpl. split. trivial. split. assumption.
           assumption.
         - rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in *; intuition.
         (* END adressesRangePreservedIfOriginAndNextOk *)
       }

       assert(HchildBlockPropss1: childsBlocksPropsInParent s1).
       { (* BEGIN childsBlocksPropsInParent s1 *)
         unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
         rewrite HblockInMappedBlocksEqs1 in HblockInMappedBlocks.
         apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdparent pdentryParent
                blockInParentPartitionAddr bentry
                (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
           try(intuition; congruence).
         intros child blockChild startChild endChild HchildIsChild HblockChildMapped HstartChild HendChild
               HPFlagChild HstartProp HendProp.
         assert(HwellFormedBlock: wellFormedBlock s1) by (unfold consistency1 in Hconss1; intuition).
         assert(startaddr < endaddr).
         {
           specialize(HwellFormedBlock blockInParentPartitionAddr startaddr endaddr HPFlag HstartAddr HendAddr).
           destruct HwellFormedBlock. assumption.
         }
         assert(HwellFormedBlocks0: wellFormedBlock s0)
               by (unfold consistency in Hconsists0; unfold consistency1 in Hconsists0; intuition).
         assert(startChild < endChild).
         {
           specialize(HwellFormedBlocks0 blockChild startChild endChild HPFlagChild HstartChild HendChild).
           destruct HwellFormedBlocks0. assumption.
         }
         destruct HblockPart as [blockPart [bentryPart (HlookupBlockPart & HPFlagPart & HblockPartMapped
                    & HstartPart & HendPart & HcheckPart)]].
         assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryPart))
                                                                        (endAddr (blockrange bentryPart)))).
         {
           unfold bentryStartAddr in HstartPart. unfold bentryEndAddr in HendPart.
           rewrite HlookupBlockPart in *. rewrite <-HstartPart. rewrite <-HendPart.
           apply getAllPaddrBlockIncl; lia.
         }
         assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                       = Some (BE bentryChild)
                                                       /\ startChild = startAddr (blockrange bentryChild)
                                                       /\ endChild = endAddr (blockrange bentryChild)).
         {
           unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
           unfold bentryEndAddr in HendChild.
           destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
           destruct v; try(exfalso; congruence). exists b. intuition.
         }
         destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
         assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                         (endAddr (blockrange bentryChild)))).
         {
           subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
         }
         assert(HgetMappedEq: getMappedBlocks partition s1 = getMappedBlocks partition s0).
         {
           rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
           rewrite <-HnewB. rewrite HnewBentry. simpl. reflexivity.
         }
         rewrite HgetMappedEq in HblockPartMapped. clear HgetMappedEq.
         destruct (beqAddr child partition) eqn:HbeqChildPart.
         + rewrite <-DTL.beqAddrTrue in HbeqChildPart. subst child.
           destruct (beqAddr blockChild blockPart) eqn:HbeqBlockChildBlockPart.
           * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockPart. subst blockChild. unfold bentryStartAddr in *.
             unfold bentryEndAddr in *. rewrite Hs1 in HstartPart. rewrite Hs1 in HendPart. simpl in *.
             destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
             -- rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockPart. rewrite HlookupBlocks0 in *.
                rewrite <-HnewB in *. rewrite HnewBentry in *. simpl in *.
                rewrite <-HstartChild in HstartPart. rewrite <-HendChild in HendPart. split. assumption.
                assumption.
             -- rewrite <-beqAddrFalse in HbeqBlockBlock.
                rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
                rewrite HlookupBlockChild in *. rewrite <-HstartChild in HstartPart.
                rewrite <-HendChild in HendPart. split. assumption. assumption.
           * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockPart.
             assert(HpartIsPDT: isPDT partition s0) by (unfold isPDT; rewrite HlookupParts0; trivial).
             specialize(HnoDup partition HpartIsPDT). unfold getUsedPaddr in HnoDup.
             apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
             induction (getMappedBlocks partition s0).
             { intuition. }
             simpl in *. destruct HblockPartMapped as [Ha1IsPart | HblockPartMappedRec].
             -- subst a1. destruct HblockChildMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
                rewrite Hs1 in HlookupBlockPart. simpl in HlookupBlockPart.
                destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
                ++ rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockPart.
                   rewrite HlookupBlocks0 in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                   rewrite <-HnewB in HlookupBlockPart. rewrite HnewBentry in HlookupBlockPart.
                   simpl in HlookupBlockPart. injection HlookupBlockPart as HentriesEq.
                   rewrite <-HentriesEq in HstartChildInBlockBase. simpl in HstartChildInBlockBase.
                   destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
                   contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
                   rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
                ++ rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HlookupBlockPart;
                          try(apply not_eq_sym; assumption).
                   rewrite HlookupBlockPart in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                   destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
                   contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
                   rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
             -- destruct HblockChildMapped as [Hcontra | HblockChildIsMappedRec].
                ++ subst a1. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                   destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                   contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockPart. assumption. simpl.
                   rewrite Hs1 in HlookupBlockPart. simpl in HlookupBlockPart.
                   destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
                   ** rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockPart. rewrite HlookupBlocks0.
                      rewrite <-HnewB in HlookupBlockPart. rewrite HnewBentry in HlookupBlockPart.
                      simpl in HlookupBlockPart. injection HlookupBlockPart as HentriesEq.
                      rewrite <-HentriesEq in HstartChildInBlockBase. simpl in HstartChildInBlockBase.
                      rewrite app_nil_r. assumption.
                   ** rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HlookupBlockPart;
                            try(apply not_eq_sym; assumption).
                      rewrite HlookupBlockPart. rewrite app_nil_r. assumption.
                ++ destruct (lookup a1 (memory s0) beqAddr) eqn:HlookupA1; try(apply IHl; assumption).
                   destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                   destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
         + rewrite <-beqAddrFalse in HbeqChildPart.
           assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
           {
             apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
             rewrite app_nil_r. assumption.
           }
           assert(HstartInChild: In startChild (getUsedPaddr child s0)).
           {
             unfold getUsedPaddr. apply in_or_app. right. assumption.
           }
           assert(HstartInMappedBuild: In startChild (getMappedPaddr partition s0)).
           {
             apply addrInBlockIsMapped with blockPart; try(assumption). simpl.
             rewrite Hs1 in HlookupBlockPart. simpl in HlookupBlockPart.
             destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
             ** rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockPart. rewrite HlookupBlocks0.
                rewrite <-HnewB in HlookupBlockPart. rewrite HnewBentry in HlookupBlockPart.
                simpl in HlookupBlockPart. injection HlookupBlockPart as HentriesEq.
                rewrite <-HentriesEq in HstartChildInBlockBase. simpl in HstartChildInBlockBase.
                rewrite app_nil_r. assumption.
             ** rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HlookupBlockPart;
                      try(apply not_eq_sym; assumption).
                rewrite HlookupBlockPart. rewrite app_nil_r. assumption.
           }
           assert(HisChild: isChild s0)
                 by (unfold consistency in Hconsists0; unfold consistency1 in Hconsists0; intuition).
           assert(HpartIsChild: StateLib.pdentryParent partition pdparent s0).
           {
             unfold StateLib.pdentryParent. rewrite HlookupParts0. assumption.
           }
           specialize(HisChild partition pdparent HpartIsPart HpartIsChild).
           specialize(HPIs0 pdparent child partition HparentIsPart HchildIsChild HisChild HbeqChildPart
                       startChild HstartInChild).
           contradict HPIs0. unfold getUsedPaddr. apply in_or_app. right. assumption.
         (* END childsBlocksPropsInParent *)
       }

       assert(HPDChildProp: noChildImpliesAddressesNotShared s1).
       { (* BEGIN noChildImpliesAddressesNotShared s1 *)
         assert(Hcons0: noChildImpliesAddressesNotShared s0) by assumption.
         intros part pdentry block sh1entryaddr HpartBisIsPart HlookupPartBis HblockMapped Hsh1 HPDChild
            child addr HchildIsChild HaddrInBlock. rewrite HgetPartEq in HpartBisIsPart.
         assert(HlookupPartBiss0: lookup part (memory s0) beqAddr = Some (PDT pdentry)).
         {
           rewrite Hs1 in HlookupPartBis. simpl in HlookupPartBis.
           destruct (beqAddr blockInParentPartitionAddr part) eqn:HbeqBlockPart; try(exfalso; congruence).
           rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupPartBis; intuition.
         }
         assert(HgetBlocksEq: getMappedBlocks part s1 = getMappedBlocks part s0).
         {
           destruct (beqAddr part pdparent) eqn:HbeqPartParent.
           - rewrite <-DTL.beqAddrTrue in HbeqPartParent. subst part. assumption.
           - rewrite <-beqAddrFalse in HbeqPartParent. rewrite Hs1.
             apply getMappedBlocksEqBENoChange with bentry. assumption. rewrite <-HnewB. rewrite HnewBentry.
             simpl. reflexivity.
         }
         rewrite HgetBlocksEq in HblockMapped.
         assert(HPDChilds0: sh1entryPDchild sh1entryaddr nullAddr s0).
         {
           unfold sh1entryPDchild in *. rewrite Hs1 in HPDChild. simpl in HPDChild.
           destruct (beqAddr blockInParentPartitionAddr sh1entryaddr) eqn:HbeqBlockSh1;
              try(exfalso; congruence). rewrite <-beqAddrFalse in HbeqBlockSh1.
           rewrite removeDupIdentity in HPDChild; intuition.
         }
         assert(HgetChildrenEq: getChildren part s1 = getChildren part s0).
         {
           rewrite Hs1. apply getChildrenEqBENoStartNoPresentChange with bentry; try(assumption).
           - unfold isPDT. rewrite HlookupPartBiss0. trivial.
           - rewrite <-HnewB. rewrite HnewBentry. simpl. reflexivity.
           - rewrite <-HnewB. rewrite HnewBentry. simpl. reflexivity.
         }
         rewrite HgetChildrenEq in HchildIsChild.
         assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
         {
           simpl. simpl in HaddrInBlock. rewrite Hs1 in HaddrInBlock. simpl in HaddrInBlock.
           destruct (beqAddr blockInParentPartitionAddr block) eqn:HbeqBlocks.
           + rewrite <-DTL.beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupBlocks0.
             rewrite <-HnewB in HaddrInBlock. rewrite HnewBentry in HaddrInBlock. simpl in HaddrInBlock.
             assumption.
           + rewrite <-beqAddrFalse in HbeqBlocks. rewrite removeDupIdentity in HaddrInBlock; intuition.
         }
         specialize(Hcons0 part pdentry block sh1entryaddr HpartBisIsPart HlookupPartBiss0 HblockMapped Hsh1
            HPDChilds0 child addr HchildIsChild HaddrInBlocks0).
         assert(HgetPaddrEq: getMappedPaddr child s1 = getMappedPaddr child s0).
         {
           rewrite Hs1. apply getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry;
              try(assumption).
           - apply childrenArePDT with part; try(assumption). unfold consistency1 in *; intuition.
           - rewrite <-HnewB. rewrite HnewBentry. simpl. reflexivity.
           - rewrite <-HnewB. rewrite HnewBentry. simpl. reflexivity.
           - rewrite <-HnewB. rewrite HnewBentry. simpl. reflexivity.
         }
         rewrite HgetPaddrEq. assumption.
         (* END noChildImpliesAddressesNotShared *)
       }

       split.
       ++ (* consistency1 s *)
          (* Disjunction on the value of s *)
          destruct HpropsOr as [Hs1sEq | Hs].
          ** (* s = s1 *)
             rewrite Hs1sEq. assumption.
          ** (* s <> s1 *)
             destruct (beqAddr pdparent nullAddr) eqn:HbeqParentNull.
             {
               assert(HnullExists: nullAddrExists s1) by (unfold consistency1 in *; intuition).
               unfold nullAddrExists in HnullExists. unfold isPADDR in HnullExists.
               rewrite <-DTL.beqAddrTrue in HbeqParentNull. rewrite HbeqParentNull in *.
               rewrite HlookupParent in HnullExists. exfalso; congruence.
             }
             assert(HcurrPartEq: currentPartition s0 = currentPartition s1).
             {
               rewrite Hs1. simpl. reflexivity.
             }
             rewrite HcurrPartEq in *.
             assert(HblockInMappedBlocksEqs: getMappedBlocks pdparent s = getMappedBlocks pdparent s1).
             {
               rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent. assumption.
               unfold consistency1 in *; intuition. simpl. reflexivity.
             }
             assert(HlowerThanMaxs: blockindex newBentry < kernelStructureEntriesNb) by (apply Hidx).
             assert(HblockIsNotFrees1: ~isFreeSlot blockInParentPartitionAddr s1).
             {
               unfold isFreeSlot. rewrite HlookupBlocks1.
               assert(HwellFormeds1: wellFormedFstShadowIfBlockEntry s1)
                     by (unfold consistency1 in *; intuition).
               unfold wellFormedFstShadowIfBlockEntry in HwellFormeds1.
               assert(HblockIsBE: isBE blockInParentPartitionAddr s1).
               { unfold isBE. rewrite HlookupBlocks1. trivial. }
               specialize(HwellFormeds1 blockInParentPartitionAddr HblockIsBE).
               unfold isSHE in HwellFormeds1.
               destruct (lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr);
                     try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               assert(HwellFormedCuts1: wellFormedShadowCutIfBlockEntry s1)
                     by (unfold consistency1 in *; intuition).
               unfold wellFormedShadowCutIfBlockEntry in HwellFormedCuts1.
               specialize(HwellFormedCuts1 blockInParentPartitionAddr HblockIsBE).
               destruct HwellFormedCuts1 as [scentryaddr (HwellFormedCuts1 & HsceValue)].
               subst scentryaddr. unfold isSCE in HwellFormedCuts1.
               destruct (lookup (CPaddr (blockInParentPartitionAddr + scoffset)) (memory s1) beqAddr);
                     try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               unfold bentryPFlag in HPFlag. rewrite HlookupBlocks1 in HPFlag.
               rewrite <-HPFlag. intro Hcontra. destruct Hcontra as (_ & _ & _ & _ & hcontra & _). congruence.
             }
             assert(HgetFreeSlotsListEqs: forall pd, isPDT pd s1
                                                -> lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr
                                                  -> getFreeSlotsList pd s = getFreeSlotsList pd s1).
             {
               intros pd HisPDT HlookupPdEq. unfold isPDT in HisPDT. unfold getFreeSlotsList in *.
               rewrite HlookupPdEq in *.
               destruct (lookup pd (memory s1) beqAddr) eqn:HlookupPd; try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFreeNull.
               + (* firstfreeslot p = nullAddr *)
                 reflexivity.
               + (* firstfreeslot p <> nullAddr *)
                 assert(HbeqFirstFreeParent: firstfreeslot p <> pdparent).
                 {
                   assert(HfirstFree: FirstFreeSlotPointerIsBEAndFreeSlot s1)
                         by (unfold consistency1 in *; intuition).
                   unfold FirstFreeSlotPointerIsBEAndFreeSlot in HfirstFree.
                   rewrite <-beqAddrFalse in HbeqFirstFreeNull.
                   specialize(HfirstFree pd p HlookupPd HbeqFirstFreeNull).
                   destruct HfirstFree as [HfirstIsBE HfirstIsFree].
                   intro Hcontra. rewrite Hcontra in HfirstIsBE. unfold isBE in HfirstIsBE.
                   rewrite HlookupParent in HfirstIsBE. congruence.
                 }
                 rewrite Hs. apply getFreeSlotsListRecEqPDT; try(intuition; congruence).
                 * unfold isBE. rewrite HlookupParent. intro. trivial.
                 * unfold isPADDR. rewrite HlookupParent. intro. trivial.
             }

             assert(HnullExists: nullAddrExists s).
             { (* BEGIN nullAddrExists s *)
               assert(Hcons0: nullAddrExists s1) by (unfold consistency1 in *; intuition).
               unfold nullAddrExists in *. unfold isPADDR in *.
               rewrite Hs. simpl. rewrite HbeqParentNull.
               rewrite <-beqAddrFalse in HbeqParentNull. rewrite removeDupIdentity; intuition.
               (* END nullAddrExists *)
             }

             rewrite <-HcurrPartEq in Hs1.

             assert(HwellFormed: wellFormedFstShadowIfBlockEntry s).
             { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
               assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
                      by (unfold consistency in *; unfold consistency1 in *; intuition).
               apply wellFormedFstShadowIfBlockEntryPreservedIsBuilt with s1 s0 pdparent pdentryParent
                    blockInParentPartitionAddr bentry
                    (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
               (* END wellFormedFstShadowIfBlockEntry *)
             }

             assert(HPDTI: PDTIfPDFlag s).
             { (* BEGIN PDTIfPDFlag s *)
               assert(Hcons0: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
               apply PDTIfPDFlagPreservedIsBuilt with s1 s0 pdparent pdentryParent
                    blockInParentPartitionAddr bentry
                    (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
               (* END PDTIfPDFlag *)
             }

             assert(Haccessible: AccessibleNoPDFlag s).
             { (* BEGIN AccessibleNoPDFlag s *)
               unfold consistency in *. unfold consistency1 in *.
               apply AccessibleNoPDFlagPreservedIsBuilt with s1 s0 pdparent pdentryParent
                    blockInParentPartitionAddr bentry
                    (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
               (* END AccessibleNoPDFlag *)
             }

             assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
             { (* BEGIN multiplexerIsPDT s *)
               assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s1) by (unfold consistency1 in *; intuition).
               unfold FirstFreeSlotPointerIsBEAndFreeSlot in *.
               intros pdentryaddr pdentry HlookupPdaddr HfirstFreeNotNull.
               assert(HlookupPdaddrs1: exists pdentrys1, lookup pdentryaddr (memory s1) beqAddr
                                                          = Some (PDT pdentrys1)
                                                         /\ firstfreeslot pdentrys1 <> nullAddr
                                                         /\ firstfreeslot pdentrys1 = firstfreeslot pdentry).
               {
                 rewrite Hs in HlookupPdaddr. simpl in HlookupPdaddr.
                 destruct (beqAddr pdparent pdentryaddr) eqn:HbeqParentPdaddr.
                 - (* pdparent = pdentryaddr *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPdaddr. rewrite HbeqParentPdaddr in *.
                   rewrite HlookupParent. exists pdentryParent. split. reflexivity.
                   injection HlookupPdaddr as Hpdentry. rewrite <-Hpdentry in *.
                   simpl in HfirstFreeNotNull. split. assumption. simpl. reflexivity.
                 - (* pdparent <> pdentryaddr *)
                   rewrite <-beqAddrFalse in HbeqParentPdaddr. exists pdentry.
                   rewrite removeDupIdentity in HlookupPdaddr; intuition.
               }
               destruct HlookupPdaddrs1 as [pdentrys1 (HlookupPdaddrs1 & (HfirstFreeNotNulls1 & HfirstFreeEq))].
               specialize(Hcons0 pdentryaddr pdentrys1 HlookupPdaddrs1 HfirstFreeNotNulls1).
               rewrite HfirstFreeEq in *. destruct Hcons0 as [HfirstFreeIsBE HfirstFreeIsFree].
               unfold isBE in *. unfold isFreeSlot in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (firstfreeslot pdentry)) eqn:HbeqParentFirst.
               { (* pdparent = firstfreeslot pdentry *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFirst. rewrite HbeqParentFirst in *.
                 rewrite HlookupParent in HfirstFreeIsBE. exfalso; congruence.
               }
               (* pdparent <> firstfreeslot pdentry *)
               rewrite <-beqAddrFalse in HbeqParentFirst. rewrite removeDupIdentity; intuition.
               destruct (lookup (firstfreeslot pdentry) (memory s1) beqAddr) eqn:HlookupFirst; try(congruence).
               destruct v; try(congruence).
               destruct(beqAddr pdparent (CPaddr (firstfreeslot pdentry + sh1offset))) eqn:HbeqParentFirstSh1.
               { (* pdparent = CPaddr (firstfreeslot pdentry + sh1offset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFirstSh1. rewrite <-HbeqParentFirstSh1 in *.
                 rewrite HlookupParent in HfirstFreeIsFree. congruence.
               }
               (* pdparent <> CPaddr (firstfreeslot pdentry + sh1offset) *)
               rewrite <-beqAddrFalse in HbeqParentFirstSh1. rewrite removeDupIdentity; intuition.
               destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s1) beqAddr);
                      try(congruence).
               destruct v; try(congruence).
               destruct (beqAddr pdparent (CPaddr (firstfreeslot pdentry + scoffset))) eqn:HbeqParentFirstSce.
               { (* pdparent = CPaddr (firstfreeslot pdentry + scoffset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFirstSce. rewrite <-HbeqParentFirstSce in *.
                 rewrite HlookupParent in HfirstFreeIsFree. congruence.
               }
               (* pdparent <> CPaddr (firstfreeslot pdentry + scoffset) *)
               rewrite <-beqAddrFalse in HbeqParentFirstSce. rewrite removeDupIdentity; intuition.
               (* END multiplexerIsPDT *)
             }

             assert(multiplexerIsPDT s).
             { (* BEGIN multiplexerIsPDT s *)
               assert(Hcons0: multiplexerIsPDT s1) by (unfold consistency1 in *; intuition).
               unfold multiplexerIsPDT in *.
               unfold isPDT in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent multiplexer) eqn:HbeqParentMultip.
               - (* pdparent = multiplexer *)
                 trivial.
               - (* pdparent <> multiplexer *)
                 rewrite <-beqAddrFalse in HbeqParentMultip. rewrite removeDupIdentity; intuition.
               (* END multiplexerIsPDT *)
             }

             assert(HgetPartitionsEq: getPartitions multiplexer s = getPartitions multiplexer s1).
             {
               rewrite Hs. apply getPartitionsEqPDT with pdentryParent; try(unfold consistency1 in *; intuition).
             }

             assert(currentPartitionInPartitionsList s).
             { (* BEGIN currentPartitionInPartitionsList s *)
               assert(Hcons0: currentPartitionInPartitionsList s1) by (unfold consistency1 in *; intuition).
               unfold currentPartitionInPartitionsList in *.
               rewrite HgetPartitionsEq. rewrite Hs. simpl. assumption.
               (* END currentPartitionInPartitionsList *)
             }

             assert(wellFormedShadowCutIfBlockEntry s).
             { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
               assert(Hcons0: wellFormedShadowCutIfBlockEntry s1) by (unfold consistency1 in *; intuition).
               unfold wellFormedShadowCutIfBlockEntry in *. intros pa HpaIsBE.
               assert(HlookupPaEq: lookup pa (memory s) beqAddr = lookup pa (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. unfold isBE in HpaIsBE. rewrite Hs in HpaIsBE. simpl in HpaIsBE.
                 destruct (beqAddr pdparent pa) eqn:HbeqParentPa; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentPa. rewrite removeDupIdentity; intuition.
               }
               assert(HpaIsBEs1: isBE pa s1).
               {
                 unfold isBE in *. rewrite HlookupPaEq in HpaIsBE. assumption.
               }
               specialize(Hcons0 pa HpaIsBEs1). destruct Hcons0 as [scentryaddr (HsceIsSce & HsceVal)].
               exists scentryaddr. split. unfold isSCE in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent scentryaddr) eqn:HbeqParentSce.
               { (* pdparent = scentryaddr *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentSce. rewrite HbeqParentSce in *.
                 rewrite HlookupParent in HsceIsSce. congruence.
               }
               (* pdparent <> scentryaddr *)
               rewrite <-beqAddrFalse in HbeqParentSce. rewrite removeDupIdentity; intuition.
               assumption.
               (* END wellFormedShadowCutIfBlockEntry *)
             }

             assert(BlocksRangeFromKernelStartIsBE s).
             { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
               assert(Hcons0: BlocksRangeFromKernelStartIsBE s1) by (unfold consistency1 in *; intuition).
               unfold BlocksRangeFromKernelStartIsBE in *.
               intros kernelentryaddr blockidx HkernIsKS HidxIsValid.
               assert(HkernIsKSs1: isKS kernelentryaddr s1).
               {
                 unfold isKS in *. rewrite Hs in HkernIsKS. simpl in HkernIsKS.
                 destruct (beqAddr pdparent kernelentryaddr) eqn:HbeqParentKern; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentKern. rewrite removeDupIdentity in HkernIsKS; intuition.
               }
               specialize(Hcons0 kernelentryaddr blockidx HkernIsKSs1 HidxIsValid).
               unfold isBE in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (CPaddr (kernelentryaddr + blockidx))) eqn:HbeqParentKernIdx.
               { (* pdparent = CPaddr (kernelentryaddr + blockidx) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentKernIdx. rewrite <-HbeqParentKernIdx in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> CPaddr (kernelentryaddr + blockidx) *)
               rewrite <-beqAddrFalse in HbeqParentKernIdx. rewrite removeDupIdentity; intuition.
               (* END BlocksRangeFromKernelStartIsBE *)
             }

             assert(KernelStructureStartFromBlockEntryAddrIsKS s).
             { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
               assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s1)
                      by (unfold consistency1 in *; intuition).
               unfold KernelStructureStartFromBlockEntryAddrIsKS in *.
               intros blockentryaddr blockidx HblockIsBE HidxIsBlockIdx.
               assert(HlookupBlockEq: lookup blockentryaddr (memory s) beqAddr
                                      = lookup blockentryaddr (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. unfold isBE in HblockIsBE. rewrite Hs in HblockIsBE. simpl in HblockIsBE.
                 destruct (beqAddr pdparent blockentryaddr) eqn:HbeqParentBlock; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
               }
               assert(HblockIsBEs1: isBE blockentryaddr s1).
               {
                 unfold isBE in *. rewrite HlookupBlockEq in HblockIsBE. assumption.
               }
               assert(HidxIsBlockIdxs1: bentryBlockIndex blockentryaddr blockidx s1).
               {
                 unfold bentryBlockIndex in *. rewrite HlookupBlockEq in HidxIsBlockIdx. assumption.
               }
               specialize(Hcons0 blockentryaddr blockidx HblockIsBEs1 HidxIsBlockIdxs1).
               unfold isKS in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (CPaddr (blockentryaddr - blockidx))) eqn:HbeqParentBlockMinus.
               { (* pdparent = CPaddr (blockentryaddr - blockidx) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentBlockMinus. rewrite <-HbeqParentBlockMinus in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> CPaddr (blockentryaddr - blockidx) *)
               rewrite <-beqAddrFalse in HbeqParentBlockMinus. rewrite removeDupIdentity; intuition.
               (* END KernelStructureStartFromBlockEntryAddrIsKS *)
             }

             assert(sh1InChildLocationIsBE s).
             { (* BEGIN sh1InChildLocationIsBE s *)
               assert(Hcons0: sh1InChildLocationIsBE s1) by (unfold consistency1 in *; intuition).
               unfold sh1InChildLocationIsBE in *.
               intros sh1entryaddr sh1entry HlookupSh1 HinChild.
               assert(HlookupSh1s1: lookup sh1entryaddr (memory s1) beqAddr = Some (SHE sh1entry)).
               {
                 rewrite Hs in HlookupSh1. simpl in HlookupSh1.
                 destruct (beqAddr pdparent sh1entryaddr) eqn:HbeqParentSh1; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity in HlookupSh1; intuition.
               }
               specialize(Hcons0 sh1entryaddr sh1entry HlookupSh1s1 HinChild).
               unfold isBE in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent (inChildLocation sh1entry)) eqn:HbeqParentInChild.
               { (* pdparent = inChildLocation sh1entry *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentInChild. rewrite HbeqParentInChild in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> inChildLocation sh1entry *)
               rewrite <-beqAddrFalse in HbeqParentInChild. rewrite removeDupIdentity; intuition.
               (* END sh1InChildLocationIsBE *)
             }

             assert(StructurePointerIsKS s).
             { (* BEGIN StructurePointerIsKS s *)
                assert(Hcons0: StructurePointerIsKS s0)
                      by (unfold consistency in *; unfold consistency1 in *; intuition).
               apply StructurePointerIsKSPreservedIsBuilt with s1 s0 pdparent pdentryParent
                    blockInParentPartitionAddr bentry
                    (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
               (* END StructurePointerIsKS *)
             }

             assert(NextKSIsKS s).
             { (* BEGIN NextKSIsKS s *)
               assert(Hcons0: NextKSIsKS s1) by (unfold consistency1 in *; intuition).
               unfold NextKSIsKS in *. intros addr nextKSaddr nextKS HaddrIsKS HnextKS HnextEntry HnextKSnotNull.
               assert(HaddrIsKSs1: isKS addr s1).
               {
                 unfold isKS in *. rewrite Hs in HaddrIsKS. simpl in HaddrIsKS.
                 destruct (beqAddr pdparent addr) eqn:HbeqParentAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentAddr. rewrite removeDupIdentity in HaddrIsKS; intuition.
               }
               assert(HnextKSs1: nextKSAddr addr nextKSaddr s1).
               {
                 unfold nextKSAddr in *. rewrite Hs in HnextKS. simpl in HnextKS.
                 destruct (beqAddr pdparent addr) eqn:HbeqParentAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentAddr. rewrite removeDupIdentity in HnextKS; intuition.
               }
               assert(HnextEntrys1: nextKSentry nextKSaddr nextKS s1).
               {
                 unfold nextKSentry in *. rewrite Hs in HnextEntry. simpl in HnextEntry.
                 destruct (beqAddr pdparent nextKSaddr) eqn:HbeqParentNextAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentNextAddr.
                 rewrite removeDupIdentity in HnextEntry; intuition.
               }
               specialize(Hcons0 addr nextKSaddr nextKS HaddrIsKSs1 HnextKSs1 HnextEntrys1 HnextKSnotNull).
               unfold isKS in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent nextKS) eqn:HbeqParentNext; try(exfalso; congruence).
               { (* pdparent = nextKS *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentNext. rewrite HbeqParentNext in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> nextKS *)
               rewrite <-beqAddrFalse in HbeqParentNext. rewrite removeDupIdentity; intuition.
               (* END NextKSIsKS *)
             }

             assert(NextKSOffsetIsPADDR s).
             { (* BEGIN NextKSOffsetIsPADDR s *)
               assert(Hcons0: NextKSOffsetIsPADDR s1) by (unfold consistency1 in *; intuition).
               unfold NextKSOffsetIsPADDR in *. intros addr nextksaddr HaddrIsKS HnextKS.
               assert(HaddrIsKSs1: isKS addr s1).
               {
                 unfold isKS in *. rewrite Hs in HaddrIsKS. simpl in HaddrIsKS.
                 destruct (beqAddr pdparent addr) eqn:HbeqParentAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentAddr. rewrite removeDupIdentity in HaddrIsKS; intuition.
               }
               assert(HnextKSs1: nextKSAddr addr nextksaddr s1).
               {
                 unfold nextKSAddr in *. rewrite Hs in HnextKS. simpl in HnextKS.
                 destruct (beqAddr pdparent addr) eqn:HbeqParentAddr; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentAddr. rewrite removeDupIdentity in HnextKS; intuition.
               }
               specialize(Hcons0 addr nextksaddr HaddrIsKSs1 HnextKSs1).
               destruct Hcons0 as [HnextIsPADDR HnextNotNull]. split. unfold isPADDR in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent nextksaddr) eqn:HbeqParentNext.
               { (* pdparent = nextksaddr *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentNext. rewrite HbeqParentNext in *.
                 rewrite HlookupParent in HnextIsPADDR. congruence.
               }
               (* pdparent <> nextksaddr *)
               rewrite <-beqAddrFalse in HbeqParentNext. rewrite removeDupIdentity; intuition. assumption.
               (* END NextKSOffsetIsPADDR *)
             }

             assert(HlookupParents: lookup pdparent (memory s) beqAddr
                        = Some (PDT
                                  ({|
                                    structure := structure pdentryParent;
                                    firstfreeslot := firstfreeslot pdentryParent;
                                    nbfreeslots := nbfreeslots pdentryParent;
                                    nbprepare := nbprepare pdentryParent;
                                    parent := parent pdentryParent;
                                    MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                                    vidtAddr := vidtAddr pdentryParent
                                  |}))).
             {
               rewrite Hs. simpl. rewrite beqAddrTrue. reflexivity.
             }

             assert(HgetFreeSlotsParent: getFreeSlotsList pdparent s = getFreeSlotsList pdparent s1).
             {
               unfold getFreeSlotsList. rewrite HlookupParent. rewrite HlookupParents. simpl.
               destruct (beqAddr (firstfreeslot pdentryParent) nullAddr) eqn:HbeqFirstFreeNull; try(reflexivity).
               rewrite Hs. apply getFreeSlotsListRecEqPDT.
               + apply firstBlockPDNotEq with pdentryParent s1. assumption. unfold pdentryFirstFreeSlot.
                 rewrite HlookupParent. reflexivity. exists (firstfreeslot pdentryParent).
                 rewrite <-beqAddrFalse in HbeqFirstFreeNull. unfold pdentryFirstFreeSlot.
                 rewrite HlookupParent. split. reflexivity. assumption. assumption.
               + unfold isBE. rewrite HlookupParent. intuition.
               + unfold isPADDR. rewrite HlookupParent. intuition.
             }

             assert(NoDupInFreeSlotsList s).
             { (* BEGIN NoDupInFreeSlotsList s *)
               assert(Hcons0: NoDupInFreeSlotsList s1) by (unfold consistency1 in *; intuition).
               unfold NoDupInFreeSlotsList in *. intros pd pdentry HlookupPd.
               destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
               - (* pdparent = pd *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                 specialize(Hcons0 pd pdentryParent HlookupParent).
                 destruct Hcons0 as [optionFreeSlotsList (HgetFreeList & (HwellFormedList & HnoDupList))].
                 exists optionFreeSlotsList. split; try(split; assumption; assumption).
                 subst optionFreeSlotsList.
                 apply eq_sym. assumption.
               - (* pdparent <> pd *)
                 assert(HlookupPds1: lookup pd (memory s1) beqAddr = Some (PDT pdentry)).
                 {
                   rewrite Hs in HlookupPd. simpl in HlookupPd. rewrite HbeqParentPd in HlookupPd.
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in HlookupPd; intuition.
                 }
                 specialize(Hcons0 pd pdentry HlookupPds1).
                 destruct Hcons0 as [optionFreeSlotsList (HgetFreeList & (HwellFormedList & HnoDupList))].
                 exists optionFreeSlotsList. split; try(split; assumption; assumption).
                 subst optionFreeSlotsList.
                 assert(HlookupPdsEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
                 {
                   rewrite HlookupPds1. assumption.
                 }
                 apply eq_sym. apply HgetFreeSlotsListEqs.
                 unfold isPDT. rewrite HlookupPds1. trivial. assumption.
               (* END NoDupInFreeSlotsList *)
             }

             assert(freeSlotsListIsFreeSlot s).
             { (* BEGIN freeSlotsListIsFreeSlot s *)
               assert(Hcons0: freeSlotsListIsFreeSlot s1) by (unfold consistency1 in *; intuition).
               unfold freeSlotsListIsFreeSlot in *.
               intros pd freeslotaddr optionFreeSlotsList freeSlotsList HpdIsPDT HoptionList HfreeSlotsList
                      HfreeSlotNotNull.
               assert(HpdIsPDTs1: isPDT pd s1).
               {
                 unfold isPDT in *. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *. rewrite HlookupParent.
                   trivial.
                 - (* pdparent <> pd *)
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in HpdIsPDT; intuition.
               }
               assert(HoptionLists1: optionFreeSlotsList = getFreeSlotsList pd s1
                                     /\ wellFormedFreeSlotsList optionFreeSlotsList <> False).
               {
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite <-HgetFreeSlotsParent. assumption.
                 - (* pdparent <> pd *)
                   assert(HlookupPdEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
                   {
                     rewrite Hs. simpl. rewrite HbeqParentPd. rewrite <-beqAddrFalse in HbeqParentPd.
                     rewrite removeDupIdentity; intuition.
                   }
                   specialize(HgetFreeSlotsListEqs pd HpdIsPDTs1 HlookupPdEq).
                   rewrite <-HgetFreeSlotsListEqs. assumption.
               }
               specialize(Hcons0 pd freeslotaddr optionFreeSlotsList freeSlotsList HpdIsPDTs1 HoptionLists1
                          HfreeSlotsList HfreeSlotNotNull).
               unfold isFreeSlot in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent freeslotaddr) eqn:HbeqParentFree.
               { (* pdparent = freeslotaddr *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFree. rewrite HbeqParentFree in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> freeslotaddr *)
               rewrite <-beqAddrFalse in HbeqParentFree. rewrite removeDupIdentity; intuition.
               destruct (lookup freeslotaddr (memory s1) beqAddr); try(exfalso; congruence).
               destruct v; try(exfalso; congruence).
               destruct (beqAddr pdparent (CPaddr (freeslotaddr + sh1offset))) eqn:HbeqParentFreeSh1.
               { (* pdparent = CPaddr (freeslotaddr + sh1offset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFreeSh1. rewrite HbeqParentFreeSh1 in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> CPaddr (freeslotaddr + sh1offset) *)
               rewrite <-beqAddrFalse in HbeqParentFreeSh1. rewrite removeDupIdentity; intuition.
               destruct (lookup (CPaddr (freeslotaddr + sh1offset)) (memory s1) beqAddr); try(congruence).
               destruct v; try(congruence).
               destruct (beqAddr pdparent (CPaddr (freeslotaddr + scoffset))) eqn:HbeqParentFreeSce.
               { (* pdparent = CPaddr (freeslotaddr + scoffset) *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentFreeSce. rewrite <-HbeqParentFreeSce in *.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               (* pdparent <> CPaddr (freeslotaddr + scoffset) *)
               rewrite <-beqAddrFalse in HbeqParentFreeSce. rewrite removeDupIdentity; intuition.
               (* END freeSlotsListIsFreeSlot *)
             }

             assert(DisjointFreeSlotsLists s).
             { (* BEGIN DisjointFreeSlotsLists s *)
               assert(Hcons0: DisjointFreeSlotsLists s1) by (unfold consistency1 in *; intuition).
               unfold DisjointFreeSlotsLists in *. intros pd1 pd2 Hpd1IsPDT Hpd2IsPDT Hpd1pd2Diff.
               assert(Hpd1IsPDTs1: isPDT pd1 s1).
               {
                 unfold isPDT in *. rewrite Hs in Hpd1IsPDT. simpl in Hpd1IsPDT.
                 destruct (beqAddr pdparent pd1) eqn:HbeqParentPd1.
                 - (* pdparent = pd1 *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd1. rewrite HbeqParentPd1 in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent <> pd1 *)
                   rewrite <-beqAddrFalse in HbeqParentPd1. rewrite removeDupIdentity in Hpd1IsPDT; intuition.
               }
               assert(Hpd2IsPDTs1: isPDT pd2 s1).
               {
                 unfold isPDT in *. rewrite Hs in Hpd2IsPDT. simpl in Hpd2IsPDT.
                 destruct (beqAddr pdparent pd2) eqn:HbeqParentPd2.
                 - (* pdparent = pd2 *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd2. rewrite HbeqParentPd2 in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent <> pd2 *)
                   rewrite <-beqAddrFalse in HbeqParentPd2. rewrite removeDupIdentity in Hpd2IsPDT; intuition.
               }
               specialize(Hcons0 pd1 pd2 Hpd1IsPDTs1 Hpd2IsPDTs1 Hpd1pd2Diff).
               destruct Hcons0 as [optionFreeSlotsList1 (optionFreeSlotsList2 & (Hlist1 & (HwellFormedList1 &
                                  (Hlist2 & (HwellFormedList2 & Hdisjoint)))))].
               exists optionFreeSlotsList1. exists optionFreeSlotsList2. subst optionFreeSlotsList1.
               subst optionFreeSlotsList2. split. destruct (beqAddr pdparent pd1) eqn:HbeqParentPd1.
               { (* pdparent = pd1 *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd1. rewrite HbeqParentPd1 in *.
                 rewrite <-HgetFreeSlotsParent. reflexivity.
               }
               (* pdparent <> pd1 *)
               assert(HlookupPd1Eq: lookup pd1 (memory s) beqAddr = lookup pd1 (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. rewrite HbeqParentPd1. rewrite <-beqAddrFalse in HbeqParentPd1.
                 rewrite removeDupIdentity; intuition.
               }
               specialize(HgetFreeSlotsListEqs pd1 Hpd1IsPDTs1 HlookupPd1Eq).
               rewrite <-HgetFreeSlotsListEqs. reflexivity. split. assumption. split.
               destruct (beqAddr pdparent pd2) eqn:HbeqParentPd2.
               { (* pdparent = pd2 *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd2. rewrite HbeqParentPd2 in *.
                 rewrite <-HgetFreeSlotsParent. reflexivity.
               }
               (* pdparent <> pd2 *)
               assert(HlookupPd2Eq: lookup pd2 (memory s) beqAddr = lookup pd2 (memory s1) beqAddr).
               {
                 rewrite Hs. simpl. rewrite HbeqParentPd2. rewrite <-beqAddrFalse in HbeqParentPd2.
                 rewrite removeDupIdentity; intuition.
               }
               specialize(HgetFreeSlotsListEqs pd2 Hpd2IsPDTs1 HlookupPd2Eq).
               rewrite <-HgetFreeSlotsListEqs. reflexivity. split. assumption. assumption.
               (* END DisjointFreeSlotsLists *)
             }

             assert(HgetKSEq: forall pd, getKSEntries pd s = getKSEntries pd s1).
             {
               intro pd. assert(StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               rewrite Hs. apply getKSEntriesEqPDT with pdentryParent; try(assumption). simpl. reflexivity.
             }

             assert(inclFreeSlotsBlockEntries s).
             { (* BEGIN inclFreeSlotsBlockEntries s *)
               assert(Hcons0: inclFreeSlotsBlockEntries s1) by (unfold consistency1 in *; intuition).
               unfold inclFreeSlotsBlockEntries in *. intros pd HpdIsPDT.
               assert(HpdIsPDTs1: isPDT pd s1).
               {
                 unfold isPDT in *. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent <> pd *)
                   rewrite <-DTL.beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in HpdIsPDT; intuition.
               }
               specialize(Hcons0 pd HpdIsPDTs1).
               destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
               - (* pdparent = pd *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                 rewrite HgetFreeSlotsParent. rewrite HgetKSEq. assumption.
               - (* pdparent = pd *)
                 assert(HlookupPdEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
                 {
                   rewrite Hs. simpl. rewrite HbeqParentPd. rewrite <-beqAddrFalse in HbeqParentPd.
                   rewrite removeDupIdentity; intuition.
                 }
                 specialize(HgetFreeSlotsListEqs pd HpdIsPDTs1 HlookupPdEq).
                 rewrite HgetFreeSlotsListEqs. rewrite HgetKSEq. assumption.
               (* END inclFreeSlotsBlockEntries *)
             }

             assert(DisjointKSEntries s).
             { (* BEGIN DisjointKSEntries s *)
               assert(Hcons0: DisjointKSEntries s0)
                      by (unfold consistency in *; unfold consistency1 in *; intuition).
               assert(Hstructs0: StructurePointerIsKS s0)
                      by (unfold consistency in *; unfold consistency1 in *; intuition).
               apply DisjointKSEntriesPreservedIsBuilt with s1 s0 pdparent pdentryParent
                    blockInParentPartitionAddr bentry
                    (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
               (* END DisjointKSEntries *)
             }

             assert(noDupPartitionTree s).
             { (* BEGIN noDupPartitionTree s *)
               assert(Hcons0: noDupPartitionTree s1) by (unfold consistency1 in *; intuition).
               unfold noDupPartitionTree in *. rewrite HgetPartitionsEq. assumption.
               (* END noDupPartitionTree *)
             }

             assert(HgetChildrenEq: forall pd, getChildren pd s = getChildren pd s1).
             {
               intro pd. assert(StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               rewrite Hs. apply getChildrenEqPDT with pdentryParent; try(assumption). simpl. reflexivity.
             }

             assert(HpdentryParentEq: forall pd parent, StateLib.pdentryParent pd parent s
                                                        = StateLib.pdentryParent pd parent s1).
             {
               intros pd parent. unfold StateLib.pdentryParent. rewrite Hs. simpl.
               destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
               - (* pdparent = pd *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                 rewrite HlookupParent. simpl. reflexivity.
               - (* pdparent = pd *)
                 rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity; intuition.
             }

             assert(isParent s).
             { (* BEGIN isParent s *)
               assert(Hcons0: isParent s1) by (unfold consistency1 in *; intuition).
               unfold isParent in *. intros part parent Hparent'IsPart HpartIsChild.
               rewrite HgetPartitionsEq in Hparent'IsPart. rewrite HgetChildrenEq in HpartIsChild.
               specialize(Hcons0 part parent Hparent'IsPart HpartIsChild). rewrite HpdentryParentEq.
               assumption.
               (* END isParent *)
             }

             assert(isChild s).
             { (* BEGIN isChild s *)
               assert(Hcons0: isChild s1) by (unfold consistency1 in *; intuition).
               unfold isChild in *. intros part parent Hpart'IsPart HparentIsParent.
               rewrite HgetPartitionsEq in Hpart'IsPart. rewrite HpdentryParentEq in HparentIsParent.
               specialize(Hcons0 part parent Hpart'IsPart HparentIsParent).
               rewrite HgetChildrenEq. assumption.
               (* END isChild *)
             }

             assert(noDupKSEntriesList s).
             { (* BEGIN noDupKSEntriesList s *)
               assert(Hcons0: noDupKSEntriesList s1) by (unfold consistency1 in *; intuition).
               unfold noDupKSEntriesList in *. intros part HpartIsPDT.
               assert(HpartIsPDTs1: isPDT part s1).
               {
                 unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
                 destruct (beqAddr pdparent part) eqn:HbeqParentPart.
                 - (* pdparent = part *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent = part *)
                   rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
               }
               specialize(Hcons0 part HpartIsPDTs1). rewrite HgetKSEq. assumption.
               (* END noDupKSEntriesList *)
             }

             assert(HmappedBlocksEq: forall pd, getMappedBlocks pd s = getMappedBlocks pd s1).
             {
               intro pd. assert(StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent; try(assumption). simpl. reflexivity.
             }

             assert(noDupMappedBlocksList s).
             { (* BEGIN noDupMappedBlocksList s *)
               assert(Hcons0: noDupMappedBlocksList s1) by (unfold consistency1 in *; intuition).
               unfold noDupMappedBlocksList in *. intros part HpartIsPDT.
               assert(HpartIsPDTs1: isPDT part s1).
               {
                 unfold isPDT in *. rewrite Hs in HpartIsPDT. simpl in HpartIsPDT.
                 destruct (beqAddr pdparent part) eqn:HbeqParentPart.
                 - (* pdparent = part *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPart. rewrite HbeqParentPart in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent = part *)
                   rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HpartIsPDT; intuition.
               }
               specialize(Hcons0 part HpartIsPDTs1). rewrite HmappedBlocksEq. assumption.
               (* END noDupMappedBlocksList *)
             }

             assert(wellFormedBlock s).
             { (* BEGIN wellFormedBlock s *)
               assert(bentryPFlag blockInParentPartitionAddr true s0).
               {
                 unfold bentryPFlag in *. rewrite HlookupBlocks0. rewrite HlookupBlocks1 in HPFlag.
                 rewrite HnewBentry in HPFlag. simpl in HPFlag. assumption.
               }
               assert(Hcons0: wellFormedBlock s0)
                     by (unfold consistency in *; unfold consistency1 in *; intuition).
               apply wellFormedBlockPreservedIsBuilt with s1 s0 pdparent pdentryParent
                    blockInParentPartitionAddr bentry
                    (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
               (* END wellFormedBlock *)
             }

             assert(HaccessMappedBlocksEq: forall pd, getAccessibleMappedBlocks pd s
                                                       = getAccessibleMappedBlocks pd s1).
             {
               intro pd. assert(StructurePointerIsKS s1) by (unfold consistency1 in *; intuition).
               rewrite Hs. apply getAccessibleMappedBlocksEqPDT with pdentryParent; try(assumption). simpl.
               reflexivity.
             }

             assert(parentOfPartitionIsPartition s).
             { (* BEGIN parentOfPartitionIsPartition s *)
               unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
               apply parentOfPartitionIsPartitionPreservedIsBuilt with s1 s0 pdparent pdentryParent
                    blockInParentPartitionAddr bentry
                    (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
               (* END parentOfPartitionIsPartition *)
             }

             assert(NbFreeSlotsISNbFreeSlotsInList s).
             { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
               assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s1) by (unfold consistency1 in *; intuition).
               unfold NbFreeSlotsISNbFreeSlotsInList in *. intros pd nbfreeslots HpdIsPDT Hnbfreeslots.
               assert(HpdIsPDTs1: isPDT pd s1).
               {
                 unfold isPDT in *. rewrite Hs in HpdIsPDT. simpl in HpdIsPDT.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite HlookupParent. trivial.
                 - (* pdparent = pd *)
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in HpdIsPDT; intuition.
               }
               assert(Hnbfreeslotss1: pdentryNbFreeSlots pd nbfreeslots s1).
               {
                 unfold pdentryNbFreeSlots in *. rewrite Hs in Hnbfreeslots. simpl in Hnbfreeslots.
                 destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
                 - (* pdparent = pd *)
                   rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                   rewrite HlookupParent. rewrite Hnbfreeslots. simpl. reflexivity.
                 - (* pdparent = pd *)
                   rewrite <-beqAddrFalse in HbeqParentPd. rewrite removeDupIdentity in Hnbfreeslots; intuition.
               }
               specialize(Hcons0 pd nbfreeslots HpdIsPDTs1 Hnbfreeslotss1).
               destruct Hcons0 as [optionFreeSlotsList (Hlist & (HwellFormedList & HnbfreeslotsList))].
               exists optionFreeSlotsList. destruct (beqAddr pdparent pd) eqn:HbeqParentPd.
               - (* pdparent = pd *)
                 rewrite <-DTL.beqAddrTrue in HbeqParentPd. rewrite HbeqParentPd in *.
                 rewrite HgetFreeSlotsParent. intuition.
               - (* pdparent = pd *)
                 assert(HlookupEq: lookup pd (memory s) beqAddr = lookup pd (memory s1) beqAddr).
                 {
                   rewrite Hs. simpl. rewrite HbeqParentPd. rewrite <-beqAddrFalse in HbeqParentPd.
                   rewrite removeDupIdentity; intuition.
                 }
                 specialize(HgetFreeSlotsListEqs pd HpdIsPDTs1 HlookupEq). rewrite HgetFreeSlotsListEqs.
                 intuition.
               (* END NbFreeSlotsISNbFreeSlotsInList *)
             }

             assert(maxNbPrepareIsMaxNbKernels s).
             { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
               assert(Hcons0: maxNbPrepareIsMaxNbKernels s1) by (unfold consistency1 in Hconss1; intuition).
               unfold maxNbPrepareIsMaxNbKernels in *.
               intros part kernList HisLisOfKern.
               assert(HisLisOfKerns1: isListOfKernels kernList part s1).
               {
                 apply isListOfKernelsEqPDT with pdparent
                                                 {|
                                                   structure := structure pdentryParent;
                                                   firstfreeslot := firstfreeslot pdentryParent;
                                                   nbfreeslots := nbfreeslots pdentryParent;
                                                   nbprepare := nbprepare pdentryParent;
                                                   parent := parent pdentryParent;
                                                   MPU := MAL.removeBlockFromPhysicalMPUAux
                                                               blockInParentPartitionAddr realMPU;
                                                   vidtAddr := vidtAddr pdentryParent
                                                 |} pdentryParent; simpl; intuition; congruence.
               }
               specialize(Hcons0 part kernList HisLisOfKerns1). assumption.
               (* END maxNbPrepareIsMaxNbKernels *)
             }

             assert(blockInChildHasAtLeastEquivalentBlockInParent s).
             { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
               assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s1)
                   by (unfold consistency1 in Hconss1; intuition).
               unfold blockInChildHasAtLeastEquivalentBlockInParent in *.
               intros parentPart child block startChild endChild Hparent'IsPart HchildIsChild HblockMapped
                    HstartChild HendChild HPFlagChild. rewrite HgetPartitionsEq in Hparent'IsPart.
               assert(HparentIsPDT: isPDT parentPart s1).
               {
                 unfold consistency1 in Hconss1. apply partitionsArePDT; intuition.
               }
               assert(HgetChildrenParentEq: getChildren parentPart s = getChildren parentPart s1)
                   by (apply HgetChildrenEq).
               rewrite HgetChildrenEq in HchildIsChild.
               assert(HgetMappedEq: getMappedBlocks child s = getMappedBlocks child s1).
               {
                 rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent. assumption.
                 unfold consistency1 in Hconss1; intuition.
                 simpl; reflexivity.
               }
               rewrite HgetMappedEq in HblockMapped.
               assert(Hprops: bentryStartAddr block startChild s1 /\ bentryEndAddr block endChild s1
                              /\ bentryPFlag block true s1).
               {
                 unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
                 rewrite Hs in HstartChild. rewrite Hs in HendChild. rewrite Hs in HPFlagChild. simpl in *.
                 rewrite <-HnewB in *. rewrite HnewBentry in *.
                 destruct (beqAddr pdparent block) eqn:HbeqParentBlock; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in *; intuition.
               }
               destruct Hprops as (HstartChilds1 & HendChilds1 & HPFlagChilds1).
               specialize(Hcons0 parentPart child block startChild endChild Hparent'IsPart HchildIsChild
                    HblockMapped HstartChilds1 HendChilds1 HPFlagChilds1).
               assert(HgetMappedParentEq: getMappedBlocks parentPart s = getMappedBlocks parentPart s1).
               {
                 rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent. assumption.
                 unfold consistency1 in Hconss1; intuition. simpl; reflexivity.
               }
               rewrite HgetMappedParentEq. destruct Hcons0 as [blockParent [startParent [endParent
                    (HblockParentMapped & HstartParent & HendParent & HstartProp & HendProp)]]].
               exists blockParent. exists startParent. exists endParent. split. assumption.
               unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs. simpl.
               destruct (beqAddr pdparent blockParent) eqn:HbeqParentBlock.
               {
                 rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockParent. rewrite HlookupParent in *.
                 exfalso; congruence.
               }
               rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in *; intuition.
               (* END blockInChildHasAtLeastEquivalentBlockInParent *)
             }

             assert(partitionTreeIsTree s).
             { (* BEGIN partitionTreeIsTree s *)
               unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
               apply partitionTreeIsTreePreservedIsBuilt with s1 s0 pdparent pdentryParent
                    blockInParentPartitionAddr bentry
                    (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
                 try(intuition; congruence).
               (* END partitionTreeIsTree *)
             }

             assert(kernelEntriesAreValid s).
             { (* BEGIN kernelEntriesAreValid s *)
               assert(Hcons0: kernelEntriesAreValid s1) by (unfold consistency1 in *; intuition).
               intros kernel index HKS HidxBounded.
               assert(HKSs0: isKS kernel s1).
               {
                 unfold isKS in *. rewrite Hs in HKS. simpl in HKS.
                 destruct (beqAddr pdparent kernel) eqn:HbeqParentKern; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentKern. rewrite removeDupIdentity in HKS; intuition.
               }
               specialize(Hcons0 kernel index HKSs0 HidxBounded). unfold isBE. unfold isBE in Hcons0.
               rewrite Hs. simpl.
               destruct (beqAddr pdparent (CPaddr (kernel + index))) eqn:HbeqParentKernIdx.
               {
                 rewrite <-DTL.beqAddrTrue in HbeqParentKernIdx. rewrite <-HbeqParentKernIdx in Hcons0.
                 rewrite HlookupParent in Hcons0. congruence.
               }
               rewrite <-beqAddrFalse in HbeqParentKernIdx. rewrite removeDupIdentity; intuition.
               (* END kernelEntriesAreValid *)
             }

             assert(nextKernelIsValid s).
             { (* BEGIN nextKernelIsValid s *)
               assert(Hcons0: nextKernelIsValid s1) by (unfold consistency1 in *; intuition).
               intros kernel HKS.
               assert(HKSs1: isKS kernel s1).
               {
                 unfold isKS in *. rewrite Hs in HKS. simpl in HKS.
                 destruct (beqAddr pdparent kernel) eqn:HbeqBlockKern; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqBlockKern. rewrite removeDupIdentity in HKS; intuition.
               }
               specialize(Hcons0 kernel HKSs1).
               destruct Hcons0 as (HnextOffValid & [nextAddr (HlookupNext & HnextType)]). split. assumption.
               exists nextAddr. split.
               intro Hp. specialize(HlookupNext Hp). rewrite Hs. simpl.
               destruct (beqAddr pdparent {| p:= kernel+nextoffset; Hp:= Hp |}) eqn:HbeqParentNext.
               {
                 rewrite <-DTL.beqAddrTrue in HbeqParentNext. rewrite <-HbeqParentNext in HlookupNext.
                 exfalso; congruence.
               }
               rewrite <-beqAddrFalse in HbeqParentNext. rewrite removeDupIdentity; intuition.
               destruct HnextType as [HnextIsKS | Hnull]; try(right; assumption). left. unfold isKS.
               unfold isKS in HnextIsKS. rewrite Hs. simpl.
               destruct (beqAddr pdparent nextAddr) eqn:HbeqParentNextKern.
               {
                 rewrite <-DTL.beqAddrTrue in HbeqParentNextKern. subst nextAddr.
                 rewrite HlookupParent in HnextIsKS. congruence.
               }
               rewrite <-beqAddrFalse in HbeqParentNextKern. rewrite removeDupIdentity; intuition.
               (* END nextKernelIsValid *)
             }

             assert(noDupListOfKerns s).
             { (* BEGIN noDupListOfKerns s *)
               assert(Hcons0: noDupListOfKerns s1) by (unfold consistency1 in *; intuition).
               intros part kernList HkernList.
               assert(HkernLists1: isListOfKernels kernList part s1).
               {
                 apply isListOfKernelsEqPDT with pdparent
                         {|
                           structure := structure pdentryParent;
                           firstfreeslot := firstfreeslot pdentryParent;
                           nbfreeslots := nbfreeslots pdentryParent;
                           nbprepare := nbprepare pdentryParent;
                           parent := parent pdentryParent;
                           MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                           vidtAddr := vidtAddr pdentryParent
                         |} pdentryParent; simpl; try(assumption). reflexivity. rewrite Hs in HkernList.
                 assumption.
               }
               specialize(Hcons0 part kernList HkernLists1). assumption.
               (* END noDupListOfKerns *)
             }

             assert(MPUsizeIsBelowMax s).
             { (* BEGIN MPUsizeIsBelowMax s *)
               assert(Hcons0: MPUsizeIsBelowMax s1) by (unfold consistency1 in *; intuition).
               intros part MPUlist HMPUpart.
               destruct (beqAddr pdparent part) eqn:HbeqParentPart.
               - rewrite <-DTL.beqAddrTrue in HbeqParentPart. subst part.
                 specialize(Hcons0 pdparent realMPU HMPU). unfold pdentryMPU in HMPUpart.
                 rewrite Hs in HMPUpart. simpl in HMPUpart. rewrite beqAddrTrue in HMPUpart. simpl in HMPUpart.
                 pose proof (removeBlockFromPhysicalMPUAuxLenEq blockInParentPartitionAddr realMPU) as Hlen.
                 rewrite <-HMPUpart in Hlen. lia.
               - assert(HMPUs0: pdentryMPU part MPUlist s1).
                 {
                   unfold pdentryMPU in *. rewrite Hs in HMPUpart. simpl in HMPUpart.
                   rewrite HbeqParentPart in HMPUpart. rewrite <-beqAddrFalse in HbeqParentPart.
                   rewrite removeDupIdentity in HMPUpart; intuition.
                 }
                 specialize(Hcons0 part MPUlist HMPUs0). assumption.
               (* END MPUsizeIsBelowMax *)
             }

             assert(originIsParentBlocksStart s).
             { (* BEGIN originIsParentBlocksStart s *)
               assert(Hcons0: originIsParentBlocksStart s1) by (unfold consistency1 in *; intuition).
               intros part pdentry block scentryaddr scorigin HpartBisIsPart HlookupPartBis HblockMapped Hsce
                  Horigin. rewrite HgetPartitionsEq in HpartBisIsPart.
               assert(HgetBlocksEq: getMappedBlocks part s = getMappedBlocks part s1).
               {
                 rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent; try(assumption).
                 unfold consistency1 in *; intuition.
                 simpl. reflexivity.
               }
               rewrite HgetBlocksEq in HblockMapped.
               assert(Horigins1: scentryOrigin scentryaddr scorigin s1).
               {
                 unfold scentryOrigin in *. rewrite Hs in Horigin. simpl in Horigin.
                 destruct (beqAddr pdparent scentryaddr) eqn:HbeqParentSce; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentSce. rewrite removeDupIdentity in Horigin; intuition.
               }
               assert(HgetBlocksParentEq: getMappedBlocks (parent pdentry) s
                                          = getMappedBlocks (parent pdentry) s1).
               {
                 rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent; try(assumption).
                 unfold consistency1 in *; intuition.
                 simpl. reflexivity.
               }
               rewrite HgetBlocksParentEq.
               assert(HlookupBlocksEq: forall blockBis, isBE blockBis s1
                        -> lookup blockBis (memory s) beqAddr = lookup blockBis (memory s1) beqAddr).
               {
                 intros blockBis HblockBisIsBE. unfold isBE in HblockBisIsBE. rewrite Hs. simpl.
                 destruct (beqAddr pdparent blockBis) eqn:HbeqParentBlock.
                 {
                   rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockBis.
                   rewrite HlookupParent in HblockBisIsBE. exfalso; congruence.
                 }
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
               }
               assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
               {
                 apply HlookupBlocksEq. pose proof (mappedBlockIsBE block part s1 HblockMapped) as Hres.
                 destruct Hres as [bentryBlock (Hlookup & _)]. unfold isBE. rewrite Hlookup. trivial.
               }
               destruct (beqAddr pdparent part) eqn:HbeqParentPart.
               - rewrite <-DTL.beqAddrTrue in HbeqParentPart. subst part.
                 specialize(Hcons0 pdparent pdentryParent block scentryaddr scorigin HpartBisIsPart HlookupParent
                    HblockMapped Hsce Horigins1). destruct Hcons0 as (Hcons0 & HstartAbove). split.
                 + intro HbeqPartRoot. specialize(Hcons0 HbeqPartRoot).
                   destruct Hcons0 as [blockParent (HblockParentMapped & HstartParent & Hincl)].
                   rewrite Hs in HlookupPartBis. simpl in HlookupPartBis. rewrite beqAddrTrue in HlookupPartBis.
                   injection HlookupPartBis as Hpdentries. subst pdentry. simpl. exists blockParent. split.
                   assumption.
                   assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                                = lookup blockParent (memory s1) beqAddr).
                   {
                     apply HlookupBlocksEq.
                     pose proof (mappedBlockIsBE blockParent (parent pdentryParent) s1 HblockParentMapped) as Hres.
                     destruct Hres as [bentryBlock (Hlookup & _)]. unfold isBE. rewrite Hlookup. trivial.
                   }
                   split. unfold bentryStartAddr. rewrite HlookupBlockParentEq. assumption.
                   rewrite HlookupBlockEq. rewrite HlookupBlockParentEq. simpl in Hincl. assumption.
                 + intros startBlock HstartBlock. apply HstartAbove. unfold bentryStartAddr in HstartBlock.
                   rewrite Hs in HstartBlock. simpl in HstartBlock.
                   destruct (beqAddr pdparent block) eqn:HbeqParentBlock; try(exfalso; congruence).
                   rewrite <-beqAddrFalse in HbeqParentBlock.
                   rewrite removeDupIdentity in HstartBlock; try(apply not_eq_sym); assumption.
               - assert(HlookupPartBiss1: lookup part (memory s1) beqAddr = Some (PDT pdentry)).
                 {
                   rewrite Hs in HlookupPartBis. simpl in HlookupPartBis.
                   rewrite HbeqParentPart in HlookupPartBis. rewrite <-beqAddrFalse in HbeqParentPart.
                   rewrite removeDupIdentity in HlookupPartBis; intuition.
                 }
                 specialize(Hcons0 part pdentry block scentryaddr scorigin HpartBisIsPart HlookupPartBiss1
                    HblockMapped Hsce Horigins1). destruct Hcons0 as (Hcons0 & HstartAbove). split.
                 + intro HbeqPartRoot. specialize(Hcons0 HbeqPartRoot).
                   destruct Hcons0 as [blockParent (HblockParentMapped & HstartParent & Hincl)].
                   assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                                = lookup blockParent (memory s1) beqAddr).
                   {
                     apply HlookupBlocksEq.
                     pose proof (mappedBlockIsBE blockParent (parent pdentry) s1 HblockParentMapped) as Hres.
                     destruct Hres as [bentryBlock (Hlookup & _)]. unfold isBE. rewrite Hlookup. trivial.
                   }
                   exists blockParent. split. assumption. split. unfold bentryStartAddr.
                   rewrite HlookupBlockParentEq. assumption. simpl. simpl in Hincl. rewrite HlookupBlockEq.
                   rewrite HlookupBlockParentEq. assumption.
                 + intros startBlock HstartBlock. apply HstartAbove. unfold bentryStartAddr in HstartBlock.
                   rewrite Hs in HstartBlock. simpl in HstartBlock.
                   destruct (beqAddr pdparent block) eqn:HbeqParentBlock; try(exfalso; congruence).
                   rewrite <-beqAddrFalse in HbeqParentBlock.
                   rewrite removeDupIdentity in HstartBlock; try(apply not_eq_sym); assumption.
               (* END originIsParentBlocksStart *)
             }

             assert(nextImpliesBlockWasCut s).
             { (* BEGIN nextImpliesBlockWasCut s *)
               assert(Hcons0: nextImpliesBlockWasCut s1) by (unfold consistency1 in *; intuition).
               intros part pdentry block scentryaddr scnext endBlock HpartBisIsPart HlookupPart HblockMapped
                  HblockEnd Hsce HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartitionsEq in HpartBisIsPart.
               assert(HgetBlocksEq: getMappedBlocks part s = getMappedBlocks part s1).
               {
                 rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent; try(assumption).
                 unfold consistency1 in *; intuition.
                 simpl. reflexivity.
               }
               rewrite HgetBlocksEq in HblockMapped.
               assert(HgetBlocksParentEq: getMappedBlocks (parent pdentry) s
                                          = getMappedBlocks (parent pdentry) s1).
               {
                 rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent; try(assumption).
                 unfold consistency1 in *; intuition.
                 simpl. reflexivity.
               }
               rewrite HgetBlocksParentEq.
               assert(HlookupBlocksEq: forall blockBis, isBE blockBis s1
                        -> lookup blockBis (memory s) beqAddr = lookup blockBis (memory s1) beqAddr).
               {
                 intros blockBis HblockBisIsBE. unfold isBE in HblockBisIsBE. rewrite Hs. simpl.
                 destruct (beqAddr pdparent blockBis) eqn:HbeqParentBlock.
                 {
                   rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockBis.
                   rewrite HlookupParent in HblockBisIsBE. exfalso; congruence.
                 }
                 rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
               }
               assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
               {
                 apply HlookupBlocksEq. pose proof (mappedBlockIsBE block part s1 HblockMapped) as Hres.
                 destruct Hres as [bentryBlock (Hlookup & _)]. unfold isBE. rewrite Hlookup. trivial.
               }
               unfold bentryEndAddr in HblockEnd. rewrite HlookupBlockEq in HblockEnd.
               assert(Hnexts1: scentryNext scentryaddr scnext s1).
               {
                 unfold scentryNext in *. rewrite Hs in Hnext. simpl in Hnext.
                 destruct (beqAddr pdparent scentryaddr) eqn:HbeqParentSce; try(exfalso; congruence).
                 rewrite <-beqAddrFalse in HbeqParentSce. rewrite removeDupIdentity in Hnext; intuition.
               }
               assert(HlookupPartBiss1: exists pdentry1, lookup part (memory s1) beqAddr = Some (PDT pdentry1)
                                        /\ parent pdentry1 = parent pdentry).
               {
                 rewrite Hs in HlookupPart. simpl in HlookupPart.
                 destruct (beqAddr pdparent part) eqn:HbeqParentPart.
                 - rewrite <-DTL.beqAddrTrue in HbeqParentPart. subst part. injection HlookupPart as Hpdentries.
                   subst pdentry. simpl. exists pdentryParent. split. assumption. reflexivity.
                 - rewrite <-beqAddrFalse in HbeqParentPart. exists pdentry.
                   rewrite removeDupIdentity in HlookupPart; intuition.
               }
               destruct HlookupPartBiss1 as [pdentry1 (HlookupPartBiss1 & HparentsEq)].
               specialize(Hcons0 part pdentry1 block scentryaddr scnext endBlock HpartBisIsPart
                  HlookupPartBiss1 HblockMapped HblockEnd Hsce HbeqNextNull Hnexts1 HbeqPartRoot).
               destruct Hcons0 as [blockParent [endParent (HblockParentMapped & HendParent & Hends & Hincl)]].
               rewrite HparentsEq in *.
               assert(HlookupBlockParentEq: lookup blockParent (memory s) beqAddr
                                            = lookup blockParent (memory s1) beqAddr).
               {
                 apply HlookupBlocksEq.
                 pose proof (mappedBlockIsBE blockParent (parent pdentry) s1 HblockParentMapped) as Hres.
                 destruct Hres as [bentryBlock (Hlookup & _)]. unfold isBE. rewrite Hlookup. trivial.
               }
               exists blockParent. exists endParent. split. assumption. split. unfold bentryEndAddr.
               rewrite HlookupBlockParentEq. assumption. split. assumption. simpl. simpl in Hincl.
               rewrite HlookupBlockEq. rewrite HlookupBlockParentEq. assumption.
               (* END nextImpliesBlockWasCut *)
             }

             unfold consistency1. intuition.
       ++ split.
          { (* noDupUsedPaddrList s *)
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
            apply noDupUsedPaddrListPreservedIsBuilt with s1 s0 pdparent pdentryParent
                 blockInParentPartitionAddr bentry
                 (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag; intuition.
          }
          split.
          { (* sharedBlockPointsToChild s *)
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            unfold sharedBlockPointsToChild in *.
            intros parent child addr parentblock sh1entryaddr Hparent'IsPart HchildIsChild HaddrUsedChild
                  HaddrInParentBlock HparentBlockMappedParent Hsh1.
            assert(HgetPartEqs: getPartitions multiplexer s = getPartitions multiplexer s1).
            {
              rewrite Hs.
              unfold consistency1 in Hconss1; apply getPartitionsEqPDT with pdentryParent; simpl; intuition.
            }
            assert(HgetChildrenEq: getChildren parent s = getChildren parent s1).
            {
              rewrite Hs.
              unfold consistency1 in Hconss1; apply getChildrenEqPDT with pdentryParent; simpl; intuition.
            }
            rewrite HgetPartEqs in Hparent'IsPart. rewrite HgetChildrenEq in HchildIsChild.
            assert(HgetUsedEq: getUsedPaddr child s = getUsedPaddr child s1).
            {
              assert(HgetMappedEq: getMappedPaddr child s = getMappedPaddr child s1).
              {
                rewrite Hs. apply getMappedPaddrEqPDT with pdentryParent; simpl; intuition.
                unfold consistency1 in Hconss1; intuition.
              }
              assert(HgetConfigEq: getConfigPaddr child s = getConfigPaddr child s1).
              {
                rewrite Hs. apply getConfigPaddrEqPDT with pdentryParent; simpl; intuition.
                unfold consistency1 in Hconss1; apply childrenArePDT with parent; intuition.
              }
              unfold getUsedPaddr. rewrite HgetConfigEq. rewrite HgetMappedEq. reflexivity.
            }
            assert(HgetAllPaddrEq: getAllPaddrAux [parentblock] s = getAllPaddrAux [parentblock] s1).
            {
              rewrite Hs. apply getAllPaddrAuxEqPDT.
              unfold consistency1 in Hconss1; apply partitionsArePDT ; intuition.
              rewrite HgetPartEq. assumption.
            }
            rewrite HgetUsedEq in HaddrUsedChild. rewrite HgetAllPaddrEq in HaddrInParentBlock.
            assert(HgetMappedEq: getMappedBlocks parent s = getMappedBlocks parent s1).
            {
              rewrite Hs.
              unfold consistency1 in Hconss1; apply getMappedBlocksEqPDT with pdentryParent; intuition.
            }
            assert(Hsh1s1: sh1entryAddr parentblock sh1entryaddr s1).
            {
              rewrite Hs in Hsh1. unfold sh1entryAddr in *. simpl in Hsh1.
              destruct (beqAddr pdparent parentblock) eqn:HbeqParentParentBlock; try(exfalso; congruence).
              rewrite <-beqAddrFalse in HbeqParentParentBlock. rewrite removeDupIdentity in Hsh1; intuition.
            }
            rewrite HgetMappedEq in HparentBlockMappedParent.
            specialize(Hshareds1 parent child addr parentblock sh1entryaddr Hparent'IsPart HchildIsChild
                  HaddrUsedChild HaddrInParentBlock HparentBlockMappedParent Hsh1s1).
            destruct Hshareds1 as [HPDchild | HPDflag].
            - left. unfold sh1entryPDchild in *. rewrite Hs. simpl.
              destruct (beqAddr pdparent (CPaddr (parentblock + sh1offset))) eqn:HbeqParentSh1.
              {
                rewrite <-DTL.beqAddrTrue in HbeqParentSh1. rewrite HbeqParentSh1 in *.
                rewrite HlookupParent in HPDchild; congruence.
              }
              rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity; intuition.
            - right. unfold sh1entryPDflag in *. rewrite Hs. simpl.
              destruct (beqAddr pdparent (CPaddr (parentblock + sh1offset))) eqn:HbeqParentSh1.
              {
                rewrite <-DTL.beqAddrTrue in HbeqParentSh1. rewrite HbeqParentSh1 in *.
                rewrite HlookupParent in HPDflag; congruence.
              }
              rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity; intuition.
          }
          split.
          { (* adressesRangePreservedIfOriginAndNextOk s *)
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            unfold adressesRangePreservedIfOriginAndNextOk in *.
            intros part pdentry block scentryaddr startBlock endBlock HpartBisIsPart HblockMapped HblockIsBE
                  HblockStart HblockEnd HPFlagBlock Hscentryaddr Horigin Hnext HlookupPart HpartNotEqRoot.
            assert(HgetPartEqs: getPartitions multiplexer s = getPartitions multiplexer s1).
            {
              rewrite Hs. apply getPartitionsEqPDT with pdentryParent; try(assumption).
              simpl. reflexivity.
              unfold consistency1 in *; intuition.
              unfold consistency1 in *; intuition.
            }
            rewrite HgetPartEqs in HpartBisIsPart.
            assert(HgetMappedPartEq: getMappedBlocks part s = getMappedBlocks part s1).
            {
              rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent. assumption.
              unfold consistency1 in Hconss1; intuition. simpl; reflexivity.
            }
            rewrite HgetMappedPartEq in HblockMapped.
            assert(HblockIsBEs0: isBE block s1).
            {
              unfold isBE in *. rewrite Hs in HblockIsBE. simpl in HblockIsBE.
              destruct (beqAddr pdparent block) eqn:HbeqParentBlock; try(exfalso; congruence).
              rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in HblockIsBE; intuition.
            }
            assert(Hblocks1: bentryStartAddr block startBlock s1 /\ bentryEndAddr block endBlock s1
                             /\ bentryPFlag block true s1).
            {
              unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
              rewrite Hs in HblockStart. rewrite Hs in HblockEnd. rewrite Hs in HPFlagBlock. simpl in *.
              destruct (beqAddr pdparent block) eqn:HbeqParentBlock; try(exfalso; congruence).
              rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in *; intuition.
            }
            destruct Hblocks1 as (HstartBlocks1 & HendBlocks1 & HPFlagBlocks1).
            assert(HlookupSCEEq: lookup scentryaddr (memory s) beqAddr = lookup scentryaddr (memory s1) beqAddr).
            {
              unfold scentryOrigin in Horigin. rewrite Hs. rewrite Hs in Horigin. simpl in *.
              destruct (beqAddr pdparent scentryaddr) eqn:HbeqParentSCE; try(exfalso; congruence).
              rewrite <-beqAddrFalse in HbeqParentSCE. rewrite removeDupIdentity; intuition.
            }
            unfold scentryOrigin in *. unfold scentryNext in *. rewrite HlookupSCEEq in *.
            assert(HgetMappedEq: getMappedBlocks (parent pdentry) s = getMappedBlocks (parent pdentry) s1).
            {
              rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent. assumption.
              unfold consistency1 in Hconss1; intuition. simpl; reflexivity.
            }
            rewrite Hs in HlookupPart. simpl in HlookupPart.
            destruct (beqAddr pdparent part) eqn:HbeqParentPart.
            - rewrite <-DTL.beqAddrTrue in HbeqParentPart. subst part. injection HlookupPart as HentriesEq.
              specialize(Hranges1 pdparent pdentryParent block scentryaddr startBlock endBlock HpartBisIsPart
                         HblockMapped HblockIsBEs0 HstartBlocks1 HendBlocks1 HPFlagBlocks1 Hscentryaddr Horigin
                         Hnext HlookupParent HpartNotEqRoot).
              destruct Hranges1 as [blockParent (HblockParentMapped & HblockParentIsBE & HstartParent &
                      HendParent)].
              exists blockParent.
              rewrite HgetMappedEq. split. rewrite <-HentriesEq. simpl. assumption. unfold isBE in *.
              unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs. simpl.
              destruct (beqAddr pdparent blockParent) eqn:HbeqParentBlock.
              {
                rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockParent.
                rewrite HlookupParent in HblockParentIsBE. exfalso; congruence.
              }
              rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
            - rewrite <-beqAddrFalse in HbeqParentPart. rewrite removeDupIdentity in HlookupPart;
                  try(apply not_eq_sym; assumption).
              specialize(Hranges1 part pdentry block scentryaddr startBlock endBlock HpartBisIsPart HblockMapped
                         HblockIsBEs0 HstartBlocks1 HendBlocks1 HPFlagBlocks1 Hscentryaddr Horigin Hnext
                         HlookupPart HpartNotEqRoot).
              destruct Hranges1 as [blockParent (HblockParentMapped & HblockParentIsBE & HstartParent &
                      HendParent)].
              exists blockParent.
              rewrite HgetMappedEq. split. assumption. unfold isBE in *. unfold bentryStartAddr in *.
              unfold bentryEndAddr in *. rewrite Hs. simpl.
              destruct (beqAddr pdparent blockParent) eqn:HbeqParentBlock.
              {
                rewrite <-DTL.beqAddrTrue in HbeqParentBlock. subst blockParent.
                rewrite HlookupParent in HblockParentIsBE. exfalso; congruence.
              }
              rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in *; intuition.
          }
          split.
          { (* childsBlocksPropsInParent s *)
            unfold consistency in Hconsists0. unfold consistency1 in Hconsists0.
            apply childsBlocksPropsInParentPreservedIsBuilt with s1 s0 pdparent pdentryParent
                   blockInParentPartitionAddr bentry
                   (MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU) flag startaddr endaddr;
              try(intuition; congruence).
            intros child blockChild startChild endChild HchildIsChild HblockChildMapped HstartChild HendChild
                  HPFlagChild HstartProp HendProp.
            assert(HwellFormedBlock: wellFormedBlock s1) by (unfold consistency1 in Hconss1; intuition).
            assert(startaddr < endaddr).
            {
              specialize(HwellFormedBlock blockInParentPartitionAddr startaddr endaddr HPFlag HstartAddr
                          HendAddr).
              destruct HwellFormedBlock. assumption.
            }
            assert(HwellFormedBlocks0: wellFormedBlock s0)
                  by (unfold consistency in Hconsists0; unfold consistency1 in Hconsists0; intuition).
            assert(startChild < endChild).
            {
              specialize(HwellFormedBlocks0 blockChild startChild endChild HPFlagChild HstartChild HendChild).
              destruct HwellFormedBlocks0. assumption.
            }
            destruct HblockPart as [blockPart [bentryPart (HlookupBlockPart & HPFlagPart & HblockPartMapped
                       & HstartPart & HendPart & HcheckPart)]].
            assert(HstartChildInBlockBase: In startChild (getAllPaddrBlock (startAddr (blockrange bentryPart))
                                                                           (endAddr (blockrange bentryPart)))).
            {
              unfold bentryStartAddr in HstartPart. unfold bentryEndAddr in HendPart.
              rewrite HlookupBlockPart in *. rewrite <-HstartPart. rewrite <-HendPart.
              apply getAllPaddrBlockIncl; lia.
            }
            assert(HlookupBlockChild: exists bentryChild, lookup blockChild (memory s0) beqAddr
                                                          = Some (BE bentryChild)
                                                          /\ startChild = startAddr (blockrange bentryChild)
                                                          /\ endChild = endAddr (blockrange bentryChild)).
            {
              unfold bentryPFlag in HPFlagChild. unfold bentryStartAddr in HstartChild.
              unfold bentryEndAddr in HendChild.
              destruct (lookup blockChild (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
              destruct v; try(exfalso; congruence). exists b. intuition.
            }
            destruct HlookupBlockChild as [bentryChild (HlookupBlockChild & HstartChildVal & HendChildVal)].
            assert(HstartChildInBlockChild: In startChild (getAllPaddrBlock (startAddr (blockrange bentryChild))
                                                                            (endAddr (blockrange bentryChild)))).
            {
              subst startChild. subst endChild. apply getAllPaddrBlockIncl; lia.
            }
            assert(HgetMappedEq: getMappedBlocks partition s1 = getMappedBlocks partition s0).
            {
              rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption.
              rewrite <-HnewB. rewrite HnewBentry. simpl. reflexivity.
            }
            rewrite HgetMappedEq in HblockPartMapped. clear HgetMappedEq.
            destruct (beqAddr child partition) eqn:HbeqChildPart.
            + rewrite <-DTL.beqAddrTrue in HbeqChildPart. subst child.
              destruct (beqAddr blockChild blockPart) eqn:HbeqBlockChildBlockPart.
              * rewrite <-DTL.beqAddrTrue in HbeqBlockChildBlockPart. subst blockChild.
                unfold bentryStartAddr in *.
                unfold bentryEndAddr in *. rewrite Hs1 in HstartPart. rewrite Hs1 in HendPart. simpl in *.
                destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
                -- rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockPart. rewrite HlookupBlocks0 in *.
                   rewrite <-HnewB in *. rewrite HnewBentry in *. simpl in *.
                   rewrite <-HstartChild in HstartPart. rewrite <-HendChild in HendPart. split. assumption.
                   assumption.
                -- rewrite <-beqAddrFalse in HbeqBlockBlock.
                   rewrite removeDupIdentity in *; try(apply not_eq_sym; assumption).
                   rewrite HlookupBlockChild in *. rewrite <-HstartChild in HstartPart.
                   rewrite <-HendChild in HendPart. split. assumption. assumption.
              * exfalso. rewrite <-beqAddrFalse in HbeqBlockChildBlockPart.
                assert(HpartIsPDT: isPDT partition s0) by (unfold isPDT; rewrite HlookupParts0; trivial).
                specialize(HnoDup partition HpartIsPDT). unfold getUsedPaddr in HnoDup.
                apply Lib.NoDupSplit in HnoDup. destruct HnoDup as [_ HnoDup]. unfold getMappedPaddr in HnoDup.
                induction (getMappedBlocks partition s0).
                { intuition. }
                simpl in *. destruct HblockPartMapped as [Ha1IsPart | HblockPartMappedRec].
                -- subst a1. destruct HblockChildMapped as [Hcontra | HblockChildIsMappedRec]; try(congruence).
                   rewrite Hs1 in HlookupBlockPart. simpl in HlookupBlockPart.
                   destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
                   ++ rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockPart.
                      rewrite HlookupBlocks0 in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                      rewrite <-HnewB in HlookupBlockPart. rewrite HnewBentry in HlookupBlockPart.
                      simpl in HlookupBlockPart. injection HlookupBlockPart as HentriesEq.
                      rewrite <-HentriesEq in HstartChildInBlockBase. simpl in HstartChildInBlockBase.
                      destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
                      contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
                      rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
                   ++ rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HlookupBlockPart;
                             try(apply not_eq_sym; assumption).
                      rewrite HlookupBlockPart in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                      destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockBase).
                      contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockChild. assumption. simpl.
                      rewrite HlookupBlockChild. rewrite app_nil_r. assumption.
                -- destruct HblockChildMapped as [Hcontra | HblockChildIsMappedRec].
                   ++ subst a1. rewrite HlookupBlockChild in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup.
                      destruct HnoDup as [_ HnoDup]. specialize(HnoDup startChild HstartChildInBlockChild).
                      contradict HnoDup. apply blockIsMappedAddrInPaddrList with blockPart. assumption. simpl.
                      rewrite Hs1 in HlookupBlockPart. simpl in HlookupBlockPart.
                      destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
                      ** rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockPart. rewrite HlookupBlocks0.
                         rewrite <-HnewB in HlookupBlockPart. rewrite HnewBentry in HlookupBlockPart.
                         simpl in HlookupBlockPart. injection HlookupBlockPart as HentriesEq.
                         rewrite <-HentriesEq in HstartChildInBlockBase. simpl in HstartChildInBlockBase.
                         rewrite app_nil_r. assumption.
                      ** rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HlookupBlockPart;
                               try(apply not_eq_sym; assumption).
                         rewrite HlookupBlockPart. rewrite app_nil_r. assumption.
                   ++ destruct (lookup a1 (memory s0) beqAddr) eqn:HlookupA1; try(apply IHl; assumption).
                      destruct v; try(apply IHl; assumption). apply Lib.NoDupSplit in HnoDup.
                      destruct HnoDup as [_ HnoDup]. apply IHl; assumption.
            + rewrite <-beqAddrFalse in HbeqChildPart.
              assert(HstartInMappedChild: In startChild (getMappedPaddr child s0)).
              {
                apply addrInBlockIsMapped with blockChild; try(assumption). simpl. rewrite HlookupBlockChild.
                rewrite app_nil_r. assumption.
              }
              assert(HstartInChild: In startChild (getUsedPaddr child s0)).
              {
                unfold getUsedPaddr. apply in_or_app. right. assumption.
              }
              assert(HstartInMappedBuild: In startChild (getMappedPaddr partition s0)).
              {
                apply addrInBlockIsMapped with blockPart; try(assumption). simpl.
                rewrite Hs1 in HlookupBlockPart. simpl in HlookupBlockPart.
                destruct (beqAddr blockInParentPartitionAddr blockPart) eqn:HbeqBlockBlock.
                ** rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. subst blockPart. rewrite HlookupBlocks0.
                   rewrite <-HnewB in HlookupBlockPart. rewrite HnewBentry in HlookupBlockPart.
                   simpl in HlookupBlockPart. injection HlookupBlockPart as HentriesEq.
                   rewrite <-HentriesEq in HstartChildInBlockBase. simpl in HstartChildInBlockBase.
                   rewrite app_nil_r. assumption.
                ** rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity in HlookupBlockPart;
                         try(apply not_eq_sym; assumption).
                   rewrite HlookupBlockPart. rewrite app_nil_r. assumption.
              }
              assert(HisChild: isChild s0)
                    by (unfold consistency in Hconsists0; unfold consistency1 in Hconsists0; intuition).
              assert(HpartIsChild: StateLib.pdentryParent partition pdparent s0).
              {
                unfold StateLib.pdentryParent. rewrite HlookupParts0. assumption.
              }
              specialize(HisChild partition pdparent HpartIsPart HpartIsChild).
              specialize(HPIs0 pdparent child partition HparentIsPart HchildIsChild HisChild HbeqChildPart
                          startChild HstartInChild).
              contradict HPIs0. unfold getUsedPaddr. apply in_or_app. right. assumption.
          }
          split.
          { (* BEGIN noChildImpliesAddressesNotShared s *)
            assert(Hcons0: noChildImpliesAddressesNotShared s1) by assumption.
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            intros part pdentry block sh1entryaddr HpartBisIsPart HlookupPartBis HblockMapped Hsh1 HPDChild
               child addr HchildIsChild HaddrInBlock.
            assert(HgetPartitionsEq: getPartitions multiplexer s = getPartitions multiplexer s1).
            {
              rewrite Hs. apply getPartitionsEqPDT with pdentryParent; try(unfold consistency1 in *; intuition).
            }
            rewrite HgetPartitionsEq in HpartBisIsPart.
            assert(HgetBlocksEq: getMappedBlocks part s = getMappedBlocks part s1).
            {
              rewrite Hs. apply getMappedBlocksEqPDT with pdentryParent; try(assumption).
              unfold consistency1 in *; intuition.
              simpl. reflexivity.
            }
            rewrite HgetBlocksEq in HblockMapped.
            assert(HlookupPartBiss1: exists pdentry1, lookup part (memory s1) beqAddr = Some (PDT pdentry1)
                                     /\ parent pdentry1 = parent pdentry).
            {
              rewrite Hs in HlookupPartBis. simpl in HlookupPartBis.
              destruct (beqAddr pdparent part) eqn:HbeqParentPart.
              - rewrite <-DTL.beqAddrTrue in HbeqParentPart. subst part.
                injection HlookupPartBis as Hpdentries. subst pdentry. simpl. exists pdentryParent. split.
                assumption. reflexivity.
              - rewrite <-beqAddrFalse in HbeqParentPart. exists pdentry.
                rewrite removeDupIdentity in HlookupPartBis; intuition.
            }
            destruct HlookupPartBiss1 as [pdentry1 (HlookupPartBiss1 & HparentsEq)].
            assert(HPDChilds1: sh1entryPDchild sh1entryaddr nullAddr s1).
            {
              unfold sh1entryPDchild in *. rewrite Hs in HPDChild. simpl in HPDChild.
              destruct (beqAddr pdparent sh1entryaddr) eqn:HbeqParentSh1; try(exfalso; congruence).
              rewrite <-beqAddrFalse in HbeqParentSh1. rewrite removeDupIdentity in HPDChild; intuition.
            }
            assert(HgetChildrenEq: getChildren part s = getChildren part s1).
            {
              rewrite Hs.
              unfold consistency1 in Hconss1; apply getChildrenEqPDT with pdentryParent; simpl; intuition.
            }
            rewrite HgetChildrenEq in HchildIsChild.
            assert(HaddrInBlocks1: In addr (getAllPaddrAux [block] s1)).
            {
              simpl. simpl in HaddrInBlock. rewrite Hs in HaddrInBlock. simpl in HaddrInBlock.
              destruct (beqAddr pdparent block) eqn:HbeqParentBlock;
                try(simpl in HaddrInBlock; exfalso; congruence).
              rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity in HaddrInBlock; intuition.
            }
            specialize(Hcons0 part pdentry1 block sh1entryaddr HpartBisIsPart HlookupPartBiss1 HblockMapped
               Hsh1 HPDChilds1 child addr HchildIsChild HaddrInBlocks1).
            assert(HgetPaddrEq: getMappedPaddr child s = getMappedPaddr child s1).
            {
              rewrite Hs. apply getMappedPaddrEqPDT with pdentryParent; try(assumption).
              simpl. reflexivity.
              unfold consistency1 in *; intuition.
            }
            rewrite HgetPaddrEq. assumption.
            (* END noChildImpliesAddressesNotShared *)
          }
          assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
          specialize(HparentOfPart partition pdentryPart HlookupParts1).
          destruct HparentOfPart as (_ & _ & HparentNotPart). rewrite beqAddrFalse in HparentNotPart.
          rewrite <-HparentEq in HparentNotPart.
          split.
          {
            intros parentsList2 HparentsList2.
            assert(HparentsList2Ext: isParentsList s (pdparent::parentsList2) partition).
            {
              simpl. destruct HpropsOr as [Hss1Eq | Hs].
              - subst s. rewrite HlookupParent. split. assumption. split; try(assumption). exists pdentryPart.
                split; assumption.
              - rewrite Hs. simpl. rewrite beqAddrTrue. split. assumption.
                split; try(rewrite Hs in HparentsList2; assumption). exists pdentryPart.
                rewrite HparentNotPart.
                rewrite <-beqAddrFalse in HparentNotPart. rewrite removeDupIdentity; intuition.
            }
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s;
                specialize(Hlength (pdparent::parentsList2) HparentsList2Ext); simpl in Hlength; lia).
            assert(HparentsList2Exts1: isParentsList s1 (pdparent::parentsList2) partition).
            {
              apply isParentsListEqPDTSameParent with pdparent
                        {|
                          structure := structure pdentryParent;
                          firstfreeslot := firstfreeslot pdentryParent;
                          nbfreeslots := nbfreeslots pdentryParent;
                          nbprepare := nbprepare pdentryParent;
                          parent := parent pdentryParent;
                          MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                          vidtAddr := vidtAddr pdentryParent
                        |} s; simpl; try(assumption); try(unfold consistency1 in *; intuition; congruence).
              exists pdentryPart. exists pdentryPart. exists pdentryParent. intuition.
              - rewrite Hs. simpl. rewrite HparentNotPart. rewrite <-beqAddrFalse in HparentNotPart.
                rewrite removeDupIdentity; intuition.
              - rewrite <-beqAddrFalse in HparentNotPart. exfalso; congruence.
              - rewrite <-beqAddrFalse in HparentNotPart. exfalso; congruence.
            }
            specialize(Hlength (pdparent::parentsList2) HparentsList2Exts1). simpl in Hlength. lia.
          }
          split.
          {
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            assert(HgetMappedPaddrEq: getMappedPaddr pdparent s = getMappedPaddr pdparent s1).
            {
              rewrite Hs. apply getMappedPaddrEqPDT with pdentryParent; simpl. assumption. reflexivity.
              unfold consistency1 in *; intuition.
            }
            rewrite HgetMappedPaddrEq. assumption.
          }
          exists sInit. exists (parent pdentryParent). exists (statesList ++ [s]).
          exists (parentsList ++ [pdparent]). split. assumption. split. assumption. split. assumption.
          split. instantiate(1:= fun sIn => P sIn). simpl. assumption.
          split. assumption. split.
          assert(HlookupPartsInit: exists pdentryPartsInit, lookup partition (memory sInit) beqAddr
                                                              = Some(PDT pdentryPartsInit)
                                                            /\ parent pdentryPart = parent pdentryPartsInit).
          {
            apply stablePDTParentIsBuiltRev with statesList parentsList pdbasepartition startaddr endaddr flag s0.
            assumption.
            rewrite Hs1 in HlookupParts1. simpl in HlookupParts1.
            destruct (beqAddr blockInParentPartitionAddr partition) eqn:HbeqBlockPart; try(exfalso; congruence).
            rewrite <-beqAddrFalse in HbeqBlockPart. rewrite removeDupIdentity in HlookupParts1; intuition.
          }
          destruct HlookupPartsInit as [pdentryPartsInit (HlookupPartsInit & HparentsEq)].
          assert(HlookupParentsInit: exists pdentryParentsInit, lookup pdparent (memory sInit) beqAddr
                                                              = Some(PDT pdentryParentsInit)
                                                            /\ parent pdentryParent = parent pdentryParentsInit).
          {
            apply stablePDTParentIsBuiltRev with statesList parentsList pdbasepartition startaddr endaddr flag s0.
            assumption.
            rewrite Hs1 in HlookupParent. simpl in HlookupParent. rewrite HbeqBlockParent in *.
            rewrite <-beqAddrFalse in HbeqBlockParent. rewrite removeDupIdentity in HlookupParent; intuition.
          }
          destruct HlookupParentsInit as [pdentryParentsInit (HlookupParentsInit & _)].
          apply isParentsListRec with partition pdentryParentsInit pdentryPartsInit; try(assumption).
          rewrite HparentEq. assumption.
          split. apply eq_sym. apply last_last.
          split. apply eq_sym. apply last_last. split.
          exists pdentryBase. destruct HpropsOr as [Hss1Eq | Hs].
          { subst s. intuition. }
          {
            rewrite Hs. simpl.
            assert(HbeqParentBase: pdparent <> pdbasepartition).
            {
              unfold consistency in HconsistInit; unfold consistency1 in HconsistInit.
              apply not_eq_sym. apply basePartNotLastInParentsLists with (parentsList ++ [pdparent]) sInit;
                    try(intuition; congruence).
              rewrite last_last. reflexivity.
              intro Hcontra. apply app_eq_nil in Hcontra. destruct Hcontra. congruence.
            }
            rewrite beqAddrFalse in HbeqParentBase. rewrite HbeqParentBase.
            rewrite <-beqAddrFalse in HbeqParentBase. rewrite removeDupIdentity; intuition.
          }
          split.
          destruct HpropsOr as [Hss1Eq | Hs].
          {
            subst s. exists pdentryParent. split. assumption.
            assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
            specialize(HparentOfPart pdparent pdentryParent HlookupParent).
            destruct HparentOfPart as (HpdparentIsPart & HparentOfRoot & _).
            destruct (beqAddr pdparent constantRootPartM) eqn:HbeqParentRoot.
            - right. rewrite <-DTL.beqAddrTrue in HbeqParentRoot. rewrite HbeqParentRoot in HparentOfRoot.
              intuition.
            - left. rewrite <-beqAddrFalse in HbeqParentRoot. intuition.
          }
          {
            exists ({|
                      structure := structure pdentryParent;
                      firstfreeslot := firstfreeslot pdentryParent;
                      nbfreeslots := nbfreeslots pdentryParent;
                      nbprepare := nbprepare pdentryParent;
                      parent := parent pdentryParent;
                      MPU := MAL.removeBlockFromPhysicalMPUAux blockInParentPartitionAddr realMPU;
                      vidtAddr := vidtAddr pdentryParent
                    |}). rewrite Hs. simpl. rewrite beqAddrTrue. split. reflexivity.
            assert(HparentOfPart: parentOfPartitionIsPartition s1) by (unfold consistency1 in *; intuition).
            specialize(HparentOfPart pdparent pdentryParent HlookupParent).
            destruct HparentOfPart as (HpdparentIsPart & HparentOfRoot & _).
            destruct (beqAddr pdparent constantRootPartM) eqn:HbeqParentRoot.
            - right. rewrite <-DTL.beqAddrTrue in HbeqParentRoot. rewrite HbeqParentRoot in HparentOfRoot.
              intuition.
            - left. rewrite <-beqAddrFalse in HbeqParentRoot. intuition.
          }
          split. rewrite <-HgetPartEqsInit. assumption. split. rewrite <-HgetPartEqsInit. assumption.
          assert(HlookupParentsInit: lookup pdparent (memory sInit) beqAddr = Some (PDT pdentryParent)).
          {
            assert(HparentIsPDT: isPDT pdparent sInit).
            {
              assert(HPDT: exists pdentryParentInit,
                            lookup pdparent (memory sInit) beqAddr = Some (PDT pdentryParentInit)
                            /\ parent pdentryParent = parent pdentryParentInit).
              {
                apply stablePDTParentIsBuiltRev with statesList parentsList pdbasepartition startaddr endaddr
                    flag s0; assumption.
              }
              destruct HPDT as [pdentryParentInit (HlookupParentsInit & _)].
              unfold isPDT. rewrite HlookupParentsInit. trivial.
            }
            assert(HlookupEq: lookup pdparent (memory s0) beqAddr = lookup pdparent (memory sInit) beqAddr).
            {
              apply lookupPDTEqWriteAccess with statesList parentsList startaddr endaddr flag pdbasepartition;
                    try(assumption);
                    try(unfold isPDT; rewrite HlookupBasesInit; trivial).
            }
            rewrite HlookupParents0 in HlookupEq. apply eq_sym. assumption.
          }
          assert(HcurrPartEq: currentPartition s1 = currentPartition sInit).
          {
            rewrite Hs1. simpl. apply currentPartitionEqIsBuilt with pdbasepartition statesList parentsList
                                            startaddr endaddr flag. assumption.
          }
          rewrite HcurrPartEq in HpropsOr.
          split. destruct HbaseBlock as [blockBase [bentryBase [bentryBasesInit (HlookupBlockBasesInit &
                                          HPFlagBasesInit & HAFlagBasesInit & HblockBaseIsMappedsInit &
                                          HblockBaseAccMappedsInit & HstartBasesInit & HendBasesInit &
                                          HcheckBasesInit & HlookupBlockBase & HPFlagBase & HAFlagBase &
                                          HblockBaseIsMapped & HstartBase & HendBase & HckeckBase)]]].
          assert(HlookupBlockBases1: lookup blockBase (memory s1) beqAddr = Some (BE bentryBase)).
          {
            rewrite Hs1. simpl. destruct (beqAddr blockInParentPartitionAddr blockBase) eqn:HbeqBlockBlock.
            {
              rewrite <-DTL.beqAddrTrue in HbeqBlockBlock. rewrite HbeqBlockBlock in *.
              assert(Hdisjoint: DisjointKSEntries s0) by (unfold consistency1 in *; intuition).
              assert(HbeqBaseParent: pdbasepartition <> pdparent).
              {
                assert(Htree: partitionTreeIsTree sInit)
                    by (unfold consistency in *; unfold consistency1 in *; intuition).
                assert(HparentOfPart: parentOfPartitionIsPartition sInit)
                            by (unfold consistency in *; unfold consistency1 in *; intuition).
                apply basePartNotLastInParentsLists with (parentsList++[pdparent]) sInit; try(assumption).
                - apply eq_sym. apply last_last.
                - intro Hcontra. apply app_eq_nil in Hcontra. destruct Hcontra. congruence.
              }
              assert(HbaseIsPDT: isPDT pdbasepartition s0).
              { unfold isPDT. rewrite HlookupBases0. trivial. }
              assert(HpdparentIsPDT: isPDT pdparent s0).
              {
                unfold isPDT. rewrite HlookupParents0. trivial.
              }
              specialize(Hdisjoint pdbasepartition pdparent HbaseIsPDT HpdparentIsPDT HbeqBaseParent).
              destruct Hdisjoint as [entriesList1 [entriesList2 (Hlist1 & Hlist2 & Hdisjoint)]].
              subst entriesList1. subst entriesList2.
              unfold getMappedBlocks in *. apply InFilterPresentInList in HblockInMappedBlocks0.
              apply InFilterPresentInList in HblockBaseIsMapped.
              specialize(Hdisjoint blockBase HblockBaseIsMapped). exfalso; congruence.
            }
            rewrite <-beqAddrFalse in HbeqBlockBlock. rewrite removeDupIdentity; intuition.
          }
          exists blockBase. exists bentryBase. exists bentryBasesInit.
          assert(HlookupBlockBases: lookup blockBase (memory s) beqAddr = Some (BE bentryBase)).
          {
            destruct HpropsOr as [Hss1Eq | Hs].
            ** subst s. assumption.
            ** rewrite Hs. simpl. destruct (beqAddr pdparent blockBase) eqn:HbeqParentBase.
               {
                 rewrite <-DTL.beqAddrTrue in HbeqParentBase. rewrite HbeqParentBase in *.
                 rewrite HlookupBlockBases1 in HlookupParent. exfalso; congruence.
               }
               rewrite <-beqAddrFalse in HbeqParentBase. rewrite removeDupIdentity; intuition.
          }
          assert(bentryPFlag blockBase true s).
          {
            unfold bentryPFlag in *. rewrite HlookupBlockBases. rewrite HlookupBlockBase in HPFlagBase.
            assumption.
          }
          assert(bentryAFlag blockBase true s).
          {
            unfold bentryAFlag in *. rewrite HlookupBlockBases. rewrite HlookupBlockBase in HAFlagBase.
            assumption.
          }
          assert(In blockBase (getMappedBlocks pdbasepartition s)).
          {
            assert(HgetMappedEq: getMappedBlocks pdbasepartition s1 = getMappedBlocks pdbasepartition s0).
            {
              rewrite Hs1. apply getMappedBlocksEqBENoChange with bentry. assumption. rewrite <-HnewB.
              rewrite HnewBentry. simpl. reflexivity.
            }
            rewrite <-HgetMappedEq in HblockBaseIsMapped. destruct HpropsOr as [Hss1Eq | Hs].
            subst s. assumption.
            assert(HgetMappedBaseEq: getMappedBlocks pdbasepartition s = getMappedBlocks pdbasepartition s1).
            {
              rewrite Hs. rewrite <-HcurrPartEq. apply getMappedBlocksEqPDT with pdentryParent. assumption.
              unfold consistency1 in *; intuition.
              simpl. reflexivity.
            }
            rewrite HgetMappedBaseEq. assumption.
          }
          assert(bentryStartAddr blockBase startaddr s).
          {
            unfold bentryStartAddr in *. rewrite HlookupBlockBases. rewrite HlookupBlockBase in HstartBase.
            assumption.
          }
          assert(bentryEndAddr blockBase endaddr s).
          {
            unfold bentryEndAddr in *. rewrite HlookupBlockBases. rewrite HlookupBlockBase in HendBase.
            assumption.
          }
          assert(HcheckBases1: false = checkChild blockBase s1 (CPaddr (blockBase + sh1offset))).
          {
            unfold checkChild in *.
            assert(HblockBaseIsBE: isBE blockBase s0) by (unfold isBE; rewrite HlookupBlockBase; trivial).
            assert(HlookupSh1Eq: lookup (CPaddr (blockBase + sh1offset)) (memory s1) beqAddr
                                  = lookup (CPaddr (blockBase + sh1offset)) (memory s0) beqAddr).
            {
              assert(HwellFormedShadow: wellFormedFstShadowIfBlockEntry s0)
                      by (unfold consistency1 in *; intuition).
              specialize(HwellFormedShadow blockBase HblockBaseIsBE). unfold isSHE in HwellFormedShadow.
              rewrite Hs1. simpl.
              destruct (beqAddr blockInParentPartitionAddr (CPaddr (blockBase + sh1offset)))
                  eqn:HbeqBlockBlockBaseSh1.
              {
                rewrite <-DTL.beqAddrTrue in HbeqBlockBlockBaseSh1. rewrite <-HbeqBlockBlockBaseSh1 in *.
                rewrite HlookupBlocks0 in HwellFormedShadow. exfalso; congruence.
              }
              rewrite <-beqAddrFalse in HbeqBlockBlockBaseSh1. rewrite removeDupIdentity; intuition.
            }
            rewrite HlookupSh1Eq. rewrite Hs1. simpl.
            destruct (beqAddr blockInParentPartitionAddr blockBase) eqn:HbeqBlockBlockBase.
            - rewrite HlookupBlockBase in HckeckBase. assumption.
            - rewrite <-beqAddrFalse in HbeqBlockBlockBase. rewrite removeDupIdentity; intuition.
          }
          assert(false = checkChild blockBase s (CPaddr (blockBase + sh1offset))).
          {
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            unfold checkChild in *.
            assert(HblockBaseIsBE: isBE blockBase s0) by (unfold isBE; rewrite HlookupBlockBase; trivial).
            assert(HlookupSh1Eq: lookup (CPaddr (blockBase + sh1offset)) (memory s) beqAddr
                                  = lookup (CPaddr (blockBase + sh1offset)) (memory s1) beqAddr).
            {
              assert(HwellFormedShadow: wellFormedFstShadowIfBlockEntry s0)
                      by (unfold consistency1 in *; intuition).
              specialize(HwellFormedShadow blockBase HblockBaseIsBE). unfold isSHE in HwellFormedShadow.
              rewrite Hs. simpl.
              destruct (beqAddr pdparent (CPaddr (blockBase + sh1offset))) eqn:HbeqParentBlockBaseSh1.
              {
                rewrite <-DTL.beqAddrTrue in HbeqParentBlockBaseSh1. rewrite <-HbeqParentBlockBaseSh1 in *.
                rewrite HlookupParents0 in HwellFormedShadow. exfalso; congruence.
              }
              rewrite <-beqAddrFalse in HbeqParentBlockBaseSh1. rewrite removeDupIdentity; intuition.
            }
            rewrite HlookupSh1Eq. rewrite Hs. simpl.
            destruct (beqAddr pdparent blockBase) eqn:HbeqParentBlockBase.
            { reflexivity. }
            rewrite <-beqAddrFalse in HbeqParentBlockBase. rewrite removeDupIdentity; intuition.
          }
          intuition. split. exists blockInParentPartitionAddr. exists newBentry.
          assert(HblockInMappedBlocksEqs: getMappedBlocks pdparent s = getMappedBlocks pdparent s1).
          {
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; reflexivity).
            rewrite Hs. rewrite <-HcurrPartEq. apply getMappedBlocksEqPDT with pdentryParent. assumption.
            unfold consistency1 in *; intuition. simpl. reflexivity.
          }
          rewrite HblockInMappedBlocksEqs.
          assert(Hprops: bentryPFlag blockInParentPartitionAddr true s
                          /\ bentryStartAddr blockInParentPartitionAddr startaddr s
                          /\ bentryEndAddr blockInParentPartitionAddr endaddr s).
          {
            unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
            rewrite HlookupBlocks. rewrite HlookupBlocks1 in *. intuition.
          }
          assert(HcheckBlocks1: false = checkChild blockInParentPartitionAddr s1
                                              (CPaddr (blockInParentPartitionAddr + sh1offset))).
          {
            unfold checkChild in *.
            assert(HblockIsBE: isBE blockInParentPartitionAddr s0)
                        by (unfold isBE; rewrite HlookupBlocks0; trivial).
            assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr
                                  = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s0) beqAddr).
            {
              assert(HwellFormedShadow: wellFormedFstShadowIfBlockEntry s0)
                      by (unfold consistency1 in *; intuition).
              specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE).
              unfold isSHE in HwellFormedShadow. rewrite Hs1. simpl. rewrite HbeqBlockBlockSh1.
              rewrite <-beqAddrFalse in HbeqBlockBlockSh1. rewrite removeDupIdentity; intuition.
            }
            rewrite HlookupSh1Eq. rewrite Hs1. simpl. rewrite beqAddrTrue.
            rewrite HlookupBlocks0 in HnoPDFlagBlock. assumption.
          }
          assert(false = checkChild blockInParentPartitionAddr s
                                (CPaddr (blockInParentPartitionAddr + sh1offset))).
          {
            destruct HpropsOr as [Hss1Eq | Hs]; try(subst s; assumption).
            unfold checkChild in *.
            assert(HblockIsBE: isBE blockInParentPartitionAddr s1)
                  by (unfold isBE; rewrite HlookupBlocks1; trivial).
            assert(HlookupSh1Eq: lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s) beqAddr
                                  = lookup (CPaddr (blockInParentPartitionAddr + sh1offset)) (memory s1) beqAddr).
            {
              assert(HwellFormedShadow: wellFormedFstShadowIfBlockEntry s1)
                      by (unfold consistency1 in *; intuition).
              specialize(HwellFormedShadow blockInParentPartitionAddr HblockIsBE).
              unfold isSHE in HwellFormedShadow. rewrite Hs. simpl.
              destruct (beqAddr pdparent (CPaddr (blockInParentPartitionAddr + sh1offset)))
                          eqn:HbeqParentBlockSh1.
              {
                rewrite <-DTL.beqAddrTrue in HbeqParentBlockSh1. rewrite <-HbeqParentBlockSh1 in *.
                rewrite HlookupParent in HwellFormedShadow. exfalso; congruence.
              }
              rewrite <-beqAddrFalse in HbeqParentBlockSh1. rewrite removeDupIdentity; intuition.
            }
            rewrite HlookupSh1Eq. rewrite Hs. simpl.
            destruct (beqAddr pdparent blockInParentPartitionAddr) eqn:HbeqParentBlock.
            { reflexivity. }
            rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
          }
          intuition.
          split; try(split; try(unfold consistency in *; unfold consistency2 in *; intuition; congruence);
                  try(apply isBuiltFromWriteAccessibleRecRec with s0 s1 partition pdentryPart pdentryParent
                              pdentryBase blockInParentPartitionAddr bentry newBentry realMPU; intuition)).
          destruct HpropsOr as [Hss1Eq | Hs].
          ** (* s = s1 *)
             subst s.
             destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                                           HAFlagBlockAddr & HblockAddrMappedParent & HstartBlockAddr &
                                           HendBlockAddr & HpartialAccess))].
             exists blockaddr. exists bentryBlockAddr. intuition. subst flag. assumption.
          ** (* s <> s1 *)
             destruct HpartialAccess as [blockaddr (bentryBlockAddr & (HlookupBlockAddr & HPFlagBlockAddr &
                                           HAFlagBlockAddr & HblockAddrMappedParent & HstartBlockAddr &
                                           HendBlockAddr & HpartialAccess))].
             exists blockaddr. exists bentryBlockAddr.
             assert(HlookupBlockAddrs: lookup blockaddr (memory s) beqAddr = Some (BE bentryBlockAddr)).
             {
               rewrite Hs. simpl.
               destruct (beqAddr pdparent blockaddr) eqn:HbeqParentBlock.
               {
                 rewrite <-DTL.beqAddrTrue in HbeqParentBlock. rewrite HbeqParentBlock in *.
                 rewrite HlookupParent in HlookupBlockAddr. exfalso; congruence.
               }
               rewrite <-beqAddrFalse in HbeqParentBlock. rewrite removeDupIdentity; intuition.
             }
             split. assumption. split. unfold bentryPFlag in *. rewrite HlookupBlockAddrs.
             rewrite HlookupBlockAddr in HPFlagBlockAddr. assumption. split. intro Hflag. subst flag.
             unfold bentryAFlag in *. rewrite HlookupBlockAddrs. rewrite HlookupBlockAddr in HAFlagBlockAddr.
             assumption.
             rewrite <-HcurrPartEq in Hs.
             assert(HblockInMappedBlocksEqs: getMappedBlocks pdparent s = getMappedBlocks pdparent s1).
             {
               rewrite Hs. unfold consistency1 in Hconss1; apply getMappedBlocksEqPDT with pdentryParent;
                  intuition.
             }
             rewrite HblockInMappedBlocksEqs. split. assumption. split. unfold bentryStartAddr in *.
             rewrite HlookupBlockAddrs. rewrite HlookupBlockAddr in HstartBlockAddr. assumption.
             split. unfold bentryEndAddr in *. rewrite HlookupBlockAddrs.
             rewrite HlookupBlockAddr in HendBlockAddr. assumption. right.
             intros parent child addr HnotEdgeCase Hparent'IsPart HchildIsChild HaddrAccMappedParent
                   HaddrMappedChild.
             assert(HgetPartEqs: getPartitions multiplexer s = getPartitions multiplexer s1).
             {
               rewrite Hs. unfold consistency1 in Hconss1; apply getPartitionsEqPDT with pdentryParent;
                  intuition.
             }
             assert(HgetChildrenEq: getChildren parent s = getChildren parent s1).
             {
               rewrite Hs. unfold consistency1 in Hconss1; apply getChildrenEqPDT with pdentryParent;
                  intuition.
             }
             assert(HgetAccMappedEq: getAccessibleMappedPaddr parent s = getAccessibleMappedPaddr parent s1).
             {
               rewrite Hs.
               unfold consistency1 in Hconss1; apply getAccessibleMappedPaddrEqPDT with pdentryParent;
                  intuition.
             }
             assert(HgetMappedEq: getMappedPaddr child s = getMappedPaddr child s1).
             {
               rewrite Hs. unfold consistency1 in Hconss1; apply getMappedPaddrEqPDT with pdentryParent;
                  intuition.
             }
             rewrite HgetPartEqs in Hparent'IsPart. rewrite HgetChildrenEq in HchildIsChild.
             rewrite HgetAccMappedEq in HaddrAccMappedParent. rewrite HgetMappedEq in HaddrMappedChild.
             specialize(HpartialAccess parent child addr HnotEdgeCase Hparent'IsPart HchildIsChild
                   HaddrAccMappedParent HaddrMappedChild).
             assert(HgetAccMappedEqChild: getAccessibleMappedPaddr child s = getAccessibleMappedPaddr child s1).
             {
               rewrite Hs.
               unfold consistency1 in Hconss1; apply getAccessibleMappedPaddrEqPDT with pdentryParent;
                  intuition.
             }
             rewrite HgetAccMappedEqChild. assumption.
    -- simpl. intros s writeSucc Hprops.
       destruct Hprops as (HPIs & HKDIs & HVSs & Hprops).
       destruct Hprops as [s0 [pdentryBase [statesList
                           [parentsList (HPIs0 & HKDIs0 & HVSs0 & HPs0 & Hconsists0 & HparentsList & HsIsLast &
                            HlookupBases0 & HlookupBases & HbaseIsPart & Hconsists & HnoDup & Hshared & Hrange
                            & HchildBlockProps & HblockBase & HpartialAccess & HlastProps & HisBuilt)]]]].
       split. assumption. split. assumption. split. assumption.
       exists s0. exists pdentryBase. exists statesList. exists parentsList.
       intuition.
Qed.

Lemma writeAccessibleRec (pdbasepartition startaddr endaddr : paddr) (flag : bool)
                          (P : state -> Prop):
{{fun s => partitionsIsolation s
            /\ kernelDataIsolation s
            /\ verticalSharing s
            /\ consistency s
            /\ P s
            /\ (exists pdentryBase, lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase))
            /\ In pdbasepartition (getPartitions multiplexer s)
            /\ (exists blockBase bentryBase,
                   lookup blockBase (memory s) beqAddr = Some (BE bentryBase)
                   /\ bentryPFlag blockBase true s
                   /\ bentryAFlag blockBase true s
                   /\ In blockBase (getMappedBlocks pdbasepartition s)
                   /\ bentryStartAddr blockBase startaddr s
                   /\ bentryEndAddr blockBase endaddr s
                   /\ false = checkChild blockBase s (CPaddr (blockBase + sh1offset)))
}}
writeAccessibleRec pdbasepartition startaddr endaddr flag
{{fun writeSucceded s =>
      partitionsIsolation s
      /\ kernelDataIsolation s
      /\ verticalSharing s
      /\ exists s0 pdentryBase statesList parentsList,
          (*it probably is impossible to prove that pdbasepart = pdbasepartition*)
          (* Common properties *)
          partitionsIsolation s0
          /\ kernelDataIsolation s0
          /\ verticalSharing s0
          /\ P s0
          /\ consistency s0
          /\ isParentsList s0 parentsList pdbasepartition
          /\ s = last statesList s0
          /\ lookup pdbasepartition (memory s0) beqAddr = Some (PDT pdentryBase)
          /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase)
          /\ In pdbasepartition (getPartitions multiplexer s0)
          /\ consistency1 s
          /\ noDupUsedPaddrList s
          /\ sharedBlockPointsToChild s
          /\ adressesRangePreservedIfOriginAndNextOk s
          /\ childsBlocksPropsInParent s
          /\ noChildImpliesAddressesNotShared s
          /\ (exists blockBase bentryBase bentryBases0,
                 lookup blockBase (memory s0) beqAddr = Some (BE bentryBases0)
                 /\ bentryPFlag blockBase true s0
                 /\ bentryAFlag blockBase true s0
                 /\ In blockBase (getMappedBlocks pdbasepartition s0)
                 /\ In blockBase (getAccessibleMappedBlocks pdbasepartition s0)
                 /\ bentryStartAddr blockBase startaddr s0
                 /\ bentryEndAddr blockBase endaddr s0
                 /\ false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
                 /\ lookup blockBase (memory s) beqAddr = Some (BE bentryBase)
                 /\ bentryPFlag blockBase true s
                 /\ bentryAFlag blockBase true s
                 /\ In blockBase (getMappedBlocks pdbasepartition s)
                 /\ bentryStartAddr blockBase startaddr s
                 /\ bentryEndAddr blockBase endaddr s
                 /\ false = checkChild blockBase s (CPaddr (blockBase + sh1offset)))
          (*/\ (timeout > maxAddr -> writeSucceded = true)*) (*probably true, but impossible to prove*)
          /\ accessibleParentPaddrIsAccessibleIntoChild s
          /\ (exists lastPart pdentryLast,
                 lastPart = last parentsList pdbasepartition
                 /\ lookup lastPart (memory s) beqAddr = Some (PDT pdentryLast)
                 /\ (parent pdentryLast = nullAddr
                    \/ (forall block,
                         In block (getMappedBlocks (parent pdentryLast) s)
                          -> ~ (bentryStartAddr block startaddr s /\ bentryEndAddr block endaddr s))))
          /\ isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition startaddr endaddr flag
}}.
Proof.
unfold writeAccessibleRec. eapply weaken. apply writeAccessibleRecAux.
simpl. intros s Hprops.
destruct Hprops as (HPI & HKDI & HVS & Hconsist & HP & [pdentryBase HlookupBase] & HbaseIsPart & HblockBase).
unfold consistency in Hconsist. unfold consistency2 in Hconsist.
assert(forall parentsList, isParentsList s parentsList pdbasepartition -> length parentsList < MAL.N).
{
  intros parentsList HparentsList. unfold MAL.N.
  assert(HnoDup: NoDup parentsList).
  {
    unfold consistency1 in Hconsist; apply parentOfPartNotInParentsListsTail with pdbasepartition s; intuition.
  }
  assert(HnoDupExt: NoDup (pdbasepartition::parentsList)).
  {
    apply NoDup_cons; try(assumption).
    assert(Htree: partitionTreeIsTree s) by (unfold consistency1 in *; intuition).
    unfold partitionTreeIsTree in Htree. destruct parentsList. intuition.
    simpl in HparentsList.
    destruct (lookup p (memory s) beqAddr) eqn:HlookupParent; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct HparentsList as (HbaseNotRoot & [pdentryBaseBis (HlookupBaseBis & Hparent)] & HparentsListRec).
    subst p. rewrite HlookupBase in HlookupBaseBis. injection HlookupBaseBis as HentriesEq.
    subst pdentryBaseBis.
    assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
    specialize(HparentOfPart pdbasepartition pdentryBase HlookupBase).
    destruct HparentOfPart as (HparentIsPart & _ & HparentNotPart). specialize(HparentIsPart HbaseNotRoot).
    destruct HparentIsPart as (_ & HparentIsPart). simpl. apply Classical_Prop.and_not_or. split.
    assumption. apply Htree with (parent pdentryBase); try(assumption). unfold pdentryParent.
    rewrite HlookupBase. reflexivity.
  }
  pose proof (lengthNoDupPartitions (pdbasepartition::parentsList) HnoDupExt) as Hres. simpl in Hres. lia.
}
assert(In startaddr (getMappedPaddr pdbasepartition s)).
{
  destruct HblockBase as [blockBase [_ (_ & HPFlag & _ & HblockBaseMapped & Hstart & Hend & _)]].
  apply addrInBlockIsMapped with blockBase; try(assumption). simpl.
  assert(HwellFormed: wellFormedBlock s) by (unfold consistency1 in *; intuition).
  specialize(HwellFormed blockBase startaddr endaddr HPFlag Hstart Hend). destruct HwellFormed.
  unfold bentryStartAddr in *.
  unfold bentryEndAddr in *. destruct (lookup blockBase (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend.
  apply getAllPaddrBlockIncl; lia.
}
intuition. exists s.
exists (parent pdentryBase). exists []. exists [].
destruct HblockBase as [blockBase [bentryBase (HlookupBlock & HPFlag & HAFlag & HblockMapped & Hstart & Hend &
                        HnoPDFlag)]].
intuition.
- unfold consistency. unfold consistency2. intuition.
- simpl. trivial.
- exists pdentryBase. intuition.
- exists pdentryBase. split. assumption.
  assert(HparentOfPart: parentOfPartitionIsPartition s) by (unfold consistency1 in *; intuition).
  specialize(HparentOfPart pdbasepartition pdentryBase HlookupBase).
  destruct HparentOfPart as (HparentIsPart & HparentOfRoot & _).
  destruct (beqAddr pdbasepartition constantRootPartM) eqn:HbeqBaseRoot.
  + rewrite <-DTL.beqAddrTrue in HbeqBaseRoot. specialize(HparentOfRoot HbeqBaseRoot). right. intuition.
  + rewrite <-beqAddrFalse in HbeqBaseRoot. left. intuition.
- exists blockBase. exists bentryBase. exists bentryBase. intuition.
  unfold getAccessibleMappedBlocks. rewrite HlookupBase. apply accessibleIsInFilterAccessible with bentryBase;
      try(assumption). unfold bentryAFlag in HAFlag. rewrite HlookupBlock in HAFlag. intuition.
- exists blockBase. exists bentryBase. intuition.
- exists blockBase. exists bentryBase. intuition.
- simpl. intuition.
Qed.

(* Used in collect too *)
Lemma writeAccessibleToAncestorsIfNotCutRec (pdbasepartition entryaddr blockStart blockEnd : paddr) (flag : bool)
                                            (P : state -> Prop):
{{fun  s => partitionsIsolation s
            /\ kernelDataIsolation s
            /\ verticalSharing s
            /\ P s /\ consistency s
            /\ (exists pdentryBase, lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentryBase))
            /\ In pdbasepartition (getPartitions multiplexer s)
            /\ (exists bentry : BlockEntry, lookup entryaddr s.(memory) beqAddr = Some (BE bentry))
            /\ bentryPFlag entryaddr true s
            /\ bentryAFlag entryaddr true s
            /\ bentryStartAddr entryaddr blockStart s
            /\ bentryEndAddr entryaddr blockEnd s
            /\ In entryaddr (getMappedBlocks pdbasepartition s)
}}
writeAccessibleToAncestorsIfNotCutRec pdbasepartition entryaddr flag
{{fun writeSucceded s =>
      partitionsIsolation s
      /\ kernelDataIsolation s
      /\ verticalSharing s
      /\ consistency s
      /\ exists s0 pdentry blockOrigin (*blockStart blockEnd*) blockNext parentsList statesList blockBase
            bentryBase bentryBases0,
        partitionsIsolation s0
        /\ kernelDataIsolation s0
        /\ verticalSharing s0
        /\ isParentsList s0 parentsList pdbasepartition
        /\ s = last statesList s0
        /\ isBuiltFromWriteAccessibleRec s0 s statesList parentsList pdbasepartition blockStart blockEnd flag
        /\ isPDT pdbasepartition s0
        /\ In pdbasepartition (getPartitions multiplexer s0)
        /\ lookup pdbasepartition (memory s) beqAddr = Some (PDT pdentry)
        /\ In pdbasepartition (getPartitions multiplexer s0)
        /\ P s0
        /\ consistency s0
        /\ lookup blockBase (memory s0) beqAddr = Some (BE bentryBases0)
        /\ bentryPFlag blockBase true s0
        /\ bentryAFlag blockBase true s0
        /\ In blockBase (getMappedBlocks pdbasepartition s0)
        /\ In blockBase (getAccessibleMappedBlocks pdbasepartition s0)
        /\ bentryStartAddr blockBase blockStart s0
        /\ bentryEndAddr blockBase blockEnd s0
        /\ false = checkChild blockBase s0 (CPaddr (blockBase + sh1offset))
        /\ lookup blockBase (memory s) beqAddr = Some (BE bentryBase)
        /\ bentryPFlag blockBase true s
        /\ bentryAFlag blockBase true s
        /\ In blockBase (getMappedBlocks pdbasepartition s)
        /\ bentryStartAddr blockBase blockStart s
        /\ bentryEndAddr blockBase blockEnd s
        /\ false = checkChild blockBase s (CPaddr (blockBase + sh1offset))
        /\ (exists (scentry : SCEntry) (scentryaddr : paddr),
              lookup scentryaddr (memory s0) beqAddr = Some (SCE scentry)
              /\ scentryNext scentryaddr blockNext s0)
        /\ (exists (scentry : SCEntry) (scentryaddr : paddr),
              lookup scentryaddr (memory s0) beqAddr = Some (SCE scentry)
              /\ scentryOrigin scentryaddr blockOrigin s0)
        /\ bentryStartAddr entryaddr blockStart s0
        /\ (s0 = s
           \/ (blockStart = blockOrigin /\ blockNext = nullAddr))
        /\ (exists lastPart pdentryLast,
               lastPart = last parentsList pdbasepartition
               /\ lookup lastPart (memory s) beqAddr = Some (PDT pdentryLast)
               /\ (parent pdentryLast = nullAddr
                  \/ (forall block,
                       In block (getMappedBlocks (parent pdentryLast) s)
                        -> ~ (bentryStartAddr block blockStart s /\ bentryEndAddr block blockEnd s))))
}}.
Proof.
unfold writeAccessibleToAncestorsIfNotCutRec.
eapply bindRev.
{ (** MAL.readSCOriginFromBlockEntryAddr **)
  eapply weaken. eapply readSCOriginFromBlockEntryAddr.
  simpl. intros s Hprops.
  split. eapply Hprops. intuition.
}
intro blockOrigin. eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr **)
  eapply weaken. eapply readBlockStartFromBlockEntryAddr.
  intros s Hprops. simpl.
  split. eapply Hprops. unfold StateLib.isBE.
  destruct Hprops as [Hprops1 HpropsSCE].
  destruct Hprops1 as (_ & _ & _ & _ & _ & _ & _ & HBE & _). destruct HBE as [bentry HBE]. rewrite HBE.
  trivial.
}
intro blockStartBis. eapply bindRev.
{ (** MAL.readSCNextFromBlockEntryAddr **)
  eapply weaken. eapply readSCNextFromBlockEntryAddr.
  simpl. intros s Hprops. split. eapply Hprops. unfold consistency in Hprops. intuition.
}
intro blockNext. eapply bindRev.
{ (** readBlockStartFromBlockEntryAddr **)
  eapply weaken. eapply readBlockStartFromBlockEntryAddr.
  simpl. intros s Hprops. split. apply Hprops.
  destruct Hprops as ((((_ & _ & _ & _ & _ & _ & _ & HBE & _) & _) & _) & _). unfold StateLib.isBE.
  destruct HBE as [bentry HBE]. rewrite HBE. trivial.
}
intro globalIdBlock. eapply bindRev.
{ (** readBlockEndFromBlockEntryAddr **)
  eapply weaken. eapply readBlockEndFromBlockEntryAddr.
  simpl. intros s Hprops. split. apply Hprops.
  destruct Hprops as (((((_ & _ & _ & _ & _ & _ & _ & HBE & _) & _) & _) & _) & _). unfold StateLib.isBE.
  destruct HBE as [bentry HBE]. rewrite HBE. trivial.
}
intro globalEnd. simpl.
destruct (beqAddr blockStartBis blockOrigin && beqAddr blockNext nullAddr)%bool eqn:HnotCutYet.
- (* beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr = true -> block hasn't been cut *)
  assert(HblocksEq: blockStartBis = blockOrigin /\ blockNext = nullAddr).
  {
    apply Bool.andb_true_iff in HnotCutYet. destruct HnotCutYet as [Hstart Hnext].
    rewrite <-DTL.beqAddrTrue in *. intuition.
  }
  destruct HblocksEq as [Hstart Hnext]. subst blockStartBis. subst blockNext.
  eapply bindRev.
  { (** Internal.writeAccessibleRec **)
    eapply weaken. apply writeAccessibleRec.
    simpl. intros s Hprops. split. intuition. split. intuition. split. intuition. split. intuition.
    split. eapply Hprops. split. intuition. split. intuition.
    destruct Hprops as ((((((_ & _ & _ & _ & Hconsist & _ & _ & HBE & HPFlag & HAFlag & Hmapped) & _) &
            HstartOrigin) & _) & Hstart) & Hend).
    destruct HBE as [bentryAddr HlookupEntryAddr].
    exists entryaddr. exists bentryAddr. intuition. unfold checkChild. rewrite HlookupEntryAddr.
    assert(HPDFlag: AccessibleNoPDFlag s) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HBE: isBE entryaddr s) by (unfold isBE; rewrite HlookupEntryAddr; trivial).
    assert(Hsh1: sh1entryAddr entryaddr (CPaddr (entryaddr + sh1offset)) s).
    { apply lookupSh1EntryAddr with bentryAddr. assumption. }
    specialize(HPDFlag entryaddr (CPaddr (entryaddr + sh1offset)) HBE Hsh1 HAFlag).
    unfold sh1entryPDflag in HPDFlag.
    destruct (lookup (CPaddr (entryaddr + sh1offset)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). assumption.
  }
  intro recWriteEnded. simpl.
  destruct (negb recWriteEnded) eqn:HpbWrite.
  + (* recWriteEnded = false *)
    eapply weaken. eapply WP.ret. simpl. intros s Hprops. destruct Hprops as (HPI & HKDI & HVS & Hprops).
    destruct Hprops as [s0 [pdentryBase [statesList [parentsList (HPI0 & HKDI0 & HVS0 & Hprops)]]]].
    destruct Hprops as (Hprops & Hconsist0 & HparentsList & HsIsLast & HlookupBaseBis & _ & HbaseBisIsPart &
          Hconsist1 & HnoDup & Hshared & Hrange & HchildBlockProps & HnoChild & HblockBase & Haccess & HlastProps
          & HisBuilt).
    destruct Hprops as ((((((_ & _ & _ & HP & _ & HPDT & HbaseIsPart & HBE & HPFlag & HAFlag & Hstart & Hend &
          Hmapped) & Horigin) & HstartOrigin) & Hnext) & HstartBis) & HendBis).
    assert(blockStart = globalIdBlock).
    {
      unfold bentryStartAddr in *. destruct (lookup entryaddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-HstartBis in Hstart. assumption.
    }
    subst blockStart.
    assert(blockEnd = globalEnd).
    {
      unfold bentryEndAddr in *. destruct (lookup entryaddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-HendBis in Hend. assumption.
    }
    subst blockEnd.
    split. assumption. split. assumption. split. assumption. split. unfold consistency. unfold consistency2.
    intuition. destruct HPDT as [pdentryBase' HlookupBase].
    assert(HPDT: isPDT pdbasepartition s).
    {
      apply stablePDTIsBuilt with statesList s0 parentsList pdbasepartition globalIdBlock globalEnd flag;
          try(assumption); unfold isPDT. rewrite HlookupBaseBis. trivial. rewrite HlookupBase. trivial.
    }
    unfold isPDT in HPDT.
    destruct (lookup pdbasepartition (memory s) beqAddr) eqn:HlookupBases; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct HblockBase as [blockBase [bentryBase [bentryBases0 HblockBase]]].
    assert(Heq: globalIdBlock = blockOrigin).
    {
      unfold bentryStartAddr in *. destruct (lookup entryaddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite HstartOrigin. assumption.
    }
    subst globalIdBlock. exists s0. exists p. exists blockOrigin. (*exists blockOrigin.
    exists globalEnd.*) exists nullAddr. exists parentsList. exists statesList. exists blockBase.
    exists bentryBase. exists bentryBases0. intuition.
    unfold isPDT. rewrite HlookupBaseBis. trivial.
    unfold scentryNext in Hnext.
    destruct (lookup (CPaddr (entryaddr + scoffset)) (memory s0) beqAddr) eqn:HlookupSce;
        try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s1.
    exists (CPaddr (entryaddr + scoffset)). split. assumption. unfold scentryNext. rewrite HlookupSce.
    assumption.
    assert(Hlookup: exists scentry, lookup (CPaddr (entryaddr + scoffset)) (memory s0) beqAddr
                                    = Some (SCE scentry)).
    {
      unfold scentryOrigin in Horigin. destruct (lookup (CPaddr (entryaddr + scoffset)) (memory s0) beqAddr);
        try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s1. reflexivity.
    }
    destruct Hlookup as [scentry Hlookup]. exists scentry. exists (CPaddr (entryaddr + scoffset)).
    split; assumption.
  + (* recWriteEnded = true *)
    eapply weaken. eapply WP.ret. simpl. intros s Hprops. destruct Hprops as (HPI & HKDI & HVS & Hprops).
    destruct Hprops as [s0 [pdentryBase [statesList [parentsList (HPI0 & HKDI0 & HVS0 & Hprops)]]]].
    destruct Hprops as (Hprops & Hconsist0 & HparentsList & HsIsLast & HlookupBaseBis & _ & HbaseBisIsPart &
          Hconsist1 & HnoDup & Hshared & Hrange & HchildBlockProps & HnoChild & HblockBase & Haccess & HlastProps
          & HisBuilt).
    destruct Hprops as ((((((_ & _ & _ & HP & _ & HPDT & HbaseIsPart & HBE & HPFlag & HAFlag & Hstart & Hend &
          Hmapped) & Horigin) & HstartOrigin) & Hnext) & HstartBis) & HendBis).
    assert(blockStart = globalIdBlock).
    {
      unfold bentryStartAddr in *. destruct (lookup entryaddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-HstartBis in Hstart. assumption.
    }
    subst blockStart.
    assert(blockEnd = globalEnd).
    {
      unfold bentryEndAddr in *. destruct (lookup entryaddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-HendBis in Hend. assumption.
    }
    subst blockEnd.
    split. assumption. split. assumption. split. assumption. split. unfold consistency. unfold consistency2.
    intuition. destruct HPDT as [pdentryBase' HlookupBase].
    assert(HPDT: isPDT pdbasepartition s).
    {
      apply stablePDTIsBuilt with statesList s0 parentsList pdbasepartition globalIdBlock globalEnd flag;
          try(assumption); unfold isPDT. rewrite HlookupBaseBis. trivial. rewrite HlookupBase. trivial.
    }
    unfold isPDT in HPDT.
    destruct (lookup pdbasepartition (memory s) beqAddr) eqn:HlookupBases; try(exfalso; congruence).
    destruct v; try(exfalso; congruence).
    destruct HblockBase as [blockBase [bentryBase [bentryBases0 HblockBase]]].
    assert(Heq: globalIdBlock = blockOrigin).
    {
      unfold bentryStartAddr in *. destruct (lookup entryaddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite HstartOrigin. assumption.
    }
    subst globalIdBlock. exists s0. exists p. exists blockOrigin. (*exists blockOrigin.
    exists globalEnd.*) exists nullAddr. exists parentsList. exists statesList. exists blockBase.
    exists bentryBase. exists bentryBases0. intuition.
    unfold isPDT. rewrite HlookupBaseBis. trivial.
    unfold scentryNext in Hnext.
    destruct (lookup (CPaddr (entryaddr + scoffset)) (memory s0) beqAddr) eqn:HlookupSce;
        try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s1.
    exists (CPaddr (entryaddr + scoffset)). split. assumption. unfold scentryNext. rewrite HlookupSce.
    assumption.
    assert(Hlookup: exists scentry, lookup (CPaddr (entryaddr + scoffset)) (memory s0) beqAddr
                                    = Some (SCE scentry)).
    {
      unfold scentryOrigin in Horigin. destruct (lookup (CPaddr (entryaddr + scoffset)) (memory s0) beqAddr);
        try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s1. reflexivity.
    }
    destruct Hlookup as [scentry Hlookup]. exists scentry. exists (CPaddr (entryaddr + scoffset)).
    split; assumption.
- (* beqAddr blockStart blockOrigin && beqAddr blockNext nullAddr = false -> block has been cut *)
  eapply weaken. eapply WP.ret. simpl. intros s Hprops.
  destruct Hprops as ((((((HPI & HKDI & HVS & HP & Hconsist & (pdentry & HlookupBase) & Hprops2) & Horigin) &
        Hstart) & Hnext) & HentryStartGlob) & HentryEndGlob).
  destruct Hprops2 as (HbaseIsPart & [bentryBase HlookupBlockBase] & Hprops2). intuition.
  exists s. exists pdentry. exists blockOrigin. (*exists blockStart. exists globalEnd.*)
  exists blockNext. exists []. exists []. exists entryaddr. exists bentryBase. exists bentryBase. simpl.
  assert(false = checkChild entryaddr s (CPaddr (entryaddr + sh1offset))).
  {
    unfold checkChild. rewrite HlookupBlockBase.
    assert(HPDFlag: AccessibleNoPDFlag s) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(HBE: isBE entryaddr s) by (unfold isBE; rewrite HlookupBlockBase; trivial).
    assert(Hsh1: sh1entryAddr entryaddr (CPaddr (entryaddr + sh1offset)) s).
    {
      unfold sh1entryAddr. rewrite HlookupBlockBase. reflexivity.
    }
    specialize(HPDFlag entryaddr (CPaddr (entryaddr + sh1offset)) HBE Hsh1 H1). unfold sh1entryPDflag in HPDFlag.
    destruct (lookup (CPaddr (entryaddr + sh1offset)) (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). assumption.
  }
  intuition. unfold isPDT. rewrite HlookupBase. trivial.
  apply accessibleBlockIsAccessibleMapped; assumption.
  unfold scentryNext in Hnext.
  destruct (lookup (CPaddr (entryaddr + scoffset)) (memory s) beqAddr) eqn:HlookupSce;
      try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s0.
  exists (CPaddr (entryaddr + scoffset)). split. assumption. unfold scentryNext. rewrite HlookupSce.
  assumption.
  assert(Hlookup: exists scentry, lookup (CPaddr (entryaddr + scoffset)) (memory s) beqAddr = Some (SCE scentry)).
  {
    unfold scentryOrigin in Horigin. destruct (lookup (CPaddr (entryaddr + scoffset)) (memory s) beqAddr);
      try(exfalso; congruence). destruct v; try(exfalso; congruence). exists s0. reflexivity.
  }
  destruct Hlookup as [scentry Hlookup]. exists scentry. exists (CPaddr (entryaddr + scoffset)).
  split; assumption.
  exists pdbasepartition. exists pdentry. split. reflexivity. split. assumption.
  assert(HparentOfPart: parentOfPartitionIsPartition s)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
  specialize(HparentOfPart pdbasepartition pdentry HlookupBase).
  destruct HparentOfPart as (HparentIsPart & HparentOfRoot & _).
  destruct (beqAddr pdbasepartition constantRootPartM) eqn:HbeqBaseRoot.
  + left. rewrite <-DTL.beqAddrTrue in HbeqBaseRoot. specialize(HparentOfRoot HbeqBaseRoot). assumption.
  + right. apply andb_false_iff in HnotCutYet. intros block HblockMappedParent HboundsBlock.
    destruct HboundsBlock as (HstartBlock & HendBlock). rewrite <-beqAddrFalse in HbeqBaseRoot.
    specialize(HparentIsPart HbeqBaseRoot).
    destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
    destruct HnotCutYet as [HoriginWrong | HnextWrong].
    * rewrite <-beqAddrFalse in HoriginWrong.
      assert(HoriginIsStart: originIsParentBlocksStart s)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(HeqTriv: CPaddr (entryaddr + scoffset) = CPaddr (entryaddr + scoffset)) by reflexivity.
      specialize(HoriginIsStart pdbasepartition pdentry entryaddr (CPaddr (entryaddr + scoffset)) blockOrigin
          HbaseIsPart HlookupBase H4 HeqTriv Horigin). destruct HoriginIsStart as (HoriginIsStart & _).
      specialize(HoriginIsStart HbeqBaseRoot).
      destruct HoriginIsStart as [blockParent (HblockParentMapped & HstartParent & Hincl)].
      assert(HblocksEq: block = blockParent).
      {
        destruct (beqAddr block blockParent) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption).
        exfalso. rewrite <-beqAddrFalse in HbeqBlocks.
        assert(HparentIsPDT: isPDT (parent pdentry) s) by (unfold isPDT; rewrite HlookupParent; trivial).
        assert(HnoDup: noDupUsedPaddrList s) by (unfold consistency in *; unfold consistency2 in *; intuition).
        assert(HwellFormed: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HwellFormed entryaddr blockStart blockEnd H H0 H2). destruct HwellFormed as (HwellFormed & _).
        assert(HstartInEntry: In blockStart (getAllPaddrAux [entryaddr] s)).
        {
          simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup entryaddr (memory s) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. subst blockStart. subst blockEnd.
          apply getAllPaddrBlockIncl; lia.
        }
        assert(HstartInBlock: In blockStart (getAllPaddrAux [block] s)).
        {
          simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup block (memory s) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. subst blockStart. subst blockEnd.
          apply getAllPaddrBlockIncl; lia.
        }
        pose proof (DisjointPaddrInPart (parent pdentry) block blockParent blockStart s HnoDup HparentIsPDT
            HblockMappedParent HblockParentMapped HbeqBlocks HstartInBlock) as Hcontra.
        specialize(Hincl blockStart HstartInEntry). congruence.
      }
      subst block. assert(HstartIsOrigin: blockStart = blockOrigin).
      {
        unfold bentryStartAddr in *. destruct (lookup blockParent (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-HstartParent in HstartBlock. assumption.
      }
      subst blockStart. unfold bentryStartAddr in *.
      destruct (lookup entryaddr (memory s) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
    * rewrite <-beqAddrFalse in HnextWrong.
      assert(HnextThenCut: nextImpliesBlockWasCut s)
          by (unfold consistency in *; unfold consistency1 in *; intuition).
      assert(HeqTriv: CPaddr (entryaddr + scoffset) = CPaddr (entryaddr + scoffset)) by reflexivity.
      specialize(HnextThenCut pdbasepartition pdentry entryaddr (CPaddr (entryaddr + scoffset)) blockNext
          blockEnd HbaseIsPart HlookupBase H4 H2 HeqTriv HnextWrong Hnext HbeqBaseRoot).
      destruct HnextThenCut as [blockParent [endParent (HblockParentMapped & HendParent & Hends & Hincl)]].
      assert(HblocksEq: block = blockParent).
      {
        destruct (beqAddr block blockParent) eqn:HbeqBlocks; try(rewrite DTL.beqAddrTrue; assumption).
        exfalso. rewrite <-beqAddrFalse in HbeqBlocks.
        assert(HparentIsPDT: isPDT (parent pdentry) s) by (unfold isPDT; rewrite HlookupParent; trivial).
        assert(HnoDup: noDupUsedPaddrList s) by (unfold consistency in *; unfold consistency2 in *; intuition).
        assert(HwellFormed: wellFormedBlock s) by (unfold consistency in *; unfold consistency1 in *; intuition).
        specialize(HwellFormed entryaddr blockStart blockEnd H H0 H2). destruct HwellFormed as (HwellFormed & _).
        assert(HstartInEntry: In blockStart (getAllPaddrAux [entryaddr] s)).
        {
          simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup entryaddr (memory s) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. subst blockStart. subst blockEnd.
          apply getAllPaddrBlockIncl; lia.
        }
        assert(HstartInBlock: In blockStart (getAllPaddrAux [block] s)).
        {
          simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
          destruct (lookup block (memory s) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite app_nil_r. subst blockStart. subst blockEnd.
          apply getAllPaddrBlockIncl; lia.
        }
        pose proof (DisjointPaddrInPart (parent pdentry) block blockParent blockStart s HnoDup HparentIsPDT
            HblockMappedParent HblockParentMapped HbeqBlocks HstartInBlock) as Hcontra.
        specialize(Hincl blockStart HstartInEntry). congruence.
      }
      subst block. assert(HendsEq: blockEnd = endParent).
      {
        unfold bentryEndAddr in *. destruct (lookup blockParent (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-HendParent in HendBlock. assumption.
      }
      subst blockEnd. lia.
Qed.

