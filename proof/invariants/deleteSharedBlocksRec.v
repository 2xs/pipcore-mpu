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
              Proof.InternalLemmas (*Proof.Isolation*).
Require Import Hoare Invariants checkBlockCut writeAccessibleToAncestorsIfNotCutRec.
Require Import FunctionalExtensionality List Lia Coq.Logic.ProofIrrelevance Coq.Bool.Bool Coq.Bool.BoolEq.
Import List.ListNotations.

Module WP := WeakestPreconditions.
Module DTL := DependentTypeLemmas.

Lemma deleteSharedBlocksInStructRecAux timeout currentPart kernelStructureStartAddr idPDchildToDelete
(currIndex: index) P:
{{ fun s => P s /\ timeout > currIndex /\ currIndex < kernelStructureEntriesNb
            /\ isKS kernelStructureStartAddr s
            (*consistency props*)
            /\ BlocksRangeFromKernelStartIsBE s
            /\ wellFormedFstShadowIfBlockEntry s
            /\ KernelStructureStartFromBlockEntryAddrIsKS s
            /\ nullAddrExists s
}}
deleteSharedBlocksInStructRecAux timeout currentPart kernelStructureStartAddr idPDchildToDelete currIndex
{{ fun _ s => P s }}.
Proof.
revert currIndex. induction timeout; intro; simpl.
- eapply weaken. apply ret. intros s Hprops. destruct Hprops as (_ & Hcontra). exfalso. lia.
- eapply bindRev.
  { (* MAL.getBlockEntryAddrFromKernelStructureStart *)
    eapply weaken. apply getBlockEntryAddrFromKernelStructureStart. intros s Hprops. simpl. split. apply Hprops.
    intuition.
  }
  intro currBlockEntryAddr. eapply bindRev.
  { (* MAL.readBlockStartFromBlockEntryAddr *)
    eapply weaken. apply readBlockStartFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
    intuition.
  }
  intro blockID. eapply bindRev.
  { (* MAL.readBlockEndFromBlockEntryAddr *)
    eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
    intuition.
  }
  intro endBlock. eapply bindRev.
  { (* MAL.readSh1PDChildFromBlockEntryAddr *)
    eapply weaken. apply readSh1PDChildFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
    intuition. apply isBELookupEq. assumption.
  }
  intro currPDChild. destruct (beqAddr currPDChild idPDchildToDelete) eqn:HbeqCurrToDel.
  + eapply bindRev.
    { (* MAL.writeBlockAccessibleFromBlockEntryAddr *)
      eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr. intros s Hprops. simpl.
      destruct Hprops as ((((Hprops & HcurrAddr & HcurrAddrIsBE) & HstartCurr) & HendCurr) & Hsh1).
      unfold isBE in HcurrAddrIsBE.
      destruct (lookup currBlockEntryAddr (memory s) beqAddr) eqn:HlookupCurr; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists b. split. reflexivity.
      instantiate(1 := fun _ s =>
            exists s0 bentry sh1entry sh1entryaddr,
                s = {|
                      currentPartition := currentPartition s0;
                      memory :=
                        add currBlockEntryAddr
                          (BE (CBlockEntry (read bentry) (write bentry) (exec bentry) (present bentry) true
                              (blockindex bentry) (blockrange bentry)))
                          (memory s0) beqAddr
                    |}
                /\ bentryStartAddr currBlockEntryAddr blockID s
                /\ bentryEndAddr currBlockEntryAddr endBlock s
                /\ isKS kernelStructureStartAddr s
                /\ lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry)
                /\ sh1entryPDchild sh1entryaddr currPDChild s
                /\ sh1entryAddr currBlockEntryAddr sh1entryaddr s
                (* independant properties *)
                /\ S timeout > currIndex
                /\ currIndex < kernelStructureEntriesNb
                /\ currBlockEntryAddr = CPaddr (kernelStructureStartAddr + blkoffset + currIndex)
                (* properties of s0 *)
                /\ lookup currBlockEntryAddr (memory s0) beqAddr = Some (BE bentry)
                /\ P s0
                /\ BlocksRangeFromKernelStartIsBE s0
                /\ wellFormedFstShadowIfBlockEntry s0
                /\ KernelStructureStartFromBlockEntryAddrIsKS s0
                /\ nullAddrExists s0). simpl.
      destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDChild & Hsh1)]]. exists s. exists b.
      exists sh1entry. exists sh1entryaddr.
      set(s' := {|
                  currentPartition := currentPartition s;
                  memory :=
                    add currBlockEntryAddr
                      (BE (CBlockEntry (read b) (write b) (exec b) (present b) true (blockindex b)
                          (blockrange b)))
                      (memory s) beqAddr
                |}). split. reflexivity.
      destruct (beqAddr currBlockEntryAddr sh1entryaddr) eqn:HbeqCurrSh1.
      {
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqCurrSh1. subst sh1entryaddr. unfold sh1entryAddr in Hsh1.
        rewrite HlookupSh1 in Hsh1. congruence.
      }
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold isKS in *. unfold sh1entryPDchild in *.
      unfold sh1entryAddr in *. simpl. rewrite beqAddrTrue. rewrite HbeqCurrSh1. unfold CBlockEntry.
      assert(blockindex b < kernelStructureEntriesNb) by (apply Hidx).
      destruct (Compare_dec.lt_dec (blockindex b) kernelStructureEntriesNb); try(lia). simpl.
      rewrite HlookupCurr in *. intuition.
      2,3: rewrite <-beqAddrFalse in HbeqCurrSh1; rewrite removeDupIdentity; try(apply not_eq_sym; assumption);
            intuition.
      destruct (beqAddr currBlockEntryAddr kernelStructureStartAddr) eqn:HbeqCurrKernStart.
      - simpl. rewrite <-DTL.beqAddrTrue in HbeqCurrKernStart. subst kernelStructureStartAddr.
        rewrite HlookupCurr in *. assumption.
      - rewrite <-beqAddrFalse in HbeqCurrKernStart. rewrite removeDupIdentity; try(apply not_eq_sym); assumption.
    }
    intro. eapply bindRev.
    { (* MAL.writeSh1EntryFromBlockEntryAddr *)
      eapply weaken. apply writeSh1EntryFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops.
      admit.
    }
    intro. eapply bindRev.
    { (* checkBlockCut *)
      eapply weaken. apply checkBlockCut. intros s Hprops. simpl. split. apply Hprops.
      destruct Hprops as [s0 [sh1entry1 [sh1entry0 Hprops]]]. intuition.
      * admit.
      * admit.
    }
    intro isCut. destruct (negb isCut).
    * eapply bindRev.
      { (* Internal.writeAccessibleRec *)
        admit. (*eapply weaken. apply writeAccessibleRec. intros s Hprops. simpl.*)
        (*TODO HERE use writeAccessibleRecAuxLight*)
      }
      intro. eapply bindRev.
      { (* MALInternal.Index.zero *)
        eapply weaken. apply Index.zero. intros s Hprops. simpl. apply Hprops.
      }
      intro zero. destruct (indexEq currIndex zero) eqn:HbeqCurrIdxZero.
      -- eapply weaken. apply ret. intros s Hprops. simpl. admit.
      -- eapply bindRev.
         { (* indexPredM *)
           eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops.
           destruct Hprops as (_ & Hzero). subst zero. unfold indexEq in *.
           apply PeanoNat.Nat.eqb_neq in HbeqCurrIdxZero. unfold CIndex in HbeqCurrIdxZero.
           destruct (Compare_dec.le_dec 0 maxIdx); try(lia). simpl in HbeqCurrIdxZero. lia.
         }
         intro idxpred. eapply weaken. apply IHtimeout. intros s Hprops. simpl. admit.
    * eapply bindRev.
      { (* MALInternal.Index.zero *)
        eapply weaken. apply Index.zero. intros s Hprops. simpl. apply Hprops.
      }
      intro zero. destruct (indexEq currIndex zero) eqn:HbeqCurrIdxZero.
      -- eapply weaken. apply ret. intros s Hprops. simpl. admit.
      -- eapply bindRev.
         { (* indexPredM *)
           eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops.
           destruct Hprops as (_ & Hzero). subst zero. unfold indexEq in *.
           apply PeanoNat.Nat.eqb_neq in HbeqCurrIdxZero. unfold CIndex in HbeqCurrIdxZero.
           destruct (Compare_dec.le_dec 0 maxIdx); try(lia). simpl in HbeqCurrIdxZero. lia.
         }
         intro idxpred. eapply weaken. apply IHtimeout. intros s Hprops. simpl. admit.
  + eapply bindRev.
    { (* MALInternal.Index.zero *)
      eapply weaken. apply Index.zero. intros s Hprops. simpl. apply Hprops.
    }
    intro zero. destruct (indexEq currIndex zero) eqn:HbeqCurrIdxZero.
    * eapply weaken. apply ret. intros s Hprops. simpl. admit.
    * unfold indexEq in HbeqCurrIdxZero. apply PeanoNat.Nat.eqb_neq in HbeqCurrIdxZero. eapply bindRev.
      { (* indexPredM *)
        eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops.
        destruct Hprops as (Hprops & Hzero). subst zero. unfold CIndex in HbeqCurrIdxZero.
        destruct (Compare_dec.le_dec 0 maxIdx); try(lia). simpl in HbeqCurrIdxZero. lia.
      }
      intro idxpred. eapply weaken. apply IHtimeout. intros s Hprops. simpl. admit.
Admitted.

Lemma deleteSharedBlocksRecAux timeout currentPart (currKernelStructureStartAddr: paddr) idPDchildToDelete P:
{{ fun s => P s
            /\ (forall kernList, isListOfKernelsAux kernList currKernelStructureStartAddr s
                  -> timeout > length kernList)
            /\ isKS currKernelStructureStartAddr s
            (*consistency props*)
            /\ BlocksRangeFromKernelStartIsBE s
            /\ wellFormedFstShadowIfBlockEntry s
            /\ KernelStructureStartFromBlockEntryAddrIsKS s
            /\ nullAddrExists s
            /\ NextKSOffsetIsPADDR s
}}
deleteSharedBlocksRecAux timeout currentPart currKernelStructureStartAddr idPDchildToDelete
{{ fun _ s => P s }}.
Proof.
revert currKernelStructureStartAddr. induction timeout; simpl; intro.
- eapply weaken. apply ret. intros s Hprops. simpl. intuition. (*TODO to be changed with the Hoare triple*)
- destruct (beqAddr currKernelStructureStartAddr nullAddr) eqn:HbeqCurrKernNull.
  + eapply weaken. apply ret. intros s Hprops. simpl. intuition. (*TODO to be changed with the Hoare triple*)
  + eapply bindRev.
    { (* MALInternal.getKernelStructureEntriesNb *)
      eapply weaken. apply getKernelStructureEntriesNb. intros s Hprops. simpl. apply Hprops.
    }
    intro entriesnb. eapply bindRev.
    { (* indexPredM *)
      eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops.
      destruct Hprops as (Hprops & Hentries). subst entriesnb. unfold CIndex.
      pose proof KSEntriesNbLessThanMaxIdx.
      destruct (Compare_dec.le_dec kernelStructureEntriesNb maxIdx); try(lia). simpl. apply KSEntriesNbNotZero.
    }
    intro lastindex. eapply bindRev.
    { (* Internal.deleteSharedBlocksInStructRecAux *)
      eapply weaken. apply deleteSharedBlocksInStructRecAux. intros s Hprops. simpl. split. apply Hprops.
      admit.
    }
    intro deleteSucceded. eapply bindRev.
    { (* MAL.readNextFromKernelStructureStart *)
      eapply weaken. apply readNextFromKernelStructureStart. intros s Hprops. simpl. split. apply Hprops.
      admit.
    }
    intro nextStructureAddr. eapply weaken. apply IHtimeout. intros s Hprops. simpl. admit.
Admitted.

Lemma deleteSharedBlocksRec currentPart kernelStructureStartAddr idPDchildToDelete P:
{{ fun s => P s }}
deleteSharedBlocksRec currentPart kernelStructureStartAddr idPDchildToDelete
{{ fun _ s => P s }}.
Proof.
unfold deleteSharedBlocksRec. eapply weaken. apply deleteSharedBlocksRecAux. intros s Hprops. simpl.
admit.
Admitted.
