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
    This file contains the invariant of [findBlock].
    We prove that this PIP service preserves the isolation property *)

Require Import Model.ADT Core.Services.
Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib Proof.DependentTypeLemmas Proof.InternalLemmas.
Require Import Invariants (*getGlobalIdPDCurrentOrChild*) findBlockInKSWithAddr sizeOfBlock eraseBlock.
Require Import Compare_dec Bool.

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
                                  List.In blockInCurrentPartitionAddr (getMappedBlocks currentPart s))
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
eapply bindRev.
{ (* Internal.sizeOfBlock *)
  eapply weaken. apply sizeOfBlock. intros s Hprops. simpl. split. apply Hprops. split. apply Hprops.
  destruct Hprops as (_ & Hres). unfold isBlockInRAM in Hres. unfold isBE.
  destruct (lookup blockInCurrentPartitionAddr (memory s) beqAddr ); try(congruence).
  destruct v; try(congruence). trivial.
}
intro blockSize. eapply bindRev.
{ (* getMinBlockSize *)
  eapply weaken. apply Invariants.getMinBlockSize. intros s Hprops. simpl. destruct Hprops as (Hprops & _).
  apply Hprops.
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
                    /\ isBlockTooSmall = indexLt blockSize minBlockSize). simpl. intuition.
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
                    /\ structLen = Constants.PDStructureTotalLength). simpl. intuition.
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
                    /\ isBlockTooSmall = indexLt blockSize PDStructureTotalLength). simpl. intuition.
}
intro isBlockTooSmall2. destruct isBlockTooSmall2.
{
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
eapply bindRev.
{ (* MAL.readSh1PDChildFromBlockEntryAddr *)
  eapply weaken. apply readSh1PDChildFromBlockEntryAddr. intros s Hprops. simpl. split. apply Hprops. split.
  apply Hprops. destruct Hprops as (_ & _ & _ & _ & _ & _ & Hres & _). destruct Hres as [bentry (Hlookup & _)].
  exists bentry. assumption.
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
eapply bindRev.
{ (* MAL.initPDTable *) (*TODO HERE*)
  (*eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.*) admit.
}
eapply bindRev.
{ (* MAL.writePDParent *)
  (*eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.*) admit.
}
eapply bindRev.
{ (* MAL.writeBlockAccessibleFromBlockEntryAddr *)
  (*eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.*) admit.
}
eapply bindRev.
{ (* MAL.removeBlockFromPhysicalMPU *)
  (*eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.*) admit.
}
eapply bindRev.
{ (* MAL.writeSh1PDFlagFromBlockEntryAddr *)
  (*eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.*) admit.
}
eapply bindRev.
{ (* MAL.readSCOriginFromBlockEntryAddr *)
  (*eapply weaken. apply eraseBlock. intros s Hprops. simpl. apply Hprops.*) admit.
}
Qed.

