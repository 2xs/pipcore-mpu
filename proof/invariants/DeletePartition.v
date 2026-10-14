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

Require Import Model.ADT Model.Lib Model.MAL Model.Monad.
Require Import Core.Services.

Require Import Proof.Isolation Proof.Hoare Proof.Consistency Proof.WeakestPreconditions
Proof.StateLib (*Proof.InternalLemmas*) Proof.InternalLemmas2 Proof.DependentTypeLemmas Proof.InternalLemmas3.

Require Import Invariants findBlockInKSWithAddr eraseBlock checkBlockCut writeAccessibleToAncestorsIfNotCutRec.
Require Import deleteProps initStructure.

Require Import Model.Monad.

From Stdlib Require Import List Bool Lia Logic.ProofIrrelevance .
Import List.ListNotations.

Definition deleteProps s0 s currentPart blockToDelete blockStartAddr:=
  nullAddrExists s
  /\ wellFormedFstShadowIfBlockEntry s
  /\ (*partial PDTIfPDFlag*)
      (forall idPDchild sh1entryaddr part, idPDchild <> blockToDelete
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
  /\ AccessibleNoPDFlag s
  /\ FirstFreeSlotPointerIsBEAndFreeSlot s
  /\ multiplexerIsPDT s
  /\ currentPartitionInPartitionsList s
  /\ wellFormedShadowCutIfBlockEntry s
  /\ BlocksRangeFromKernelStartIsBE s
  /\ KernelStructureStartFromBlockEntryAddrIsKS s
  /\ (*partial sh1InChildLocationIsBE*)
      (forall part block sh1entryaddr sh1entry,
        sh1entry.(PDchild) <> blockStartAddr
        -> In part (getPartitions multiplexer s)
        -> In block (getMappedBlocks part s)
        -> sh1entryaddr = CPaddr (block+sh1offset)
        -> lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry)
        -> sh1entry.(inChildLocation) <> nullAddr
        -> isBE sh1entry.(inChildLocation) s)
  /\ StructurePointerIsKS s
  /\ (*partial NextKSIsKS*)
      (forall addr nextKSaddr nextKS,
        (forall block, In block (filterOptionPaddr (getKSEntries currentPart s))
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s0
          -> ~In nextKS (getAllPaddrAux [block] s))
        -> isKS addr s
        -> nextKSAddr addr nextKSaddr s
        -> nextKSentry nextKSaddr nextKS s
        -> nextKS <> nullAddr
        -> isKS nextKS s)
  /\ NextKSOffsetIsPADDR s
  /\ NoDupInFreeSlotsList s
  /\ freeSlotsListIsFreeSlot s
  /\ DisjointFreeSlotsLists s
  /\ inclFreeSlotsBlockEntries s
  /\ DisjointKSEntries s
  /\ noDupPartitionTree s
  /\ (*partial isParent*)
      (forall partition pdparent,
        partition <> blockStartAddr
        -> In pdparent (getPartitions multiplexer s)
        -> In partition (getChildren pdparent s) -> pdentryParent partition pdparent s)
  /\ isChild s
  /\ noDupKSEntriesList s
  /\ wellFormedBlock s
  /\ (*partial parentOfPartitionIsPartition*)
      (exists wrongParts,
              (forall partition entry,
                lookup partition (memory s) beqAddr = Some (PDT entry)
                -> (~In (parent entry) wrongParts
                    -> partition <> constantRootPartM
                    -> (exists parentEntry, lookup (parent entry) (memory s) beqAddr = Some (PDT parentEntry))
                        /\ In (parent entry) (getPartitions multiplexer s))
                  /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
              /\ (forall oldPart, In oldPart wrongParts
                  -> (forall desc, In desc (getPartitions oldPart s)
                      -> desc <> blockStartAddr
                      -> ~In desc (getPartitions multiplexer s))
              (* exists block, In oldPart (getAllPaddrAux [block] s)
              /\ In block (getMappedBlocks currentPart s)
              /\ sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s *)))
  /\ NbFreeSlotsISNbFreeSlotsInList s
  /\ maxNbPrepareIsMaxNbKernels s
  /\ blockInChildHasAtLeastEquivalentBlockInParent s
  /\ partitionTreeIsTree s
  /\ nextKernelIsValid s
  /\ noDupListOfKerns s
  /\ MPUsizeIsBelowMax s
  /\ originIsParentBlocksStart s
  /\ nextImpliesBlockWasCut s
  /\ blocksAddressesTypes s
  /\ notPDTIfNotPDflag s
  /\ nextKernAddrIsInSameBlock s
  /\ PDflagMeansNoChild s
  /\ nbPrepareIsNbKern s
  /\ pdchildIsPDT s
  /\ childBlockNullIfChildNull s
  /\ accessibleBlocksArePresent s
  /\ sharedBlockIsPresent s
  /\ (*partial sharedBlockNoPDflagNoLocIsKern (modified version)*)
      (forall part block child startaddr,
        child <> blockStartAddr
        -> In part (getPartitions multiplexer s)
        -> In block (getMappedBlocks part s)
        -> sh1entryPDchild (CPaddr (block + sh1offset)) child s
        -> child <> nullAddr
        -> sh1entryPDflag (CPaddr (block + sh1offset)) false s
        -> sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) nullAddr s
        -> bentryStartAddr block startaddr s
        -> In startaddr (getConfigBlocks child s)
            /\ (forall addr child2, In addr (getAllPaddrAux [block] s)
                  -> In child2 (getChildren part s)
                  -> ~In addr (getMappedPaddr child2 s))
            /\ (forall (addr:paddr) endaddr part2, bentryEndAddr block endaddr s
                  -> In part2 (getPartitions multiplexer s)
                  -> startaddr+Constants.kernelStructureTotalLength <= addr
                  -> addr < endaddr
                  -> ~In addr (getConfigPaddr part2 s)))
  /\ partitionNotAutoMapped s
  /\ configAddrNotMappedInChild s
  /\ fullKernelIsInOneBlock s
  /\ (*partial sharedBlocksAdressesAreAllMappedInChild*)
      (forall partition block sh1entryaddr blockChild idchild,
        idchild <> blockStartAddr
        -> In partition (getPartitions multiplexer s)
        -> In block (getMappedBlocks partition s)
        -> sh1entryAddr block sh1entryaddr s
        -> sh1entryPDchild sh1entryaddr idchild s
        -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
        -> idchild <> nullAddr
        -> blockChild <> nullAddr
        -> forall addr, In addr (getAllPaddrAux [block] s) -> In addr (getMappedPaddr idchild s))
  /\ kernInSameBlock s
  /\ blockAndSh1InSameBlock s
  /\ blockAndSceInSameBlock s
  /\ (*partial kernelIsSomePartsConfig s*)
      (forall kernel, isKS kernel s
        -> (forall block, In block (filterOptionPaddr (getKSEntries currentPart s))
              -> sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s0
              -> ~In kernel (getAllPaddrAux [block] s))
        -> exists part pdentry, In part (getPartitions multiplexer s)
            /\ lookup part (memory s) beqAddr = Some (PDT pdentry)
            /\ In kernel (completeListOfKernels (structure pdentry) s))
  /\ PDTisNoConfigInChild s /\ PDTisNoConfigInPart s /\ usedPaddrAreShared s /\ indexIsDistFromKern s
  /\ blockAndNextInSameBlock s
  (*TODO HERE add the latest props*)
  /\ noDupMappedPaddrList s /\ accessibleParentPaddrIsAccessibleIntoChild s /\ sharedBlockPointsToChild s
  /\ adressesRangePreservedIfOriginAndNextOk s /\ childsBlocksPropsInParent s /\ noChildImpliesAddressesNotShared s
  /\ kernelsAreNotAccessible s /\ blockAndNextAreSideBySide s /\ parentBlocksBoundsIfNoNext s
  /\ (*partial childLocMappedInChild*)
      (forall partition block sh1entryaddr blockChild idchild startaddr,
        idchild <> blockStartAddr
        -> In partition (getPartitions multiplexer s)
        -> In block (getMappedBlocks partition s)
        -> sh1entryAddr block sh1entryaddr s
        -> sh1entryPDchild sh1entryaddr idchild s
        -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
        -> idchild <> nullAddr
        -> bentryStartAddr block startaddr s
        -> ~ isKS startaddr s
        -> blockChild <> nullAddr
            /\ In blockChild (getMappedBlocks idchild s) /\ bentryStartAddr blockChild startaddr s)
  /\ (*partial childLocHasSameStart*)
      (forall partition block sh1entryaddr blockChild idchild,
        idchild <> blockStartAddr
        -> In partition (getPartitions multiplexer s)
        -> In block (getMappedBlocks partition s)
        -> sh1entryAddr block sh1entryaddr s
        -> sh1entryPDchild sh1entryaddr idchild s
        -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
        -> idchild <> nullAddr
        -> blockChild <> nullAddr
        -> (forall startaddr, bentryStartAddr block startaddr s -> bentryStartAddr blockChild startaddr s)
              /\ In blockChild (getMappedBlocks idchild s))
  /\ partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s.

Lemma deleteSharedBlocksInStructRecAux n m currentPart (kernel:paddr) blockTDParent blockToDelete (currIdx:index)
(P: state->Prop):
{{ fun s => exists pdentryCurr,
    (exists s0, P s0 /\ deleteProps s0 s currentPart blockTDParent blockToDelete
        /\ (forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s
              -> sh1entryPDchild sh1entryaddr child s0)
        /\ (forall idx, idx <= currIdx
              -> lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory s) beqAddr
                  = lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory s0) beqAddr)
        /\ (forall idx addr, idx > currIdx -> idx < kernelStructureEntriesNb
              -> sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete s0
              -> In addr (getAllPaddrAux [CPaddr (kernel+idx)] s)
              -> lookup addr (memory s) beqAddr = None)
        /\ (exists kernList, isListOfKernels kernList currentPart s
              /\ ((kernList = [] /\ kernel = structure pdentryCurr)
                  \/ (kernList <> []
                      /\ nextKSentry (CPaddr (last kernList (structure pdentryCurr)+nextoffset)) kernel s))
              /\ m > maxNbPrepare - length kernList
              /\ (forall kernBis idx, In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                    -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s)
              /\ (forall kernBis idx addr,
                    In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                    -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete s0
                    -> In addr (getAllPaddrAux [CPaddr (kernBis + idx)] s)
                    -> lookup addr (memory s) beqAddr = None)
              /\ (forall kernBis idx, In kernBis (completeListOfKernels kernel s)
                    -> kernBis <> kernel -> idx <= kernelStructureEntriesNb - 1
                    -> lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s) beqAddr
                        = lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s0) beqAddr)))
    /\ n > currIdx
    /\ currIdx < kernelStructureEntriesNb
    /\ isKS kernel s
    /\ In kernel (completeListOfKernels (structure pdentryCurr) s)
    /\ lookup blockToDelete (memory s) beqAddr = None
    /\ In blockTDParent (getMappedBlocks currentPart s)
    /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s
    /\ bentryStartAddr blockTDParent blockToDelete s
    /\ In blockToDelete (getPartitions multiplexer s)
    /\ (forall blockIdx, blockIdx < kernelStructureEntriesNb
          -> In (CPaddr (kernel+blockIdx)) (filterOptionPaddr (getKSEntries currentPart s)))
    /\ In currentPart (getPartitions multiplexer s)
    /\ lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)
    /\ (forall block startBlock endBlock, In block (getMappedBlocks currentPart s)
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s
          -> bentryStartAddr block startBlock s
          -> bentryEndAddr block endBlock s
          -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
              -> ~In addr (getPartitions multiplexer s)
                  /\ (forall part, In part (getPartitions multiplexer s)
                      -> ~In addr (filterOptionPaddr (getKSEntries part s))
                          /\ ~In addr (getConfigPaddr part s))
                  /\ (forall child, In child (getChildren currentPart s)
                      -> ~In addr (getMappedPaddr child s))
                  /\ (isBE addr s -> addr + scoffset < endBlock)
                  /\ (isKS addr s -> addr + nextoffset < endBlock)
                  /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+sh1offset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+scoffset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ addr <> nullAddr))
    /\ (forall part, In part (getPartitions multiplexer s) -> In blockToDelete (getChildren part s)
          -> part = currentPart)
    /\ (forall idx, idx > currIdx -> idx < kernelStructureEntriesNb
          -> ~sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete s)
    /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
          -> In block (getMappedBlocks part s)
          -> sh1entryPDchild (CPaddr (block+sh1offset)) child s
          -> child <> blockToDelete)
}}
Internal.deleteSharedBlocksInStructRecAux n currentPart kernel blockToDelete currIdx
{{ fun _ s => exists pdentryCurr,
  (forall idx, idx < kernelStructureEntriesNb
    -> ~sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete s)
  /\ isKS kernel s
  /\ In kernel (completeListOfKernels (structure pdentryCurr) s)
  /\ lookup blockToDelete (memory s) beqAddr = None
  /\ In blockTDParent (getMappedBlocks currentPart s)
  /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s
  /\ bentryStartAddr blockTDParent blockToDelete s
  /\ In blockToDelete (getPartitions multiplexer s)
  /\ In currentPart (getPartitions multiplexer s)
  /\ lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)
  /\ (forall block startBlock endBlock, In block (getMappedBlocks currentPart s)
        -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s
        -> bentryStartAddr block startBlock s
        -> bentryEndAddr block endBlock s
        -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
            -> ~In addr (getPartitions multiplexer s)
                /\ (forall part, In part (getPartitions multiplexer s)
                    -> ~In addr (filterOptionPaddr (getKSEntries part s))
                        /\ ~In addr (getConfigPaddr part s))
                /\ (forall child, In child (getChildren currentPart s)
                    -> ~In addr (getMappedPaddr child s))
                /\ (isBE addr s -> addr + scoffset < endBlock)
                /\ (isKS addr s -> addr + nextoffset < endBlock)
                /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+sh1offset)
                      -> In blockB (getAllPaddrBlock startBlock endBlock))
                /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+scoffset)
                      -> In blockB (getAllPaddrBlock startBlock endBlock))
                /\ addr <> nullAddr))
  /\ (forall part, In part (getPartitions multiplexer s) -> In blockToDelete (getChildren part s)
        -> part = currentPart)
  /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
        -> In block (getMappedBlocks part s)
        -> sh1entryPDchild (CPaddr (block+sh1offset)) child s
        -> child <> blockToDelete)
  /\ (exists s0, P s0 /\ deleteProps s0 s currentPart blockTDParent blockToDelete
      /\ (forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s
            -> sh1entryPDchild sh1entryaddr child s0)
      /\ (forall idx addr, idx < kernelStructureEntriesNb
            -> sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete s0
            -> In addr (getAllPaddrAux [CPaddr (kernel+idx)] s)
            -> lookup addr (memory s) beqAddr = None)
      /\ (exists kernList, isListOfKernels kernList currentPart s
            /\ ((kernList = [] /\ kernel = structure pdentryCurr)
                \/ (kernList <> []
                    /\ nextKSentry (CPaddr (last kernList (structure pdentryCurr)+nextoffset)) kernel s))
            /\ m > maxNbPrepare - length kernList
            /\ (forall kernBis idx, In kernBis kernList -> idx < kernelStructureEntriesNb
                  -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s)
            /\ (forall kernBis idx addr,
                  In kernBis (kernList++[kernel]) -> idx < kernelStructureEntriesNb
                  -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete s0
                  -> In addr (getAllPaddrAux [CPaddr (kernBis + idx)] s)
                  -> lookup addr (memory s) beqAddr = None)
            /\ (forall kernBis idx, In kernBis (completeListOfKernels kernel s)
                  -> kernBis <> kernel -> idx <= kernelStructureEntriesNb - 1
                  -> lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s) beqAddr
                      = lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s0) beqAddr)))
}}.
Proof.
revert currIdx. induction n; simpl; intro currIdx.
{
  eapply weaken. apply WP.ret. intros s Hprops. exfalso. destruct Hprops as [_ (_ & Hcontra & _)]. lia.
}
eapply bindRev.
{ (** MAL.getBlockEntryAddrFromKernelStructureStart **)
  eapply weaken. apply getBlockEntryAddrFromKernelStructureStartLight. intros s Hprops. apply Hprops.
}
intro currBlock. eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr **)
  eapply weaken. apply readBlockStartFromBlockEntryAddr. intros s Hprops. split. apply Hprops.
  destruct Hprops as ([pdentryCurr ([s0 Hprops] & _ & HltIdxKernEntriesNb & HkernIsKS & _)] & HcurrBlock).
  cbn in HcurrBlock. assert(Hres: BlocksRangeFromKernelStartIsBE s) by (unfold deleteProps in *; intuition).
  rewrite PeanoNat.Nat.add_0_r in HcurrBlock. subst currBlock. apply Hres; trivial.
}
intro startBlock. eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr **)
  eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. split. apply Hprops.
  destruct Hprops as (_ & Hstart). unfold bentryStartAddr in *. unfold isBE.
  destruct (lookup currBlock (memory s) beqAddr); try(congruence). destruct v; try(congruence). trivial.
}
intro endBlock. eapply bindRev.
{ (** MAL.readSh1PDChildFromBlockEntryAddr **)
  eapply weaken. apply readSh1PDChildFromBlockEntryAddr. intros s Hprops. split. apply Hprops.
  destruct Hprops as ((([pdentryCurr ([s0 Hprops] & _)] & _) & _) & Hend). unfold deleteProps in *. intuition.
  unfold bentryEndAddr in *.
  destruct (lookup currBlock (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
  exists b. reflexivity.
}
intro currPDChild. destruct (beqAddr currPDChild blockToDelete) eqn:HbeqChildBTD.
- rewrite <-beqAddrTrue in HbeqChildBTD. subst currPDChild. eapply bindRev.
  { (** MAL.writeBlockAccessibleFromBlockEntryAddr **)
    eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr. intros s Hprops.
    destruct Hprops as (((([pdentryCurr ([s0 (Hprops & HPDchildImpl)] & HgtNIdx & HltIdxKernEntriesNb & HkernIsKS &
      HkernIsConfig & HlookupBTD & HBTDPMappedCurr & HPDflagBTDP & HstartBTDP & HBTDIsPart & HblocksInCurr &
      HcurrIsPart & HcurrIsPDT & HpropsAddrToRemove)] & HcurrBlock) & Hstart) & Hend) & [_ [sh1entryaddr (_ &
      HPDchild & Hsh1)]]).
    unfold sh1entryAddr in *.
    destruct (lookup currBlock (memory s) beqAddr) eqn:HlookupCurr; try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists b. split; trivial. cbn in HcurrBlock.
    rewrite PeanoNat.Nat.add_0_r in HcurrBlock.
    instantiate(1 := fun _ s => exists s0 sInit bentry0 sh1entryaddr pdentryCurr,
      s = {|
            currentPartition := currentPartition s0;
            memory :=
              add currBlock
                (BE (CBlockEntry (read bentry0) (write bentry0) (exec bentry0) (present bentry0) true
                  (blockindex bentry0) (blockrange bentry0)))
                (memory s0) beqAddr
          |}
      /\ P sInit
      /\ lookup currBlock (memory s0) beqAddr = Some (BE bentry0)
      /\ lookup blockToDelete (memory s0) beqAddr = None
      /\ In blockTDParent (getMappedBlocks currentPart s0)
      /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s0
      /\ bentryStartAddr blockTDParent blockToDelete s0
      /\ In blockToDelete (getPartitions multiplexer s0)
      /\ (forall blockIdx, blockIdx < kernelStructureEntriesNb
            -> In (CPaddr (kernel+blockIdx)) (filterOptionPaddr (getKSEntries currentPart s0)))
      /\ In currentPart (getPartitions multiplexer s0)
      /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentryCurr)
      /\ sh1entryaddr = CPaddr (currBlock + sh1offset)
      /\ deleteProps sInit s0 currentPart blockTDParent blockToDelete /\ S n > currIdx
      /\ currIdx < kernelStructureEntriesNb
      /\ isKS kernel s0
      /\ In kernel (completeListOfKernels (structure pdentryCurr) s0) /\ currBlock = CPaddr (kernel + currIdx)
      /\ bentryStartAddr currBlock startBlock s0
      /\ bentryEndAddr currBlock endBlock s0
      /\ sh1entryPDchild sh1entryaddr blockToDelete s0
      /\ (forall block startBlock endBlock, In block (getMappedBlocks currentPart s0)
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s0
          -> bentryStartAddr block startBlock s0
          -> bentryEndAddr block endBlock s0
          -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
              -> ~In addr (getPartitions multiplexer s0)
                  /\ (forall part, In part (getPartitions multiplexer s0)
                      -> ~In addr (filterOptionPaddr (getKSEntries part s0))
                          /\ ~In addr (getConfigPaddr part s0))
                  /\ (forall child, In child (getChildren currentPart s0)
                      -> ~In addr (getMappedPaddr child s0))
                  /\ (isBE addr s0 -> addr + scoffset < endBlock)
                  /\ (isKS addr s0 -> addr + nextoffset < endBlock)
                  /\ (forall blockB, isBE blockB s0 -> addr = CPaddr (blockB+sh1offset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ (forall blockB, isBE blockB s0 -> addr = CPaddr (blockB+scoffset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ addr <> nullAddr))
      /\ (forall part, In part (getPartitions multiplexer s0) -> In blockToDelete (getChildren part s0)
            -> part = currentPart)
      /\ (forall idx, idx > currIdx -> idx < kernelStructureEntriesNb
            -> ~sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete s0)
      /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s0)
            -> In block (getMappedBlocks part s0)
            -> sh1entryPDchild (CPaddr (block+sh1offset)) child s0
            -> child <> blockToDelete)
      /\ (forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s0
          -> sh1entryPDchild sh1entryaddr child sInit)
      /\ (forall idx, idx <= currIdx
            -> lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory s0) beqAddr
                = lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory sInit) beqAddr)
      /\ (forall idx addr, idx > currIdx -> idx < kernelStructureEntriesNb
            -> sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete sInit
            -> In addr (getAllPaddrAux [CPaddr (kernel+idx)] s0)
            -> lookup addr (memory s0) beqAddr = None)
      /\ (exists kernList, isListOfKernels kernList currentPart s0
            /\ ((kernList = [] /\ kernel = structure pdentryCurr)
                \/ (kernList <> []
                    /\ nextKSentry (CPaddr (last kernList (structure pdentryCurr)+nextoffset)) kernel s0))
            /\ m > maxNbPrepare - length kernList
            /\ (forall kernBis idx, In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                  -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s0)
            /\ (forall kernBis idx addr,
                  In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                  -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete sInit
                  -> In addr (getAllPaddrAux [CPaddr (kernBis + idx)] s0)
                  -> lookup addr (memory s0) beqAddr = None)
            /\ (forall kernBis idx, In kernBis (completeListOfKernels kernel s0)
                  -> kernBis <> kernel -> idx <= kernelStructureEntriesNb - 1
                  -> lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s0) beqAddr
                      = lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory sInit) beqAddr))).
    exists s. exists s0. exists b. exists sh1entryaddr. exists pdentryCurr. intuition.
  }
  intro. eapply bindRev.
  { (** MAL.writeSh1EntryFromBlockEntryAddrLight **)
    eapply weaken. apply writeSh1EntryFromBlockEntryAddrLight. intros s Hprops.
    destruct Hprops as [s0 [sInit [bentry0 [sh1entryaddr [pdentryCurr (Hs & HP & HlookupCurrs0 & HlookupBTDs0 &
      HBTDPMappedCurrs0 & HPDflagBTDPs0 & HstartBTDPs0 & HBTDIsPart & HblocksInCurr & HcurrIsPart & HcurrIsPDT &
      Hsh1s0 & Hpropss0 & HgtNIdx & HltIdxKernEntrieNb & HkernIsKSs0 & HkernIsConfigs0 & HcurrBlock & Hstarts0 &
      Hends0 & HPDchilds0 & HpropsAddrToRemove & HBTDIsUniqueChild & HBTDNotChilds0 & HBDTNotElses0 &
      HPDchildImpls0)]]]]].
    set(newBentry:= CBlockEntry (read bentry0) (write bentry0) (exec bentry0) (present bentry0) true
      (blockindex bentry0) (blockrange bentry0)). fold newBentry in Hs. unfold CBlockEntry in *.
    assert(blockindex bentry0 < kernelStructureEntriesNb) by (apply Hidx).
    destruct (Compare_dec.lt_dec (blockindex bentry0) kernelStructureEntriesNb); try(lia).
    assert(HkernIsKS: isKS kernel s).
    {
      unfold isKS in *. rewrite Hs. simpl. destruct (beqAddr currBlock kernel) eqn:HbeqCurrKern.
      - rewrite <-beqAddrTrue in HbeqCurrKern. subst kernel. rewrite HlookupCurrs0 in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(Hstart: bentryStartAddr currBlock startBlock s).
    {
      unfold bentryStartAddr in *. rewrite HlookupCurrs0 in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue. auto.
    }
    assert(Hend: bentryEndAddr currBlock endBlock s).
    {
      unfold bentryEndAddr in *. rewrite HlookupCurrs0 in *. rewrite Hs. simpl. rewrite IL.beqAddrTrue. auto.
    }
    assert(HPDchild: sh1entryPDchild sh1entryaddr blockToDelete s).
    {
      unfold sh1entryPDchild in *. rewrite Hs. simpl. destruct (beqAddr currBlock sh1entryaddr) eqn:HbeqCurrSh1.
      { rewrite <-beqAddrTrue in HbeqCurrSh1. rewrite HbeqCurrSh1 in *. rewrite HlookupCurrs0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HlookupBTD: lookup blockToDelete (memory s) beqAddr = None).
    {
      rewrite Hs. simpl. destruct (beqAddr currBlock blockToDelete) eqn:HbeqCBBTD.
      { rewrite <-beqAddrTrue in HbeqCBBTD. subst blockToDelete. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(bentryStartAddr blockTDParent blockToDelete s).
    {
      unfold bentryStartAddr in *. rewrite Hs. simpl. destruct (beqAddr currBlock blockTDParent) eqn:HbeqCurrBBTDP.
      - rewrite <-beqAddrTrue in HbeqCurrBBTDP. subst blockTDParent. rewrite HlookupCurrs0 in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    instantiate(1 := fun s => S n > currIdx /\ currIdx < kernelStructureEntriesNb
      /\ currBlock = CPaddr (kernel + currIdx)
      /\ isKS kernel s
      /\ bentryStartAddr currBlock startBlock s
      /\ bentryEndAddr currBlock endBlock s
      /\ lookup blockToDelete (memory s) beqAddr = None
      /\ bentryStartAddr blockTDParent blockToDelete s
      /\ exists s0 sInit bentry0 sh1entryaddr newBentry pdentryCurr,
          P sInit /\ deleteProps sInit s0 currentPart blockTDParent blockToDelete
          /\ s = {|
                   currentPartition := currentPartition s0; memory := add currBlock (BE newBentry) (memory s0) beqAddr
                 |}
          /\ (exists l,
                newBentry = {|
                              read := read bentry0;
                              write := write bentry0;
                              exec := exec bentry0;
                              present := present bentry0;
                              accessible := true;
                              blockindex := blockindex bentry0;
                              blockrange := blockrange bentry0;
                              Hidx := l
                            |})
          /\ lookup currBlock (memory s0) beqAddr = Some (BE bentry0)
          /\ sh1entryaddr = CPaddr (currBlock + sh1offset)
          /\ isKS kernel s0
          /\ In kernel (completeListOfKernels (structure pdentryCurr) s0)
          /\ bentryStartAddr currBlock startBlock s0
          /\ bentryEndAddr currBlock endBlock s0
          /\ sh1entryPDchild sh1entryaddr blockToDelete s0
          /\ sh1entryPDchild sh1entryaddr blockToDelete s
          /\ lookup blockToDelete (memory s0) beqAddr = None
          /\ In blockTDParent (getMappedBlocks currentPart s0)
          /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s0
          /\ bentryStartAddr blockTDParent blockToDelete s0
          /\ In blockToDelete (getPartitions multiplexer s0)
          /\ (forall blockIdx, blockIdx < kernelStructureEntriesNb
                -> In (CPaddr (kernel+blockIdx)) (filterOptionPaddr (getKSEntries currentPart s0)))
          /\ In currentPart (getPartitions multiplexer s0)
          /\ lookup currentPart (memory s0) beqAddr = Some (PDT pdentryCurr)
          /\ (forall block startBlock endBlock, In block (getMappedBlocks currentPart s0)
                -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s0
                -> bentryStartAddr block startBlock s0
                -> bentryEndAddr block endBlock s0
                -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
                    -> ~In addr (getPartitions multiplexer s0)
                        /\ (forall part, In part (getPartitions multiplexer s0)
                            -> ~In addr (filterOptionPaddr (getKSEntries part s0))
                                /\ ~In addr (getConfigPaddr part s0))
                        /\ (forall child, In child (getChildren currentPart s0)
                            -> ~In addr (getMappedPaddr child s0))
                        /\ (isBE addr s0 -> addr + scoffset < endBlock)
                        /\ (isKS addr s0 -> addr + nextoffset < endBlock)
                        /\ (forall blockB, isBE blockB s0 -> addr = CPaddr (blockB+sh1offset)
                              -> In blockB (getAllPaddrBlock startBlock endBlock))
                        /\ (forall blockB, isBE blockB s0 -> addr = CPaddr (blockB+scoffset)
                              -> In blockB (getAllPaddrBlock startBlock endBlock))
                        /\ addr <> nullAddr))
          /\ (forall part, In part (getPartitions multiplexer s0) -> In blockToDelete (getChildren part s0)
                -> part = currentPart)
          /\ (forall idx, idx > currIdx -> idx < kernelStructureEntriesNb
                -> ~sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete s0)
          /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s0)
                -> In block (getMappedBlocks part s0)
                -> sh1entryPDchild (CPaddr (block+sh1offset)) child s0
                -> child <> blockToDelete)
          /\ (forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s0
              -> sh1entryPDchild sh1entryaddr child sInit)
          /\ (forall idx addr, idx > currIdx -> idx < kernelStructureEntriesNb
                -> sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete sInit
                -> In addr (getAllPaddrAux [CPaddr (kernel+idx)] s0)
                -> lookup addr (memory s0) beqAddr = None)
          /\ (forall idx, idx <= currIdx
                -> lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory s0) beqAddr
                    = lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory sInit) beqAddr)
          /\ (exists kernList, isListOfKernels kernList currentPart s0
              /\ ((kernList = [] /\ kernel = structure pdentryCurr)
                  \/ (kernList <> []
                      /\ nextKSentry (CPaddr (last kernList (structure pdentryCurr)+nextoffset)) kernel s0))
              /\ m > maxNbPrepare - length kernList
              /\ (forall kernBis idx, In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                    -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s0)
              /\ (forall kernBis idx addr,
                    In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                    -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete sInit
                    -> In addr (getAllPaddrAux [CPaddr (kernBis + idx)] s0)
                    -> lookup addr (memory s0) beqAddr = None)
              /\ (forall kernBis idx, In kernBis (completeListOfKernels kernel s0)
                    -> kernBis <> kernel -> idx <= kernelStructureEntriesNb - 1
                    -> lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s0) beqAddr
                        = lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory sInit) beqAddr))).
    intuition.
    - exists s0. exists sInit. exists bentry0. exists sh1entryaddr. exists newBentry. exists pdentryCurr. intuition.
      exists (ADT.CBlockEntry_obligation_1 (blockindex bentry0) l). auto.
    - exists newBentry. rewrite Hs at 1. simpl. rewrite IL.beqAddrTrue. split; trivial.
      assert(HblockMinIdxIsKS: KernelStructureStartFromBlockEntryAddrIsKS s0) by (unfold deleteProps in *; intuition).
      assert(HblkIdxCB: bentryBlockIndex currBlock (blockindex bentry0) s0).
      { unfold bentryBlockIndex. rewrite HlookupCurrs0. reflexivity. }
      assert(HCBIsBE: isBE currBlock s0) by (unfold isBE; rewrite HlookupCurrs0; trivial).
      specialize(HblockMinIdxIsKS currBlock (blockindex bentry0) HCBIsBE HblkIdxCB). unfold isKS in *. rewrite Hs.
      simpl. assert(HgebCBIdx: currBlock >= blockindex bentry0).
      {
        destruct (Nat.ltb currBlock (blockindex bentry0)) eqn:HltCBIdx.
        {
          apply PeanoNat.Nat.ltb_lt in HltCBIdx. exfalso. assert(Heq: currBlock - blockindex bentry0 = 0) by lia.
          rewrite Heq in HblockMinIdxIsKS. assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition).
          fold nullAddr in HblockMinIdxIsKS. unfold isPADDR in *.
          destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        apply PeanoNat.Nat.ltb_ge in HltCBIdx. lia.
      }
      destruct (beqAddr currBlock (CPaddr (currBlock - blockindex bentry0))) eqn:HbeqCBIdxCB.
      + simpl. unfold CPaddr in HbeqCBIdxCB. assert(currBlock <= maxAddr) by (apply Hp).
        destruct (Compare_dec.le_dec (currBlock - blockindex bentry0) maxAddr); try(lia).
        rewrite <-beqAddrTrue in HbeqCBIdxCB. apply paddrEqNatEqEquiv in HbeqCBIdxCB. simpl in *.
        assert(HidxIsZero: i (blockindex bentry0) = 0).
        {
          revert HbeqCBIdxCB HgebCBIdx. generalize (i (blockindex bentry0)). intros blkidx HbeqCBIdxCB HgebCBIdx.
          destruct blkidx; trivial. exfalso.
          assert(currBlock - S blkidx < currBlock) by (apply PeanoNat.Nat.sub_lt; lia). lia.
        }
        rewrite HidxIsZero. split; try(lia). unfold zero. apply index_eq_i. cbn. assumption.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
  }
  intro. eapply bindRev.
  { (** MAL.forgetBlock **)
    eapply weaken. apply forgetBlock. intros s Hprops. apply Hprops.
  }
  intro forgetSucc. eapply bindRev.
  { (** Internal.checkBlockCut **)
    eapply weaken. apply checkBlockCut (*may need to change that*). intros s Hprops. simpl.
    destruct Hprops as [s2 ([s1 (Hs2 & HgtNIdx & HltIdxKernEntriesNb & HcurrBlock & HkernCIsKSs1 & HstartCBs1 &
      HendCBs1 & HlookupBTDs1 & HstartBTDPs1 & [s0 [sInit [bentry0 [sh1entryaddr [newBentry [pdentryCurr (HP &
      Hpropss0 & Hs1 & HnewB & HlookupCurrBs0 & Hsh1CB & HkernCIsKSs0 & HkernCIsConfigs0 & HstartCBs0 & HendCBs0 &
      HPDchildCBs0 & HPDchildCBs1 & HlookupBTDs0 & HBTDPMappedCurrs0 & HPDflagBTDPs0 & HstartBTDPs0 & HBTDIsParts0 &
      HblocksInCurr & HcurrIsPart & HlookupCurr & HpropsAddrToRemove & HBTDIsUniqueChild & HBTDNotChilds0 &
      HBDTNotElses0 & HPDchildImpls0 & HnewEmptyAddrs & HremainingLookup & HkernList)]]]]]])] & HcurrEq &
      HremovedAddrs & HlookupsEq & _)].

    assert(HcurrEqss0: currentPartition s = currentPartition s2).
    { rewrite HcurrEq. rewrite Hs2. simpl. rewrite Hs1. reflexivity. }
    assert(Hsh1CBs0: sh1entryAddr currBlock sh1entryaddr s0).
    { unfold sh1entryAddr. rewrite HlookupCurrBs0. assumption. }
    assert(HCBIsBEs0: isBE currBlock s0).
    { unfold isBE. rewrite HlookupCurrBs0. trivial. }
    assert(HPDflagCBs0: sh1entryPDflag sh1entryaddr false s0).
    {
      assert(HPDNoChild: PDflagMeansNoChild s0) by (unfold deleteProps in *; intuition). subst sh1entryaddr.
      specialize(HPDNoChild currBlock HCBIsBEs0). unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
      destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). destruct (PDflag s3); trivial. exfalso. assert(HeqTriv: true = true) by trivial.
      specialize(HPDNoChild HeqTriv). rewrite <-HPDNoChild in *. subst blockToDelete.
      assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
      rewrite HlookupBTDs0 in *. congruence.
    }
    assert(HgetPartsEqs1s0: getPartitions multiplexer s1 = getPartitions multiplexer s0).
    {
      rewrite Hs1. apply getPartitionsEqBEPDflagFalse with bentry0 sh1entryaddr blockTDParent blockToDelete; trivial.
      1-3: unfold deleteProps in *; intuition.
      unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
    }
    destruct HnewB as [l HnewB].
    assert(HgetPartsGenEqs1s0: forall part partBase, In part (getPartitions partBase s1)
      -> In part (getPartitions partBase s0)).
    {
      intros part partBase. rewrite Hs1. apply getPartitionsImplBE with bentry0; trivial; rewrite HnewB; reflexivity.
    }
    assert(HgetKSEqs1s0: forall part, getKSEntries part s1 = getKSEntries part s0).
    {
      intro part. rewrite Hs1. apply IL.getKSEntriesEqBE; trivial.
    }
    assert(HgetMappedBEqs1s0: forall part, getMappedBlocks part s1 = getMappedBlocks part s0).
    {
      intro part. rewrite Hs1. apply IL.getMappedBlocksEqBENoChange with bentry0; trivial. subst newBentry.
      reflexivity.
    }
    assert(HgetMappedPEqs1s0: forall part, isPDT part s0 -> getMappedPaddr part s1 = getMappedPaddr part s0).
    {
      intros part HpartIsPDT. rewrite Hs1.
      apply IL.getMappedPaddrEqBEPresentNoChangeStartNoChangeEndNoChangeEquivalence with bentry0; subst newBentry;
        auto.
    }
    assert(HbeqBTDNull: blockToDelete <> nullAddr).
    {
      intro. subst blockToDelete. assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition).
      unfold isPADDR in *. rewrite HlookupBTDs0 in *. congruence.
    }
    assert(HCBInCurrs0: In currBlock (filterOptionPaddr (getKSEntries currentPart s0))).
    { subst currBlock. apply HblocksInCurr; assumption. }
    assert(HgetAccMappedBEqs1s0: forall part, In part (getPartitions multiplexer s0) -> currentPart <> part
      -> getAccessibleMappedBlocks part s1 = getAccessibleMappedBlocks part s0).
    {
      intros part HpartIsPart HbeqCurrPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getAccessibleMappedBlocks. rewrite HlookupBTDs1.
        rewrite HlookupBTDs0. reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite Hs1. assert(isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        apply IL.getAccessibleMappedBlocksEqBENotInPart; trivial.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold deleteProps in *; intuition).
        specialize(Hdisjoint currentPart part HcurrIsPart HpartIsPart HbeqCurrPart).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        specialize(Hdisjoint currBlock HCBInCurrs0). assumption.
    }
    assert(HgetAccMappedBEqCurrs1s0: accessible bentry0 = true
      -> getAccessibleMappedBlocks currentPart s1 = getAccessibleMappedBlocks currentPart s0).
    {
      intro Haccess. rewrite Hs1.
      apply IL.getAccessibleMappedBlocksEqBEAccessiblePresentNoChange with bentry0; trivial; subst newBentry;
        auto.
    }
    assert(HPflagCBs0: bentryPFlag currBlock true s0).
    {
      assert(Hres: sharedBlockIsPresent s0) by (unfold deleteProps in *; intuition). unfold sharedBlockIsPresent in *.
      subst sh1entryaddr. apply Hres with currentPart blockToDelete; trivial.
    }
    assert(HgetAccMappedBImplCurrs1s0: accessible bentry0 = false
      -> forall block, In block (getAccessibleMappedBlocks currentPart s1)
          <-> In block (currBlock::getAccessibleMappedBlocks currentPart s0)).
    {
      intros Haccess block. rewrite Hs1.
      apply IL.getAccessibleMappedBlocksEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence with bentry0; trivial.
      1-4: rewrite HnewB; auto.
      - unfold bentryPFlag in *. rewrite HlookupCurrBs0 in *. auto.
      - rewrite Haccess. simpl. intro; congruence.
      - apply IL.noDupKSMappedImpl; unfold deleteProps in *; intuition.
    }
    assert(HgetAccMappedPEqs1s0: forall part, In part (getPartitions multiplexer s0) -> currentPart <> part
      -> getAccessibleMappedPaddr part s1 = getAccessibleMappedPaddr part s0).
    {
      intros part HpartIsPart HbeqCurrPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getAccessibleMappedPaddr.
        unfold getAccessibleMappedBlocks. rewrite HlookupBTDs1. rewrite HlookupBTDs0. reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite Hs1. assert(isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        apply IL.getAccessibleMappedPaddrEqBENotInPart; trivial.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold deleteProps in *; intuition).
        specialize(Hdisjoint currentPart part HcurrIsPart HpartIsPart HbeqCurrPart).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        specialize(Hdisjoint currBlock HCBInCurrs0). assumption.
    }
    assert(HcurrIsPDT: isPDT currentPart s0) by (unfold isPDT; rewrite HlookupCurr; trivial).
    assert(HgetAccMappedPEqCurrs1s0: accessible bentry0 = true
      -> getAccessibleMappedPaddr currentPart s1 = getAccessibleMappedPaddr currentPart s0).
    {
      intro Haccess. rewrite Hs1.
      apply IL.getAccessibleMappedPaddrEqBEPresentAccessibleNoChange with bentry0; trivial; subst newBentry;
        auto.
    }
    assert(HgetAccMappedPImplCurrs1s0: accessible bentry0 = false
      -> forall addr, In addr (getAccessibleMappedPaddr currentPart s1)
          <-> In addr (getAllPaddrBlock startBlock endBlock ++ getAccessibleMappedPaddr currentPart s0)).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupCurrBs0 in *. rewrite HstartCBs0.
      rewrite HendCBs0. intros Haccess addr. rewrite Hs1.
      apply IL.getAccessibleMappedPaddrEqBEPresentTrueNoChangeAccessibleTrueChangeEquivalence; trivial.
      1-6: rewrite HnewB; auto.
      - unfold bentryPFlag in *. rewrite HlookupCurrBs0 in *. auto.
      - rewrite Haccess. simpl. intro; congruence.
      - apply IL.noDupKSMappedImpl; unfold deleteProps in *; intuition.
    }
    assert(HgetConfigEqs1s0: forall part, isPDT part s0 -> getConfigPaddr part s1 = getConfigPaddr part s0).
    {
      intros part HpartIsPDT. rewrite Hs1. apply IL.getConfigPaddrEqBE; trivial.
    }
    assert(HbeqCBNull: currBlock <> nullAddr).
    {
      intro Hcontra. rewrite Hcontra in *. assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition).
      unfold isPADDR in *. rewrite HlookupCurrBs0 in *. congruence.
    }
    assert(HcurrBNotFrees0: forall part, In part (getPartitions multiplexer s0)
      -> ~In currBlock (filterOptionPaddr (getFreeSlotsList part s0))).
    {
      intros part HpartIsPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getFreeSlotsList. rewrite HlookupBTDs0. simpl. auto.
      - rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        assert(HwellFree: getFreeSlotsList part s0 = getFreeSlotsList part s0
          /\ wellFormedFreeSlotsList (getFreeSlotsList part s0) <> False).
        {
          split; trivial. assert(Hres: NoDupInFreeSlotsList s0) by (unfold deleteProps in *; intuition).
          unfold isPDT in *. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
          destruct v; try(exfalso; congruence). specialize(Hres part HpartIsPart).
          destruct Hres as [optFree (HoptFree & Hres & _)]. subst optFree. assumption.
        }
        assert(HfreeAreFree: freeSlotsListIsFreeSlot s0) by (unfold deleteProps in *; intuition). intro Hcontra.
        assert(HCBIsFree: filterOptionPaddr (getFreeSlotsList part s0) = filterOptionPaddr (getFreeSlotsList part s0)
          /\ In currBlock (filterOptionPaddr (getFreeSlotsList part s0))) by auto.
        specialize(HfreeAreFree part currBlock (getFreeSlotsList part s0) (filterOptionPaddr
          (getFreeSlotsList part s0)) HpartIsPDT HpartIsPart HwellFree HCBIsFree HbeqCBNull). unfold isFreeSlot in *.
        unfold bentryPFlag in *. rewrite HlookupCurrBs0 in *. rewrite <-HPflagCBs0 in *.
        destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (lookup (CPaddr (currBlock+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). destruct HfreeAreFree as (_ & _ & _ & _ & HcontraB & _). congruence.
    }
    assert(HgetFreeEqs1s0: forall part, In part (getPartitions multiplexer s0)
      -> getFreeSlotsList part s1 = getFreeSlotsList part s0).
    {
      intros part HpartIsPart. rewrite Hs1. unfold getFreeSlotsList in *. specialize(HcurrBNotFrees0 part).
      simpl lookup. destruct (beqAddr currBlock part) eqn:HbeqCurrBPart.
      - rewrite <-beqAddrTrue in HbeqCurrBPart. subst part. rewrite HlookupCurrBs0. reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        assert(HfreeProps: NoDupInFreeSlotsList s0) by (unfold deleteProps in *; intuition).
        destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
        specialize(HfreeProps part HpartIsPart).
        destruct HfreeProps as [optFree (HoptFree & HwellFree & HnoDupFree)]. subst optFree.
        assert(HpartIsPDT: isPDT part s0) by (unfold isPDT; rewrite HlookupPart; trivial).
        specialize(HcurrBNotFrees0 HpartIsPart). unfold getFreeSlotsList in *. rewrite HlookupPart in *.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial.
        apply IL.getFreeSlotsListRecEqBE; trivial. intro Hcontra. rewrite <-Hcontra in *. contradict HcurrBNotFrees0.
        assert(HeqTriv: getFreeSlotsList part s0 = getFreeSlotsList part s0) by trivial. rewrite <-beqAddrFalse in *.
        assert(HfirstIsFree: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold deleteProps in *; intuition).
        assert(HnbFree: pdentryNbFreeSlots part (nbfreeslots p) s0).
        { unfold pdentryNbFreeSlots. rewrite HlookupPart. reflexivity. }
        assert(Hlen: length (getFreeSlotsList part s0) = nbfreeslots p).
        {
          assert(Hres: NbFreeSlotsISNbFreeSlotsInList s0) by (unfold deleteProps in *; intuition).
          specialize(Hres part (nbfreeslots p) HpartIsPart HnbFree).
          destruct Hres as [optFree (Heq & _ & Hres)]. subst optFree. auto.
        }
        pose proof (firstFreeSlotPointerIsFirstFreeLight part s0 p (getFreeSlotsList part s0) (nbfreeslots p)
          HeqTriv HlookupPart HpartIsPart HbeqFirstNull Hlen HnbFree HfirstIsFree) as Hres.
        destruct Hres as [remainsSlotsList [_ [_ (Hres & _)]]]. unfold getFreeSlotsList in *.
        rewrite HlookupPart in *. rewrite beqAddrFalse in *. rewrite HbeqFirstNull in *. rewrite Hres. simpl. auto.
    }
    assert(HgetChildrenEqs1s0: forall part, isPDT part s0 -> getChildren part s1 = getChildren part s0).
    {
      intros part HpartIsPart. rewrite Hs1. apply IL.getChildrenEqBENoStartNoPresentChange with bentry0; trivial;
        rewrite HnewB; auto.
    }
    assert(HgetAllPaddrAuxEqs1s0: forall block, getAllPaddrAux [block] s1 = getAllPaddrAux [block] s0).
    {
      intro block. rewrite Hs1. simpl. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
      - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB. reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(Hnulls1: nullAddrExists s1).
    { (* BEGIN nullAddr s1 *)
      unfold nullAddrExists. assert(Hcons0: isPADDR nullAddr s0) by (unfold deleteProps in *; intuition).
      unfold isPADDR in *. rewrite Hs1. simpl. destruct (beqAddr currBlock nullAddr) eqn:HbeqCurrBNull.
      {
        rewrite <-beqAddrTrue in HbeqCurrBNull. rewrite HbeqCurrBNull in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END nullAddrExists *)
    }
    assert(HCBInCurrs1: In currBlock (filterOptionPaddr (getKSEntries currentPart s1))).
    { rewrite HgetKSEqs1s0. assumption. }
    assert(Hsh1CurrIsSHEs0: wellFormedFstShadowIfBlockEntry s0) by (unfold deleteProps in *; intuition).
    specialize(Hsh1CurrIsSHEs0 currBlock HCBIsBEs0).
    assert(HlookupSh1Eqs1s0: lookup (CPaddr (currBlock + sh1offset)) (memory s1) beqAddr
      = lookup (CPaddr (currBlock + sh1offset)) (memory s0) beqAddr).
    {
      unfold isSHE in *. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (currBlock+sh1offset))) eqn:HbeqCBSh1.
      {
        rewrite <-beqAddrTrue in HbeqCBSh1. rewrite <-HbeqCBSh1 in *. rewrite HlookupCurrBs0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HgetPartsEqs2s1: getPartitions multiplexer s2 = getPartitions multiplexer s1).
    {
      subst sh1entryaddr. unfold sh1entryPDflag in *. rewrite <-HlookupSh1Eqs1s0 in *.
      destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s1) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite Hs2.
      apply getPartitionsEqSHEPDflagNoChange with s3; trivial.
    }
    assert(HgetPartsGenEqs2s1: forall part, getPartitions part s2 = getPartitions part s1).
    {
      intro part. subst sh1entryaddr. unfold sh1entryPDflag in *. rewrite <-HlookupSh1Eqs1s0 in *.
      destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s1) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite Hs2.
      apply getPartitionsEqSHEPDflagNoChange with s3; trivial.
    }
    unfold isSHE in *. rewrite <-HlookupSh1Eqs1s0 in *.
    assert(HgetKSEqs2s1: forall part, isPDT part s1 -> getKSEntries part s2 = getKSEntries part s1).
    {
      intros part HpartIsPDT. unfold isPDT in *. rewrite Hs2.
      destruct (lookup part (memory s1) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      apply IL.getKSEntriesEqSHE with p; trivial.
    }
    assert(HgetMappedBEqs2s1: forall part, isPDT part s1 -> getMappedBlocks part s2 = getMappedBlocks part s1).
    {
      intros part HpartIsPDT. rewrite Hs2. apply IL.getMappedBlocksEqSHE; trivial.
    }
    assert(HgetMappedPEqs2s1: forall part, isPDT part s1 -> getMappedPaddr part s2 = getMappedPaddr part s1).
    {
      intros part HpartIsPDT. rewrite Hs2. apply IL.getMappedPaddrEqSHE; trivial.
    }
    assert(HgetAccMappedBEqs2s1: forall part, isPDT part s1
      -> getAccessibleMappedBlocks part s2 = getAccessibleMappedBlocks part s1).
    {
      intros part HpartIsPDT. rewrite Hs2. apply IL.getAccessibleMappedBlocksEqSHE; trivial.
    }
    assert(HgetAccMappedPEqs2s1: forall part, isPDT part s1
      -> getAccessibleMappedPaddr part s2 = getAccessibleMappedPaddr part s1).
    {
      intros part HpartIsPDT. rewrite Hs2. apply IL.getAccessibleMappedPaddrEqSHE; trivial.
    }
    assert(HgetChildrenEqs2s1: forall part, isPDT part s1 -> getChildren part s2 = getChildren part s1).
    {
      subst sh1entryaddr. unfold sh1entryPDflag in *. rewrite <-HlookupSh1Eqs1s0 in *.
      destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s1) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      intros part HpartIsPDT. rewrite Hs2. apply IL.getChildrenEqSHE with s3; trivial.
    }
    assert(HfirstIsFrees1: FirstFreeSlotPointerIsBEAndFreeSlot s1).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s1 *)
      assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold deleteProps in *; intuition).
      intros part pdentry HlookupPart HpartIsPart HbeqFirstNull. rewrite HgetPartsEqs1s0 in *.
      rewrite Hs1 in HlookupPart. simpl in *.
      destruct (beqAddr currBlock part) eqn:HbeqCurrBPart; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; auto. specialize(Hcons0 part pdentry HlookupPart HpartIsPart HbeqFirstNull).
      destruct Hcons0 as (HfirstIsBE & HfirstIsFree). unfold isBE in *. unfold isFreeSlot in *. rewrite Hs1 at 1.
      rewrite Hs1 at 1. simpl. destruct (beqAddr currBlock (firstfreeslot pdentry)) eqn:HbeqCurrBFirst.
      {
        exfalso. rewrite <-beqAddrTrue in HbeqCurrBFirst. rewrite <-HbeqCurrBFirst in *. rewrite <-Hsh1CB in *.
        rewrite HlookupCurrBs0 in *. unfold sh1entryPDchild in *.
        destruct (lookup sh1entryaddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
        rewrite <-HPDchildCBs0 in *.
        destruct (lookup (CPaddr (currBlock+scoffset)) (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). destruct HfirstIsFree as (_ & _ & _ & _ & _ & _ & Hcontra & _).
        rewrite Hcontra in *. unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupBTDs1 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. split; trivial.
      destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite Hs1. simpl. destruct (beqAddr currBlock (CPaddr (firstfreeslot pdentry + sh1offset))) eqn:HbeqCBSh1.
      {
        rewrite <-beqAddrTrue in HbeqCBSh1. rewrite <-HbeqCBSh1 in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence).
      destruct (beqAddr currBlock (CPaddr (firstfreeslot pdentry+scoffset))) eqn:HbeqCBSce.
      {
        rewrite <-beqAddrTrue in HbeqCBSce. rewrite <-HbeqCBSce in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }
    assert(HgetFreeEqs2s1: forall part, In part (getPartitions multiplexer s1)
      -> getFreeSlotsList part s2 = getFreeSlotsList part s1).
    {
      intros part HpartIsPart. rewrite Hs2. unfold getFreeSlotsList. simpl lookup.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part.
      - rewrite <-beqAddrTrue in HbeqSh1Part. subst part. unfold isSHE in *.
        destruct (lookup (CPaddr (currBlock + sh1offset)) (memory s1) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        destruct (lookup part (memory s1) beqAddr) eqn:HlookupPart; trivial. destruct v; trivial.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstNull; trivial. unfold isSHE in *.
        apply IL.getFreeSlotsListRecEqSHE; trivial.
        2,3: unfold isBE; unfold isPADDR; destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s1) beqAddr);
          try(exfalso; congruence); destruct v; try(exfalso; congruence); auto.
        rewrite <-beqAddrFalse in *. specialize(HfirstIsFrees1 part p HlookupPart HpartIsPart HbeqFirstNull).
        destruct HfirstIsFrees1 as (HfirstIsBE & _). unfold isBE in *. intro Hcontra. rewrite <-Hcontra in *.
        destruct (lookup (firstfreeslot p) (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    assert(HgetConfigEqs2s1: forall part, isPDT part s1 -> getConfigPaddr part s2 = getConfigPaddr part s1).
    {
      intros part HpartIsPDT. rewrite Hs2. apply IL.getConfigPaddrEqSHE; trivial.
    }
    assert(Hwell: wellFormedBlock s0) by (unfold deleteProps in *; intuition).
    specialize(Hwell currBlock startBlock endBlock HPflagCBs0 HstartCBs0 HendCBs0).
    destruct Hwell as (HltStartEndCB & HlebMinSizeCB).
    assert(HpropsAddrToRemoveCopy: forall block startBlock endBlock, In block (getMappedBlocks currentPart s0)
      -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s0
      -> bentryStartAddr block startBlock s0
      -> bentryEndAddr block endBlock s0
      -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
          -> ~In addr (getPartitions multiplexer s0)
              /\ (forall part, In part (getPartitions multiplexer s0)
                  -> ~In addr (filterOptionPaddr (getKSEntries part s0))
                      /\ ~In addr (getConfigPaddr part s0))
              /\ (forall child, In child (getChildren currentPart s0)
                  -> ~In addr (getMappedPaddr child s0))
              /\ (isBE addr s0 -> addr + scoffset < endBlock)
              /\ (isKS addr s0 -> addr + nextoffset < endBlock)
              /\ (forall blockB, isBE blockB s0 -> addr = CPaddr (blockB + sh1offset)
                    -> In blockB (getAllPaddrBlock startBlock endBlock))
              /\ (forall blockB, isBE blockB s0 -> addr = CPaddr (blockB + scoffset)
                    -> In blockB (getAllPaddrBlock startBlock endBlock))
              /\ addr <> nullAddr)) by assumption.
    assert(HCBMapped: In currBlock (getMappedBlocks currentPart s0)).
    {
      unfold getMappedBlocks. unfold bentryPFlag in *. rewrite HlookupCurrBs0 in *.
      apply IL.presentIsInFilterPresent with bentry0; auto.
    }
    rewrite Hsh1CB in HPDchildCBs0.
    specialize(HpropsAddrToRemoveCopy currBlock startBlock endBlock HCBMapped HPDchildCBs0 HstartCBs0 HendCBs0).
    assert(HgetPartsEqs2s0: getPartitions multiplexer s2 = getPartitions multiplexer s0).
    { rewrite <-HgetPartsEqs1s0. assumption. }
    assert(Hnulls2: isPADDR nullAddr s2).
    {
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) nullAddr) eqn:HbeqSh1Null.
      {
        rewrite <-beqAddrTrue in HbeqSh1Null. rewrite HbeqSh1Null in *.
        destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(Hstructs2: StructurePointerIsKS s2).
    {
      assert(Hcons0: StructurePointerIsKS s0) by (unfold deleteProps in *; intuition).
      intros part pdentry HpartIsPart HlookupPart HbeqStructNull. rewrite HgetPartsEqs2s0 in *.
      rewrite Hs2 in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart. simpl in *.
      destruct (beqAddr currBlock part) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part pdentry HpartIsPart HlookupPart HbeqStructNull). unfold isKS in *. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (structure pdentry)) eqn:HbeqSh1Struct.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Struct. rewrite HbeqSh1Struct in *.
        destruct (lookup (structure pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (structure pdentry)) eqn:HbeqCBStruct.
      - rewrite <-beqAddrTrue in HbeqCBStruct. rewrite <-HbeqCBStruct in *. rewrite HlookupCurrBs0 in *.
        rewrite HnewB. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HcomplKernLEqs2s0: forall kern, completeListOfKernels kern s2 = completeListOfKernels kern s0).
    {
      intro. rewrite Hs2. rewrite completeListOfKernelsEqSHE; trivial. rewrite Hs1.
      apply completeListOfKernelsEqBE with bentry0; trivial. rewrite HnewB. reflexivity.
    }
    assert(HnextPropss2: nextKernelIsValid s2).
    {
      assert(Hcons0: nextKernelIsValid s0) by (unfold deleteProps in *; intuition).
      intros part pdentry kern HpartIsPart HlookupPart HkernIsConfig HkernIsKS. rewrite HgetPartsEqs2s0 in *.
      rewrite Hs2 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart.
      simpl in HlookupPart. destruct (beqAddr currBlock part) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite HcomplKernLEqs2s0 in *.
      assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS in *. rewrite Hs2 in HkernIsKS. simpl in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HkernIsKS. simpl in *.
        destruct (beqAddr currBlock kern) eqn:HbeqCBKern.
        - rewrite <-beqAddrTrue in HbeqCBKern. subst kern. rewrite HlookupCurrBs0. subst newBentry. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 part pdentry kern HpartIsPart HlookupPart HkernIsConfig HkernIsKSs0).
      destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNext & HnextProps)]).
      split; trivial. exists nextAddr. split.
      - intro Hp. specialize(HlookupNext Hp). rewrite Hs2. simpl.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) {| p := kern + nextoffset; Hp := Hp |}) eqn:HbeqSh1Next.
        {
          rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *.
          rewrite HlookupNext in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock {| p := kern + nextoffset; Hp := Hp |}) eqn:HbeqCBNext.
        { rewrite <-beqAddrTrue in HbeqCBNext. exfalso; congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      - destruct HnextProps as [(HnextIsKS & HnextIsConfig) | HnextIsNull]; auto. left. split; trivial.
        unfold isKS in *. rewrite Hs2. simpl.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) nextAddr) eqn:HbeqSh1Next.
        {
          rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *.
          destruct (lookup nextAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock nextAddr) eqn:HbeqCBNext.
        + rewrite <-beqAddrTrue in HbeqCBNext. rewrite HbeqCBNext in *. rewrite HlookupCurrBs0 in *.
          rewrite HnewB. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HmaxPrepIsMaxLen: maxNbPrepareIsMaxNbKernels s2).
    {
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by (unfold deleteProps in *; intuition).
      intros part kernList HpartIsPart HkernListB. rewrite HgetPartsEqs2s0 in *. rewrite Hs2 in HkernListB.
      apply IL.isListOfKernelsEqSHE in HkernListB. rewrite Hs1 in HkernListB.
      apply IL.isListOfKernelsEqBE in HkernListB. specialize(Hcons0 part kernList HpartIsPart HkernListB).
      assumption.
    }
    assert(HblkidxIsBEs2: BlocksRangeFromKernelStartIsBE s2).
    {
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by (unfold deleteProps in *; intuition).
      intros kern idx HkernIsKS HltIdxKSNb. assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS in *. rewrite Hs2 in HkernIsKS. simpl in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HkernIsKS. simpl in *.
        destruct (beqAddr currBlock kern) eqn:HbeqCBKern.
        - rewrite <-beqAddrTrue in HbeqCBKern. subst kern. rewrite HlookupCurrBs0. subst newBentry. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 kern idx HkernIsKSs0 HltIdxKSNb). unfold isBE in *. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (kern + idx))) eqn:HbeqSh1Block.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Block. rewrite HbeqSh1Block in *.
        destruct (lookup (CPaddr (kern + idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (kern + idx))) eqn:HbeqBlocks; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HfirstIsFrees2: FirstFreeSlotPointerIsBEAndFreeSlot s2).
    {
      intros part pdentry HlookupPart HpartIsPart HbeqFirstNull. rewrite HgetPartsEqs2s1 in *.
      rewrite Hs2 in HlookupPart. simpl in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(HfirstIsFrees1 part pdentry HlookupPart HpartIsPart HbeqFirstNull).
      destruct HfirstIsFrees1 as (HfirstIsBE & HfirstIsFree). unfold isBE in *. unfold isFreeSlot in *. rewrite Hs2.
      simpl. destruct (beqAddr (CPaddr (currBlock + sh1offset)) (firstfreeslot pdentry)) eqn:HbeqSh1First.
      {
        rewrite <-beqAddrTrue in HbeqSh1First. rewrite HbeqSh1First in *. exfalso.
        destruct (lookup (firstfreeslot pdentry) (memory s1) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. split; trivial.
      destruct (lookup (firstfreeslot pdentry) (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (firstfreeslot pdentry + scoffset))) eqn:HbeqSh1Sce.
      {
        exfalso. rewrite <-beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *.
        destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence).
        destruct (lookup (CPaddr (firstfreeslot pdentry + scoffset)) (memory s1) beqAddr); try(congruence).
        destruct v; congruence.
      }
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (firstfreeslot pdentry + sh1offset))) eqn:HbeqSh1s.
      - rewrite <-beqAddrTrue in HbeqSh1s. rewrite <-HbeqSh1s in *.
        destruct (lookup (CPaddr (currBlock + sh1offset)) (memory s1) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        destruct (lookup (CPaddr (firstfreeslot pdentry + scoffset)) (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence). intuition.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite removeDupIdentity; auto.
    }
    assert(HwellSh1s2: wellFormedFstShadowIfBlockEntry s2).
    {
      assert(Hcons0: wellFormedFstShadowIfBlockEntry s0) by (unfold deleteProps in *; intuition).
      intros block HblockIsBE. unfold isBE in *. rewrite Hs2 in HblockIsBE. simpl in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE. rewrite Hs1 in HblockIsBE. simpl in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 block HblockIsBEs0). unfold isSHE in *. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s; trivial.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (block + sh1offset))) eqn:HbeqCBSh1.
      {
        rewrite <-beqAddrTrue in HbeqCBSh1. rewrite <-HbeqCBSh1 in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HnoDupTrees2: noDupPartitionTree s2).
    { unfold noDupPartitionTree. rewrite HgetPartsEqs2s0. unfold deleteProps in *; intuition. }
    assert(HBEsIntact: forall block, isBE block s2 -> isBE block s0).
    {
      intros block HblockIsBEs2. unfold isBE in *. rewrite Hs2 in HblockIsBEs2. simpl in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBEs2; auto. rewrite Hs1 in HblockIsBEs2.
      simpl in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
      - rewrite <-beqAddrTrue in HbeqBlocks. subst block. assumption.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in HblockIsBEs2; auto.
    }
    assert(HlookupBTDs2: lookup blockToDelete (memory s2) beqAddr = None).
    {
      rewrite Hs2. simpl. destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockToDelete) eqn:HbeqSh1BTD.
      {
        rewrite <-beqAddrTrue in HbeqSh1BTD. rewrite HbeqSh1BTD in *. rewrite HlookupBTDs1 in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HpropsAddrToRemoveSpecs2: forall addr, In addr (getAllPaddrBlock startBlock endBlock)
      -> ~In addr (getPartitions multiplexer s2)
          /\ (forall part, In part (getPartitions multiplexer s2)
            -> ~In addr (filterOptionPaddr (getKSEntries part s2)) /\ ~ In addr (getConfigPaddr part s2))
          /\ (forall child, In child (getChildren currentPart s2)
              -> ~In addr (getMappedPaddr child s2))
          /\ (isBE addr s2 -> addr + scoffset < endBlock)
          /\ (isKS addr s2 -> addr + nextoffset < endBlock)
          /\ (forall blockB, isBE blockB s2 -> addr = CPaddr (blockB + sh1offset)
                -> In blockB (getAllPaddrBlock startBlock endBlock))
          /\ (forall blockB, isBE blockB s2 -> addr = CPaddr (blockB + scoffset)
                -> In blockB (getAllPaddrBlock startBlock endBlock))
          /\ addr <> nullAddr).
    {
      intros addr HaddrInRange. specialize(HpropsAddrToRemoveCopy addr HaddrInRange).
      destruct HpropsAddrToRemoveCopy as (HaddrNotPart & HaddrNotConfig & HaddrNotInChildren & HltSceEnd & HltNextEnd
        & Hsh1InRange & HsceInRange & HbeqAddrNull).
      rewrite HgetPartsEqs2s0. split; trivial.
      split; only 2: (split; only 2: split; try(split; try(split); try(split))); trivial.
      - intros part HpartIsPart. specialize(HaddrNotConfig part HpartIsPart).
        destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
        + rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getKSEntries. unfold getConfigPaddr.
          unfold getConfigBlocks. simpl getAllPaddrPDTAux. rewrite HlookupBTDs2. simpl. auto.
        + rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
          {
            apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial;
              unfold deleteProps in *; intuition.
          }
          assert(isPDT part s1).
          {
            unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
            {
              rewrite <-beqAddrTrue in HbeqCBPart. subst part. rewrite HlookupCurrBs0 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
          }
          rewrite HgetKSEqs2s1; trivial. rewrite HgetKSEqs1s0. rewrite HgetConfigEqs2s1; trivial.
          rewrite HgetConfigEqs1s0; assumption.
      - intros child HchildIsChild Hcontra.
        assert(HchildIsPDTs2: isPDT child s2).
        {
          unfold getMappedPaddr in *. unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
          destruct (lookup child (memory s2) beqAddr); try(simpl in Hcontra; congruence).
          destruct v; try(simpl in Hcontra; congruence). trivial.
        }
        unfold isPDT in HchildIsPDTs2. rewrite Hs2 in HchildIsPDTs2. simpl in HchildIsPDTs2.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) child) eqn:HbeqSh1Child; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        rewrite HgetMappedPEqs2s1 in Hcontra; trivial. assert(isPDT currentPart s1).
        {
          unfold getKSEntries in *. unfold isPDT.
          destruct (lookup currentPart (memory s1) beqAddr); try(simpl in HCBInCurrs1; congruence).
          destruct v; try(simpl in HCBInCurrs1; congruence). trivial.
        }
        rewrite HgetChildrenEqs2s1 in HchildIsChild; trivial. rewrite HgetChildrenEqs1s0 in HchildIsChild; trivial.
        rewrite Hs1 in HchildIsPDTs2. simpl in HchildIsPDTs2.
        destruct (beqAddr currBlock child) eqn:HbeqCBChild; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        rewrite HgetMappedPEqs1s0 in Hcontra; trivial.
        specialize(HaddrNotInChildren child HchildIsChild). congruence.
      - intro HaddrIsBE. assert(HaddrIsBEs0: isBE addr s0).
        {
          unfold isBE in *. rewrite Hs2 in HaddrIsBE. simpl in *.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrIsBE. simpl in *.
          destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
          - rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. rewrite HlookupCurrBs0. trivial.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        apply HltSceEnd; assumption.
      - intro HaddrIsKS. assert(HaddrIsKSs0: isKS addr s0).
        {
          unfold isKS in *. rewrite Hs2 in HaddrIsKS. simpl in *.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrIsKS. simpl in *.
          destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
          - rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. rewrite HlookupCurrBs0. subst newBentry. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        apply HltNextEnd; assumption.
      - intros blockB HblockBIsBEs2. apply Hsh1InRange. auto.
      - intros blockB HblockBIsBEs2. apply HsceInRange. auto.
    }
    assert(HcurrIsPDTs1: isPDT currentPart s1).
    {
      unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock currentPart) eqn:HbeqCBCurr.
      {
        rewrite <-beqAddrTrue in HbeqCBCurr. rewrite HbeqCBCurr in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HpropsAddrToRemoves2: forall block startBlock endBlock,
       In block (getMappedBlocks currentPart s2)
       -> sh1entryPDchild (CPaddr (block + sh1offset)) blockToDelete s2
       -> bentryStartAddr block startBlock s2
       -> bentryEndAddr block endBlock s2
       -> forall addr, In addr (getAllPaddrBlock startBlock endBlock)
           -> ~In addr (getPartitions multiplexer s2)
             /\ (forall part, In part (getPartitions multiplexer s2)
                -> ~In addr (filterOptionPaddr (getKSEntries part s2)) /\ ~ In addr (getConfigPaddr part s2))
             /\ (forall child, In child (getChildren currentPart s2)
                 -> ~In addr (getMappedPaddr child s2))
             /\ (isBE addr s2 -> addr + scoffset < endBlock)
             /\ (isKS addr s2 -> addr + nextoffset < endBlock)
             /\ (forall blockB, isBE blockB s2 -> addr = CPaddr (blockB + sh1offset)
                   -> In blockB (getAllPaddrBlock startBlock endBlock))
             /\ (forall blockB, isBE blockB s2 -> addr = CPaddr (blockB + scoffset)
                   -> In blockB (getAllPaddrBlock startBlock endBlock)) /\ addr <> nullAddr).
    {
      intros block startaddr endaddr HblockMapped HPDchild Hstart Hend addr HaddrInRange.
      rewrite HgetMappedBEqs2s1 in HblockMapped; trivial. rewrite HgetMappedBEqs1s0 in *. unfold sh1entryPDchild in *.
      rewrite Hs2 in HPDchild. simpl in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) (CPaddr (block+sh1offset))) eqn:HbeqSh1s;
        try(simpl in *; exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      rewrite Hs1 in HPDchild. simpl in *.
      destruct (beqAddr currBlock (CPaddr (block+sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hbounds: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
      {
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite Hs2 in Hstart. rewrite Hs2 in Hend.
        simpl in *.
        destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hstart. rewrite Hs1 in Hend.
        simpl in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        {
          rewrite <-beqAddrTrue in HbeqBlocks. subst block. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hbounds as (Hstarts0 & Hends0).
      specialize(HpropsAddrToRemove block startaddr endaddr HblockMapped HPDchild Hstarts0 Hends0 addr HaddrInRange).
      destruct HpropsAddrToRemove as (HaddrNotPart & HaddrNotConfig & HaddrNotInChildren & HltSceEnd & HltNextEnd &
        Hsh1InRange & HsceInRange & HbeqAddrNull).
      rewrite HgetPartsEqs2s0. split; trivial.
      split; only 2: (split; only 2: split; try(split; try(split); try(split))); trivial.
      - intros part HpartIsPart. specialize(HaddrNotConfig part HpartIsPart).
        destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
        + rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getKSEntries. unfold getConfigPaddr.
          unfold getConfigBlocks. simpl getAllPaddrPDTAux. rewrite HlookupBTDs2. simpl. auto.
        + rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
          {
            apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial;
              unfold deleteProps in *; intuition.
          }
          assert(isPDT part s1).
          {
            unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
            {
              rewrite <-beqAddrTrue in HbeqCBPart. subst part. rewrite HlookupCurrBs0 in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
          }
          rewrite HgetKSEqs2s1; trivial. rewrite HgetKSEqs1s0. rewrite HgetConfigEqs2s1; trivial.
          rewrite HgetConfigEqs1s0; assumption.
      - intros child HchildIsChild Hcontra.
        assert(HchildIsPDTs2: isPDT child s2).
        {
          unfold getMappedPaddr in *. unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
          destruct (lookup child (memory s2) beqAddr); try(simpl in Hcontra; congruence).
          destruct v; try(simpl in Hcontra; congruence). trivial.
        }
        unfold isPDT in HchildIsPDTs2. rewrite Hs2 in HchildIsPDTs2. simpl in HchildIsPDTs2.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) child) eqn:HbeqSh1Child; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        rewrite HgetMappedPEqs2s1 in Hcontra; trivial. assert(isPDT currentPart s1).
        {
          unfold getKSEntries in *. unfold isPDT.
          destruct (lookup currentPart (memory s1) beqAddr); try(simpl in HCBInCurrs1; congruence).
          destruct v; try(simpl in HCBInCurrs1; congruence). trivial.
        }
        rewrite HgetChildrenEqs2s1 in HchildIsChild; trivial. rewrite HgetChildrenEqs1s0 in HchildIsChild; trivial.
        rewrite Hs1 in HchildIsPDTs2. simpl in HchildIsPDTs2.
        destruct (beqAddr currBlock child) eqn:HbeqCBChild; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        rewrite HgetMappedPEqs1s0 in Hcontra; trivial.
        specialize(HaddrNotInChildren child HchildIsChild). congruence.
      - intro HaddrIsBE. assert(HaddrIsBEs0: isBE addr s0).
        {
          unfold isBE in *. rewrite Hs2 in HaddrIsBE. simpl in *.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrIsBE. simpl in *.
          destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
          - rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. rewrite HlookupCurrBs0. trivial.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        apply HltSceEnd; assumption.
      - intro HaddrIsKS. assert(HaddrIsKSs0: isKS addr s0).
        {
          unfold isKS in *. rewrite Hs2 in HaddrIsKS. simpl in *.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrIsKS. simpl in *.
          destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
          - rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. rewrite HlookupCurrBs0. subst newBentry. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        apply HltNextEnd; assumption.
      - intros blockB HblockBIsBEs2. apply Hsh1InRange. auto.
      - intros blockB HblockBIsBEs2. apply HsceInRange. auto.
    }
    assert(HlookupBTDs: lookup blockToDelete (memory s) beqAddr = None).
    {
      assert(HpropsOr: In blockToDelete (getAllPaddrBlock startBlock endBlock)
        \/ ~In blockToDelete (getAllPaddrBlock startBlock endBlock)) by (apply Classical_Prop.classic).
      destruct HpropsOr.
      - apply HremovedAddrs; assumption.
      - rewrite HlookupsEq; assumption.
    }
    assert(HpropsForStructEqs2: forall addr, In addr (getAllPaddrBlock startBlock endBlock)
      -> ~In addr (getPartitions multiplexer s2)
          /\ (forall partition, In partition (getPartitions multiplexer s2)
              -> ~ In addr (getConfigPaddr partition s2))
          /\ addr <> nullAddr).
    {
      intros addr HaddrInRange. specialize(HpropsAddrToRemoveSpecs2 addr HaddrInRange).
      destruct HpropsAddrToRemoveSpecs2 as (HaddrNotPart & HaddrNotConfig & _ & _ & _ & _ & _ & HbeqAddrNull).
      split; trivial. split; trivial. intros part HpartIsPart. apply HaddrNotConfig; trivial.
    }
    assert(HgetPartsEqss0: getPartitions multiplexer s = getPartitions multiplexer s0).
    {
      rewrite <-HgetPartsEqs1s0. rewrite <-HgetPartsEqs2s1.
      apply getPartitionsEqNoImpact with startBlock endBlock; trivial.
      unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
    }
    assert(HgetPartsGenEqss0: forall part basePart, In part (getPartitions basePart s)
      -> In part (getPartitions basePart s0)).
    {
      intros part basePart HpartIsPart. apply HgetPartsGenEqs1s0. rewrite <-HgetPartsGenEqs2s1.
      apply getPartitionsImplNoImpact with s startBlock endBlock; trivial.
    }
    assert(HgetKSEqss0: forall part, In part (getPartitions multiplexer s0)
      -> getKSEntries part s = getKSEntries part s0).
    {
      intros part HpartIsPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getKSEntries. rewrite HlookupBTDs0.
        rewrite HlookupBTDs. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        assert(isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
          {
            rewrite <-beqAddrTrue in HbeqCBPart. rewrite HbeqCBPart in *. rewrite HlookupCurrBs0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite <-HgetKSEqs1s0. rewrite <-HgetKSEqs2s1; trivial. rewrite <-HgetPartsEqs2s0 in HpartIsPart.
        apply getKSEntriesEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
    }
    assert(HgetMappedBEqss0: forall part, In part (getPartitions multiplexer s0)
      -> getMappedBlocks part s = getMappedBlocks part s0).
    {
      intros part HpartIsPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getMappedBlocks. unfold getKSEntries.
        rewrite HlookupBTDs0. rewrite HlookupBTDs. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        assert(isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
          {
            rewrite <-beqAddrTrue in HbeqCBPart. rewrite HbeqCBPart in *. rewrite HlookupCurrBs0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite <-HgetMappedBEqs1s0. rewrite <-HgetMappedBEqs2s1; trivial. rewrite <-HgetPartsEqs2s0 in HpartIsPart.
        apply getMappedBlocksEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
    }
    assert(HgetMappedPEqss0: forall part, In part (getPartitions multiplexer s0)
      -> getMappedPaddr part s = getMappedPaddr part s0).
    {
      intros part HpartIsPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getMappedPaddr. unfold getMappedBlocks.
        unfold getKSEntries. rewrite HlookupBTDs0. rewrite HlookupBTDs. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        assert(isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
          {
            rewrite <-beqAddrTrue in HbeqCBPart. rewrite HbeqCBPart in *. rewrite HlookupCurrBs0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite <-HgetMappedPEqs1s0; trivial. rewrite <-HgetMappedPEqs2s1; trivial.
        rewrite <-HgetPartsEqs2s0 in HpartIsPart.
        apply getMappedPaddrEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
    }
    assert(HgetAccMappedBEqss0NotCurr: forall part, In part (getPartitions multiplexer s0)
      -> currentPart <> part
      -> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s0).
    {
      intros part HpartIsPart HbeqCurrPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getAccessibleMappedBlocks. unfold getMappedBlocks.
        unfold getKSEntries. rewrite HlookupBTDs0. rewrite HlookupBTDs. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        assert(isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
          {
            rewrite <-beqAddrTrue in HbeqCBPart. rewrite HbeqCBPart in *. rewrite HlookupCurrBs0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite <-HgetAccMappedBEqs1s0; trivial. rewrite <-HgetAccMappedBEqs2s1; trivial.
        rewrite <-HgetPartsEqs2s0 in HpartIsPart.
        apply getAccessibleMappedBlocksEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
    }
    assert(HgetAccMappedPEqss0NotCurr: forall part, In part (getPartitions multiplexer s0)
      -> currentPart <> part
      -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s0).
    {
      intros part HpartIsPart HbeqCurrPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getAccessibleMappedPaddr.
        unfold getAccessibleMappedBlocks. unfold getMappedBlocks.
        unfold getKSEntries. rewrite HlookupBTDs0. rewrite HlookupBTDs. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        assert(isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
          {
            rewrite <-beqAddrTrue in HbeqCBPart. rewrite HbeqCBPart in *. rewrite HlookupCurrBs0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite <-HgetAccMappedPEqs1s0; trivial. rewrite <-HgetAccMappedPEqs2s1; trivial.
        rewrite <-HgetPartsEqs2s0 in HpartIsPart.
        apply getAccessibleMappedPaddrEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
    }
    assert(HgetAccMappedBEqCurrss0: accessible bentry0 = true
      -> getAccessibleMappedBlocks currentPart s = getAccessibleMappedBlocks currentPart s0).
    {
      intro Haccess. rewrite <-HgetAccMappedBEqCurrs1s0; trivial. rewrite <-HgetAccMappedBEqs2s1; trivial.
      rewrite <-HgetPartsEqs2s0 in HcurrIsPart.
      apply getAccessibleMappedBlocksEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
      specialize(HpropsForStructEqs2 addr HaddrInRange).
      destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
    }
    assert(HgetAccMappedBImplCurrss0: accessible bentry0 = false
      -> forall block, In block (getAccessibleMappedBlocks currentPart s)
          <-> In block (currBlock :: getAccessibleMappedBlocks currentPart s0)).
    {
      intros Haccess block. specialize(HgetAccMappedBImplCurrs1s0 Haccess block).
      rewrite <-HgetAccMappedBEqs2s1 in HgetAccMappedBImplCurrs1s0; trivial.
      assert(Heq: getAccessibleMappedBlocks currentPart s = getAccessibleMappedBlocks currentPart s2).
      {
        rewrite <-HgetPartsEqs2s0 in HcurrIsPart.
        apply getAccessibleMappedBlocksEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
      }
      rewrite Heq. assumption.
    }
    assert(HgetAccMappedPEqCurrss0: accessible bentry0 = true
      -> getAccessibleMappedPaddr currentPart s = getAccessibleMappedPaddr currentPart s0).
    {
      intro Haccess. rewrite <-HgetAccMappedPEqCurrs1s0; trivial. rewrite <-HgetAccMappedPEqs2s1; trivial.
      rewrite <-HgetPartsEqs2s0 in HcurrIsPart.
      apply getAccessibleMappedPaddrEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
      specialize(HpropsForStructEqs2 addr HaddrInRange).
      destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
    }
    assert(HgetAccMappedPImplCurrss0: accessible bentry0 = false
      -> forall addr, In addr (getAccessibleMappedPaddr currentPart s)
          <-> In addr (getAllPaddrBlock startBlock endBlock ++ getAccessibleMappedPaddr currentPart s0)).
    {
      intros Haccess block. specialize(HgetAccMappedPImplCurrs1s0 Haccess block).
      rewrite <-HgetAccMappedPEqs2s1 in HgetAccMappedPImplCurrs1s0; trivial.
      assert(Heq: getAccessibleMappedPaddr currentPart s = getAccessibleMappedPaddr currentPart s2).
      {
        rewrite <-HgetPartsEqs2s0 in HcurrIsPart.
        apply getAccessibleMappedPaddrEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). auto.
      }
      rewrite Heq. assumption.
    }
    assert(HgetConfigEqss0: forall part, In part (getPartitions multiplexer s0)
      -> getConfigPaddr part s = getConfigPaddr part s0).
    {
      intros part HpartIsPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getConfigPaddr.
        unfold getConfigBlocks. simpl getAllPaddrPDTAux. rewrite HlookupBTDs0. rewrite HlookupBTDs. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        assert(isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
          {
            rewrite <-beqAddrTrue in HbeqCBPart. rewrite HbeqCBPart in *. rewrite HlookupCurrBs0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite <-HgetConfigEqs1s0; trivial. rewrite <-HgetConfigEqs2s1; trivial.
        rewrite <-HgetPartsEqs2s0 in HpartIsPart.
        apply getConfigPaddrEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). split; try(split); auto.
        specialize(HaddrNotConfig part HpartIsPart). unfold getConfigPaddr in *.
        apply Lib.in_app_or_neg in HaddrNotConfig. apply HaddrNotConfig.
    }
    assert(HgetConfigBEqs1s0: forall part, isPDT part s0 -> getConfigBlocks part s1 = getConfigBlocks part s0).
    {
      intros part HpartIsPDT. rewrite Hs1. apply IL.getConfigBlocksEqBE; trivial.
    }
    assert(HgetConfigBEqs2s1: forall part, isPDT part s1 -> getConfigBlocks part s2 = getConfigBlocks part s1).
    {
      intros part HpartIsPDT. apply isPDTLookupEq in HpartIsPDT. destruct HpartIsPDT as [pdentry HlookupPart].
      rewrite Hs2. apply IL.getConfigBlocksEqSHE with pdentry; trivial.
    }
    assert(HgetConfigBEqss0: forall part, In part (getPartitions multiplexer s0)
      -> getConfigBlocks part s = getConfigBlocks part s0).
    {
      intros part HpartIsPart. destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getConfigBlocks.
        rewrite HlookupBTDs0. rewrite HlookupBTDs. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(HpartIsPDT: isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        assert(isPDT part s1).
        {
          unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
          {
            rewrite <-beqAddrTrue in HbeqCBPart. rewrite HbeqCBPart in *. rewrite HlookupCurrBs0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite <-HgetConfigBEqs1s0; trivial. rewrite <-HgetConfigBEqs2s1; trivial.
        rewrite <-HgetPartsEqs2s0 in HpartIsPart.
        apply getConfigBlocksEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
        specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (HaddrNotPart & HaddrNotConfig & HbeqAddrNull). split; try(split); auto.
        specialize(HaddrNotConfig part HpartIsPart). unfold getConfigPaddr in *.
        apply Lib.in_app_or_neg in HaddrNotConfig. apply HaddrNotConfig.
    }

    assert(HgetFreeEqs2s0: forall part, In part (getPartitions multiplexer s0)
      -> getFreeSlotsList part s2 = getFreeSlotsList part s0).
    {
      intros part HpartIsPart. specialize(HgetFreeEqs1s0 part HpartIsPart). rewrite <-HgetFreeEqs1s0.
      destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getFreeSlotsList.
        rewrite HlookupBTDs1. rewrite HlookupBTDs2. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        rewrite Hs2. unfold getFreeSlotsList. simpl lookup.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part.
        {
          rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Part. rewrite HbeqSh1Part in *. exfalso.
          unfold isPDT in *. destruct (lookup part (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        destruct (lookup part (memory s1) beqAddr) eqn:HlookupParts1; trivial. destruct v; trivial.
        destruct (beqAddr (firstfreeslot p) nullAddr) eqn:HbeqFirstFNull; trivial. rewrite <-HgetPartsEqs1s0 in *.
        rewrite <-beqAddrFalse in *. specialize(HfirstIsFrees1 part p HlookupParts1 HpartIsPart HbeqFirstFNull).
        destruct HfirstIsFrees1 as (HfirstIsBE & _).
        apply IL.getFreeSlotsListRecEqSHE; trivial; only 2-3: (unfold isBE; unfold isPADDR; intro Hcontra;
          destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s1) beqAddr); try(congruence); destruct v;
          congruence). intro Hcontra. rewrite <-Hcontra in *. unfold isBE in *.
        destruct (lookup (firstfreeslot p) (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }

    assert(NoDupInFreeSlotsList s2).
    {
      assert(Hcons0: NoDupInFreeSlotsList s0) by (unfold deleteProps in *; intuition).
      intros partition HpartIsPart. rewrite HgetPartsEqs2s0 in *. specialize(Hcons0 partition HpartIsPart).
      rewrite HgetFreeEqs2s0; trivial.
    }

    assert(inclFreeSlotsBlockEntries s2).
    {
      assert(Hcons0: inclFreeSlotsBlockEntries s0) by (unfold deleteProps in *; intuition).
      intros partition HpartIsPart. rewrite HgetPartsEqs2s0 in *. specialize(Hcons0 partition HpartIsPart).
      rewrite HgetFreeEqs2s0; trivial. intros block HblockFree. specialize(Hcons0 block HblockFree).
      assert(isPDT partition s1).
      {
        unfold getKSEntries in *. unfold isPDT. rewrite Hs1. simpl.
        destruct (beqAddr currBlock partition) eqn:HbeqCBPart.
        {
          rewrite <-beqAddrTrue in HbeqCBPart. subst partition. rewrite HlookupCurrBs0 in *. simpl in Hcons0.
          congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        destruct (lookup partition (memory s0) beqAddr); try(simpl in Hcons0; congruence).
        destruct v; try(simpl in Hcons0; congruence). trivial.
      }
      rewrite HgetKSEqs2s1; trivial. rewrite HgetKSEqs1s0. assumption.
    }

    assert(HgetFreeEqss0: forall part, In part (getPartitions multiplexer s0)
      -> getFreeSlotsList part s = getFreeSlotsList part s0).
    {
      intros part HpartIsPart. specialize(HgetFreeEqs2s0 part HpartIsPart). rewrite <-HgetFreeEqs2s0.
      rewrite <-HgetPartsEqs2s0 in *.
      apply getFreeSlotsListEqNoImpact with startBlock endBlock; trivial. intros addr HaddrInRange.
      specialize(HpropsAddrToRemoveSpecs2 addr HaddrInRange).
      destruct HpropsAddrToRemoveSpecs2 as (HaddrNotPart & HaddrNotConfig & _ & _ & _ & _ & _ & HbeqAddrNull).
      specialize(HaddrNotConfig part HpartIsPart). destruct HaddrNotConfig. auto.
    }

    assert(HbeqSh1CBNull: CPaddr (currBlock+sh1offset) <> nullAddr).
    {
      unfold nullAddrExists in *. unfold isPADDR in *. intro Hcontra. rewrite Hcontra in *.
      destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
    }
    assert(HsceCBIsSCE: isSCE (CPaddr (currBlock+scoffset)) s0).
    {
      assert(Hres: wellFormedShadowCutIfBlockEntry s0) by (unfold deleteProps in *; intuition).
      specialize(Hres currBlock HCBIsBEs0). destruct Hres as [scentryaddr (Hres & Hsce)]. subst scentryaddr.
      assumption.
    }
    assert(HbeqSceCBNull: CPaddr (currBlock+scoffset) <> nullAddr).
    {
      assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition). unfold isPADDR in *. unfold isSCE in *.
      intro Hcontra. rewrite Hcontra in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }

    assert(HgetChildrenEqss0: forall part, In part (getPartitions multiplexer s0)
      -> getChildren part s = getChildren part s0).
    {
      intros part HpartIsPart.
      destruct (beqAddr part blockToDelete) eqn:HbeqPartBTD.
      - rewrite <-beqAddrTrue in HbeqPartBTD. subst part. unfold getChildren.
        rewrite HlookupBTDs. rewrite HlookupBTDs0. reflexivity.
      - rewrite <-beqAddrFalse in *. assert(isPDT part s0).
        {
          apply partitionsArePDTPartialBis with blockTDParent blockToDelete; trivial; unfold deleteProps in *;
            intuition.
        }
        rewrite <-HgetChildrenEqs1s0; trivial. assert(Heq: getChildren part s2 = getChildren part s1).
        {
          rewrite Hs2. unfold sh1entryPDflag in *. subst sh1entryaddr. rewrite HlookupSh1Eqs1s0 in *.
          destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1;
            try(exfalso; congruence).
          destruct v; try(exfalso; congruence). apply IL.getChildrenEqSHE with s3; trivial.
          unfold isPDT in *. rewrite Hs1. simpl. destruct (beqAddr currBlock part) eqn:HbeqCBPart.
          { rewrite <-beqAddrTrue in HbeqCBPart. subst part. rewrite HlookupCurrBs0 in *. congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite <-Heq. rewrite <-HgetPartsEqs2s0 in *. apply getChildrenEqNoImpact with startBlock endBlock; trivial.
        intros addr HaddrInRange. specialize(HpropsAddrToRemoveSpecs2 addr HaddrInRange).
        destruct HpropsAddrToRemoveSpecs2 as (HaddrNotPart & HaddrNotConfig & _ & _ & _ & _ & _ & HbeqAddrNull).
        specialize(HaddrNotConfig part HpartIsPart). destruct HaddrNotConfig. auto.
    }

    assert(nullAddrExists s).
    { (* BEGIN nullAddrExists s *)
      unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupsEq; trivial. intro Hcontra.
      specialize(HpropsForStructEqs2 nullAddr Hcontra). destruct HpropsForStructEqs2 as (_ & _ & Hneq). congruence.
      (* END nullAddrExists *)
    }

    assert(Hranges0: getAllPaddrAux [currBlock] s0 = getAllPaddrBlock startBlock endBlock).
    {
      simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      destruct (lookup currBlock (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      rewrite <-HstartCBs0. rewrite <-HendCBs0. apply app_nil_r.
    }

    assert(Hranges1: getAllPaddrAux [currBlock] s1 = getAllPaddrBlock startBlock endBlock).
    {
      simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      destruct (lookup currBlock (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      rewrite <-HstartCBs1. rewrite <-HendCBs1. apply app_nil_r.
    }

    assert(HlookupCBEqs2s1: lookup currBlock (memory s2) beqAddr = lookup currBlock (memory s1) beqAddr).
    {
      unfold bentryStartAddr in *. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) currBlock) eqn:HbeqNextCB.
      {
        rewrite <-beqAddrTrue in HbeqNextCB. rewrite HbeqNextCB in *. exfalso.
        destruct (lookup currBlock (memory s1) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }

    assert(Hranges2: getAllPaddrAux [currBlock] s2 = getAllPaddrBlock startBlock endBlock).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl. rewrite HlookupCBEqs2s1.
      destruct (lookup currBlock (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
      rewrite <-HstartCBs1. rewrite <-HendCBs1. apply app_nil_r.
    }

    assert(wellFormedFstShadowIfBlockEntry s).
    { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
      intros block HblockIsBE. unfold isBE in *.
      assert(HblockNotInRange: ~In block (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. apply HremovedAddrs in Hcontra. rewrite Hcontra in *. congruence.
      }
      rewrite HlookupsEq in HblockIsBE; trivial. specialize(HwellSh1s2 block HblockIsBE). unfold isSHE in *.
      rewrite HlookupsEq; trivial. contradict HblockNotInRange. rewrite <-Hranges0 in *.
      assert(Hres: blockAndSh1InSameBlock s0) by (unfold deleteProps in *; intuition).
      unfold blockAndSh1InSameBlock in *. apply Hres with currentPart; trivial. apply HBEsIntact; assumption.
      (* END wellFormedFstShadowIfBlockEntry *)
    }

    assert(forall idPDchild sh1entryaddr part, idPDchild <> blockTDParent
        -> In part (getPartitions multiplexer s)
        -> In idPDchild (getMappedBlocks part s)
        -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
        -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s)).
    { (* BEGIN PDTIfPDFlag s *)
      assert(Hcons0: forall idPDchild sh1entryaddr part, idPDchild <> blockTDParent
        -> In part (getPartitions multiplexer s0)
        -> In idPDchild (getMappedBlocks part s0)
        -> true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0
        -> bentryAFlag idPDchild false s0 /\ bentryPFlag idPDchild true s0
            /\ (exists startaddr, bentryStartAddr idPDchild startaddr s0 /\ entryPDT idPDchild startaddr s0))
        by (unfold deleteProps in *; intuition).
      intros block sh1entryaddrB part HbeqBlockBTDP HpartIsPart HblockMapped HcheckChild.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in *; trivial.
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        destruct HcheckChild as (_ & Hsh1). unfold sh1entryAddr in *.
        assert(~ In block (getAllPaddrBlock startBlock endBlock)).
        {
          intro Hcontra. apply HremovedAddrs in Hcontra. rewrite Hcontra in *. congruence.
        }
        rewrite HlookupsEq; trivial. rewrite HlookupsEq in Hsh1; trivial. rewrite Hs2. rewrite Hs2 in Hsh1.
        simpl in *. destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqNextBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      unfold checkChild in *. unfold sh1entryAddr in *. unfold bentryAFlag. unfold bentryPFlag.
      unfold bentryStartAddr. unfold entryPDT. rewrite HlookupBlockEq in *.
      assert(HcheckChilds0: true = checkChild block s0 sh1entryaddrB /\ sh1entryAddr block sh1entryaddrB s0).
      {
        unfold checkChild. unfold sh1entryAddr. destruct HcheckChild as (HcheckChild & Hsh1).
        assert(HlookupSh1BEq: lookup sh1entryaddrB (memory s) beqAddr = lookup sh1entryaddrB (memory s0) beqAddr).
        {
          destruct (lookup block (memory s1) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
          {
            intro Hcontra. apply HremovedAddrs in Hcontra. rewrite Hcontra in *. congruence.
          }
          rewrite HlookupsEq; trivial. rewrite HlookupsEq in HcheckChild; trivial. rewrite Hs2 in HcheckChild.
          rewrite Hs2. simpl in *. destruct (beqAddr (CPaddr (currBlock + sh1offset)) sh1entryaddrB) eqn:HbeqSh1s;
            try(simpl in HcheckChild; exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; auto. rewrite Hs1 in HcheckChild. rewrite Hs1. simpl in *.
          destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        rewrite HlookupSh1BEq in *. rewrite Hs1 in Hsh1. rewrite Hs1 in HcheckChild. simpl in *.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 block sh1entryaddrB part HbeqBlockBTDP HpartIsPart HblockMapped HcheckChilds0).
      destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartIsPDT)]).
      assert(HstartBIsPart: In startaddr (getPartitions multiplexer s0)).
      {
        apply IL.childrenPartitionInPartitionList with part; trivial.
        - unfold deleteProps in *; intuition.
        - unfold getChildren. assert(isPDT part s0).
          {
            unfold isPDT. unfold getMappedBlocks in *. unfold getKSEntries in *.
            destruct (lookup part (memory s0) beqAddr); try(simpl in HblockMapped; congruence).
            destruct v; try(simpl in HblockMapped; congruence). trivial.
          }
          unfold isPDT in *. destruct (lookup part (memory s0) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence).
          induction (getMappedBlocks part s0); simpl in HblockMapped; simpl; try(congruence). unfold getPDs. simpl.
          destruct HblockMapped as [Heq | Hrec].
          + subst a1. unfold childFilter at 1. destruct HcheckChilds0 as (HcheckChilds0 & Hsh1s0).
            unfold checkChild in *. unfold sh1entryAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). subst sh1entryaddrB. unfold CPaddr in HcheckChilds0.
            unfold Paddr.addPaddrIdx. assert(block+sh1offset <= maxAddr).
            {
              assert(Hnull: isPADDR nullAddr s0) by (unfold deleteProps in *; intuition).
              destruct (Compare_dec.le_dec (block + sh1offset) maxAddr); try(lia). exfalso. unfold isPADDR in *.
              cbn in Hnull. replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (block + sh1offset) n0 |} with
                {| p := 0; Hp := ADT.CPaddr_obligation_1 0 (PeanoNat.Nat.le_0_l maxAddr) |} in HcheckChilds0;
                only 2: (f_equal; apply proof_irrelevance).
              destruct (lookup {| p := 0; Hp := ADT.CPaddr_obligation_1 0 (PeanoNat.Nat.le_0_l maxAddr) |}
                (memory s0) beqAddr); try(congruence). destruct v; congruence.
            }
            destruct (Compare_dec.le_dec (block + sh1offset) maxAddr); try(lia).
            replace {| p := block + sh1offset; Hp := StateLib.Paddr.addPaddrIdx_obligation_1 block sh1offset l1 |}
              with {| p := block + sh1offset; Hp := ADT.CPaddr_obligation_1 (block + sh1offset) l1 |};
              only 2: (f_equal; apply proof_irrelevance).
            destruct (lookup {| p := block + sh1offset; Hp := ADT.CPaddr_obligation_1 (block + sh1offset) l1 |}
              (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
            rewrite <-HcheckChilds0. simpl. unfold bentryStartAddr in *.
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). auto.
          + destruct (childFilter s0 a1); auto. simpl. auto.
      }
      assert(HstartNotInRange: ~In startaddr (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy startaddr Hcontra).
        destruct HpropsAddrToRemoveCopy as (HcontraB & _). congruence.
      }
      assert(HlookupStartEqss2: lookup startaddr (memory s) beqAddr = lookup startaddr (memory s2) beqAddr).
      { apply HlookupsEq; assumption. }
      assert(HlookupStartEq: lookup startaddr (memory s) beqAddr = lookup startaddr (memory s0) beqAddr).
      {
        rewrite HlookupStartEqss2. rewrite Hs2. unfold entryPDT in *. unfold bentryStartAddr in *.
        destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-Hstart in HstartIsPDT. simpl.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) startaddr) eqn:HbeqSh1Start.
        {
          rewrite <-beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *. rewrite HlookupSh1Eqs1s0 in *. exfalso.
          destruct (lookup startaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock startaddr) eqn:HbeqCurrStart.
        {
          rewrite <-beqAddrTrue in HbeqCurrStart. rewrite HbeqCurrStart in *. rewrite HlookupCurrBs0 in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      rewrite Hs1. simpl. destruct (beqAddr currBlock block) eqn:HbeqCurrBlock.
      {
        rewrite <-beqAddrTrue in HbeqCurrBlock. subst block. exfalso. assert(startaddr = startBlock).
        {
          unfold bentryStartAddr in *. rewrite HlookupCurrBs0 in *. rewrite HstartCBs0. assumption.
        }
        subst startaddr. contradict HstartNotInRange. apply IL.getAllPaddrBlockIncl; lia.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. split; trivial. split; trivial. exists startaddr.
      split; trivial. unfold entryPDT in *. unfold bentryStartAddr in *.
      destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite <-Hstart in *. rewrite HlookupStartEq. assumption.
      (* END PDTIfPDFlag *)
    }

    assert(AccessibleNoPDFlag s).
    { (* BEGIN AccessibleNoPDFlag s *)
      assert(Hcons0: AccessibleNoPDFlag s0) by (unfold deleteProps in *; intuition).
      intros block sh1entryaddrB HblockIsBE Hsh1 HAflag. unfold bentryAFlag in *. unfold sh1entryAddr in *.
      unfold isBE in *. assert(~ In block (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. apply HremovedAddrs in Hcontra. rewrite Hcontra in *. congruence. }
      assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s1) beqAddr).
      {
        rewrite HlookupsEq; trivial. rewrite HlookupsEq in HAflag; trivial. rewrite Hs2. rewrite Hs2 in HAflag.
        simpl in *. destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqNextBlock;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      rewrite HlookupBlockEq in *. assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE. rewrite Hs1 in HblockIsBE. simpl in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      assert(HlookupSh1BEqss2: lookup sh1entryaddrB (memory s) beqAddr = lookup sh1entryaddrB (memory s2) beqAddr).
      {
        apply HlookupsEq. intro Hcontra.
        assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0) by (unfold deleteProps in *; intuition).
        specialize(Hsh1IsSHE block HblockIsBEs0). specialize(HpropsAddrToRemoveCopy sh1entryaddrB Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & _ & _ & _ & _ & HnotInRange & _).
        destruct (lookup block (memory s1) beqAddr); try(congruence). destruct v; try(congruence).
        specialize(HnotInRange block HblockIsBEs0 Hsh1). congruence.
      }
      unfold sh1entryPDflag in *. rewrite HlookupSh1BEqss2. rewrite Hs1 in Hsh1. rewrite Hs1 in HAflag. simpl in *.
      destruct (beqAddr currBlock block) eqn:HbeqBlocks.
      - rewrite <-beqAddrTrue in HbeqBlocks. subst block. subst sh1entryaddrB. rewrite <-Hsh1CB. rewrite Hs2. simpl.
        rewrite <-Hsh1CB. rewrite IL.beqAddrTrue. reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(Hcons0 block sh1entryaddrB HblockIsBEs0 Hsh1 HAflag). unfold sh1entryPDflag in *. rewrite Hs2.
        simpl. destruct (beqAddr (CPaddr (currBlock + sh1offset)) sh1entryaddrB) eqn:HbeqSh1s; try(reflexivity).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1.
        {
          rewrite <-beqAddrTrue in HbeqCBSh1. rewrite HbeqCBSh1 in *. rewrite HlookupCurrBs0 in *. congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END AccessibleNoPDFlag *)
    }

    assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
    { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
      intros partition pdentry HlookupPart HpartIsPart HbeqFirstNull. rewrite HgetPartsEqss0 in *.
      rewrite <-HgetPartsEqs2s0 in *. assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. specialize(HremovedAddrs partition Hcontra). congruence. }
      rewrite HlookupsEq in HlookupPart; trivial. unfold isBE.
      specialize(HfirstIsFrees2 partition pdentry HlookupPart HpartIsPart HbeqFirstNull).
      destruct HfirstIsFrees2 as (_ & HfirstIsFrees2). unfold isFreeSlot in *.
      assert(~In (firstfreeslot pdentry) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveSpecs2 (firstfreeslot pdentry) Hcontra).
        destruct HpropsAddrToRemoveSpecs2 as (_ & HfirstNotConfig & _). rewrite Hs2 in HlookupPart. simpl in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(HfirstNotConfig partition HpartIsPart). destruct HfirstNotConfig as (HfirstNotEntry & _).
        assert(isPDT partition s1) by (unfold isPDT; rewrite HlookupPart; trivial).
        contradict HfirstNotEntry. rewrite HgetKSEqs2s1; trivial. rewrite HgetKSEqs1s0.
        assert(Hres: inclFreeSlotsBlockEntries s0) by (unfold deleteProps in *; intuition).
        rewrite HgetPartsEqs2s0 in *. specialize(Hres partition HpartIsPart (SomePaddr (firstfreeslot pdentry))).
        assert(HnoDupFree: NoDupInFreeSlotsList s0) by (unfold deleteProps in *; intuition).
        specialize(HnoDupFree partition HpartIsPart). destruct HnoDupFree as [optFreeList (Hlist & HwellFFree & _)].
        subst optFreeList. apply optionIsInFilter. apply Hres. rewrite Hs1 in HlookupPart. simpl in *.
        destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        unfold getFreeSlotsList in *. rewrite HlookupPart in *.
        rewrite beqAddrFalse in HbeqFirstNull. rewrite HbeqFirstNull in *. rewrite MaxIdxNextEq in *. simpl in *.
        assert(HfirstFreeIsFrees0: FirstFreeSlotPointerIsBEAndFreeSlot s0) by (unfold deleteProps in *; intuition).
        rewrite <-beqAddrFalse in *.
        specialize(HfirstFreeIsFrees0 partition pdentry HlookupPart HpartIsPart HbeqFirstNull).
        destruct HfirstFreeIsFrees0 as (HfirstIsBE & _). unfold isBE in *.
        destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (StateLib.Index.pred (nbfreeslots pdentry)); try(simpl in HwellFFree; exfalso; congruence).
        simpl. auto.
      }
      rewrite HlookupsEq; trivial.
      destruct (lookup (firstfreeslot pdentry) (memory s2) beqAddr) eqn:HlookupFirst; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). split; trivial.
      assert(HfirstIsBE: isBE (firstfreeslot pdentry) s0).
      {
        rewrite Hs2 in HlookupFirst. simpl in *.
        destruct (beqAddr (CPaddr (currBlock+sh1offset)) (firstfreeslot pdentry)) eqn:HbeqSh1First;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        rewrite Hs1 in HlookupFirst. simpl in *. unfold isBE.
        destruct (beqAddr currBlock (firstfreeslot pdentry)) eqn:HbeqCBFirst.
        - rewrite <-beqAddrTrue in HbeqCBFirst. rewrite <-HbeqCBFirst in *. rewrite HlookupCurrBs0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite HlookupFirst. trivial.
      }
      assert(~In (CPaddr (firstfreeslot pdentry+sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. rewrite <-Hranges0 in *. rewrite HgetPartsEqs2s0 in *.
        assert(Hsh1InSameBs0: blockAndSh1InSameBlock s0) by (unfold deleteProps in *; intuition).
        specialize(Hsh1InSameBs0 currentPart (firstfreeslot pdentry) currBlock HcurrIsPart HCBMapped HfirstIsBE
          Hcontra). congruence.
      }
      rewrite HlookupsEq; trivial.
      destruct (lookup (CPaddr (firstfreeslot pdentry+sh1offset)) (memory s2) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      assert(~In (CPaddr (firstfreeslot pdentry+scoffset)) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. rewrite <-Hranges0 in *. rewrite HgetPartsEqs2s0 in *.
        assert(HsceInSameBs0: blockAndSceInSameBlock s0) by (unfold deleteProps in *; intuition).
        specialize(HsceInSameBs0 currentPart (firstfreeslot pdentry) currBlock HcurrIsPart HCBMapped HfirstIsBE
          Hcontra). congruence.
      }
      rewrite HlookupsEq; trivial.
      (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
    }

    assert(multiplexerIsPDT s).
    { (* BEGIN multiplexerIsPDT s *)
      assert(Hcons0: multiplexerIsPDT s0) by (unfold deleteProps in *; intuition).
      unfold multiplexerIsPDT in *. unfold isPDT in *. assert(~In multiplexer (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy multiplexer Hcontra).
        destruct HpropsAddrToRemoveCopy as (HmultNotPart & _). contradict HmultNotPart. unfold getPartitions.
        replace (maxAddr+2) with (S (maxAddr+1)); only 2: lia. simpl. auto.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) multiplexer) eqn:HbeqSh1Mult.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Mult. rewrite HbeqSh1Mult in *.
        destruct (lookup multiplexer (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock multiplexer) eqn:HbeqCBMult.
      {
        rewrite <-beqAddrTrue in HbeqCBMult. rewrite HbeqCBMult in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END multiplexerIsPDT *)
    }

    rewrite Hs2 in HcurrEqss0. simpl in HcurrEqss0. rewrite Hs1 in HcurrEqss0. simpl in HcurrEqss0.

    assert(currentPartitionInPartitionsList s).
    { (* BEGIN currentPartitionInPartitionsList s *)
      assert(Hcons0: currentPartitionInPartitionsList s0) by (unfold deleteProps in *; intuition).
      unfold currentPartitionInPartitionsList. rewrite HgetPartsEqss0. rewrite HcurrEqss0. assumption.
      (* END currentPartitionInPartitionsList *)
    }

    assert(wellFormedShadowCutIfBlockEntry s).
    { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
      assert(Hcons0: wellFormedShadowCutIfBlockEntry s0) by (unfold deleteProps in *; intuition).
      intros block HblockIsBE. unfold isBE in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HblockIsBE; trivial. }
      rewrite HlookupsEq in HblockIsBE; trivial. rewrite Hs2 in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE. rewrite Hs1 in HblockIsBE. simpl in HblockIsBE.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. assumption.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 block HblockIsBEs0). destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr.
      split; trivial. subst scentryaddr. unfold isSCE in *.
      assert(~In (CPaddr (block+scoffset)) (getAllPaddrBlock startBlock endBlock)).
      {
        rewrite <-Hranges0. intro Hcontra.
        assert(HsceInSameB: blockAndSceInSameBlock s0) by (unfold deleteProps in *; intuition).
        specialize(HsceInSameB currentPart block currBlock HcurrIsPart HCBMapped HblockIsBEs0 Hcontra).
        congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) (CPaddr (block+scoffset))) eqn:HbeqSh1Sce.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *.
        destruct (lookup (CPaddr (block+scoffset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (block+scoffset))) eqn:HbeqCBSce.
      {
        rewrite <-beqAddrTrue in HbeqCBSce. rewrite <-HbeqCBSce in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END wellFormedShadowCutIfBlockEntry *)
    }

    assert(BlocksRangeFromKernelStartIsBE s).
    { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
      assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by (unfold deleteProps in *; intuition).
      intros kern idx HkernIsKS HltIdxKernEntries. unfold isKS in *.
      assert(~In kern (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HkernIsKS; trivial. }
      rewrite HlookupsEq in HkernIsKS; trivial. rewrite Hs2 in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr currBlock kern) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 kern idx HkernIsKSs0 HltIdxKernEntries). unfold isBE in *.
      assert(~In (CPaddr (kern+idx)) (getAllPaddrBlock startBlock endBlock)).
      {
        rewrite <-Hranges0 in *. intro Hcontra.
        assert(HkernInSameB: kernInSameBlock s0) by (unfold deleteProps in *; intuition).
        assert(Hblkidx: indexIsDistFromKern s0) by (unfold deleteProps in *; intuition).
        specialize(Hblkidx kern idx HkernIsKSs0 HltIdxKernEntries).
        specialize(HkernInSameB currBlock currentPart idx (CPaddr (kern+idx)) HcurrIsPart HCBMapped Hcontra Hblkidx).
        assert(Heq: CPaddr (kern+idx)-idx = kern).
        {
          unfold CPaddr. unfold CPaddr in Hcons0.
          destruct (Compare_dec.le_dec (kern + idx) maxAddr); try(simpl; lia). exfalso.
          replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (kern + idx) n0 |} with nullAddr in *;
            try(cbn; f_equal; apply proof_irrelevance).
          assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
          destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite Heq in *. rewrite paddrEqId in HkernInSameB. congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) (CPaddr (kern+idx))) eqn:HbeqSh1Blk.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Blk. rewrite HbeqSh1Blk in *.
        destruct (lookup (CPaddr (kern+idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (kern + idx))) eqn:HbeqCBBlk; trivial. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; auto.
      (* END BlocksRangeFromKernelStartIsBE *)
    }

    assert(KernelStructureStartFromBlockEntryAddrIsKS s).
    { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s *)
      assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0)
        by (unfold deleteProps in *; intuition). intros block idx HblockIsBE Hblkidx. unfold isBE in *.
      unfold bentryBlockIndex in *. assert(HblockNotInRange: ~In block (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HblockIsBE; trivial. }
      rewrite HlookupsEq in HblockIsBE; trivial. rewrite HlookupsEq in Hblkidx; trivial. rewrite Hs2 in HblockIsBE.
      rewrite Hs2 in Hblkidx. simpl in HblockIsBE. simpl in Hblkidx.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: isBE block s0 /\ bentryBlockIndex block idx s0).
      {
        unfold isBE. unfold bentryBlockIndex. rewrite Hs1 in HblockIsBE. rewrite Hs1 in Hblkidx. simpl in HblockIsBE.
        simpl in Hblkidx. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HnewB in *. rewrite HlookupCurrBs0. split; auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (HblockIsBEs0 & Hblkidxs0). specialize(Hcons0 block idx HblockIsBEs0 Hblkidxs0).
      unfold isKS in *. assert(~In (CPaddr (block-idx)) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy (CPaddr (block-idx)) Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & _ & _ & _ & Hprop & _). specialize(Hprop Hcons0).
        apply IL.getAllPaddrBlockInclRev in Hcontra. destruct Hcontra as (HlebStartKern & _).
        contradict HblockNotInRange. assert(CPaddr (block-idx) <= block).
        {
          unfold CPaddr. assert(block <= maxAddr) by (apply Hp).
          destruct (Compare_dec.le_dec (block - idx) maxAddr); try(lia). simpl. lia.
        }
        assert(block <= CPaddr (block-idx) + nextoffset).
        {
          unfold CPaddr. assert(block <= maxAddr) by (apply Hp). rewrite nextoffsetVal.
          destruct (Compare_dec.le_dec (block - idx) maxAddr); try(lia). simpl.
          assert(idx < kernelStructureEntriesNb).
          {
            unfold bentryBlockIndex in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite Hblkidxs0. apply Hidx.
          }
          lia.
        }
        apply IL.getAllPaddrBlockIncl; lia.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (block - idx))) eqn:HbeqSh1Kern.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Kern. rewrite HbeqSh1Kern in *.
        destruct (lookup (CPaddr (block-idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (block-idx))) eqn:HbeqCBKern.
      - rewrite HnewB. rewrite <-beqAddrTrue in HbeqCBKern. rewrite <-HbeqCBKern in *. rewrite HlookupCurrBs0 in *.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END KernelStructureStartFromBlockEntryAddrIsKS *)
    }

    assert(forall part block sh1entryaddr sh1entry,
        sh1entry.(PDchild) <> blockToDelete
        -> In part (getPartitions multiplexer s)
        -> In block (getMappedBlocks part s)
        -> sh1entryaddr = CPaddr (block+sh1offset)
        -> lookup sh1entryaddr (memory s) beqAddr = Some (SHE sh1entry)
        -> sh1entry.(inChildLocation) <> nullAddr
        -> isBE sh1entry.(inChildLocation) s).
    { (* BEGIN sh1InChildLocationIsBE s *)
      assert(Hcons0: forall part block sh1entryaddr sh1entry,
        sh1entry.(PDchild) <> blockToDelete
        -> In part (getPartitions multiplexer s0)
        -> In block (getMappedBlocks part s0)
        -> sh1entryaddr = CPaddr (block+sh1offset)
        -> lookup sh1entryaddr (memory s0) beqAddr = Some (SHE sh1entry)
        -> sh1entry.(inChildLocation) <> nullAddr
        -> isBE sh1entry.(inChildLocation) s0) by (unfold deleteProps in *; intuition).
      intros part block sh1entryaddrB sh1entry HbeqChildBTD HpartIsPart HblockMapped Hsh1 HlookupSh1 HbeqLocNull.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in *; trivial.
      assert(Hsh1BNotInRange: ~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HlookupSh1; trivial. congruence. }
      rewrite HlookupsEq in HlookupSh1; trivial. rewrite Hs2 in HlookupSh1. simpl in HlookupSh1.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) sh1entryaddrB) eqn:HbeqSh1s.
      {
        simpl in HlookupSh1. injection HlookupSh1 as Hsh1entriesEq. subst sh1entry. simpl in HbeqLocNull. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupSh1.
      simpl in HlookupSh1. destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block sh1entryaddrB sh1entry HbeqChildBTD HpartIsPart HblockMapped Hsh1 HlookupSh1
        HbeqLocNull). unfold isBE in *.
      assert(~In (inChildLocation sh1entry) (getAllPaddrBlock startBlock endBlock)).
      {
        assert(HchildStart: forall partition block sh1entryaddr blockChild idchild,
          idchild <> blockToDelete
          -> In partition (getPartitions multiplexer s0)
          -> In block (getMappedBlocks partition s0)
          -> sh1entryAddr block sh1entryaddr s0
          -> sh1entryPDchild sh1entryaddr idchild s0
          -> sh1entryInChildLocationWeak sh1entryaddr blockChild s0
          -> idchild <> nullAddr
          -> blockChild <> nullAddr
          -> (forall startaddr, bentryStartAddr block startaddr s0 -> bentryStartAddr blockChild startaddr s0)
                /\ In blockChild (getMappedBlocks idchild s0)) by (unfold deleteProps in *; intuition).
        intro Hcontra. specialize(HpropsAddrToRemoveCopy (inChildLocation sh1entry) Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & HlocNotKS & _).
        assert(HPDchild: sh1entryPDchild sh1entryaddrB (PDchild sh1entry) s0).
        { unfold sh1entryPDchild. rewrite HlookupSh1. reflexivity. }
        assert(Hsh1B: sh1entryAddr block sh1entryaddrB s0).
        {
          unfold sh1entryAddr. apply IL.mappedBlockIsBE in HblockMapped.
          destruct HblockMapped as [bentry (Hlookup & _)]. rewrite Hlookup. assumption.
        }
        assert(Hloc: sh1entryInChildLocationWeak sh1entryaddrB (inChildLocation sh1entry) s0).
        { unfold sh1entryInChildLocationWeak. rewrite HlookupSh1. reflexivity. }
        assert(HbeqChildNull: PDchild sh1entry <> nullAddr).
        {
          assert(HlocNullToo: childBlockNullIfChildNull s0) by (unfold deleteProps in *; intuition). intro HcontraB.
          rewrite HcontraB in *.
          specialize(HlocNullToo part block sh1entryaddrB HpartIsPart HblockMapped Hsh1B HPDchild).
          unfold sh1entryInChildLocation in *. unfold sh1entryInChildLocationWeak in *. rewrite HlookupSh1 in *.
          destruct HlocNullToo. congruence.
        }
        specialize(HchildStart part block sh1entryaddrB (inChildLocation sh1entry) (PDchild sh1entry) HbeqChildBTD
          HpartIsPart HblockMapped Hsh1B HPDchild Hloc HbeqChildNull HbeqLocNull).
        specialize(HpropsAddrToRemove currBlock startBlock endBlock HCBMapped HPDchildCBs0 HstartCBs0 HendCBs0
          (inChildLocation sh1entry) Hcontra). destruct HpropsAddrToRemove as (_ & HlocNotKSE & _).
        assert(HchildIsPart: In (PDchild sh1entry) (getPartitions multiplexer s0)).
        {
          assert(HchildIsChild: pdchildIsPDT s0) by (unfold deleteProps in *; intuition).
          specialize(HchildIsChild part block sh1entryaddrB (PDchild sh1entry) HpartIsPart HblockMapped Hsh1B HPDchild
            HbeqChildNull).
          apply IL.childrenPartitionInPartitionList with part; trivial; unfold deleteProps in *; intuition.
        }
        specialize(HlocNotKSE (PDchild sh1entry) HchildIsPart). destruct HlocNotKSE as (HlocNotKSE & _).
        destruct HchildStart as (_ & HlocMappedChild). unfold getMappedBlocks in *.
        apply InFilterPresentInList in HlocMappedChild. congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (inChildLocation sh1entry)) eqn:HbeqSh1Loc.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Loc. rewrite HbeqSh1Loc in *.
        destruct (lookup (inChildLocation sh1entry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (inChildLocation sh1entry)) eqn:HbeqCBLoc; trivial. rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity; auto.
      (* END sh1InChildLocationIsBE *)
    }

    assert(StructurePointerIsKS s).
    { (* BEGIN StructurePointerIsKS s *)
      assert(Hcons0: StructurePointerIsKS s0) by (unfold deleteProps in *; intuition).
      intros partition pdentry HpartIsPart HlookupPart HbeqStructNull. rewrite HgetPartsEqss0 in *.
      assert(HpartNotInRange: ~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HlookupPart; trivial. congruence. }
      rewrite HlookupsEq in HlookupPart; trivial. rewrite Hs2 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart.
      simpl in HlookupPart. destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition pdentry HpartIsPart HlookupPart HbeqStructNull). unfold isKS in *.
      assert(~In (structure pdentry) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy (structure pdentry) Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & Hprop & _). specialize(Hprop partition HpartIsPart).
        destruct Hprop as (_ & Hprop). contradict Hprop. unfold getConfigPaddr. apply in_or_app. right.
        unfold getConfigBlocks. rewrite HlookupPart. rewrite MaxIdxNextEq. simpl.
        assert(Hnext: nextKSAddr (structure pdentry) (CPaddr ((structure pdentry)+nextoffset)) s0).
        {
          unfold nextKSAddr. destruct (lookup (structure pdentry) (memory s0) beqAddr); try(congruence).
          destruct v; congruence.
        }
        assert(HnextIsPADDR: NextKSOffsetIsPADDR s0) by (unfold deleteProps in *; intuition).
        specialize(HnextIsPADDR (structure pdentry) (CPaddr ((structure pdentry)+nextoffset)) Hcons0 Hnext).
        destruct HnextIsPADDR as (HnextIsPADDR & HbeqNextNull).
        destruct (lookup (structure pdentry) (memory s0) beqAddr) eqn:HlookupStruct; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        assert(structure pdentry +nextoffset <= maxAddr).
        {
          unfold CPaddr in HbeqNextNull. cbn in HbeqNextNull.
          destruct (Compare_dec.le_dec (structure pdentry + nextoffset) maxAddr); try(lia). contradict HbeqNextNull.
          f_equal. apply proof_irrelevance.
        }
        unfold Paddr.addPaddrIdx. unfold CPaddr in HnextIsPADDR.
        destruct (Compare_dec.le_dec (structure pdentry + nextoffset) maxAddr); try(lia).
        replace {|
                   p := structure pdentry + nextoffset;
                   Hp := StateLib.Paddr.addPaddrIdx_obligation_1 (structure pdentry) nextoffset l0
                 |}
          with {|
                 p := structure pdentry + nextoffset;
                 Hp := ADT.CPaddr_obligation_1 (structure pdentry + nextoffset) l0
               |}; try(f_equal; apply proof_irrelevance). unfold isPADDR in *.
        destruct (lookup
         {|
           p := structure pdentry + nextoffset;
           Hp := ADT.CPaddr_obligation_1 (structure pdentry + nextoffset) l0
         |} (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        assert(In (structure pdentry)
          (getAllPaddrBlockAux 0 (structure pdentry) Constants.kernelStructureTotalLength)).
        {
          rewrite kernelStructureTotalLengthVal. apply IL.getAllPaddrBlockAuxIncl; lia.
        }
        destruct (StateLib.Index.pred (CIndex maxNbPrepare)); simpl; rewrite HlookupStruct.
        - apply in_or_app. left. assumption.
        - rewrite app_nil_r. assumption.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (structure pdentry)) eqn:HbeqSh1Struct.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Struct. rewrite HbeqSh1Struct in *.
        destruct (lookup (structure pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (structure pdentry)) eqn:HbeqCBStruct.
      - rewrite HnewB. rewrite <-beqAddrTrue in HbeqCBStruct. rewrite <-HbeqCBStruct in *.
        rewrite HlookupCurrBs0 in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END StructurePointerIsKS *)
    }

    assert((forall addr nextKSaddr nextKS,
        (forall block, In block (filterOptionPaddr (getKSEntries currentPart s))
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete sInit
          -> ~In nextKS (getAllPaddrAux [block] s))
        -> isKS addr s
        -> nextKSAddr addr nextKSaddr s
        -> nextKSentry nextKSaddr nextKS s
        -> nextKS <> nullAddr
        -> isKS nextKS s)).
    { (* BEGIN NextKSIsKS s *)
      assert(Hcons0: forall addr nextKSaddr nextKS,
        (forall block, In block (filterOptionPaddr (getKSEntries currentPart s0))
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete sInit
          -> ~In nextKS (getAllPaddrAux [block] s0))
        -> isKS addr s0
        -> nextKSAddr addr nextKSaddr s0
        -> nextKSentry nextKSaddr nextKS s0
        -> nextKS <> nullAddr
        -> isKS nextKS s0) by (unfold deleteProps in *; intuition). clear HlookupBTDs.
      intros kern nextKSaddr nextKS Hexcept HkernIsKS HnextAddr HnextKSAddr HbeqNextNull. unfold nextKSAddr in *.
      unfold nextKSentry in *. assert(HkernNotInRange: ~In kern (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HnextAddr; trivial. }
      unfold isKS in HkernIsKS. assert(HnextaddrNotInRange: ~In nextKSaddr (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HnextKSAddr; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HnextAddr. rewrite Hs2 in HnextKSAddr. simpl in HnextAddr.
      simpl in HnextKSAddr. rewrite Hs2 in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) nextKSaddr) eqn:HbeqSh1Nextaddr; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HnextKSAddr.
      simpl in HnextKSAddr. destruct (beqAddr currBlock nextKSaddr) eqn:HbeqCBNextaddr; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hkerns0: isKS kern s0 /\ nextKSAddr kern nextKSaddr s0).
      {
        unfold nextKSAddr. unfold isKS. rewrite Hs1 in HnextAddr. rewrite Hs1 in HkernIsKS. simpl in HnextAddr.
        simpl in HkernIsKS. destruct (beqAddr currBlock kern) eqn:HbeqCBKern.
        - rewrite <-beqAddrTrue in HbeqCBKern. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in HkernIsKS. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hkerns0 as (HkernIsKSs0 & HnextAddrs0).
      assert(Hexcepts0: forall block, In block (filterOptionPaddr (getKSEntries currentPart s0))
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete sInit
          -> ~In nextKS (getAllPaddrAux [block] s0)).
      {
        intros blockB HblockBMapped HPDchildB. rewrite <-HgetKSEqss0 in HblockBMapped; trivial.
        assert(~In blockB (getAllPaddrBlock startBlock endBlock)).
        {
          apply KSentriesAreBE in HblockBMapped. unfold isBE in *.
          intro Hcontra. rewrite HremovedAddrs in HblockBMapped; trivial.
        }
        specialize(Hexcept blockB HblockBMapped HPDchildB). simpl in Hexcept. simpl.
        rewrite HlookupsEq in Hexcept; trivial. rewrite Hs2 in Hexcept. simpl in Hexcept.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockB) eqn:HbeqSh1BlockB.
        - rewrite <-beqAddrTrue in HbeqSh1BlockB. rewrite HbeqSh1BlockB in *. rewrite HlookupSh1Eqs1s0 in *.
          destruct (lookup blockB (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). simpl. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hexcept.
          simpl in Hexcept. destruct (beqAddr currBlock blockB) eqn:HbeqBlocks.
          + rewrite <-beqAddrTrue in HbeqBlocks. subst blockB. rewrite HlookupCurrBs0. rewrite HnewB in Hexcept.
            auto.
          + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 kern nextKSaddr nextKS Hexcepts0 HkernIsKSs0 HnextAddrs0 HnextKSAddr HbeqNextNull).
      unfold isKS in *. assert(~In nextKS (getAllPaddrBlock startBlock endBlock)).
      {
        apply HPDchildImpls0 in HPDchildCBs0; trivial. apply Hexcepts0 in HPDchildCBs0; trivial.
        rewrite Hranges0 in *. assumption.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) nextKS) eqn:HbeqSh1Next.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *.
        destruct (lookup nextKS (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock nextKS) eqn:HbeqCBNext.
      - rewrite HnewB. rewrite <-beqAddrTrue in HbeqCBNext. rewrite <-HbeqCBNext in *.
        rewrite HlookupCurrBs0 in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END NextKSIsKS *)
    }

    assert(NextKSOffsetIsPADDR s).
    { (* BEGIN NextKSOffsetIsPADDR s *)
      assert(Hcons0: NextKSOffsetIsPADDR s0) by (unfold deleteProps in *; intuition). clear HlookupBTDs.
      intros kern nextKSaddr HkernIsKS HnextAddr. unfold nextKSAddr in *.
      unfold isKS in HkernIsKS. assert(HkernNotInRange: ~In kern (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HnextAddr; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HnextAddr. rewrite Hs2 in HkernIsKS. simpl in HnextAddr.
      simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hkerns0: isKS kern s0 /\ nextKSAddr kern nextKSaddr s0).
      {
        unfold nextKSAddr. unfold isKS. rewrite Hs1 in HnextAddr. rewrite Hs1 in HkernIsKS. simpl in HnextAddr.
        simpl in HkernIsKS. destruct (beqAddr currBlock kern) eqn:HbeqCBKern.
        - rewrite <-beqAddrTrue in HbeqCBKern. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in HkernIsKS. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hkerns0 as (HkernIsKSs0 & HnextAddrs0).
      specialize(Hcons0 kern nextKSaddr HkernIsKSs0 HnextAddrs0). destruct Hcons0 as (HnextaIsPADDR & HbeqNextaNull).
      split; trivial. unfold isPADDR in *. assert(~In nextKSaddr (getAllPaddrBlock startBlock endBlock)).
      {
        assert(HnextInSameB: blockAndNextInSameBlock s0) by (unfold deleteProps in *; intuition).
        intro Hcontra. rewrite <-Hranges0 in *. destruct (lookup kern (memory s1) beqAddr); try(congruence).
        destruct v; try(congruence). subst nextKSaddr.
        specialize(HnextInSameB currentPart kern currBlock HcurrIsPart HCBMapped HkernIsKSs0 Hcontra). congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) nextKSaddr) eqn:HbeqSh1Nexta.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Nexta. rewrite HbeqSh1Nexta in *.
        destruct (lookup nextKSaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock nextKSaddr) eqn:HbeqCBNexta.
      {
        rewrite <-beqAddrTrue in HbeqCBNexta. rewrite HbeqCBNexta in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END NextKSOffsetIsPADDR *)
    }

    assert(NoDupInFreeSlotsList s).
    { (* BEGIN NoDupInFreeSlotsList s *)
      assert(Hcons0: NoDupInFreeSlotsList s0) by (unfold deleteProps in *; intuition).
      intros partition HpartPart. rewrite HgetPartsEqss0 in *. specialize(Hcons0 partition HpartPart).
      rewrite HgetFreeEqss0; trivial.
      (* END NoDupInFreeSlotsList *)
    }

    assert(freeSlotsListIsFreeSlot s).
    { (* BEGIN freeSlotsListIsFreeSlot s *)
      assert(Hcons0: freeSlotsListIsFreeSlot s0) by (unfold deleteProps in *; intuition).
      intros partition addr optionfreeslotslist freeslotslist HpartIsPDT HpartIsPart HwellFormed HaddrInList
        HbeqAddrNull. rewrite HgetPartsEqss0 in *. rewrite HgetFreeEqss0 in *; trivial. clear HlookupBTDs.
      unfold isPDT in *. assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy partition Hcontra).
        destruct HpropsAddrToRemoveCopy as (HpartNotPart & _). congruence.
      }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HpartIsPDT. simpl in HpartIsPDT.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HpartIsPDT.
      simpl in HpartIsPDT. destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition addr optionfreeslotslist freeslotslist HpartIsPDT HpartIsPart HwellFormed
        HaddrInList HbeqAddrNull). unfold isFreeSlot in *.
      assert(~In addr (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy addr Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & HaddrNotEntry & _). specialize(HaddrNotEntry partition HpartIsPart).
        destruct HaddrNotEntry as (HaddrNotEntry & _). contradict HaddrNotEntry.
        assert(Hincl: inclFreeSlotsBlockEntries s0) by (unfold deleteProps in *; intuition).
        specialize(Hincl partition HpartIsPart (SomePaddr addr)). apply optionIsInFilter. apply Hincl.
        destruct HaddrInList as (HeqList & HaddrInList). subst freeslotslist. apply optionIsInFilter in HaddrInList.
        destruct HwellFormed as (HeqList & _). subst optionfreeslotslist. assumption.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *.
        destruct (lookup addr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
      {
        rewrite <-beqAddrTrue in HbeqCBAddr. rewrite HbeqCBAddr in *. unfold bentryPFlag in *.
        rewrite HlookupCurrBs0 in *. exfalso.
        destruct (lookup (CPaddr (addr+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
        destruct (lookup (CPaddr (addr+scoffset)) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
        destruct Hcons0 as (_ & _ & _ & _ & Hcons0 & _). congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      destruct (lookup addr (memory s0) beqAddr) eqn:HlookupAddr; try(congruence). destruct v; try(congruence).
      assert(~In (CPaddr (addr+sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      {
        rewrite <-Hranges0 in *. intro Hcontra.
        assert(HaddrIsBE: isBE addr s0) by (unfold isBE; rewrite HlookupAddr; trivial).
        assert(Hsh1InSameB: blockAndSh1InSameBlock s0) by (unfold deleteProps in *; intuition).
        specialize(Hsh1InSameB currentPart addr currBlock HcurrIsPart HCBMapped HaddrIsBE Hcontra). congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (addr + sh1offset))) eqn:HbeqSh1s.
      {
        rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (addr+sh1offset))) eqn:HbeqCBSh1.
      {
        rewrite <-beqAddrTrue in HbeqCBSh1. rewrite <-HbeqCBSh1 in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      destruct (lookup (CPaddr (addr+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      assert(~In (CPaddr (addr+scoffset)) (getAllPaddrBlock startBlock endBlock)).
      {
        rewrite <-Hranges0 in *. intro Hcontra.
        assert(HaddrIsBE: isBE addr s0) by (unfold isBE; rewrite HlookupAddr; trivial).
        assert(HsceInSameB: blockAndSceInSameBlock s0) by (unfold deleteProps in *; intuition).
        specialize(HsceInSameB currentPart addr currBlock HcurrIsPart HCBMapped HaddrIsBE Hcontra). congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (addr + scoffset))) eqn:HbeqSh1Sce.
      {
        rewrite <-beqAddrTrue in HbeqSh1Sce. rewrite HbeqSh1Sce in *. rewrite HlookupSh1Eqs1s0 in *.
        destruct (lookup (CPaddr (addr+scoffset)) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (addr+scoffset))) eqn:HbeqCBSce.
      {
        rewrite <-beqAddrTrue in HbeqCBSce. rewrite <-HbeqCBSce in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END freeSlotsListIsFreeSlot *)
    }

    assert(DisjointFreeSlotsLists s).
    { (* BEGIN DisjointFreeSlotsLists s *)
      assert(Hcons0: DisjointFreeSlotsLists s0) by (unfold deleteProps in *; intuition).
      intros part1 part2 Hpart1IsPart Hpart2IsPart HbeqParts. rewrite HgetPartsEqss0 in *.
      rewrite HgetFreeEqss0; trivial. specialize(Hcons0 part1 part2 Hpart1IsPart Hpart2IsPart HbeqParts).
      rewrite HgetFreeEqss0; trivial.
      (* END DisjointFreeSlotsLists *)
    }

    assert(inclFreeSlotsBlockEntries s).
    { (* BEGIN inclFreeSlotsBlockEntries s *)
      assert(Hcons0: inclFreeSlotsBlockEntries s0) by (unfold deleteProps in *; intuition).
      intros partition HpartIsPart. rewrite HgetPartsEqss0 in *. specialize(Hcons0 partition HpartIsPart).
      rewrite HgetFreeEqss0; trivial. rewrite HgetKSEqss0; trivial.
      (* END inclFreeSlotsBlockEntries *)
    }

    assert(DisjointKSEntries s).
    { (* BEGIN DisjointKSEntries s *)
      assert(Hcons0: DisjointKSEntries s0) by (unfold deleteProps in *; intuition).
      intros part1 part2 Hpart1IsPart Hpart2IsPart HbeqParts. rewrite HgetPartsEqss0 in *.
      specialize(Hcons0 part1 part2 Hpart1IsPart Hpart2IsPart HbeqParts). rewrite HgetKSEqss0; trivial.
      rewrite HgetKSEqss0; trivial.
      (* END DisjointKSEntries *)
    }

    assert(noDupPartitionTree s).
    { (* BEGIN noDupPartitionTree s *)
      assert(Hcons0: noDupPartitionTree s0) by (unfold deleteProps in *; intuition). unfold noDupPartitionTree.
      rewrite HgetPartsEqss0. assumption.
      (* END noDupPartitionTree *)
    }

    assert(forall partition pdparent,
        partition <> blockToDelete
        -> In pdparent (getPartitions multiplexer s)
        -> In partition (getChildren pdparent s) -> pdentryParent partition pdparent s).
    { (* BEGIN isParent s *)
      assert(Hcons0: forall partition pdparent,
          partition <> blockToDelete
          -> In pdparent (getPartitions multiplexer s0)
          -> In partition (getChildren pdparent s0) -> pdentryParent partition pdparent s0)
        by (unfold deleteProps in *; intuition).
      intros partition pdparent HbeqPartBTD HparentIsPart HpartIsChild. rewrite HgetPartsEqss0 in *.
      rewrite HgetChildrenEqss0 in *; trivial.
      specialize(Hcons0 partition pdparent HbeqPartBTD HparentIsPart HpartIsChild). unfold pdentryParent in *.
      assert(In partition (getPartitions multiplexer s0)).
      {
        apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition.
      }
      assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy partition Hcontra).
        destruct HpropsAddrToRemoveCopy as (HpartNotPart & _). congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Part. rewrite HbeqSh1Part in *.
        destruct (lookup partition (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock partition) eqn:HbeqCBPart.
      {
        rewrite <-beqAddrTrue in HbeqCBPart. subst partition. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END isParent *)
    }

    assert(isChild s).
    { (* BEGIN isChild s *)
      assert(Hcons0: isChild s0) by (unfold deleteProps in *; intuition).
      intros partition pdparent HpartIsPart HparentIsParent HbeqPartRoot. rewrite HgetPartsEqss0 in *.
      unfold pdentryParent in *. assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HparentIsParent; trivial. }
      rewrite HlookupsEq in HparentIsParent; trivial. rewrite Hs2 in HparentIsParent. simpl in HparentIsParent.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HparentIsParent.
      simpl in HparentIsParent. destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
      rewrite HgetChildrenEqss0; trivial.
      assert(HparentOfPart: exists wrongParts,
            (forall partition entry,
              lookup partition (memory s0) beqAddr = Some (PDT entry)
              -> (~In (parent entry) wrongParts
                  -> partition <> constantRootPartM
                  -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                      /\ In (parent entry) (getPartitions multiplexer s0))
                /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
            /\ (forall oldPart, In oldPart wrongParts
                -> (forall desc, In desc (getPartitions oldPart s0)
                    -> desc <> blockToDelete
                    -> ~In desc (getPartitions multiplexer s0))))
          by (unfold deleteProps in *; intuition).
      destruct HparentOfPart as [wrongParts (HparentOfPart & HwrongParts)].
      destruct (lookup partition (memory s0) beqAddr) eqn:HlookupPart; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). subst pdparent.
      assert(HparentNotWrong: ~In (parent p) wrongParts).
      {
        intro Hcontra. specialize(HwrongParts (parent p) Hcontra).
        assert(HpartIsDesc: In partition (getPartitions (parent p) s0)).
        {
          unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); only 2: lia. simpl. right.
          induction (getChildren (parent p) s0); simpl in *; only 1: congruence. apply in_or_app.
          destruct Hcons0 as [Heq | Hcons0]; auto. subst a1. left.
          replace (maxAddr+1) with (S maxAddr); only 2: lia. simpl. auto.
        }
        assert(HbeqPartBTD: partition <> blockToDelete) by (intro; subst partition; congruence).
        specialize(HwrongParts partition HpartIsDesc HbeqPartBTD). congruence.
      }
      specialize(HparentOfPart partition p HlookupPart).
      destruct HparentOfPart as (HparentIsPart & _). apply HparentIsPart; assumption.
      (* END isChild *)
    }

    assert(noDupKSEntriesList s).
    { (* BEGIN noDupKSEntriesList s *)
      assert(Hcons0: noDupKSEntriesList s0) by (unfold deleteProps in *; intuition).
      intros partition HpartIsPart. rewrite HgetPartsEqss0 in *. specialize(Hcons0 partition HpartIsPart).
      rewrite HgetKSEqss0; assumption.
      (* END noDupKSEntriesList *)
    }

    assert(wellFormedBlock s).
    { (* BEGIN wellFormedBlock s *)
      assert(Hcons0: wellFormedBlock s0) by (unfold deleteProps in *; intuition).
      intros block startaddr endaddr HPflag HstartBlock HendBlock. unfold bentryPFlag in *. unfold bentryEndAddr in *.
      unfold bentryStartAddr in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HPflag; trivial. }
      clear HlookupBTDs. rewrite HlookupsEq in *; trivial. rewrite Hs2 in HPflag. rewrite Hs2 in HstartBlock.
      rewrite Hs2 in HendBlock. simpl in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: bentryPFlag block true s0 /\ bentryStartAddr block startaddr s0
        /\ bentryEndAddr block endaddr s0).
      {
        unfold bentryPFlag. unfold bentryStartAddr. unfold bentryEndAddr. rewrite Hs1 in HPflag.
        rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock. simpl in *.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (HPflags0 & HstartBlocks0 & HendBlocks0).
      specialize(Hcons0 block startaddr endaddr HPflags0 HstartBlocks0 HendBlocks0). assumption.
      (* END wellFormedBlock *)
    }

    assert(exists wrongParts,
          (forall partition entry,
            lookup partition (memory s) beqAddr = Some (PDT entry)
            -> (~In (parent entry) wrongParts
                -> partition <> constantRootPartM
                -> (exists parentEntry, lookup (parent entry) (memory s) beqAddr = Some (PDT parentEntry))
                    /\ In (parent entry) (getPartitions multiplexer s))
              /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
          /\ (forall oldPart, In oldPart wrongParts
              -> (forall desc, In desc (getPartitions oldPart s)
                  -> desc <> blockToDelete
                  -> ~In desc (getPartitions multiplexer s)))).
    { (* BEGIN parentOfPartitionIsPartition s *)
      assert(Hcons0: exists wrongParts,
          (forall partition entry,
            lookup partition (memory s0) beqAddr = Some (PDT entry)
            -> (~In (parent entry) wrongParts
                -> partition <> constantRootPartM
                -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                    /\ In (parent entry) (getPartitions multiplexer s0))
              /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
          /\ (forall oldPart, In oldPart wrongParts
              -> (forall desc, In desc (getPartitions oldPart s0)
                  -> desc <> blockToDelete
                  -> ~In desc (getPartitions multiplexer s0)))) by (unfold deleteProps in *; intuition).
      destruct Hcons0 as [wrongParts (HparentOfPart & HwrongParts)]. exists wrongParts. split.
      - intros partition pdentry HlookupPart.
        assert(~In partition (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HlookupPart; trivial. exfalso; congruence. }
        rewrite HlookupsEq in HlookupPart; trivial. rewrite Hs2 in HlookupPart. simpl in HlookupPart.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart.
        simpl in HlookupPart. destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(HparentOfPart partition pdentry HlookupPart).
        destruct HparentOfPart as (HparentIsPart & HparentOfPart). split; trivial.
        intros HparentNotWrong HbeqPartRoot. specialize(HparentIsPart HparentNotWrong HbeqPartRoot).
        rewrite HgetPartsEqss0. destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
        split; trivial. assert(~In (parent pdentry) (getAllPaddrBlock startBlock endBlock)).
        {
          intro Hcontra. specialize(HpropsAddrToRemoveCopy (parent pdentry) Hcontra).
          destruct HpropsAddrToRemoveCopy as (HparentNotPart & _). congruence.
        }
        rewrite HlookupsEq; trivial. exists parentEntry. rewrite Hs2. simpl.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) (parent pdentry)) eqn:HbeqSh1Parent.
        {
          rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Parent. rewrite HbeqSh1Parent in *.
          rewrite HlookupParent in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock (parent pdentry)) eqn:HbeqCBParent.
        {
          rewrite <-beqAddrTrue in HbeqCBParent. rewrite <-HbeqCBParent in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      - intros oldPart HoldIsWrong desc HdescIsDesc HbeqDescBTD. rewrite HgetPartsEqss0.
        apply HgetPartsGenEqss0 in HdescIsDesc.
        specialize(HwrongParts oldPart HoldIsWrong desc HdescIsDesc HbeqDescBTD). assumption.
      (* END parentOfPartitionIsPartition *)
    }

    assert(NbFreeSlotsISNbFreeSlotsInList s).
    { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
      assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0) by (unfold deleteProps in *; intuition).
      intros partition nbfreeslots HpartIsPart HnbFree. rewrite HgetPartsEqss0 in *. unfold pdentryNbFreeSlots in *.
      assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. apply HremovedAddrs in Hcontra. rewrite Hcontra in *. congruence. }
      rewrite HlookupsEq in HnbFree; trivial. rewrite Hs2 in HnbFree. simpl in HnbFree.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HnbFree. simpl in HnbFree.
      destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition nbfreeslots HpartIsPart HnbFree). rewrite HgetFreeEqss0; assumption.
      (* END NbFreeSlotsISNbFreeSlotsInList *)
    }

    assert(HkernListImpls2s0: forall kernList partition, isListOfKernels kernList partition s2
      -> isListOfKernels kernList partition s0).
    {
      intros kernList partition HkernLists2. assert(HkernLists1: isListOfKernels kernList partition s1).
      { revert HkernLists2. rewrite Hs2. apply IL.isListOfKernelsEqSHE. }
      revert HkernLists1. rewrite Hs1. apply IL.isListOfKernelsEqBE.
    }

    assert(HkernListImplss0: forall kernList partition, isListOfKernels kernList partition s
      -> isListOfKernels kernList partition s0).
    {
      intros kernList partition HkernLists. apply HkernListImpls2s0. unfold isListOfKernels in *.
      destruct kernList as [| kern kernList]; trivial.
      destruct HkernLists as [pdentry (HlookupPart & HbeqStructNull & Hstruct & HkernLists)].
      rewrite HlookupsEq in HlookupPart; only 2: (intro Hcontra; apply HremovedAddrs in Hcontra; congruence).
      exists pdentry. split; trivial. split; trivial. split; trivial. clear Hstruct. revert kern HkernLists.
      induction kernList; intros; simpl in *; trivial.
      destruct HkernLists as (HlookupNext & HlebNextMax & HbeqA1Null & HkernLists).
      rewrite HlookupsEq in HlookupNext; only 2: (intro Hcontra; apply HremovedAddrs in Hcontra; congruence). auto.
    }

    assert(maxNbPrepareIsMaxNbKernels s).
    { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
      assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by (unfold deleteProps in *; intuition).
      intros partition kernList HpartIsPart HlistOfKerns. apply HkernListImplss0 in HlistOfKerns.
      rewrite HgetPartsEqss0 in *. specialize(Hcons0 partition kernList HpartIsPart HlistOfKerns). assumption.
      (* END maxNbPrepareIsMaxNbKernels *)
    }

    assert(blockInChildHasAtLeastEquivalentBlockInParent s).
    { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
      assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0) by (unfold deleteProps in *; intuition).
      intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild HstartChild
        HendChild HPflagChild. rewrite HgetPartsEqss0 in *. rewrite HgetChildrenEqss0 in *; trivial.
      assert(In child (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition. }
      rewrite HgetMappedBEqss0 in *; trivial. unfold bentryPFlag in HPflagChild. unfold bentryEndAddr in HendChild.
      unfold bentryStartAddr in HstartChild. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. apply HremovedAddrs in Hcontra. rewrite Hcontra in *. congruence. }
      clear HlookupBTDs. rewrite HlookupsEq in *; trivial. rewrite Hs2 in HstartChild. rewrite Hs2 in HendChild.
      rewrite Hs2 in HPflagChild. simpl in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: bentryStartAddr block startChild s0 /\ bentryEndAddr block endChild s0
        /\ bentryPFlag block true s0).
      {
        rewrite Hs1 in HstartChild. rewrite Hs1 in HendChild. rewrite Hs1 in HPflagChild. simpl in *.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. unfold bentryStartAddr. unfold bentryEndAddr.
          unfold bentryPFlag. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (HstartChilds0 & HendChilds0 & HPflagChilds0).
      specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
        HstartChilds0 HendChilds0 HPflagChilds0).
      destruct Hcons0 as [blockParent [startParent [endParent (HblockParMapped & HstartPar & HendPar & Hbounds)]]].
      exists blockParent. exists startParent. exists endParent. unfold bentryStartAddr in *.
      unfold bentryEndAddr in *. assert(~In blockParent (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy blockParent Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & HBPNotKS & _). specialize(HBPNotKS pdparent HparentIsPart).
        destruct HBPNotKS as (HBPNotKS & _). unfold getMappedBlocks in *.
        apply DTL.InFilterPresentInList in HblockParMapped. congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockParent) eqn:HbeqSh1BP.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1BP. rewrite HbeqSh1BP in *. exfalso.
        destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      assert(HBPs1: bentryStartAddr blockParent startParent s1 /\ bentryEndAddr blockParent endParent s1).
      {
        unfold bentryStartAddr. unfold bentryEndAddr. rewrite Hs1. simpl.
        destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
        - rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      destruct HBPs1. auto.
      (* END blockInChildHasAtLeastEquivalentBlockInParent *)
    }

    assert(HparentsListImplss0: forall parentsList part, isParentsList s parentsList part
      -> isParentsList s0 parentsList part).
    {
      intros parentsList part HparentsLists. assert(HparentsLists2: isParentsList s2 parentsList part).
      {
        revert part HparentsLists. induction parentsList as [| pdparent parentsList]; simpl; intros; trivial.
        assert(~In pdparent (getAllPaddrBlock startBlock endBlock)).
        { intro Hcontra. rewrite HremovedAddrs in HparentsLists; trivial. }
        rewrite HlookupsEq in HparentsLists; trivial.
        destruct (lookup pdparent (memory s2) beqAddr); try(congruence). destruct v; try(congruence).
        destruct HparentsLists as (HbeqPartRoot & [pdentry (HlookupPart & Hparent)] & HparentsLists). split; trivial.
        split; auto. exists pdentry. split; trivial. rewrite <-HlookupsEq; trivial. intro Hcontra.
        rewrite HremovedAddrs in HlookupPart; trivial. congruence.
      }
      assert(HparentsLists1: isParentsList s1 parentsList part).
      {
        assert(HpropsOr: isParentsList s1 parentsList part
          \/ exists pdentry, lookup part (memory s1) beqAddr = Some (PDT pdentry)).
        {
          destruct parentsList; simpl in *; auto. right.
          destruct (lookup p (memory s2) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
          destruct HparentsLists2 as (_ & [pdentry (HlookupPart & _)] & _). exists pdentry.
          rewrite Hs2 in HlookupPart. simpl in HlookupPart.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        destruct HpropsOr as [Hres | HlookupPart]; trivial. revert HparentsLists2. rewrite Hs2.
        destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s1) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
        destruct v; try(exfalso; congruence). apply isParentsListEqSHERevBis with s3; trivial.
      }
      assert(HpropsOr: isParentsList s0 parentsList part
        \/ exists pdentry, lookup part (memory s0) beqAddr = Some (PDT pdentry)).
      {
        destruct parentsList; simpl in *; auto. right.
        destruct (lookup p (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        destruct HparentsLists1 as (_ & [pdentry (HlookupPart & _)] & _). exists pdentry.
        rewrite Hs1 in HlookupPart. simpl in HlookupPart.
        destruct (beqAddr currBlock part) eqn:HbeqSh1Part; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct HpropsOr as [Hres | HlookupPart]; trivial.
      revert HparentsLists1. rewrite Hs1. apply isParentsListEqBERevBis with bentry0; trivial.
    }

    assert(partitionTreeIsTree s).
    { (* BEGIN partitionTreeIsTree s *)
      assert(Hcons0: partitionTreeIsTree s0) by (unfold deleteProps in *; intuition).
      intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList.
      rewrite HgetPartsEqss0 in *. apply HparentsListImplss0 in HparentsList. unfold pdentryParent in *.
      assert(~In child (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HparentIsParent; trivial. }
      rewrite HlookupsEq in HparentIsParent; trivial. rewrite Hs2 in HparentIsParent. simpl in HparentIsParent.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) child) eqn:HbeqSh1Child; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HparentIsParent.
      simpl in HparentIsParent. destruct (beqAddr currBlock child) eqn:HbeqCBChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsParent HparentsList).
      assumption.
      (* END partitionTreeIsTree *)
    }

    assert(HcomplKernLEq: forall part pdentry, In part (getPartitions multiplexer s0)
      -> lookup part (memory s0) beqAddr = Some (PDT pdentry)
      -> completeListOfKernels (structure pdentry) s = completeListOfKernels (structure pdentry) s0).
    {
      intros part pdentry HpartIsPart HlookupPart. rewrite <-HcomplKernLEqs2s0. rewrite <-HgetPartsEqs2s0 in *.
      assert(HlookupParts2: lookup part (memory s2) beqAddr = Some (PDT pdentry)).
      {
        rewrite Hs2. simpl. destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part.
        {
          rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Part. subst part. rewrite HlookupPart in *.
          exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock part) eqn:HbeqCBPart.
        { rewrite <-beqAddrTrue in HbeqCBPart. subst part. congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      }
      destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
      - rewrite <-beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. unfold completeListOfKernels.
        unfold nullAddrExists in *. unfold isPADDR in *.
        destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        destruct (lookup nullAddr (memory s2) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). reflexivity.
      - rewrite <-beqAddrFalse in *. specialize (Hstructs2 part pdentry HpartIsPart HlookupParts2 HbeqStructNull).
        apply completeListOfKernelsEqNoImpact with (maxIdx+1) part pdentry startBlock endBlock; trivial.
        + unfold completeListOfKernels. unfold isKS in *.
          destruct (lookup (structure pdentry) (memory s2) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). rewrite Hstructs2. rewrite IL.indexEqRefl. cbn -[maxNbPrepare]. auto.
        + pose proof maxNbPrepareNbLessThanMaxIdx. lia.
        + intros addr HaddrInRange. specialize(HpropsForStructEqs2 addr HaddrInRange).
          destruct HpropsForStructEqs2 as (_ & HaddrNotConfig & _). specialize(HaddrNotConfig part HpartIsPart).
          unfold getConfigPaddr in *. apply Lib.in_app_or_neg in HaddrNotConfig.
          destruct HaddrNotConfig as (_ & HaddrNotConfig). unfold getConfigBlocks in *. rewrite HlookupParts2 in *.
          assumption.
    }

    assert(HlookupCurrs2: lookup currentPart (memory s2) beqAddr = Some (PDT pdentryCurr)).
    {
      rewrite Hs2. simpl. destruct (beqAddr (CPaddr (currBlock + sh1offset)) currentPart) eqn:HbeqSh1Curr.
      {
        rewrite <-beqAddrTrue in HbeqSh1Curr. rewrite HbeqSh1Curr in *. rewrite HlookupSh1Eqs1s0 in *.
        rewrite HlookupCurr in *. exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock currentPart) eqn:HbeqCBCurr.
      { rewrite <-beqAddrTrue in HbeqCBCurr. subst currentPart. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(In kernel (completeListOfKernels (structure pdentryCurr) s)).
    { rewrite HcomplKernLEq with (part:=currentPart); assumption. }
    assert(HkernCIsKSs2: isKS kernel s2).
    {
      unfold isKS in *. rewrite Hs2. simpl. destruct (beqAddr (CPaddr (currBlock+sh1offset)) kernel) eqn:HbeqSh1Kern.
      {
        rewrite <-beqAddrTrue in HbeqSh1Kern. rewrite HbeqSh1Kern in *.
        destruct (lookup kernel (memory s1) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(HcomplKernLEqKern: completeListOfKernels kernel s = completeListOfKernels kernel s0).
    {
      rewrite <-HcomplKernLEqs2s0. rewrite <-HgetPartsEqs2s0 in *.
      apply completeListOfKernelsEqNoImpact with (maxIdx+1) currentPart pdentryCurr startBlock endBlock; trivial.
      - rewrite HcomplKernLEqs2s0. assumption.
      - pose proof maxNbPrepareNbLessThanMaxIdx. lia.
      - intros addr HaddrInRange. specialize(HpropsForStructEqs2 addr HaddrInRange).
        destruct HpropsForStructEqs2 as (_ & HaddrNotConfig & _). specialize(HaddrNotConfig currentPart HcurrIsPart).
        unfold getConfigPaddr in *. apply Lib.in_app_or_neg in HaddrNotConfig.
        destruct HaddrNotConfig as (_ & HaddrNotConfig).
        assert(HconfigEq: getConfigBlocks currentPart s2 = completeListOfKernels (structure pdentryCurr) s2).
        { apply completeKernListIsConfig; assumption. }
        destruct (beqAddr (structure pdentryCurr) kernel) eqn:HbeqStructKern.
        + rewrite <-beqAddrTrue in HbeqStructKern. subst kernel. unfold getConfigBlocks in HaddrNotConfig.
          rewrite HlookupCurrs2 in *. assumption.
        + rewrite <-beqAddrFalse in *.
          assert(HcomplIsKL: isListOfKernels (completeListOfKernels (structure pdentryCurr) s2) currentPart s2).
          { apply completeKernListIsListOfKern; assumption. }
          specialize(HmaxPrepIsMaxLen currentPart (completeListOfKernels (structure pdentryCurr) s2) HcurrIsPart
            HcomplIsKL).
          assert(HconfigAuxEq: filterOptionPaddr (getConfigBlocksAux (maxIdx+1) kernel s2 (CIndex maxNbPrepare))
            = kernel::completeListOfKernelsAux (CIndex maxNbPrepare) kernel s2).
          {
            pose proof maxNbPrepareNbLessThanMaxIdx. unfold CIndex.
            destruct (Compare_dec.le_dec maxNbPrepare maxIdx); try(lia).
            apply completeKernListIsConfigAux with currentPart pdentryCurr; trivial.
            - rewrite HcomplKernLEqs2s0. assumption.
            - simpl. lia.
            - simpl i. rewrite <-HcomplKernLEqs2s0 in *. unfold completeListOfKernels in *.
              destruct (lookup (structure pdentryCurr) (memory s2) beqAddr);
                try(simpl in HkernCIsConfigs0; exfalso; congruence).
              destruct v; try(simpl in HkernCIsConfigs0; exfalso; congruence).
              destruct (indexEq (blockindex b) (CIndex 0)); try(simpl in HkernCIsConfigs0; exfalso; congruence).
              cbn -[maxNbPrepare] in HkernCIsConfigs0. cbn -[maxNbPrepare] in HmaxPrepIsMaxLen.
              destruct HkernCIsConfigs0 as [Hcontra | HkernCIsConfigs0]; try(exfalso; congruence).
              cbn -[maxNbPrepare]. revert HmaxPrepIsMaxLen HkernCIsConfigs0. generalize maxNbPrepare as bound.
              intro. generalize (structure pdentryCurr) as kernInit. induction bound; simpl; intros; try(lia).
              destruct (lookup (CPaddr (kernInit+nextoffset)) (memory s2) beqAddr);
                try(simpl in HkernCIsConfigs0; exfalso; congruence).
              destruct v; try(simpl in HkernCIsConfigs0; exfalso; congruence).
              destruct (beqAddr p nullAddr); try(simpl in HkernCIsConfigs0; exfalso; congruence).
              assert(HgebLen: S (length (completeListOfKernelsAux bound p s2)) <= bound)
                by (simpl in HmaxPrepIsMaxLen; lia). specialize(IHbound p HgebLen).
              simpl in HkernCIsConfigs0. destruct HkernCIsConfigs0 as [Heq | HkernCIsConfigs0].
              + subst p. assert(Heq: completeListOfKernelsAux bound kernel s2
                  = completeListOfKernelsAux (S bound) kernel s2).
                { apply completeListOfKernelsAuxN; lia. }
                rewrite Heq in HgebLen. auto.
              + specialize(IHbound HkernCIsConfigs0). assert(Heq: completeListOfKernelsAux bound kernel s2
                  = completeListOfKernelsAux (S bound) kernel s2).
                { apply completeListOfKernelsAuxN; lia. }
                rewrite Heq in IHbound. auto.
          }
          rewrite HconfigAuxEq. rewrite HconfigEq in *. rewrite <-HcomplKernLEqs2s0 in *.
          unfold completeListOfKernels in *. pose proof maxNbPrepareNbLessThanMaxIdx. unfold CIndex.
          destruct (Compare_dec.le_dec maxNbPrepare maxIdx); try(lia). simpl i.
          destruct (lookup (structure pdentryCurr) (memory s2) beqAddr) eqn:HlookupStruct;
            try(simpl in HkernCIsConfigs0; exfalso; congruence).
          destruct v; try(simpl in HkernCIsConfigs0; exfalso; congruence).
          destruct (indexEq (blockindex b) (CIndex 0)); try(simpl in HkernCIsConfigs0; exfalso; congruence).
          cbn -[maxNbPrepare] in HkernCIsConfigs0. cbn -[maxNbPrepare] in HmaxPrepIsMaxLen.
          destruct HkernCIsConfigs0 as [Hcontra | HkernCIsConfigs0]; try(exfalso; congruence).
          cbn -[maxNbPrepare] in HaddrNotConfig. rewrite HlookupStruct in *.
          apply Lib.in_app_or_neg in HaddrNotConfig. destruct HaddrNotConfig as (_ & HaddrNotConfig).
          revert HaddrNotConfig HmaxPrepIsMaxLen HkernCIsConfigs0. generalize maxNbPrepare as bound.
          intro. generalize (structure pdentryCurr) as kernInit.
          induction bound; intros; try(simpl in HmaxPrepIsMaxLen; lia). simpl in HmaxPrepIsMaxLen.
          simpl in HkernCIsConfigs0. simpl in HaddrNotConfig.
          destruct (lookup (CPaddr (kernInit+nextoffset)) (memory s2) beqAddr);
            try(simpl in HkernCIsConfigs0; exfalso; congruence).
          destruct v; try(simpl in HkernCIsConfigs0; exfalso; congruence).
          destruct (beqAddr p nullAddr); try(simpl in HkernCIsConfigs0; exfalso; congruence).
          assert(HgebLen: S (length (completeListOfKernelsAux bound p s2)) <= bound)
            by (simpl in HmaxPrepIsMaxLen; lia).
          simpl in HkernCIsConfigs0. destruct HkernCIsConfigs0 as [Heq | HkernCIsConfigs0].
          * subst p.
            assert(Heq: completeListOfKernelsAux bound kernel s2 = completeListOfKernelsAux (S bound) kernel s2).
            { apply completeListOfKernelsAuxN; lia. }
            rewrite <-Heq. assumption.
          * assert(HaddrNotConfigRec: ~In addr (getAllPaddrConfigAux (completeListOfKernelsAux bound p s2) s2)).
            {
              simpl in HaddrNotConfig. destruct (lookup p (memory s2) beqAddr); trivial. destruct v; trivial.
              apply Lib.in_app_or_neg in HaddrNotConfig. apply HaddrNotConfig.
            }
            specialize(IHbound p HaddrNotConfigRec HgebLen HkernCIsConfigs0).
            assert(Heq: completeListOfKernelsAux bound kernel s2 = completeListOfKernelsAux (S bound) kernel s2).
            {
              apply completeListOfKernelsAuxN; try(lia).
              assert(HgtLen: length (completeListOfKernelsAux bound p s2) < bound) by lia.
              revert HgtLen HkernCIsConfigs0. generalize bound as boundR. intro. generalize p as kern.
              induction boundR; intros; simpl in HkernCIsConfigs0; try(exfalso; congruence). simpl in HgtLen.
              destruct (lookup (CPaddr (kern+nextoffset)) (memory s2) beqAddr);
                try(simpl in HkernCIsConfigs0; exfalso; congruence).
              destruct v; try(simpl in HkernCIsConfigs0; exfalso; congruence).
              destruct (beqAddr p0 nullAddr); try(simpl in HkernCIsConfigs0; exfalso; congruence).
              assert(HgtLenB: length (completeListOfKernelsAux boundR p0 s2) < boundR)
                by (simpl in HgtLen; lia). specialize(IHboundR p0 HgtLenB).
              simpl in HkernCIsConfigs0. destruct HkernCIsConfigs0 as [Heq | HkernCIsConfigs0].
              --- subst p0. assert(Heq: completeListOfKernelsAux boundR kernel s2
                    = completeListOfKernelsAux (S boundR) kernel s2).
                  { apply completeListOfKernelsAuxN; lia. }
                  rewrite <-Heq. lia.
              --- specialize(IHboundR HkernCIsConfigs0). assert(Heq: completeListOfKernelsAux boundR kernel s2
                    = completeListOfKernelsAux (S boundR) kernel s2).
                  { apply completeListOfKernelsAuxN; lia. }
                  rewrite <-Heq. lia.
            }
            rewrite <-Heq. assumption.
    }

    assert(nextKernelIsValid s).
    { (* BEGIN nextKernelIsValid s *)
      assert(Hcons0: nextKernelIsValid s0) by (unfold deleteProps in *; intuition).
      intros part pdentry kern HpartIsPart HlookupPart HkernIsConfig HkernIsKS. rewrite HgetPartsEqss0 in *.
      assert(~In part (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupPart; trivial. congruence. }
      rewrite HlookupsEq in HlookupPart; trivial. unfold isKS in *.
      assert(~In kern (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HkernIsKS; trivial. }
      rewrite HlookupsEq in HkernIsKS; trivial. rewrite Hs2 in HkernIsKS. rewrite Hs2 in HlookupPart.
      simpl in HkernIsKS. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart.
      simpl in HlookupPart. destruct (beqAddr currBlock part) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS. destruct (beqAddr currBlock kern) eqn:HbeqCBKern.
        - rewrite <-beqAddrTrue in HbeqCBKern. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite HcomplKernLEq with part pdentry in *; trivial.
      specialize(Hcons0 part pdentry kern HpartIsPart HlookupPart HkernIsConfig HkernIsKSs0).
      destruct Hcons0 as (HlebNextAMax & [nextAddr (HlookupNextA & Hnext)]). split; trivial. exists nextAddr. split.
      - intro Hp. assert(~In {| p := kern+nextoffset; Hp := Hp |} (getAllPaddrBlock startBlock endBlock)).
        {
          intro Hcontra. assert(HnextInSameB: blockAndNextInSameBlock s0) by (unfold deleteProps in *; intuition).
          assert(Heq: {| p := kern+nextoffset; Hp := Hp |} = CPaddr (kern+nextoffset)).
          {
            unfold CPaddr. destruct (Compare_dec.le_dec (kern + nextoffset) maxAddr); try(lia). f_equal.
            apply proof_irrelevance.
          }
          rewrite Heq in *. rewrite <-Hranges0 in *. specialize(HnextInSameB currentPart kern currBlock
            HcurrIsPart HCBMapped HkernIsKSs0 Hcontra). congruence.
        }
        rewrite HlookupsEq; trivial. specialize(HlookupNextA Hp). rewrite Hs2. simpl.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) {| p := kern + nextoffset; Hp := Hp |}) eqn:HbeqSh1NextA.
        {
          rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1NextA. rewrite <-HbeqSh1NextA in *.
          rewrite HlookupNextA in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock {| p := kern + nextoffset; Hp := Hp |}) eqn:HbeqCBNextA.
        {
          rewrite <-beqAddrTrue in HbeqCBNextA. rewrite <-HbeqCBNextA in *. exfalso; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      - destruct Hnext as [(HnextIsKS & HnextIsConfig) | HnextIsNull]; auto. left. split; trivial. unfold isKS in *.
        assert(~In nextAddr (getAllPaddrBlock startBlock endBlock)).
        {
          intro Hcontra. specialize(HpropsAddrToRemoveCopy nextAddr Hcontra).
          destruct HpropsAddrToRemoveCopy as (_ & Hprop & _). specialize(Hprop part HpartIsPart).
          assert(HconfigEq: getConfigBlocks part s0 = completeListOfKernels (structure pdentry) s0).
          {
            apply completeKernListIsConfig; trivial; unfold deleteProps in *; intuition.
          }
          rewrite <-HconfigEq in HnextIsConfig. destruct Hprop as (_ & Hprop). contradict Hprop.
          unfold getConfigPaddr. apply in_or_app. right. apply getAllPaddrConfigAuxIncl; trivial. intro.
          apply configBlocksAreBE.
        }
        rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) nextAddr) eqn:HbeqSh1Next.
        {
          rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *.
          destruct (lookup nextAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock nextAddr) eqn:HbeqCBNext.
        + rewrite HnewB. rewrite <-beqAddrTrue in HbeqCBNext. rewrite <-HbeqCBNext in *.
          rewrite HlookupCurrBs0 in *. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END nextKernelIsValid *)
    }

    assert(noDupListOfKerns s).
    { (* BEGIN noDupListOfKerns s *)
      assert(Hcons0: noDupListOfKerns s0) by (unfold deleteProps in *; intuition).
      intros partition kernList HpartIsPart HlistOfKerns. apply HkernListImplss0 in HlistOfKerns.
      rewrite HgetPartsEqss0 in *. specialize(Hcons0 partition kernList HpartIsPart HlistOfKerns). assumption.
      (* END noDupListOfKerns *)
    }

    assert(MPUsizeIsBelowMax s).
    { (* BEGIN MPUsizeIsBelowMax s *)
      assert(Hcons0: MPUsizeIsBelowMax s0) by (unfold deleteProps in *; intuition).
      intros partition MPUlist HMPU. unfold pdentryMPU in *.
      assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HMPU; trivial. }
      rewrite HlookupsEq in HMPU; trivial. rewrite Hs2 in HMPU. simpl in HMPU.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HMPU. simpl in HMPU.
      destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition MPUlist HMPU). assumption.
      (* END MPUsizeIsBelowMax *)
    }

    assert(originIsParentBlocksStart s).
    { (* BEGIN originIsParentBlocksStart s *)
      assert(Hcons0: originIsParentBlocksStart s0) by (unfold deleteProps in *; intuition).
      intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
      rewrite HgetPartsEqss0 in *. assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupPart; trivial. congruence. }
      rewrite HlookupsEq in HlookupPart; trivial. rewrite Hs2 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart.
      simpl in HlookupPart. destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      rewrite HgetMappedBEqss0 in HblockMapped; trivial. unfold scentryOrigin in *.
      assert(~In scentryaddr (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Horigin; trivial. }
      rewrite HlookupsEq in Horigin; trivial. rewrite Hs2 in Horigin. simpl in Horigin.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) scentryaddr) eqn:HbeqSh1Sce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Horigin.
      simpl in Horigin. destruct (beqAddr currBlock scentryaddr) eqn:HbeqCBSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
        Horigin). destruct Hcons0 as (HinclParent & HlebOriginStart). split.
      - intro HbeqPartRoot. specialize(HinclParent HbeqPartRoot).
        destruct HinclParent as [blockParent (HblockPMapped & HstartBP & HinclParent)]. exists blockParent.
        assert(In (parent pdentry) (getPartitions multiplexer s0)).
        {
          assert(HparentOfPart: exists wrongParts,
              (forall partition entry,
                lookup partition (memory s0) beqAddr = Some (PDT entry)
                -> (~In (parent entry) wrongParts
                    -> partition <> constantRootPartM
                    -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                        /\ In (parent entry) (getPartitions multiplexer s0))
                  /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
              /\ (forall oldPart, In oldPart wrongParts
                  -> (forall desc, In desc (getPartitions oldPart s0)
                      -> desc <> blockToDelete
                      -> ~In desc (getPartitions multiplexer s0))))
            by (unfold deleteProps in *; intuition).
          destruct HparentOfPart as [wrongParts (HparentOfPart & HwrongParts)].
          specialize(HparentOfPart partition pdentry HlookupPart).
          destruct HparentOfPart as (HparentIsPart & HparentOfRoot & _).
          assert(HparentNotWrong: ~In (parent pdentry) wrongParts).
          {
            intro Hcontra. assert(HpartIsDesc: In partition (getPartitions (parent pdentry) s0)).
            {
              unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. right.
              assert(HpartIsChild: isChild s0) by (unfold deleteProps in *; intuition).
              assert(Hparent: pdentryParent partition (parent pdentry) s0).
              { unfold pdentryParent. rewrite HlookupPart. reflexivity. }
              specialize(HpartIsChild partition (parent pdentry) HpartIsPart Hparent HbeqPartRoot).
              induction (getChildren (parent pdentry) s0); simpl in *; try(congruence). apply in_or_app.
              destruct HpartIsChild; auto. subst. left. replace (maxAddr+1) with (S maxAddr); try(lia). simpl.
              auto.
            }
            assert(HbeqPartBTD: partition <> blockToDelete) by (intro; subst partition; congruence).
            specialize(HwrongParts (parent pdentry) Hcontra partition HpartIsDesc HbeqPartBTD). congruence.
          }
          specialize(HparentIsPart HparentNotWrong HbeqPartRoot). apply HparentIsPart.
        }
        rewrite <-HgetMappedBEqss0 in HblockPMapped; trivial.
        assert(HlookupBPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s1) beqAddr).
        {
          apply IL.mappedBlockIsBE in HblockPMapped. destruct HblockPMapped as [bentry (Hlookup & _)].
          assert(~In blockParent (getAllPaddrBlock startBlock endBlock)).
          { intro Hcontra. rewrite HremovedAddrs in Hlookup; trivial. congruence. }
          clear HlookupBTDs. rewrite HlookupsEq in *; trivial. rewrite Hs2. rewrite Hs2 in Hlookup. simpl in *.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockParent) eqn:HbeqSh1BP; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        unfold bentryStartAddr. simpl. rewrite HlookupBPEq. split; trivial.
        assert(bentryStartAddr blockParent scorigin s1).
        {
          unfold bentryStartAddr in *. rewrite Hs1. simpl. destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
          - rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        split; trivial. intros addr HaddrInBlock. assert(~In block (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HaddrInBlock; trivial. }
        rewrite HlookupsEq in HaddrInBlock; trivial. rewrite Hs2 in HaddrInBlock. simpl in HaddrInBlock.
        destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block;
          try(simpl in HaddrInBlock; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; auto. assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
        {
          simpl. rewrite Hs1 in HaddrInBlock. simpl in HaddrInBlock.
          destruct (beqAddr currBlock block) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in HaddrInBlock.
            auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        specialize(HinclParent addr HaddrInBlocks0). simpl in HinclParent. rewrite Hs1. simpl.
        destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
        + rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      - intros startaddr Hstart. apply HlebOriginStart. unfold bentryStartAddr in *.
        assert(~In block (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in Hstart; trivial. }
        rewrite HlookupsEq in Hstart; trivial. rewrite Hs2 in Hstart. simpl in Hstart.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. unfold bentryStartAddr.
        rewrite Hs1 in Hstart. simpl in Hstart.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        + rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      (* END originIsParentBlocksStart *)
    }

    assert(nextImpliesBlockWasCut s).
    { (* BEGIN nextImpliesBlockWasCut s *)
      assert(Hcons0: nextImpliesBlockWasCut s0) by (unfold deleteProps in *; intuition).
      intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped HendBlock Hsce
        HbeqNextNull Hnext HbeqPartRoot. rewrite HgetPartsEqss0 in *.
      assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupPart; trivial. congruence. }
      rewrite HlookupsEq in HlookupPart; trivial. rewrite Hs2 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart.
      simpl in HlookupPart. destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      rewrite HgetMappedBEqss0 in HblockMapped; trivial. unfold bentryEndAddr in HendBlock.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HendBlock; trivial. }
      unfold scentryNext in *. assert(~In scentryaddr (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hnext; trivial. }
      unfold getAllPaddrAux at 1. clear HlookupBTDs. rewrite HlookupsEq in *; trivial. rewrite Hs2 in HendBlock.
      rewrite Hs2. rewrite Hs2 in Hnext. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) scentryaddr) eqn:HbeqSh1Sce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HendBlocks0: bentryEndAddr block endaddr s0).
      {
        unfold bentryEndAddr. rewrite Hs1 in HendBlock. simpl in HendBlock.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in HendBlock. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite Hs1 in Hnext. simpl in Hnext.
      destruct (beqAddr currBlock scentryaddr) eqn:HbeqSBSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
        HendBlocks0 Hsce HbeqNextNull Hnext HbeqPartRoot).
      destruct Hcons0 as [blockParent [endPar (HblockPMapped & HendPar & HltEnds & Hincl)]]. exists blockParent.
      exists endPar. assert(In (parent pdentry) (getPartitions multiplexer s0)).
      {
        assert(HparentOfPart: exists wrongParts,
            (forall partition entry,
              lookup partition (memory s0) beqAddr = Some (PDT entry)
              -> (~In (parent entry) wrongParts
                  -> partition <> constantRootPartM
                  -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                      /\ In (parent entry) (getPartitions multiplexer s0))
                /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
            /\ (forall oldPart, In oldPart wrongParts
                -> (forall desc, In desc (getPartitions oldPart s0)
                    -> desc <> blockToDelete
                    -> ~In desc (getPartitions multiplexer s0))))
          by (unfold deleteProps in *; intuition).
        destruct HparentOfPart as [wrongParts (HparentOfPart & HwrongParts)].
        specialize(HparentOfPart partition pdentry HlookupPart).
        destruct HparentOfPart as (HparentIsPart & HparentOfRoot & _).
        assert(HparentNotWrong: ~In (parent pdentry) wrongParts).
        {
          intro Hcontra. assert(HpartIsDesc: In partition (getPartitions (parent pdentry) s0)).
          {
            unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. right.
            assert(HpartIsChild: isChild s0) by (unfold deleteProps in *; intuition).
            assert(Hparent: pdentryParent partition (parent pdentry) s0).
            { unfold pdentryParent. rewrite HlookupPart. reflexivity. }
            specialize(HpartIsChild partition (parent pdentry) HpartIsPart Hparent HbeqPartRoot).
            induction (getChildren (parent pdentry) s0); simpl in *; try(congruence). apply in_or_app.
            destruct HpartIsChild; auto. subst. left. replace (maxAddr+1) with (S maxAddr); try(lia). simpl.
            auto.
          }
          assert(HbeqPartBTD: partition <> blockToDelete) by (intro; subst partition; congruence).
          specialize(HwrongParts (parent pdentry) Hcontra partition HpartIsDesc HbeqPartBTD). congruence.
        }
        specialize(HparentIsPart HparentNotWrong HbeqPartRoot). apply HparentIsPart.
      }
      rewrite <-HgetMappedBEqss0 in *; trivial. split; trivial. apply IL.mappedBlockIsBE in HblockPMapped.
      destruct HblockPMapped as [bentry (HlookupBP & _)]. unfold bentryEndAddr. simpl.
      assert(~In blockParent (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupBP; trivial. congruence. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2. rewrite Hs2 in HlookupBP. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockParent) eqn:HbeqSh1BP; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. assert(bentryEndAddr blockParent endPar s1).
      {
        unfold bentryEndAddr in *. rewrite Hs1. simpl. destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
        - rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. rewrite HlookupCurrBs0 in HendPar. rewrite HnewB.
          auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      split; trivial. split; trivial. intros addr HaddrInBlock.
      assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
      {
        simpl. rewrite Hs1 in HaddrInBlock. simpl in HaddrInBlock.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in HaddrInBlock.
          auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hincl addr HaddrInBlocks0). simpl in Hincl. rewrite Hs1. simpl.
      destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
      - rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END nextImpliesBlockWasCut *)
    }

    assert(blocksAddressesTypes s).
    { (* BEGIN blocksAddressesTypes s *)
      assert(Hcons0: blocksAddressesTypes s0) by (unfold deleteProps in *; intuition).
      intros block startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HlocBlock.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in HblockMapped; trivial. unfold bentryEndAddr in *.
      unfold bentryStartAddr in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HendBlock; trivial. }
      rewrite HlookupsEq in HstartBlock; trivial. rewrite HlookupsEq in HendBlock; trivial.
      unfold sh1entryInChildLocationWeak in *.
      assert(~In (CPaddr (block+sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlocBlock; trivial. }
      rewrite HlookupsEq in HlocBlock; trivial. rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock.
      simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
      {
        unfold bentryStartAddr. unfold bentryEndAddr. rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock.
        simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *.
          simpl blockrange in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (HstartBlocks0 & HendBlocks0). rewrite Hs2 in HlocBlock. simpl in HlocBlock.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1.
      - rewrite <-beqAddrTrue in HbeqSh1. apply CPaddrAddEq in HbeqSh1; trivial. subst block.
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupCurrBs0 in *.
        rewrite <-HstartBlocks0 in *. rewrite <-HendBlocks0 in *. subst startaddr. subst endaddr. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlocBlock.
        simpl in HlocBlock.
        destruct (beqAddr currBlock (CPaddr (block + sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(Hcons0 block startaddr endaddr part HpartIsPart HblockMapped HstartBlocks0 HendBlocks0 HlocBlock).
        assert(HpropsOr: In startaddr (getAllPaddrBlock startBlock endBlock)
          \/ ~In startaddr (getAllPaddrBlock startBlock endBlock)) by (apply Classical_Prop.classic).
        destruct HpropsOr as [HstartIn | HstartNotIn].
        + right. right. intros addr HaddrInRange. rewrite <-Hranges0 in *.
          assert(HparentIsAnc: In part (currentPart::filterOptionPaddr (completeParentsList currentPart s0))).
          {
            assert(Hwell: wellFormedBlock s0) by (unfold deleteProps in *; intuition).
            assert(HPflag: bentryPFlag block true s0).
            {
              apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
              unfold bentryPFlag. rewrite Hlookup. auto.
            }
            specialize(Hwell block startaddr endaddr HPflag HstartBlocks0 HendBlocks0). destruct Hwell as (Hwell & _).
            assert(In startaddr (getMappedPaddr part s0)).
            {
              apply IL.addrInBlockIsMapped with block; trivial. simpl. unfold bentryStartAddr in *.
              unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0.
              rewrite app_nil_r. apply IL.getAllPaddrBlockIncl; lia.
            }
            assert(Hbloodline: In part (filterOptionPaddr (completeParentsList currentPart s0))
              \/ part = currentPart
              \/ In currentPart (filterOptionPaddr (completeParentsList part s0))).
            {
              apply addressesBloodlinePartial with startaddr blockTDParent blockToDelete; trivial;
                try(apply IL.noDupKSMappedImpl); only 1-13: (unfold deleteProps in *; intuition).
              apply IL.addrInBlockIsMapped with currBlock; trivial.
            }
            simpl. destruct Hbloodline as [Hres | [Heq | Hcontra]]; auto. exfalso.
            assert(Hchild: exists child, pdentryParent child currentPart s0
             /\ In child (getPartitions multiplexer s0)
             /\ In child (part::filterOptionPaddr (completeParentsList part s0))).
            {
              apply completeParentsListChildPartial with blockTDParent blockToDelete; trivial;
                unfold deleteProps in *; intuition.
            }
            destruct Hchild as [child (Hparent & HchildIsPart & HchildIsAnc)].
            destruct (beqAddr child blockToDelete) eqn:HbeqChildren.
            - rewrite <-beqAddrTrue in HbeqChildren. subst child. unfold pdentryParent in *.
              rewrite HlookupBTDs0 in *. congruence.
            - rewrite <-beqAddrFalse in *. specialize(HpropsAddrToRemoveCopy startaddr HstartIn).
              destruct HpropsAddrToRemoveCopy as (_ & _ & HstartInNoChild & _). apply not_eq_sym in HbeqChildren.
              assert(HchildIsChild: isChild s0) by (unfold deleteProps in *; intuition).
              assert(HbeqChildRoot: child <> constantRootPartM).
              {
                assert(HparentOfPart: exists wrongParts,
                    (forall partition entry,
                      lookup partition (memory s0) beqAddr = Some (PDT entry)
                      -> (~In (parent entry) wrongParts
                          -> partition <> constantRootPartM
                          -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                              /\ In (parent entry) (getPartitions multiplexer s0))
                        /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
                    /\ (forall oldPart, In oldPart wrongParts
                        -> (forall desc, In desc (getPartitions oldPart s0)
                            -> desc <> blockToDelete
                            -> ~In desc (getPartitions multiplexer s0))))
                  by (unfold deleteProps in *; intuition). intro HbeqChildRoot.
                destruct HparentOfPart as [wrongParts (HparentOfPart & _)]. unfold pdentryParent in *.
                destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(congruence).
                destruct v; try(congruence). specialize(HparentOfPart child p HlookupChild).
                destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot HbeqChildRoot).
                rewrite HparentOfRoot in *. subst currentPart. unfold isPDT in *.
                assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
                destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
              }
              specialize(HchildIsChild child currentPart HchildIsPart Hparent HbeqChildRoot).
              specialize(HstartInNoChild child HchildIsChild). contradict HstartInNoChild.
              simpl in HchildIsAnc. destruct HchildIsAnc as [Heq | HchildIsAnc]; try(subst child; assumption).
              apply addrBelongToAncestorsPartial with part blockTDParent blockToDelete; trivial;
                only 6: apply IL.blockInclImpliesAddrIncl; unfold deleteProps in *; intuition.
          }
          assert(HstartInRange: In startaddr (getAllPaddrAux [block] s0)).
          {
            unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl.
            destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-HstartBlocks0. rewrite <-HendBlocks0.
            rewrite app_nil_r. apply IL.getAllPaddrBlockInclRev in HaddrInRange.
            destruct HaddrInRange as (_ & _ & HltStartEnd). apply IL.getAllPaddrBlockIncl; lia.
          }
          assert(part = currentPart).
          {
            simpl in HparentIsAnc.
            destruct (beqAddr part currentPart) eqn:HbeqPartCurr; only 1: (rewrite beqAddrTrue; assumption).
            rewrite <-beqAddrFalse in *. exfalso.
            destruct HparentIsAnc as [Heq | HpartIsAnc]; only 1: congruence. 
            assert(Hchild: exists child, pdentryParent child part s0
             /\ In child (getPartitions multiplexer s0)
             /\ In child (currentPart::filterOptionPaddr (completeParentsList currentPart s0))).
            {
              apply completeParentsListChildPartial with blockTDParent blockToDelete; trivial;
                unfold deleteProps in *; intuition.
            }
            destruct Hchild as [child (Hparent & HchildIsPart & HchildIsAnc)].
            assert(HchildIsChild: isChild s0) by (unfold deleteProps in *; intuition).
            assert(HbeqChildRoot: child <> constantRootPartM).
            {
              assert(HparentOfPart: exists wrongParts,
                  (forall partition entry,
                    lookup partition (memory s0) beqAddr = Some (PDT entry)
                    -> (~In (parent entry) wrongParts
                        -> partition <> constantRootPartM
                        -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                            /\ In (parent entry) (getPartitions multiplexer s0))
                      /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
                  /\ (forall oldPart, In oldPart wrongParts
                      -> (forall desc, In desc (getPartitions oldPart s0)
                          -> desc <> blockToDelete
                          -> ~In desc (getPartitions multiplexer s0))))
                by (unfold deleteProps in *; intuition). intro HbeqChildRoot.
              destruct HparentOfPart as [wrongParts (HparentOfPart & _)]. unfold pdentryParent in *.
              destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(congruence).
              destruct v; try(congruence). specialize(HparentOfPart child p HlookupChild).
              destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot HbeqChildRoot).
              rewrite HparentOfRoot in *. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *.
              assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
              destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
              destruct v; simpl in HblockMapped; congruence.
            }
            specialize(HchildIsChild child part HchildIsPart Hparent HbeqChildRoot).
            assert(HstartNotIsChild: ~In startaddr (getMappedPaddr child s0)).
            {
              assert(HlocBlockCopy: sh1entryInChildLocationWeak (CPaddr (block+sh1offset)) nullAddr s0) by assumption.
              destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1;
                try(exfalso; congruence). destruct v; try(exfalso; congruence).
              destruct (beqAddr (PDchild s3) nullAddr) eqn:HbeqPDchildNull.
              - rewrite <-beqAddrTrue in HbeqPDchildNull.
                assert(HPDchild: sh1entryPDchild (CPaddr (block+sh1offset)) nullAddr s0).
                { unfold sh1entryPDchild. rewrite HlookupSh1. auto. }
                assert(Hres: noChildImpliesAddressesNotShared s0) by (unfold deleteProps in *; intuition).
                assert(HlookupPart: exists pdentry, lookup part (memory s0) beqAddr = Some (PDT pdentry)).
                {
                  unfold getMappedBlocks in *. unfold getKSEntries in *.
                  destruct (lookup part (memory s0) beqAddr); try(simpl in HblockMapped; exfalso; congruence).
                  destruct v; try(simpl in HblockMapped; exfalso; congruence). exists p. reflexivity.
                }
                destruct HlookupPart as [pdentry HlookupPart].
                unfold noChildImpliesAddressesNotShared in *. revert HchildIsChild HstartInRange.
                apply Hres with pdentry (CPaddr (block+sh1offset)); trivial.
              - rewrite <-beqAddrFalse in *.
                assert(HPDchild: sh1entryPDchild (CPaddr (block+sh1offset)) (PDchild s3) s0).
                { unfold sh1entryPDchild. rewrite HlookupSh1. reflexivity. }
                assert(HbeqPDchildBTD: PDchild s3 <> blockToDelete).
                {
                  intro HbeqPDchildBTD. rewrite HbeqPDchildBTD in *.
                  assert(HPDchildIsChild: pdchildIsPDT s0) by (unfold deleteProps in *; intuition).
                  assert(Hsh1: sh1entryAddr block (CPaddr (block+sh1offset)) s0).
                  {
                    unfold sh1entryAddr. unfold bentryStartAddr in *.
                    destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; congruence.
                  }
                  specialize(HPDchildIsChild part block (CPaddr (block+sh1offset)) blockToDelete HpartIsPart
                    HblockMapped Hsh1 HPDchild HbeqBTDNull).
                  specialize(HBTDIsUniqueChild part HpartIsPart HPDchildIsChild). congruence.
                }
                assert(HpropsKern: forall part block child startaddr,
                  child <> blockToDelete
                  -> In part (getPartitions multiplexer s0)
                  -> In block (getMappedBlocks part s0)
                  -> sh1entryPDchild (CPaddr (block + sh1offset)) child s0
                  -> child <> nullAddr
                  -> sh1entryPDflag (CPaddr (block + sh1offset)) false s0
                  -> sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) nullAddr s0
                  -> bentryStartAddr block startaddr s0
                  -> In startaddr (getConfigBlocks child s0)
                      /\ (forall addr child2, In addr (getAllPaddrAux [block] s0)
                            -> In child2 (getChildren part s0)
                            -> ~In addr (getMappedPaddr child2 s0))
                      /\ (forall (addr:paddr) endaddr part2, bentryEndAddr block endaddr s0
                            -> In part2 (getPartitions multiplexer s0)
                            -> startaddr+Constants.kernelStructureTotalLength <= addr
                            -> addr < endaddr
                            -> ~In addr (getConfigPaddr part2 s0))) by (unfold deleteProps in *; intuition).
                assert(HPDflag: sh1entryPDflag (CPaddr (block + sh1offset)) false s0).
                {
                  assert(HPDflagNoChild: PDflagMeansNoChild s0) by (unfold deleteProps in *; intuition).
                  assert(HblockIsBE: isBE block s0).
                  {
                    unfold bentryStartAddr in *. unfold isBE.
                    destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
                    trivial.
                  }
                  specialize(HPDflagNoChild block HblockIsBE). unfold sh1entryPDflag in *.
                  unfold sh1entryPDchild in *. rewrite HlookupSh1 in *. destruct (PDflag s3); trivial. exfalso.
                  assert(HeqTriv: true = true) by reflexivity. specialize(HPDflagNoChild HeqTriv). congruence.
                }
                specialize(HpropsKern part block (PDchild s3) startaddr HbeqPDchildBTD HpartIsPart HblockMapped
                  HPDchild HbeqPDchildNull HPDflag HlocBlockCopy HstartBlocks0).
                destruct HpropsKern as (_ & Hres & _). apply Hres; trivial.
            }
            contradict HstartNotIsChild. assert(HstartInCurr: In startaddr (getMappedPaddr currentPart s0)).
            { apply IL.addrInBlockIsMapped with currBlock; trivial. }
            simpl in HchildIsAnc. destruct HchildIsAnc as [Heq | HchildIsAnc]; try(subst child; assumption).
            revert HstartInCurr. apply addrBelongToAncestorsPartial with blockTDParent blockToDelete; trivial;
              only 6: apply IL.blockInclImpliesAddrIncl; unfold deleteProps in *; intuition.
          }
          subst part. assert(block = currBlock).
          {
            destruct (beqAddr block currBlock) eqn:HbeqBlocks; only 1: (rewrite beqAddrTrue; assumption). exfalso.
            rewrite <-beqAddrFalse in *.
            assert(HnoDupP: noDupMappedPaddrList s0) by (unfold deleteProps in *; intuition).
            pose proof (DisjointPaddrInPart currentPart block currBlock startaddr s0 HnoDupP HpartIsPart HblockMapped
              HCBMapped HbeqBlocks HstartInRange). congruence.
          }
          subst block. unfold bentryStartAddr in *. unfold bentryEndAddr in *. apply HremovedAddrs. rewrite Hranges0.
          rewrite HlookupCurrBs0 in *. rewrite <-HstartCBs0 in *. rewrite <-HendCBs0 in *. subst startaddr.
          subst endaddr. assumption.
        + assert(HlookupStartEq: lookup startaddr (memory s) beqAddr = lookup startaddr (memory s2) beqAddr).
          { apply HlookupsEq; assumption. }
          unfold isKS in *. unfold isPDT in *. rewrite HlookupStartEq.
          destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hrange]].
          * left. rewrite Hs2. simpl. destruct (beqAddr (CPaddr (currBlock+sh1offset)) startaddr) eqn:HbeqSh1Start.
            {
              rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *.
              exfalso. destruct (lookup startaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. assert(isKS startaddr s1).
            {
              unfold isKS. rewrite Hs1. simpl. destruct (beqAddr currBlock startaddr) eqn:HbeqCBStart.
              - rewrite <-beqAddrTrue in HbeqCBStart. subst startaddr. rewrite HlookupCurrBs0 in *. rewrite HnewB.
                auto.
              - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
            }
            split; trivial. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
            specialize(HremovedAddrs addr). specialize(HlookupsEq addr).
            assert(HpropsOr: In addr (getAllPaddrBlock startBlock endBlock)
              \/ ~In addr (getAllPaddrBlock startBlock endBlock)) by (apply Classical_Prop.classic).
            destruct HpropsOr; only 1: (right; auto). unfold isBE. unfold isSHE. unfold isSCE. unfold isPADDR.
            rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
            destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr; auto.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
            destruct (beqAddr currBlock addr) eqn:HbeqCBAddr; auto.
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
          * right. left. rewrite Hs2. simpl.
            destruct (beqAddr (CPaddr (currBlock+sh1offset)) startaddr) eqn:HbeqSh1Start.
            {
              rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *.
              exfalso. destruct (lookup startaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
            destruct (beqAddr currBlock startaddr) eqn:HbeqCBStart.
            {
              rewrite <-beqAddrTrue in HbeqCBStart. subst startaddr. rewrite HlookupCurrBs0 in *. exfalso.
              congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. split; trivial.
            intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
            assert(HpropsOr: In addr (getAllPaddrBlock startBlock endBlock)
              \/ ~In addr (getAllPaddrBlock startBlock endBlock)) by (apply Classical_Prop.classic).
            destruct HpropsOr; auto. rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
            destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr.
            {
              rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *.
              exfalso. rewrite Hrange in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
            destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
            {
              rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
          * right. right. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
            assert(HpropsOr: In addr (getAllPaddrBlock startBlock endBlock)
              \/ ~In addr (getAllPaddrBlock startBlock endBlock)) by (apply Classical_Prop.classic).
            destruct HpropsOr; auto. rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
            destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr.
            {
              rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Addr. rewrite HbeqSh1Addr in *.
              exfalso. rewrite Hrange in *. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
            destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
            {
              rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. congruence.
            }
            rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END blocksAddressesTypes *)
    }

    assert(notPDTIfNotPDflag s).
    { (* BEGIN notPDTIfNotPDflag s *)
      assert(Hcons0: notPDTIfNotPDflag s0) by (unfold deleteProps in *; intuition).
      intros block startaddr sh1entryaddrB part HpartIsPart HblockMapped HstartBlock Hsh1 HPDflag HPDchild.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in HblockMapped; trivial. unfold sh1entryAddr in *.
      unfold bentryStartAddr in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hsh1; trivial. }
      rewrite HlookupsEq in HstartBlock; trivial. rewrite HlookupsEq in Hsh1; trivial.
      unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
      assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDflag; trivial. }
      rewrite HlookupsEq in HPDflag; trivial. rewrite HlookupsEq in HPDchild; trivial. rewrite Hs2 in HstartBlock.
      rewrite Hs2 in Hsh1. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ sh1entryAddr block sh1entryaddrB s0).
      {
        unfold bentryStartAddr. unfold sh1entryAddr. rewrite Hs1 in HstartBlock. rewrite Hs1 in Hsh1.
        simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *.
          simpl blockrange in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (HstartBlocks0 & Hsh1s0). rewrite Hs2 in HPDflag. simpl in HPDflag.
      rewrite Hs2 in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) sh1entryaddrB) eqn:HbeqSh1.
      - assert(block = currBlock).
        {
          destruct (lookup block (memory s1) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
          subst sh1entryaddrB. rewrite <-beqAddrTrue in HbeqSh1. apply CPaddrAddEq in HbeqSh1; trivial. auto.
        }
        subst block. unfold bentryStartAddr in *. rewrite HlookupCurrBs0 in *. rewrite <-HstartCBs0 in *.
        subst startaddr. unfold isPDT. rewrite HremovedAddrs; auto. apply IL.getAllPaddrBlockIncl; lia.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDflag. simpl in HPDflag.
        rewrite Hs1 in HPDchild. simpl in HPDchild.
        destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(Hcons0 block startaddr sh1entryaddrB part HpartIsPart HblockMapped HstartBlocks0 Hsh1s0 HPDflag
          HPDchild). contradict Hcons0. unfold isPDT in *.
        assert(~In startaddr (getAllPaddrBlock startBlock endBlock)).
        { intro Hcontra. apply HremovedAddrs in Hcontra. rewrite Hcontra in *. congruence. }
        rewrite HlookupsEq in Hcons0; trivial. rewrite Hs2 in Hcons0. simpl in Hcons0.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) startaddr) eqn:HbeqSh1Start; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hcons0. simpl in Hcons0.
        destruct (beqAddr currBlock startaddr) eqn:HbeqCBStart; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      (* END notPDTIfNotPDflag *)
    }

    assert(nextKernAddrIsInSameBlock s).
    { (* BEGIN nextKernAddrIsInSameBlock s *)
      assert(Hcons0: nextKernAddrIsInSameBlock s0) by (unfold deleteProps in *; intuition).
      intros block kern startaddr endaddr part HpartIsPart HblockMapped HstartBlock HendBlock HPDchildBlock HkernIsKS.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in HblockMapped; trivial. unfold bentryEndAddr in *.
      unfold bentryStartAddr in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HendBlock; trivial. }
      rewrite HlookupsEq in HstartBlock; trivial. rewrite HlookupsEq in HendBlock; trivial.
      unfold sh1entryPDchild in *. unfold isKS in *.
      assert(~In (CPaddr (block+sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDchildBlock; trivial. }
      assert(~In kern (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HkernIsKS; trivial. }
      rewrite HlookupsEq in HkernIsKS; trivial. rewrite HlookupsEq in HPDchildBlock; trivial.
      rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. rewrite Hs2 in HkernIsKS. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
      {
        unfold bentryStartAddr. unfold bentryEndAddr. rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock.
        simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *.
          simpl blockrange in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (HstartBlocks0 & HendBlocks0). assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS. destruct (beqAddr currBlock kern) eqn:HbeqCBKern.
        - rewrite <-beqAddrTrue in HbeqCBKern. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in HkernIsKS. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite Hs2 in HPDchildBlock. simpl in HPDchildBlock.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (block+sh1offset))) eqn:HbeqSh1.
      - rewrite <-beqAddrTrue in HbeqSh1. apply CPaddrAddEq in HbeqSh1; trivial. subst block.
        unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupCurrBs0 in *.
        rewrite <-HstartBlocks0 in *. rewrite <-HendBlocks0 in *. subst startaddr. subst endaddr. intro HnextIn.
        assert(HnextInSameB: blockAndNextInSameBlock s0) by (unfold deleteProps in *; intuition).
        rewrite <-Hranges0 in *. exfalso.
        specialize(HnextInSameB part kern currBlock HpartIsPart HblockMapped HkernIsKSs0 HnextIn). congruence.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchildBlock.
        simpl in HPDchildBlock.
        destruct (beqAddr currBlock (CPaddr (block+sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(Hcons0 block kern startaddr endaddr part HpartIsPart HblockMapped HstartBlocks0 HendBlocks0
          HPDchildBlock HkernIsKSs0). assumption.
      (* END nextKernAddrIsInSameBlock *)
    }

    assert(PDflagMeansNoChild s).
    { (* BEGIN PDflagMeansNoChild s *)
      assert(Hcons0: PDflagMeansNoChild s0) by (unfold deleteProps in *; intuition).
      intros block HblockIsBE HPDflagBlock. unfold isBE in *. unfold sh1entryPDflag in *. unfold sh1entryPDchild.
      clear HlookupBTDs. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HblockIsBE; trivial. }
      assert(~In (CPaddr (block + sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDflagBlock; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HblockIsBE. rewrite Hs2 in HPDflagBlock. rewrite Hs2.
      simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s; auto.
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE. rewrite Hs1 in HblockIsBE. simpl in HblockIsBE.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite Hs1 in HPDflagBlock. rewrite Hs1. simpl lookup in *.
      destruct (beqAddr currBlock (CPaddr (block + sh1offset))) eqn:HbeqCBSh1; try(congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 block HblockIsBEs0 HPDflagBlock). assumption.
      (* END PDflagMeansNoChild *)
    }

    assert(nbPrepareIsNbKern s).
    { (* BEGIN nbPrepareIsNbKern s *)
      assert(Hcons0: nbPrepareIsNbKern s0) by (unfold deleteProps in *; intuition).
      intros partition pdentry HpartIsPart HlookupPart. assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupPart; trivial. congruence. }
      rewrite HlookupsEq in HlookupPart; trivial. rewrite Hs2 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart.
      simpl in HlookupPart. destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite HgetPartsEqss0 in *.
      specialize(Hcons0 partition pdentry HpartIsPart HlookupPart).
      rewrite HcomplKernLEq with (part:=partition); trivial.
     (* END nbPrepareIsNbKern *)
    }

    assert(pdchildIsPDT s).
    { (* BEGIN pdchildIsPDT s *)
      assert(Hcons0: pdchildIsPDT s0) by (unfold deleteProps in *; intuition).
      intros part block sh1entryaddrB idchild HpartBisIsPart HblockMapped Hsh1 HPDchild HbeqIdChildNull.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in HblockMapped; trivial. unfold sh1entryAddr in *.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hsh1; trivial. }
      rewrite HlookupsEq in Hsh1; trivial. unfold sh1entryPDchild in *.
      assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDchild; trivial. }
      rewrite HlookupsEq in HPDchild; trivial. rewrite Hs2 in Hsh1. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite Hs2 in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) sh1entryaddrB) eqn:HbeqSh1;
        try(simpl in HPDchild; subst idchild; exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hsh1s0: sh1entryAddr block sh1entryaddrB s0).
      {
        unfold sh1entryAddr. rewrite Hs1 in Hsh1. simpl lookup in *.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *.
          simpl blockrange in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite Hs1 in HPDchild. simpl in HPDchild.
      destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block sh1entryaddrB idchild HpartBisIsPart HblockMapped Hsh1s0 HPDchild HbeqIdChildNull).
      rewrite HgetChildrenEqss0; assumption.
      (* END pdchildIsPDT *)
    }

    assert(childBlockNullIfChildNull s).
    { (* BEGIN childBlockNullIfChildNull s *)
      assert(Hcons0: childBlockNullIfChildNull s0) by (unfold deleteProps in *; intuition).
      intros part block sh1entryaddrB HpartBisIsPart HblockMapped Hsh1 HPDchild.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in HblockMapped; trivial. unfold sh1entryAddr in *.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hsh1; trivial. }
      rewrite HlookupsEq in Hsh1; trivial. unfold sh1entryInChildLocation. unfold sh1entryPDchild in *.
      assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDchild; trivial. }
      rewrite HlookupsEq; trivial. rewrite HlookupsEq in HPDchild; trivial. rewrite Hs2 in Hsh1. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hsh1s0: sh1entryAddr block sh1entryaddrB s0).
      {
        unfold sh1entryAddr. rewrite Hs1 in Hsh1. simpl lookup in *.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *.
          simpl blockrange in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite Hs2. simpl. rewrite Hs2 in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) sh1entryaddrB) eqn:HbeqSh1.
      - split; auto. intro Hcontra. exfalso; congruence.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchild. rewrite Hs1.
        simpl lookup in *. destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        specialize(Hcons0 part block sh1entryaddrB HpartBisIsPart HblockMapped Hsh1s0 HPDchild).
        unfold sh1entryInChildLocation in *. destruct (lookup sh1entryaddrB (memory s0) beqAddr); try(congruence).
        destruct v; try(congruence). destruct Hcons0 as (Hcons0 & _). split; trivial. intro. exfalso; congruence.
      (* END childBlockNullIfChildNull *)
    }

    assert(accessibleBlocksArePresent s).
    { (* BEGIN accessibleBlocksArePresent s *)
      assert(Hcons0: accessibleBlocksArePresent s0) by (unfold deleteProps in *; intuition).
      intros block HAflag. unfold bentryAFlag in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HAflag; trivial. }
      unfold bentryPFlag. clear HlookupBTDs. rewrite HlookupsEq in *; trivial. rewrite Hs2 in HAflag. rewrite Hs2.
      simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HAflag. rewrite Hs1.
      simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
      - rewrite <-beqAddrTrue in HbeqBlocks. subst block. unfold bentryPFlag in *. rewrite HlookupCurrBs0 in *.
        rewrite HnewB. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. specialize(Hcons0 block HAflag).
        assumption.
      (* END accessibleBlocksArePresent *)
    }

    assert(sharedBlockIsPresent s).
    { (* BEGIN sharedBlockIsPresent s *)
      assert(Hcons0: sharedBlockIsPresent s0) by (unfold deleteProps in *; intuition).
      intros part block child HpartIsPart HblockIsEntry HPDchild HbeqChildNull. rewrite HgetPartsEqss0 in *.
      assert(HblockIsBE: isBE block s) by (apply KSentriesAreBE in HblockIsEntry; assumption).
      rewrite HgetKSEqss0 in *; trivial. unfold sh1entryPDchild in *.
      assert(~In (CPaddr (block + sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDchild; trivial. }
      rewrite HlookupsEq in HPDchild; trivial. rewrite Hs2 in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s;
        try(simpl in HPDchild; exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchild. simpl in HPDchild.
      destruct (beqAddr currBlock (CPaddr (block + sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block child HpartIsPart HblockIsEntry HPDchild HbeqChildNull). unfold bentryPFlag in *.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { unfold isBE in *. intro. rewrite HremovedAddrs in HblockIsBE; trivial. }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Block. rewrite HbeqSh1Block in *.
        destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock block) eqn:HbeqBlocks.
      - rewrite <-beqAddrTrue in HbeqBlocks. subst block. unfold bentryPFlag in *. rewrite HlookupCurrBs0 in *.
        rewrite HnewB. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      (* END sharedBlockIsPresent *)
    }

    assert(forall part block child startaddr,
        child <> blockToDelete
        -> In part (getPartitions multiplexer s)
        -> In block (getMappedBlocks part s)
        -> sh1entryPDchild (CPaddr (block + sh1offset)) child s
        -> child <> nullAddr
        -> sh1entryPDflag (CPaddr (block + sh1offset)) false s
        -> sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) nullAddr s
        -> bentryStartAddr block startaddr s
        -> In startaddr (getConfigBlocks child s)
            /\ (forall addr child2, In addr (getAllPaddrAux [block] s)
                  -> In child2 (getChildren part s)
                  -> ~In addr (getMappedPaddr child2 s))
            /\ (forall (addr:paddr) endaddr part2, bentryEndAddr block endaddr s
                  -> In part2 (getPartitions multiplexer s)
                  -> startaddr+Constants.kernelStructureTotalLength <= addr
                  -> addr < endaddr
                  -> ~In addr (getConfigPaddr part2 s))).
    { (* BEGIN sharedBlockNoPDflagNoLocIsKern s *)
      assert(Hcons0: forall part block child startaddr,
        child <> blockToDelete
        -> In part (getPartitions multiplexer s0)
        -> In block (getMappedBlocks part s0)
        -> sh1entryPDchild (CPaddr (block + sh1offset)) child s0
        -> child <> nullAddr
        -> sh1entryPDflag (CPaddr (block + sh1offset)) false s0
        -> sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) nullAddr s0
        -> bentryStartAddr block startaddr s0
        -> In startaddr (getConfigBlocks child s0)
            /\ (forall addr child2, In addr (getAllPaddrAux [block] s0)
                  -> In child2 (getChildren part s0)
                  -> ~In addr (getMappedPaddr child2 s0))
            /\ (forall (addr:paddr) endaddr part2, bentryEndAddr block endaddr s0
                  -> In part2 (getPartitions multiplexer s0)
                  -> startaddr+Constants.kernelStructureTotalLength <= addr
                  -> addr < endaddr
                  -> ~In addr (getConfigPaddr part2 s0))) by (unfold deleteProps in *; intuition).
      intros part block child startaddr HbeqChildBTD HpartIsPart HblockMapped HPDchild HbeqChildNull HPDflag Hloc
        Hstart.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in HblockMapped; trivial. unfold bentryStartAddr in *.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hstart; trivial. }
      rewrite HlookupsEq in Hstart; trivial. unfold sh1entryInChildLocationWeak in *. unfold sh1entryPDflag in *.
      unfold sh1entryPDchild in *. assert(~In (CPaddr (block + sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hloc; trivial. }
      rewrite HlookupsEq in Hloc; trivial. rewrite HlookupsEq in HPDflag; trivial.
      rewrite HlookupsEq in HPDchild; trivial. rewrite Hs2 in Hstart. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hstarts0: bentryStartAddr block startaddr s0).
      {
        unfold bentryStartAddr. rewrite Hs1 in Hstart. simpl lookup in *.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite Hs2 in Hloc. simpl in Hloc. rewrite Hs2 in HPDflag. simpl in HPDflag. rewrite Hs2 in HPDchild.
      simpl in HPDchild.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (block+sh1offset))) eqn:HbeqSh1s;
        try(simpl in HPDchild; exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchild. rewrite Hs1 in Hloc.
      rewrite Hs1 in HPDflag. simpl lookup in *.
      destruct (beqAddr currBlock (CPaddr (block + sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block child startaddr HbeqChildBTD HpartIsPart HblockMapped HPDchild HbeqChildNull
        HPDflag Hloc Hstarts0). destruct Hcons0 as (HstartInConfB & HaddrsNotInChildren & HdeadAddrs).
      assert(In child (getPartitions multiplexer s0)).
      {
        assert(HchildIsChild: pdchildIsPDT s0) by (unfold deleteProps in *; intuition).
        assert(Hsh1: sh1entryAddr block (CPaddr (block+sh1offset)) s0).
        {
          unfold sh1entryAddr. unfold bentryStartAddr in *.
          destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; congruence.
        }
        specialize(HchildIsChild part block (CPaddr (block+sh1offset)) child HpartIsPart HblockMapped Hsh1 HPDchild
          HbeqChildNull).
        apply IL.childrenPartitionInPartitionList with part; trivial; unfold deleteProps in *; intuition.
      }
      rewrite HgetConfigBEqss0; trivial. rewrite HgetChildrenEqss0; trivial. split; trivial. split.
      - intros addr child2 HaddrInBlock Hchild2IsChild. assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
        {
          simpl. simpl in HaddrInBlock. rewrite HlookupsEq in HaddrInBlock; trivial. rewrite Hs2 in HaddrInBlock.
          simpl in HaddrInBlock. rewrite beqAddrFalse in HbeqSh1Block. rewrite HbeqSh1Block in *.
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrInBlock.
          simpl in HaddrInBlock. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        specialize(HaddrsNotInChildren addr child2 HaddrInBlocks0 Hchild2IsChild). rewrite HgetMappedPEqss0; trivial.
        apply IL.childrenPartitionInPartitionList with part; trivial; unfold deleteProps in *; intuition.
      - intros addr endaddr part2 Hend Hpart2IsPart HlebStartDeadAddr HltAddrEnd. unfold bentryEndAddr in *.
        rewrite HlookupsEq in Hend; trivial. rewrite Hs2 in Hend. simpl in Hend. rewrite beqAddrFalse in HbeqSh1Block.
        rewrite HbeqSh1Block in *. rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        assert(Hends0: bentryEndAddr block endaddr s0).
        {
          unfold bentryEndAddr. rewrite Hs1 in Hend. simpl in Hend. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        specialize(HdeadAddrs addr endaddr part2 Hends0 Hpart2IsPart HlebStartDeadAddr HltAddrEnd).
        rewrite HgetConfigEqss0; trivial.
      (* END sharedBlockNoPDflagNoLocIsKern *)
    }

    assert(partitionNotAutoMapped s).
    { (* BEGIN partitionNotAutoMapped s *)
      assert(Hcons0: partitionNotAutoMapped s0) by (unfold deleteProps in *; intuition).
      intros part HpartIsPart. rewrite HgetPartsEqss0 in *. specialize(Hcons0 part HpartIsPart).
      rewrite HgetMappedPEqss0; trivial.
      (* END partitionNotAutoMapped *)
    }

    assert(configAddrNotMappedInChild s).
    { (* BEGIN configAddrNotMappedInChild s *)
      assert(Hcons0: configAddrNotMappedInChild s0) by (unfold deleteProps in *; intuition).
      intros part child addr HpartIsPart HchildIsChild HaddrIsConfig. rewrite HgetPartsEqss0 in *.
      rewrite HgetChildrenEqss0 in *; trivial. rewrite HgetConfigEqss0 in *; trivial.
      specialize(Hcons0 part child addr HpartIsPart HchildIsChild HaddrIsConfig). unfold getUsedPaddr.
      assert(In child (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with part; trivial; unfold deleteProps in *; intuition. }
      rewrite HgetConfigEqss0; trivial. rewrite HgetMappedPEqss0; trivial.
      (* END configAddrNotMappedInChild *)
    }

    assert(fullKernelIsInOneBlock s).
    { (* BEGIN fullKernelIsInOneBlock s *)
      assert(Hcons0: fullKernelIsInOneBlock s0) by (unfold deleteProps in *; intuition).
      intros part block kern HpartIsPart HblockMapped HkernInBlock HkernIsKS. rewrite HgetPartsEqss0 in *.
      rewrite HgetMappedBEqss0 in *; trivial. assert(HrangesEq: getAllPaddrAux [block] s= getAllPaddrAux [block] s0).
      {
        simpl. simpl in HkernInBlock. assert(~In block (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HkernInBlock; trivial. }
        rewrite HlookupsEq in HkernInBlock; trivial. rewrite HlookupsEq; trivial.
        rewrite Hs2 in HkernInBlock. rewrite Hs2. simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block;
          try(simpl in HkernInBlock; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; auto. rewrite Hs1 in HkernInBlock. rewrite Hs1.
        simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite HrangesEq in *. assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS in *. assert(~In kern (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HkernIsKS; trivial. }
        rewrite HlookupsEq in HkernIsKS; trivial. rewrite Hs2 in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HkernIsKS.
        simpl in HkernIsKS. destruct (beqAddr currBlock kern) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 part block kern HpartIsPart HblockMapped HkernInBlock HkernIsKSs0). assumption.
      (* END fullKernelIsInOneBlock *)
    }

    assert(forall partition block sh1entryaddr blockChild idchild,
        idchild <> blockToDelete
        -> In partition (getPartitions multiplexer s)
        -> In block (getMappedBlocks partition s)
        -> sh1entryAddr block sh1entryaddr s
        -> sh1entryPDchild sh1entryaddr idchild s
        -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
        -> idchild <> nullAddr
        -> blockChild <> nullAddr
        -> forall addr, In addr (getAllPaddrAux [block] s) -> In addr (getMappedPaddr idchild s)).
    { (* BEGIN sharedBlocksAdressesAreAllMappedInChild s *)
      assert(Hcons0: forall partition block sh1entryaddr blockChild idchild,
          idchild <> blockToDelete
          -> In partition (getPartitions multiplexer s0)
          -> In block (getMappedBlocks partition s0)
          -> sh1entryAddr block sh1entryaddr s0
          -> sh1entryPDchild sh1entryaddr idchild s0
          -> sh1entryInChildLocationWeak sh1entryaddr blockChild s0
          -> idchild <> nullAddr
          -> blockChild <> nullAddr
          -> forall addr, In addr (getAllPaddrAux [block] s0) -> In addr (getMappedPaddr idchild s0))
        by (unfold deleteProps in *; intuition).
      intros part block sh1entryaddrB blockChild child HbeqChildBTD HpartIsPart HblockMapped Hsh1 HPDchild Hloc
        HbeqChildNull HbeqLocNull addr HaddrInBlock. rewrite HgetPartsEqss0 in *.
      rewrite HgetMappedBEqss0 in *; trivial. unfold sh1entryAddr in *. simpl in HaddrInBlock.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hsh1; trivial. }
      rewrite HlookupsEq in HaddrInBlock; trivial. rewrite HlookupsEq in Hsh1; trivial.
      rewrite Hs2 in HaddrInBlock. rewrite Hs2 in Hsh1. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block;
        try(simpl in HaddrInBlock; exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: sh1entryAddr block sh1entryaddrB s0 /\ In addr (getAllPaddrAux [block] s0)).
      {
        unfold sh1entryAddr. simpl. rewrite Hs1 in HaddrInBlock. rewrite Hs1 in Hsh1.
        simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (Hsh1s0 & HaddrInBlocks0). unfold sh1entryInChildLocationWeak in *.
      unfold sh1entryPDchild in *. assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hloc; trivial. }
      rewrite HlookupsEq in Hloc; trivial. rewrite HlookupsEq in HPDchild; trivial. rewrite Hs2 in HPDchild.
      rewrite Hs2 in Hloc. simpl lookup in *. destruct (beqAddr (CPaddr (currBlock+sh1offset)) sh1entryaddrB)
        eqn:HbeqSh1s; try(simpl in Hloc; exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchild. rewrite Hs1 in Hloc. simpl lookup in *.
      destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block sh1entryaddrB blockChild child HbeqChildBTD HpartIsPart HblockMapped Hsh1s0
        HPDchild Hloc HbeqChildNull HbeqLocNull addr HaddrInBlocks0). rewrite HgetMappedPEqss0; trivial.
      assert(HchildIsChild: pdchildIsPDT s0) by (unfold deleteProps in *; intuition).
      specialize(HchildIsChild part block sh1entryaddrB child HpartIsPart HblockMapped Hsh1s0 HPDchild HbeqChildNull).
      apply IL.childrenPartitionInPartitionList with part; trivial; unfold deleteProps in *; intuition.
      (* END sharedBlocksAdressesAreAllMappedInChild *)
    }

    assert(kernInSameBlock s).
    { (* BEGIN kernInSameBlock s *)
      assert(Hcons0: kernInSameBlock s0) by (unfold deleteProps in *; intuition).
      intros parentBlock part blkidx block HpartIsPart HPBMapped HblockInRange Hblkidx. rewrite HgetPartsEqss0 in *.
      rewrite HgetMappedBEqss0 in *; trivial.
      assert(HrangesEq: getAllPaddrAux [parentBlock] s = getAllPaddrAux [parentBlock] s0).
      {
        simpl. simpl in HblockInRange. assert(~In parentBlock (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HblockInRange; trivial. }
        rewrite HlookupsEq in HblockInRange; trivial. rewrite HlookupsEq; trivial.
        rewrite Hs2 in HblockInRange. rewrite Hs2. simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) parentBlock) eqn:HbeqSh1Block;
          try(simpl in HblockInRange; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; auto. rewrite Hs1 in HblockInRange. rewrite Hs1.
        simpl lookup in *. destruct (beqAddr currBlock parentBlock) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst parentBlock. rewrite HlookupCurrBs0. rewrite HnewB. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite HrangesEq in *. unfold bentryBlockIndex in *.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hblkidx; trivial. }
      rewrite HlookupsEq in Hblkidx; trivial. rewrite Hs2 in Hblkidx. simpl in Hblkidx.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblkidxs0: bentryBlockIndex block blkidx s0).
      {
        unfold bentryBlockIndex. rewrite Hs1 in Hblkidx. simpl in Hblkidx.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 parentBlock part blkidx block HpartIsPart HPBMapped HblockInRange Hblkidxs0). assumption.
      (* END kernInSameBlock *)
    }

    assert(blockAndSh1InSameBlock s).
    { (* BEGIN blockAndSh1InSameBlock s *)
      assert(Hcons0: blockAndSh1InSameBlock s0) by (unfold deleteProps in *; intuition).
      intros part block parentBlock HpartIsPart HPBMapped HblockIsBE Hsh1InRange. rewrite HgetPartsEqss0 in *.
      rewrite HgetMappedBEqss0 in *; trivial.
      assert(HrangesEq: getAllPaddrAux [parentBlock] s = getAllPaddrAux [parentBlock] s0).
      {
        simpl. simpl in Hsh1InRange. assert(~In parentBlock (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in Hsh1InRange; trivial. }
        rewrite HlookupsEq in Hsh1InRange; trivial. rewrite HlookupsEq; trivial.
        rewrite Hs2 in Hsh1InRange. rewrite Hs2. simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) parentBlock) eqn:HbeqSh1Block;
          try(simpl in Hsh1InRange; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hsh1InRange. rewrite Hs1.
        simpl lookup in *. destruct (beqAddr currBlock parentBlock) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst parentBlock. rewrite HlookupCurrBs0. rewrite HnewB. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite HrangesEq in *. unfold isBE in *.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HblockIsBE; trivial. }
      rewrite HlookupsEq in HblockIsBE; trivial. rewrite Hs2 in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE. rewrite Hs1 in HblockIsBE. simpl in HblockIsBE.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 part block parentBlock HpartIsPart HPBMapped HblockIsBEs0 Hsh1InRange). assumption.
      (* END blockAndSh1InSameBlock *)
    }

    assert(blockAndSceInSameBlock s).
    { (* BEGIN blockAndSceInSameBlock s *)
      assert(Hcons0: blockAndSceInSameBlock s0) by (unfold deleteProps in *; intuition).
      intros part block parentBlock HpartIsPart HPBMapped HblockIsBE HsceInRange. rewrite HgetPartsEqss0 in *.
      rewrite HgetMappedBEqss0 in *; trivial.
      assert(HrangesEq: getAllPaddrAux [parentBlock] s = getAllPaddrAux [parentBlock] s0).
      {
        simpl. simpl in HsceInRange. assert(~In parentBlock (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HsceInRange; trivial. }
        rewrite HlookupsEq in HsceInRange; trivial. rewrite HlookupsEq; trivial.
        rewrite Hs2 in HsceInRange. rewrite Hs2. simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) parentBlock) eqn:HbeqSh1Block;
          try(simpl in HsceInRange; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; auto. rewrite Hs1 in HsceInRange. rewrite Hs1.
        simpl lookup in *. destruct (beqAddr currBlock parentBlock) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst parentBlock. rewrite HlookupCurrBs0. rewrite HnewB. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite HrangesEq in *. unfold isBE in *.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HblockIsBE; trivial. }
      rewrite HlookupsEq in HblockIsBE; trivial. rewrite Hs2 in HblockIsBE. simpl in HblockIsBE.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HblockIsBEs0: isBE block s0).
      {
        unfold isBE. rewrite Hs1 in HblockIsBE. simpl in HblockIsBE.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 part block parentBlock HpartIsPart HPBMapped HblockIsBEs0 HsceInRange). assumption.
      (* END blockAndSceInSameBlock *)
    }

    assert(blockAndNextInSameBlock s).
    { (* BEGIN blockAndNextInSameBlock s *)
      assert(Hcons0: blockAndNextInSameBlock s0) by (unfold deleteProps in *; intuition).
      intros part kern parentBlock HpartIsPart HPBMapped HkernIsKS HnextInRange. rewrite HgetPartsEqss0 in *.
      rewrite HgetMappedBEqss0 in *; trivial.
      assert(HrangesEq: getAllPaddrAux [parentBlock] s = getAllPaddrAux [parentBlock] s0).
      {
        simpl. simpl in HnextInRange. assert(~In parentBlock (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HnextInRange; trivial. }
        rewrite HlookupsEq in HnextInRange; trivial. rewrite HlookupsEq; trivial.
        rewrite Hs2 in HnextInRange. rewrite Hs2. simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) parentBlock) eqn:HbeqSh1Block;
          try(simpl in HnextInRange; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; auto. rewrite Hs1 in HnextInRange. rewrite Hs1.
        simpl lookup in *. destruct (beqAddr currBlock parentBlock) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst parentBlock. rewrite HlookupCurrBs0. rewrite HnewB. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite HrangesEq in *. unfold isKS in *.
      assert(~In kern (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HkernIsKS; trivial. }
      rewrite HlookupsEq in HkernIsKS; trivial. rewrite Hs2 in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) kern) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS.
        destruct (beqAddr currBlock kern) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in *. trivial.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 part kern parentBlock HpartIsPart HPBMapped HkernIsKSs0 HnextInRange). assumption.
      (* END blockAndNextInSameBlock *)
    }

    assert(forall kernel, isKS kernel s
      -> (forall block, In block (filterOptionPaddr (getKSEntries currentPart s))
            -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete sInit
            -> ~In kernel (getAllPaddrAux [block] s))
      -> exists part pdentry, In part (getPartitions multiplexer s)
          /\ lookup part (memory s) beqAddr = Some (PDT pdentry)
          /\ In kernel (completeListOfKernels (structure pdentry) s)).
    { (* BEGIN kernelIsSomePartsConfig s *)
      assert(Hcons0: forall kernel, isKS kernel s0
        -> (forall block, In block (filterOptionPaddr (getKSEntries currentPart s0))
              -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete sInit
              -> ~In kernel (getAllPaddrAux [block] s0))
        -> exists part pdentry, In part (getPartitions multiplexer s0)
            /\ lookup part (memory s0) beqAddr = Some (PDT pdentry)
            /\ In kernel (completeListOfKernels (structure pdentry) s0)) by (unfold deleteProps in *; intuition).
      intros kern HkernIsKS Hexcept. unfold isKS in *.
      assert(HkernNotInRange: ~In kern (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HkernIsKS; trivial. }
      rewrite HlookupsEq in HkernIsKS; trivial. rewrite Hs2 in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS. destruct (beqAddr currBlock kern) eqn:HbeqCBKern.
        - rewrite <-beqAddrTrue in HbeqCBKern. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in HkernIsKS. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      assert(Hexcepts0: forall block, In block (filterOptionPaddr (getKSEntries currentPart s0))
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete sInit
          -> ~In kern (getAllPaddrAux [block] s0)).
      {
        intros blockB HblockBMapped HPDchildB. rewrite <-HgetKSEqss0 in HblockBMapped; trivial.
        assert(~In blockB (getAllPaddrBlock startBlock endBlock)).
        {
          apply KSentriesAreBE in HblockBMapped. unfold isBE in *.
          intro Hcontra. rewrite HremovedAddrs in HblockBMapped; trivial.
        }
        specialize(Hexcept blockB HblockBMapped HPDchildB). simpl in Hexcept. simpl.
        rewrite HlookupsEq in Hexcept; trivial. rewrite Hs2 in Hexcept. simpl in Hexcept.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockB) eqn:HbeqSh1BlockB.
        - rewrite <-beqAddrTrue in HbeqSh1BlockB. rewrite HbeqSh1BlockB in *. rewrite HlookupSh1Eqs1s0 in *.
          destruct (lookup blockB (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). simpl. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hexcept.
          simpl in Hexcept. destruct (beqAddr currBlock blockB) eqn:HbeqBlocks.
          + rewrite <-beqAddrTrue in HbeqBlocks. subst blockB. rewrite HlookupCurrBs0. rewrite HnewB in Hexcept.
            auto.
          + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 kern HkernIsKSs0 Hexcepts0). rewrite HgetPartsEqss0.
      destruct Hcons0 as [part [pdentry (HpartIsPart & HlookupPart & HkernIsConfig)]]. exists part. exists pdentry.
      rewrite HcomplKernLEq with (part:=part); trivial. assert(~In part (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. apply HpropsForStructEqs2 in Hcontra. destruct Hcontra as (Hcontra & _).
        rewrite HgetPartsEqs2s0 in *. congruence.
      }
      rewrite HlookupsEq; trivial. split; trivial. split; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) part) eqn:HbeqSh1Part.
      {
        rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Part. subst part. rewrite HlookupPart in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock part) eqn:HbeqCBPart.
      { rewrite <-beqAddrTrue in HbeqCBPart. subst part. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END kernelIsSomePartsConfig *)
    }

    assert(HpaddrConfigEq: forall l, (forall el, In el l -> isBE el s)
      -> getAllPaddrConfigAux l s = getAllPaddrConfigAux l s0).
    {
      intros l1 HelsAreBE. induction l1; simpl; trivial. simpl in HelsAreBE.
      assert(HelsAreBERec: forall el, In el l1 -> isBE el s).
      { intros. apply HelsAreBE; auto. }
      specialize(IHl1 HelsAreBERec). assert(Htriv: a1 = a1 \/ In a1 l1) by auto. specialize(HelsAreBE a1 Htriv).
      rewrite IHl1. unfold isBE in *. assert(~In a1 (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HelsAreBE; trivial. }
      rewrite HlookupsEq; trivial. rewrite HlookupsEq in HelsAreBE; trivial. rewrite Hs2. rewrite Hs2 in HelsAreBE.
      simpl lookup in *. destruct (beqAddr (CPaddr (currBlock+sh1offset)) a1) eqn:HbeqSh1A; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1. simpl lookup.
      destruct (beqAddr currBlock a1) eqn:HbeqBlocks.
      - rewrite <-beqAddrTrue in HbeqBlocks. subst a1. rewrite HlookupCurrBs0. reflexivity.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }

    assert(PDTisNoConfigInChild s).
    { (* BEGIN PDTisNoConfigInChild s *)
      assert(Hcons0: PDTisNoConfigInChild s0) by (unfold deleteProps in *; intuition).
      intros pdparent child pdentry block sh1entryaddrB addr HparentIsPart HchildIsChild HlookupChild HblockMapped
        Hsh1 HPDflag HaddrInBlock. rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in *; trivial.
      rewrite HgetChildrenEqss0 in *; trivial. assert(~In child (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. rewrite HremovedAddrs in HlookupChild; trivial. congruence.
      }
      rewrite HlookupsEq in HlookupChild; trivial. rewrite Hs2 in HlookupChild. simpl in HlookupChild.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) child) eqn:HbeqSh1Child; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupChild.
      simpl in HlookupChild. destruct (beqAddr currBlock child) eqn:HbeqCBChild; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: sh1entryAddr block sh1entryaddrB s0 /\ In addr (getAllPaddrAux [block] s0)).
      {
        unfold sh1entryAddr in *. simpl. simpl in HaddrInBlock.
        assert(~In block (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HaddrInBlock; trivial. }
        rewrite HlookupsEq in HaddrInBlock; trivial. rewrite HlookupsEq in Hsh1; trivial.
        rewrite Hs2 in HaddrInBlock. rewrite Hs2 in Hsh1. simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrInBlock.
        rewrite Hs1 in Hsh1. simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (Hsh1s0 & HaddrInBlocks0). unfold sh1entryPDflag in *.
      assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HPDflag; trivial. }
      rewrite HlookupsEq in HPDflag; trivial. rewrite Hs2 in HPDflag. simpl in HPDflag.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) sh1entryaddrB) eqn:HbeqSh1s;
        try(simpl in HPDflag; exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      rewrite Hs1 in HPDflag. simpl in HPDflag.
      destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; auto. specialize(Hcons0 pdparent child pdentry block sh1entryaddrB addr
        HparentIsPart HchildIsChild HlookupChild HblockMapped Hsh1s0 HPDflag HaddrInBlocks0).
      assert(forall el, In el (getConfigBlocks child s) -> isBE el s).
      { intro. apply configBlocksAreBE. }
      rewrite HpaddrConfigEq; trivial. rewrite HgetConfigBEqss0; trivial.
      apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition.
      (* END PDTisNoConfigInChild *)
    }

    assert(PDTisNoConfigInPart s).
    { (* BEGIN PDTisNoConfigInPart s *)
      assert(Hcons0: PDTisNoConfigInPart s0) by (unfold deleteProps in *; intuition).
      intros pdparent block sh1entryaddrB addr HparentIsPart HblockMapped Hsh1 HPDflag HaddrInBlock.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in *; trivial.
      assert(Hblocks0: sh1entryAddr block sh1entryaddrB s0 /\ In addr (getAllPaddrAux [block] s0)).
      {
        unfold sh1entryAddr in *. simpl. simpl in HaddrInBlock.
        assert(~In block (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HaddrInBlock; trivial. }
        rewrite HlookupsEq in HaddrInBlock; trivial. rewrite HlookupsEq in Hsh1; trivial.
        rewrite Hs2 in HaddrInBlock. rewrite Hs2 in Hsh1. simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrInBlock.
        rewrite Hs1 in Hsh1. simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (Hsh1s0 & HaddrInBlocks0). unfold sh1entryPDflag in *.
      assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HPDflag; trivial. }
      rewrite HlookupsEq in HPDflag; trivial. rewrite Hs2 in HPDflag. simpl in HPDflag.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) sh1entryaddrB) eqn:HbeqSh1s;
        try(simpl in HPDflag; exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      rewrite Hs1 in HPDflag. simpl in HPDflag.
      destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 pdparent block sh1entryaddrB addr HparentIsPart HblockMapped Hsh1s0 HPDflag HaddrInBlocks0).
      rewrite HgetConfigEqss0; trivial.
      (* END PDTisNoConfigInPart *)
    }

    assert(usedPaddrAreShared s).
    { (* BEGIN usedPaddrAreShared s *)
      assert(Hcons0: usedPaddrAreShared s0) by (unfold deleteProps in *; intuition).
      intros child pdparent block addr HparentIsPart HchildIsChild HaddrUsedC HblockMapped HaddrInBlock.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in *; trivial. rewrite HgetChildrenEqss0 in *; trivial.
      assert(HchildIsPart: In child (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition. }
      assert(forall el, In el (getConfigBlocks child s) -> isBE el s).
      { intro. apply configBlocksAreBE. }
      rewrite HpaddrConfigEq in *; trivial. rewrite HgetConfigBEqss0 in *; trivial.
      rewrite HgetMappedPEqss0 in *; trivial. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { simpl in HaddrInBlock. intro. rewrite HremovedAddrs in HaddrInBlock; trivial. }
      assert(HaddrInBlocks0: In addr (getAllPaddrAux [block] s0)).
      {
        simpl. simpl in HaddrInBlock. rewrite HlookupsEq in HaddrInBlock; trivial. rewrite Hs2 in HaddrInBlock.
        simpl lookup in *. destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block;
          try(simpl in HaddrInBlock; exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrInBlock.
        simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 child pdparent block addr HparentIsPart HchildIsChild HaddrUsedC HblockMapped HaddrInBlocks0).
      unfold sh1entryPDchild in *. assert(~In (CPaddr (block+sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy (CPaddr (block+sh1offset)) Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & _ & _ & _ & _ & Hsh1InSameBlock & _).
        assert(HblockIsBE: isBE block s0).
        {
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)]. unfold isBE.
          rewrite Hlookup. trivial.
        }
        assert(HeqTriv: CPaddr (block + sh1offset) = CPaddr (block + sh1offset)) by reflexivity.
        specialize(Hsh1InSameBlock block HblockIsBE HeqTriv). congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s.
      {
        rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. subst block. rewrite Hranges0 in *.
        specialize(HpropsAddrToRemoveCopy addr HaddrInBlocks0).
        destruct HpropsAddrToRemoveCopy as (_ & HaddrNotConfig & HaddrNotMappedChild & _).
        assert(pdparent = currentPart).
        {
          destruct (beqAddr pdparent currentPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption). exfalso.
          rewrite <-beqAddrFalse in *. unfold getMappedBlocks in *. apply InFilterPresentInList in HCBMapped.
          apply InFilterPresentInList in HblockMapped.
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold deleteProps in *; intuition).
          specialize(Hdisjoint pdparent currentPart HparentIsPart HcurrIsPart HbeqParts).
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint currBlock HblockMapped). congruence.
        }
        subst pdparent. specialize(HaddrNotConfig child HchildIsPart).
        destruct HaddrNotConfig as (_ & HaddrNotConfig). specialize(HaddrNotMappedChild child HchildIsChild).
        unfold getConfigPaddr in *. apply Lib.in_app_or_neg in HaddrNotConfig.
        destruct HaddrNotConfig as (_ & HaddrNotConfig). apply in_app_or in HaddrUsedC.
        destruct HaddrUsedC; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (block + sh1offset))) eqn:HbeqCBSh1.
      { rewrite <-beqAddrTrue in HbeqCBSh1. rewrite <-HbeqCBSh1 in *. rewrite HlookupCurrBs0 in *. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END usedPaddrAreShared *)
    }

    assert(indexIsDistFromKern s).
    { (* BEGIN indexIsDistFromKern s *)
      assert(Hcons0: indexIsDistFromKern s0) by (unfold deleteProps in *; intuition).
      intros kern idx HkernIsKS HltIdxNbKern. unfold isKS in *.
      assert(HkernNotInRange: ~In kern (getAllPaddrBlock startBlock endBlock)).
      { intro Hcontra. rewrite HremovedAddrs in HkernIsKS; trivial. }
      rewrite HlookupsEq in HkernIsKS; trivial. rewrite Hs2 in HkernIsKS. simpl in HkernIsKS.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) kern) eqn:HbeqSh1Kern; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HkernIsKSs0: isKS kern s0).
      {
        unfold isKS. rewrite Hs1 in HkernIsKS. simpl in HkernIsKS. destruct (beqAddr currBlock kern) eqn:HbeqCBKern.
        - rewrite <-beqAddrTrue in HbeqCBKern. subst kern. rewrite HlookupCurrBs0. rewrite HnewB in HkernIsKS. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      specialize(Hcons0 kern idx HkernIsKSs0 HltIdxNbKern). unfold bentryBlockIndex in *.
      assert(~In (CPaddr (kern+idx)) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. assert(HkernInSameBlock: kernInSameBlock s0) by (unfold deleteProps in *; intuition).
        rewrite <-Hranges0 in *. specialize(HkernInSameBlock currBlock currentPart idx (CPaddr (kern+idx)) HcurrIsPart
          HCBMapped Hcontra Hcons0).
        assert(Heq: CPaddr (CPaddr (kern + idx) - idx) = kern).
        {
          assert(kern + idx <= maxAddr).
          {
            unfold CPaddr in Hcons0. destruct (Compare_dec.le_dec (kern + idx) maxAddr); try(lia). exfalso.
            assert(Hnull: isPADDR nullAddr s0) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
            cbn in Hnull. replace {| p := 0; Hp := ADT.CPaddr_obligation_1 0 (PeanoNat.Nat.le_0_l maxAddr) |}
              with {| p := 0; Hp := ADT.CPaddr_obligation_2 (kern + idx) n0 |} in *;
              try(f_equal; apply proof_irrelevance).
            destruct (lookup {| p:= 0; Hp:= ADT.CPaddr_obligation_2 (kern+idx) n0 |} (memory s0) beqAddr);
              try(congruence). destruct v; congruence.
          }
          unfold CPaddr. destruct (Compare_dec.le_dec (kern + idx) maxAddr); try(lia). simpl.
          rewrite PeanoNat.Nat.add_sub. assert(kern <= maxAddr) by (apply Hp).
          destruct (Compare_dec.le_dec kern maxAddr); try(lia). apply paddrEqNatEqEquiv. reflexivity.
        }
        rewrite Heq in *. congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (kern + idx))) eqn:HbeqSh1Block.
      {
        rewrite <-beqAddrTrue in HbeqSh1Block. rewrite HbeqSh1Block in *. rewrite HlookupSh1Eqs1s0 in *.
        destruct (lookup (CPaddr (kern + idx)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (kern + idx))) eqn:HbeqCBBlock.
      - rewrite <-beqAddrTrue in HbeqCBBlock. rewrite HbeqCBBlock in *. rewrite HlookupCurrBs0 in *. rewrite HnewB.
        auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END indexIsDistFromKern *)
    }

    assert(noDupMappedPaddrList s).
    { (* BEGIN noDupMappedPaddrList s *)
      assert(Hcons0: noDupMappedPaddrList s0) by (unfold deleteProps in *; intuition).
      intros partition HpartIsPart. rewrite HgetPartsEqss0 in *. specialize(Hcons0 partition HpartIsPart).
      rewrite HgetMappedPEqss0; assumption.
      (* END noDupMappedPaddrList *)
    }

    assert(accessibleParentPaddrIsAccessibleIntoChild s).
    { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
      assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s0) by (unfold deleteProps in *; intuition).
      intros pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParent HaddrMappedChild.
      rewrite HgetPartsEqss0 in *. rewrite HgetChildrenEqss0 in *; trivial.
      assert(In child (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition. }
      rewrite HgetMappedPEqss0 in *; trivial.
      assert(HaddrAccMappedParents0: In addr (getAccessibleMappedPaddr pdparent s0)).
      {
        destruct (beqAddr currentPart pdparent) eqn:HbeqCurrParent.
        - rewrite <-beqAddrTrue in HbeqCurrParent. subst pdparent. destruct (accessible bentry0).
          + assert(HeqTriv: true = true) by reflexivity. rewrite <-HgetAccMappedPEqCurrss0; trivial.
          + assert(HeqTriv: false = false) by reflexivity. specialize(HgetAccMappedPImplCurrss0 HeqTriv).
            apply HgetAccMappedPImplCurrss0 in HaddrAccMappedParent. apply in_app_or in HaddrAccMappedParent.
            destruct HaddrAccMappedParent as [HaddrInR | Hres]; trivial. exfalso.
            specialize(HpropsAddrToRemoveCopy addr HaddrInR).
            destruct HpropsAddrToRemoveCopy as (_ & _ & HaddrNotMappedChildren & _).
            specialize(HaddrNotMappedChildren child HchildIsChild). congruence.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetAccMappedPEqss0NotCurr; trivial.
      }
      specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccMappedParents0 HaddrMappedChild).
      destruct (beqAddr currentPart child) eqn:HbeqCurrChild.
      - rewrite <-beqAddrTrue in HbeqCurrChild. subst child. destruct (accessible bentry0).
        + assert(HeqTriv: true = true) by reflexivity. rewrite HgetAccMappedPEqCurrss0; trivial.
        + assert(HeqTriv: false = false) by reflexivity. specialize(HgetAccMappedPImplCurrss0 HeqTriv).
          apply HgetAccMappedPImplCurrss0. apply in_or_app. auto.
      - rewrite <-beqAddrFalse in *. rewrite HgetAccMappedPEqss0NotCurr; trivial.
      (* END accessibleParentPaddrIsAccessibleIntoChild *)
    }

    assert(sharedBlockPointsToChild s).
    { (* BEGIN sharedBlockPointsToChild s *)
      assert(Hcons0: sharedBlockPointsToChild s0) by (unfold deleteProps in *; intuition).
      intros pdparent child addr blockParent sh1entryaddrB HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParent HblockParentMapped Hsh1. rewrite HgetPartsEqss0 in *.
      rewrite HgetChildrenEqss0 in *; trivial. assert(HchildIsPart: In child (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition. }
      unfold getUsedPaddr in *. rewrite HgetConfigEqss0 in *; trivial. rewrite HgetMappedPEqss0 in *; trivial.
      rewrite HgetMappedBEqss0 in *; trivial. unfold sh1entryAddr in *. simpl in HaddrInBlockParent.
      assert(~In blockParent (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hsh1; trivial. }
      assert(Hsh1IsSHE: isSHE (CPaddr (blockParent + sh1offset)) s).
      {
        assert(Hres: wellFormedFstShadowIfBlockEntry s) by assumption. assert(HBPIsBE: isBE blockParent s).
        {
          unfold isBE. destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; try(congruence).
          trivial.
        }
        specialize(Hres blockParent HBPIsBE). assumption.
      }
      unfold isSHE in *. assert(~In (CPaddr (blockParent + sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hsh1IsSHE; trivial. }
      clear HlookupBTDs. unfold sh1entryPDflag. unfold sh1entryPDchild. rewrite HlookupsEq in *; trivial.
      rewrite Hs2 in Hsh1. rewrite Hs2 in HaddrInBlockParent. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) blockParent) eqn:HbeqSh1BP; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      rewrite Hs1 in Hsh1. rewrite Hs1 in HaddrInBlockParent. simpl lookup in *.
      destruct (beqAddr currBlock blockParent) eqn:HbeqBlocks.
      {
        rewrite <-beqAddrTrue in HbeqBlocks. subst blockParent. rewrite HnewB in HaddrInBlockParent.
        simpl in HaddrInBlockParent. assert(HaddrInR: In addr (getAllPaddrAux [currBlock] s0)).
        { simpl. rewrite HlookupCurrBs0. assumption. }
        rewrite Hranges0 in *. specialize(HpropsAddrToRemoveCopy addr HaddrInR).
        destruct HpropsAddrToRemoveCopy as (_ & HaddrNotConf & HaddrNotMappedChildren & _). exfalso.
        specialize(HaddrNotConf child HchildIsPart). destruct HaddrNotConf as (_ & HaddrNotConf).
        assert(pdparent = currentPart).
        {
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold deleteProps in *; intuition).
          destruct (beqAddr pdparent currentPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. assert(HparentIsPDT: isPDT pdparent s0).
          {
            unfold getChildren in *. unfold isPDT.
            destruct (lookup pdparent (memory s0) beqAddr); try(simpl in HchildIsChild; congruence).
            destruct v; try(simpl in HchildIsChild; congruence). trivial.
          }
          specialize(Hdisjoint pdparent currentPart HparentIsPart HcurrIsPart HbeqParts). unfold getMappedBlocks in *.
          apply InFilterPresentInList in HblockParentMapped.
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint currBlock HblockParentMapped). congruence.
        }
        subst pdparent. specialize(HaddrNotMappedChildren child HchildIsChild). apply in_app_or in HaddrUsedChild.
        destruct HaddrUsedChild; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 pdparent child addr blockParent sh1entryaddrB HparentIsPart HchildIsChild HaddrUsedChild
        HaddrInBlockParent HblockParentMapped Hsh1). rewrite Hs2 in Hsh1IsSHE. rewrite Hs2. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (blockParent + sh1offset))) eqn:HbeqSh1s.
      { rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. exfalso; congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hsh1IsSHE. rewrite Hs1.
      simpl lookup in *.
      destruct (beqAddr currBlock (CPaddr (blockParent+sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END sharedBlockPointsToChild *)
    }

    assert(adressesRangePreservedIfOriginAndNextOk s).
    { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
      assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0) by (unfold deleteProps in *; intuition).
      intros partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped HblockIsBE HstartBlock
        HendBlock HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. rewrite HgetPartsEqss0 in *.
      clear HlookupBTDs. unfold bentryStartAddr in *. assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupPart; trivial. congruence. }
      unfold bentryPFlag in *. unfold bentryEndAddr in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HstartBlock; trivial. }
      unfold isBE in *. unfold scentryOrigin in *. assert(~In scentryaddr (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Horigin; trivial. }
      unfold scentryNext in *. rewrite HlookupsEq in *; trivial. rewrite Hs2 in HblockIsBE. rewrite Hs2 in HPflag.
      rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. rewrite Hs2 in Horigin. rewrite Hs2 in Hnext.
      rewrite Hs2 in HlookupPart. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) scentryaddr) eqn:HbeqSh1Sce; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: isBE block s0 /\ bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0
        /\ bentryPFlag block true s0).
      {
        unfold isBE. unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryPFlag. rewrite Hs1 in HblockIsBE.
        rewrite Hs1 in HPflag. rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock. simpl lookup in *.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (HblockIsBEs0 & HstartBlocks0 & HendBlocks0 & HPflags0). rewrite Hs1 in Horigin.
      rewrite Hs1 in Hnext. rewrite Hs1 in HlookupPart. simpl lookup in *.
      destruct (beqAddr currBlock scentryaddr) eqn:HbeqCBSce; try(exfalso; congruence).
      destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(In (parent pdentry) (getPartitions multiplexer s0)).
      {
        assert(HparentOfPart: exists wrongParts,
            (forall partition entry,
              lookup partition (memory s0) beqAddr = Some (PDT entry)
              -> (~In (parent entry) wrongParts
                  -> partition <> constantRootPartM
                  -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                      /\ In (parent entry) (getPartitions multiplexer s0))
                /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
            /\ (forall oldPart, In oldPart wrongParts
                -> (forall desc, In desc (getPartitions oldPart s0)
                    -> desc <> blockToDelete
                    -> ~In desc (getPartitions multiplexer s0))))
          by (unfold deleteProps in *; intuition).
        destruct HparentOfPart as [wrongParts (HparentOfPart & HwrongParts)].
        specialize(HparentOfPart partition pdentry HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
        assert(HbeqPartBTD: partition <> blockToDelete).
        { intro. subst partition. congruence. }
        assert(HparentNotWrong: ~In (parent pdentry) wrongParts).
        {
          intro Hcontra. assert(HpartIsDesc: In partition (getPartitions (parent pdentry) s0)).
          {
            unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. right.
            assert(HpartIsChild: isChild s0) by (unfold deleteProps in *; intuition).
            assert(Hparent: pdentryParent partition (parent pdentry) s0).
            { unfold pdentryParent. rewrite HlookupPart. reflexivity. }
            specialize(HpartIsChild partition (parent pdentry) HpartIsPart Hparent HbeqPartRoot).
            induction (getChildren (parent pdentry) s0); simpl in *; only 1: congruence. apply in_or_app.
            destruct HpartIsChild as [Heq | HpartIsChild]; auto. subst a1. left.
            replace (maxAddr+1) with (S maxAddr); try(lia). simpl. auto.
          }
          specialize(HwrongParts (parent pdentry) Hcontra partition HpartIsDesc HbeqPartBTD). congruence.
        }
        apply HparentIsPart; assumption.
      }
      rewrite HgetMappedBEqss0 in HblockMapped; trivial.
      specialize(Hcons0 partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped HblockIsBEs0
        HstartBlocks0 HendBlocks0 HPflags0 Hsce Horigin Hnext HlookupPart HbeqPartRoot).
      destruct Hcons0 as [blockParent (HBPMapped & HBPIsBE & HstartBP & HendBP)]. unfold bentryEndAddr in *.
      rewrite <-HgetMappedBEqss0 in HBPMapped; trivial. exists blockParent. split; trivial.
      apply IL.mappedBlockIsBE in HBPMapped. destruct HBPMapped as [bentry (HlookupBP & _)].
      unfold bentryStartAddr in *. assert(~In blockParent (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupBP; trivial. congruence. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HlookupBP. rewrite Hs2. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockParent) eqn:HbeqSh1BP; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
      - rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. rewrite HnewB. rewrite HlookupCurrBs0 in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      (* END adressesRangePreservedIfOriginAndNextOk *)
    }

    assert(childsBlocksPropsInParent s).
    { (* BEGIN childsBlocksPropsInParent s *)
      assert(Hcons0: childsBlocksPropsInParent s0) by (unfold deleteProps in *; intuition).
      intros child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
        HchildIsChild HblockChildMapped HstartChild HendChild HPflagChild HblockParentMapped HstartParent HendParent
        HPflagParent HlebStart HgebEnd. rewrite HgetPartsEqss0 in *.
      rewrite HgetChildrenEqss0 in *; trivial. assert(HchildIsPart: In child (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition. }
      rewrite HgetMappedBEqss0 in *; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      unfold bentryPFlag in *. unfold checkChild. unfold bentryAFlag. clear HlookupBTDs.
      assert(HBPIsBE: isBE blockParent s).
      {
        unfold isBE. destruct (lookup blockParent (memory s) beqAddr); try(congruence). destruct v; try(congruence).
        trivial.
      }
      assert(~In blockChild (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HstartChild; trivial. }
      assert(~In blockParent (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HstartParent; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HstartChild. rewrite Hs2 in HendChild.
      rewrite Hs2 in HPflagChild. rewrite Hs2 in HstartParent. rewrite Hs2 in HendParent. rewrite Hs2 in HPflagParent.
      rewrite Hs2. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockChild) eqn:HbeqSh1BC; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockParent) eqn:HbeqSh1BP; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HBCs0: bentryStartAddr blockChild startChild s0 /\ bentryEndAddr blockChild endChild s0
        /\ bentryPFlag blockChild true s0).
      {
        unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryPFlag. rewrite Hs1 in HstartChild.
        rewrite Hs1 in HendChild. rewrite Hs1 in HPflagChild. simpl lookup in *.
        destruct (beqAddr currBlock blockChild) eqn:HbeqCBBC.
        - rewrite <-beqAddrTrue in *. subst blockChild. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      assert(HBPs0: bentryStartAddr blockParent startParent s0 /\ bentryEndAddr blockParent endParent s0
        /\ bentryPFlag blockParent true s0).
      {
        unfold bentryStartAddr. unfold bentryEndAddr. unfold bentryPFlag. rewrite Hs1 in HstartParent.
        rewrite Hs1 in HendParent. rewrite Hs1 in HPflagParent. simpl lookup in *.
        destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
        - rewrite <-beqAddrTrue in *. subst blockParent. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct HBCs0 as (HstartChilds0 & HendChilds0 & HPflagChilds0).
      destruct HBPs0 as (HstartParents0 & HendParents0 & HPflagParents0).
      specialize(Hcons0 child pdparent blockChild startChild endChild blockParent startParent endParent HparentIsPart
        HchildIsChild HblockChildMapped HstartChilds0 HendChilds0 HPflagChilds0 HblockParentMapped HstartParents0
        HendParents0 HPflagParents0 HlebStart HgebEnd).
      destruct Hcons0 as (HcheckChild & HPDchildNotNull & HlocNotNull & HnotAccIfWrongBounds).
      assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s) by assumption.
      specialize(Hsh1IsSHE blockParent HBPIsBE). unfold isSHE in *. unfold sh1entryInChildLocation.
      unfold sh1entryPDchild. assert(~In (CPaddr (blockParent + sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hsh1IsSHE; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in Hsh1IsSHE. rewrite Hs2. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (blockParent + sh1offset))) eqn:HbeqSh1s.
      {
        rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. subst blockParent. exfalso.
        assert(pdparent = currentPart).
        {
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold deleteProps in *; intuition).
          destruct (beqAddr pdparent currentPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. assert(HparentIsPDT: isPDT pdparent s0).
          {
            unfold getChildren in *. unfold isPDT.
            destruct (lookup pdparent (memory s0) beqAddr); try(simpl in HchildIsChild; congruence).
            destruct v; try(simpl in HchildIsChild; congruence).
          }
          specialize(Hdisjoint pdparent currentPart HparentIsPart HcurrIsPart HbeqParts). unfold getMappedBlocks in *.
          apply InFilterPresentInList in HblockParentMapped.
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint currBlock HblockParentMapped). congruence.
        }
        subst pdparent. assert(Hbounds: startParent = startBlock /\ endParent = endBlock).
        {
          unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupCurrBs0 in *.
          rewrite <-HstartCBs0 in *. rewrite <-HendCBs0 in *. auto.
        }
        destruct Hbounds. subst startParent. subst endParent.
        assert(Hwell: wellFormedBlock s0) by (unfold deleteProps in *; intuition).
        specialize(Hwell blockChild startChild endChild HPflagChilds0 HstartChilds0 HendChilds0).
        destruct Hwell as (Hwell & _). assert(HstartCInR: In startChild (getAllPaddrBlock startBlock endBlock)).
        { apply IL.getAllPaddrBlockIncl; lia. }
        assert(HstartCInChild: In startChild (getMappedPaddr child s0)).
        {
          apply IL.addrInBlockIsMapped with blockChild; trivial. simpl. unfold bentryStartAddr in *.
          unfold bentryEndAddr in *. destruct (lookup blockChild (memory s0) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite <-HstartChilds0. rewrite <-HendChilds0. rewrite app_nil_r.
          apply IL.getAllPaddrBlockIncl; lia.
        }
        specialize(HpropsAddrToRemoveCopy startChild HstartCInR).
        destruct HpropsAddrToRemoveCopy as (_ & _ & HstartCNotInChildren & _).
        specialize(HstartCNotInChildren child HchildIsChild). congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HlookupSh1Eq: lookup (CPaddr (blockParent + sh1offset)) (memory s1) beqAddr
        = lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr).
      {
        rewrite Hs1 in Hsh1IsSHE. rewrite Hs1. simpl lookup in *.
        destruct (beqAddr currBlock (CPaddr (blockParent + sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite HlookupSh1Eq in *. split; only 2: (split; only 2: split); trivial.
      - unfold checkChild in *. rewrite Hs1. simpl. destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
        + rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. rewrite HlookupCurrBs0 in *. assumption.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      - intros blockIDInChild Hloc.
        assert(Hlocs0: sh1entryInChildLocation (CPaddr (blockParent+sh1offset)) blockIDInChild s0).
        {
          unfold sh1entryInChildLocation.
          destruct (lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). destruct Hloc as (Hloc & HlocIsBE). split; trivial. intro HbeqLocNull.
          specialize(HlocIsBE HbeqLocNull). unfold isBE in *.
          assert(~In blockIDInChild (getAllPaddrBlock startBlock endBlock)).
          { intro. rewrite HremovedAddrs in HlocIsBE; trivial. }
          rewrite HlookupsEq in *; trivial. rewrite Hs2 in HlocIsBE. simpl in HlocIsBE.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockIDInChild) eqn:HbeqSh1Loc; try(exfalso; congruence).
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlocIsBE.
          simpl in HlocIsBE. destruct (beqAddr currBlock blockIDInChild) eqn:HbeqCBLoc.
          - rewrite <-beqAddrTrue in HbeqCBLoc. rewrite HbeqCBLoc in *. rewrite HlookupCurrBs0. trivial.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        apply HlocNotNull; assumption.
      - intro HwrongBounds. specialize(HnotAccIfWrongBounds HwrongBounds). rewrite Hs1. simpl.
        destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
        { rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. exfalso; congruence. }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END childsBlocksPropsInParent *)
    }

    assert(noChildImpliesAddressesNotShared s).
    { (* BEGIN noChildImpliesAddressesNotShared s *)
      assert(Hcons0: noChildImpliesAddressesNotShared s0) by (unfold deleteProps in *; intuition).
      intros partition pdentry block sh1entryaddrB HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild child addr
        HchildIsChild HaddrInBlock. rewrite HgetPartsEqss0 in *. rewrite HgetChildrenEqss0 in *; trivial.
      assert(HchildIsPart: In child (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with partition; trivial; unfold deleteProps in *; intuition. }
      rewrite HgetMappedBEqss0 in *; trivial. simpl in HaddrInBlock. unfold sh1entryPDchild in *.
      clear HlookupBTDs. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HaddrInBlock; trivial. }
      rewrite HgetMappedPEqss0; trivial. assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDchild; trivial. }
      assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupPart; trivial. congruence. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HlookupPart. rewrite Hs2 in HaddrInBlock. simpl in HlookupPart.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      simpl in HaddrInBlock. destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block;
        try(simpl in HaddrInBlock; exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupPart. simpl in HlookupPart.
      destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence). rewrite <-beqAddrFalse in *.
      rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrInBlock. simpl in HaddrInBlock.
      destruct (beqAddr currBlock block) eqn:HbeqBlocks.
      {
        rewrite <-beqAddrTrue in HbeqBlocks. subst block. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
        rewrite HnewB in HaddrInBlock. rewrite HlookupCurrBs0 in *. simpl in HaddrInBlock. rewrite <-HstartCBs0 in *.
        rewrite <-HendCBs0 in *. rewrite app_nil_r in *. specialize(HpropsAddrToRemoveCopy addr HaddrInBlock).
        destruct HpropsAddrToRemoveCopy as (_ & _ & Hres & _). apply Hres.
        assert(partition = currentPart).
        {
          assert(Hdisjoint: DisjointKSEntries s0) by (unfold deleteProps in *; intuition).
          destruct (beqAddr partition currentPart) eqn:HbeqParts; try(rewrite beqAddrTrue; assumption).
          rewrite <-beqAddrFalse in *. assert(HparentIsPDT: isPDT partition s0).
          { unfold isPDT. rewrite HlookupPart. trivial. }
          specialize(Hdisjoint partition currentPart HpartIsPart HcurrIsPart HbeqParts). unfold getMappedBlocks in *.
          apply InFilterPresentInList in HblockMapped.
          destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
          specialize(Hdisjoint currBlock HblockMapped). congruence.
        }
        subst partition. assumption.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs2 in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) sh1entryaddrB) eqn:HbeqSh1s.
      {
        subst sh1entryaddrB. rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchild. simpl in HPDchild.
      destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition pdentry block sh1entryaddrB HpartIsPart HlookupPart HblockMapped Hsh1 HPDchild
        child addr HchildIsChild HaddrInBlock). assumption.
      (* END noChildImpliesAddressesNotShared *)
    }

    assert(kernelsAreNotAccessible s).
    { (* BEGIN kernelsAreNotAccessible s *)
      assert(Hcons0: kernelsAreNotAccessible s0) by (unfold deleteProps in *; intuition).
      intros block startaddr part HpartIsPart HblockMapped Hstart HstartIsKS. rewrite HgetPartsEqss0 in *.
      rewrite HgetMappedBEqss0 in *; trivial. unfold isKS in *. unfold bentryStartAddr in *. unfold bentryAFlag.
      clear HlookupBTDs. assert(HstartNotInR: ~In startaddr (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HstartIsKS; trivial. }
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hstart; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in Hstart. rewrite Hs2 in HstartIsKS. rewrite Hs2.
      simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) startaddr) eqn:HbeqSh1Start; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. assert(HstartIsKSs0: isKS startaddr s0).
      {
        unfold isKS. rewrite Hs1 in HstartIsKS. simpl in HstartIsKS.
        destruct (beqAddr currBlock startaddr) eqn:HbeqCBStart.
        - rewrite <-beqAddrTrue in HbeqCBStart. subst startaddr. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite Hs1 in Hstart. rewrite Hs1. simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
      {
        exfalso. rewrite HnewB in Hstart. simpl in Hstart. rewrite HlookupCurrBs0 in HstartCBs0.
        rewrite <-HstartCBs0 in *. subst startaddr. contradict HstartNotInR. apply IL.getAllPaddrBlockIncl; lia.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 block startaddr part HpartIsPart HblockMapped Hstart HstartIsKSs0). assumption.
      (* END kernelsAreNotAccessible *)
    }

    assert(blockAndNextAreSideBySide s).
    { (* BEGIN blockAndNextAreSideBySide s *)
      assert(Hcons0: blockAndNextAreSideBySide s0) by (unfold deleteProps in *; intuition).
      intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlock Hsce HbeqNextNull Hnext.
      rewrite HgetPartsEqss0 in *. rewrite HgetMappedBEqss0 in *; trivial. unfold bentryEndAddr in *.
      unfold scentryNext in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HendBlock; trivial. }
      clear HlookupBTDs. assert(~In scentryaddr (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hnext; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HendBlock. rewrite Hs2 in Hnext. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) scentryaddr) eqn:HbeqSh1Sce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(HendBlocks0: bentryEndAddr block endaddr s0).
      {
        unfold bentryEndAddr. rewrite Hs1 in HendBlock. simpl in HendBlock.
        destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      rewrite Hs1 in Hnext. simpl in Hnext.
      destruct (beqAddr currBlock scentryaddr) eqn:HbeqCBSce; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped HendBlocks0 Hsce
        HbeqNextNull Hnext). destruct Hcons0 as (HstartNext & HnextMapped). split; trivial.
      rewrite <-HgetMappedBEqss0 in HnextMapped; trivial. apply IL.mappedBlockIsBE in HnextMapped.
      destruct HnextMapped as [bentry (HlookupNext & _)]. assert(~In scnext (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupNext; trivial. congruence. }
      unfold bentryStartAddr in *. rewrite HlookupsEq in *; trivial. rewrite Hs2 in HlookupNext. rewrite Hs2.
      simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) scnext) eqn:HbeqSh1Next; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HlookupNext. rewrite Hs1.
      simpl lookup in *. destruct (beqAddr currBlock scnext) eqn:HbeqCBNext.
      - rewrite <-beqAddrTrue in HbeqCBNext. subst scnext. rewrite HnewB. rewrite HlookupCurrBs0 in *. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END blockAndNextAreSideBySide *)
    }

    assert(parentBlocksBoundsIfNoNext s).
    { (* BEGIN parentBlocksBoundsIfNoNext s *)
      assert(Hcons0: parentBlocksBoundsIfNoNext s0) by (unfold deleteProps in *; intuition).
      intros partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlock HendBlock Hsce
        Hnext HbeqPartRoot HlookupPart. rewrite HgetPartsEqss0 in *.
      clear HlookupBTDs. unfold bentryStartAddr in *. assert(~In partition (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupPart; trivial. congruence. }
      unfold bentryEndAddr in *. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HstartBlock; trivial. }
      unfold scentryNext in *. assert(~In scentryaddr (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hnext; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HstartBlock. rewrite Hs2 in HendBlock. rewrite Hs2 in Hnext.
      rewrite Hs2 in HlookupPart. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) scentryaddr) eqn:HbeqSh1Sce; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) partition) eqn:HbeqSh1Part; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(Hblocks0: bentryStartAddr block startaddr s0 /\ bentryEndAddr block endaddr s0).
      {
        unfold bentryStartAddr. unfold bentryEndAddr. rewrite Hs1 in HstartBlock. rewrite Hs1 in HendBlock.
        simpl lookup in *. destruct (beqAddr currBlock block) eqn:HbeqBlocks.
        - rewrite <-beqAddrTrue in HbeqBlocks. subst block. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      }
      destruct Hblocks0 as (HstartBlocks0 & HendBlocks0). rewrite Hs1 in Hnext. rewrite Hs1 in HlookupPart.
      simpl lookup in *. destruct (beqAddr currBlock scentryaddr) eqn:HbeqCBSce; try(exfalso; congruence).
      destruct (beqAddr currBlock partition) eqn:HbeqCBPart; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      assert(In (parent pdentry) (getPartitions multiplexer s0)).
      {
        assert(HparentOfPart: exists wrongParts,
            (forall partition entry,
              lookup partition (memory s0) beqAddr = Some (PDT entry)
              -> (~In (parent entry) wrongParts
                  -> partition <> constantRootPartM
                  -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                      /\ In (parent entry) (getPartitions multiplexer s0))
                /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
            /\ (forall oldPart, In oldPart wrongParts
                -> (forall desc, In desc (getPartitions oldPart s0)
                    -> desc <> blockToDelete
                    -> ~In desc (getPartitions multiplexer s0))))
          by (unfold deleteProps in *; intuition).
        destruct HparentOfPart as [wrongParts (HparentOfPart & HwrongParts)].
        specialize(HparentOfPart partition pdentry HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
        assert(HbeqPartBTD: partition <> blockToDelete).
        { intro. subst partition. congruence. }
        assert(HparentNotWrong: ~In (parent pdentry) wrongParts).
        {
          intro Hcontra. assert(HpartIsDesc: In partition (getPartitions (parent pdentry) s0)).
          {
            unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. right.
            assert(HpartIsChild: isChild s0) by (unfold deleteProps in *; intuition).
            assert(Hparent: pdentryParent partition (parent pdentry) s0).
            { unfold pdentryParent. rewrite HlookupPart. reflexivity. }
            specialize(HpartIsChild partition (parent pdentry) HpartIsPart Hparent HbeqPartRoot).
            induction (getChildren (parent pdentry) s0); simpl in *; only 1: congruence. apply in_or_app.
            destruct HpartIsChild as [Heq | HpartIsChild]; auto. subst a1. left.
            replace (maxAddr+1) with (S maxAddr); try(lia). simpl. auto.
          }
          specialize(HwrongParts (parent pdentry) Hcontra partition HpartIsDesc HbeqPartBTD). congruence.
        }
        apply HparentIsPart; assumption.
      }
      rewrite HgetMappedBEqss0 in *; trivial.
      specialize(Hcons0 partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped HstartBlocks0
        HendBlocks0 Hsce Hnext HbeqPartRoot HlookupPart).
      destruct Hcons0 as [blockParent [startParent (HBPMapped & HstartParent & HendParent & HlebStarts)]].
      exists blockParent. exists startParent. split; trivial. rewrite <-HgetMappedBEqss0 in HBPMapped; trivial.
      apply IL.mappedBlockIsBE in HBPMapped. destruct HBPMapped as [bentry (HlookupBP & _)].
      unfold bentryStartAddr in *. assert(~In blockParent (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupBP; trivial. congruence. }
      unfold bentryEndAddr in *. rewrite HlookupsEq in *; trivial. rewrite Hs2 in HlookupBP. rewrite Hs2.
      simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockParent) eqn:HbeqSh1BP; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock blockParent) eqn:HbeqCBBP.
      - rewrite <-beqAddrTrue in HbeqCBBP. subst blockParent. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
      - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END parentBlocksBoundsIfNoNext *)
    }

    assert(forall partition block sh1entryaddr blockChild idchild startaddr,
        idchild <> blockToDelete
        -> In partition (getPartitions multiplexer s)
        -> In block (getMappedBlocks partition s)
        -> sh1entryAddr block sh1entryaddr s
        -> sh1entryPDchild sh1entryaddr idchild s
        -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
        -> idchild <> nullAddr
        -> bentryStartAddr block startaddr s
        -> ~ isKS startaddr s
        -> blockChild <> nullAddr
            /\ In blockChild (getMappedBlocks idchild s) /\ bentryStartAddr blockChild startaddr s).
    { (* BEGIN childLocMappedInChild s *)
      assert(Hcons0: forall partition block sh1entryaddr blockChild idchild startaddr,
          idchild <> blockToDelete
          -> In partition (getPartitions multiplexer s0)
          -> In block (getMappedBlocks partition s0)
          -> sh1entryAddr block sh1entryaddr s0
          -> sh1entryPDchild sh1entryaddr idchild s0
          -> sh1entryInChildLocationWeak sh1entryaddr blockChild s0
          -> idchild <> nullAddr
          -> bentryStartAddr block startaddr s0
          -> ~ isKS startaddr s0
          -> blockChild <> nullAddr
              /\ In blockChild (getMappedBlocks idchild s0) /\ bentryStartAddr blockChild startaddr s0)
        by (unfold deleteProps in *; intuition).
      intros part block sh1entryaddrB blockChild idchild startaddr HbeqChildBTD HpartIsPart HblockMapped Hsh1 HPDchild
        Hloc HbeqIdChildNull Hstart HstartNotKS. assert(HchildIsChild: pdchildIsPDT s) by assumption.
      specialize(HchildIsChild part block sh1entryaddrB idchild HpartIsPart HblockMapped Hsh1 HPDchild
        HbeqIdChildNull). rewrite HgetPartsEqss0 in *. rewrite HgetChildrenEqss0 in *; trivial.
      assert(HchildIsPart: In idchild (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with part; trivial; unfold deleteProps in *; intuition. }
      rewrite HgetMappedBEqss0 in *; trivial. unfold sh1entryAddr in *. unfold sh1entryInChildLocationWeak in *.
      unfold sh1entryPDchild in *. unfold bentryStartAddr in Hstart.
      clear HlookupBTDs. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hstart; trivial. }
      assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hloc; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in Hsh1. rewrite Hs2 in HPDchild. rewrite Hs2 in Hstart.
      rewrite Hs2 in Hloc. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) sh1entryaddrB) eqn:HbeqSh1s;
        try(simpl in HPDchild; exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hsh1. rewrite Hs1 in HPDchild.
      rewrite Hs1 in Hstart. rewrite Hs1 in Hloc. simpl lookup in *.
      destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
      destruct (beqAddr currBlock block) eqn:HbeqCBBlock.
      { rewrite <-beqAddrTrue in HbeqCBBlock. subst block. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. unfold isKS in *.
      assert(HpropsOr: In startaddr (getAllPaddrBlock startBlock endBlock)
        \/ ~In startaddr (getAllPaddrBlock startBlock endBlock)) by (apply Classical_Prop.classic).
      destruct HpropsOr as [HstartInR | HstartNotInR].
      - assert(HendBlocks0: exists endaddr, bentryEndAddr block endaddr s0).
        {
          unfold bentryEndAddr. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). exists (endAddr (blockrange b)). reflexivity.
        }
        destruct HendBlocks0 as [endaddr HendBlocks0].
        assert(Hwell: wellFormedBlock s0) by (unfold deleteProps in *; intuition).
        assert(HPflag: bentryPFlag block true s0).
        {
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & Hpres)].
          unfold bentryPFlag. rewrite Hlookup. auto.
        }
        specialize(Hwell block startaddr endaddr HPflag Hstart HendBlocks0). destruct Hwell as (Hwell & _).
        assert(HpartIsAnc: In part (currentPart::filterOptionPaddr (completeParentsList currentPart s0))).
        {
          rewrite <-Hranges0 in *. assert(In startaddr (getMappedPaddr part s0)).
          {
            apply IL.addrInBlockIsMapped with block; trivial. simpl. unfold bentryStartAddr in *.
            unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-Hstart. rewrite <-HendBlocks0.
            rewrite app_nil_r. apply IL.getAllPaddrBlockIncl; lia.
          }
          assert(Hbloodline: In part (filterOptionPaddr (completeParentsList currentPart s0))
            \/ part = currentPart
            \/ In currentPart (filterOptionPaddr (completeParentsList part s0))).
          {
            apply addressesBloodlinePartial with startaddr blockTDParent blockToDelete; trivial;
              try(apply IL.noDupKSMappedImpl); only 1-13: (unfold deleteProps in *; intuition).
            apply IL.addrInBlockIsMapped with currBlock; trivial.
          }
          simpl. destruct Hbloodline as [Hres | [Heq | Hcontra]]; auto. exfalso.
          assert(Hchild: exists child, pdentryParent child currentPart s0
           /\ In child (getPartitions multiplexer s0)
           /\ In child (part::filterOptionPaddr (completeParentsList part s0))).
          {
            apply completeParentsListChildPartial with blockTDParent blockToDelete; trivial;
              unfold deleteProps in *; intuition.
          }
          destruct Hchild as [child (Hparent & HchildBIsPart & HchildIsAnc)].
          destruct (beqAddr child blockToDelete) eqn:HbeqChildren.
          - rewrite <-beqAddrTrue in HbeqChildren. subst child. unfold pdentryParent in *.
            rewrite HlookupBTDs0 in *. congruence.
          - rewrite <-beqAddrFalse in *. specialize(HpropsAddrToRemoveCopy startaddr HstartInR).
            destruct HpropsAddrToRemoveCopy as (_ & _ & HstartInNoChild & _). apply not_eq_sym in HbeqChildren.
            assert(HchildBIsChild: isChild s0) by (unfold deleteProps in *; intuition).
            assert(HbeqChildRoot: child <> constantRootPartM).
            {
              assert(HparentOfPart: exists wrongParts,
                  (forall partition entry,
                    lookup partition (memory s0) beqAddr = Some (PDT entry)
                    -> (~In (parent entry) wrongParts
                        -> partition <> constantRootPartM
                        -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                            /\ In (parent entry) (getPartitions multiplexer s0))
                      /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
                  /\ (forall oldPart, In oldPart wrongParts
                      -> (forall desc, In desc (getPartitions oldPart s0)
                          -> desc <> blockToDelete
                          -> ~In desc (getPartitions multiplexer s0))))
                by (unfold deleteProps in *; intuition). intro HbeqChildRoot.
              destruct HparentOfPart as [wrongParts (HparentOfPart & _)]. unfold pdentryParent in *.
              destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(congruence).
              destruct v; try(congruence). specialize(HparentOfPart child p HlookupChild).
              destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot HbeqChildRoot).
              rewrite HparentOfRoot in *. subst currentPart. unfold isPDT in *.
              assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
              destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
            }
            specialize(HchildBIsChild child currentPart HchildBIsPart Hparent HbeqChildRoot).
            specialize(HstartInNoChild child HchildBIsChild). contradict HstartInNoChild.
            simpl in HchildIsAnc. destruct HchildIsAnc as [Heq | HchildIsAnc]; try(subst child; assumption).
            apply addrBelongToAncestorsPartial with part blockTDParent blockToDelete; trivial;
              only 6: apply IL.blockInclImpliesAddrIncl; unfold deleteProps in *; intuition.
        }
        assert(HstartInBlock: In startaddr (getAllPaddrAux [block] s0)).
        {
          simpl. unfold bentryEndAddr in *. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
          destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-HendBlocks0. rewrite app_nil_r.
          apply IL.getAllPaddrBlockIncl; lia.
        }
        assert(HbeqPartCurr: part <> currentPart).
        {
          intro. subst part. assert(block = currBlock).
          {
            destruct (beqAddr block currBlock) eqn:HbeqBlocks; try(rewrite beqAddrTrue; assumption). exfalso.
            rewrite <-beqAddrFalse in *. rewrite <-Hranges0 in *.
            assert(HnoDupP: noDupMappedPaddrList s0) by (unfold deleteProps in *; intuition).
            pose proof (DisjointPaddrInPart currentPart block currBlock startaddr s0 HnoDupP HcurrIsPart HblockMapped
              HCBMapped HbeqBlocks HstartInBlock). congruence.
          }
          subst block. rewrite HlookupCurrBs0 in *. subst sh1entryaddrB. congruence.
        }
        simpl in HpartIsAnc. destruct HpartIsAnc as [Hcontra | HpartIsAnc]; try(exfalso; congruence).
        assert(Hchild: exists child, pdentryParent child part s0
         /\ In child (getPartitions multiplexer s0)
         /\ In child (currentPart::filterOptionPaddr (completeParentsList currentPart s0))).
        {
          apply completeParentsListChildPartial with blockTDParent blockToDelete; trivial;
            unfold deleteProps in *; intuition.
        }
        destruct Hchild as [child (Hparent & HchildBIsPart & HchildIsAnc)].
        assert(HbeqChildNull: blockChild <> nullAddr).
        {
          intro. subst blockChild.
          assert(Hres: forall part block child startaddr,
            child <> blockToDelete
            -> In part (getPartitions multiplexer s0)
            -> In block (getMappedBlocks part s0)
            -> sh1entryPDchild (CPaddr (block + sh1offset)) child s0
            -> child <> nullAddr
            -> sh1entryPDflag (CPaddr (block + sh1offset)) false s0
            -> sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) nullAddr s0
            -> bentryStartAddr block startaddr s0
            -> In startaddr (getConfigBlocks child s0)
                /\ (forall addr child2, In addr (getAllPaddrAux [block] s0)
                      -> In child2 (getChildren part s0)
                      -> ~In addr (getMappedPaddr child2 s0))
                /\ (forall (addr:paddr) endaddr part2, bentryEndAddr block endaddr s0
                      -> In part2 (getPartitions multiplexer s0)
                      -> startaddr+Constants.kernelStructureTotalLength <= addr
                      -> addr < endaddr
                      -> ~In addr (getConfigPaddr part2 s0))) by (unfold deleteProps in *; intuition).
          assert(HPDflag: sh1entryPDflag (CPaddr (block+sh1offset)) false s0).
          {
            assert(HnoChild: PDflagMeansNoChild s0) by (unfold deleteProps in *; intuition).
            assert(HblockIsBE: isBE block s0).
            {
              unfold isBE. destruct (lookup block (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
              trivial.
            }
            specialize(HnoChild block HblockIsBE). unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). subst sh1entryaddrB.
            destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). destruct (PDflag s3); trivial. exfalso.
            assert(HeqTriv: true = true) by reflexivity. specialize(HnoChild HeqTriv). congruence.
          }
          assert(sh1entryaddrB = CPaddr (block+sh1offset)).
          {
            destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). assumption.
          }
          subst sh1entryaddrB. assert(HchildBIsChild: isChild s0) by (unfold deleteProps in *; intuition).
          assert(HbeqChildRoot: child <> constantRootPartM).
          {
            assert(HparentOfPart: exists wrongParts,
                (forall partition entry,
                  lookup partition (memory s0) beqAddr = Some (PDT entry)
                  -> (~In (parent entry) wrongParts
                      -> partition <> constantRootPartM
                      -> (exists parentEntry, lookup (parent entry) (memory s0) beqAddr = Some (PDT parentEntry))
                          /\ In (parent entry) (getPartitions multiplexer s0))
                    /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
                /\ (forall oldPart, In oldPart wrongParts
                    -> (forall desc, In desc (getPartitions oldPart s0)
                        -> desc <> blockToDelete
                        -> ~In desc (getPartitions multiplexer s0))))
              by (unfold deleteProps in *; intuition). intro HbeqChildRoot.
            destruct HparentOfPart as [wrongParts (HparentOfPart & _)]. unfold pdentryParent in *.
            destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(congruence).
            destruct v; try(congruence). specialize(HparentOfPart child p HlookupChild).
            destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot HbeqChildRoot).
            rewrite HparentOfRoot in *. subst part. unfold getChildren in *.
            assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
            destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
            destruct v; simpl in HchildIsChild; congruence.
          }
          specialize(HchildBIsChild child part HchildBIsPart Hparent HbeqChildRoot).
          specialize(Hres part block idchild startaddr HbeqChildBTD HpartIsPart HblockMapped HPDchild HbeqIdChildNull
            HPDflag Hloc Hstart). destruct Hres as (_ & Hres & _).
          specialize(Hres startaddr child HstartInBlock HchildBIsChild). contradict Hres. rewrite <-Hranges0 in *.
          assert(HstartInCurr: In startaddr (getMappedPaddr currentPart s0)).
          { apply IL.addrInBlockIsMapped with currBlock; trivial. }
          simpl in HchildIsAnc. destruct HchildIsAnc as [Heq | HchildIsAnc]; try(subst child; assumption).
          apply addrBelongToAncestorsPartial with currentPart blockTDParent blockToDelete; trivial;
            only 6: apply IL.blockInclImpliesAddrIncl; unfold deleteProps in *; intuition.
        }
        assert(Hres: forall partition block sh1entryaddr blockChild idchild,
          idchild <> blockToDelete
          -> In partition (getPartitions multiplexer s0)
          -> In block (getMappedBlocks partition s0)
          -> sh1entryAddr block sh1entryaddr s0
          -> sh1entryPDchild sh1entryaddr idchild s0
          -> sh1entryInChildLocationWeak sh1entryaddr blockChild s0
          -> idchild <> nullAddr
          -> blockChild <> nullAddr
          -> (forall startaddr, bentryStartAddr block startaddr s0 -> bentryStartAddr blockChild startaddr s0)
                /\ In blockChild (getMappedBlocks idchild s0)) by (unfold deleteProps in *; intuition).
        specialize(Hres part block sh1entryaddrB blockChild idchild HbeqChildBTD HpartIsPart HblockMapped Hsh1
          HPDchild Hloc HbeqIdChildNull HbeqChildNull). split; trivial. destruct Hres as (HstartsEq & HBCMapped).
        split; trivial. specialize(HstartsEq startaddr Hstart). rewrite <-HgetMappedBEqss0 in HBCMapped; trivial.
        apply IL.mappedBlockIsBE in HBCMapped. destruct HBCMapped as [bentry (HlookupBC & _)].
        clear HstartNotKS. assert(~In blockChild (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HlookupBC; trivial. congruence. }
        unfold bentryStartAddr in *. rewrite HlookupsEq in *; trivial. rewrite Hs2. rewrite Hs2 in HlookupBC.
        simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock+sh1offset)) blockChild) eqn:HbeqSh1BC; try(congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock blockChild) eqn:HbeqBlocks.
        + rewrite <-beqAddrTrue in HbeqBlocks. subst blockChild. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      - rewrite HlookupsEq in *; trivial. assert(HstartNotKSs0: ~isKS startaddr s0).
        {
          unfold isKS. contradict HstartNotKS. rewrite Hs2. simpl.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) startaddr) eqn:HbeqSh1Start.
          {
            rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Start. rewrite HbeqSh1Start in *.
            destruct (lookup startaddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
          destruct (beqAddr currBlock startaddr) eqn:HbeqCBStart.
          - rewrite <-beqAddrTrue in HbeqCBStart. subst startaddr. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        specialize(Hcons0 part block sh1entryaddrB blockChild idchild startaddr HbeqChildBTD HpartIsPart HblockMapped
          Hsh1 HPDchild Hloc HbeqIdChildNull Hstart HstartNotKSs0). unfold bentryStartAddr in *.
        destruct Hcons0 as (HbeqBCNull & HBCMapped & HstartBC). split; trivial. split; trivial.
        rewrite <-HgetMappedBEqss0 in HBCMapped; trivial. apply IL.mappedBlockIsBE in HBCMapped.
        destruct HBCMapped as [bentry (HlookupBC & _)]. assert(~In blockChild (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HlookupBC; trivial. congruence. }
        rewrite HlookupsEq in *; trivial. rewrite Hs2 in HlookupBC. rewrite Hs2. simpl lookup in *.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockChild) eqn:HbeqSh1BC; try(congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
        destruct (beqAddr currBlock blockChild) eqn:HbeqBlocks.
        + rewrite <-beqAddrTrue in HbeqBlocks. subst blockChild. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END childLocMappedInChild *)
    }

    assert(forall partition block sh1entryaddr blockChild idchild,
        idchild <> blockToDelete
        -> In partition (getPartitions multiplexer s)
        -> In block (getMappedBlocks partition s)
        -> sh1entryAddr block sh1entryaddr s
        -> sh1entryPDchild sh1entryaddr idchild s
        -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
        -> idchild <> nullAddr
        -> blockChild <> nullAddr
        -> (forall startaddr, bentryStartAddr block startaddr s -> bentryStartAddr blockChild startaddr s)
              /\ In blockChild (getMappedBlocks idchild s)).
    { (* BEGIN childLocHasSameStart s *)
      assert(Hcons0: forall partition block sh1entryaddr blockChild idchild,
        idchild <> blockToDelete
        -> In partition (getPartitions multiplexer s0)
        -> In block (getMappedBlocks partition s0)
        -> sh1entryAddr block sh1entryaddr s0
        -> sh1entryPDchild sh1entryaddr idchild s0
        -> sh1entryInChildLocationWeak sh1entryaddr blockChild s0
        -> idchild <> nullAddr
        -> blockChild <> nullAddr
        -> (forall startaddr, bentryStartAddr block startaddr s0 -> bentryStartAddr blockChild startaddr s0)
              /\ In blockChild (getMappedBlocks idchild s0)) by (unfold deleteProps in *; intuition).
      intros part block sh1entryaddrB blockChild idchild HbeqIdChildBTD HpartIsPart HblockMapped Hsh1 HPDchild Hloc
        HbeqIdChildNull HbeqBCNull. assert(HchildIsChild: pdchildIsPDT s) by assumption.
      specialize(HchildIsChild part block sh1entryaddrB idchild HpartIsPart HblockMapped Hsh1 HPDchild
        HbeqIdChildNull). rewrite HgetPartsEqss0 in *. rewrite HgetChildrenEqss0 in *; trivial.
      assert(HchildIsPart: In idchild (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with part; trivial; unfold deleteProps in *; intuition. }
      rewrite HgetMappedBEqss0 in *; trivial. unfold sh1entryAddr in *. unfold sh1entryInChildLocationWeak in *.
      unfold sh1entryPDchild in *. unfold bentryStartAddr.
      clear HlookupBTDs. assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hsh1; trivial. }
      assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hloc; trivial. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in Hsh1. rewrite Hs2 in HPDchild. rewrite Hs2.
      rewrite Hs2 in Hloc. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) sh1entryaddrB) eqn:HbeqSh1s;
        try(simpl in HPDchild; exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in Hsh1. rewrite Hs1 in HPDchild.
      rewrite Hs1. rewrite Hs1 in Hloc. simpl lookup in *.
      destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
      destruct (beqAddr currBlock block) eqn:HbeqCBBlock.
      { rewrite <-beqAddrTrue in HbeqCBBlock. subst block. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(Hcons0 part block sh1entryaddrB blockChild idchild HbeqIdChildBTD HpartIsPart HblockMapped Hsh1
        HPDchild Hloc HbeqIdChildNull HbeqBCNull). destruct Hcons0 as (HstartsEq & HBCMapped). split; trivial.
      intros startaddr Hstart. specialize(HstartsEq startaddr Hstart). unfold bentryStartAddr in *.
      rewrite <-HgetMappedBEqss0 in HBCMapped; trivial. apply IL.mappedBlockIsBE in HBCMapped.
      destruct HBCMapped as [bentry (HlookupBC & _)]. assert(~In blockChild (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HlookupBC; trivial. congruence. }
      rewrite HlookupsEq in *; trivial. rewrite Hs2 in HlookupBC. rewrite Hs2. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockChild) eqn:HbeqSh1BC; try(congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock blockChild) eqn:HbeqBlocks.
      + rewrite <-beqAddrTrue in HbeqBlocks. subst blockChild. rewrite HlookupCurrBs0 in *. rewrite HnewB. auto.
      + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      (* END childLocHasSameStart *)
    }

    assert(verticalSharing s).
    { (* BEGIN verticalSharing s *)
      assert(Hcons0: verticalSharing s0) by (unfold deleteProps in *; intuition).
      intros pdparent child HparentIsPart HchildIsChild. unfold getUsedPaddr. rewrite HgetPartsEqss0 in *.
      rewrite HgetChildrenEqss0 in *; trivial. assert(HchildIsPart: In child (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition. }
      specialize(Hcons0 pdparent child HparentIsPart HchildIsChild).
      rewrite HgetMappedPEqss0; trivial. rewrite HgetMappedPEqss0; trivial. rewrite HgetConfigEqss0; trivial.
      (* END verticalSharing *)
    }

    assert(partitionsIsolation s).
    { (* BEGIN partitionsIsolation s *)
      assert(Hcons0: partitionsIsolation s0) by (unfold deleteProps in *; intuition).
      intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren. unfold getUsedPaddr.
      rewrite HgetPartsEqss0 in *. rewrite HgetChildrenEqss0 in *; trivial.
      assert(Hchild1IsPart: In child1 (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition. }
      assert(Hchild2IsPart: In child2 (getPartitions multiplexer s0)).
      { apply IL.childrenPartitionInPartitionList with pdparent; trivial; unfold deleteProps in *; intuition. }
      specialize(Hcons0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
      rewrite HgetMappedPEqss0; trivial. rewrite HgetMappedPEqss0; trivial. rewrite HgetConfigEqss0; trivial.
      rewrite HgetConfigEqss0; trivial.
      (* END partitionsIsolation *)
    }

    assert(kernelDataIsolation s).
    { (* BEGIN kernelDataIsolation s *)
      assert(Hcons0: kernelDataIsolation s0) by (unfold deleteProps in *; intuition).
      intros part1 part2 Hpart1IsPart Hpart2IsPart. rewrite HgetPartsEqss0 in *. rewrite HgetConfigEqss0; trivial.
      specialize(Hcons0 part1 part2 Hpart1IsPart Hpart2IsPart). intros addr HaddrAccPart1.
      assert(HpropsOr: In addr (getAccessibleMappedPaddr part1 s0) \/ In addr (getAllPaddrBlock startBlock endBlock)).
      {
        destruct (beqAddr currentPart part1) eqn:HbeqParts.
        - rewrite <-beqAddrTrue in HbeqParts. subst part1. destruct (accessible bentry0).
          + assert(HeqTriv: true = true) by reflexivity. rewrite HgetAccMappedPEqCurrss0 in *; auto.
          + assert(HeqTriv: false = false) by reflexivity. specialize(HgetAccMappedPImplCurrss0 HeqTriv).
            apply HgetAccMappedPImplCurrss0 in HaddrAccPart1. apply in_app_or in HaddrAccPart1.
            destruct HaddrAccPart1; auto.
        - rewrite <-beqAddrFalse in *. rewrite <-HgetAccMappedPEqss0NotCurr; auto.
      }
      destruct HpropsOr as [HaddrAccPart1s0 | HaddrInR].
      - apply Hcons0; assumption.
      - specialize(HpropsAddrToRemoveCopy addr HaddrInR). destruct HpropsAddrToRemoveCopy as (_ & Hres & _).
        apply Hres; assumption.
      (* END kernelDataIsolation *)
    }

    assert(HpropsAddrToRemoves: forall block startBlock endBlock, In block (getMappedBlocks currentPart s)
      -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s
      -> bentryStartAddr block startBlock s
      -> bentryEndAddr block endBlock s
      -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
          -> ~In addr (getPartitions multiplexer s)
              /\ (forall part, In part (getPartitions multiplexer s)
                  -> ~In addr (filterOptionPaddr (getKSEntries part s))
                      /\ ~In addr (getConfigPaddr part s))
              /\ (forall child, In child (getChildren currentPart s)
                  -> ~ In addr (getMappedPaddr child s))
              /\ (isBE addr s -> addr + scoffset < endBlock)
              /\ (isKS addr s -> addr + nextoffset < endBlock)
              /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB + sh1offset)
                  -> In blockB (getAllPaddrBlock startBlock endBlock))
              /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB + scoffset)
                  -> In blockB (getAllPaddrBlock startBlock endBlock))
              /\ addr <> nullAddr)).
    {
      intros block startaddr endaddr HblockMapped HPDchild Hstart Hend addr HaddrInRange. rewrite HgetPartsEqss0.
      rewrite HgetMappedBEqss0 in *; trivial. rewrite HgetChildrenEqss0; trivial. unfold sh1entryPDchild in *.
      unfold bentryStartAddr in *. unfold bentryEndAddr in *.
      assert(~In block (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hstart; trivial. }
      assert(~In (CPaddr (block + sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDchild; trivial. }
      clear HlookupBTDs. rewrite HlookupsEq in *; trivial. rewrite Hs2 in HPDchild. rewrite Hs2 in Hstart.
      rewrite Hs2 in Hend. simpl lookup in *.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) (CPaddr (block+sh1offset))) eqn:HbeqSh1s;
        try(simpl in HPDchild; congruence).
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) block) eqn:HbeqSh1Block; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchild. rewrite Hs1 in Hend.
      rewrite Hs1 in Hstart. simpl lookup in *.
      destruct (beqAddr currBlock (CPaddr (block+sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
      destruct (beqAddr currBlock block) eqn:HbeqBlocks.
      { rewrite <-beqAddrTrue in HbeqBlocks. subst block. congruence. }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      specialize(HpropsAddrToRemove block startaddr endaddr HblockMapped HPDchild Hstart Hend addr HaddrInRange).
      destruct HpropsAddrToRemove as (HaddrNotPart & HaddrNotConfig & HaddrInNoChild & HsceInSameBRev &
        HnextInSameBRev & Hsh1InSameB & HsceInSameB & HbeqAddrNull).
      split; try(split; only 2: (split; try(split; try(split; try(split; try(split)))))); trivial.
      - intros part HpartIsPart. specialize(HaddrNotConfig part HpartIsPart). rewrite HgetKSEqss0; trivial.
        rewrite HgetConfigEqss0; assumption.
      - intros child HchildIsChild. specialize(HaddrInNoChild child HchildIsChild). rewrite HgetMappedPEqss0; trivial.
        apply IL.childrenPartitionInPartitionList with currentPart; trivial; unfold deleteProps in *; intuition.
      - intro HaddrIsBE. apply HsceInSameBRev. unfold isBE in *.
        assert(~In addr (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HaddrIsBE; trivial. }
        rewrite HlookupsEq in HaddrIsBE; trivial. rewrite Hs2 in HaddrIsBE. simpl in HaddrIsBE.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrIsBE.
        simpl in HaddrIsBE. destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
        + rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. rewrite HlookupCurrBs0. trivial.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      - intro HaddrIsKS. apply HnextInSameBRev. unfold isKS in *.
        assert(~In addr (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HaddrIsKS; trivial. }
        rewrite HlookupsEq in HaddrIsKS; trivial. rewrite Hs2 in HaddrIsKS. simpl in HaddrIsKS.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrIsKS.
        simpl in HaddrIsKS. destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
        + rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. rewrite HlookupCurrBs0. rewrite HnewB in *. auto.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      - intros blockB HblockBIsBE. apply Hsh1InSameB. unfold isBE in *.
        assert(~In blockB (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HblockBIsBE; trivial. }
        rewrite HlookupsEq in HblockBIsBE; trivial. rewrite Hs2 in HblockBIsBE. simpl in HblockBIsBE.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockB) eqn:HbeqSh1BlockB; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HblockBIsBE.
        simpl in HblockBIsBE. destruct (beqAddr currBlock blockB) eqn:HbeqCBBlockB.
        + rewrite <-beqAddrTrue in HbeqCBBlockB. subst blockB. rewrite HlookupCurrBs0. trivial.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      - intros blockB HblockBIsBE. apply HsceInSameB. unfold isBE in *.
        assert(~In blockB (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HblockBIsBE; trivial. }
        rewrite HlookupsEq in HblockBIsBE; trivial. rewrite Hs2 in HblockBIsBE. simpl in HblockBIsBE.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockB) eqn:HbeqSh1BlockB; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HblockBIsBE.
        simpl in HblockBIsBE. destruct (beqAddr currBlock blockB) eqn:HbeqCBBlockB.
        + rewrite <-beqAddrTrue in HbeqCBBlockB. subst blockB. rewrite HlookupCurrBs0. trivial.
        + rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
    }

    assert(HlookupCBEqss1: lookup currBlock (memory s) beqAddr = lookup currBlock (memory s1) beqAddr).
    {
      rewrite <-HlookupCBEqs2s1. rewrite <-HgetMappedBEqss0 in HCBMapped; trivial.
      apply IL.mappedBlockIsBE in HCBMapped. destruct HCBMapped as [bentry (Hlookup & _)].
      assert(~In currBlock (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in Hlookup; trivial. congruence. }
      apply HlookupsEq; assumption.
    }

    assert(Hcons: deleteProps sInit s currentPart blockTDParent blockToDelete).
    { unfold deleteProps. intuition. }
    assert(forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s
      -> sh1entryPDchild sh1entryaddr child sInit).
    {
      intros sh1entryaddrB child HbeqChildNull HPDchild. apply HPDchildImpls0; trivial. unfold sh1entryPDchild in *.
      assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDchild; trivial. }
      rewrite HlookupsEq in HPDchild; trivial. rewrite Hs2 in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) sh1entryaddrB) eqn:HbeqSh1s;
        try(simpl in HPDchild; exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchild.
      simpl in HPDchild. destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
    }
    assert(~In kernel (getAllPaddrBlock startBlock endBlock)).
    {
      intro Hcontra. specialize(HpropsAddrToRemoveCopy kernel Hcontra).
      destruct HpropsAddrToRemoveCopy as (_ & HkernNotConfig & _). specialize(HkernNotConfig currentPart HcurrIsPart).
      destruct HkernNotConfig as (HkernNotInKS & _).
      assert(HltZeroStructNb: 0 < kernelStructureEntriesNb) by (cbn; lia).
      specialize(HblocksInCurr 0 HltZeroStructNb). rewrite PeanoNat.Nat.add_0_r in *.
      rewrite paddrEqId in HblocksInCurr. congruence.
    }
    assert(~In currBlock (getAllPaddrBlock startBlock endBlock)).
    {
      intro Hcontra. specialize(HpropsAddrToRemoveCopy currBlock Hcontra).
      destruct HpropsAddrToRemoveCopy as (_ & HCBNotConfig & _). specialize(HCBNotConfig currentPart HcurrIsPart).
      destruct HCBNotConfig as (HCBNotInKS & _). congruence.
    }
    assert(lookup blockToDelete (memory s) beqAddr = None).
    {
      assert(~In blockToDelete (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy blockToDelete Hcontra).
        destruct HpropsAddrToRemoveCopy as (HBTDNotPart & _). congruence.
      }
      rewrite HlookupsEq; trivial.
    }
    assert(~In blockTDParent (getAllPaddrBlock startBlock endBlock)).
    {
      intro Hcontra. specialize(HpropsAddrToRemoveCopy blockTDParent Hcontra).
      destruct HpropsAddrToRemoveCopy as (_ & HBPNotInKS & _). specialize(HBPNotInKS currentPart HcurrIsPart).
      destruct HBPNotInKS as (HBPNotInKS & _). unfold getMappedBlocks in *.
      apply InFilterPresentInList in HBTDPMappedCurrs0. congruence.
    }
    assert(~In (CPaddr (blockTDParent+sh1offset)) (getAllPaddrBlock startBlock endBlock)).
    {
      intro Hcontra. specialize(HpropsAddrToRemoveCopy (CPaddr (blockTDParent+sh1offset)) Hcontra).
      destruct HpropsAddrToRemoveCopy as (_ & _ & _ & _ & _ & Hprops & _).
      assert(HBTDPIsBE: isBE blockTDParent s0).
      {
        apply IL.mappedBlockIsBE in HBTDPMappedCurrs0. destruct HBTDPMappedCurrs0 as [bentry (Hlookup & _)].
        unfold isBE. rewrite Hlookup. trivial.
      }
      assert(HeqTriv: CPaddr (blockTDParent+sh1offset) = CPaddr (blockTDParent+sh1offset)) by reflexivity.
      specialize(Hprops blockTDParent HBTDPIsBE HeqTriv). congruence.
    }
    assert(sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s).
    {
      unfold sh1entryPDflag in *. rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (blockTDParent + sh1offset))) eqn:HbeqSh1s.
      {
        rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. exfalso. subst blockTDParent.
        assert(Hres: PDflagMeansNoChild s0) by (unfold deleteProps in *; intuition).
        specialize(Hres currBlock HCBIsBEs0 HPDflagBTDPs0). unfold sh1entryPDchild in *.
        destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      destruct (beqAddr currBlock (CPaddr (blockTDParent + sh1offset))) eqn:HbeqCBSh1.
      {
        rewrite <-beqAddrTrue in HbeqCBSh1. rewrite <-HbeqCBSh1 in *. rewrite HlookupCurrBs0 in *. congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(bentryStartAddr blockTDParent blockToDelete s).
    {
      unfold bentryStartAddr in *. rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) blockTDParent) eqn:HbeqSh1BP.
      {
        rewrite <-beqAddrTrue in HbeqSh1BP. rewrite HbeqSh1BP in *.
        destruct (lookup blockTDParent (memory s1) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }

    rewrite <-HgetMappedBEqss0 in HBTDPMappedCurrs0; trivial. rewrite <-HgetPartsEqss0 in *.
    rewrite <-HgetKSEqss0 in HblocksInCurr; trivial. assert(isPDT currentPart s).
    {
      unfold getMappedBlocks in *. unfold getKSEntries in *. unfold isPDT.
      destruct (lookup currentPart (memory s) beqAddr); try(simpl in HBTDPMappedCurrs0; congruence).
      destruct v; try(simpl in HBTDPMappedCurrs0; congruence). trivial.
    }
    assert(forall part, In part (getPartitions multiplexer s) -> In blockToDelete (getChildren part s)
      -> part = currentPart).
    {
      intros part HpartIsPart HBTDIsChild. apply HBTDIsUniqueChild; trivial. rewrite <-HgetChildrenEqss0; assumption.
    }
    assert(~In (CPaddr (currBlock+sh1offset)) (getAllPaddrBlock startBlock endBlock)).
    {
      intro Hcontra. specialize(HpropsAddrToRemoveCopy (CPaddr (currBlock+sh1offset)) Hcontra).
      destruct HpropsAddrToRemoveCopy as (_ & _ & _ & _ & _ & Hsh1InSameBlock & _).
      assert(Htriv: CPaddr (currBlock+sh1offset) = CPaddr (currBlock+sh1offset)) by reflexivity.
      specialize(Hsh1InSameBlock currBlock HCBIsBEs0 Htriv). congruence.
    }
    assert(HPDchildCB: sh1entryPDchild (CPaddr (currBlock+sh1offset)) nullAddr s).
    {
      unfold sh1entryPDchild. rewrite HlookupsEq; trivial. rewrite Hs2. simpl. rewrite IL.beqAddrTrue. reflexivity.
    }
    assert(HBTDNotChilds: forall idx, idx >= currIdx -> idx < kernelStructureEntriesNb
      -> ~sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete s).
    {
      intros idx HgtIdxCurrM HltIdxStructNb. destruct (Nat.eqb idx currIdx) eqn:HeqIdxCurr.
      - apply PeanoNat.Nat.eqb_eq in HeqIdxCurr. subst idx. rewrite <-HcurrBlock. intro Hcontra.
        unfold sh1entryPDchild in *.
        destruct (lookup (CPaddr (currBlock+sh1offset)) (memory s) beqAddr); try(congruence). destruct v; congruence.
      - apply PeanoNat.Nat.eqb_neq in HeqIdxCurr. assert(HgtIdxCurr: idx > currIdx) by lia.
        specialize(HBTDNotChilds0 idx HgtIdxCurr HltIdxStructNb). unfold sh1entryPDchild in *.
        set(sh1entryaddrB := CPaddr (CPaddr (kernel + idx) + sh1offset)). fold sh1entryaddrB in HBTDNotChilds0.
        contradict HBTDNotChilds0. assert(~In sh1entryaddrB (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HBTDNotChilds0; trivial. }
        rewrite HlookupsEq in HBTDNotChilds0; trivial. rewrite Hs2 in HBTDNotChilds0. simpl in HBTDNotChilds0.
        destruct (beqAddr (CPaddr (currBlock+sh1offset)) sh1entryaddrB) eqn:HbeqSh1s;
          try(simpl in HBTDNotChilds0; exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HBTDNotChilds0.
        simpl in HBTDNotChilds0. destruct (beqAddr currBlock sh1entryaddrB) eqn:HbeqCBSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
    }
    assert(forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
      -> In block (getMappedBlocks part s) -> sh1entryPDchild (CPaddr (block + sh1offset)) child s
      -> child <> blockToDelete).
    {
      intros part block child HbeqParts HpartIsPart HblockMapped HPDchild. rewrite HgetMappedBEqss0 in *; trivial.
      apply HBDTNotElses0 with part block; trivial. unfold sh1entryPDchild in *.
      assert(~In (CPaddr (block + sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      { intro. rewrite HremovedAddrs in HPDchild; trivial. }
      rewrite HlookupsEq in HPDchild; trivial. rewrite Hs2 in HPDchild. simpl in HPDchild.
      destruct (beqAddr (CPaddr (currBlock+sh1offset)) (CPaddr (block + sh1offset))) eqn:HbeqSh1s.
      {
        rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. subst block. exfalso.
        assert(Hdisjoint: DisjointKSEntries s0) by (unfold deleteProps in *; intuition). rewrite HgetPartsEqss0 in *.
        specialize(Hdisjoint part currentPart HpartIsPart HcurrIsPart HbeqParts).
        destruct Hdisjoint as [list1 [list2 (Hlist1 & Hlist2 & Hdisjoint)]]. subst list1. subst list2.
        unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMapped.
        specialize(Hdisjoint currBlock HblockMapped). congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1 in HPDchild. simpl in HPDchild.
      destruct (beqAddr currBlock (CPaddr (block + sh1offset))) eqn:HbeqCBSh1; try(exfalso; congruence).
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
    }
    assert(forall idx addr, idx >= currIdx -> idx < kernelStructureEntriesNb
      -> sh1entryPDchild (CPaddr (CPaddr (kernel + idx) + sh1offset)) blockToDelete sInit
      -> In addr (getAllPaddrAux [CPaddr (kernel + idx)] s) -> lookup addr (memory s) beqAddr = None).
    {
      intros idx addr HgtIdxCurrM HltIdxStructNb HPDchild HaddrInBlock. destruct (Nat.eqb idx currIdx) eqn:HeqIdxCurr.
      - apply PeanoNat.Nat.eqb_eq in HeqIdxCurr. subst idx. rewrite <-HcurrBlock in *. simpl in HaddrInBlock.
        rewrite HlookupCBEqss1 in *. simpl in Hranges1. rewrite Hranges1 in HaddrInBlock.
        apply HremovedAddrs; assumption.
      - apply PeanoNat.Nat.eqb_neq in HeqIdxCurr. assert(HgtIdxCurr: idx > currIdx) by lia. simpl in HaddrInBlock.
        assert(~In (CPaddr (kernel + idx)) (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in HaddrInBlock; trivial. }
        assert(HaddrInBlocks0: In addr (getAllPaddrAux [CPaddr (kernel + idx)] s0)).
        {
          rewrite HlookupsEq in HaddrInBlock; trivial. simpl. rewrite Hs2 in HaddrInBlock. simpl in HaddrInBlock.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (kernel + idx))) eqn:HbeqSh1Block;
            try(simpl in HaddrInBlock; exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrInBlock. simpl in HaddrInBlock.
          destruct (beqAddr currBlock (CPaddr (kernel + idx))) eqn:HbeqBlocks.
          - rewrite <-beqAddrTrue in HbeqBlocks. rewrite HbeqBlocks in *. rewrite HlookupCurrBs0. rewrite HnewB in *.
            auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        specialize(HnewEmptyAddrs idx addr HgtIdxCurr HltIdxStructNb HPDchild HaddrInBlocks0).
        assert(HpropsOr: In addr (getAllPaddrBlock startBlock endBlock)
          \/ ~In addr (getAllPaddrBlock startBlock endBlock)) by (apply Classical_Prop.classic).
        destruct HpropsOr.
        + apply HremovedAddrs; assumption.
        + rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr.
          {
            rewrite HlookupSh1Eqs1s0 in *. rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr.
            rewrite HnewEmptyAddrs in *. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
          destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
          { rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. exfalso; congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(forall idx, idx < currIdx
      -> lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory s) beqAddr
          = lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory sInit) beqAddr).
    {
      intros idx HltIdxCurr. assert(HgebIdxCurr: idx <= currIdx) by lia. specialize(HremainingLookup idx HgebIdxCurr).
      rewrite <-HremainingLookup. assert(HltIdxStructNb: idx < kernelStructureEntriesNb) by lia.
      specialize(HblocksInCurr idx HltIdxStructNb).
      assert(~In (CPaddr (kernel+idx)) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy (CPaddr (kernel+idx)) Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & Hprop & _). specialize(Hprop currentPart HcurrIsPart).
        destruct Hprop as (Hprop & _). rewrite HgetKSEqss0 in *; trivial. congruence.
      }
      assert(HblockIsBE: isBE (CPaddr (kernel+idx)) s0).
      { rewrite HgetKSEqss0 in *; trivial. apply KSentriesAreBE with currentPart; trivial. }
      assert(~In (CPaddr (CPaddr (kernel+idx)+sh1offset)) (getAllPaddrBlock startBlock endBlock)).
      {
        intro Hcontra. specialize(HpropsAddrToRemoveCopy (CPaddr (CPaddr (kernel+idx)+sh1offset)) Hcontra).
        destruct HpropsAddrToRemoveCopy as (_ & _ & _ & _ & _ & Hsh1InSameBlock & _).
        assert(Htriv: CPaddr (CPaddr (kernel+idx)+sh1offset) = CPaddr (CPaddr (kernel+idx)+sh1offset))
          by reflexivity.
        specialize(Hsh1InSameBlock (CPaddr (kernel+idx)) HblockIsBE Htriv). congruence.
      }
      rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
      destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (CPaddr (kernel + idx) + sh1offset))) eqn:HbeqSh1s.
      {
        exfalso. rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial. rewrite HcurrBlock in *.
        assert(idx = currIdx).
        {
          unfold nullAddr in HbeqCBNull. unfold CPaddr in *. simpl in *.
          destruct (Compare_dec.le_dec (kernel + currIdx) maxAddr).
          - destruct (Compare_dec.le_dec (kernel + idx) maxAddr).
            + injection HbeqSh1s as HbeqSh1s. rewrite PeanoNat.Nat.add_comm in HbeqSh1s. apply eq_sym in HbeqSh1s.
              rewrite PeanoNat.Nat.add_comm in HbeqSh1s. apply eq_sym in HbeqSh1s.
              apply PeanoNat.Nat.add_cancel_r in HbeqSh1s. auto.
            + contradict HbeqCBNull. rewrite HbeqSh1s. f_equal. apply proof_irrelevance.
          - contradict HbeqCBNull. f_equal. apply proof_irrelevance.
        }
        subst idx. lia.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
      assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0) by (unfold deleteProps in *; intuition).
      specialize(Hsh1IsSHE (CPaddr (kernel + idx)) HblockIsBE).
      destruct (beqAddr currBlock (CPaddr (CPaddr (kernel + idx) + sh1offset))) eqn:HbeqCBSh1.
      {
        rewrite <-beqAddrTrue in HbeqCBSh1. rewrite <-HbeqCBSh1 in *. unfold isSHE in *. rewrite HlookupCurrBs0 in *.
        exfalso; congruence.
      }
      rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }
    assert(~In currentPart (getAllPaddrBlock startBlock endBlock)).
    {
      intro Hcontra. specialize(HpropsAddrToRemoveCopy currentPart Hcontra). destruct HpropsAddrToRemoveCopy.
      congruence.
    }
    assert(HstructIsKS: isKS (structure pdentryCurr) s0).
    {
      unfold completeListOfKernels in *. unfold isKS.
      destruct (lookup (structure pdentryCurr) (memory s0) beqAddr); try(simpl in HkernCIsConfigs0; congruence).
      destruct v; try(simpl in HkernCIsConfigs0; congruence).
      destruct (indexEq (blockindex b) (CIndex 0)) eqn:HbeqIdxZero;
        try(simpl in HkernCIsConfigs0; exfalso; congruence). apply beqIdxTrue in HbeqIdxZero. assumption.
    }
    assert(HstructIsConfig: In (structure pdentryCurr) (completeListOfKernels (structure pdentryCurr) s0)).
    {
      unfold completeListOfKernels. unfold isKS in *.
      destruct (lookup (structure pdentryCurr) (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite HstructIsKS. rewrite IL.indexEqRefl. cbn -[maxNbPrepare]. auto.
    }
    assert(HbeqStructCNull: structure pdentryCurr <> nullAddr).
    {
      intro Hcontra. rewrite Hcontra in *. assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition).
      unfold isKS in *. unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    assert(exists kernList, isListOfKernels kernList currentPart s
      /\ ((kernList = [] /\ kernel = structure pdentryCurr)
          \/ (kernList <> []
              /\ nextKSentry (CPaddr (last kernList (structure pdentryCurr)+nextoffset)) kernel s))
      /\ m > maxNbPrepare - length kernList
      /\ (forall kernBis idx, In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
            -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s)
      /\ (forall kernBis idx addr,
            In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
            -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete sInit
            -> In addr (getAllPaddrAux [CPaddr (kernBis + idx)] s)
            -> lookup addr (memory s) beqAddr = None)
      /\ (forall kernBis idx, In kernBis (completeListOfKernels kernel s)
            -> kernBis <> kernel -> idx <= kernelStructureEntriesNb - 1
            -> lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s) beqAddr
                = lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory sInit) beqAddr)).
    {
      destruct HkernList as [kernList (HkernList & HstructOrNext & HgtMRest & HBTDNotChildAnc & HremovedAddrsAnc &
        Hsh1sLookupsEq)].
      exists kernList. assert(HkernLists: isListOfKernels kernList currentPart s).
      {
        assert(HkernLists2: isListOfKernels kernList currentPart s2).
        {
          rewrite Hs2. apply IL.isListOfKernelsEqSHERev; trivial. rewrite Hs1.
          apply IL.isListOfKernelsEqBERev; assumption.
        }
        unfold isListOfKernels in *. destruct kernList as [| kern kernList]; trivial.
        destruct HkernLists2 as [pdentry (HlookupPart & HbeqStructNull & Hstruct & HkernLists)].
        rewrite HlookupsEq; trivial. exists pdentry. split; trivial. split; trivial. split; trivial.
        assert(HblocksNotRemoved: forall block, In block (kern::kernList)
          -> ~In block (getAllPaddrBlock startBlock endBlock)).
        {
          intros block HblockIn Hcontra. rewrite <-HgetPartsEqs2s0 in *.
          assert(In block (completeListOfKernels (structure pdentryCurr) s2)).
          {
            subst kern. rewrite HlookupCurrs2 in *. injection HlookupPart as Heq. subst pdentry.
            apply kernListInclComplete with ((structure pdentryCurr)::kernList) currentPart; trivial.
            simpl. exists pdentryCurr. auto.
          }
          assert(In block (getConfigBlocks currentPart s2)).
          {
            rewrite completeKernListIsConfig with (pdentry:=pdentryCurr); trivial.
          }
          specialize(HpropsForStructEqs2 block Hcontra). destruct HpropsForStructEqs2 as (_ & Hprop & _).
          specialize(Hprop currentPart HcurrIsPart). unfold getConfigPaddr in *. apply Lib.in_app_or_neg in Hprop.
          destruct Hprop as (_ & Hprop). contradict Hprop. apply addrInKernIsConfig with block; trivial.
          - apply configBlocksAreBE with currentPart; assumption.
          - rewrite kernelStructureTotalLengthVal. apply IL.getAllPaddrBlockAuxIncl; lia.
        }
        assert(HblocksAreKS: forall block, In block (kern::kernList) -> isKS block s0).
        {
          intros block HblockIn. rewrite HgetPartsEqss0 in *.
          assert(In block (completeListOfKernels (structure pdentryCurr) s0)).
          {
            subst kern. rewrite HlookupCurrs2 in *. injection HlookupPart as Heq. subst pdentry.
            apply kernListInclComplete with ((structure pdentryCurr)::kernList) currentPart; trivial;
              unfold deleteProps in *; intuition.
          }
          assert(In block (getConfigBlocks currentPart s0)).
          {
            rewrite completeKernListIsConfig with (pdentry:=pdentryCurr); trivial; unfold deleteProps in *; intuition.
          }
          apply configBlocksAreKS with currentPart; trivial; unfold deleteProps in *; intuition.
        }
        clear Hstruct HgtMRest HBTDNotChildAnc HkernList HstructOrNext HremovedAddrsAnc.
        revert kern HkernLists HblocksNotRemoved HblocksAreKS. induction kernList; simpl; intros; trivial.
        destruct HkernLists as (HlookupNext & HlebNextMax & HbeqA1Null & HkernLists).
        assert(forall block, In block (a1::kernList) -> ~ In block (getAllPaddrBlock startBlock endBlock)).
        { simpl. intros. apply HblocksNotRemoved; auto. }
        assert(forall block, In block (a1::kernList) -> isKS block s0).
        { simpl. intros. apply HblocksAreKS; auto. }
        assert(Htriv: kern = kern \/ a1 = kern \/ In kern kernList) by auto. specialize(HblocksNotRemoved kern Htriv).
        specialize(HblocksAreKS kern Htriv). rewrite HgetPartsEqss0 in *.
        rewrite HlookupsEq; auto. intro Hcontra. rewrite <-Hranges0 in *.
        assert(HnextInSameB: blockAndNextInSameBlock s0) by (unfold deleteProps in *; intuition).
        specialize(HnextInSameB currentPart kern currBlock HcurrIsPart HCBMapped HblocksAreKS Hcontra).
        congruence.
      }
      split; trivial. repeat (split; trivial).
      - destruct HstructOrNext as [Hleft | (HbeqListNul & Hnext)]; auto. right. split; trivial.
        assert(Hnexts2: nextKSentry (CPaddr (last kernList (structure pdentryCurr) + nextoffset)) kernel s2).
        {
          unfold nextKSentry in *. set(block := last kernList (structure pdentryCurr)). fold block in Hnext.
          rewrite Hs2. simpl.
          destruct (beqAddr (CPaddr (currBlock+sh1offset)) (CPaddr (block+nextoffset))) eqn:HbeqSh1Next.
          {
            rewrite <-beqAddrTrue in HbeqSh1Next. rewrite HbeqSh1Next in *. rewrite HlookupSh1Eqs1s0 in *.
            destruct (lookup (CPaddr (block+nextoffset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
          destruct (beqAddr currBlock (CPaddr (block+nextoffset))) eqn:HbeqCBNext.
          {
            rewrite <-beqAddrTrue in HbeqCBNext. rewrite <-HbeqCBNext in *. rewrite HlookupCurrBs0 in *. congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
        }
        unfold nextKSentry in *. rewrite HlookupsEq; trivial. intro Hcontra. rewrite <-Hranges0 in *.
        assert(HlastIsConfig: In (last kernList (structure pdentryCurr)) (getConfigBlocks currentPart s0)).
        {
          rewrite HgetPartsEqss0 in *.
          assert(In (last kernList (structure pdentryCurr)) (completeListOfKernels (structure pdentryCurr) s0)).
          {
            destruct kernList as [| kern]; try(exfalso; congruence).
            apply kernListInclComplete with (kern::kernList) currentPart; trivial.
            1,2: unfold deleteProps in *; intuition.
            apply IL.lastOfNotEmptyIsIn with (structure pdentryCurr); reflexivity.
          }
          rewrite completeKernListIsConfig with (pdentry:=pdentryCurr); trivial; unfold deleteProps in *; intuition.
        }
        rewrite HgetPartsEqss0 in *. assert(HlastIsKS: isKS (last kernList (structure pdentryCurr)) s0).
        {
          apply configBlocksAreKS with currentPart; trivial; unfold deleteProps in *; intuition.
        }
        assert(HnextInSameB: blockAndNextInSameBlock s0) by (unfold deleteProps in *; intuition).
        specialize(HnextInSameB currentPart (last kernList (structure pdentryCurr)) currBlock HcurrIsPart HCBMapped
          HlastIsKS Hcontra). specialize(HpropsAddrToRemoveCopy (last kernList (structure pdentryCurr)) HnextInSameB).
        destruct HpropsAddrToRemoveCopy as (_ & Hprop & _). specialize(Hprop currentPart HcurrIsPart).
        destruct Hprop as (Hprop & _). contradict Hprop.
        apply configBlocksAreEntries; trivial; unfold deleteProps in *; intuition.
      - intros kern idx HkernIn HbeqKerns HltIdxStructNb. unfold sh1entryPDchild in *.
        specialize(HBTDNotChildAnc kern idx HkernIn HbeqKerns HltIdxStructNb). contradict HBTDNotChildAnc.
        rewrite HlookupsEq in HBTDNotChildAnc; try(intro; rewrite HremovedAddrs in HBTDNotChildAnc; trivial).
        rewrite Hs2 in HBTDNotChildAnc. simpl in HBTDNotChildAnc.
        destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (CPaddr (kern + idx) + sh1offset))) eqn:HbeqSh1s;
          try(simpl in HBTDNotChildAnc; exfalso; congruence). rewrite <-beqAddrFalse in *.
        rewrite removeDupIdentity in *; auto. rewrite Hs1 in HBTDNotChildAnc. simpl in HBTDNotChildAnc.
        destruct (beqAddr currBlock (CPaddr (CPaddr (kern + idx) + sh1offset))) eqn:HbeqCBSh1;
          try(exfalso; congruence). rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
      - intros kern idx addr HkernIn HbeqKerns HltIdxStructNb HPDchildInit HaddrIn.
        assert(HaddrIns0: In addr (getAllPaddrAux [CPaddr (kern + idx)] s0)).
        {
          simpl. simpl in HaddrIn.
          rewrite HlookupsEq in HaddrIn; try(intro; rewrite HremovedAddrs in HaddrIn; trivial).
          rewrite Hs2 in HaddrIn. simpl in HaddrIn.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) (CPaddr (kern + idx))) eqn:HbeqSh1Block;
            try(simpl in HaddrIn; exfalso; congruence). rewrite <-beqAddrFalse in *.
          rewrite removeDupIdentity in *; auto. rewrite Hs1 in HaddrIn. simpl in HaddrIn.
          destruct (beqAddr currBlock (CPaddr (kern + idx))) eqn:HbeqCBBlock.
          - rewrite <-beqAddrTrue in HbeqCBBlock. rewrite <-HbeqCBBlock. rewrite HlookupCurrBs0.
            rewrite HnewB in HaddrIn. auto.
          - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto.
        }
        specialize(HremovedAddrsAnc kern idx addr HkernIn HbeqKerns HltIdxStructNb HPDchildInit HaddrIns0).
        assert(HpropsOr: In addr (getAllPaddrBlock startBlock endBlock)
          \/ ~In addr (getAllPaddrBlock startBlock endBlock)) by (apply Classical_Prop.classic).
        destruct HpropsOr.
        + apply HremovedAddrs; assumption.
        + rewrite HlookupsEq; trivial. rewrite Hs2. simpl.
          destruct (beqAddr (CPaddr (currBlock + sh1offset)) addr) eqn:HbeqSh1Addr.
          {
            rewrite <-beqAddrTrue in HbeqSh1Addr. subst addr. rewrite HlookupSh1Eqs1s0 in *.
            rewrite HremovedAddrsAnc in *. exfalso; congruence.
          }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. rewrite Hs1. simpl.
          destruct (beqAddr currBlock addr) eqn:HbeqCBAddr.
          { rewrite <-beqAddrTrue in HbeqCBAddr. subst addr. exfalso; congruence. }
          rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
      - intros kern idx HkernIn HbeqKerns HltIdxStructNb. rewrite HcomplKernLEqKern in *.
        rewrite <-Hsh1sLookupsEq; trivial. assert(HkernIsConfig: In kern (getConfigBlocks currentPart s0)).
        {
          assert(HnextProps: nextKernelIsValid s0) by (unfold deleteProps in *; intuition).
          rewrite HgetPartsEqss0 in *. rewrite completeKernListIsConfig with (pdentry:=pdentryCurr); trivial.
          2-4: unfold deleteProps in *; intuition.
          destruct (beqAddr (structure pdentryCurr) kernel) eqn:HbeqStructKern.
          - rewrite <-beqAddrTrue in HbeqStructKern. subst kernel. assumption.
          - rewrite <-beqAddrFalse in *. unfold completeListOfKernels in HkernIn.
            assert(HkernCIsKSs0Copy: isKS kernel s0) by assumption. unfold isKS in HkernCIsKSs0Copy.
            destruct (lookup kernel (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite HkernCIsKSs0Copy in *. rewrite IL.indexEqRefl in *.
            cbn -[maxNbPrepare] in HkernIn. destruct HkernIn as [Heq | HkernIn]; try(subst kern; assumption).
            pose proof (inCompleteKernListIsKernListLast maxNbPrepare currentPart pdentryCurr kern kernel s0
              HnextProps HcurrIsPart HlookupCurr HkernCIsConfigs0 HkernCIsKSs0 HkernIn) as Hlist2.
            unfold completeListOfKernels in HkernCIsConfigs0.
            assert(HstructIsKSCopy: isKS (structure pdentryCurr) s0) by assumption. unfold isKS in HstructIsKSCopy.
            destruct (lookup (structure pdentryCurr) (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite HstructIsKSCopy in *. rewrite IL.indexEqRefl in *.
            cbn -[maxNbPrepare] in HkernCIsConfigs0.
            destruct HkernCIsConfigs0 as [Heq | HkernCIsConfigs0]; try(exfalso; congruence).
            pose proof (inCompleteKernListIsKernListLast maxNbPrepare currentPart pdentryCurr kernel
              (structure pdentryCurr) s0 HnextProps HcurrIsPart HlookupCurr HstructIsConfig HstructIsKS
              HkernCIsConfigs0) as Hlist1. destruct Hlist1 as [kernList1 (Hlist1 & Hlast1 & _)].
            destruct Hlist2 as [kernList2 (Hlist2 & Hlast2 & _)].
            assert(HkernListAux: isListOfKernelsAux (kernList1 ++ kernList2) (structure pdentryCurr) s0).
            { apply isListOfKernelsAuxRecFull with kernel; assumption. }
            assert(HkernListB: isListOfKernels ((structure pdentryCurr)::kernList1 ++ kernList2) currentPart s0).
            { simpl. exists pdentryCurr. auto. }
            assert(In kern ((structure pdentryCurr)::kernList1 ++ kernList2)).
            {
              assert(Hlist2B: exists kernList2B, kernList2 = kernList2B ++ [kern]).
              {
                exists (removelast kernList2). rewrite Hlast2. apply app_removelast_last. intro. subst kernList2.
                simpl in Hlast2. congruence.
              }
              destruct Hlist2B as [kernList2B Hlist2B]. rewrite Hlist2B. simpl. right. apply in_or_app. right.
              apply in_or_app. right. simpl. auto.
            }
            revert HkernListB. apply kernListInclComplete; trivial; unfold deleteProps in *; intuition.
        }
        assert(HblockIsBE: isBE (CPaddr (kern+idx)) s).
        {
          rewrite <-HgetConfigBEqss0 in HkernIsConfig; trivial. assert(HkernIsKS: isKS kern s).
          { apply configBlocksAreKS with currentPart; trivial. }
          assert(Hres: BlocksRangeFromKernelStartIsBE s) by assumption.
          assert(HeqIdx: i (CIndex idx) = idx).
          {
            unfold CIndex. pose proof KSEntriesNbLessThanMaxIdx. destruct (Compare_dec.le_dec idx maxIdx); try(lia).
            reflexivity.
          }
          assert(HltIdxStructNbB: CIndex idx < kernelStructureEntriesNb) by lia.
          specialize(Hres kern (CIndex idx) HkernIsKS HltIdxStructNbB). rewrite HeqIdx in *. assumption.
        }
        assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s) by assumption.
        specialize(Hsh1IsSHE (CPaddr (kern+idx)) HblockIsBE). unfold isSHE in *.
        set(sh1 := CPaddr (CPaddr (kern + idx) + sh1offset)). fold sh1 in Hsh1IsSHE.
        assert(~In sh1 (getAllPaddrBlock startBlock endBlock)).
        { intro. rewrite HremovedAddrs in Hsh1IsSHE; trivial. }
        rewrite HlookupsEq; trivial. rewrite HlookupsEq in Hsh1IsSHE; trivial. rewrite Hs2. rewrite Hs2 in Hsh1IsSHE.
        simpl lookup in *. destruct (beqAddr (CPaddr (currBlock + sh1offset)) sh1) eqn:HbeqSh1s.
        {
          unfold sh1 in HbeqSh1s. rewrite <-beqAddrTrue in HbeqSh1s. apply CPaddrAddEq in HbeqSh1s; trivial.
          rewrite HcurrBlock in HbeqSh1s. assert(HbeqBlocks: kernel+currIdx = kern+idx).
          {
            unfold CPaddr in HbeqSh1s. assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition).
            assert(isPADDR nullAddr s) by assumption. unfold isPADDR in *. unfold isBE in *. subst currBlock.
            unfold CPaddr in HCBIsBEs0. destruct (Compare_dec.le_dec (kernel + currIdx) maxAddr).
            - unfold CPaddr in HblockIsBE. destruct (Compare_dec.le_dec (kern + idx) maxAddr).
              + injection HbeqSh1s. auto.
              + exfalso. replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (kern + idx) n0 |} with nullAddr in *;
                  try(cbn; f_equal; apply proof_irrelevance).
                destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
            - exfalso. replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (kernel + currIdx) n0 |} with nullAddr in *;
                  try(cbn; f_equal; apply proof_irrelevance).
                destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          exfalso. assert(HnoDupKS: noDupKSEntriesList s0) by (unfold deleteProps in *; intuition).
          assert(HkernelIsConfig: In kernel (getConfigBlocks currentPart s0)).
          {
            rewrite HgetPartsEqss0 in *. rewrite completeKernListIsConfig with (pdentry:=pdentryCurr); trivial;
              unfold deleteProps in *; intuition.
          }
          assert(Hnull: nullAddrExists s0) by (unfold deleteProps in *; intuition).
          assert(Hstruct: StructurePointerIsKS s0) by (unfold deleteProps in *; intuition).
          assert(HlenKern: maxNbPrepareIsMaxNbKernels s0) by (unfold deleteProps in *; intuition).
          assert(HnextValid: nextKernelIsValid s0) by (unfold deleteProps in *; intuition).
          assert(HblockIdxIn: In (CPaddr (kern+idx)) (filterOptionPaddr
            (getKSEntriesInStructAux (maxIdx + 1) kern s0 (CIndex (kernelStructureEntriesNb - 1))))).
          {
            assert(Heq: kern + idx = CPaddr (kern + idx)).
            {
              unfold CPaddr. unfold CPaddr in HblockIsBE. assert(isPADDR nullAddr s) by assumption.
              unfold isPADDR in *. destruct (Compare_dec.le_dec (kern + idx) maxAddr); trivial. exfalso.
              replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (kern + idx) n0 |} with nullAddr in *;
                try(cbn; f_equal; apply proof_irrelevance). unfold isBE in *.
              destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
            }
            rewrite HgetPartsEqss0 in *. assert(HkernIsKS: isKS kern s0).
            { apply configBlocksAreKS with currentPart; trivial; unfold deleteProps in *; intuition. }
            pose proof KSEntriesNbLessThanMaxIdx. apply blockInRangeInStructLight; trivial.
            - unfold deleteProps in *; intuition.
            - unfold deleteProps in *; intuition.
            - assert(Hres: BlocksRangeFromKernelStartIsBE s0) by (unfold deleteProps in *; intuition).
              assert(HeqIdx: i (CIndex idx) = idx).
              {
                unfold CIndex. pose proof KSEntriesNbLessThanMaxIdx.
                destruct (Compare_dec.le_dec idx maxIdx); try(lia). reflexivity.
              }
              assert(HltIdxStructNbB: CIndex idx < kernelStructureEntriesNb) by lia.
              specialize(Hres kern (CIndex idx) HkernIsKS HltIdxStructNbB). rewrite HeqIdx in *. assumption.
            - rewrite <-Heq. lia.
            - unfold CIndex. destruct (Compare_dec.le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
              cbn -[kernelStructureEntriesNb]. lia.
            - unfold CIndex. destruct (Compare_dec.le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
              cbn -[kernelStructureEntriesNb]. lia.
            - rewrite <-Heq. unfold CIndex.
              destruct (Compare_dec.le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
              cbn -[kernelStructureEntriesNb]. lia.
          }
          rewrite HgetPartsEqss0 in *. pose proof (noDupBlocksInConfig currentPart kern kernel s0 Hnull HnoDupKS
            Hstruct HlenKern HnextValid HcurrIsPart HkernIsConfig HkernelIsConfig HbeqKerns (CPaddr (kern+idx))
            HblockIdxIn) as Hcontra. rewrite <-HbeqSh1s in Hcontra. contradict Hcontra. subst currBlock.
          assert(Heq: kernel + currIdx = CPaddr (kernel + currIdx)).
          {
            unfold CPaddr. unfold CPaddr in HCBIsBEs0.
            assert(isPADDR nullAddr s0) by (unfold deleteProps in *; intuition).
            unfold isPADDR in *. destruct (Compare_dec.le_dec (kernel + currIdx) maxAddr); trivial. exfalso.
            replace {| p := 0; Hp := ADT.CPaddr_obligation_2 (kernel + currIdx) n0 |} with nullAddr in *;
              try(cbn; f_equal; apply proof_irrelevance). unfold isBE in *.
            destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
          }
          pose proof KSEntriesNbLessThanMaxIdx. apply blockInRangeInStructLight; trivial.
          - unfold deleteProps in *; intuition.
          - unfold deleteProps in *; intuition.
          - rewrite <-Heq. lia.
          - unfold CIndex. destruct (Compare_dec.le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
            cbn -[kernelStructureEntriesNb]. lia.
          - unfold CIndex. destruct (Compare_dec.le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
            cbn -[kernelStructureEntriesNb]. lia.
          - rewrite <-Heq. unfold CIndex.
            destruct (Compare_dec.le_dec (kernelStructureEntriesNb - 1) maxIdx); try(lia).
            cbn -[kernelStructureEntriesNb]. lia.
        }
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity in *; auto. rewrite Hs1. rewrite Hs1 in Hsh1IsSHE.
        simpl lookup in *. destruct (beqAddr currBlock sh1) eqn:HbeqCBSh1; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
    }

    instantiate(1 := fun s => exists pdentryCurr,
      S n > currIdx
      /\ currIdx < kernelStructureEntriesNb
      /\ isKS kernel s
      /\ In kernel (completeListOfKernels (structure pdentryCurr) s)
      /\ lookup blockToDelete (memory s) beqAddr = None
      /\ In blockTDParent (getMappedBlocks currentPart s)
      /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s
      /\ bentryStartAddr blockTDParent blockToDelete s
      /\ In blockToDelete (getPartitions multiplexer s)
      /\ (forall blockIdx, blockIdx < kernelStructureEntriesNb
            -> In (CPaddr (kernel+blockIdx)) (filterOptionPaddr (getKSEntries currentPart s)))
      /\ In currentPart (getPartitions multiplexer s)
      /\ lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)
      /\ (forall block startBlock endBlock, In block (getMappedBlocks currentPart s)
            -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s
            -> bentryStartAddr block startBlock s
            -> bentryEndAddr block endBlock s
            -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
                -> ~In addr (getPartitions multiplexer s)
                    /\ (forall part, In part (getPartitions multiplexer s)
                        -> ~In addr (filterOptionPaddr (getKSEntries part s))
                            /\ ~In addr (getConfigPaddr part s))
                    /\ (forall child, In child (getChildren currentPart s)
                        -> ~In addr (getMappedPaddr child s))
                    /\ (isBE addr s -> addr + scoffset < endBlock)
                    /\ (isKS addr s -> addr + nextoffset < endBlock)
                    /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+sh1offset)
                          -> In blockB (getAllPaddrBlock startBlock endBlock))
                    /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+scoffset)
                          -> In blockB (getAllPaddrBlock startBlock endBlock))
                    /\ addr <> nullAddr))
      /\ (forall part, In part (getPartitions multiplexer s) -> In blockToDelete (getChildren part s)
            -> part = currentPart)
      /\ (forall idx, idx >= currIdx -> idx < kernelStructureEntriesNb
            -> ~sh1entryPDchild (CPaddr (CPaddr (kernel+idx)+sh1offset)) blockToDelete s)
      /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
            -> In block (getMappedBlocks part s) -> sh1entryPDchild (CPaddr (block + sh1offset)) child s
            -> child <> blockToDelete)

      /\ exists sInit, P sInit /\ deleteProps sInit s currentPart blockTDParent blockToDelete
          /\ (forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s
                -> sh1entryPDchild sh1entryaddr child sInit)
          /\ (forall idx addr, idx >= currIdx -> idx < kernelStructureEntriesNb
                -> sh1entryPDchild (CPaddr (CPaddr (kernel + idx) + sh1offset)) blockToDelete sInit
                -> In addr (getAllPaddrAux [CPaddr (kernel + idx)] s) -> lookup addr (memory s) beqAddr = None)
          /\ (forall idx, idx < currIdx
                -> lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory s) beqAddr
                    = lookup (CPaddr (CPaddr (kernel+idx)+sh1offset)) (memory sInit) beqAddr)
          /\ (exists kernList, isListOfKernels kernList currentPart s
              /\ ((kernList = [] /\ kernel = structure pdentryCurr)
                  \/ (kernList <> []
                      /\ nextKSentry (CPaddr (last kernList (structure pdentryCurr)+nextoffset)) kernel s))
              /\ m > maxNbPrepare - length kernList
              /\ (forall kernBis idx, In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                    -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s)
              /\ (forall kernBis idx addr,
                    In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                    -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete sInit
                    -> In addr (getAllPaddrAux [CPaddr (kernBis + idx)] s)
                    -> lookup addr (memory s) beqAddr = None)
              /\ (forall kernBis idx, In kernBis (completeListOfKernels kernel s)
                    -> kernBis <> kernel -> idx <= kernelStructureEntriesNb - 1
                    -> lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s) beqAddr
                        = lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory sInit) beqAddr))).

    assert(isBE currBlock s).
    { unfold isBE. rewrite HlookupCBEqss1. unfold isBE. rewrite Hs1. simpl. rewrite IL.beqAddrTrue. trivial. }
    assert(lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)).
    { rewrite HlookupsEq; assumption. }
    assert(isKS kernel s).
    { unfold isKS. rewrite HlookupsEq; assumption. }

    split; only 2: intuition. exists pdentryCurr. intuition. exists sInit. intuition.
  }
  intro isCut. destruct isCut; simpl.
  + eapply bindRev.
    { (** MALInternal.Index.zero **)
      eapply weaken. apply Index.zero. intros s Hprops. apply Hprops.
    }
    intro zero. destruct (indexEq currIdx zero) eqn:HbeqIdxZero.
    * eapply weaken. apply WP.ret. intros s Hprops. simpl. apply beqIdxTrue in HbeqIdxZero.
      destruct Hprops as (Hprops & Hzero). rewrite Hzero in *. cbn in HbeqIdxZero. rewrite HbeqIdxZero in *.
      simpl i in *. destruct Hprops as ([pdentryCurr (_ & _ & HkernIsKS & HkernIsConfig & HlookupBTD & HBPMapped &
        HPDflagBP & HstartBP & HBTDIsPart & HblocksAreKSE & HcurrIsPart & HcurrIsPDT & HpropsAddrsToRem &
        HuniqueParent & HBTDNotChild & HBTDNotElse & [sInit (HP & Hcons & HPDchildImpl & HremovedAddrs &
        HremainingLookup & HkernList)])] & _).
      exists pdentryCurr. repeat (split; trivial).
      --- intro idx. assert(HgebIdxZero: idx >= 0) by lia. apply HBTDNotChild; assumption.
      --- exists sInit. repeat (split; trivial).
          +++ intros idx addr. apply HremovedAddrs; lia.
          +++ destruct HkernList as [kernList (HkernList & HstructOr & Hlen & HBTDNotChildAnc & HremovedAddrsAnc &
                HremainingLookupAnc)].
              exists kernList. repeat (split; trivial).
              *** intros kern idx HkernIn HltIdxStructNb. destruct (beqAddr kern kernel) eqn:HbeqKerns.
                  ----- rewrite <-beqAddrTrue in HbeqKerns. subst kern. apply HBTDNotChild; lia.
                  ----- rewrite <-beqAddrFalse in *. apply HBTDNotChildAnc; assumption.
              *** intros kern idx addr HkernIn HltIdxStructNb HPDchild HaddrIn.
                  destruct (beqAddr kern kernel) eqn:HbeqKerns.
                  ----- rewrite <-beqAddrTrue in HbeqKerns. subst kern. apply HremovedAddrs with idx; trivial; lia.
                  ----- rewrite <-beqAddrFalse in *. apply in_app_or in HkernIn. simpl in HkernIn.
                        destruct HkernIn as [HkernIn | [Hcontra | Hcontra]]; try(exfalso; congruence).
                        apply HremovedAddrsAnc with kern idx; assumption.
    * eapply bindRev.
      { (** indexPredM **)
        eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops.
        apply beqIdxFalse in HbeqIdxZero. destruct Hprops as (Hprops & Hzero). subst zero.
        apply index_neq_i in HbeqIdxZero. cbn in HbeqIdxZero. lia.
      }
      intro idxpred. eapply weaken. apply IHn.
      intros s Hprops. simpl. destruct Hprops as ((([pdentryCurr (HgtSNCurr & HltCurrStructNb & HkernIsKS &
        HkernIsConfig & HlookupBTD & HBPMapped & HPDflagBP & HstartBP & HBTDIsPart & HblocksAreKSE & HcurrIsPart &
        HcurrIsPDT & HpropsAddrToRemove & HuniqueParent & HBTDNotChild & HBTDNotElse & [sInit (HP & Hcons &
        HPDchildImpl & HaddrsRemoved & HremainingLookup & HkernList)])] & Horigin) & Hzero) & Hpred).
      unfold StateLib.Index.pred in *. destruct (Compare_dec.gt_dec currIdx 0); try(exfalso; congruence).
      injection Hpred as Hpred. subst idxpred. simpl. exists pdentryCurr. intuition.
      +++ exists sInit. repeat (split; trivial).
          *** intros idx HgtIdxCurrM. apply HremainingLookup; lia.
          *** intros idx addr HgtIdxCurrM. apply HaddrsRemoved; lia.
      +++ lia.
      +++ lia.
      +++ assert(HgebIdxCurr: idx >= currIdx) by lia. specialize(HBTDNotChild idx HgebIdxCurr).
          apply HBTDNotChild; assumption.
  + (* eapply bindRev.
    { (** Internal.writeAccessibleRec **)
      eapply weaken. apply ? (*TODO needs another lemma*). intros s Hprops. apply Hprops.
    }
    intro. eapply bindRev.
    { (** MALInternal.Index.zero **)
      eapply weaken. apply Index.zero. intros s Hprops. apply Hprops.
    }
    intro zero. destruct (indexEq currIdx zero) eqn:HbeqIdxZero. (*TODO*)
    * eapply weaken. apply WP.ret. intros s Hprops. simpl. apply beqIdxTrue in HbeqIdxZero.
      
    *  *) admit.
- eapply bindRev.
  { (** MALInternal.Index.zero **)
    eapply weaken. apply Index.zero. intros s Hprops. apply Hprops.
  }
  intro zero. destruct (indexEq currIdx zero) eqn:HbeqIdxZero.
  + eapply weaken. apply WP.ret. intros s Hprops. simpl. apply beqIdxTrue in HbeqIdxZero.
    destruct Hprops as (Hprops & Hzero). rewrite Hzero in *. cbn in HbeqIdxZero. rewrite HbeqIdxZero in *.
    simpl i in *. destruct Hprops as (((([pdentryCurr ([sInit (HP & Hcons & HPDchildImpl & HremainingLookup &
      HremovedAddrs & HkernList)] & _ & _ & HkernIsKS & HkernIsConfig & HlookupBTD & HBPMapped & HPDflagBP & HstartBP
      & HBTDIsPart & HblocksAreKSE & HcurrIsPart & HcurrIsPDT & HpropsAddrsToRem & HuniqueParent & HBTDNotChild &
      HBTDNotElse)] & Hcurr) & Hstart) & Hend) & Hsh1).
    exists pdentryCurr. repeat (split; trivial).
    * intro idx. destruct (Nat.eqb idx 0) eqn:HeqIdxZero.
      --- apply PeanoNat.Nat.eqb_eq in HeqIdxZero. subst idx. do 2 (rewrite <-plus_n_O in *). rewrite <-Hcurr in *.
          intros _. destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchild & Hsh1)]].
          unfold sh1entryAddr in *. destruct (lookup currBlock (memory s) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). subst sh1entryaddr. intro Hcontra. unfold sh1entryPDchild in *.
          rewrite <-beqAddrFalse in *. rewrite HlookupSh1 in *. rewrite <-Hcontra in *. congruence.
      --- apply PeanoNat.Nat.eqb_neq in HeqIdxZero. assert(HgtIdxZero: idx > 0) by lia.
          apply HBTDNotChild; assumption.
    * exists sInit. assert(forall idx addr, idx < kernelStructureEntriesNb
        -> sh1entryPDchild (CPaddr (CPaddr (kernel + idx) + sh1offset)) blockToDelete sInit
        -> In addr (getAllPaddrAux [(CPaddr (kernel+idx))] s)
        -> lookup addr (memory s) beqAddr = None).
      {
        intros idx addr. destruct (Nat.eqb idx 0) eqn:HbeqIdxBZero.
        - apply PeanoNat.Nat.eqb_eq in HbeqIdxBZero. subst idx. rewrite <-plus_n_O in *. rewrite <-plus_n_O in *.
          rewrite <-Hcurr. destruct Hsh1 as [sh1entry [sh1 (_ & HPDchild & Hsh1)]]. intros _ HPDchildB. exfalso.
          unfold sh1entryAddr in *. destruct (lookup currBlock (memory s) beqAddr); try(congruence).
          destruct v; try(congruence). subst sh1. assert(Hleb: 0 <= 0) by lia.
          specialize(HremainingLookup 0 Hleb). rewrite <-plus_n_O in *. unfold sh1entryPDchild in *.
          rewrite <-Hcurr in *. rewrite HremainingLookup in *. rewrite <-beqAddrFalse in *.
          destruct (lookup (CPaddr (currBlock + sh1offset)) (memory sInit) beqAddr); try(congruence).
          destruct v; congruence.
        - apply PeanoNat.Nat.eqb_neq in HbeqIdxBZero. apply HremovedAddrs; lia.
      }
      repeat (split; trivial).
      destruct HkernList as [kernList (HkernList & HstructOr & Hlen & HBTDNotChildAnc & HremovedAddrsAnc &
        HremainingLookupAnc)].
      exists kernList. repeat (split; trivial).
      --- intros kern idx HkernIn. destruct (beqAddr kern kernel) eqn:HbeqKerns.
          +++ apply <-beqAddrTrue in HbeqKerns. subst kern. destruct (Nat.eqb idx 0) eqn:HeqIdxZero.
              *** apply PeanoNat.Nat.eqb_eq in HeqIdxZero. subst idx. do 2 (rewrite <-plus_n_O in *).
                  rewrite <-Hcurr in *. intros _ HPDchild. rewrite <-beqAddrFalse in *.
                  destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchildB & Hsh1)]].
                  unfold sh1entryAddr in *. destruct (lookup currBlock (memory s) beqAddr); try(exfalso; congruence).
                  destruct v; try(exfalso; congruence). subst sh1entryaddr. exfalso. assert(HlebZero: 0 <= 0) by lia.
                  specialize(HremainingLookup 0 HlebZero). rewrite <-plus_n_O in *. rewrite <-Hcurr in *.
                  unfold sh1entryPDchild in *. rewrite HremainingLookup in *. rewrite HlookupSh1 in *.
                  rewrite <-HPDchild in *. congruence.
              *** apply PeanoNat.Nat.eqb_neq in HeqIdxZero. assert(HgtIdxZero: idx > 0) by lia.
                  apply HBTDNotChild; assumption.
          +++ rewrite <-beqAddrFalse in *. apply HBTDNotChildAnc; assumption.
      --- intros kern idx addr HkernIn. destruct (beqAddr kern kernel) eqn:HbeqKerns.
          +++ apply <-beqAddrTrue in HbeqKerns. subst kern. destruct (Nat.eqb idx 0) eqn:HeqIdxZero.
              *** apply PeanoNat.Nat.eqb_eq in HeqIdxZero. subst idx. do 2 (rewrite <-plus_n_O in *).
                  rewrite <-Hcurr in *. intros _ HPDchildCB _.
                  destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchildB & Hsh1)]].
                  unfold sh1entryAddr in *. destruct (lookup currBlock (memory s) beqAddr); try(exfalso; congruence).
                  destruct v; try(exfalso; congruence). subst sh1entryaddr. exfalso. assert(HlebZero: 0 <= 0) by lia.
                  specialize(HremainingLookup 0 HlebZero). rewrite <-plus_n_O in *. rewrite <-Hcurr in *.
                  unfold sh1entryPDchild in *. rewrite HremainingLookup in *. rewrite HlookupSh1 in *.
                  rewrite <-HPDchildCB in *. rewrite <-beqAddrFalse in *. congruence.
              *** apply PeanoNat.Nat.eqb_neq in HeqIdxZero. assert(HgtIdxZero: idx > 0) by lia.
                  apply HremovedAddrs; assumption.
          +++ rewrite <-beqAddrFalse in *. apply in_app_or in HkernIn. simpl in HkernIn.
              destruct HkernIn as [HkernIn | [Hcontra | Hcontra]]; try(exfalso; congruence).
              apply HremovedAddrsAnc; assumption.
  + eapply bindRev.
    { (** indexPredM **)
      eapply weaken. apply Index.pred. intros s Hprops. simpl. split. apply Hprops.
      apply beqIdxFalse in HbeqIdxZero. destruct Hprops as (Hprops & Hzero). subst zero.
      apply index_neq_i in HbeqIdxZero. cbn in HbeqIdxZero. lia.
    }
    intro idxpred. eapply weaken. apply IHn.
    intros s Hprops. simpl. destruct Hprops as (((((([pdentryCurr ([sInit (HP & Hcons & HPDchildImpl &
      HremainingLookup & HremovedAddrs & HkernList)] & HgtSNCurr & HltCurrStructNb & HkernIsKS & HkernIsConfig &
      HlookupBTD & HBPMapped & HPDflagBP & HstartBP & HBTDIsPart & HblocksAreKSE & HcurrIsPart & HcurrIsPDT &
      HpropsAddrsToRem & HuniqueParent & HBTDNotChild & HBTDNotElse)] & Hcurr) & Hstart) & Hend) & Hsh1) & Hzero) &
      Hpred).
    exists pdentryCurr. unfold StateLib.Index.pred in *.
    destruct (Compare_dec.gt_dec currIdx 0); try(exfalso; congruence). injection Hpred as Hpred. subst idxpred.
    simpl. intuition.
    * exists sInit. repeat (split; trivial).
      --- intros idx HgtIdxCurrM. apply HremainingLookup; lia.
      --- intros idx addr HgtIdxCurrM.
          destruct (Nat.eqb idx currIdx) eqn:HeqIdx.
          +++ apply PeanoNat.Nat.eqb_eq in HeqIdx. subst idx. cbn in Hcurr. rewrite <-plus_n_O in *.
              rewrite <-Hcurr in *.
              intros _ HPDchildCB _. destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchildB & Hsh1)]].
              unfold sh1entryAddr in *. destruct (lookup currBlock (memory s) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). subst sh1entryaddr. exfalso.
              assert(HlebCurr: currIdx <= currIdx) by lia. specialize(HremainingLookup currIdx HlebCurr).
              rewrite <-Hcurr in *. unfold sh1entryPDchild in *. rewrite HremainingLookup in *.
              rewrite HlookupSh1 in *. rewrite <-HPDchildCB in *. rewrite <-beqAddrFalse in *. congruence.
          +++ apply PeanoNat.Nat.eqb_neq in HeqIdx. apply HremovedAddrs; lia.
    * lia.
    * lia.
    * destruct (Nat.eqb idx currIdx) eqn:HeqIdx.
      --- apply PeanoNat.Nat.eqb_eq in HeqIdx. subst idx. cbn in Hcurr. rewrite <-plus_n_O in *. rewrite <-Hcurr in *.
          destruct Hsh1 as [sh1entry [sh1entryaddr (HlookupSh1 & HPDchildB & Hsh1)]]. unfold sh1entryAddr in *.
          exfalso. destruct (lookup currBlock (memory s) beqAddr); try(congruence). destruct v; try(congruence).
          subst sh1entryaddr. unfold sh1entryPDchild in *. rewrite HlookupSh1 in *. rewrite <-HPDchildB in *.
          rewrite <-beqAddrFalse in *. congruence.
      --- apply PeanoNat.Nat.eqb_neq in HeqIdx. assert(HgtIdxCurr: idx > currIdx) by lia.
          specialize(HBTDNotChild idx HgtIdxCurr). apply HBTDNotChild; assumption.
Admitted.

Lemma deleteSharedBlocksRecAux n currentPart kernel blockTDParent blockToDelete P:
{{ fun s => exists pdentryCurr,
    (exists s0, P s0 /\ deleteProps s0 s currentPart blockTDParent blockToDelete
        /\ (forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s
              -> sh1entryPDchild sh1entryaddr child s0)
        /\ (exists kernList, isListOfKernels kernList currentPart s
              /\ ((kernList = [] /\ kernel = structure pdentryCurr)
                  \/ (kernList <> []
                      /\ nextKSentry (CPaddr (last kernList (structure pdentryCurr)+nextoffset)) kernel s))
              /\ n > maxNbPrepare - length kernList
              /\ (forall kernBis idx, In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                    -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s)
              /\ (forall kernBis idx addr,
                    In kernBis kernList -> kernBis <> kernel -> idx < kernelStructureEntriesNb
                    -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete s0
                    -> In addr (getAllPaddrAux [CPaddr (kernBis + idx)] s)
                    -> lookup addr (memory s) beqAddr = None)
              /\ (forall kernBis idx, In kernBis (completeListOfKernels kernel s)
                    -> idx <= kernelStructureEntriesNb - 1
                    -> lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s) beqAddr
                        = lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s0) beqAddr)))
    /\ (kernel <> nullAddr -> isKS kernel s /\ In kernel (completeListOfKernels (structure pdentryCurr) s))
    /\ lookup blockToDelete (memory s) beqAddr = None
    /\ In blockTDParent (getMappedBlocks currentPart s)
    /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s
    /\ bentryStartAddr blockTDParent blockToDelete s
    /\ In blockToDelete (getPartitions multiplexer s)
    /\ (forall kernBis blockIdx, In kernBis (completeListOfKernels kernel s) -> blockIdx < kernelStructureEntriesNb
          -> In (CPaddr (kernBis+blockIdx)) (filterOptionPaddr (getKSEntries currentPart s)))
    /\ In currentPart (getPartitions multiplexer s)
    /\ lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)
    /\ (forall block startBlock endBlock, In block (getMappedBlocks currentPart s)
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s
          -> bentryStartAddr block startBlock s
          -> bentryEndAddr block endBlock s
          -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
              -> ~In addr (getPartitions multiplexer s)
                  /\ (forall part, In part (getPartitions multiplexer s)
                      -> ~In addr (filterOptionPaddr (getKSEntries part s))
                          /\ ~In addr (getConfigPaddr part s))
                  /\ (forall child, In child (getChildren currentPart s)
                      -> ~In addr (getMappedPaddr child s))
                  /\ (isBE addr s -> addr + scoffset < endBlock)
                  /\ (isKS addr s -> addr + nextoffset < endBlock)
                  /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+sh1offset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+scoffset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ addr <> nullAddr))
    /\ (forall part, In part (getPartitions multiplexer s) -> In blockToDelete (getChildren part s)
          -> part = currentPart)
    /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
          -> In block (getMappedBlocks part s)
          -> sh1entryPDchild (CPaddr (block+sh1offset)) child s
          -> child <> blockToDelete)
}}
Internal.deleteSharedBlocksRecAux n currentPart kernel blockToDelete
{{ fun _ s => exists pdentryCurr,
  lookup blockToDelete (memory s) beqAddr = None /\ In blockTDParent (getMappedBlocks currentPart s)
  /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s
  /\ bentryStartAddr blockTDParent blockToDelete s /\ In blockToDelete (getPartitions multiplexer s)
  /\ In currentPart (getPartitions multiplexer s)
  /\ lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)
  /\ (forall kernBis idx, In kernBis (completeListOfKernels (structure pdentryCurr) s)
      -> idx < kernelStructureEntriesNb
      -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s)
  /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
        -> In block (getMappedBlocks part s)
        -> sh1entryPDchild (CPaddr (block+sh1offset)) child s
        -> child <> blockToDelete)
  /\ (exists s0, P s0 /\ deleteProps s0 s currentPart blockTDParent blockToDelete
      /\ (forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s
            -> sh1entryPDchild sh1entryaddr child s0)
      /\ (forall kernBis idx, In kernBis (completeListOfKernels (structure pdentryCurr) s)
            -> idx < kernelStructureEntriesNb
            -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete s)
      /\ (forall kernBis idx addr, In kernBis (completeListOfKernels (structure pdentryCurr) s)
            -> idx < kernelStructureEntriesNb
            -> sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s0
            -> In addr (getAllPaddrAux [CPaddr (kernBis+idx)] s)
            -> lookup addr (memory s) beqAddr = None))
}}.
Proof.
revert kernel.
induction n; cbn -[maxNbPrepare nullAddr getAllPaddrAux getConfigPaddr kernelStructureEntriesNb]; intro.
{
  eapply weaken. apply WP.ret. intros s Hprops.
  destruct Hprops as [_ ([s0 (_ & _ & _ & [kernList (_ & _ & Hn & _)])] & _)]. lia.
}
destruct (beqAddr kernel nullAddr) eqn:HbeqKernNull.
- eapply weaken. apply WP.ret. intros s Hprops. simpl. destruct Hprops as [pdentryCurr ([sInit (HP & Hcons &
    HPDchildImpl & [kernList (HkernList & HlastKern & HgtSNMax & HBTDNotChild & HremovedAddrs & HlookupAncEq)])] &
    HkernIsNullOrKS & HlookupBTD & HBPMapped & HPDflagBP & HstartBP & HBTDIsPart & HblocksAreKSE & HcurrIsPart &
    HlookupCurr & HpropsAddrsToRemove & HuniqueChild & HBTDNotInElse)]. exists pdentryCurr.
  rewrite <-beqAddrTrue in HbeqKernNull. subst kernel.
  assert(HkernListIsCompl: forall kernBis, In kernBis (completeListOfKernels (structure pdentryCurr) s)
    -> In kernBis kernList /\ kernBis <> nullAddr).
  {
    intros kernBis HkernBis. assert(Hlen: maxNbPrepareIsMaxNbKernels s) by (unfold deleteProps in *; intuition).
    specialize(Hlen currentPart kernList HcurrIsPart HkernList).
    destruct kernList; simpl in HkernList.
    {
      destruct HlastKern as [(_ & HbeqNullStruct) | (Hcontra & _)]; try(exfalso; congruence).
      rewrite <-HbeqNullStruct in *. unfold completeListOfKernels in *.
      assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition). unfold isPADDR in *. exfalso.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; simpl in HkernBis; congruence.
    }
    destruct HkernList as [pdentryCBis (HlookupCurrB & HbeqStructNull & HstructEq & HkernList)].
    rewrite HlookupCurr in *. injection HlookupCurrB as HpdentriesEq. subst pdentryCBis. rewrite <-HstructEq in *.
    destruct HlastKern as [(Hcontra & _) | (_ & HnullIsNext)]; try(exfalso; congruence).
    assert(HstructIsKS: StructurePointerIsKS s) by (unfold deleteProps in *; intuition).
    specialize(HstructIsKS currentPart pdentryCurr HcurrIsPart HlookupCurr HbeqStructNull).
    assert(Hpost: exists postList, completeListOfKernels (structure pdentryCurr) s
      = (structure pdentryCurr)::kernList++postList).
    {
      apply listOfKernIsInclInComplete with currentPart pdentryCurr; trivial.
      - unfold deleteProps in *; intuition.
      - unfold completeListOfKernels. unfold isKS in *.
        destruct (lookup (structure pdentryCurr) (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite HstructIsKS. rewrite IL.indexEqRefl. cbn -[maxNbPrepare]. auto.
      - simpl in Hlen. lia.
    }
    destruct Hpost as [postList Hpost].
    assert(HcomplIsKL: isListOfKernels (completeListOfKernels (structure pdentryCurr) s) currentPart s).
    { apply completeKernListIsListOfKern; trivial; unfold deleteProps in *; intuition. }
    rewrite Hpost in *. clear Hpost HBTDNotChild Hlen HgtSNMax HkernList HremovedAddrs. simpl. simpl in HkernBis.
    simpl in HcomplIsKL. destruct HcomplIsKL as [_ (_ & _ & _ & HcomplIsKL)]. clear IHn.
    destruct HkernBis as [HeqKernStruct | HkernBis].
    - subst kernBis. auto.
    - assert(Hres: In kernBis kernList /\ kernBis <> nullAddr).
      {
        assert(HlastEq: last (structure pdentryCurr::kernList) (structure pdentryCurr)
          = last kernList (structure pdentryCurr)).
        { apply IL.lastRec with (structure pdentryCurr). reflexivity. }
        rewrite HlastEq in *. clear HlastEq. revert HkernBis HcomplIsKL HnullIsNext. clear HkernIsNullOrKS.
        generalize (structure pdentryCurr). induction kernList; intro initKern; intros.
        {
          destruct postList; simpl in *; try(exfalso; congruence). unfold nextKSentry in *.
          destruct HcomplIsKL as (HlookupNext & _ & HbeqFirstNull & HcomplIsKL). rewrite HlookupNext in *.
          exfalso; congruence.
        }
        assert(HlastEq: last (a::kernList) initKern = last kernList a).
        { apply IL.lastRec with initKern. reflexivity. }
        rewrite HlastEq in *. clear HlastEq. simpl in *.
        destruct HcomplIsKL as (HlookupNext & _ & HbeqANull & HcomplIsKL). destruct HkernBis as [Heq | HkernBis].
        + subst a. auto.
        + specialize(IHkernList a HkernBis HcomplIsKL HnullIsNext). destruct IHkernList. auto.
      }
      destruct Hres. auto.
  }
  repeat (split; trivial).
  + intros kernBis idx HkernBInCompl. apply HkernListIsCompl in HkernBInCompl. destruct HkernBInCompl.
    apply HBTDNotChild; assumption.
  + exists sInit. repeat (split; trivial).
    * intros kernBis idx HkernBInCompl. apply HkernListIsCompl in HkernBInCompl. destruct HkernBInCompl.
      apply HBTDNotChild; assumption.
    * intros kernBis idx addr HkernBInCompl. apply HkernListIsCompl in HkernBInCompl. destruct HkernBInCompl.
      apply HremovedAddrs; assumption.
- eapply bindRev.
  { (* MALInternal.getKernelStructureEntriesNb *)
    apply getKernelStructureEntriesNb.
  }
  intro entriesnb. eapply bindRev.
  { (* indexPredM *)
    eapply weaken. apply Index.pred. intros s Hprops. split. apply Hprops. destruct Hprops as (_ & Heq).
    subst entriesnb. cbn. unfold CIndex. pose proof Constants.maxIdxBiggerThanMinBlock.
    destruct (Compare_dec.le_dec 8 maxIdx); try(lia). simpl. lia.
  }
  intro lastindex. eapply bindRev.
  { (* Internal.deleteSharedBlocksInStructRecAux *)
    eapply weaken. apply deleteSharedBlocksInStructRecAux with (blockTDParent:=blockTDParent).
    intros s Hprops. destruct Hprops as (([pdentryCurr ([sInit (HP & Hcons & HPDchildImpl & [kernList (HkernList &
      HlastKern & HgtSNMax & HBTDNotChild & HremovedAddrs & HlookupAncEq)])] & HkernIsNullOrKS & HlookupBTD &
      HBPMapped & HPDflagBP & HstartBP & HBTDIsPart & HblocksAreKSE & HcurrIsPart & HlookupCurr & HpropsAddrsToRemove
      & HuniqueChild & HBTDNotInElse)] & Hentries) & Hpred). exists pdentryCurr. instantiate(2 := P).
    unfold StateLib.Index.pred in *. destruct (Compare_dec.gt_dec entriesnb 0); try(exfalso; congruence).
    injection Hpred as Hpred. subst lastindex. simpl i. pose proof maxIdxBiggerThanNbOfKernels as HgtMaxStructNb.
    assert(HiEntries: i entriesnb = kernelStructureEntriesNb).
    {
      unfold CIndex in Hentries. destruct (Compare_dec.le_dec kernelStructureEntriesNb maxIdx); try(lia).
      subst entriesnb. reflexivity.
    }
    rewrite HiEntries. unfold N. rewrite maxIdxEqualMaxAddr in HgtMaxStructNb. rewrite <-beqAddrFalse in *.
    specialize(HkernIsNullOrKS HbeqKernNull). destruct HkernIsNullOrKS as (HkernIsNullOrKS & HkernIsConfig).
    assert(forall blockIdx, blockIdx < kernelStructureEntriesNb
      -> In (CPaddr (kernel + blockIdx)) (filterOptionPaddr (getKSEntries currentPart s))).
    {
      intro. assert(In kernel (completeListOfKernels kernel s)).
      {
        unfold completeListOfKernels. unfold isKS in *.
        destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        rewrite HkernIsNullOrKS. rewrite IL.indexEqRefl. cbn -[maxNbPrepare]. auto.
      }
      apply HblocksAreKSE; assumption.
    }
    assert(forall idx, idx > kernelStructureEntriesNb - 1 -> idx < kernelStructureEntriesNb
      -> ~sh1entryPDchild (CPaddr (CPaddr (kernel + idx) + sh1offset)) blockToDelete s).
    { intros idx Hgt Hlt. lia. }
    assert(HlookupBlocksEq: forall idx, idx <= kernelStructureEntriesNb - 1
      -> lookup (CPaddr (CPaddr (kernel + idx) + sh1offset)) (memory s) beqAddr
          = lookup (CPaddr (CPaddr (kernel + idx) + sh1offset)) (memory sInit) beqAddr).
    {
      intros idx HlebIdxStructNb. assert(HkernIsAutoConfig: In kernel (completeListOfKernels kernel s)).
      {
        unfold completeListOfKernels. unfold isKS in *.
        destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite HkernIsNullOrKS. rewrite IL.indexEqRefl. cbn -[maxNbPrepare].
        auto.
      }
      apply HlookupAncEq; assumption.
    }
    assert(forall idx addr, idx > kernelStructureEntriesNb - 1 -> idx < kernelStructureEntriesNb
      -> sh1entryPDchild (CPaddr (CPaddr (kernel + idx) + sh1offset)) blockToDelete sInit
      -> In addr (getAllPaddrAux [CPaddr (kernel + idx)] s) -> lookup addr (memory s) beqAddr = None).
    { intros idx addr Hgt Hlt. lia. }
    repeat (split; trivial); try(lia). exists sInit. repeat (split; trivial). exists kernList. instantiate(1 := S n).
    repeat (split; trivial). intros kern idx HkernBIsConfig _. apply HlookupAncEq; assumption.
    (*TODO that's weird, right ?*)
  }
  intro. eapply bindRev.
  { (* MAL.readNextFromKernelStructureStart *)
    eapply weaken. apply readNextFromKernelStructureStart. intros s Hprops. split. apply Hprops.
    destruct Hprops as [pdentryCurr (_ & HkernIsKS & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & [sInit Hprops0])].
    unfold deleteProps in *; intuition.
  }
  intro nextStructureAddr. eapply weaken. apply IHn. intros s Hprops.
  destruct Hprops as ([pdentryCurr (HBTDNotChild & HkernIsKS & HkernIsConfig & HlookupBTD & HBPMapped & HPDflagBP &
    HstartBP & HBTDIsPart & HcurrIsPart & HlookupCurr & HpropsAddrsToRemove & HuniqueChild & HBTDNotInElse & [sInit
    (HP & Hprops & HPDchildImpl & HremovedAddrs & HkernList)])] & [offset ((Hoffset & HnextKern) & HnextIsPADDR)]).
  assert(HnextProps: nextStructureAddr <> nullAddr -> isKS nextStructureAddr s
    /\ In nextStructureAddr (completeListOfKernels (structure pdentryCurr) s)).
  {
    intro HbeqNextNull. assert(HnextValid: nextKernelIsValid s) by (unfold deleteProps in *; intuition).
    specialize(HnextValid currentPart pdentryCurr kernel HcurrIsPart HlookupCurr HkernIsConfig HkernIsKS).
    destruct HnextValid as (Hleb & [nextAddr (Hlookup & HresOr)]). subst offset.
    unfold CPaddr in HnextIsPADDR. unfold nextKSentry in HnextIsPADDR.
    destruct (Compare_dec.le_dec (kernel + nextoffset) maxAddr); try(lia). rewrite Hlookup in HnextIsPADDR.
    subst nextAddr. destruct HresOr; try(exfalso; congruence). assumption.
  }
  exists pdentryCurr. repeat (split; trivial).
  + exists sInit. repeat (split; trivial). destruct HkernList as [kernList (HkernList & HpropsOr & Hlen &
      HBTDNotChildL & HremovedAddrsAnc & HlookupAncEq)]. exists (kernList++[kernel]).
    assert(HkernListRec: isListOfKernels (kernList ++ [kernel]) currentPart s).
    {
      destruct kernList; simpl in HkernList; simpl.
      - destruct HpropsOr as [(_ & Heq) | (Hcontra & _)]; try(exfalso; congruence). exists pdentryCurr.
        rewrite <-beqAddrFalse in *. subst kernel. auto.
      - destruct HkernList as [pdentry (Hlookup & HbeqStructNull & Heq & HkernList)]. exists pdentry.
        repeat (split; trivial). destruct HpropsOr as [(Hcontra & _) | (_ & Hnext)]; try(exfalso; congruence).
        rewrite <-beqAddrFalse in *.
        apply IL.isListOfKernelsAuxRec with (last (p :: kernList) (structure pdentryCurr)); trivial.
        + apply IL.lastRec with (structure pdentryCurr); reflexivity.
        + unfold nextKSentry in *.
          destruct (lookup (CPaddr (last (p :: kernList) (structure pdentryCurr) + nextoffset)) (memory s) beqAddr);
            try(exfalso; congruence). destruct v; try(exfalso; congruence). rewrite <-Hnext. reflexivity.
        + assert(Hres: nextKernelIsValid s) by (unfold deleteProps in *; intuition).
          assert(HlastIsConfig: In (last (p::kernList) (structure pdentryCurr))
            (completeListOfKernels (structure pdentryCurr) s)).
          {
            apply kernListInclComplete with (p::kernList) currentPart; trivial.
            1-2: unfold deleteProps in *; intuition.
            - apply IL.lastOfNotEmptyIsIn with (structure pdentryCurr); reflexivity.
            - simpl. exists pdentry. auto.
          }
          assert(HlastIsKS: isKS (last (p::kernList) (structure pdentryCurr)) s).
          {
            rewrite <-completeKernListIsConfig with (part:=currentPart) in HlastIsConfig; trivial.
            2-4: unfold deleteProps in *; intuition.
            apply configBlocksAreKS with currentPart; trivial; unfold deleteProps in *; intuition.
          }
          specialize(Hres currentPart pdentryCurr (last (p::kernList) (structure pdentryCurr)) HcurrIsPart
            HlookupCurr HlastIsConfig HlastIsKS). apply Hres.
    }
    assert(kernList ++ [kernel] = [] /\ nextStructureAddr = structure pdentryCurr \/
       kernList ++ [kernel] <> [] /\
       nextKSentry (CPaddr (last (kernList ++ [kernel]) (structure pdentryCurr) + nextoffset)) nextStructureAddr s).
    {
      right. split.
      - intro Hcontra. apply app_eq_nil in Hcontra. destruct Hcontra; congruence.
      - rewrite last_last. subst offset. assumption.
    }
    assert(n > maxNbPrepare - length (kernList ++ [kernel])).
    {
      assert(HlenKL: maxNbPrepareIsMaxNbKernels s) by (unfold deleteProps in *; intuition).
      specialize(HlenKL currentPart (kernList ++ [kernel]) HcurrIsPart HkernListRec).
      rewrite length_app in *. cbn -[maxNbPrepare] in *. rewrite PeanoNat.Nat.sub_add_distr. lia.
    }
    assert(forall kernBis idx, In kernBis (kernList ++ [kernel]) -> kernBis <> nextStructureAddr
      -> idx < kernelStructureEntriesNb
      -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete s).
    {
      intros kern idx HkernInL _. apply in_app_or in HkernInL. simpl in HkernInL.
      destruct HkernInL as [HkernInL | [Heq | Hcontra]]; try(exfalso; congruence).
      - apply HBTDNotChildL; assumption.
      - subst kern. apply HBTDNotChild; assumption.
    }
    assert(forall kernBis idx addr, In kernBis (kernList ++ [kernel]) -> kernBis <> nextStructureAddr
      -> idx < kernelStructureEntriesNb
      -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete sInit
      -> In addr (getAllPaddrAux [CPaddr (kernBis + idx)] s) -> lookup addr (memory s) beqAddr = None).
    {
      intros kern idx addr HkernInL _. apply HremovedAddrsAnc; assumption.
    }
    assert(forall kernBis idx, In kernBis (completeListOfKernels nextStructureAddr s)
      -> idx <= kernelStructureEntriesNb - 1
      -> lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory s) beqAddr
          = lookup (CPaddr (CPaddr (kernBis + idx) + sh1offset)) (memory sInit) beqAddr).
    {
      intros kern idx HkernIsConfigNext.
      assert(HlistEq: completeListOfKernels kernel s = kernel::completeListOfKernels nextStructureAddr s).
      {
        assert(HlenL: length (completeListOfKernels kernel s) <= maxNbPrepare).
        {
          assert(HlenL: maxNbPrepareIsMaxNbKernels s) by (unfold deleteProps in *; intuition).
          assert(Hlist: isListOfKernels (completeListOfKernels (structure pdentryCurr) s) currentPart s).
          { apply completeKernListIsListOfKern; trivial; unfold deleteProps in *; intuition. }
          specialize(HlenL currentPart (completeListOfKernels (structure pdentryCurr) s) HcurrIsPart Hlist).
          unfold completeListOfKernels in *. destruct (lookup (structure pdentryCurr) (memory s) beqAddr);
            try(simpl in HkernIsConfig; exfalso; congruence).
          destruct v; try(simpl in HkernIsConfig; exfalso; congruence).
          destruct (indexEq (blockindex b) (CIndex 0)); try(simpl in HkernIsConfig; exfalso; congruence).
          assert(HkernIsKSCopy: isKS kernel s) by assumption. unfold isKS in HkernIsKSCopy.
          destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
          rewrite HkernIsKSCopy. rewrite IL.indexEqRefl. revert HkernIsConfig HlenL. generalize maxNbPrepare as m.
          intro. generalize (structure pdentryCurr) as kernB. induction m; intros; try(simpl in HlenL; lia).
          simpl in HkernIsConfig. destruct HkernIsConfig as [Heq | HkernIsConfig].
          - subst kernB. assumption.
          - simpl in HlenL. destruct (lookup (CPaddr (kernB + nextoffset)) (memory s) beqAddr);
              try(simpl in HkernIsConfig; exfalso; congruence).
            destruct v; try(simpl in HkernIsConfig; exfalso; congruence).
            destruct (beqAddr p nullAddr); try(simpl in HkernIsConfig; exfalso; congruence).
            assert(HlenLRec: length (p :: completeListOfKernelsAux m p s) <= m) by lia.
            specialize(IHm p HkernIsConfig HlenLRec).
            assert(Heq: completeListOfKernelsAux m kernel s = completeListOfKernelsAux (S m) kernel s).
            {
              simpl in IHm. apply completeListOfKernelsAuxN; lia.
            }
            rewrite <-Heq. lia.
        }
        unfold completeListOfKernels in *. unfold isKS in *.
        destruct (lookup kernel (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        destruct (lookup nextStructureAddr (memory s) beqAddr) eqn:HlookupNext;
          try(simpl in HkernIsConfigNext; exfalso; congruence).
        destruct v; try(simpl in HkernIsConfigNext; exfalso; congruence). rewrite HkernIsKS in *.
        destruct (indexEq (blockindex b0) (CIndex 0)); try(simpl in HkernIsConfigNext; exfalso; congruence).
        rewrite IL.indexEqRefl in *. f_equal. cbn -[maxNbPrepare] in HlenL.
        assert(Hpred: exists predMax, maxNbPrepare = S predMax).
        { pose proof maxNbPrepareNotZero. destruct maxNbPrepare; try(lia). exists n0. reflexivity. }
        destruct Hpred as [predMax Hpred]. rewrite Hpred at 1. rewrite Hpred in HlenL. cbn -[maxNbPrepare nullAddr].
        simpl in HlenL. subst offset. unfold nextKSentry in *.
        destruct (lookup (CPaddr (kernel + nextoffset)) (memory s) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-HnextIsPADDR in *.
        destruct (beqAddr nextStructureAddr nullAddr) eqn:HbeqNextNull.
        {
          rewrite <-beqAddrTrue in HbeqNextNull. rewrite HbeqNextNull in *.
          assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
          rewrite HlookupNext in *. exfalso; congruence.
        }
        f_equal. rewrite Hpred. simpl in HlenL. apply completeListOfKernelsAuxN; lia.
      }
      assert(HkernIsConfigK: In kern (completeListOfKernels kernel s)).
      { rewrite HlistEq. simpl. auto. }
      assert(kern <> kernel).
      {
        assert(HnoDup: noDupListOfKerns s) by (unfold deleteProps in *; intuition).
        assert(HkernL1: exists kernL1, isListOfKernelsAux kernL1 (structure pdentryCurr) s
          /\ kernel = last kernL1 (structure pdentryCurr)).
        {
          destruct (beqAddr kernel (structure pdentryCurr)) eqn:HbeqKernStruct.
          - rewrite <-beqAddrTrue in HbeqKernStruct. subst kernel. exists []. simpl. auto.
          - rewrite <-beqAddrFalse in *.
            assert(HkernL1: exists kernL1, isListOfKernelsAux kernL1 (structure pdentryCurr) s
              /\ kernel = last kernL1 (structure pdentryCurr) /\ kernL1 <> []).
            {
              apply inCompleteKernListIsKernListLast with maxNbPrepare currentPart pdentryCurr; trivial.
              + unfold deleteProps in *; intuition.
              + unfold completeListOfKernels in *. destruct (lookup (structure pdentryCurr) (memory s) beqAddr);
                  try(simpl in HkernIsConfig; exfalso; congruence).
                destruct v; try(simpl in HkernIsConfig; exfalso; congruence).
                destruct (indexEq (blockindex b) (CIndex 0)); try(simpl in HkernIsConfig; exfalso; congruence).
                cbn -[maxNbPrepare]. auto.
              + unfold isKS. unfold completeListOfKernels in *.
                destruct (lookup (structure pdentryCurr) (memory s) beqAddr); try(simpl in HkernIsConfig; congruence).
                destruct v; try(simpl in HkernIsConfig; congruence).
                destruct (indexEq (blockindex b) (CIndex 0)) eqn:Hres;
                  try(simpl in HkernIsConfig; exfalso; congruence).
                apply beqIdxTrue in Hres. assumption.
              + unfold completeListOfKernels in *. destruct (lookup (structure pdentryCurr) (memory s) beqAddr);
                  try(simpl in HkernIsConfig; exfalso; congruence).
                destruct v; try(simpl in HkernIsConfig; exfalso; congruence).
                destruct (indexEq (blockindex b) (CIndex 0)); try(simpl in HkernIsConfig; exfalso; congruence).
                cbn -[maxNbPrepare] in HkernIsConfig. destruct HkernIsConfig; try(exfalso; congruence). assumption.
            }
            destruct HkernL1 as [kernL1 (HkernL1 & Hlast1 & _)]. exists kernL1. auto.
        }
        destruct HkernL1 as [kernL1 (HkernL1 & Hlast1)].
        assert(HkernL2: exists kernL2, isListOfKernelsAux kernL2 kernel s /\ kern = last kernL2 kernel
          /\ kernL2 <> []).
        {
          unfold completeListOfKernels in HkernIsConfigNext. destruct (lookup nextStructureAddr (memory s) beqAddr)
            eqn:HlookupNext; try(simpl in HkernIsConfigNext; exfalso; congruence).
          destruct v; try(simpl in HkernIsConfigNext; exfalso; congruence).
          destruct (indexEq (blockindex b) (CIndex 0)) eqn:HeqIdx;
            try(simpl in HkernIsConfigNext; exfalso; congruence). apply beqIdxTrue in HeqIdx.
          cbn -[maxNbPrepare] in HkernIsConfigNext. destruct HkernIsConfigNext as [Heq | HkernIsConfigNext].
          - subst kern. exists [nextStructureAddr]. simpl. subst offset. repeat (split; auto).
            + unfold nextKSentry in *.
              destruct (lookup (CPaddr (kernel + nextoffset)) (memory s) beqAddr); try(exfalso; congruence).
              destruct v; try(exfalso; congruence). rewrite <-HnextIsPADDR. reflexivity.
            + assert(Hres: nextKernelIsValid s) by (unfold deleteProps in *; intuition).
              specialize(Hres currentPart pdentryCurr kernel HcurrIsPart HlookupCurr HkernIsConfig HkernIsKS).
              apply Hres.
            + assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition). intro. subst nextStructureAddr.
              unfold isPADDR in *. rewrite HlookupNext in *. congruence.
            + intro. congruence.
          - assert(HkernL2: exists kernL2, isListOfKernelsAux kernL2 nextStructureAddr s
              /\ kern = last kernL2 nextStructureAddr /\ kernL2 <> []).
            {
              apply inCompleteKernListIsKernListLast with maxNbPrepare currentPart pdentryCurr; trivial.
              - unfold deleteProps in *; intuition.
              - assert(isListOfKernels ((structure pdentryCurr)::kernL1++[nextStructureAddr]) currentPart s).
                {
                  simpl. exists pdentryCurr. repeat (split; trivial).
                  - assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
                    unfold completeListOfKernels in *. intro Hcontra. rewrite Hcontra in *.
                    destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
                    destruct v; simpl in HkernIsConfig; congruence.
                  - apply IL.isListOfKernelsAuxRec with kernel; trivial.
                    + intro Hcontra. assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition).
                      unfold isPADDR in *. rewrite Hcontra in *. rewrite HlookupNext in *. congruence.
                    + subst offset. unfold nextKSentry in *.
                      destruct (lookup (CPaddr (kernel + nextoffset)) (memory s) beqAddr); try(exfalso; congruence).
                      destruct v; try(exfalso; congruence). rewrite <-HnextIsPADDR. reflexivity.
                    + assert(Hres: nextKernelIsValid s) by (unfold deleteProps in *; intuition).
                      specialize(Hres currentPart pdentryCurr kernel HcurrIsPart HlookupCurr HkernIsConfig HkernIsKS).
                      apply Hres.
                }
                apply kernListInclComplete with
                  (structure pdentryCurr::kernL1++[nextStructureAddr]) currentPart; trivial.
                1-2: unfold deleteProps in *; intuition. simpl. right. apply in_or_app. simpl. auto.
              - unfold isKS. rewrite HlookupNext. assumption.
            }
            destruct HkernL2 as [kernL2 (HkernL2 & Hlast2 & HeqList2Nil)]. exists (nextStructureAddr::kernL2).
            split; only 2: split.
            + simpl. repeat (split; trivial).
              * subst offset. unfold nextKSentry in *.
                destruct (lookup (CPaddr (kernel + nextoffset)) (memory s) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). rewrite <-HnextIsPADDR. reflexivity.
              * assert(Hres: nextKernelIsValid s) by (unfold deleteProps in *; intuition).
                specialize(Hres currentPart pdentryCurr kernel HcurrIsPart HlookupCurr HkernIsConfig HkernIsKS).
                apply Hres.
              * assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition). intro. subst nextStructureAddr.
                unfold isPADDR in *. rewrite HlookupNext in *. congruence.
            + apply IL.lastRecInc; assumption.
            + intro. congruence.
        }
        destruct HkernL2 as [kernL2 (HkernL2 & Hlast2 & HeqList2Nil)].
        assert(Hl: isListOfKernels ((structure pdentryCurr)::kernL1 ++ kernL2) currentPart s).
        {
          simpl. exists pdentryCurr. repeat (split; trivial).
          - assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
            unfold completeListOfKernels in *. intro Hcontra. rewrite Hcontra in *.
            destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
            destruct v; simpl in HkernIsConfig; congruence.
          - apply isListOfKernelsAuxRecFull with kernel; assumption.
        }
        specialize(HnoDup currentPart ((structure pdentryCurr)::kernL1 ++ kernL2) HcurrIsPart Hl).
        rewrite app_comm_cons in HnoDup. apply Lib.NoDupSplitInclIff in HnoDup. destruct HnoDup as (_ & Hdisjoint).
        assert(HkernelIn1: In kernel (structure pdentryCurr :: kernL1)).
        {
          destruct kernL1.
          - simpl. simpl in Hlast1. auto.
          - apply IL.lastOfNotEmptyIsIn with nullAddr. apply IL.lastRecInc; assumption.
        }
        specialize(Hdisjoint kernel HkernelIn1). intro. subst kern. contradict Hdisjoint.
        destruct kernL2; try(exfalso; congruence). apply IL.lastOfNotEmptyIsIn with kernel; auto.
      }
      apply HlookupAncEq; assumption.
    }
    repeat (split; trivial).
  + intros kern idx HkernIsConfigNext HltidxStructNb. assert(HkernIsConfigB: In kern (getConfigBlocks currentPart s)).
    {
      rewrite completeKernListIsConfig with (pdentry:=pdentryCurr); trivial.
      2-5: unfold deleteProps in *; intuition. assert(HbeqNextNull: nextStructureAddr <> nullAddr).
      {
        unfold completeListOfKernels in *. assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition).
        unfold isPADDR in *. intro. subst nextStructureAddr.
        destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
        destruct v; simpl in HkernIsConfigNext; congruence.
      }
      specialize(HnextProps HbeqNextNull). destruct HnextProps as (HnextIsKS & HnextIsConfig).
      unfold completeListOfKernels in HkernIsConfigNext.
      destruct (lookup nextStructureAddr (memory s) beqAddr); try(simpl in HkernIsConfigNext; exfalso; congruence).
      destruct v; try(simpl in HkernIsConfigNext; exfalso; congruence).
      destruct (indexEq (blockindex b) (CIndex 0)); try(simpl in HkernIsConfigNext; exfalso; congruence).
      cbn -[maxNbPrepare] in HkernIsConfigNext.
      destruct HkernIsConfigNext as [Heq | HkernIsConfigNext]; try(subst kern; assumption).
      assert(HkernL1: exists kernList, isListOfKernelsAux kernList (structure pdentryCurr) s
        /\ nextStructureAddr = last kernList (structure pdentryCurr)).
      {
        unfold completeListOfKernels in HnextIsConfig. destruct (lookup (structure pdentryCurr) (memory s) beqAddr)
          eqn:HlookupStruct; try(simpl in HnextIsConfig; exfalso; congruence).
        destruct v; try(simpl in HnextIsConfig; exfalso; congruence).
        destruct (indexEq (blockindex b0) (CIndex 0)) eqn:HeqIdx; try(simpl in HnextIsConfig; exfalso; congruence).
        cbn -[maxNbPrepare] in HnextIsConfig. destruct HnextIsConfig as [Heq | HnextIsConfig].
        - subst nextStructureAddr. exists []. simpl. auto.
        - assert(Hres: exists kernList, isListOfKernelsAux kernList (structure pdentryCurr) s
            /\ nextStructureAddr = last kernList (structure pdentryCurr) /\ kernList <> []).
          {
            apply inCompleteKernListIsKernListLast with maxNbPrepare currentPart pdentryCurr; trivial.
            - unfold deleteProps in *; intuition.
            - unfold completeListOfKernels. rewrite HlookupStruct. rewrite HeqIdx. cbn -[maxNbPrepare]. auto.
            - unfold isKS. rewrite HlookupStruct. apply beqIdxTrue in HeqIdx. assumption.
          }
          destruct Hres as [kernL (HkernL & Hlast & _)]. exists kernL. auto.
      }
      destruct HkernL1 as [kernL1 (HkernL1 & Hlast1)].
      assert(HcomplNextIsKL: isListOfKernelsAux (completeListOfKernelsAux maxNbPrepare nextStructureAddr s)
        nextStructureAddr s).
      {
        apply completeKernListIsListOfKernAux with currentPart pdentryCurr; trivial; unfold deleteProps in *;
          intuition.
      }
      assert(isListOfKernels ((structure pdentryCurr)::kernL1
        ++ (completeListOfKernelsAux maxNbPrepare nextStructureAddr s)) currentPart s).
      {
        cbn -[maxNbPrepare nullAddr]. exists pdentryCurr. repeat (split; trivial).
        - assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition). unfold isPADDR in *. intro Hcontra.
          rewrite Hcontra in *. unfold completeListOfKernels in HkernIsConfig.
          destruct (lookup nullAddr (memory s) beqAddr); try(congruence).
          destruct v; simpl in HkernIsConfig; congruence.
        - apply isListOfKernelsAuxRecFull with nextStructureAddr; assumption.
      }
      apply kernListInclComplete with ((structure pdentryCurr)::kernL1
        ++ (completeListOfKernelsAux maxNbPrepare nextStructureAddr s)) currentPart; trivial.
      1-2: unfold deleteProps in *; intuition. cbn -[maxNbPrepare]. right. apply in_or_app. auto.
    }
    apply configBlocksRangesAreEntries; trivial; unfold deleteProps in *; intuition.
Qed.

Lemma deleteSharedBlocksRec currentPart kernel blockTDParent blockToDelete P:
{{ fun s => P s /\ deleteProps s s currentPart blockTDParent blockToDelete
    /\ (exists pdentryCurr, lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)
          /\ kernel = structure pdentryCurr)
    /\ lookup blockToDelete (memory s) beqAddr = None
    /\ In blockTDParent (getMappedBlocks currentPart s)
    /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s
    /\ bentryStartAddr blockTDParent blockToDelete s
    /\ In blockToDelete (getPartitions multiplexer s)
    /\ In currentPart (getPartitions multiplexer s)
    /\ (forall block startBlock endBlock, In block (getMappedBlocks currentPart s)
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockToDelete s
          -> bentryStartAddr block startBlock s
          -> bentryEndAddr block endBlock s
          -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
              -> ~In addr (getPartitions multiplexer s)
                  /\ (forall part, In part (getPartitions multiplexer s)
                      -> ~In addr (filterOptionPaddr (getKSEntries part s))
                          /\ ~In addr (getConfigPaddr part s))
                  /\ (forall child, In child (getChildren currentPart s)
                      -> ~In addr (getMappedPaddr child s))
                  /\ (isBE addr s -> addr + scoffset < endBlock)
                  /\ (isKS addr s -> addr + nextoffset < endBlock)
                  /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+sh1offset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+scoffset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ addr <> nullAddr))
    /\ (forall part, In part (getPartitions multiplexer s) -> In blockToDelete (getChildren part s)
          -> part = currentPart)
    /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
          -> In block (getMappedBlocks part s)
          -> sh1entryPDchild (CPaddr (block+sh1offset)) child s
          -> child <> blockToDelete)
}}
Internal.deleteSharedBlocksRec currentPart kernel blockToDelete
{{ fun _ s => exists pdentryCurr,
  lookup blockToDelete (memory s) beqAddr = None /\ In blockTDParent (getMappedBlocks currentPart s)
  /\ sh1entryPDflag (CPaddr (blockTDParent+sh1offset)) true s
  /\ bentryStartAddr blockTDParent blockToDelete s /\ In blockToDelete (getPartitions multiplexer s)
  /\ In currentPart (getPartitions multiplexer s)
  /\ lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)
  /\ (forall kernBis idx, In kernBis (completeListOfKernels (structure pdentryCurr) s)
      -> idx < kernelStructureEntriesNb
      -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s)
  /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
        -> In block (getMappedBlocks part s)
        -> sh1entryPDchild (CPaddr (block+sh1offset)) child s
        -> child <> blockToDelete)
  /\ (exists s0, P s0 /\ deleteProps s0 s currentPart blockTDParent blockToDelete
      /\ (forall sh1entryaddr child, child <> nullAddr -> sh1entryPDchild sh1entryaddr child s
            -> sh1entryPDchild sh1entryaddr child s0)
      /\ (forall kernBis idx, In kernBis (completeListOfKernels (structure pdentryCurr) s)
            -> idx < kernelStructureEntriesNb
            -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockToDelete s)
      /\ (forall kernBis idx addr, In kernBis (completeListOfKernels (structure pdentryCurr) s)
            -> idx < kernelStructureEntriesNb
            -> sh1entryPDchild (CPaddr (CPaddr (kernBis+idx)+sh1offset)) blockToDelete s0
            -> In addr (getAllPaddrAux [CPaddr (kernBis+idx)] s)
            -> lookup addr (memory s) beqAddr = None))
}}.
Proof.
unfold Internal.deleteSharedBlocksRec. eapply weaken. apply deleteSharedBlocksRecAux. intros s Hprops.
destruct Hprops as (HP & Hcons & [pdentryCurr (HlookupCurr & HkernIsStruct)] & HlookupBTD & HBPMapped & HPDflagBP &
  HstartBP & HBTSIsPart & HcurrIsPart & HpropsAddrsToRemove & HuniqueParent & HBTDNotInElse). exists pdentryCurr.
assert(kernel <> nullAddr -> isKS kernel s /\ In kernel (completeListOfKernels (structure pdentryCurr) s)).
{
  intro HbeqStructNull. assert(HstructIsKS: StructurePointerIsKS s) by (unfold deleteProps in *; intuition).
  subst kernel. specialize(HstructIsKS currentPart pdentryCurr HcurrIsPart HlookupCurr HbeqStructNull).
  split; trivial. unfold completeListOfKernels. unfold isKS in *.
  destruct (lookup (structure pdentryCurr) (memory s) beqAddr); try(exfalso; congruence).
  destruct v; try(exfalso; congruence). rewrite HstructIsKS. rewrite IL.indexEqRefl. cbn -[maxNbPrepare]. auto.
}
assert(forall kernBis blockIdx, In kernBis (completeListOfKernels kernel s)
  -> blockIdx < kernelStructureEntriesNb
  -> In (CPaddr (kernBis + blockIdx)) (filterOptionPaddr (getKSEntries currentPart s))).
{
  intros kern idx HkernIsConfig HltIdxStructNb. assert(In kern (getConfigBlocks currentPart s)).
  {
    subst kernel. rewrite completeKernListIsConfig with (pdentry:=pdentryCurr); trivial; unfold deleteProps in *;
      intuition.
  }
  apply configBlocksRangesAreEntries; trivial; unfold deleteProps in *; intuition.
}
repeat (split; trivial). exists s. repeat (split; trivial). exists []. cbn -[maxNbPrepare kernelStructureEntriesNb].
repeat (split; auto).
- unfold N. pose proof maxNbPrepareNbLessThanMaxIdx. rewrite <-maxIdxEqualMaxAddr. lia.
- intros; exfalso; congruence.
Qed.

Lemma deletePartition idPDchildToDelete:
{{fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}
deletePartition idPDchildToDelete
{{fun _ s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s /\ consistency s }}.
Proof.
unfold deletePartition. eapply bindRev.
{ (** MAL.getCurPartition **)
  eapply weaken. apply getCurPartition. intros s Hprops. apply Hprops.
}
intro currentPart. eapply bindRev.
{ (** Internal.findBlockInKSWithAddr **)
  eapply weaken. apply findBlockInKSWithAddr. intros s Hprops. simpl.
  destruct Hprops as (Hprops & Hcurr). assert(In currentPart (getPartitions multiplexer s)).
  { subst currentPart. unfold consistency in *; unfold consistency1 in *; intuition. }
  assert(isPDT currentPart s).
  { apply IL.partitionsArePDT; trivial; unfold consistency in *; unfold consistency1 in *; intuition. }
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ currentPart = currentPartition s /\ isPDT currentPart s /\ In currentPart (getPartitions multiplexer s)).
  intuition.
}
intro blockToDeleteInCurrPartAddr. eapply bindRev.
{ (** Internal.compareAddrToNull **)
  eapply weaken. apply compareAddrToNull. intros s Hprops. apply Hprops.
}
intro addrIsNull. destruct addrIsNull.
{ (* case addrIsNull = true *)
  eapply weaken. apply WP.ret. intros s Hprops. intuition.
}
(* case addrIsNull = false *)
eapply bindRev.
{ (** MAL.readSh1PDFlagFromBlockEntryAddr **)
  eapply weaken. apply readSh1PDFlagFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as (((HPI & HKDI & HVS & Hcurr & HcurrIsPDT & HcurrIsPart) & Hconsist & HpropsOr) & HbeqNullBTD).
  rewrite <-beqAddrFalse in HbeqNullBTD. destruct HpropsOr as
    [Hcontra | [bentry (HlookupBTD & HblocksEq & HPflagBTD & HBTDMapped)]]; try(exfalso; congruence).
  instantiate(1 := fun s => partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ consistency s /\ currentPart = currentPartition s /\ isPDT currentPart s
    /\ In currentPart (getPartitions multiplexer s)
    /\ blockToDeleteInCurrPartAddr = idPDchildToDelete
    /\ bentryPFlag blockToDeleteInCurrPartAddr true s
    /\ In blockToDeleteInCurrPartAddr (getMappedBlocks currentPart s)
    /\ blockToDeleteInCurrPartAddr <> nullAddr).
  split. intuition. split; trivial. exists bentry. assumption.
}
intro isChild. destruct (negb isChild) eqn:HneqChild.
{ (* case isChild = false *)
  eapply weaken. apply WP.ret. intros s Hprops. simpl. intuition.
}
(* case isChild = true *)
apply negb_false_iff in HneqChild. subst isChild. eapply bindRev.
{ (** MAL.readBlockStartFromBlockEntryAddr **)
  eapply weaken. apply readBlockStartFromBlockEntryAddr. intros s Hprops. split. apply Hprops.
  destruct Hprops as ((_ & _ & _ & _ & _ & _ & _ & _ & HPflag & _) & _). unfold bentryPFlag in *. unfold isBE.
  destruct (lookup blockToDeleteInCurrPartAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  trivial.
}
intro blockStartAddr. eapply bindRev.
{ (** MAL.readBlockEndFromBlockEntryAddr **)
  eapply weaken. apply readBlockEndFromBlockEntryAddr. intros s Hprops. split. apply Hprops.
  destruct Hprops as (_ & Hstart). unfold bentryStartAddr in *. unfold isBE.
  destruct (lookup blockToDeleteInCurrPartAddr (memory s) beqAddr); try(congruence). destruct v; try(congruence).
  trivial.
}
intro blockEndAddr. eapply bindRev.
{ (** MAL.eraseBlock **)
  eapply weaken. apply eraseBlock. intros s Hprops. apply Hprops.
}
intro eraseSucc. eapply bindRev.
{ (** MAL.readPDStructurePointer **)
  eapply weaken. apply readPDStructurePointer. intros s Hprops. simpl.
  destruct Hprops as [s0 (((((HPIs0 & HKDIs0 & HVSs0 & Hconsists0 & Hcurr & HcurrIsPDT & HcurrIsPart & HblocksEq &
    HPflagBTDs0 & HBTDMapped & HbeqBTDNull) & [_ [sh1entryaddr (_ & HPDflag & Hsh1)]]) & HstartBTDs0) & HendBTDs0) &
    HcurrEq & HlookupRange & HlookupNotRange & _)].
  assert(HBTDIsBE: isBE blockToDeleteInCurrPartAddr s0).
  {
    unfold isBE. unfold bentryPFlag in *.
    destruct (lookup blockToDeleteInCurrPartAddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    trivial.
  }
  unfold sh1entryAddr in *.
  destruct (lookup blockToDeleteInCurrPartAddr (memory s0) beqAddr) eqn:HlookupBTD; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). subst sh1entryaddr.
  assert(HPDchild: sh1entryPDchild (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) nullAddr s0).
  {
    assert(Hres: PDflagMeansNoChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    specialize(Hres blockToDeleteInCurrPartAddr HBTDIsBE HPDflag). assumption.
  }
  assert(HisPDT: PDTIfPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  assert(HcheckChild:
    true = checkChild blockToDeleteInCurrPartAddr s0 (CPaddr (blockToDeleteInCurrPartAddr+sh1offset))
    /\ sh1entryAddr blockToDeleteInCurrPartAddr (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) s0).
  {
    unfold checkChild. unfold sh1entryAddr. rewrite HlookupBTD. split; trivial. unfold sh1entryPDflag in *.
    destruct (lookup (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). auto.
  }
  assert(HcurrIsParts0: In currentPart (getPartitions multiplexer s0)).
  {
    subst currentPart. unfold consistency in *; unfold consistency1 in *; intuition.
  }
  specialize(HisPDT blockToDeleteInCurrPartAddr (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) currentPart
    HcurrIsParts0 HBTDMapped HcheckChild).
  destruct HisPDT as (HAflagBTDs0 & _ & [startBTDBis (HstartBTDs0Bis & HisPDT)]).
  assert(startBTDBis = blockStartAddr).
  {
    unfold bentryStartAddr in *. rewrite HlookupBTD in *. rewrite <-HstartBTDs0 in *. assumption.
  }
  subst startBTDBis. clear HstartBTDs0Bis. assert(HstartIsPDT: isPDT blockStartAddr s0).
  {
    unfold entryPDT in *. unfold isPDT. unfold bentryStartAddr in *. rewrite HlookupBTD in *.
    rewrite <-HstartBTDs0 in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). trivial.
  }
  assert(HrangeWereNone: forall addr, In addr (getAllPaddrBlock blockStartAddr blockEndAddr) -> addr <> blockStartAddr
    -> lookup addr (memory s0) beqAddr = None).
  {
    intros addr HaddrInRange HbeqAddrStart.
    assert(Htypes: blocksAddressesTypes s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    assert(Hloc: sh1entryInChildLocationWeak (CPaddr (blockToDeleteInCurrPartAddr + sh1offset)) nullAddr s0).
    {
      assert(HnullEquiv: childBlockNullIfChildNull s0)
        by (unfold consistency in *; unfold consistency1 in *; intuition). destruct HcheckChild as (_ & Hsh1).
      specialize(HnullEquiv currentPart blockToDeleteInCurrPartAddr (CPaddr (blockToDeleteInCurrPartAddr+sh1offset))
        HcurrIsParts0 HBTDMapped Hsh1 HPDchild). unfold sh1entryInChildLocation in *.
      unfold sh1entryInChildLocationWeak.
      destruct (lookup (CPaddr (blockToDeleteInCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; try(congruence). destruct HnullEquiv. assumption.
    }
    specialize(Htypes blockToDeleteInCurrPartAddr blockStartAddr blockEndAddr currentPart HcurrIsParts0 HBTDMapped
      HstartBTDs0 HendBTDs0 Hloc). destruct Htypes as [(Hcontra & _) | [(_ & Hres) | Hcontra]].
    - unfold isKS in *. unfold isPDT in *. exfalso.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    - apply Hres; auto.
    - (*false, but quicker to prove this way*) apply Hcontra; assumption.
  }
  assert(HlookupsEq: forall addr, addr <> blockStartAddr
    -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr).
  {
    intros addr HbeqAddrStart. assert(HpropsOr: In addr (getAllPaddrBlock blockStartAddr blockEndAddr)
      \/ ~In addr (getAllPaddrBlock blockStartAddr blockEndAddr)) by (apply Classical_Prop.classic).
    destruct HpropsOr.
    - rewrite HrangeWereNone; trivial. apply HlookupRange; assumption.
    - apply HlookupNotRange; assumption.
  }
  assert(Hwell: wellFormedBlock s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  specialize(Hwell blockToDeleteInCurrPartAddr blockStartAddr blockEndAddr HPflagBTDs0 HstartBTDs0 HendBTDs0).
  destruct Hwell as (Hwell & _). assert(HlookupStarts: lookup blockStartAddr (memory s) beqAddr = None).
  {
    apply HlookupRange. apply IL.getAllPaddrBlockIncl; lia.
  }
  assert(blockToDeleteInCurrPartAddr <> blockStartAddr).
  { intro. subst blockStartAddr. unfold isPDT in *. rewrite HlookupBTD in *. congruence. }
  assert(HlookupBTDEq: lookup blockToDeleteInCurrPartAddr (memory s) beqAddr
    = lookup blockToDeleteInCurrPartAddr (memory s0) beqAddr).
  { apply HlookupsEq; assumption. }
  assert(CPaddr (blockToDeleteInCurrPartAddr+sh1offset) <> blockStartAddr).
  {
    intro. subst blockStartAddr. unfold isPDT in *. unfold sh1entryPDchild in *.
    destruct (lookup (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
  }
  assert(HlookupBTDSh1Eq: lookup (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) (memory s) beqAddr
    = lookup (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) (memory s0) beqAddr).
  { apply HlookupsEq; assumption. }
  assert(HstartIsChilds0: In blockStartAddr (getChildren currentPart s0)).
  {
    apply PDflagImpliesChild with blockToDeleteInCurrPartAddr; trivial;
      unfold consistency in *; unfold consistency1 in *; intuition.
  }
  assert(HcurrIsParent: isParent s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
  specialize(HcurrIsParent blockStartAddr currentPart HcurrIsParts0 HstartIsChilds0).

  assert(nullAddrExists s).
  { (* BEGIN nullAddrExists s *)
    assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold nullAddrExists in *. unfold isPADDR in *. rewrite HlookupsEq; trivial. unfold isPDT in *. intro.
    subst blockStartAddr. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END nullAddrExists *)
  }
  assert(wellFormedFstShadowIfBlockEntry s).
  { (* BEGIN wellFormedFstShadowIfBlockEntry s *)
    assert(Hcons0: wellFormedFstShadowIfBlockEntry s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block HblockIsBE. unfold isBE in *. assert(block <> blockStartAddr).
    {
      intro. subst blockStartAddr. rewrite HlookupStarts in *. congruence.
    }
    rewrite HlookupsEq in HblockIsBE; trivial. unfold isSHE. specialize(Hcons0 block HblockIsBE).
    rewrite HlookupsEq; trivial. unfold isSHE in *. intro. subst blockStartAddr. unfold isPDT in *.
    destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END wellFormedFstShadowIfBlockEntry *)
  }
  (* PDTIfPDFlag s false *)
  assert(AccessibleNoPDFlag s).
  { (* BEGIN AccessibleNoPDFlag s *)
    assert(Hcons0: AccessibleNoPDFlag s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros block sh1entryaddrBis HblockIsBE Hsh1Bis HAFlag. unfold isBE in *. unfold sh1entryAddr in *.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    {
      apply HlookupsEq. intro. subst blockStartAddr. rewrite HlookupStarts in *. congruence.
    }
    unfold bentryAFlag in *. rewrite HlookupBlockEq in *.
    specialize(Hcons0 block sh1entryaddrBis HblockIsBE Hsh1Bis HAFlag). unfold sh1entryPDflag in *.
    rewrite HlookupsEq; trivial. intro. subst blockStartAddr. unfold isPDT in *.
    destruct (lookup sh1entryaddrBis (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END AccessibleNoPDFlag *)
  }
  assert(HgetPartsImpl: forall part, In part (getPartitions multiplexer s) -> In part (getPartitions multiplexer s0)).
  { intro part. apply getPartitionsImplRemoveAddr with blockStartAddr; trivial. }
  assert(FirstFreeSlotPointerIsBEAndFreeSlot s).
  { (* BEGIN FirstFreeSlotPointerIsBEAndFreeSlot s *)
    assert(Hcons0: FirstFreeSlotPointerIsBEAndFreeSlot s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros partition pdentry HlookupPart HpartIsPart HbeqFirstNull. apply HgetPartsImpl in HpartIsPart.
    rewrite HlookupsEq in HlookupPart; try(intro; subst blockStartAddr; congruence).
    specialize(Hcons0 partition pdentry HlookupPart HpartIsPart HbeqFirstNull). unfold isBE. unfold isFreeSlot in *.
    destruct Hcons0 as (HfirstIsBE & HfirstFree).
    assert(HlookupFirstEq: lookup (firstfreeslot pdentry) (memory s) beqAddr
      = lookup (firstfreeslot pdentry) (memory s0) beqAddr).
    {
      apply HlookupsEq. intro. subst blockStartAddr. unfold isPDT in *.
      destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupFirstEq. split; trivial.
    destruct (lookup (firstfreeslot pdentry) (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    assert(HlookupFirstSh1Eq: lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s) beqAddr
      = lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr).
    {
      apply HlookupsEq. intro. subst blockStartAddr. unfold isPDT in *.
      destruct (lookup (CPaddr (firstfreeslot pdentry+sh1offset)) (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite HlookupFirstSh1Eq.
    destruct (lookup (CPaddr (firstfreeslot pdentry + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). rewrite HlookupsEq; trivial. intro. subst blockStartAddr. unfold isPDT in *.
    destruct (lookup (CPaddr (firstfreeslot pdentry+scoffset)) (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
    (* END FirstFreeSlotPointerIsBEAndFreeSlot *)
  }
  unfold pdentryParent in *.
  destruct (lookup blockStartAddr (memory s0) beqAddr) eqn:HlookupStart; try(exfalso; congruence).
  destruct v; try(exfalso; congruence).
  assert(multiplexerIsPDT s).
  { (* BEGIN multiplexerIsPDT s *)
    unfold multiplexerIsPDT. unfold isPDT. rewrite HlookupsEq.
    unfold consistency in *; unfold consistency1 in *; intuition. unfold multiplexer. intro Hcontra.
    assert(HparentOfPart: parentOfPartitionIsPartition s0)
      by (unfold consistency in *; unfold consistency1 in *; intuition). apply eq_sym in Hcontra.
    specialize(HparentOfPart blockStartAddr p HlookupStart). destruct HparentOfPart as (_ & HparentOfRoot & _).
    specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *. rewrite HcurrIsParent in *. unfold isPDT in *.
    assert(isPADDR nullAddr s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    unfold isPADDR in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END multiplexerIsPDT *)
  }
  unfold consistency in *; unfold consistency1 in *; unfold consistency2 in *.
  assert(HgetKSEq: forall part, part <> blockStartAddr -> getKSEntries part s = getKSEntries part s0).
  { intros part HbeqPartStart. apply getKSEntriesEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetMappedBEq: forall part, part <> blockStartAddr -> getMappedBlocks part s = getMappedBlocks part s0).
  { intros part HbeqPartStart. apply getMappedBlocksEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetMappedPEq: forall part, part <> blockStartAddr -> getMappedPaddr part s = getMappedPaddr part s0).
  { intros part HbeqPartStart. apply getMappedPaddrEqRemoveAddr with blockStartAddr; trivial. }
  assert(HAccgetMappedBEq: forall part, part <> blockStartAddr
    -> getAccessibleMappedBlocks part s = getAccessibleMappedBlocks part s0).
  { intros part HbeqPartStart. apply getAccessibleMappedBlocksEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetAccMappedPEq: forall part, part <> blockStartAddr
    -> getAccessibleMappedPaddr part s = getAccessibleMappedPaddr part s0).
  { intros part HbeqPartStart. apply getAccessibleMappedPaddrEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetConfigBEq: forall part, part <> blockStartAddr -> getConfigBlocks part s = getConfigBlocks part s0).
  { intros part HbeqPartStart. apply getConfigBlocksEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetConfigEq: forall part, part <> blockStartAddr -> getConfigPaddr part s = getConfigPaddr part s0).
  { intros part HbeqPartStart. apply getConfigPaddrEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetChildrenEqNotStart: forall part, part <> blockStartAddr -> getChildren part s = getChildren part s0).
  { intros part HbeqPartStart. apply getChildrenEqRemoveAddr with blockStartAddr; trivial. }
  assert(HgetChildrenImpl: forall part partBase, In part (getChildren partBase s)
    -> In part (getChildren partBase s0)).
  { intros part partBase. apply getChildrenImplRemoveAddr with blockStartAddr; trivial. }
  assert(HgetPartsImplRev: forall part, In part (getPartitions multiplexer s0)
     -> In part (getPartitions multiplexer s) \/ In part (getPartitions blockStartAddr s0)).
  { intro part. apply getPartitionsImplRemoveAddrRev; trivial. }
  assert(HgetFreeEq: forall part, part <> blockStartAddr -> getFreeSlotsList part s = getFreeSlotsList part s0).
  { intro part. apply getFreeSlotsListEqRemoveAddr; trivial. }
  assert(HcurrNotInDesc: ~In currentPart (getPartitions blockStartAddr s0)).
  {
    assert(HpartNoDup: NoDup (getPartitions currentPart s0)).
    { apply noDupPartitionTreeExt; trivial; intuition. }
    assert(Hlen: length (getPartitions currentPart s0) <= maxAddr+1).
    { apply IL.lengthNoDupPartitions; trivial. }
    assert(NoDup (getPartitions blockStartAddr s0)).
    {
      unfold getPartitions in *. apply noDupPartitionTreeExtAux with currentPart; trivial.
      - lia.
      - replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. right.
        induction (getChildren currentPart s0); simpl in *; try(congruence). apply in_or_app.
        destruct HstartIsChilds0 as [Heq | HstartIsChilds0]; try(right; apply IHl; assumption). subst a. left.
        rewrite PeanoNat.Nat.add_1_r. simpl. auto.
    }
    unfold getPartitions. unfold getPartitions in HpartNoDup. unfold getPartitions in Hlen.
    replace (maxAddr+2) with (S (maxAddr+1)) in *; try(lia). simpl in HpartNoDup. apply NoDup_cons_iff in HpartNoDup.
    destruct HpartNoDup as (HpartNotIn & _).
    assert(Hres: ~In currentPart (getPartitionsAux (maxAddr+1) blockStartAddr s0)).
    {
      induction (getChildren currentPart s0); simpl in *; try(exfalso; congruence).
      apply Lib.in_app_or_neg in HpartNotIn. destruct HpartNotIn as (HcurrNotInA & HcurrNotIn).
      destruct HstartIsChilds0 as [Heq | HstartIsChilds0]; try(apply IHl; assumption). subst a. assumption.
    }
    assert(HlenRec: length (flat_map (fun p : paddr => getPartitionsAux (maxAddr + 1) p s0)
      (getChildren currentPart s0)) <= maxAddr).
    { simpl in Hlen. lia. }
    rewrite getPartitionsEnd; trivial. clear HpartNotIn. clear Hlen.
    induction (getChildren currentPart s0); simpl in *; try(exfalso; congruence). rewrite length_app in HlenRec.
    assert(HnewLen: length (flat_map (fun p : paddr => getPartitionsAux (maxAddr + 1) p s0) l) <= maxAddr) by lia.
    destruct HstartIsChilds0 as [Heq | HstartIsChilds0]; try(apply IHl; assumption). subst a. lia.
  }
  assert(HstartIsParts0: In blockStartAddr (getPartitions multiplexer s0)).
  {
    apply IL.childrenPartitionInPartitionList with currentPart; trivial; intuition.
  }

  assert(currentPartitionInPartitionsList s).
  { (* BEGIN currentPartitionInPartitionsList s *)
    assert(Hcons0: currentPartitionInPartitionsList s0) by intuition. unfold currentPartitionInPartitionsList in *.
    rewrite HcurrEq. apply HgetPartsImplRev in Hcons0. rewrite <-Hcurr in *.
    destruct Hcons0; try(exfalso; congruence). assumption.
    (* END currentPartitionInPartitionsList *)
  }
  assert(wellFormedShadowCutIfBlockEntry s).
  { (* BEGIN wellFormedShadowCutIfBlockEntry s *)
    assert(Hcons0: wellFormedShadowCutIfBlockEntry s0) by intuition.
    intros block HblockIsBE. unfold isBE in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. specialize(Hcons0 block HblockIsBE).
    destruct Hcons0 as [scentryaddr (HsceIsSCE & Hsce)]. exists scentryaddr. unfold isSCE in *.
    rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END wellFormedShadowCutIfBlockEntry *)
  }
  assert(BlocksRangeFromKernelStartIsBE s).
  { (* BEGIN BlocksRangeFromKernelStartIsBE s *)
    assert(Hcons0: BlocksRangeFromKernelStartIsBE s0) by intuition. intros kernel blockidx HkernIsKS Hblockidx.
    unfold isKS in *. assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. specialize(Hcons0 kernel blockidx HkernIsKS Hblockidx).
    unfold isBE in *. rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END BlocksRangeFromKernelStartIsBE *)
  }
  assert(KernelStructureStartFromBlockEntryAddrIsKS s).
  { (* BEGIN KernelStructureStartFromBlockEntryAddrIsKS s*)
    assert(Hcons0: KernelStructureStartFromBlockEntryAddrIsKS s0) by intuition.
    intros block blockidx HblockIsBE Hblockidx. unfold isBE in *. unfold bentryBlockIndex in *.
    assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. rewrite HlookupsEq in Hblockidx; trivial.
    specialize(Hcons0 block blockidx HblockIsBE Hblockidx). unfold isKS in *. rewrite HlookupsEq; auto. intro Hcontra.
    rewrite Hcontra in *. unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
    (* END KernelStructureStartFromBlockEntryAddrIsKS *)
  }
  assert(sh1InChildLocationIsBE s).
  { (* BEGIN sh1InChildLocationIsBE s*)
    assert(Hcons0: sh1InChildLocationIsBE s0) by intuition.
    intros part block sh1entryaddrBis sh1entryBis HpartIsPart HblockMapped Hsh1 HlookupSh1Bis HbeqInChildNull.
    apply HgetPartsImpl in HpartIsPart. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. assert(sh1entryaddrBis <> blockStartAddr).
    { intro. subst sh1entryaddrBis. congruence. }
    rewrite HlookupsEq in HlookupSh1Bis; trivial.
    specialize(Hcons0 part block sh1entryaddrBis sh1entryBis HpartIsPart HblockMapped Hsh1 HlookupSh1Bis
      HbeqInChildNull). unfold isBE in *.
    rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END sh1InChildLocationIsBE *)
  }
  assert(StructurePointerIsKS s).
  { (* BEGIN StructurePointerIsKS s *)
    assert(Hcons0: StructurePointerIsKS s0) by intuition.
    intros partition pdentry HpartIsPart HlookupPart HbeqStructNull. apply HgetPartsImpl in HpartIsPart.
    assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HlookupPart; trivial.
    specialize(Hcons0 partition pdentry HpartIsPart HlookupPart HbeqStructNull).
    unfold isKS in *. rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END StructurePointerIsKS *)
  }
  assert(NextKSIsKS s).
  { (* BEGIN NextKSIsKS s *)
    assert(Hcons0: NextKSIsKS s0) by intuition.
    intros kernel nextKSaddr nextKS HkernIsKS HnextKSAddr HnextKS HbeqNextNull.
    unfold isKS in *. unfold nextKSAddr in *. assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. rewrite HlookupsEq in HnextKSAddr; trivial.
    unfold nextKSentry in *. assert(nextKSaddr <> blockStartAddr).
    { intro. subst nextKSaddr. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HnextKS; trivial.
    specialize(Hcons0 kernel nextKSaddr nextKS HkernIsKS HnextKSAddr HnextKS HbeqNextNull). rewrite HlookupsEq; auto.
    intro Hcontra. rewrite Hcontra in *. unfold isPDT in *. unfold isKS in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END NextKSIsKS *)
  }
  assert(NextKSOffsetIsPADDR s).
  { (* BEGIN NextKSOffsetIsPADDR s *)
    assert(Hcons0: NextKSOffsetIsPADDR s0) by intuition. intros kern nextksaddr HkernIsKS HnextIsNext.
    unfold isKS in *. unfold nextKSAddr in *. assert(kern <> blockStartAddr).
    { intro. subst kern. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. rewrite HlookupsEq in HnextIsNext; trivial.
    specialize(Hcons0 kern nextksaddr HkernIsKS HnextIsNext). destruct Hcons0 as (Hcons0 & HbeqNextNull).
    split; trivial. unfold isPADDR in *. rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *.
    unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END NextKSOffsetIsPADDR *)
  }
  assert(NoDupInFreeSlotsList s).
  { (* BEGIN NoDupInFreeSlotsList s *)
    assert(Hcons0: NoDupInFreeSlotsList s0) by intuition. intros partition HpartIsPart.
    apply HgetPartsImpl in HpartIsPart. specialize(Hcons0 partition HpartIsPart).
    destruct (beqAddr partition blockStartAddr) eqn:HbeqPartStart.
    - rewrite <-beqAddrTrue in HbeqPartStart. subst partition. unfold getFreeSlotsList. rewrite HlookupStarts.
      exists []. simpl. split; trivial. split; only 2: apply NoDup_nil. intro Hcontra. rewrite <-Hcontra. trivial.
    - rewrite <-beqAddrFalse in *. rewrite HgetFreeEq; trivial.
    (* END NoDupInFreeSlotsList *)
  }
  assert(freeSlotsListIsFreeSlot s).
  { (* BEGIN freeSlotsListIsFreeSlot s *)
    assert(Hcons0: freeSlotsListIsFreeSlot s0) by intuition.
    intros partition freeslot optionfreeslotslist freeslotslist HpartIsPDT HpartIsPart Hoption HslotsList
      HbeqFreeNull. apply HgetPartsImpl in HpartIsPart. unfold isPDT in *. assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HpartIsPDT; trivial. rewrite HgetFreeEq in Hoption; trivial.
    specialize(Hcons0 partition freeslot optionfreeslotslist freeslotslist HpartIsPDT HpartIsPart Hoption HslotsList
      HbeqFreeNull). unfold isFreeSlot in *. assert(freeslot <> blockStartAddr).
    {
      intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; trivial.
    destruct (lookup freeslot (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    assert(CPaddr (freeslot+sh1offset) <> blockStartAddr).
    {
      intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; trivial. destruct (lookup (CPaddr (freeslot+sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). rewrite HlookupsEq; auto. intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END freeSlotsListIsFreeSlot *)
  }
  assert(DisjointFreeSlotsLists s).
  { (* BEGIN DisjointFreeSlotsLists s *)
    assert(Hcons0: DisjointFreeSlotsLists s0) by intuition.
    intros part1 part2 Hpart1IsPart Hpart2IsPart HbeqPart1Part2. apply HgetPartsImpl in Hpart1IsPart.
    assert(HnoDupFree: NoDupInFreeSlotsList s0) by intuition.
    apply HgetPartsImpl in Hpart2IsPart. destruct (beqAddr part1 blockStartAddr) eqn:HbeqPart1Start.
    - rewrite <-beqAddrTrue in HbeqPart1Start. subst part1. unfold getFreeSlotsList at 1. rewrite HlookupStarts.
      exists []. rewrite HgetFreeEq; auto. specialize(HnoDupFree part2 Hpart2IsPart).
      destruct HnoDupFree as [optFreeL (HoptFree & HwellFOpt & _)]. exists optFreeL. unfold Lib.disjoint. simpl.
      split; trivial. split; auto. intro Hcontra. rewrite <-Hcontra. trivial.
    - rewrite <-beqAddrFalse in *. rewrite HgetFreeEq; trivial.
      destruct (beqAddr part2 blockStartAddr) eqn:HbeqPart2Start.
      + rewrite <-beqAddrTrue in HbeqPart2Start. subst part2. unfold getFreeSlotsList at 2. rewrite HlookupStarts.
        specialize(HnoDupFree part1 Hpart1IsPart). destruct HnoDupFree as [optFreeL (HoptFree & HwellFOpt & _)].
        exists optFreeL. exists []. unfold Lib.disjoint. simpl. split; trivial. split; trivial. split; trivial.
        split; auto. intro Hcontra. rewrite <-Hcontra. trivial.
      + rewrite <-beqAddrFalse in *. rewrite HgetFreeEq; trivial.
        specialize(Hcons0 part1 part2 Hpart1IsPart Hpart2IsPart HbeqPart1Part2). assumption.
    (* END DisjointFreeSlotsLists *)
  }
  assert(inclFreeSlotsBlockEntries s).
  { (* BEGIN inclFreeSlotsBlockEntries s *)
    assert(Hcons0: inclFreeSlotsBlockEntries s0) by intuition. intros partition HpartIsPart.
    apply HgetPartsImpl in HpartIsPart. specialize(Hcons0 partition HpartIsPart).
    destruct (beqAddr partition blockStartAddr) eqn:HbeqPartStart.
    - rewrite <-beqAddrTrue in HbeqPartStart. subst partition. unfold getFreeSlotsList. unfold getKSEntries.
      rewrite HlookupStarts. unfold incl. simpl. auto.
    - rewrite <-beqAddrFalse in *. rewrite HgetFreeEq; trivial. rewrite HgetKSEq; trivial.
    (* END inclFreeSlotsBlockEntries *)
  }
  assert(DisjointKSEntries s).
  { (* BEGIN DisjointKSEntries s *)
    assert(Hcons0: DisjointKSEntries s0) by intuition.
    intros part1 part2 Hpart1IsPart Hpart2IsPart HbeqPart1Part2.
    destruct (beqAddr part1 blockStartAddr) eqn:HbeqPart1Start.
    - rewrite <-beqAddrTrue in HbeqPart1Start. subst part1. exists []. exists (getKSEntries part2 s).
      unfold getKSEntries at 1. rewrite HlookupStarts. unfold Lib.disjoint. auto.
    - destruct (beqAddr part2 blockStartAddr) eqn:HbeqPart2Start.
      + rewrite <-beqAddrTrue in HbeqPart2Start. subst part2. exists (getKSEntries part1 s). exists [].
        unfold getKSEntries at 3. rewrite HlookupStarts. unfold Lib.disjoint. auto.
      + rewrite <-beqAddrFalse in *. apply HgetPartsImpl in Hpart1IsPart. apply HgetPartsImpl in Hpart2IsPart.
        specialize(Hcons0 part1 part2 Hpart1IsPart Hpart2IsPart HbeqPart1Part2). rewrite HgetKSEq; trivial.
        rewrite HgetKSEq; trivial.
    (* END DisjointKSEntries *)
  }
  assert(noDupPartitionTree s).
  { (* BEGIN noDupPartitionTree s *)
    assert(Hcons0: noDupPartitionTree s0) by intuition. unfold noDupPartitionTree in *.
    apply noDupGetPartitionsEqRemoveAddr with s0 blockStartAddr; trivial.
    (* END noDupPartitionTree *)
  }
  assert(HpartialIsParent: forall partition pdparent, partition <> blockStartAddr
    -> In pdparent (getPartitions multiplexer s) -> In partition (getChildren pdparent s)
    -> pdentryParent partition pdparent s).
  { (* BEGIN partial isParent s *)
    assert(Hcons0: isParent s0) by intuition. intros partition pdparent HbeqPartStart HparentIsPart HpartIsChild.
    apply HgetPartsImpl in HparentIsPart. assert(pdparent <> blockStartAddr).
    {
      assert(isPDT pdparent s).
      {
        unfold getChildren in *. unfold isPDT.
        destruct (lookup pdparent (memory s) beqAddr); try(simpl in *; congruence).
        destruct v; try(simpl in *; congruence). trivial.
      }
      intro. subst pdparent. unfold isPDT in *. rewrite HlookupStarts in *. congruence.
    }
    rewrite HgetChildrenEqNotStart in HpartIsChild; trivial.
    specialize(Hcons0 partition pdparent HparentIsPart HpartIsChild). unfold pdentryParent.
    rewrite HlookupsEq; trivial.
    (* END partial isParent *)
  }
  assert(isChild s).
  { (* BEGIN isChild s *)
    assert(Hcons0: isChild s0) by intuition. intros partition pdparent HpartIsPart HparentIsParent.
    unfold pdentryParent in *. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    rewrite HlookupsEq in HparentIsParent; trivial. apply HgetPartsImpl in HpartIsPart. intro HbeqPartRoot.
    specialize(Hcons0 partition pdparent HpartIsPart HparentIsParent HbeqPartRoot).
    assert(pdparent <> blockStartAddr).
    {
      intro. subst pdparent. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    rewrite HgetChildrenEqNotStart; assumption.
    (* END isChild *)
  }
  assert(noDupKSEntriesList s).
  { (* BEGIN noDupKSEntriesList s *)
    assert(Hcons0: noDupKSEntriesList s0) by intuition. intros partition HpartIsPart.
    apply HgetPartsImpl in HpartIsPart. destruct (beqAddr partition blockStartAddr) eqn:HbeqPartStart.
    - rewrite <-beqAddrTrue in HbeqPartStart. subst partition. unfold getKSEntries. rewrite HlookupStarts. simpl.
      apply NoDup_nil.
    - rewrite <-beqAddrFalse in *. specialize(Hcons0 partition HpartIsPart). rewrite HgetKSEq; assumption.
    (* END noDupKSEntriesList *)
  }
  assert(wellFormedBlock s).
  { (* BEGIN wellFormedBlock s *)
    assert(Hcons0: wellFormedBlock s0) by intuition. intros block startaddr endaddr HPFlag Hstart Hend.
    unfold bentryPFlag in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    assert(HbeqBlockStart: block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    specialize(HlookupsEq block HbeqBlockStart). rewrite HlookupsEq in *.
    specialize(Hcons0 block startaddr endaddr HPFlag Hstart Hend). assumption.
    (* END wellFormedBlock *)
  }
  assert(HbelowStartParts: forall oldPart, In oldPart (getPartitions blockStartAddr s0)
    -> oldPart <> blockStartAddr
    -> ~In oldPart (getPartitions multiplexer s)).
  {
    intros oldPart HoldIsOldPart HbeqOldStart. apply oldPartsRemoveAddr with s0 blockStartAddr; trivial.
    intuition.
  }
  assert(HpartialParentOfPartIsPart: forall partition entry,
    lookup partition (memory s) beqAddr = Some (PDT entry)
    -> (~In (parent entry) (getPartitions blockStartAddr s0)
        -> partition <> constantRootPartM
        -> (exists parentEntry, lookup (parent entry) (memory s) beqAddr = Some (PDT parentEntry))
            /\ In (parent entry) (getPartitions multiplexer s))
      /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition).
  { (* BEGIN partial parentOfPartitionIsPartition s *)
    assert(Hcons0: parentOfPartitionIsPartition s0) by intuition.
    intros partition pdentry HlookupPart. assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HlookupPart; trivial. specialize(Hcons0 partition pdentry HlookupPart).
    destruct Hcons0 as (HparentIsPart & HparentProps). split; trivial. intros HparentNotInSub HbeqPartRoot.
    specialize(HparentIsPart HbeqPartRoot). destruct HparentIsPart as (HlookupParent & HparentIsPart).
    apply HgetPartsImplRev in HparentIsPart. assert(parent pdentry <> blockStartAddr).
    {
      unfold getPartitions in *. replace (maxAddr+2) with (S (maxAddr+1)) in *; try(lia). simpl in HparentNotInSub.
      apply Decidable.not_or in HparentNotInSub. destruct HparentNotInSub. auto.
    }
    destruct HparentIsPart as [HparentIsPart | Hcontra]; try(exfalso; congruence). rewrite HlookupsEq; auto.
    (* END partial parentOfPartitionIsPartition *)
  }
  assert(NbFreeSlotsISNbFreeSlotsInList s).
  { (* BEGIN NbFreeSlotsISNbFreeSlotsInList s *)
    assert(Hcons0: NbFreeSlotsISNbFreeSlotsInList s0) by intuition.
    intros partition nbfreeslots HpartIsPart HnbFree. apply HgetPartsImpl in HpartIsPart.
    unfold pdentryNbFreeSlots in *. assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HnbFree; trivial. specialize(Hcons0 partition nbfreeslots HpartIsPart HnbFree).
    rewrite HgetFreeEq; assumption.
    (* END NbFreeSlotsISNbFreeSlotsInList *)
  }
  assert(maxNbPrepareIsMaxNbKernels s).
  { (* BEGIN maxNbPrepareIsMaxNbKernels s *)
    assert(Hcons0: maxNbPrepareIsMaxNbKernels s0) by intuition. intros partition kernList HpartIsPart HkernList.
    apply HgetPartsImpl in HpartIsPart. destruct kernList; try(simpl; lia).
    apply isListOfKernelsEqRemovedAddrRev with (s0:=s0) (removedAddr:=blockStartAddr) in HkernList; trivial.
    specialize(Hcons0 partition (p0::kernList) HpartIsPart HkernList). assumption.
    (* END maxNbPrepareIsMaxNbKernels *)
  }
  assert(blockInChildHasAtLeastEquivalentBlockInParent s).
  { (* BEGIN blockInChildHasAtLeastEquivalentBlockInParent s *)
    assert(Hcons0: blockInChildHasAtLeastEquivalentBlockInParent s0) by intuition.
    intros pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild Hstart Hend
      HPflag. assert(HbeqParentStart: pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetChildrenEqNotStart in HchildIsChild; trivial. rewrite HgetMappedBEq in *; trivial.
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    unfold bentryPFlag in *. rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq in Hend; trivial.
    rewrite HlookupsEq in HPflag; trivial.
    specialize(Hcons0 pdparent child block startChild endChild HparentIsPart HchildIsChild HblockMappedChild
      Hstart Hend HPflag). destruct Hcons0 as [blockParent [startParent [endParent Hcons0]]].
    exists blockParent. exists startParent. exists endParent. assert(blockParent <> blockStartAddr).
    {
      intro. subst blockParent. unfold bentryStartAddr in *. unfold isPDT in *. destruct Hcons0 as (_ & Hcons0 & _).
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; assumption.
    (* END blockInChildHasAtLeastEquivalentBlockInParent *)
  }
  assert(partitionTreeIsTree s).
  { (* BEGIN partitionTreeIsTree s *)
    assert(Hcons0: partitionTreeIsTree s0) by intuition.
    intros child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsparent HparentsList.
    unfold pdentryParent in *. apply HgetPartsImpl in HchildIsPart. assert(child <> blockStartAddr).
    { intro. subst child. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HparentIsparent; trivial.
    apply isParentsListImplRemovedAddrRev with (s0:=s0) (removedAddr:=blockStartAddr) in HparentsList; trivial.
    specialize(Hcons0 child pdparent parentsList HbeqChildRoot HchildIsPart HparentIsparent HparentsList).
    assumption.
    (* END partitionTreeIsTree *)
  }
  assert(Hsh1BTD: sh1entryAddr blockToDeleteInCurrPartAddr (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) s0).
  { unfold sh1entryAddr. rewrite HlookupBTD. reflexivity. }
  assert(HlocBTD: sh1entryInChildLocation (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) nullAddr s0).
  {
    assert(Hres: childBlockNullIfChildNull s0) by intuition. specialize(Hres currentPart blockToDeleteInCurrPartAddr).
    apply Hres; assumption.
  }
  assert(HcomplKernLEq: forall part pdentry, In part (getPartitions multiplexer s0)
    -> lookup part (memory s0) beqAddr = Some (PDT pdentry)
    -> completeListOfKernels (structure pdentry) s = completeListOfKernels (structure pdentry) s0).
  {
    intros part pdentry HpartIsPart HlookupPart.
    assert(HstructIsKS: StructurePointerIsKS s0) by intuition.
    destruct (beqAddr (structure pdentry) nullAddr) eqn:HbeqStructNull.
    - rewrite <-beqAddrTrue in HbeqStructNull. rewrite HbeqStructNull. unfold completeListOfKernels.
      assert(isPADDR nullAddr s0) by intuition. unfold nullAddrExists in *.
      unfold isPADDR in *. destruct (lookup nullAddr (memory s) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). destruct (lookup nullAddr (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). reflexivity.
    - rewrite <-beqAddrFalse in *. specialize(HstructIsKS part pdentry HpartIsPart HlookupPart HbeqStructNull).
      apply completeListOfKernelsEqNoImpact with (maxIdx + 1) part pdentry blockStartAddr blockEndAddr; trivial.
      + intuition.
      + unfold completeListOfKernels. unfold isKS in *.
        destruct (lookup (structure pdentry) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite HstructIsKS. rewrite IL.indexEqRefl. cbn -[maxNbPrepare]. auto.
      + cbn. pose proof Constants.maxIdxBiggerThanMinBlock. lia.
      + intros addr HaddrInRange. assert(HaddrInBlock: In addr (getAllPaddrAux [blockToDeleteInCurrPartAddr] s0)).
        {
          simpl. unfold bentryStartAddr in *. unfold bentryEndAddr in *. rewrite HlookupBTD in *.
          rewrite <-HstartBTDs0. rewrite <-HendBTDs0. rewrite app_nil_r. assumption.
        }
        assert(In addr (getMappedPaddr currentPart s0)).
        { apply IL.addrInBlockIsMapped with blockToDeleteInCurrPartAddr; assumption. }
        intro HaddrInConfigR. assert(HaddrInConfig: In addr (getConfigPaddr part s0)).
        {
          unfold getConfigPaddr. apply in_or_app. right. unfold getConfigBlocks. rewrite HlookupPart. assumption.
        }
        assert(HpartIsDesc: In currentPart (part::filterOptionPaddr (completeParentsList part s0))).
        { apply configAddressesBloodline with addr; trivial; try(apply IL.noDupKSMappedImpl); intuition. }
        assert(~In currentPart (filterOptionPaddr (completeParentsList part s0))).
        {
          intro Hcontra. assert(Hchild: exists child,
            pdentryParent child currentPart s0
            /\ In child (getPartitions multiplexer s0)
            /\ In child (part::filterOptionPaddr (completeParentsList part s0))).
          { apply completeParentsListChild; trivial; intuition. }
          destruct Hchild as [child (Hparent & HchildIsPart & HchildIsAnc)]. unfold isPDT in *.
          destruct (lookup currentPart (memory s0) beqAddr) eqn:HlookupCurr; try(congruence).
          destruct v; try(congruence).
          assert(HaddrNotInChild: noChildImpliesAddressesNotShared s0) by intuition.
          assert(Htriv: CPaddr (blockToDeleteInCurrPartAddr+sh1offset)
            = CPaddr (blockToDeleteInCurrPartAddr + sh1offset)) by reflexivity.
          assert(HchildIsChild: isChild s0) by intuition. assert(HbeqChildRoot: child <> constantRootPartM).
          {
            assert(HparentOfPart: parentOfPartitionIsPartition s0) by intuition. unfold pdentryParent in *.
            intro Heq. destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(congruence).
            destruct v; try(congruence). specialize(HparentOfPart child p1 HlookupChild).
            destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot Heq). rewrite Hparent in *.
            rewrite HparentOfRoot in *. assert(isPADDR nullAddr s0) by intuition. unfold isPADDR in *.
            rewrite HlookupCurr in *. congruence.
          }
          specialize(HchildIsChild child currentPart HchildIsPart Hparent HbeqChildRoot).
          specialize(HaddrNotInChild currentPart p0 blockToDeleteInCurrPartAddr
            (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) HcurrIsParts0 HlookupCurr HBTDMapped Htriv HPDchild
            child addr HchildIsChild HaddrInBlock). destruct (beqAddr child part) eqn:HbeqChildPart.
          - rewrite <-beqAddrTrue in HbeqChildPart. subst part.
            assert(HPDTNoTInConfig: PDTisNoConfigInChild s0) by intuition.
            specialize(HPDTNoTInConfig currentPart child pdentry blockToDeleteInCurrPartAddr
              (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) addr HcurrIsParts0 HchildIsChild HlookupPart
              HBTDMapped Hsh1BTD HPDflag HaddrInBlock). unfold getConfigBlocks in *. rewrite HlookupPart in *.
            congruence.
          - rewrite <-beqAddrFalse in *. simpl in HchildIsAnc.
            destruct HchildIsAnc as [HcontraB | HchildIsAnc]; try(congruence).
            contradict HaddrNotInChild. apply configAddrMappedInAncestor with part; trivial; intuition.
        }
        simpl in HpartIsDesc. destruct HpartIsDesc as [Heq | Hcontra]; try(congruence). subst part.
        assert(HconfigNotInPart: PDTisNoConfigInPart s0) by intuition.
        specialize(HconfigNotInPart currentPart blockToDeleteInCurrPartAddr
          (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) addr HcurrIsParts0 HBTDMapped Hsh1BTD HPDflag
          HaddrInBlock). congruence.
  }
  assert(nextKernelIsValid s).
  { (* BEGIN nextKernelIsValid s *)
    assert(Hcons0: nextKernelIsValid s0) by intuition.
    intros part pdentry kernel HpartIsPart HlookupPart HkernIsConfig HkernIsKS. apply HgetPartsImpl in HpartIsPart.
    unfold isKS in *. assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial. assert(part <> blockStartAddr).
    { intro. subst part. congruence. }
    rewrite HlookupsEq in HlookupPart; trivial.
    assert(HcomplEq: completeListOfKernels (structure pdentry) s = completeListOfKernels (structure pdentry) s0).
    { apply HcomplKernLEq with part; assumption. }
    rewrite HcomplEq in *. specialize(Hcons0 part pdentry kernel HpartIsPart HlookupPart HkernIsConfig HkernIsKS).
    destruct Hcons0 as (HlebNextMax & [nextAddr (HlookupNext & Hnext)]). split; trivial. exists nextAddr. split.
    - intro Hp. specialize(HlookupNext Hp). rewrite HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *.
      unfold isPDT in *. rewrite HlookupNext in *. congruence.
    - destruct Hnext as [(HnextIsKS & HnextIsConfig) | HnextIsNull]; auto. left. split; trivial.
      rewrite HlookupsEq; trivial. intro. subst nextAddr.
      unfold isKS in *. unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    (* END nextKernelIsValid *)
  }
  assert(noDupListOfKerns s).
  { (* BEGIN noDupListOfKerns s *)
    assert(Hcons0: noDupListOfKerns s0) by intuition. intros partition kernList HpartIsPart HkernList.
    apply HgetPartsImpl in HpartIsPart.
    apply isListOfKernelsEqRemovedAddrRev with (s0:=s0) (removedAddr:=blockStartAddr) in HkernList; trivial.
    specialize(Hcons0 partition kernList HpartIsPart HkernList). assumption.
    (* END noDupListOfKerns *)
  }
  assert(MPUsizeIsBelowMax s).
  { (* BEGIN MPUsizeIsBelowMax s *)
    assert(Hcons0: MPUsizeIsBelowMax s0) by intuition. intros partition MPUlist HMPU. unfold pdentryMPU in *.
    assert(partition <> blockStartAddr).
    { intro. subst partition. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HMPU; trivial. specialize(Hcons0 partition MPUlist HMPU). assumption.
    (* END MPUsizeIsBelowMax *)
  }
  assert(originIsParentBlocksStart s).
  { (* BEGIN originIsParentBlocksStart s *)
    assert(Hcons0: originIsParentBlocksStart s0) by intuition.
    intros partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce Horigin.
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    assert(block <> blockStartAddr).
    {
      intro. subst block. apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
      congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. rewrite HlookupsEq in HlookupPart; trivial.
    unfold scentryOrigin in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Horigin; trivial.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    { apply HlookupsEq; assumption. }
    specialize(Hcons0 partition pdentry block scentryaddr scorigin HpartIsPart HlookupPart HblockMapped Hsce
      Horigin). destruct Hcons0 as (Hleft & Hright). unfold bentryStartAddr. rewrite HlookupBlockEq.
    split; trivial. intro HbeqPartRoot. specialize(Hleft HbeqPartRoot).
    destruct Hleft as [blockParent (HBPMapped & HstartP & Hincl)]. assert(parent pdentry <> blockStartAddr).
    {
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s0)).
      {
        assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent. rewrite HlookupPart.
        reflexivity.
      }
      intro Hcontra. rewrite Hcontra in *. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    exists blockParent. rewrite HgetMappedBEq; trivial. simpl. rewrite HlookupBlockEq. rewrite HlookupsEq; auto.
    intro. subst blockParent. unfold bentryStartAddr in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END originIsParentBlocksStart *)
  }
  assert(nextImpliesBlockWasCut s).
  { (* BEGIN nextImpliesBlockWasCut s *)
    assert(Hcons0: nextImpliesBlockWasCut s0) by intuition.
    intros partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped Hend Hsce
      HbeqNextNull Hnext HbeqPartRoot.
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    assert(block <> blockStartAddr).
    {
      intro. subst block. apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
      congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. rewrite HlookupsEq in HlookupPart; trivial.
    unfold scentryNext in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hnext; trivial.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    { apply HlookupsEq; assumption. }
    unfold bentryEndAddr in *. simpl. rewrite HlookupBlockEq in *.
    specialize(Hcons0 partition pdentry block scentryaddr scnext endaddr HpartIsPart HlookupPart HblockMapped
      Hend Hsce HbeqNextNull Hnext HbeqPartRoot).
    destruct Hcons0 as [blockParent [endParent (HBPMapped & HendP & HltEnds & Hincl)]].
    exists blockParent. exists endParent. assert(parent pdentry <> blockStartAddr).
    {
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s0)).
      {
        assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent. rewrite HlookupPart.
        reflexivity.
      }
      intro Hcontra. rewrite Hcontra in *. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    rewrite HgetMappedBEq; trivial. rewrite HlookupsEq; auto.
    intro. subst blockParent. unfold bentryEndAddr in *. unfold isPDT in *.
    destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    (* END nextImpliesBlockWasCut *)
  }
  assert(blocksAddressesTypes s).
  { (* BEGIN blocksAddressesTypes s *)
    assert(Hcons0: blocksAddressesTypes s0) by intuition.
    intros block startaddr endaddr part HpartIsPart HblockMapped Hstart Hend Hloc.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    unfold bentryEndAddr in *. rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq in Hend; trivial.
    unfold sh1entryInChildLocationWeak in *. assert(CPaddr (block+sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hloc; trivial.
    specialize(Hcons0 block startaddr endaddr part HpartIsPart HblockMapped Hstart Hend Hloc).
    destruct Hcons0 as [(HKS & Hrange) | [(HPDT & Hrange) | Hrange]].
    - left. unfold isKS in *. assert(startaddr <> blockStartAddr).
      {
        intro. subst startaddr. unfold isPDT in *.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      }
      rewrite HlookupsEq; trivial. split; trivial. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
      destruct Hrange as [HBE | [HSHE | [HSCE | [HPADDR | Hnone]]]].
      + left. unfold isBE in *. rewrite HlookupsEq; trivial. intro. subst addr.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      + right. left. unfold isSHE in *. rewrite HlookupsEq; trivial. intro. subst addr.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      + right. right. left. unfold isSCE in *. rewrite HlookupsEq; trivial. intro. subst addr.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      + right. right. right. left. unfold isPADDR in *. rewrite HlookupsEq; trivial. intro. subst addr.
        destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
      + right. right. right. right. rewrite HlookupsEq; trivial. intro. subst addr. congruence.
    - destruct (beqAddr startaddr blockStartAddr) eqn:HbeqStarts.
      + rewrite <-beqAddrTrue in HbeqStarts. subst startaddr. right. right. intros addr HaddrInRange.
        destruct (beqAddr addr blockStartAddr) eqn:HbeqAddrStart.
        * rewrite <-beqAddrTrue in HbeqAddrStart. subst addr. assumption.
        * rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial. apply Hrange; auto.
      + rewrite <-beqAddrFalse in *. right. left. unfold isPDT. rewrite HlookupsEq; trivial. split; trivial.
        intros addr HaddrInRange. specialize(Hrange addr HaddrInRange). rewrite HlookupsEq; trivial.
        intro. subst addr. unfold isPDT in *. rewrite Hrange in *. congruence.
    - right. right. intros addr HaddrInRange. specialize(Hrange addr HaddrInRange).
      destruct (beqAddr addr blockStartAddr) eqn:HbeqAddrStart.
      + rewrite <-beqAddrTrue in HbeqAddrStart. subst addr. assumption.
      + rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
    (* END blocksAddressesTypes *)
  }
  assert(notPDTIfNotPDflag s).
  { (* BEGIN notPDTIfNotPDflag s *)
    assert(Hcons0: notPDTIfNotPDflag s0) by intuition.
    intros block startaddr sh1entryaddrBis part HpartIsPart HblockMapped Hstart Hsh1 HPDflagB HPDchildB.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hstart; trivial. unfold sh1entryAddr in *. rewrite HlookupsEq in Hsh1; trivial.
    unfold sh1entryPDchild in *. unfold sh1entryPDflag in *. assert(sh1entryaddrBis <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. rewrite HlookupsEq in HPDflagB; trivial.
    specialize(Hcons0 block startaddr sh1entryaddrBis part HpartIsPart HblockMapped Hstart Hsh1 HPDflagB HPDchildB).
    contradict Hcons0. unfold isPDT in *. rewrite <-HlookupsEq; trivial. intro. subst startaddr.
    rewrite HlookupStarts in *. congruence.
    (* END notPDTIfNotPDflag *)
  }
  assert(nextKernAddrIsInSameBlock s).
  { (* BEGIN nextKernAddrIsInSameBlock s *)
    assert(Hcons0: nextKernAddrIsInSameBlock s0) by intuition.
    intros block kernel startaddr endaddr part HpartIsPart HblockMapped Hstart Hend HPDchildB HkernIsKS HnextInBlock.
    apply HgetPartsImpl in HpartIsPart. assert(HbeqPartStart: part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hstart; trivial. unfold bentryEndAddr in *. rewrite HlookupsEq in Hend; trivial.
    unfold sh1entryPDchild in *. assert(CPaddr (block+sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. unfold isKS in *. assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HkernIsKS; trivial.
    specialize(Hcons0 block kernel startaddr endaddr part HpartIsPart HblockMapped Hstart Hend HPDchildB HkernIsKS
      HnextInBlock). assumption.
    (* END nextKernAddrIsInSameBlock *)
  }
  assert(noDupMappedPaddrList s).
  { (* BEGIN noDupMappedPaddrList s *)
    assert(Hcons0: noDupMappedPaddrList s0) by intuition. intros partition HpartIsPart.
    apply HgetPartsImpl in HpartIsPart. destruct (beqAddr partition blockStartAddr) eqn:HbeqParts.
    - rewrite <-beqAddrTrue in HbeqParts. subst partition. unfold getMappedPaddr. unfold getMappedBlocks.
      unfold getKSEntries. rewrite HlookupStarts. simpl. apply NoDup_nil.
    - rewrite <-beqAddrFalse in *. specialize(Hcons0 partition HpartIsPart). rewrite HgetMappedPEq; assumption.
    (* END noDupMappedPaddrList *)
  }
  assert(accessibleParentPaddrIsAccessibleIntoChild s).
  { (* BEGIN accessibleParentPaddrIsAccessibleIntoChild s *)
    assert(Hcons0: accessibleParentPaddrIsAccessibleIntoChild s0) by intuition.
    intros pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild.
    apply HgetPartsImpl in HparentIsPart. assert(pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetChildrenImpl in HchildIsChild. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedPaddr in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
      rewrite HlookupStarts in *. simpl in *. congruence.
    }
    rewrite HgetAccMappedPEq in *; trivial. rewrite HgetMappedPEq in *; trivial.
    specialize(Hcons0 pdparent child addr HparentIsPart HchildIsChild HaddrAccParent HaddrMappedChild). assumption.
    (* END accessibleParentPaddrIsAccessibleIntoChild *)
  }
  assert(sharedBlockPointsToChild s).
  { (* BEGIN sharedBlockPointsToChild s *)
    assert(Hcons0: sharedBlockPointsToChild s0) by intuition.
    intros pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParent HblockParentMapped Hsh1Bis. unfold getUsedPaddr in *. assert(pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. apply HgetChildrenImpl in HchildIsChild. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedPaddr in *. unfold getMappedBlocks in *.
      unfold getKSEntries in *. unfold getConfigPaddr in *. unfold getConfigBlocks in *. simpl in *.
      rewrite HlookupStarts in *. simpl in *. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. rewrite HgetMappedPEq in *; trivial. rewrite HgetConfigEq in *; trivial.
    unfold sh1entryAddr in *. assert(blockParent <> blockStartAddr).
    { intro. subst blockParent. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1Bis; trivial. simpl in *. rewrite HlookupsEq in HaddrInBlockParent; trivial.
    specialize(Hcons0 pdparent child addr blockParent sh1entryaddrBis HparentIsPart HchildIsChild HaddrUsedChild
      HaddrInBlockParent HblockParentMapped Hsh1Bis). unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
    assert(CPaddr (blockParent + sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStart in *. destruct Hcons0; congruence. }
    rewrite HlookupsEq; assumption.
    (* END sharedBlockPointsToChild *)
  }
  assert(adressesRangePreservedIfOriginAndNextOk s).
  { (* BEGIN adressesRangePreservedIfOriginAndNextOk s *)
    assert(Hcons0: adressesRangePreservedIfOriginAndNextOk s0) by intuition.
    intros partition pdentry block scentryaddr start endaddr HpartIsPart HblockMapped HblockIsBE Hstart Hend
      HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    apply HgetPartsImpl in HpartIsPart. rewrite HgetMappedBEq in HblockMapped; trivial. unfold isBE in *.
    unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. rewrite HlookupsEq in Hstart; trivial.
    rewrite HlookupsEq in Hend; trivial. rewrite HlookupsEq in HPflag; trivial. unfold scentryNext in *.
    rewrite HlookupsEq in HlookupPart; trivial. unfold scentryOrigin in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Horigin; trivial. rewrite HlookupsEq in Hnext; trivial.
    specialize(Hcons0 partition pdentry block scentryaddr start endaddr HpartIsPart HblockMapped HblockIsBE
      Hstart Hend HPflag Hsce Horigin Hnext HlookupPart HbeqPartRoot).
    destruct Hcons0 as [blockParent (HBPMapped & HBPIsBE & Hbounds)]. assert(parent pdentry <> blockStartAddr).
    {
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s0)).
      {
        assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent. rewrite HlookupPart.
        reflexivity.
      }
      intro Hcontra. rewrite Hcontra in *. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    exists blockParent. rewrite HgetMappedBEq; trivial. rewrite HlookupsEq; auto. intro. subst blockParent.
    unfold isBE in *. rewrite HlookupStart in *. congruence.
    (* END adressesRangePreservedIfOriginAndNextOk *)
  }
  assert(childsBlocksPropsInParent s).
  { (* BEGIN childsBlocksPropsInParent s *)
    assert(Hcons0: childsBlocksPropsInParent s0) by intuition.
    intros child parentPart blockChild startChild endChild blockParent startParent endParent HparentIsPart
      HchildIsChild HchildMapped HstartChild HendChild HPFlagChild HparentMapped HparentStart HparentEnd
      HPFlagParent HleStart HgeEnd. assert(parentPart <> blockStartAddr).
    { intro. subst parentPart. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. apply HgetChildrenImpl in HchildIsChild. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. unfold bentryStartAddr in *. unfold bentryEndAddr in *.
    assert(HlookupBPEq: lookup blockParent (memory s) beqAddr = lookup blockParent (memory s0) beqAddr).
    { apply HlookupsEq. intro. subst blockParent. rewrite HlookupStarts in *. congruence. }
    unfold bentryPFlag in *. unfold checkChild. unfold bentryAFlag. rewrite HlookupBPEq in *.
    assert(HlookupBCEq: lookup blockChild (memory s) beqAddr = lookup blockChild (memory s0) beqAddr).
    { apply HlookupsEq. intro. subst blockChild. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupBCEq in *. specialize(Hcons0 child parentPart blockChild startChild endChild blockParent
      startParent endParent HparentIsPart HchildIsChild HchildMapped HstartChild HendChild HPFlagChild
      HparentMapped HparentStart HparentEnd HPFlagParent HleStart HgeEnd).
    destruct Hcons0 as (HcheckChildB & HPDchildB & HinChildLoc & HAflagParent). unfold checkChild in *.
    assert(HlookupSh1Eq: lookup (CPaddr (blockParent+sh1offset)) (memory s) beqAddr
      = lookup (CPaddr (blockParent+sh1offset)) (memory s0) beqAddr).
    {
      apply HlookupsEq. assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0) by intuition.
      assert(HBPIsBE: isBE blockParent s0).
      {
        unfold isBE. destruct (lookup blockParent (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
        trivial.
      }
      apply Hsh1IsSHE in HBPIsBE. intro Hcontra. rewrite Hcontra in *. unfold isSHE in *. rewrite HlookupStart in *.
      congruence.
    }
    unfold sh1entryPDchild. unfold sh1entryInChildLocation in *. rewrite HlookupSh1Eq.
    split; try(split; try(split)); trivial. intros blockIDInChild HchildLoc. apply HinChildLoc.
    destruct (lookup (CPaddr (blockParent + sh1offset)) (memory s0) beqAddr); try(congruence).
    destruct v; try(congruence). destruct HchildLoc as (HchildLoc & HlocIsBE). split; trivial. intro HbeqIdNull.
    specialize(HlocIsBE HbeqIdNull). unfold isBE in *. rewrite <-HlookupsEq; trivial. intro Hcontra.
    rewrite Hcontra in *. rewrite HlookupStarts in *. congruence.
    (* END childsBlocksPropsInParent *)
  }
  assert(noChildImpliesAddressesNotShared s).
  { (* BEGIN noChildImpliesAddressesNotShared s *)
    assert(Hcons0: noChildImpliesAddressesNotShared s0) by intuition.
    intros partition pdentry block sh1entryaddrBis HpartIsPart HlookupPart HblockMapped Hsh1Bis HPDChild child
      addr HchildIsChild HaddrInBlock. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    destruct (beqAddr child blockStartAddr) eqn:HbeqChildStart.
    - rewrite <-beqAddrTrue in HbeqChildStart. subst child. unfold getMappedPaddr. unfold getMappedBlocks.
      unfold getKSEntries. rewrite HlookupStarts. auto.
    - rewrite <-beqAddrFalse in *. apply HgetPartsImpl in HpartIsPart. rewrite HlookupsEq in HlookupPart; trivial.
      apply HgetChildrenImpl in HchildIsChild. simpl in *. assert(block <> blockStartAddr).
      { intro. subst block. rewrite HlookupStarts in *. simpl in *. congruence. }
      rewrite HlookupsEq in HaddrInBlock; trivial. rewrite HgetMappedBEq in *; trivial.
      rewrite HgetMappedPEq; trivial. unfold sh1entryPDchild in *. assert(sh1entryaddrBis <> blockStartAddr).
      { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
      rewrite HlookupsEq in HPDChild; trivial. specialize(Hcons0 partition pdentry block sh1entryaddrBis HpartIsPart
        HlookupPart HblockMapped Hsh1Bis HPDChild child addr HchildIsChild HaddrInBlock). assumption.
    (* END noChildImpliesAddressesNotShared *)
  }
  assert(kernelsAreNotAccessible s).
  { (* BEGIN kernelsAreNotAccessible s *)
    assert(Hcons0: kernelsAreNotAccessible s0) by intuition.
    intros block startaddr part HpartIsPart HblockMapped Hstart HstartIsKS.
    assert(HbeqPartStart: part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    unfold bentryAFlag. rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq; trivial. unfold isKS in *.
    rewrite HgetMappedBEq in *; trivial. assert(startaddr <> blockStartAddr).
    { intro. subst startaddr. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HstartIsKS; trivial.
    specialize(Hcons0 block startaddr part HpartIsPart HblockMapped Hstart HstartIsKS). assumption.
    (* END kernelsAreNotAccessible *)
  }
  assert(PDflagMeansNoChild s).
  { (* BEGIN PDflagMeansNoChild s *)
    assert(Hcons0: PDflagMeansNoChild s0) by intuition. intros block HblockIsBE HPDflagB. unfold isBE in *.
    assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. unfold sh1entryPDflag in *.
    assert(CPaddr (block+sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    unfold sh1entryPDchild. rewrite HlookupsEq in HPDflagB; trivial. specialize(Hcons0 block HblockIsBE HPDflagB).
    rewrite HlookupsEq; assumption.
    (* END PDflagMeansNoChild *)
  }

  assert(nbPrepareIsNbKern s).
  { (* BEGIN nbPrepareIsNbKern s *)
    assert(Hcons0: nbPrepareIsNbKern s0) by intuition. intros partition pdentry HpartIsPart HlookupPart.
    assert(partition <> blockStartAddr) by (intro; subst partition; congruence). apply HgetPartsImpl in HpartIsPart.
    rewrite HlookupsEq in HlookupPart; trivial. specialize(Hcons0 partition pdentry HpartIsPart HlookupPart).
    rewrite completeListOfKernelsEqRemovedAddr with (s0:=s0) (removedAddr:=blockStartAddr); assumption.
   (* END nbPrepareIsNbKern *)
  }

  assert(blockAndNextAreSideBySide s).
  { (* BEGIN blockAndNextAreSideBySide s *)
    assert(Hcons0: blockAndNextAreSideBySide s0) by intuition.
    intros partition block scentryaddr scnext endaddr HpartIsPart HblockMapped Hend Hsce HbeqNextNull Hnext.
    assert(HbeqPartStart: partition <> blockStartAddr).
    {
      intro. subst partition. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold bentryEndAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hend; trivial. rewrite HgetMappedBEq in *; trivial.
    unfold scentryNext in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hnext; trivial.
    specialize(Hcons0 partition block scentryaddr scnext endaddr HpartIsPart HblockMapped Hend Hsce HbeqNextNull
      Hnext). destruct Hcons0 as (HstartNext & HnextMapped). unfold bentryStartAddr in *. rewrite HlookupsEq; auto.
    intro. subst scnext. unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
    destruct v; congruence.
    (* END blockAndNextAreSideBySide *)
  }

  assert(parentBlocksBoundsIfNoNext s).
  { (* BEGIN parentBlocksBoundsIfNoNext s *)
    assert(Hcons0: parentBlocksBoundsIfNoNext s0) by intuition.
    intros partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped Hstart Hend Hsce
      Hnext HbeqPartRoot HlookupPart. unfold bentryStartAddr in *. assert(HbeqPartStart: partition <> blockStartAddr).
    { intro. subst partition. congruence. }
    assert(HpartIsPartCopy: In partition (getPartitions multiplexer s)) by assumption.
    apply HgetPartsImpl in HpartIsPart. unfold bentryEndAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq in Hend; trivial.
    rewrite HgetMappedBEq in HblockMapped; trivial. unfold scentryNext in *. assert(scentryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hnext; trivial. rewrite HlookupsEq in HlookupPart; trivial.
    specialize(Hcons0 partition pdentry block scentryaddr startaddr endaddr HpartIsPart HblockMapped Hstart Hend
      Hsce Hnext HbeqPartRoot HlookupPart).
    destruct Hcons0 as [blockParent [startParent (HBPMapped & HstartP & Hcons0)]]. exists blockParent.
    exists startParent. assert(parent pdentry <> blockStartAddr).
    {
      assert(HpartIsChild: In partition (getChildren (parent pdentry) s0)).
      {
        assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent. rewrite HlookupPart.
        reflexivity.
      }
      intro Hcontra. rewrite Hcontra in *. assert(HpartIsStart: In partition (getPartitions blockStartAddr s0)).
      { apply childrenAreSubParts; trivial. }
      assert(HnoDup: NoDup (getPartitions multiplexer s0)) by intuition.
      pose proof (getPartitionsExcludesRemovedAddr partition multiplexer s0 s blockStartAddr HlookupsEq HlookupStarts
        HstartIsPDT HpartIsStart HbeqPartStart HnoDup HstartIsParts0) as HnotIn. congruence.
    }
    rewrite HgetMappedBEq; trivial. unfold bentryStartAddr in *. assert(blockParent <> blockStartAddr).
    {
      intro. subst blockParent. unfold isPDT in *.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; auto.
    (* END parentBlocksBoundsIfNoNext *)
  }

  assert(pdchildIsPDT s).
  { (* BEGIN pdchildIsPDT s *)
    assert(Hcons0: pdchildIsPDT s0) by intuition.
    intros part block sh1entryaddrB idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull.
    assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1; trivial. rewrite HgetMappedBEq in *; trivial. unfold sh1entryPDchild in *.
    assert(sh1entryaddrB <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial.
    specialize(Hcons0 part block sh1entryaddrB idchild HpartIsPart HblockMapped Hsh1 HPDchildB HbeqIdChildNull).
    rewrite HgetChildrenEqNotStart; trivial.
    (* END pdchildIsPDT *)
  }

  assert(childBlockNullIfChildNull s).
  { (* BEGIN childBlockNullIfChildNull s *)
    assert(Hcons0: childBlockNullIfChildNull s0) by intuition.
    intros part block sh1entryaddrB HpartIsPart HblockMapped Hsh1 HPDchildB. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1; trivial. rewrite HgetMappedBEq in *; trivial. unfold sh1entryPDchild in *.
    assert(sh1entryaddrB <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial.
    specialize(Hcons0 part block sh1entryaddrB HpartIsPart HblockMapped Hsh1 HPDchildB).
    unfold sh1entryInChildLocation in *. rewrite HlookupsEq; trivial.
    destruct (lookup sh1entryaddrB (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
    destruct Hcons0 as (Hloc & HlocIsBE). split; trivial. intro Hcontra. exfalso; congruence.
    (* END pdchildIsPDT *)
  }

  assert(HpartialChildLocProps: forall partition block sh1entryaddr blockChild idchild startaddr,
    idchild <> blockStartAddr
    -> In partition (getPartitions multiplexer s) -> In block (getMappedBlocks partition s)
    -> sh1entryAddr block sh1entryaddr s -> sh1entryPDchild sh1entryaddr idchild s
    -> sh1entryInChildLocationWeak sh1entryaddr blockChild s -> idchild <> nullAddr
    -> bentryStartAddr block startaddr s -> ~ isKS startaddr s
    -> blockChild <> nullAddr /\ In blockChild (getMappedBlocks idchild s) /\ bentryStartAddr blockChild startaddr s).
  { (* BEGIN partial childLocMappedInChild s *)
    assert(Hcons0: childLocMappedInChild s0) by intuition.
    intros part block sh1entryaddrB blockChild idchild startaddr HbeqChildStart HpartIsPart HblockMapped Hsh1
      HPDchildB Hloc HbeqIdChildNull Hstart HstartNotKS. unfold bentryStartAddr in *. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1; trivial. rewrite HlookupsEq in Hstart; trivial.
    rewrite HgetMappedBEq in *; trivial. assert(HstartNotKSs0: ~isKS startaddr s0).
    {
      contradict HstartNotKS. unfold isKS in *. rewrite HlookupsEq; trivial. intro. subst startaddr.
      unfold isPDT in *. destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence).
      destruct v; congruence.
    }
    unfold sh1entryInChildLocationWeak in *. unfold sh1entryPDchild in *. assert(sh1entryaddrB <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. rewrite HlookupsEq in Hloc; trivial.
    specialize(Hcons0 part block sh1entryaddrB blockChild idchild startaddr HpartIsPart HblockMapped Hsh1
      HPDchildB Hloc HbeqIdChildNull Hstart HstartNotKSs0). assert(blockChild <> blockStartAddr).
    {
      destruct Hcons0 as (_ & _ & HstartC). intro. subst blockChild. unfold bentryStartAddr in *.
      rewrite HlookupStart in *. congruence.
    }
    rewrite HlookupsEq; assumption.
    (* END partial childLocMappedInChild *)
  }

  assert(HpartialSameStart: forall partition block sh1entryaddr blockChild idchild,
    idchild <> blockStartAddr
    -> In partition (getPartitions multiplexer s) -> In block (getMappedBlocks partition s)
    -> sh1entryAddr block sh1entryaddr s -> sh1entryPDchild sh1entryaddr idchild s
    -> sh1entryInChildLocationWeak sh1entryaddr blockChild s -> idchild <> nullAddr
    -> blockChild <> nullAddr
    -> (forall startaddr, bentryStartAddr block startaddr s -> bentryStartAddr blockChild startaddr s)
          /\ In blockChild (getMappedBlocks idchild s)).
  { (* BEGIN partial childLocHasSameStart s *)
    assert(Hcons0: childLocHasSameStart s0) by intuition.
    intros part block sh1entryaddrB blockChild idchild HbeqChildStart HpartIsPart HblockMapped Hsh1 HPDchildB Hloc
      HbeqIdChildNull HbeqBCNull. unfold bentryStartAddr in *. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hsh1; trivial. rewrite HlookupsEq; trivial. rewrite HgetMappedBEq in *; trivial.
    unfold sh1entryInChildLocationWeak in *. unfold sh1entryPDchild in *. assert(sh1entryaddrB <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. rewrite HlookupsEq in Hloc; trivial.
    specialize(Hcons0 part block sh1entryaddrB blockChild idchild HpartIsPart HblockMapped Hsh1
      HPDchildB Hloc HbeqIdChildNull HbeqBCNull). destruct Hcons0 as (HsameStart & HBCMapped). split; trivial.
    intros startaddr Hstart. specialize(HsameStart startaddr Hstart). unfold bentryStartAddr in *.
    rewrite HlookupsEq; trivial. intro. subst blockChild. rewrite HlookupStart in *. congruence.
    (* END partial childLocHasSameStart *)
  }

  assert(accessibleBlocksArePresent s).
  { (* BEGIN accessibleBlocksArePresent s *)
    assert(Hcons0: accessibleBlocksArePresent s0) by intuition.
    intros block HAflag. unfold bentryAFlag in *. unfold bentryPFlag. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HAflag; trivial. specialize(Hcons0 block HAflag). rewrite HlookupsEq; assumption.
    (* END accessibleBlocksArePresent *)
  }

  assert(sharedBlockIsPresent s).
  { (* BEGIN sharedBlockIsPresent s *)
    assert(Hcons0: sharedBlockIsPresent s0) by intuition.
    intros part block child HpartIsPart HblockIsEntry HPDchildB HbeqChildNull. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getKSEntries in *. rewrite HlookupStarts in *. simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. rewrite HgetKSEq in *; trivial. unfold sh1entryPDchild in *.
    assert(CPaddr (block + sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial.
    specialize(Hcons0 part block child HpartIsPart HblockIsEntry HPDchildB HbeqChildNull). unfold bentryPFlag in *.
    rewrite HlookupsEq; trivial. intro. subst block. rewrite HlookupStart in *. congruence.
    (* END sharedBlockIsPresent *)
  }

  assert(HpartialPDTIfPDFlag: forall idPDchild sh1entryaddr part, idPDchild <> blockToDeleteInCurrPartAddr
    -> In part (getPartitions multiplexer s)
    -> In idPDchild (getMappedBlocks part s)
    -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
    -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
        /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s)).
  { (* BEGIN partial PDTIfPDFlag s *)
    assert(Hcons0: PDTIfPDFlag s0) by intuition.
    intros idPDchild sh1entryaddr part HbeqBlockBTD HpartIsPart HblockMapped HcheckChildB.
    apply HgetPartsImpl in HpartIsPart. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial.
    unfold sh1entryAddr in *. unfold checkChild in *. unfold bentryAFlag. unfold bentryPFlag. unfold entryPDT.
    assert(HlookupBlockEq: lookup idPDchild (memory s) beqAddr = lookup idPDchild (memory s0) beqAddr).
    { apply HlookupsEq. destruct HcheckChildB. intro. subst idPDchild. rewrite HlookupStarts in *. congruence. }
    unfold bentryStartAddr. rewrite HlookupBlockEq in *.
    assert(HcheckChildBs0: true = checkChild idPDchild s0 sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s0).
    {
      destruct HcheckChildB as (HcheckChildB & Hsh1). split; trivial. unfold checkChild.
      destruct (lookup idPDchild (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
      rewrite <-HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence.
    }
    specialize(Hcons0 idPDchild sh1entryaddr part HpartIsPart HblockMapped HcheckChildBs0).
    destruct Hcons0 as (HAflag & HPflag & [startaddr (Hstart & HstartBIsPDT)]). split; try(split); trivial.
    exists startaddr. split; trivial. unfold entryPDT in *.
    destruct (lookup idPDchild (memory s0) beqAddr) eqn:HlookupBlock; try(congruence). destruct v; try(congruence).
    rewrite HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *. rewrite HlookupStart in *. subst startaddr.
    assert(HPDchildB: sh1entryPDchild (CPaddr (idPDchild + sh1offset)) nullAddr s0).
    {
      destruct HcheckChildB. subst sh1entryaddr. assert(Hres: PDflagMeansNoChild s0) by intuition. apply Hres.
      - unfold isBE. rewrite HlookupBlock. trivial.
      - unfold sh1entryPDflag. destruct HcheckChildBs0. unfold checkChild in *. rewrite HlookupBlock in *.
        destruct (lookup (CPaddr (idPDchild+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
    }
    assert(HstartInBTD: In blockStartAddr (getAllPaddrAux [blockToDeleteInCurrPartAddr] s0)).
    {
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl. rewrite HlookupBTD in *.
      rewrite <-HstartBTDs0. rewrite <-HendBTDs0. rewrite app_nil_r. apply IL.getAllPaddrBlockIncl; lia.
    }
    assert(HstartInBlock: In blockStartAddr (getAllPaddrAux [idPDchild] s0)).
    {
      assert(Hend: exists endaddr, bentryEndAddr idPDchild endaddr s0).
      { unfold bentryEndAddr. rewrite HlookupBlock. exists (endAddr (blockrange b0)). reflexivity. }
      assert(HwellB: wellFormedBlock s0) by intuition. destruct Hend as [endaddr Hend].
      specialize(HwellB idPDchild blockStartAddr endaddr HPflag Hstart Hend). destruct HwellB as (HwellB & _).
      unfold bentryStartAddr in *. unfold bentryEndAddr in *. simpl. rewrite HlookupBlock in *.
      rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r. apply IL.getAllPaddrBlockIncl; lia.
    }
    assert(HpartIsAnc: In part (currentPart::filterOptionPaddr (completeParentsList currentPart s0))).
    {
      apply addressesBloodlineIfNotShared with blockStartAddr blockToDeleteInCurrPartAddr; trivial;
        try(apply IL.noDupKSMappedImpl).
      1-13: intuition. apply IL.addrInBlockIsMapped with idPDchild; trivial.
    }
    assert(HcurrIsAnc: In currentPart (part::filterOptionPaddr (completeParentsList part s0))).
    {
      apply addressesBloodlineIfNotShared with blockStartAddr idPDchild; trivial; try(apply IL.noDupKSMappedImpl).
      1-13: intuition. apply IL.addrInBlockIsMapped with blockToDeleteInCurrPartAddr; trivial.
    }
    assert(Heq: part = currentPart).
    {
      destruct (beqAddr part currentPart) eqn:HbeqParts; try(apply beqAddrTrue; assumption). exfalso.
      rewrite <-beqAddrFalse in *. simpl in *. clear Hcontra.
      destruct HcurrIsAnc as [Hcontra | HcurrIsAnc]; try(congruence).
      destruct HpartIsAnc as [Hcontra | HpartIsAnc]; try(congruence).
      assert(HpartIsNotAnc: ~In part (filterOptionPaddr (completeParentsList currentPart s0))).
      { apply completeParentsListOrientation; trivial; intuition. }
      congruence.
    }
    subst part. contradict HbeqBlockBTD.
    apply uniqueBlockMapped with blockStartAddr currentPart s0; trivial; intuition.
    (* END partial PDTIfPDFlag *)
  }

  assert(HstartBTDs: bentryStartAddr blockToDeleteInCurrPartAddr blockStartAddr s).
  {
    unfold bentryStartAddr. rewrite HlookupBTDEq. assumption.
  }

  assert(HpartialSharedNoLocIsKern: forall part block child startaddr,
    child <> blockStartAddr
    -> In part (getPartitions multiplexer s)
    -> In block (getMappedBlocks part s)
    -> sh1entryPDchild (CPaddr (block + sh1offset)) child s
    -> child <> nullAddr
    -> sh1entryPDflag (CPaddr (block + sh1offset)) false s
    -> sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) nullAddr s
    -> bentryStartAddr block startaddr s
    -> In startaddr (getConfigBlocks child s)
        /\ (forall addr child2, In addr (getAllPaddrAux [block] s)
              -> In child2 (getChildren part s)
              -> ~In addr (getMappedPaddr child2 s))
        /\ (forall (addr:paddr) endaddr part2, bentryEndAddr block endaddr s
              -> In part2 (getPartitions multiplexer s)
              -> startaddr+Constants.kernelStructureTotalLength <= addr
              -> addr < endaddr
              -> ~In addr (getConfigPaddr part2 s))).
  { (* BEGIN sharedBlockNoPDflagNoLocIsKern s *)
    assert(Hcons0: sharedBlockNoPDflagNoLocIsKern s0) by intuition.
    intros part block child startaddr HbeqChildStart HpartIsPart HblockMapped HPDchildB HbeqChildNull HPDflagB Hloc
      Hstart. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. rewrite HgetMappedBEq in *; trivial. unfold sh1entryPDchild in *.
    unfold sh1entryPDflag in *. unfold sh1entryInChildLocationWeak in *. unfold bentryStartAddr in *. simpl.
    assert(CPaddr (block + sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. rewrite HlookupsEq in HPDflagB; trivial.
    rewrite HlookupsEq in Hloc; trivial. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in Hstart; trivial. rewrite HlookupsEq; trivial.
    specialize(Hcons0 part block child startaddr HpartIsPart HblockMapped HPDchildB HbeqChildNull HPDflagB Hloc
      Hstart). destruct Hcons0 as (HstartIsConfig & HrangeNotShared & Hunused). rewrite HgetConfigBEq; trivial.
    split; trivial. split.
    - intros addr child2 HaddrInBlock Hchild2IsChild. apply HgetChildrenImpl in Hchild2IsChild.
      specialize(HrangeNotShared addr child2 HaddrInBlock Hchild2IsChild). contradict HrangeNotShared.
      rewrite <-HgetMappedPEq; trivial. intro. subst child2. unfold getMappedPaddr in *. unfold getMappedBlocks in *.
      unfold getKSEntries in *. rewrite HlookupStarts in *. simpl in *. congruence.
    - intros addr endaddr part2 Hend Hpart2IsPart HlebStartUselAddr HltAddrEnd Hcontra. unfold bentryEndAddr in *.
      rewrite HlookupsEq in Hend; trivial. assert(part2 <> blockStartAddr).
      {
        intro HcontraB. subst part2. unfold getConfigPaddr in *. unfold getConfigBlocks in *. simpl in Hcontra.
        rewrite HlookupStarts in Hcontra. simpl in Hcontra. congruence.
      }
      apply HgetPartsImpl in Hpart2IsPart. rewrite HgetConfigEq in Hcontra; trivial.
      specialize(Hunused addr endaddr part2 Hend Hpart2IsPart HlebStartUselAddr HltAddrEnd). congruence.
    (* END sharedBlockNoPDflagNoLocIsKern *)
  }

  assert(partitionNotAutoMapped s).
  { (* BEGIN partitionNotAutoMapped s *)
    assert(Hcons0: partitionNotAutoMapped s0) by intuition. intros part HpartIsPart.
    apply HgetPartsImpl in HpartIsPart. specialize(Hcons0 part HpartIsPart). contradict Hcons0.
    rewrite <-HgetMappedPEq; trivial. intro. subst part. unfold getMappedPaddr in *. unfold getMappedBlocks in *.
    unfold getKSEntries in *. rewrite HlookupStarts in *. simpl in Hcons0. congruence.
    (* END partitionNotAutoMapped *)
  }

  assert(configAddrNotMappedInChild s).
  { (* BEGIN configAddrNotMappedInChild s *)
    assert(Hcons0: configAddrNotMappedInChild s0) by intuition.
    intros part child addr HpartIsPart HchildIsChild HaddrIsConfig. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getChildren in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
      rewrite HlookupStarts in *. simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. apply HgetChildrenImpl in HchildIsChild. rewrite HgetConfigEq in *; trivial.
    specialize(Hcons0 part child addr HpartIsPart HchildIsChild HaddrIsConfig). contradict Hcons0.
    unfold getUsedPaddr in *. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getMappedPaddr in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
      unfold getConfigPaddr in *. unfold getConfigBlocks in *. simpl in *. rewrite HlookupStarts in *.
      simpl in Hcons0. congruence.
    }
    rewrite <-HgetMappedPEq; trivial. rewrite <-HgetConfigEq; trivial.
    (* END configAddrNotMappedInChild *)
  }

  assert(fullKernelIsInOneBlock s).
  { (* BEGIN fullKernelIsInOneBlock s *)
    assert(Hcons0: fullKernelIsInOneBlock s0) by intuition.
    intros part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKS. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. simpl in HkernInBlock. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. simpl in HkernInBlock. congruence. }
    rewrite HgetMappedBEq in *; trivial. unfold isKS in *. assert(kernel <> blockStartAddr).
    { intro. subst kernel. rewrite HlookupStarts in *. congruence. }
    simpl. rewrite HlookupsEq in HkernInBlock; trivial. rewrite HlookupsEq in HkernIsKS; trivial.
    rewrite HlookupsEq; trivial.
    specialize(Hcons0 part block kernel HpartIsPart HblockMapped HkernInBlock HkernIsKS). assumption.
    (* END fullKernelIsInOneBlock *)
  }

  assert(kernInSameBlock s).
  {
    assert(Hcons0: kernInSameBlock s0) by intuition.
    intros parentBlock part idx block HpartIsPart HBPMapped HblockInBP Hblkidx.
    assert(HrangeEq: getAllPaddrAux [parentBlock] s = getAllPaddrAux [parentBlock] s0).
    {
      simpl. simpl in HblockInBP. rewrite HlookupsEq; trivial. intro Hcontra. subst parentBlock.
      rewrite HlookupStarts in HblockInBP. simpl in HblockInBP. congruence.
    }
    rewrite HrangeEq in *. assert(part <> blockStartAddr).
    {
      intro Hcontra. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *.
      rewrite HlookupStarts in HBPMapped. simpl in HBPMapped. congruence.
    }
    rewrite HgetMappedBEq in HBPMapped; trivial. apply HgetPartsImpl in HpartIsPart. unfold bentryBlockIndex in *.
    assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in Hblkidx. congruence. }
    rewrite HlookupsEq in Hblkidx; trivial. unfold kernInSameBlock in *. apply Hcons0 with part; trivial.
  }

  assert(blockAndSh1InSameBlock s).
  {
    assert(Hcons0: blockAndSh1InSameBlock s0) by intuition.
    intros part block parentBlock HpartIsPart HPBMapped HblockIsBE Hsh1InRange. apply HgetPartsImpl in HpartIsPart.
    assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in HPBMapped. congruence.
    }
    rewrite HgetMappedBEq in *; trivial.
    assert(HrangeEq: getAllPaddrAux [parentBlock] s = getAllPaddrAux [parentBlock] s0).
    {
      simpl. simpl in Hsh1InRange. rewrite HlookupsEq; trivial. intro Hcontra. subst parentBlock.
      rewrite HlookupStarts in Hsh1InRange. simpl in Hsh1InRange. congruence.
    }
    rewrite HrangeEq in *. unfold isBE in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in HblockIsBE. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. specialize(Hcons0 part). apply Hcons0; trivial.
  }

  assert(blockAndSceInSameBlock s).
  {
    assert(Hcons0: blockAndSceInSameBlock s0) by intuition.
    intros part block parentBlock HpartIsPart HPBMapped HblockIsBE HsceInRange. apply HgetPartsImpl in HpartIsPart.
    assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in HPBMapped. congruence.
    }
    rewrite HgetMappedBEq in *; trivial.
    assert(HrangeEq: getAllPaddrAux [parentBlock] s = getAllPaddrAux [parentBlock] s0).
    {
      simpl. simpl in HsceInRange. rewrite HlookupsEq; trivial. intro Hcontra. subst parentBlock.
      rewrite HlookupStarts in HsceInRange. simpl in HsceInRange. congruence.
    }
    rewrite HrangeEq in *. unfold isBE in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in HblockIsBE. congruence. }
    rewrite HlookupsEq in HblockIsBE; trivial. specialize(Hcons0 part). apply Hcons0; trivial.
  }

  assert(currentPart <> blockStartAddr).
  {
    contradict HcurrNotInDesc. subst blockStartAddr. unfold getPartitions.
    replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
  }

  assert(forall kernel, isKS kernel s
    -> (forall block, In block (filterOptionPaddr (getKSEntries currentPart s))
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s
          -> ~In kernel (getAllPaddrAux [block] s))
    -> exists part pdentry, In part (getPartitions multiplexer s)
        /\ lookup part (memory s) beqAddr = Some (PDT pdentry)
        /\ In kernel (completeListOfKernels (structure pdentry) s)).
  { (* BEGIN partial kernelIsSomePartsConfig s *)
    assert(Hcons0: kernelIsSomePartsConfig s0) by intuition. intros kern HkernIsKS HkernNotShared. unfold isKS in *.
    assert(kern <> blockStartAddr) by (intro; subst kern; rewrite HlookupStarts in *; congruence).
    rewrite HlookupsEq in HkernIsKS; trivial. specialize(Hcons0 kern HkernIsKS).
    destruct Hcons0 as [part [pdentry (HpartIsPart & HlookupPart & HkernIsConfig)]].
    assert(HcomplEq: completeListOfKernels (structure pdentry) s = completeListOfKernels (structure pdentry) s0).
    { apply HcomplKernLEq with part; assumption. }
    assert(HkernIsConfigB: In kern (getConfigBlocks part s0)).
    { rewrite completeKernListIsConfig with (pdentry:=pdentry); trivial; intuition. }
    apply HgetPartsImplRev in HpartIsPart as Hparts0.
    assert(HkernNotShareds0: forall block, In block (filterOptionPaddr (getKSEntries currentPart s0))
      -> sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s0
      -> ~In kern (getAllPaddrAux [block] s0)).
    {
      intros block HblockMapped HPDchildB. rewrite <-HgetKSEq in HblockMapped; trivial.
      unfold sh1entryPDchild in *. assert(HbeqSh1Start: CPaddr (block + sh1offset) <> blockStartAddr).
      { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStart in *. congruence. }
      rewrite <-HlookupsEq in HPDchildB; trivial. specialize(HkernNotShared block HblockMapped HPDchildB).
      simpl. contradict HkernNotShared. simpl. rewrite HlookupsEq; trivial. intro. subst block.
      rewrite HlookupStart in *. simpl in HkernNotShared. congruence.
    }
    assert(HpartNotSub: ~In part (getPartitions blockStartAddr s0)).
    {
      intro Hcontra. assert(HkernIsConfigP: In kern (getConfigPaddr part s0)).
      {
        unfold getConfigPaddr. apply in_or_app. right.
        assert(HconfigAreBE: forall block, In block (getConfigBlocks part s0) -> isBE block s0).
        { intro. apply configBlocksAreBE. }
        induction (getConfigBlocks part s0); simpl; simpl in HkernIsConfigB; simpl in HconfigAreBE; try(congruence).
        assert(forall block, In block l -> isBE block s0).
        { intros. apply HconfigAreBE; auto. }
        assert(Hor: a = a \/ In a l) by auto. specialize(HconfigAreBE a Hor). unfold isBE in *.
        destruct (lookup a (memory s0) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        apply in_or_app. destruct HkernIsConfigB as [Heq | HkernIsConfigB]; auto. subst a. left.
        assert(Constants.kernelStructureTotalLength > 0).
        {
          unfold Constants.kernelStructureTotalLength. unfold CIndex. rewrite nextoffsetVal. cbn.
          pose proof Constants.maxIdxBiggerThanMinBlock. destruct (Compare_dec.le_dec 25 maxIdx); try(lia).
          simpl. lia.
        }
        apply IL.getAllPaddrBlockAuxIncl; lia.
      }
      assert(HkernUsedStart: In kern (getUsedPaddr blockStartAddr s0)).
      {
        unfold getUsedPaddr. apply in_or_app. destruct (beqAddr blockStartAddr part) eqn:HbeqParts.
        - rewrite <-beqAddrTrue in HbeqParts. subst part. auto.
        - rewrite <-beqAddrFalse in *.
          assert(HstartIsAnc: In blockStartAddr (filterOptionPaddr (completeParentsList part s0))).
          {
            apply getPartitionsGivesAncestor with (maxAddr+2); try(unfold isPDT; rewrite HlookupPart); trivial;
              intuition.
          }
          right. revert HstartIsAnc. apply configAddrMappedInAncestor; trivial; intuition.
      }
      assert(HkernMappedCurr: In kern (getMappedPaddr currentPart s0)).
      {
        specialize(HVSs0 currentPart blockStartAddr). apply HVSs0; assumption.
      }
      apply IL.mappedAddrIsInMappedBlock in HkernMappedCurr.
      destruct HkernMappedCurr as [block (HblockMapped & HkernInBlock)].
      assert(Hsh1: exists child, sh1entryPDchild (CPaddr (block+sh1offset)) child s0).
      {
        assert(HblockIsBE: isBE block s0).
        {
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)]. unfold isBE.
          rewrite Hlookup. trivial.
        }
        assert(Hsh1IsSHE: wellFormedFstShadowIfBlockEntry s0) by intuition. specialize(Hsh1IsSHE block HblockIsBE).
        unfold isSHE in *. unfold sh1entryPDchild.
        destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). exists (PDchild s1). reflexivity.
      }
      destruct Hsh1 as [child HPDchildB]. destruct (beqAddr child nullAddr) eqn:HbeqChildNull.
      - rewrite <-beqAddrTrue in HbeqChildNull. subst child.
        assert(Hshared: sharedBlockPointsToChild s0) by intuition.
        assert(Hsh1: sh1entryAddr block (CPaddr (block+sh1offset)) s0).
        {
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
          unfold sh1entryAddr. rewrite Hlookup. reflexivity.
        }
        specialize(Hshared currentPart blockStartAddr kern block (CPaddr (block+sh1offset)) HcurrIsParts0
          HstartIsChilds0 HkernUsedStart HkernInBlock HblockMapped Hsh1).
        destruct Hshared as [HcontraB | HPDflagB].
        {
          unfold sh1entryPDchild in *.
          destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). rewrite <-HPDchildB in *. assert(isPADDR nullAddr s0) by intuition.
          unfold isPADDR in *. subst blockStartAddr. rewrite HlookupStart in *. congruence.
        }
        assert(HstartBIsPDT: PDTIfPDFlag s0) by intuition.
        assert(HcheckChildB: true = checkChild block s0 (CPaddr (block+sh1offset))
          /\ sh1entryAddr block (CPaddr (block+sh1offset)) s0).
        {
          split; trivial. unfold checkChild. apply IL.mappedBlockIsBE in HblockMapped.
          destruct HblockMapped as [bentry (Hlookup & _)]. rewrite Hlookup. unfold sh1entryPDflag in *.
          destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). assumption.
        }
        specialize(HstartBIsPDT block (CPaddr (block+sh1offset)) currentPart HcurrIsParts0 HblockMapped HcheckChildB).
        destruct HstartBIsPDT as (_ & _ & [startaddr (Hstart & HstartBIsPDT)]).
        assert(Htypes: blocksAddressesTypes s0) by intuition.
        assert(Hend: exists endaddr, bentryEndAddr block endaddr s0).
        {
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
          unfold bentryEndAddr. rewrite Hlookup. exists (endAddr (blockrange bentry)). reflexivity.
        }
        destruct Hend as [endaddr Hend]. assert(Hloc: childBlockNullIfChildNull s0) by intuition.
        specialize(Hloc currentPart block (CPaddr (block+sh1offset)) HcurrIsParts0 HblockMapped Hsh1 HPDchildB).
        assert(HlocW: sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) nullAddr s0).
        {
          unfold sh1entryInChildLocation in *. unfold sh1entryInChildLocationWeak.
          destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence).
          destruct v; try(congruence). destruct Hloc. assumption.
        }
        specialize(Htypes block startaddr endaddr currentPart HcurrIsParts0 HblockMapped Hstart Hend HlocW).
        assert(isPDT startaddr s0).
        {
          unfold entryPDT in *. apply IL.mappedBlockIsBE in HblockMapped as HlookupBlock. unfold bentryStartAddr in *.
          destruct HlookupBlock as [bentry (HlookupBlock & _)]. rewrite HlookupBlock in *. rewrite <-Hstart in *.
          unfold isPDT. destruct (lookup startaddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
          trivial.
        }
        assert(~isKS startaddr s0).
        {
          unfold isPDT in *. unfold isKS. destruct (lookup startaddr (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). auto.
        }
        assert(~(forall addr, In addr (getAllPaddrBlock startaddr endaddr)
          -> lookup addr (memory s0) beqAddr = None)).
        {
          intro Hnone. assert(HstartIn: In startaddr (getAllPaddrBlock startaddr endaddr)).
          {
            assert(HPflag: bentryPFlag block true s0).
            {
              unfold bentryPFlag. apply IL.mappedBlockIsBE in HblockMapped.
              destruct HblockMapped as [bentry (Hlookup & Hpre)]. rewrite Hlookup. auto.
            }
            assert(HwellB: wellFormedBlock s0) by intuition.
            specialize(HwellB block startaddr endaddr HPflag Hstart Hend). destruct HwellB.
            apply IL.getAllPaddrBlockIncl; lia.
          }
          specialize(Hnone startaddr HstartIn). unfold isPDT in *. rewrite Hnone in *. congruence.
        }
        destruct Htypes as [(HcontraB & _) | [(_ & Hrange) | HcontraB]]; try(exfalso; congruence).
        unfold isPDT in *. destruct (beqAddr kern startaddr) eqn:HbeqKernStart.
        + rewrite <-beqAddrTrue in HbeqKernStart. subst kern.
          destruct (lookup startaddr (memory s0) beqAddr); try(congruence). destruct v; try(congruence).
        + unfold bentryStartAddr in *. unfold bentryEndAddr in *. apply IL.mappedBlockIsBE in HblockMapped.
          destruct HblockMapped as [bentry (Hlookup & _)]. simpl in HkernInBlock. rewrite Hlookup in *.
          rewrite <-Hstart in *. rewrite <-Hend in *. rewrite app_nil_r in *. rewrite <-beqAddrFalse in *.
          specialize(Hrange kern (conj HkernInBlock HbeqKernStart)). rewrite Hrange in *. congruence.
      - assert(HchildIsChild: pdchildIsPDT s0) by intuition. rewrite <-beqAddrFalse in *.
        assert(Hsh1: sh1entryAddr block (CPaddr (block + sh1offset)) s0).
        {
          apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
          unfold sh1entryAddr. rewrite Hlookup. reflexivity.
        }
        specialize(HchildIsChild currentPart block (CPaddr (block+sh1offset)) child HcurrIsParts0 HblockMapped Hsh1
          HPDchildB HbeqChildNull). assert(child = blockStartAddr).
        {
          destruct (beqAddr child blockStartAddr) eqn:HbeqChildren; try(rewrite beqAddrTrue; assumption). exfalso.
          rewrite <-beqAddrFalse in *. apply not_eq_sym in HbeqChildren.
          assert(HPI: verticalSharing s0) by assumption.
          specialize(HPIs0 currentPart blockStartAddr child HcurrIsParts0 HstartIsChilds0 HchildIsChild HbeqChildren
            kern HkernUsedStart).
          assert(HPDflagB: sh1entryPDflag (CPaddr (block + sh1offset)) false s0).
          {
            assert(Hres: PDflagMeansNoChild s0) by intuition. assert(HblockIsBE: isBE block s0).
            {
              apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)]. unfold isBE.
              rewrite Hlookup. trivial.
            }
            specialize(Hres block HblockIsBE). unfold sh1entryPDchild in *. unfold sh1entryPDflag in *.
            destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence). destruct (PDflag s1); trivial. exfalso.
            assert(HeqTriv: true = true) by reflexivity. specialize(Hres HeqTriv). rewrite <-Hres in *. congruence.
          }
          assert(Hstart: exists startaddr, bentryStartAddr block startaddr s0).
          {
            apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
            unfold bentryStartAddr. rewrite Hlookup. exists (startAddr (blockrange bentry)). reflexivity.
          }
          destruct Hstart as [startaddr Hstart].
          assert(Hloc: exists blockChild, sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) blockChild s0).
          {
            unfold sh1entryInChildLocationWeak. unfold sh1entryPDchild in *.
            destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). exists (inChildLocation s1). reflexivity.
          }
          destruct Hloc as [blockChild Hloc]. destruct (beqAddr blockChild nullAddr) eqn:HbeqBCNull.
          - rewrite <-beqAddrTrue in HbeqBCNull. subst blockChild.
            assert(HsharedKern: sharedBlockNoPDflagNoLocIsKern s0) by intuition.
            specialize(HsharedKern currentPart block child startaddr HcurrIsParts0 HblockMapped HPDchildB
              HbeqChildNull HPDflagB Hloc Hstart). destruct HsharedKern as (_ & HnothingShared & HdeadAddrs).
            specialize(HnothingShared kern blockStartAddr HkernInBlock HstartIsChilds0). unfold getUsedPaddr in *.
            apply in_app_or in HkernUsedStart.
            destruct HkernUsedStart as [HkernConfigStart | HcontraB]; try(congruence).
            assert(HkernConfInNoChild: forall childS, In childS (getChildren blockStartAddr s0)
              -> ~In kern (getUsedPaddr childS s0)).
            {
              assert(Hres: configAddrNotMappedInChild s0) by intuition. intros childS HchildSIsChild.
              specialize(Hres blockStartAddr childS kern HstartIsParts0 HchildSIsChild HkernConfigStart).
              assumption.
            }
            assert(part = blockStartAddr).
            {
              unfold getPartitions in Hcontra. replace (maxAddr+2) with (S (maxAddr+1)) in Hcontra; try(lia).
              simpl in Hcontra. destruct Hcontra as [Hres | Hcontra]; auto. exfalso.
              assert(HnotInTree: forall grandchildS desc n, In grandchildS (getPartitions multiplexer s0)
                -> ~In kern (getUsedPaddr grandchildS s0)
                -> In desc (getPartitionsAux n grandchildS s0)
                -> ~In kern (getUsedPaddr desc s0)).
              {
                intros grandchildS desc n. revert grandchildS.
                induction n; simpl; intros grandchildS HgcIsPart HkernNotUsedGC HdescIsDesc; try(exfalso; congruence).
                destruct HdescIsDesc as [Heq | HdescIsDesc]; try(subst desc; assumption).
                assert(HchildenAreParts: forall grgrchildS, In grgrchildS (getChildren grandchildS s0)
                  -> In grgrchildS (getPartitions multiplexer s0)).
                { intros. apply IL.childrenPartitionInPartitionList with grandchildS; trivial; intuition. }
                assert(HkernNotInChilden: forall grgrchildS, In grgrchildS (getChildren grandchildS s0)
                  -> ~In kern (getUsedPaddr grgrchildS s0)).
                {
                  intros grgrchildS HgrgrIsChild HkernUsedGrgr. unfold getUsedPaddr in *.
                  specialize(HVSs0 grandchildS grgrchildS HgcIsPart HgrgrIsChild kern HkernUsedGrgr).
                  apply Lib.in_app_or_neg in HkernNotUsedGC. destruct HkernNotUsedGC. congruence.
                }
                induction (getChildren grandchildS s0); simpl in HdescIsDesc; try(exfalso; congruence).
                simpl in HchildenAreParts. simpl in HkernNotInChilden.
                assert(HchildenArePartsRec: forall grgrchildS, In grgrchildS l
                  -> In grgrchildS (getPartitions multiplexer s0)).
                { intros. apply HchildenAreParts; auto. }
                assert(HkernNotInChildenRec: forall grgrchildS, In grgrchildS l
                  -> ~In kern (getUsedPaddr grgrchildS s0)).
                { intros. apply HkernNotInChilden; auto. }
                assert(Htriv: a = a \/ In a l) by auto. specialize(HchildenAreParts a Htriv).
                specialize(HkernNotInChilden a Htriv). apply in_app_or in HdescIsDesc.
                destruct HdescIsDesc as [HdescIsDescA | HdescIsDescRec]; auto. apply IHn with a; trivial.
              }
              assert(~In kern (getConfigPaddr part s0)).
              {
                assert(HchildenAreParts: forall childS, In childS (getChildren blockStartAddr s0)
                  -> In childS (getPartitions multiplexer s0)).
                { intros. apply IL.childrenPartitionInPartitionList with blockStartAddr; trivial; intuition. }
                induction (getChildren blockStartAddr s0); simpl in Hcontra; try(exfalso; congruence).
                simpl in HkernConfInNoChild. simpl in HchildenAreParts. assert(Htriv: a = a \/ In a l) by auto.
                assert(HkernConfInNoChildRec: forall childS, In childS l -> ~ In kern (getUsedPaddr childS s0)).
                { intros. apply HkernConfInNoChild; auto. }
                assert(HchildenArePartsRec: forall childS, In childS l -> In childS (getPartitions multiplexer s0)).
                { intros. apply HchildenAreParts; auto. }
                specialize(HkernConfInNoChild a Htriv). specialize(HchildenAreParts a Htriv).
                apply in_app_or in Hcontra. destruct Hcontra as [HcontraA | HcontraRec]; auto.
                specialize(HnotInTree a part (maxAddr+1) HchildenAreParts HkernConfInNoChild HcontraA).
                unfold getUsedPaddr in *. apply Lib.in_app_or_neg in HnotInTree. destruct HnotInTree. assumption.
              }
              congruence.
            }
            subst part. assert(HkernUsedStart: In kern (getUsedPaddr blockStartAddr s0)).
            { unfold getUsedPaddr. apply in_or_app. auto. }
            specialize(HPI currentPart blockStartAddr HcurrIsParts0 HstartIsChilds0 kern HkernUsedStart).
            apply IL.mappedAddrIsInMappedBlock in HPI. destruct HPI as [blockP (HblockPMapped & HkernInBlockP)].
            assert(HPDchildP: usedPaddrAreShared s0) by intuition.
            assert(HkernUsedPartialStart: In kern (getAllPaddrConfigAux (getConfigBlocks blockStartAddr s0) s0
              ++ getMappedPaddr blockStartAddr s0)).
            {
              apply in_or_app. left.
              induction (getConfigBlocks blockStartAddr s0); simpl in HkernIsConfigB; try(exfalso; congruence).
              simpl. destruct HkernIsConfigB as [Heq | HkernIsConfigB].
              - subst a. destruct (lookup kern (memory s0) beqAddr); try(exfalso; congruence).
                destruct v; try(exfalso; congruence). apply in_or_app. left. rewrite kernelStructureTotalLengthVal.
                apply IL.getAllPaddrBlockAuxIncl; lia.
              - destruct (lookup a (memory s0) beqAddr); auto. destruct v; auto. apply in_or_app. auto.
            }
            specialize(HPDchildP blockStartAddr currentPart blockP kern HcurrIsParts0 HstartIsChilds0
              HkernUsedPartialStart HblockPMapped HkernInBlockP). unfold getMappedBlocks in HblockPMapped.
            apply InFilterPresentInList in HblockPMapped.
            specialize(HkernNotShareds0 blockP HblockPMapped HPDchildP). congruence.
          - rewrite <-beqAddrFalse in *. contradict HPIs0.
            assert(HkernMappedChild: sharedBlocksAdressesAreAllMappedInChild s0) by intuition.
            specialize(HkernMappedChild currentPart block (CPaddr (block+sh1offset)) blockChild child HcurrIsParts0
              HblockMapped Hsh1 HPDchildB Hloc HbeqChildNull HbeqBCNull kern HkernInBlock).
            unfold getUsedPaddr. apply in_or_app. auto.
        }
        subst child. unfold getMappedBlocks in HblockMapped. apply InFilterPresentInList in HblockMapped.
        specialize(HkernNotShareds0 block HblockMapped HPDchildB). congruence.
    }
    destruct Hparts0 as [HpartIsParts | Hcontra]; try(exfalso; congruence). exists part. exists pdentry.
    assert(part <> blockStartAddr).
    {
      intro. subst part. contradict HpartNotSub. unfold getPartitions.
      replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
    }
    rewrite HlookupsEq; trivial. rewrite HcomplEq; auto.
    (* END partial kernelIsSomePartsConfig s *)
  }

  assert(HpaddrConfigEq: forall l, getAllPaddrConfigAux l s = getAllPaddrConfigAux l s0).
  {
    intro l. induction l; simpl; trivial. rewrite IHl. destruct (beqAddr a blockStartAddr) eqn:HbeqAStart.
    - rewrite <-beqAddrTrue in HbeqAStart. subst a. rewrite HlookupStart. rewrite HlookupStarts. reflexivity.
    - rewrite <-beqAddrFalse in *. rewrite HlookupsEq; trivial.
  }

  assert(PDTisNoConfigInChild s).
  { (* BEGIN PDTisNoConfigInChild s *)
    assert(Hcons0: PDTisNoConfigInChild s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros pdparent child pdentry block sh1entryaddr addr HparentIsPart HchildIsChild HlookupChild HblockMapped
      Hsh1 HPDflagB HaddrInBlock. assert(child <> blockStartAddr).
    { intro. subst child. congruence. }
    apply HgetPartsImpl in HparentIsPart. assert(pdparent <> blockStartAddr).
    {
      intro. subst pdparent. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in HblockMapped. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. apply HgetChildrenImpl in HchildIsChild.
    rewrite HlookupsEq in HlookupChild; trivial. unfold sh1entryAddr in *. simpl in HaddrInBlock.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    { apply HlookupsEq. intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupBlockEq in *. unfold sh1entryPDflag in *. assert(sh1entryaddr <> blockStartAddr).
    { intro. subst sh1entryaddr. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDflagB; trivial. specialize(Hcons0 pdparent child pdentry block sh1entryaddr addr
      HparentIsPart HchildIsChild HlookupChild HblockMapped Hsh1 HPDflagB HaddrInBlock).
    rewrite HgetConfigBEq; trivial. rewrite HpaddrConfigEq; trivial.
    (* END PDTisNoConfigInChild s *)
  }

  assert(PDTisNoConfigInPart s).
  { (* BEGIN PDTisNoConfigInPart s *)
    assert(Hcons0: PDTisNoConfigInPart s0) by (unfold consistency in *; unfold consistency1 in *; intuition).
    intros pdparent block sh1entryaddr addr HparentIsPart HblockMapped Hsh1 HPDflagB HaddrInBlock.
    apply HgetPartsImpl in HparentIsPart. assert(pdparent <> blockStartAddr).
    {
      intro. subst pdparent. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in HblockMapped. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. unfold sh1entryAddr in *. simpl in HaddrInBlock.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    { apply HlookupsEq. intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupBlockEq in *. unfold sh1entryPDflag in *. assert(sh1entryaddr <> blockStartAddr).
    { intro. subst sh1entryaddr. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDflagB; trivial.
    specialize(Hcons0 pdparent block sh1entryaddr addr HparentIsPart HblockMapped Hsh1 HPDflagB HaddrInBlock).
    rewrite HgetConfigEq; trivial.
    (* END PDTisNoConfigInPart s *)
  }

  assert(usedPaddrAreShared s).
  { (* BEGIN usedPaddrAreShared s *)
    assert(Hcons0: usedPaddrAreShared s0) by intuition.
    intros child pdparent block addr HparentIsPart HchildIsChild HaddrUsedC HblockMapped HaddrInBlock.
    apply HgetPartsImpl in HparentIsPart. assert(pdparent <> blockStartAddr).
    {
      intro. subst pdparent. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in HblockMapped. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. assert(child <> blockStartAddr).
    {
      intro. subst child. unfold getConfigBlocks in *. unfold getMappedPaddr in *. unfold getMappedBlocks in *.
      unfold getKSEntries in *. rewrite HlookupStarts in *. simpl in HaddrUsedC. exfalso; congruence.
    }
    apply HgetChildrenImpl in HchildIsChild. rewrite HgetConfigBEq in *; trivial.
    rewrite HpaddrConfigEq in *; trivial. rewrite HgetMappedPEq in *; trivial. simpl in HaddrInBlock.
    assert(HlookupBlockEq: lookup block (memory s) beqAddr = lookup block (memory s0) beqAddr).
    { apply HlookupsEq. intro. subst block. rewrite HlookupStarts in *. simpl in HaddrInBlock. congruence. }
    rewrite HlookupBlockEq in *.
    specialize(Hcons0 child pdparent block addr HparentIsPart HchildIsChild HaddrUsedC HblockMapped HaddrInBlock).
    unfold sh1entryPDchild in *. rewrite HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *.
    rewrite HlookupStart in *. congruence.
    (* END usedPaddrAreShared *)
  }

  assert(indexIsDistFromKern s).
  { (* BEGIN indexIsDistFromKern s *)
    assert(Hcons0: indexIsDistFromKern s0) by intuition. intros kern idx HkernIsKS HltIdxNbKern. unfold isKS in *.
    assert(kern <> blockStartAddr) by (intro; subst kern; rewrite HlookupStarts in *; congruence).
    rewrite HlookupsEq in HkernIsKS; trivial. specialize(Hcons0 kern idx HkernIsKS HltIdxNbKern).
    unfold bentryBlockIndex in *. rewrite HlookupsEq; trivial. intro Hcontra. rewrite Hcontra in *.
    rewrite HlookupStart in *. congruence.
    (* END indexIsDistFromKern *)
  }

  assert(blockAndNextInSameBlock s).
  { (* BEGIN blockAndNextInSameBlock s *)
    assert(Hcons0: blockAndNextInSameBlock s0) by intuition.
    intros part kern parentBlock HparentIsPart HblockPMapped HkernIsKS HnextInBlockP.
    apply HgetPartsImpl in HparentIsPart. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in HblockPMapped. congruence.
    }
    rewrite HgetMappedBEq in *; trivial. unfold isKS in *. simpl in HnextInBlockP. simpl.
    assert(kern <> blockStartAddr) by (intro; subst kern; rewrite HlookupStarts in *; congruence).
    assert(parentBlock <> blockStartAddr)
      by (intro Hcontra; rewrite Hcontra in *; rewrite HlookupStarts in *; simpl in HnextInBlockP; congruence).
    rewrite HlookupsEq in HkernIsKS; trivial. rewrite HlookupsEq in HnextInBlockP; trivial.
    rewrite HlookupsEq; trivial.
    specialize(Hcons0 part kern parentBlock HparentIsPart HblockPMapped HkernIsKS HnextInBlockP). assumption.
    (* END blockAndNextInSameBlock *)
  }

  assert(HpartialSharedInChild: forall partition block sh1entryaddr blockChild idchild,
    idchild <> blockStartAddr
    -> In partition (getPartitions multiplexer s)
    -> In block (getMappedBlocks partition s)
    -> sh1entryAddr block sh1entryaddr s
    -> sh1entryPDchild sh1entryaddr idchild s
    -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
    -> idchild <> nullAddr
    -> blockChild <> nullAddr
    -> forall addr, In addr (getAllPaddrAux [block] s) -> In addr (getMappedPaddr idchild s)).
  { (* BEGIN sharedBlocksAdressesAreAllMappedInChild s *)
    assert(Hcons0: sharedBlocksAdressesAreAllMappedInChild s0) by intuition.
    intros part block sh1entryaddr blockChild child HbeqChildStart HpartIsPart HblockMapped Hsh1 HPDchildB Hloc
      HbeqChildNull HbeqLocNull addr HaddrInBlock. assert(part <> blockStartAddr).
    {
      intro. subst part. unfold getMappedBlocks in *. unfold getKSEntries in *. rewrite HlookupStarts in *.
      simpl in *. congruence.
    }
    apply HgetPartsImpl in HpartIsPart. unfold sh1entryAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    rewrite HgetMappedBEq in *; trivial. simpl in HaddrInBlock. rewrite HlookupsEq in HaddrInBlock; trivial.
    rewrite HlookupsEq in Hsh1; trivial. unfold sh1entryPDchild in *. unfold sh1entryInChildLocationWeak in *.
    assert(sh1entryaddr <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial. rewrite HlookupsEq in Hloc; trivial.
    specialize(Hcons0 part block sh1entryaddr blockChild child HpartIsPart HblockMapped Hsh1 HPDchildB Hloc
      HbeqChildNull HbeqLocNull addr HaddrInBlock). rewrite HgetMappedPEq; trivial.
    (* END sharedBlocksAdressesAreAllMappedInChild *)
  }

  assert(isPDT currentPart s).
  {
    unfold isPDT. rewrite HlookupsEq; trivial.
  }

  assert(verticalSharing s).
  { (* BEGIN verticalSharing s *)
    intros pdparent child HparentIsPart HchildIsChild. assert(pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. apply HgetChildrenImpl in HchildIsChild.
    rewrite HgetMappedPEq; trivial. specialize(HVSs0 pdparent child HparentIsPart HchildIsChild).
    unfold getUsedPaddr. intros addr HaddrUsedChild. destruct (beqAddr child blockStartAddr) eqn:HbeqChildStart.
    - rewrite <-beqAddrTrue in HbeqChildStart. subst child. unfold getConfigPaddr in *. unfold getMappedPaddr in *.
      unfold getConfigBlocks in *. unfold getMappedBlocks in *. unfold getKSEntries in *. exfalso. simpl in *.
      rewrite HlookupStarts in *. simpl in *. congruence.
    - rewrite <-beqAddrFalse in *. rewrite HgetConfigEq in *; trivial. rewrite HgetMappedPEq in *; trivial.
      apply HVSs0; assumption.
    (* END verticalSharing *)
  }

  assert(partitionsIsolation s).
  { (* BEGIN partitionsIsolation s *)
    intros pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren.
    assert(pdparent <> blockStartAddr).
    { intro. subst pdparent. unfold getChildren in *. rewrite HlookupStarts in *. simpl in *. congruence. }
    apply HgetPartsImpl in HparentIsPart. apply HgetChildrenImpl in Hchild1IsChild.
    apply HgetChildrenImpl in Hchild2IsChild.
    specialize(HPIs0 pdparent child1 child2 HparentIsPart Hchild1IsChild Hchild2IsChild HbeqChildren).
    unfold getUsedPaddr. destruct (beqAddr child1 blockStartAddr) eqn:HbeqChild1Start.
    - rewrite <-beqAddrTrue in HbeqChild1Start. subst child1. unfold getConfigPaddr at 1. unfold getMappedPaddr at 1.
      intros addr HaddrUsed. unfold getConfigBlocks in *. unfold getMappedBlocks in *. unfold getKSEntries in *.
      simpl in *. rewrite HlookupStarts in *. simpl in *. exfalso; congruence.
    - destruct (beqAddr child2 blockStartAddr) eqn:HbeqChild2Start.
      + rewrite <-beqAddrTrue in HbeqChild2Start. subst child2. apply Lib.disjointPermut. unfold getConfigPaddr at 1.
        unfold getMappedPaddr at 1. intros addr HaddrUsed. unfold getConfigBlocks in *. unfold getMappedBlocks in *.
        unfold getKSEntries in *. simpl in *. rewrite HlookupStarts in *. simpl in *. exfalso; congruence.
      + rewrite <-beqAddrFalse in *. rewrite HgetConfigEq; trivial. rewrite HgetMappedPEq; trivial.
        rewrite HgetConfigEq; trivial. rewrite HgetMappedPEq; trivial.
    (* END partitionsIsolation *)
  }

  assert(kernelDataIsolation s).
  { (* BEGIN kernelDataIsolation s *)
    intros part1 part2 Hpart1IsPart Hpart2IsPart. apply HgetPartsImpl in Hpart1IsPart.
    apply HgetPartsImpl in Hpart2IsPart. specialize(HKDIs0 part1 part2 Hpart1IsPart Hpart2IsPart).
    destruct (beqAddr part1 blockStartAddr) eqn:HbeqPart1Start.
    - rewrite <-beqAddrTrue in HbeqPart1Start. subst part1. unfold getAccessibleMappedPaddr.
      unfold getAccessibleMappedBlocks. intros addr HaddrUsed. rewrite HlookupStarts in *. simpl in *.
      exfalso; congruence.
    - destruct (beqAddr part2 blockStartAddr) eqn:HbeqPart2Start.
      + rewrite <-beqAddrTrue in HbeqPart2Start. subst part2. apply Lib.disjointPermut. unfold getConfigPaddr.
        unfold getMappedPaddr. intros addr HaddrUsed. unfold getConfigBlocks in *. unfold getMappedBlocks in *.
        unfold getKSEntries in *. simpl in *. rewrite HlookupStarts in *. simpl in *. exfalso; congruence.
      + rewrite <-beqAddrFalse in *. rewrite HgetConfigEq; trivial. rewrite HgetAccMappedPEq; trivial.
    (* END kernelDataIsolation *)
  }

  assert(HbeqStartNull: blockStartAddr <> nullAddr).
  {
    assert(isPADDR nullAddr s0) by intuition. intro. subst blockStartAddr. unfold isPADDR in *.
    rewrite HlookupStart in *. congruence.
  }

  assert(HnewPartsNotBelowStart: forall part, In part (getPartitions multiplexer s)
    -> part <> blockStartAddr
    -> ~In part (getPartitions blockStartAddr s0)).
  {
    intros part HpartIsPart HbeqParts. contradict HpartIsPart.
    apply getPartitionsExcludesRemovedAddr with s0 blockStartAddr; trivial. intuition.
  }

  assert(HcurrIsParts: In currentPart (getPartitions multiplexer s)).
  {
    apply HgetPartsImplRev in HcurrIsParts0. destruct HcurrIsParts0; try(exfalso; congruence). assumption.
  }

  assert(forall block startBlock endBlock, In block (getMappedBlocks currentPart s)
    -> sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s
    -> bentryStartAddr block startBlock s
    -> bentryEndAddr block endBlock s
    -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
        -> ~In addr (getPartitions multiplexer s)
            /\ (forall part, In part (getPartitions multiplexer s)
                -> ~In addr (filterOptionPaddr (getKSEntries part s))
                    /\ ~In addr (getConfigPaddr part s))
            /\ (forall child, In child (getChildren currentPart s) -> ~ In addr (getMappedPaddr child s))
            /\ (isBE addr s -> addr + scoffset < endBlock)
            /\ (isKS addr s -> addr + nextoffset < endBlock)
            /\ (forall block: paddr, isBE block s -> addr = CPaddr (block+sh1offset)
                  -> In block (getAllPaddrBlock startBlock endBlock))
            /\ (forall block: paddr, isBE block s -> addr = CPaddr (block+scoffset)
                  -> In block (getAllPaddrBlock startBlock endBlock))
            /\ addr <> nullAddr)).
  {
    intros block startBlock endBlock HblockMapped HPDchildB Hstart Hend addr HaddrInRange.
    unfold bentryStartAddr in *. assert(block <> blockStartAddr).
    { intro. subst block. rewrite HlookupStarts in *. congruence. }
    assert(Hsh1: sh1entryAddr block (CPaddr (block+sh1offset)) s0).
    {
      unfold sh1entryAddr. rewrite <-HlookupsEq; trivial. destruct (lookup block (memory s) beqAddr); try(congruence).
      destruct v; congruence.
    }
    rewrite HgetMappedBEq in HblockMapped; trivial.
    assert(HblockIsEntry: In block (filterOptionPaddr (getKSEntries currentPart s0))).
    {
      unfold getMappedBlocks in *. apply InFilterPresentInList in HblockMapped. assumption.
    }
    unfold sh1entryPDchild in *. assert(CPaddr (block+sh1offset) <> blockStartAddr).
    { intro Hcontra. rewrite Hcontra in *. rewrite HlookupStarts in *. congruence. }
    rewrite HlookupsEq in HPDchildB; trivial.
    assert(HPDflagB: sh1entryPDflag (CPaddr (block+sh1offset)) false s0).
    {
      unfold sh1entryPDflag. unfold sh1entryPDchild in *.
      destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1; try(congruence).
      destruct v; try(congruence). destruct (PDflag s1) eqn:HPD; trivial. exfalso.
      assert(HPDflagB: sh1entryPDflag (CPaddr (block+sh1offset)) true s0).
      { unfold sh1entryPDflag. rewrite HlookupSh1. auto. }
      assert(HchildNull: PDflagMeansNoChild s0) by intuition. assert(HblockIsBE: isBE block s0).
      {
        apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)]. unfold isBE.
        rewrite Hlookup. trivial.
      }
      specialize(HchildNull block HblockIsBE HPDflagB). unfold sh1entryPDchild in *. rewrite HlookupSh1 in *.
      rewrite <-HchildNull in *. congruence.
    }
    rewrite HlookupsEq in Hstart; trivial. unfold bentryEndAddr in *. rewrite HlookupsEq in Hend; trivial.
    assert(HlocOrConfig: exists blockChild, sh1entryInChildLocationWeak (CPaddr (block+sh1offset)) blockChild s0
      /\ (blockChild <> nullAddr \/ (In startBlock (getConfigBlocks blockStartAddr s0))
          /\ (forall addr child2, In addr (getAllPaddrAux [block] s0)
                -> In child2 (getChildren currentPart s0)
                -> ~In addr (getMappedPaddr child2 s0))
          /\ (forall (addr:paddr) endaddr part2, bentryEndAddr block endaddr s0
                -> In part2 (getPartitions multiplexer s0)
                -> startBlock+Constants.kernelStructureTotalLength <= addr
                -> addr < endaddr
                -> ~In addr (getConfigPaddr part2 s0)))).
    {
      unfold sh1entryInChildLocationWeak.
      destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr) eqn:HlookupSh1; try(exfalso; congruence).
      destruct v; try(exfalso; congruence). exists (inChildLocation s1). split; trivial.
      destruct (beqAddr (inChildLocation s1) nullAddr) eqn:HbeqLocNull.
      - rewrite <-beqAddrTrue in HbeqLocNull.
        assert(HPDchildBis: sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s0).
        { unfold sh1entryPDchild. rewrite HlookupSh1. assumption. }
        assert(Hloc: sh1entryInChildLocationWeak (CPaddr (block+sh1offset)) nullAddr s0).
        { unfold sh1entryInChildLocationWeak. rewrite HlookupSh1. auto. }
        assert(Hres: sharedBlockNoPDflagNoLocIsKern s0) by intuition.
        specialize(Hres currentPart block blockStartAddr startBlock). right. apply Hres; trivial.
      - rewrite <-beqAddrFalse in *. auto.
    }
    destruct HlocOrConfig as [blockChild (Hloc & HlocOrConfig)].
    assert(HaddrMappedStart: blockChild <> nullAddr -> In addr (getMappedPaddr blockStartAddr s0)).
    {
      intro HbeqLocNull. assert(Hres: sharedBlocksAdressesAreAllMappedInChild s0) by intuition.
      assert(HaddrInBlock: In addr (getAllPaddrAux [block] s0)).
      {
        simpl. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r. assumption.
      }
      specialize(Hres currentPart block (CPaddr (block+sh1offset)) blockChild blockStartAddr HcurrIsParts0
        HblockMapped Hsh1 HPDchildB Hloc HbeqStartNull HbeqLocNull addr HaddrInBlock). assumption.
    }
    assert(HconfigIsKS: forall addr part, In part (getPartitions multiplexer s0)
      -> In addr (getConfigBlocks part s0) -> isKS addr s0).
    { intros addrB part. apply configBlocksAreKS; intuition. }
    assert(~In addr (getPartitions multiplexer s)).
    {
      intro HaddrIsPart. destruct HlocOrConfig as [HbeqLocNull | HstartIsConfig].
      - specialize(HaddrMappedStart HbeqLocNull). assert(addr <> blockStartAddr).
        {
          intro. subst addr. assert(HpartNotMapped: partitionNotAutoMapped s0) by intuition.
          specialize(HpartNotMapped blockStartAddr HstartIsParts0). congruence.
        }
        assert(HaddrInRemovedParts: In addr (getPartitions blockStartAddr s0)).
        {
          apply HgetPartsImpl in HaddrIsPart.
          apply mappedAddrIsInDescendants; trivial; try(apply IL.noDupKSMappedImpl). 1-13: intuition.
        }
        apply HnewPartsNotBelowStart in HaddrIsPart; congruence.
      - destruct HstartIsConfig as (HstartIsConfig & _).
        assert(HpropsOrAddr: addr = blockStartAddr \/ ~In addr (getPartitions blockStartAddr s0)).
        {
          destruct (beqAddr addr blockStartAddr) eqn:HbeqAddrStart; try(rewrite <-beqAddrTrue in *; auto).
          rewrite <-beqAddrFalse in *. right. apply HnewPartsNotBelowStart; assumption.
        }
        apply HgetPartsImpl in HaddrIsPart. apply HconfigIsKS in HstartIsConfig; trivial. assert(isPDT addr s0).
        { apply IL.partitionsArePDT; trivial; intuition. }
        assert(Htypes: blocksAddressesTypes s0) by intuition.
        destruct (beqAddr blockChild nullAddr) eqn:HbeqBCNull.
        + rewrite <-beqAddrTrue in HbeqBCNull. subst blockChild.
          specialize(Htypes block startBlock endBlock currentPart HcurrIsPart HblockMapped Hstart Hend Hloc).
          unfold isKS in *. destruct Htypes as [(_ & HlookupRangeB) | [(Hcontra & _) | Hcontra]].
          * apply HlookupRangeB in HaddrInRange. unfold isPDT in *. unfold isBE in *. unfold isSHE in *.
            unfold isSCE in *. unfold isPADDR in *. destruct (lookup addr (memory s0) beqAddr); try(congruence).
            destruct v; try(congruence).
            destruct HaddrInRange as [Hcontra | [Hcontra | [Hcontra | [Hcontra | Hcontra]]]]; congruence.
          * unfold isPDT in *. destruct (lookup startBlock (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          * apply Hcontra in HaddrInRange. unfold isPDT in *. rewrite HaddrInRange in *. congruence.
        + rewrite <-beqAddrFalse in *. specialize(HaddrMappedStart HbeqBCNull).
          destruct (beqAddr addr blockStartAddr) eqn:HbeqAddrStart.
          * rewrite <-beqAddrTrue in HbeqAddrStart. subst addr.
            assert(HaddrInBlock: In blockStartAddr (getAllPaddrAux [block] s0)).
            {
              simpl. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
              destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r. assumption.
            }
            assert(block = blockToDeleteInCurrPartAddr).
            {
              destruct (beqAddr block blockToDeleteInCurrPartAddr) eqn:HbeqBlocks;
                try(rewrite beqAddrTrue; assumption). rewrite <-beqAddrFalse in *.
              assert(HnoDupMappedP: noDupMappedPaddrList s0) by intuition.
              pose proof (DisjointPaddrInPart currentPart block blockToDeleteInCurrPartAddr blockStartAddr s0
                HnoDupMappedP HcurrIsPart HblockMapped HBTDMapped HbeqBlocks HaddrInBlock) as Hcontra. exfalso.
              contradict Hcontra. simpl. rewrite HlookupBTD in *. rewrite app_nil_r. rewrite <-HstartBTDs0.
              rewrite <-HendBTDs0. apply IL.getAllPaddrBlockIncl; lia.
            }
            subst block. unfold sh1entryPDflag in *.
            destruct (lookup (CPaddr (blockToDeleteInCurrPartAddr + sh1offset)) (memory s0) beqAddr); try(congruence).
            destruct v; congruence.
          * rewrite <-beqAddrFalse in *. destruct HpropsOrAddr as [Hcontra | HaddrNotDesc]; try(congruence).
            contradict HaddrNotDesc. apply parentsListGivesPartitions; trivial. 1-5: intuition. simpl. right.
            apply mappedAddrIsInBloodline; trivial; try(apply IL.noDupKSMappedImpl); intuition.
    }
    assert(forall part, In part (getPartitions multiplexer s)
      -> ~In addr (filterOptionPaddr (getKSEntries part s)) /\ ~In addr (getConfigPaddr part s)).
    {
      intros part HpartIsPart. destruct (beqAddr part blockStartAddr) eqn:HbeqParts.
      - rewrite <-beqAddrTrue in HbeqParts. subst part. unfold getKSEntries. unfold getConfigPaddr.
        unfold getConfigBlocks. simpl getAllPaddrPDTAux. rewrite HlookupStarts. simpl. auto.
      - rewrite <-beqAddrFalse in *. destruct (beqAddr blockChild nullAddr) eqn:HbeqBCNull.
        + rewrite <-beqAddrTrue in HbeqBCNull. subst blockChild.
          destruct HlocOrConfig as [Hcontra | (HstartBIsConfig & HrangeNotShared & HdeadAddrs)];
            try(exfalso; congruence).
          assert(Hsimpl: ~ In addr (getConfigPaddr part s)
            -> ~ In addr (filterOptionPaddr (getKSEntries part s)) /\ ~ In addr (getConfigPaddr part s)).
          {
            intro HaddrNotConfig. split; trivial. contradict HaddrNotConfig. revert HaddrNotConfig.
            apply inclKSEntriesConfig; intuition.
          }
          apply Hsimpl. rewrite HgetConfigEq; trivial. clear Hsimpl. clear HaddrMappedStart.
          assert(HaddrInBlock: In addr (getAllPaddrAux [block] s0)).
          {
            simpl. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite app_nil_r. rewrite <-Hstart. rewrite <-Hend. assumption.
          }
          specialize(HrangeNotShared addr blockStartAddr HaddrInBlock HstartIsChilds0). intro HaddrIsConfig.
          assert(HpartNotDesc: ~In part (getPartitions blockStartAddr s0)).
          { apply HnewPartsNotBelowStart; trivial. }
          apply HgetPartsImpl in HpartIsPart.
          assert(HstartNotAnc: ~In blockStartAddr (filterOptionPaddr (completeParentsList part s0))).
          {
            contradict HpartNotDesc. apply parentsListGivesPartitions; trivial. 1-5: intuition.
            simpl. auto.
          }
          assert(HaddrMappedCurr: In addr (getMappedPaddr currentPart s0)).
          { apply IL.addrInBlockIsMapped with block; trivial. }
          assert(HpropsOr: In currentPart (part::filterOptionPaddr (completeParentsList part s0))).
          {
            apply configAddressesBloodline with addr; trivial; try(apply IL.noDupKSMappedImpl); intuition.
          }
          specialize(HdeadAddrs addr endBlock part Hend HpartIsPart).
          assert(HaddrConfigStart: In addr (getConfigPaddr blockStartAddr s0)).
          {
            unfold getConfigPaddr. apply in_or_app. right. apply addrInKernIsConfig with startBlock; trivial.
            - unfold isBE. apply HconfigIsKS in HstartBIsConfig; trivial. unfold isKS in *.
              destruct (lookup startBlock (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence). trivial.
            - apply IL.getAllPaddrBlockInclRev in HaddrInRange.
              destruct HaddrInRange as (HlebStartAddr & HltAddrEnd & _).
              destruct (Nat.ltb addr (startBlock+Constants.kernelStructureTotalLength)) eqn:HltAddrKernAddr.
              + apply PeanoNat.Nat.ltb_lt in HltAddrKernAddr. apply IL.getAllPaddrBlockAuxIncl; lia.
              + apply PeanoNat.Nat.ltb_ge in HltAddrKernAddr. exfalso.
                specialize(HdeadAddrs HltAddrKernAddr HltAddrEnd). congruence.
          }
          simpl in HpropsOr. destruct HpropsOr as [HbeqCurrPart | HcurrIsAnc].
          * subst part. assert(HconfigNotUsed: configAddrNotMappedInChild s0) by intuition.
            specialize(HconfigNotUsed currentPart blockStartAddr addr HcurrIsParts0 HstartIsChilds0 HaddrIsConfig).
            contradict HconfigNotUsed. unfold getUsedPaddr. apply in_or_app. auto.
          * assert(Hchild: exists child, pdentryParent child currentPart s0
              /\ In child (getPartitions multiplexer s0)
              /\ In child (part::filterOptionPaddr (completeParentsList part s0))).
            { apply completeParentsListChild; trivial; intuition. }
            destruct Hchild as [child (Hparent & HchildIsPart & HchildIsAnc)].
            assert(HchildIsChild: isChild s0) by intuition. assert(HbeqChildRoot: child <> constantRootPartM).
            {
              intro Hcontra. assert(HparentOfPart: parentOfPartitionIsPartition s0) by intuition.
              unfold pdentryParent in *.
              destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(congruence).
              destruct v; try(congruence). specialize(HparentOfPart child p0 HlookupChild).
              destruct HparentOfPart as (_ & HparentOfRoot & _). specialize(HparentOfRoot Hcontra).
              rewrite HparentOfRoot in *. rewrite Hparent in *.
              assert(isPADDR nullAddr s0) by intuition. unfold isPDT in *. unfold isPADDR in *.
              destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
            }
            specialize(HchildIsChild child currentPart HchildIsPart Hparent HbeqChildRoot).
            assert(HaddrUsedChild: In addr (getUsedPaddr child s0)).
            {
              simpl in HchildIsAnc. unfold getUsedPaddr. apply in_or_app.
              destruct HchildIsAnc as [Heq | HchildIsAnc]; try(subst child; left; assumption). right.
              assert(HparentPart: exists pdparent,
                In child (pdparent::filterOptionPaddr (completeParentsList pdparent s0))
                /\ In pdparent (getPartitions multiplexer s0)
                /\ In addr (getMappedPaddr pdparent s0)).
              {
                unfold completeParentsList in HchildIsAnc. set(succ:= S maxAddr). fold succ in HchildIsAnc.
                cbn -[succ] in HchildIsAnc. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart;
                  try(simpl in HchildIsAnc; exfalso; congruence).
                destruct v; try(simpl in HchildIsAnc; exfalso; congruence).
                destruct (beqAddr part constantRootPartM) eqn:HbeqPartRoot; cbn -[succ] in HchildIsAnc;
                  try(exfalso; congruence). exists (parent p0).
                assert(HparentOfPart: parentOfPartitionIsPartition s0) by intuition.
                specialize(HparentOfPart part p0 HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
                rewrite <-beqAddrFalse in *. specialize(HparentIsPart HbeqPartRoot).
                destruct HparentIsPart as (_ & HparentIsPart). split; try(split); trivial.
                - simpl. destruct HchildIsAnc as [Heq | HchildIsAnc]; auto. right. unfold completeParentsList.
                  apply completeParentsListRecN with succ; trivial; lia.
                - unfold verticalSharing in *. unfold incl in *. apply HVSs0 with part; trivial.
                  + assert(Hres: isChild s0) by intuition. apply Hres; trivial. unfold pdentryParent.
                    rewrite HlookupPart. reflexivity.
                  + unfold getUsedPaddr. apply in_or_app. auto.
              }
              destruct HparentPart as [pdparent (HchildIsAncRec & HparentIsPart & HaddrMappedParent)].
              simpl in HchildIsAncRec. destruct HchildIsAncRec as [Heq | HchildIsAncRec];
                try(subst child; assumption). assert(childPaddrIsIntoParent s0).
              { apply IL.blockInclImpliesAddrIncl; intuition. }
              apply addrBelongToAncestors with pdparent; trivial; intuition.
            }
            assert(In addr (getAllPaddrBlockAux 0 startBlock Constants.kernelStructureTotalLength)).
            {
              apply IL.getAllPaddrBlockInclRev in HaddrInRange.
              destruct HaddrInRange as (HlebStartAddr & HltAddrEnd & _).
              destruct (Nat.ltb addr (startBlock+Constants.kernelStructureTotalLength)) eqn:HltAddrKernAddr.
              - apply PeanoNat.Nat.ltb_lt in HltAddrKernAddr. apply IL.getAllPaddrBlockAuxIncl; lia.
              - apply PeanoNat.Nat.ltb_ge in HltAddrKernAddr. exfalso.
                specialize(HdeadAddrs HltAddrKernAddr HltAddrEnd). congruence.
            }
            assert(child = blockStartAddr).
            {
              destruct (beqAddr child blockStartAddr) eqn:HbeqChildStart; try(rewrite beqAddrTrue; assumption).
              exfalso. rewrite <-beqAddrFalse in *.
              specialize(HPIs0 currentPart child blockStartAddr HcurrIsParts0 HchildIsChild HstartIsChilds0
                HbeqChildStart addr HaddrUsedChild). contradict HPIs0. unfold getUsedPaddr. apply in_or_app.
              left. unfold getConfigPaddr. apply in_or_app. right.
              apply addrInKernIsConfig with startBlock; try(assumption).
              unfold isBE. apply HconfigIsKS in HstartBIsConfig; trivial. unfold isKS in *.
              destruct (lookup startBlock (memory s0) beqAddr); try(congruence).
              destruct v; try(congruence). trivial.
            }
            subst child. simpl in HchildIsAnc. destruct HchildIsAnc; congruence.
        + rewrite <-beqAddrFalse in *. specialize(HaddrMappedStart HbeqBCNull).
          assert(HpartNotInDescStart: ~In part (getPartitions blockStartAddr s0)).
          { apply HnewPartsNotBelowStart; trivial. }
          apply HgetPartsImpl in HpartIsPart. rewrite HgetKSEq; trivial. rewrite HgetConfigEq; trivial.
          apply Decidable.not_or. intro HaddrIn.
          assert(HaddrInConfig: In addr (getConfigPaddr part s0)).
          { destruct HaddrIn; trivial. apply inclKSEntriesConfig; trivial; intuition. }
          clear HaddrIn. assert(HaddrMappedInAllAnc: forall partAnc,
            In partAnc (filterOptionPaddr (completeParentsList blockStartAddr s0))
            -> In addr (getMappedPaddr partAnc s0)).
          {
            intros partAnc HpartAncIsAncStart.
            assert(HpartAncIsPart: In partAnc (getPartitions multiplexer s0)).
            {
              apply IL.partInParentsListIsPartition with (filterOptionPaddr (completeParentsList blockStartAddr s0))
                blockStartAddr; trivial.
              - intuition.
              - apply completeParentsListIsParentsList; trivial. intuition.
            }
            revert HpartAncIsAncStart HaddrMappedStart. apply addrBelongToAncestors; trivial.
            1-5: intuition. apply IL.blockInclImpliesAddrIncl; intuition.
          }
          assert(HaddrMappedMult: In addr (getMappedPaddr multiplexer s0)).
          {
            destruct (beqAddr multiplexer blockStartAddr) eqn:HbeqMultStart.
            - rewrite <-beqAddrTrue in HbeqMultStart. subst blockStartAddr. assumption.
            - rewrite <-beqAddrFalse in *. apply HaddrMappedInAllAnc.
              apply getPartitionsGivesAncestor with (maxAddr+2); trivial. 1-7: intuition.
              unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); try(lia). simpl. auto.
          }
          assert(HpropsOr: In part (filterOptionPaddr (completeParentsList blockStartAddr s0))
              \/ ~In part (filterOptionPaddr (completeParentsList blockStartAddr s0)))
            by (apply Classical_Prop.classic).
          assert(isPDT part s0) by (apply IL.partitionsArePDT; trivial; intuition).
          assert(HaddrInUsed: In addr (getUsedPaddr part s0)).
          { unfold getUsedPaddr. apply in_or_app. auto. }
          destruct HpropsOr as [HpartIsAnc | HpartNotAnc].
          * (* apply HaddrMappedInAllAnc in HpartIsAnc. *)
            assert(Hchild: exists child, In child (getChildren part s0) /\ In addr (getMappedPaddr child s0)).
            {
              assert(Hres: exists child, pdentryParent child part s0
                 /\ In child (getPartitions multiplexer s0)
                 /\ In child (blockStartAddr :: filterOptionPaddr (completeParentsList blockStartAddr s0))).
              {
                apply completeParentsListChild; trivial; intuition.
              }
              destruct Hres as [child (Hparent & HchildIsPart & HchildIsAnc)]. exists child.
              assert(HisChild: isChild s0) by intuition. assert(HbeqChildRoot: child <> constantRootPartM).
              {
                intro Hcontra. unfold pdentryParent in *.
                destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(congruence).
                destruct v; try(congruence). assert(HparentOfPart: parentOfPartitionIsPartition s0) by intuition.
                specialize(HparentOfPart child p0 HlookupChild). destruct HparentOfPart as (_ & HparentOfRoot & _).
                specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *.
                subst part. assert(isPADDR nullAddr s0) by intuition. unfold isPDT in *. unfold isPADDR in *.
                destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
              }
              specialize(HisChild child part HchildIsPart Hparent HbeqChildRoot). split; trivial. simpl in *.
              destruct HchildIsAnc as [HbeqStartChild | HchildIsAnc].
              - subst child. assumption.
              - apply HaddrMappedInAllAnc; assumption.
            }
            destruct Hchild as [child (HchildIsChild & HaddrMappedChild)].
            assert(Hres: configAddrNotMappedInChild s0) by intuition.
            specialize(Hres part child addr HpartIsPart HchildIsChild HaddrInConfig). unfold getUsedPaddr in *.
            apply Lib.in_app_or_neg in Hres. destruct Hres. congruence.
          * assert(HbeqPartRoot: part <> constantRootPartM).
            {
              intro. subst part. contradict HpartNotAnc. unfold multiplexer in HstartIsParts0.
              apply getPartitionsGivesAncestor with (maxAddr+2); trivial; intuition.
            }
            unfold isPDT in *. destruct (lookup part (memory s0) beqAddr) eqn:HlookupPart; try(congruence).
            destruct v; try(congruence). assert(HparentOfPart: parentOfPartitionIsPartition s0) by intuition.
            specialize(HparentOfPart part p0 HlookupPart). destruct HparentOfPart as (HparentIsPart & _).
            specialize(HparentIsPart HbeqPartRoot).
            destruct HparentIsPart as ([parentEntry HlookupParent] & HparentIsPart).
            assert(HpartIsChild: isChild s0) by intuition. assert(Hparent: pdentryParent part (parent p0) s0).
            { unfold pdentryParent. rewrite HlookupPart. reflexivity. }
            specialize(HpartIsChild part (parent p0) HpartIsPart Hparent HbeqPartRoot).
            specialize(HVSs0 (parent p0) part HparentIsPart HpartIsChild addr HaddrInUsed).
            assert(HparentIsAnc: In (parent p0) (filterOptionPaddr (completeParentsList blockStartAddr s0))).
            {
              assert(HbeqParentStart: blockStartAddr <> parent p0).
              {
                intro Hcontra. rewrite <-Hcontra in *. unfold getPartitions in HpartNotInDescStart.
                replace (maxAddr+2) with (S (maxAddr+1)) in HpartNotInDescStart; try(lia). simpl in *.
                apply Decidable.not_or in HpartNotInDescStart.
                destruct HpartNotInDescStart as (_ & HpartNotDescStart).
                contradict HpartNotDescStart. induction (getChildren blockStartAddr s0); simpl in *; try(congruence).
                destruct HpartIsChild as [Heq | HpartIsChild];
                  try(subst a; rewrite PeanoNat.Nat.add_1_r; simpl; auto).
                apply in_or_app. auto.
              }
              assert(Hbloodline: In (parent p0) (filterOptionPaddr (completeParentsList blockStartAddr s0))
                \/ parent p0 = blockStartAddr
                \/ In blockStartAddr (filterOptionPaddr (completeParentsList (parent p0) s0))).
              {
                apply addressesBloodline with addr; trivial; try(apply IL.noDupKSMappedImpl); intuition.
              }
              destruct Hbloodline as [Hres | [Hcontra | Hcontra]]; trivial; exfalso; try(congruence).
              assert(HcontraPart: In blockStartAddr (part::filterOptionPaddr (completeParentsList part s0))).
              {
                assert(HisParentsList: isParentsList s0 (filterOptionPaddr (completeParentsList (parent p0) s0))
                  (parent p0)).
                { apply completeParentsListIsParentsList. intuition. unfold isPDT; rewrite HlookupParent; trivial. }
                assert(HnoDupList: NoDup (filterOptionPaddr (completeParentsList (parent p0) s0))).
                { revert HisParentsList. apply IL.parentOfPartNotInParentsListsTail; intuition. }
                apply IL.lengthNoDupPartitions in HnoDupList. simpl. right.
                unfold completeParentsList in *. replace (S maxAddr) with (maxAddr+1); try(lia). simpl.
                rewrite HlookupPart. rewrite beqAddrFalse in *. rewrite HbeqPartRoot. simpl. right.
                assert(Hleb: maxAddr+1 <= S (S maxAddr)) by lia.
                pose proof (completeParentsListRecEqIfLenLowEnough (parent p0) s0 (maxAddr+1) (S (S maxAddr)) Hleb
                  HnoDupList) as Heq. rewrite Heq. assumption.
              }
              contradict HpartNotInDescStart. revert HcontraPart.
              apply parentsListGivesPartitions; trivial; intuition.
            }
            assert(HotherChild: exists child, pdentryParent child (parent p0) s0
              /\ In child (getPartitions multiplexer s0)
              /\ In child (blockStartAddr :: filterOptionPaddr (completeParentsList blockStartAddr s0))).
            {
              apply completeParentsListChild; trivial; intuition.
            }
            destruct HotherChild as [child (HparentOther & HchildIsPart & HchildIsAnc)].
            assert(HchildIsChild: isChild s0) by intuition. assert(HbeqChildRoot: child <> constantRootPartM).
            {
              unfold pdentryParent in *.
              destruct (lookup child (memory s0) beqAddr) eqn:HlookupChild; try(exfalso; congruence).
              destruct v; try(exfalso; congruence).
              assert(HparentOfPart: parentOfPartitionIsPartition s0) by intuition.
              specialize(HparentOfPart child p1 HlookupChild). destruct HparentOfPart as (_ & HparentOfRoot & _).
              intro Hcontra. specialize(HparentOfRoot Hcontra). rewrite HparentOfRoot in *. rewrite HparentOther in *.
              assert(isPADDR nullAddr s0) by intuition. unfold isPADDR in *. rewrite HlookupParent in *. congruence.
            }
            specialize(HchildIsChild child (parent p0) HchildIsPart HparentOther HbeqChildRoot).
            assert(HbeqPartChild: part <> child).
            {
              intro. subst child. simpl in *. destruct HchildIsAnc; congruence.
            }
            specialize(HPIs0 (parent p0) part child HparentIsPart HpartIsChild HchildIsChild HbeqPartChild addr
              HaddrInUsed). unfold getUsedPaddr in *. apply Lib.in_app_or_neg in HPIs0.
            destruct HPIs0 as (_ & Hcontra).
            contradict Hcontra. simpl in *. destruct HchildIsAnc as [Heq | HchildIsAnc]; try(subst child; assumption).
            apply HaddrMappedInAllAnc; assumption.
    }

    assert(forall child, In child (getChildren currentPart s) -> ~ In addr (getMappedPaddr child s)).
    {
      intros child HchildIsChild. rewrite HgetChildrenEqNotStart in HchildIsChild; trivial.
      destruct (beqAddr child blockStartAddr) eqn:HbeqChildren.
      - rewrite <-beqAddrTrue in HbeqChildren. subst child. unfold getMappedPaddr. unfold getMappedBlocks.
        unfold getKSEntries. rewrite HlookupStarts. simpl. intro. congruence.
      - rewrite <-beqAddrFalse in *. rewrite HgetMappedPEq; trivial.
        destruct (beqAddr blockChild nullAddr) eqn:HbeqBCNull.
        + rewrite <-beqAddrTrue in HbeqBCNull.
          destruct HlocOrConfig as [Hcontra | (_ & Hres & _)]; try(exfalso; congruence).
          assert(HaddrInBlock: In addr (getAllPaddrAux [block] s0)).
          {
            simpl. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
            destruct v; try(exfalso; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r. assumption.
          }
          specialize(Hres addr child HaddrInBlock HchildIsChild). assumption.
        + intro HaddrMappedC. assert(HaddrUsedC : In addr (getUsedPaddr child s0)).
          { unfold getUsedPaddr. apply in_or_app. auto. }
          specialize(HPIs0 currentPart child blockStartAddr HcurrIsParts0 HchildIsChild HstartIsChilds0 HbeqChildren
            addr HaddrUsedC). rewrite <-beqAddrFalse in *. specialize(HaddrMappedStart HbeqBCNull).
          contradict HPIs0. unfold getUsedPaddr. apply in_or_app. auto.
    }

    assert(isBE addr s -> addr + scoffset < endBlock).
    {
      intro HaddrIsBE. assert(Hkern: KernelStructureStartFromBlockEntryAddrIsKS s) by intuition.
      assert(Hblkidx: exists idx, bentryBlockIndex addr idx s).
      {
        unfold bentryBlockIndex. unfold isBE in *.
        destruct (lookup addr (memory s) beqAddr); try(exfalso; congruence). destruct v; try(exfalso; congruence).
        exists (blockindex b0). reflexivity.
      }
      destruct Hblkidx as [idx Hblkidx]. specialize(Hkern addr idx HaddrIsBE Hblkidx). unfold bentryBlockIndex in *.
      destruct (lookup addr (memory s) beqAddr) eqn:HlookupAddr; try(exfalso; congruence).
      destruct v; try(exfalso; congruence).
      assert(idx < kernelStructureEntriesNb) by (rewrite Hblkidx; apply Hidx).
      assert(addr-idx+nextoffset < endBlock).
      {
        assert(Hres: fullKernelIsInOneBlock s0) by intuition.
        assert(HkernInBlock: In (CPaddr (addr-idx)) (getAllPaddrAux [block] s0)).
        {
          assert(HresB: kernInSameBlock s0) by intuition. unfold kernInSameBlock in *.
          apply HresB with currentPart; trivial.
          - simpl. destruct (lookup block (memory s0) beqAddr); try(simpl; congruence).
            destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r. assumption.
          - unfold bentryBlockIndex. assert(~ In addr (getAllPaddrBlock blockStartAddr blockEndAddr)).
            {
              intro Hcontra. apply HlookupRange in Hcontra. congruence.
            }
            rewrite <-HlookupNotRange; trivial. rewrite HlookupAddr. assumption.
        }
        assert(Hkerns0: isKS (CPaddr (addr-idx)) s0).
        {
          unfold isKS in *. rewrite <-HlookupNotRange; trivial. intro Hcontra. apply HlookupRange in Hcontra.
          rewrite Hcontra in *. congruence.
        }
        specialize(Hres currentPart block (CPaddr (addr-idx)) HcurrIsParts0 HblockMapped HkernInBlock Hkerns0).
        assert(HkernEq: ADT.p (CPaddr (addr-idx)) = addr-idx).
        {
          unfold CPaddr. assert(addr <= maxAddr) by (apply Hp).
          destruct (Compare_dec.le_dec (addr - idx) maxAddr); try(lia). reflexivity.
        }
        rewrite HkernEq in Hres. destruct Hres as (HlebNextMax & Hres). unfold CPaddr in Hres.
        destruct (Compare_dec.le_dec (addr - idx + nextoffset) maxAddr); try(lia). simpl in Hres.
        destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
        destruct v; try(exfalso; congruence). rewrite <-Hstart in *. rewrite <-Hend in *. rewrite app_nil_r in *.
        apply IL.getAllPaddrBlockInclRev in Hres. simpl in Hres. apply Hres.
      }
      rewrite scoffsetVal. rewrite nextoffsetVal in *. lia.
    }

    assert(isKS addr s -> addr + nextoffset < endBlock).
    {
      intro HaddrIsKS. assert(Hres: fullKernelIsInOneBlock s) by assumption.
      rewrite <-HgetMappedBEq in HblockMapped; trivial. rewrite <-HlookupsEq in Hstart; trivial.
      rewrite <-HlookupsEq in Hend; trivial. assert(HaddrInBlock: In addr (getAllPaddrAux [block] s)).
      {
        simpl. destruct (lookup block (memory s) beqAddr); try(simpl; congruence).
        destruct v; try(simpl; congruence). rewrite <-Hstart. rewrite <-Hend. rewrite app_nil_r. assumption.
      }
      specialize(Hres currentPart block addr HcurrIsParts HblockMapped HaddrInBlock HaddrIsKS).
      destruct Hres as (HlebNextMax & Hres). unfold CPaddr in Hres.
      destruct (Compare_dec.le_dec (addr + nextoffset) maxAddr); try(lia). simpl in Hres.
      destruct (lookup block (memory s) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-Hstart in *. rewrite <-Hend in *. rewrite app_nil_r in *.
      apply IL.getAllPaddrBlockInclRev in Hres. simpl in Hres. apply Hres.
    }

    assert(addr <> nullAddr).
    {
      intro Hcontra. destruct (beqAddr addr startBlock) eqn:HbeqAddrStartB.
      - rewrite <-beqAddrTrue in HbeqAddrStartB. subst addr. subst startBlock.
        assert(HlastDesc: exists desc blockDesc, In desc (getPartitions multiplexer s0)
          /\ In blockDesc (getMappedBlocks desc s0) /\ bentryStartAddr blockDesc nullAddr s0
          /\ sh1entryInChildLocationWeak (CPaddr (blockDesc+sh1offset)) nullAddr s0).
        {
          apply lastDescendantBlock with currentPart block; trivial; intuition.
        }
        destruct HlastDesc as [desc [blockDesc (HdescIsPart & HBDMapped & HstartBD & HlocBD)]].
        assert(Htypes: blocksAddressesTypes s0) by intuition.
        assert(HendBD: exists endBD, bentryEndAddr blockDesc endBD s0).
        {
          unfold bentryEndAddr. unfold bentryStartAddr in *.
          destruct (lookup blockDesc (memory s0) beqAddr); try(exfalso; congruence).
          destruct v; try(exfalso; congruence). exists (endAddr (blockrange b0)). reflexivity.
        }
        destruct HendBD as [endBD HendBD].
        specialize(Htypes blockDesc nullAddr endBD desc HdescIsPart HBDMapped HstartBD HendBD HlocBD).
        assert(Hnull: isPADDR nullAddr s0) by intuition. unfold isPADDR in *.
        destruct Htypes as [(HKS & _) | [(HPDT & _) | Hnone]].
        + unfold isKS in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        + unfold isPDT in *. destruct (lookup nullAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
        + assert(HnullInBlock: In nullAddr (getAllPaddrBlock nullAddr endBD)).
          {
            assert(HPflagBD: bentryPFlag blockDesc true s0).
            {
              apply IL.mappedBlockIsBE in HBDMapped. destruct HBDMapped as [bentry (Hlookup & Hpres)].
              unfold bentryPFlag. rewrite Hlookup. auto.
            }
            assert(HwellBD: wellFormedBlock s0) by intuition.
            specialize(HwellBD blockDesc nullAddr endBD HPflagBD HstartBD HendBD). destruct HwellBD as (HwellBD & _).
            apply IL.getAllPaddrBlockIncl; lia.
          }
          apply Hnone in HnullInBlock. rewrite HnullInBlock in *. congruence.
      - rewrite <-beqAddrFalse in *. subst addr. apply paddrNeqNatNeqEquiv in HbeqAddrStartB.
        cbn in HbeqAddrStartB. apply IL.getAllPaddrBlockInclRev in HaddrInRange. cbn in HaddrInRange.
        destruct HaddrInRange as (Hcontra & _). lia.
    }

    assert(Hrange: getAllPaddrAux [block] s0 = getAllPaddrBlock startBlock endBlock).
    {
      simpl. destruct (lookup block (memory s0) beqAddr); try(exfalso; congruence).
      destruct v; try(exfalso; congruence). rewrite <-Hstart. rewrite <-Hend. apply app_nil_r.
    }

    assert(forall block, isBE block s -> addr = CPaddr (block+sh1offset)
      -> In block (getAllPaddrBlock startBlock endBlock)).
    {
      intros blockB HblockBIsBE HaddrEq. subst addr. rewrite <-Hrange in *.
      assert(Hres: blockAndSh1InSameBlock s0) by intuition. specialize(Hres currentPart). apply Hres; trivial.
      unfold isBE in *. rewrite <-HlookupsEq; trivial. intro. subst blockB. rewrite HlookupStarts in HblockBIsBE.
      congruence.
    }

    assert(forall block, isBE block s -> addr = CPaddr (block+scoffset)
      -> In block (getAllPaddrBlock startBlock endBlock)).
    {
      intros blockB HblockBIsBE HaddrEq. subst addr. rewrite <-Hrange in *.
      assert(Hres: blockAndSceInSameBlock s0) by intuition. specialize(Hres currentPart). apply Hres; trivial.
      unfold isBE in *. rewrite <-HlookupsEq; trivial. intro. subst blockB. rewrite HlookupStarts in HblockBIsBE.
      congruence.
    }
    intuition.
  }

  assert(forall oldPart, In oldPart (getPartitions blockStartAddr s0)
    -> oldPart <> blockStartAddr
    -> exists block, In oldPart (getAllPaddrAux [block] s)
        /\ In block (getMappedBlocks currentPart s)
        /\ sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s).
  {
    intros oldPart HoldIsSubP HbeqOldStart. assert(isPDT oldPart s0).
    {
      apply IL.partitionsArePDT; only 1-3: intuition. unfold getPartitions in *.
      pose proof (getPartitionsAuxExtWithMidpoint (maxAddr+2) (maxAddr+2) oldPart multiplexer blockStartAddr s0
        HoldIsSubP HstartIsParts0) as Htrans.
      replace (getPartitionsAux (maxAddr+2) multiplexer s0) with
        (getPartitionsAux (maxAddr+2+(maxAddr+2)) multiplexer s0); trivial.
      apply getPartitionsEndAny; only 1: lia.
      assert(HnoDup: NoDup (getPartitionsAux (maxAddr + 2) multiplexer s0)) by intuition.
      apply IL.PaddrListBoundedLength in HnoDup. lia.
    }
    assert(Hress0: exists block, In oldPart (getAllPaddrAux [block] s0)
        /\ In block (getMappedBlocks currentPart s0)
        /\ sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s0).
    {
      assert(HoldMapped: In oldPart (getMappedPaddr currentPart s0)).
      {
        assert(verticalSharing s0) by assumption. specialize(HVSs0 currentPart blockStartAddr).
        apply HVSs0; trivial. apply partsAreUsed; trivial; intuition.
      }
      apply IL.mappedAddrIsInMappedBlock in HoldMapped as Hblock.
      destruct Hblock as [block (HblockMapped & HoldInBlock)]. exists block. split; trivial. split; trivial.
      assert(HoldInChild: exists child, In child (getChildren blockStartAddr s0)
        /\ In oldPart (getPartitions child s0)).
      {
        unfold getPartitions in *. replace (maxAddr+2) with (S (maxAddr+1)) in HoldIsSubP; only 2: lia.
        simpl in HoldIsSubP. destruct HoldIsSubP as [Hcontra | HoldIsSubP]; only 1: (exfalso; congruence).
        induction (getChildren blockStartAddr s0); simpl in HoldIsSubP; simpl; only 1: (exfalso; congruence).
        apply in_app_or in HoldIsSubP. destruct HoldIsSubP as [HoldIsSubA | HoldIsSubP].
        - exists a. split; auto. replace (maxAddr+2) with ((maxAddr+1)+1); only 2: lia.
          apply getPartitionsAuxExt; assumption.
        - specialize(IHl HoldIsSubP). destruct IHl as [child (HchildIn & HoldIsSubChild)]. exists child. split; auto.
      }
      destruct HoldInChild as [child (HchildIsChild & HoldIsSubChild)].
      assert(HoldMappedStart: In oldPart (getMappedPaddr blockStartAddr s0)).
      {
        assert(verticalSharing s0) by assumption. specialize(HVSs0 blockStartAddr child).
        apply HVSs0; trivial. apply partsAreUsed; trivial; only 1-3: intuition.
        assert(HchildIsSubP: In child (getPartitions blockStartAddr s0)).
        {
          unfold getPartitions. replace (maxAddr+2) with (S (maxAddr+1)); only 2: lia. simpl. right. clear HVSs0.
          induction (getChildren blockStartAddr s0); simpl; simpl in HchildIsChild; only 1: congruence.
          apply in_or_app. destruct HchildIsChild as [Heq | HchildIsChild]; auto. subst a. left.
          replace (maxAddr+1) with (S maxAddr); only 2: lia. simpl. auto.
        }
        pose proof (getPartitionsAuxExtWithMidpoint (maxAddr+2) (maxAddr+2) child multiplexer blockStartAddr s0
          HchildIsSubP HstartIsParts0). unfold getPartitions.
        replace (getPartitionsAux (maxAddr+2) multiplexer s0) with
          (getPartitionsAux (maxAddr+2+(maxAddr+2)) multiplexer s0); trivial.
        apply getPartitionsEndAny; only 1: lia.
        assert(HnoDup: NoDup (getPartitionsAux (maxAddr + 2) multiplexer s0)) by intuition.
        apply IL.PaddrListBoundedLength in HnoDup. lia.
      }
      assert(HblockIsBE: isBE block s0).
      {
        unfold isBE. apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)].
        rewrite Hlookup. trivial.
      }
      assert(HPDchildB: exists currChild, sh1entryPDchild (CPaddr (block+sh1offset)) currChild s0).
      {
        assert(Hsh1: wellFormedFstShadowIfBlockEntry s0) by intuition.
        apply Hsh1 in HblockIsBE. unfold isSHE in *. unfold sh1entryPDchild.
        destruct (lookup (CPaddr (block + sh1offset)) (memory s0) beqAddr); only 2: (exfalso; congruence).
        destruct v; only 1,3-5: (exfalso; congruence). exists (PDchild s1). reflexivity.
      }
      destruct HPDchildB as [currChild HPDchildB]. assert(HbeqCChildNull: currChild <> nullAddr).
      {
        intro. subst currChild. assert(HnotShared: noChildImpliesAddressesNotShared s0) by intuition.
        unfold isPDT in *.
        destruct (lookup currentPart (memory s0) beqAddr) eqn:HlookupCurr; try(exfalso; congruence).
        destruct v; try(exfalso; congruence).
        assert(HeqTriv: CPaddr (block+sh1offset) = CPaddr (block+sh1offset)) by reflexivity.
        specialize(HnotShared currentPart p0 block (CPaddr (block+sh1offset)) HcurrIsParts0 HlookupCurr HblockMapped
          HeqTriv HPDchildB blockStartAddr oldPart HstartIsChilds0 HoldInBlock). congruence.
      }
      assert(HPDflagB: sh1entryPDflag (CPaddr (block+sh1offset)) false s0).
      {
        assert(HPDflagB: exists f, sh1entryPDflag (CPaddr (block+sh1offset)) f s0).
        {
          unfold sh1entryPDflag. unfold sh1entryPDchild in *.
          destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); only 2: (exfalso; congruence).
          destruct v; try(exfalso; congruence). exists (PDflag s1). reflexivity.
        }
        destruct HPDflagB as [f HPDflagB]. destruct f; trivial. exfalso.
        assert(HnoChild: PDflagMeansNoChild s0) by intuition. specialize(HnoChild block HblockIsBE HPDflagB).
        unfold sh1entryPDchild in *.
        destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); try(congruence).
        destruct v; congruence.
      }
      assert(Hstart: exists startaddr, bentryStartAddr block startaddr s0).
      {
        unfold bentryStartAddr. apply IL.mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & _)]. rewrite Hlookup. exists (startAddr (blockrange bentry)).
        reflexivity.
      }
      destruct Hstart as [startaddr Hstart].
      assert(Hloc: exists blockChild, sh1entryInChildLocationWeak (CPaddr (block+sh1offset)) blockChild s0).
      {
        unfold sh1entryInChildLocationWeak. unfold sh1entryPDchild in *.
        destruct (lookup (CPaddr (block+sh1offset)) (memory s0) beqAddr); only 2: (exfalso; congruence).
        destruct v; try(exfalso; congruence). exists (inChildLocation s1). reflexivity.
      }
      destruct Hloc as [blockChild Hloc]. assert(HbeqLocNull: blockChild <> nullAddr).
      {
        intro. subst blockChild. assert(HnotShared: sharedBlockNoPDflagNoLocIsKern s0) by intuition.
        specialize(HnotShared currentPart block currChild startaddr HcurrIsParts0 HblockMapped HPDchildB
          HbeqCChildNull HPDflagB Hloc Hstart). destruct HnotShared as (_ & HnotShared & _).
        specialize(HnotShared oldPart blockStartAddr HoldInBlock HstartIsChilds0). congruence.
      }
      assert(Hsh1: sh1entryAddr block (CPaddr (block+sh1offset)) s0).
      {
        unfold sh1entryAddr. apply IL.mappedBlockIsBE in HblockMapped.
        destruct HblockMapped as [bentry (Hlookup & _)]. rewrite Hlookup. reflexivity.
      }
      assert(HoldMappedChild: In oldPart (getMappedPaddr currChild s0)).
      {
        assert(Hres: sharedBlocksAdressesAreAllMappedInChild s0) by intuition.
        specialize(Hres currentPart block (CPaddr (block+sh1offset)) blockChild currChild HcurrIsParts0 HblockMapped
          Hsh1 HPDchildB Hloc HbeqCChildNull HbeqLocNull oldPart HoldInBlock). assumption.
      }
      assert(currChild = blockStartAddr).
      {
        destruct (beqAddr currChild blockStartAddr) eqn:HbeqChildren; try(rewrite beqAddrTrue; assumption). exfalso.
        rewrite <-beqAddrFalse in HbeqChildren. assert(HcChildIsChild: pdchildIsPDT s0) by intuition.
        specialize(HcChildIsChild currentPart block (CPaddr (block+sh1offset)) currChild HcurrIsParts0 HblockMapped
          Hsh1 HPDchildB HbeqCChildNull). assert(HoldUsed: In oldPart (getUsedPaddr currChild s0)).
        { unfold getUsedPaddr. apply in_or_app. auto. }
        specialize(HPIs0 currentPart currChild blockStartAddr HcurrIsParts0 HcChildIsChild HstartIsChilds0
          HbeqChildren oldPart HoldUsed). contradict HPIs0. unfold getUsedPaddr. apply in_or_app. auto.
      }
      subst currChild. assumption.
    }
    rewrite HgetMappedBEq; trivial. destruct Hress0 as [block (HoldInBlock & HblockMapped & HPDchildB)]. exists block.
    simpl. assert(block <> blockStartAddr).
    {
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)]. unfold isPDT in *.
      intro. subst block. rewrite Hlookup in *. congruence.
    }
    unfold sh1entryPDchild in *. assert(CPaddr (block+sh1offset) <> blockStartAddr).
    {
      intro Hcontra. rewrite Hcontra in *. unfold isPDT in *.
      destruct (lookup blockStartAddr (memory s0) beqAddr); try(congruence). destruct v; congruence.
    }
    rewrite HlookupsEq; trivial. rewrite HlookupsEq; auto.
  }

  assert(HstartIsPart: In blockStartAddr (getPartitions multiplexer s)).
  {
    rewrite <-HgetChildrenEqNotStart in HstartIsChilds0; trivial.
    apply IL.childrenPartitionInPartitionList with currentPart; assumption.
  }

  assert(HgetPartsImplGen: forall part partBase, In part (getPartitions partBase s)
    -> In part (getPartitions partBase s0)).
  { intros part partBase. apply getPartitionsImplRemoveAddr with blockStartAddr; trivial. }

  assert(forall part, In part (getPartitions multiplexer s) -> In blockStartAddr (getChildren part s)
    -> part = currentPart).
  {
    intros part HpartIsPart HstartIsChild. apply HgetPartsImpl in HpartIsPart.
    apply HgetChildrenImpl in HstartIsChild. assert(HisParent: isParent s0) by intuition.
    specialize(HisParent blockStartAddr part HpartIsPart HstartIsChild). assert(HisParentB: isParent s0) by intuition.
    specialize(HisParentB blockStartAddr currentPart HcurrIsPart HstartIsChilds0). unfold pdentryParent in *.
    rewrite HlookupStart in *. rewrite <-HisParentB in *. assumption.
  }

  assert(forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
    -> In block (getMappedBlocks part s) -> sh1entryPDchild (CPaddr (block + sh1offset)) child s
    -> child <> blockStartAddr).
  {
    intros part block child HbeqPartCurr HpartIsPart HblockMapped HPDchildB Hcontra. subst child.
    assert(HstartIsChild: pdchildIsPDT s) by assumption.
    assert(Hsh1: sh1entryAddr block (CPaddr (block + sh1offset)) s).
    {
      apply IL.mappedBlockIsBE in HblockMapped. destruct HblockMapped as [bentry (Hlookup & _)]. unfold sh1entryAddr.
      rewrite Hlookup. reflexivity.
    }
    specialize(HstartIsChild part block (CPaddr (block + sh1offset)) blockStartAddr HpartIsPart HblockMapped Hsh1
      HPDchildB HbeqStartNull). apply HgetChildrenImpl in HstartIsChild. contradict HbeqPartCurr.
    apply HgetPartsImpl in HpartIsPart. apply uniqueParent with blockStartAddr s0; trivial; intuition.
  }

  instantiate(1 := fun s => blockToDeleteInCurrPartAddr = idPDchildToDelete
    /\ isBE blockToDeleteInCurrPartAddr s
    /\ bentryStartAddr blockToDeleteInCurrPartAddr blockStartAddr s
    /\ bentryEndAddr blockToDeleteInCurrPartAddr blockEndAddr s
    /\ bentryPFlag blockToDeleteInCurrPartAddr true s
    /\ bentryAFlag blockToDeleteInCurrPartAddr false s
    /\ In blockToDeleteInCurrPartAddr (getMappedBlocks currentPart s)
    /\ sh1entryPDchild (CPaddr (blockToDeleteInCurrPartAddr + sh1offset)) nullAddr s
    /\ sh1entryPDflag (CPaddr (blockToDeleteInCurrPartAddr + sh1offset)) true s
    /\ currentPart = currentPartition s
    /\ In currentPart (getPartitions multiplexer s)
    /\ lookup blockStartAddr (memory s) beqAddr = None
    /\ In blockStartAddr (getPartitions multiplexer s)
    /\ blockToDeleteInCurrPartAddr <> blockStartAddr
    /\ blockToDeleteInCurrPartAddr <> nullAddr
    /\ CPaddr (blockToDeleteInCurrPartAddr + sh1offset) <> blockStartAddr

    /\ nullAddrExists s /\ wellFormedFstShadowIfBlockEntry s
    /\ (*partial PDTIfPDFlag*)
        (forall idPDchild sh1entryaddr part, idPDchild <> blockToDeleteInCurrPartAddr
          -> In part (getPartitions multiplexer s)
          -> In idPDchild (getMappedBlocks part s)
          -> true = checkChild idPDchild s sh1entryaddr /\ sh1entryAddr idPDchild sh1entryaddr s
          -> bentryAFlag idPDchild false s /\ bentryPFlag idPDchild true s
              /\ (exists startaddr, bentryStartAddr idPDchild startaddr s /\ entryPDT idPDchild startaddr s))
    /\ AccessibleNoPDFlag s /\ FirstFreeSlotPointerIsBEAndFreeSlot s /\ multiplexerIsPDT s
    /\ currentPartitionInPartitionsList s /\ wellFormedShadowCutIfBlockEntry s /\ BlocksRangeFromKernelStartIsBE s
    /\ KernelStructureStartFromBlockEntryAddrIsKS s /\ sh1InChildLocationIsBE s /\ StructurePointerIsKS s
    /\ NextKSIsKS s /\ NextKSOffsetIsPADDR s /\ NoDupInFreeSlotsList s /\ freeSlotsListIsFreeSlot s
    /\ DisjointFreeSlotsLists s /\ inclFreeSlotsBlockEntries s /\ DisjointKSEntries s /\ noDupPartitionTree s
    /\ (*partial isParent*)
        (forall partition pdparent,
          partition <> blockStartAddr
          -> In pdparent (getPartitions multiplexer s)
          -> In partition (getChildren pdparent s) -> pdentryParent partition pdparent s)
    /\ isChild s /\ noDupKSEntriesList s /\ wellFormedBlock s
    /\ NbFreeSlotsISNbFreeSlotsInList s /\ maxNbPrepareIsMaxNbKernels s
    /\ blockInChildHasAtLeastEquivalentBlockInParent s /\ partitionTreeIsTree s
    /\ nextKernelIsValid s /\ noDupListOfKerns s /\ MPUsizeIsBelowMax s /\ originIsParentBlocksStart s
    /\ nextImpliesBlockWasCut s /\ blocksAddressesTypes s /\ notPDTIfNotPDflag s /\ nextKernAddrIsInSameBlock s
    /\ PDflagMeansNoChild s /\ nbPrepareIsNbKern s /\ pdchildIsPDT s /\ childBlockNullIfChildNull s
    /\ accessibleBlocksArePresent s /\ sharedBlockIsPresent s
    /\ (*partial sharedBlockNoPDflagNoLocIsKern*)
        (forall part block child startaddr,
          child <> blockStartAddr
          -> In part (getPartitions multiplexer s)
          -> In block (getMappedBlocks part s)
          -> sh1entryPDchild (CPaddr (block + sh1offset)) child s
          -> child <> nullAddr
          -> sh1entryPDflag (CPaddr (block + sh1offset)) false s
          -> sh1entryInChildLocationWeak (CPaddr (block + sh1offset)) nullAddr s
          -> bentryStartAddr block startaddr s
          -> In startaddr (getConfigBlocks child s)
              /\ (forall addr child2, In addr (getAllPaddrAux [block] s)
                    -> In child2 (getChildren part s)
                    -> ~In addr (getMappedPaddr child2 s))
              /\ (forall addr endaddr part2: paddr, bentryEndAddr block endaddr s
                    -> In part2 (getPartitions multiplexer s)
                    -> startaddr + Constants.kernelStructureTotalLength <= addr
                    -> addr < endaddr -> ~In addr (getConfigPaddr part2 s)))
    /\ partitionNotAutoMapped s /\ configAddrNotMappedInChild s /\ fullKernelIsInOneBlock s
    /\ (*partial sharedBlocksAdressesAreAllMappedInChild*)
        (forall partition block sh1entryaddr blockChild idchild,
          idchild <> blockStartAddr
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> sh1entryAddr block sh1entryaddr s
          -> sh1entryPDchild sh1entryaddr idchild s
          -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
          -> idchild <> nullAddr
          -> blockChild <> nullAddr
          -> forall addr, In addr (getAllPaddrAux [block] s) -> In addr (getMappedPaddr idchild s))
    /\ kernInSameBlock s /\ blockAndSh1InSameBlock s /\ blockAndSceInSameBlock s
    /\ noDupMappedPaddrList s /\ accessibleParentPaddrIsAccessibleIntoChild s
    /\ sharedBlockPointsToChild s /\ adressesRangePreservedIfOriginAndNextOk s /\ childsBlocksPropsInParent s
    /\ noChildImpliesAddressesNotShared s /\ kernelsAreNotAccessible s /\ blockAndNextAreSideBySide s
    /\ (*partial kernelIsSomePartsConfig s*)
        (forall kernel, isKS kernel s
          -> (forall block, In block (filterOptionPaddr (getKSEntries currentPart s))
                -> sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s
                -> ~In kernel (getAllPaddrAux [block] s))
          -> exists part pdentry, In part (getPartitions multiplexer s)
              /\ lookup part (memory s) beqAddr = Some (PDT pdentry)
              /\ In kernel (completeListOfKernels (structure pdentry) s))
    /\ PDTisNoConfigInChild s /\ PDTisNoConfigInPart s /\ usedPaddrAreShared s /\ indexIsDistFromKern s
    /\ blockAndNextInSameBlock s
    /\ parentBlocksBoundsIfNoNext s
    /\ (*partial childLocMappedInChild*)
        (forall partition block sh1entryaddr blockChild idchild startaddr,
          idchild <> blockStartAddr
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> sh1entryAddr block sh1entryaddr s
          -> sh1entryPDchild sh1entryaddr idchild s
          -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
          -> idchild <> nullAddr
          -> bentryStartAddr block startaddr s
          -> ~ isKS startaddr s
          -> blockChild <> nullAddr
              /\ In blockChild (getMappedBlocks idchild s) /\ bentryStartAddr blockChild startaddr s)
    /\ (*partial childLocHasSameStart*)
        (forall partition block sh1entryaddr blockChild idchild,
          idchild <> blockStartAddr
          -> In partition (getPartitions multiplexer s)
          -> In block (getMappedBlocks partition s)
          -> sh1entryAddr block sh1entryaddr s
          -> sh1entryPDchild sh1entryaddr idchild s
          -> sh1entryInChildLocationWeak sh1entryaddr blockChild s
          -> idchild <> nullAddr
          -> blockChild <> nullAddr
          -> (forall startaddr, bentryStartAddr block startaddr s -> bentryStartAddr blockChild startaddr s)
                /\ In blockChild (getMappedBlocks idchild s))
    /\ partitionsIsolation s /\ kernelDataIsolation s /\ verticalSharing s
    /\ (*more info*)
        (forall block startBlock endBlock, In block (getMappedBlocks currentPart s)
          -> sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s
          -> bentryStartAddr block startBlock s
          -> bentryEndAddr block endBlock s
          -> (forall addr, In addr (getAllPaddrBlock startBlock endBlock)
              -> ~In addr (getPartitions multiplexer s)
                  /\ (forall part, In part (getPartitions multiplexer s)
                      -> ~In addr (filterOptionPaddr (getKSEntries part s))
                          /\ ~In addr (getConfigPaddr part s))
                  /\ (forall child, In child (getChildren currentPart s) -> ~ In addr (getMappedPaddr child s))
                  /\ (isBE addr s -> addr + scoffset < endBlock)
                  /\ (isKS addr s -> addr + nextoffset < endBlock)
                  /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+sh1offset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ (forall blockB, isBE blockB s -> addr = CPaddr (blockB+scoffset)
                        -> In blockB (getAllPaddrBlock startBlock endBlock))
                  /\ addr <> nullAddr))
    /\ (forall part, In part (getPartitions multiplexer s) -> In blockStartAddr (getChildren part s)
          -> part = currentPart)
    /\ (forall part block child, part <> currentPart -> In part (getPartitions multiplexer s)
          -> In block (getMappedBlocks part s) -> sh1entryPDchild (CPaddr (block + sh1offset)) child s
          -> child <> blockStartAddr)
    /\ (exists s0, consistency s0
        /\ (forall addr, addr <> blockStartAddr -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
        /\ In blockStartAddr (getPartitions multiplexer s0)
        (*TODO will probably need to add more links between s and s0*)
        /\ (*partial parentOfPartitionIsPartition*)
            (forall partition entry,
              lookup partition (memory s) beqAddr = Some (PDT entry)
              -> (~ In (parent entry) (getPartitions blockStartAddr s0)
                   -> partition <> constantRootPartM
                   -> (exists parentEntry, lookup (parent entry) (memory s) beqAddr = Some (PDT parentEntry))
                        /\ In (parent entry) (getPartitions multiplexer s))
                  /\ (partition = constantRootPartM -> parent entry = nullAddr) /\ parent entry <> partition)
        /\ (forall oldPart, In oldPart (getPartitions blockStartAddr s0)
              -> oldPart <> blockStartAddr
              -> exists block, In oldPart (getAllPaddrAux [block] s)
                  /\ In block (getMappedBlocks currentPart s)
                  /\ sh1entryPDchild (CPaddr (block+sh1offset)) blockStartAddr s)
        /\ (forall oldPart, In oldPart (getPartitions blockStartAddr s0)
              -> oldPart <> blockStartAddr
              -> ~In oldPart (getPartitions multiplexer s))
        /\ (forall part partBase, In part (getPartitions partBase s)
              -> In part (getPartitions partBase s0)))).

  unfold isBE in *. unfold bentryStartAddr in *. unfold bentryEndAddr in *. unfold bentryPFlag in *.
  unfold bentryAFlag in *. rewrite <-HlookupBTDEq in *. unfold sh1entryPDflag in *. unfold sh1entryPDchild in *.
  rewrite <-HlookupBTDSh1Eq in *. rewrite <-HgetMappedBEq in HBTDMapped; trivial. rewrite <-HcurrEq in *.
  assert(In currentPart (getPartitions multiplexer s)).
  {
    apply HgetPartsImplRev in HcurrIsParts0. destruct HcurrIsParts0; try(exfalso; congruence). assumption.
  }
  intuition. exists s0. unfold consistency; unfold consistency1; unfold consistency2; intuition.
}
intro currKernelStructureStart. eapply bindRev.
{ (** Internal.deleteSharedBlocksRec **)
  eapply weaken. apply deleteSharedBlocksRec. intros s Hprops.
  destruct Hprops as ((HBTDEq & HBTDIsBE & HstartBTD & HendBTD & HPflagBTD & HAflagBTD & HBTDMapped & HPDchildBTD &
    HPDflagBTD & Hcurr & HcurrIsPart & HlookupStart & HstartIsPart & HbeqBTDStart & HbeqBTDNull & HbeqBTDSh1Start &
    Hnull & Hsh1IsSHE & HPDTIfPDFlagPartial & HaccessNoPD & HfirstFreeIsFree & HmultIsPDT & HcurrentIsPart & HsceIsSCE
    & HblocksAreBE & HinitBlockIsKS & HlocIsBE & HstructIsKS & HnextIsKS & HnextAIsPADDR & HnoDupFree & HfreeAreFree &
    HdisjointFree & HinclFreeKS & HdijointKS & HnoDupTree & HisParentPartial & HisChild & HnoDupKS & Hwell & HlenFree
    & HlenKernList & HequivParent & Htree & HnextProps & HnoDupKernList & HlenMPU & HoriginIsStart & HnextCut & Htypes
    & HnoPDfNotPDT & HnextInBlockMeansStart & HPDfNoChild & HlenComplKL & HPDchildIsPart & HPDchildNull &
    HaccessIsPres & HsharedIsPres & HsharedKernPartial & HpartNotMapped & HconfigNotMappedChild & HnextAInSameBlock &
    HsharedIsMappedCPartial & HkernInSameBlock & Hsh1InSameBlock & HsceInSameBlock & HnoDupPaddr & HaccessChild &
    Hshared & Hrange & HchildBProps & HnoChild & HkernNotAcc & HnextSide & HkernsAreConfigPartial & HPDTNoConfigChild
    & HPDTNoConfig & HusedAreShared & HidxIsDist & HnextInSameBlock & HboundsNoNext & HlocMappedCPartial &
    HlocHasSameStart & HPI & HKDI & HVS & HpropsAddrsToRemove & HuniqueParent & HstartNotInElse & Hprops0) & Hstruct).
  instantiate(1:=blockToDeleteInCurrPartAddr).
  assert(deleteProps s s currentPart blockToDeleteInCurrPartAddr blockStartAddr).
  {
    unfold deleteProps. repeat (split; trivial).
    - intros part block sh1entryaddr sh1entry _. specialize(HlocIsBE part block sh1entryaddr sh1entry). assumption.
    - intros kernel nextKSaddr nextKS _. specialize(HnextIsKS kernel nextKSaddr nextKS). assumption.
    - destruct Hprops0 as [s0 (Hconsist0 & HlookupsEq & HstartIsParts0 & HparentOfPartPartial &
        HexceptPartsAreChildren & HexceptAreNoParts & HpartsImpl)]. exists (getPartitions blockStartAddr s0).
      split; trivial. intros oldPart HoldIsSubStart desc HdescIsSubOld HbeqDescStart.
      apply HexceptAreNoParts; trivial. apply HpartsImpl in HdescIsSubOld.
      unfold getPartitions in *. assert(Heq: getPartitionsAux ((maxAddr+2)+(maxAddr+2)) blockStartAddr s0
        = getPartitionsAux (maxAddr+2) blockStartAddr s0).
      {
        assert(HnoDupSub: NoDup (getPartitions blockStartAddr s0)).
        {
          apply noDupPartitionTreeRec; trivial; unfold consistency in *; unfold consistency1 in *; intuition.
        }
        apply IL.lengthNoDupPartitions in HnoDupSub. unfold getPartitions in *. apply getPartitionsEndAny; lia.
      }
      rewrite <-Heq. apply getPartitionsAuxExtWithMidpoint with oldPart; assumption.
  }
  assert(exists pdentryCurr, lookup currentPart (memory s) beqAddr = Some (PDT pdentryCurr)
    /\ currKernelStructureStart = structure pdentryCurr).
  {
    unfold pdentryStructurePointer in *. destruct (lookup currentPart (memory s) beqAddr); try(exfalso; congruence).
    destruct v; try(exfalso; congruence). exists p. auto.
  }
  instantiate(1:= fun _ => True). repeat (split; trivial).
}
intro. eapply bindRev.
{ (** MAL.writeSh1EntryFromBlockEntryAddr **)
  eapply weaken. apply writeSh1EntryFromBlockEntryAddrLight. intros s Hprops. simpl. split. apply Hprops.
  destruct Hprops as [pdentryCurr (HlookupStart & HBTDMapped & HPDflagBTD & Hstart & HstartIsPart & HcurrIsPart &
    HlookupCurr & HstartNotPDchild & HstartNotInElse & [s0 (_ & Hcons & Hprops)])]. unfold bentryStartAddr in *.
  destruct (lookup blockToDeleteInCurrPartAddr (memory s) beqAddr) eqn:HlookupBTD; try(exfalso; congruence).
  destruct v; try(exfalso; congruence). exists b.
  assert(HBTDIsBE: isBE blockToDeleteInCurrPartAddr s) by (unfold isBE; rewrite HlookupBTD; trivial).
  assert(Hblkidx: bentryBlockIndex blockToDeleteInCurrPartAddr (blockindex b) s).
  { unfold bentryBlockIndex. rewrite HlookupBTD. reflexivity. }
  assert(HkernIsKS: KernelStructureStartFromBlockEntryAddrIsKS s) by (unfold deleteProps in *; intuition).
  specialize(HkernIsKS blockToDeleteInCurrPartAddr (blockindex b) HBTDIsBE Hblkidx).
  assert(blockToDeleteInCurrPartAddr >= blockindex b).
  {
    unfold isKS in *. destruct (Nat.leb (blockindex b) blockToDeleteInCurrPartAddr) eqn:Hleb.
    - apply PeanoNat.Nat.leb_le in Hleb. lia.
    - apply PeanoNat.Nat.leb_gt in Hleb. assert(Heq: blockToDeleteInCurrPartAddr - blockindex b = 0) by lia.
      rewrite Heq in *. fold nullAddr in HkernIsKS. exfalso.
      assert(isPADDR nullAddr s) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
      destruct (lookup nullAddr (memory s) beqAddr); try(congruence). destruct v; congruence.
  }
  auto.
  (* set(bentryBTDs := CBlockEntry (read bentryBTD) (write bentryBTD) (exec bentryBTD) (present bentryBTD) true
    (blockindex bentryBTD) (blockrange bentryBTD)).
  fold bentryBTDs in Hs. exists bentryBTDs. rewrite Hs at 1. simpl. rewrite IL.beqAddrTrue.
  assert(HkernIsKS: KernelStructureStartFromBlockEntryAddrIsKS s1) by (unfold deleteProps in *; intuition).
  assert(HBTDIsBE: isBE blockToDeleteInCurrPartAddr s1) by (unfold isBE; rewrite HlookupBTDs1; trivial).
  unfold CBlockEntry in bentryBTDs. assert(blockindex bentryBTD < kernelStructureEntriesNb) by (apply Hidx).
  destruct (Compare_dec.lt_dec (blockindex bentryBTD) kernelStructureEntriesNb); try(lia).
  assert(Hblkidx: bentryBlockIndex blockToDeleteInCurrPartAddr (blockindex bentryBTDs) s1).
  { unfold bentryBlockIndex. rewrite HlookupBTDs1. reflexivity. }
  specialize(HkernIsKS blockToDeleteInCurrPartAddr (blockindex bentryBTDs) HBTDIsBE Hblkidx).
  assert(blockToDeleteInCurrPartAddr >= blockindex bentryBTDs).
  {
    unfold isKS in *. destruct (Nat.leb (blockindex bentryBTDs) blockToDeleteInCurrPartAddr) eqn:Hleb.
    - apply PeanoNat.Nat.leb_le in Hleb. lia.
    - apply PeanoNat.Nat.leb_gt in Hleb. assert(Heq: blockToDeleteInCurrPartAddr - blockindex bentryBTDs = 0) by lia.
      rewrite Heq in *. fold nullAddr in HkernIsKS. exfalso.
      assert(isPADDR nullAddr s1) by (unfold deleteProps in *; intuition). unfold isPADDR in *.
      destruct (lookup nullAddr (memory s1) beqAddr); try(congruence). destruct v; congruence.
  }
  split; try(split); trivial. unfold isKS in *. rewrite Hs. cbn -[bentryBTDs].
  destruct (beqAddr blockToDeleteInCurrPartAddr (CPaddr (blockToDeleteInCurrPartAddr-blockindex bentryBTDs)))
    eqn:HbeqBTDKern.
  - (*false, but does not matter*)
    rewrite <-beqAddrTrue in HbeqBTDKern. rewrite <-HbeqBTDKern in *. rewrite HlookupBTDs1 in *. auto.
  - rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto. *)
}
intro. eapply bindRev.
{ (** MAL.writeBlockAccessibleFromBlockEntryAddr **)
  eapply weaken. apply writeBlockAccessibleFromBlockEntryAddr. intros s Hprops. simpl.
  destruct Hprops as [s1 (Hs & [pdentryCurr (HlookupStart & HBTDMapped & HPDflagBTD & Hprops)])].
  assert(HlookupBTD: exists bentryBTD, lookup blockToDeleteInCurrPartAddr (memory s1) beqAddr = Some (BE bentryBTD)).
  {
    apply IL.mappedBlockIsBE in HBTDMapped.  destruct HBTDMapped as [bentry (Hlookup & _)]. exists bentry. assumption.
  }
  destruct HlookupBTD as [bentryBTD HlookupBTD]. exists bentryBTD.
  assert(lookup blockToDeleteInCurrPartAddr (memory s) beqAddr = Some (BE bentryBTD)).
  {
    rewrite Hs. simpl.
    destruct (beqAddr (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) blockToDeleteInCurrPartAddr) eqn:HbeqSh1BTD.
    {
      exfalso. rewrite <-beqAddrTrue in HbeqSh1BTD. rewrite HbeqSh1BTD in *. unfold sh1entryPDflag in *.
      rewrite HlookupBTD in *. congruence.
    }
    rewrite <-beqAddrFalse in *. rewrite removeDupIdentity; auto.
  }
  instantiate(1:= fun _ s =>
    exists s2 s1 bentryBTD pdentryCurr,
      s = {|
            currentPartition := currentPartition s2;
            memory :=
              add blockToDeleteInCurrPartAddr
                (BE
                   (CBlockEntry (read bentryBTD) (write bentryBTD) (exec bentryBTD) (present bentryBTD) true
                      (blockindex bentryBTD) (blockrange bentryBTD)))
                (memory s2) beqAddr
          |}
      /\ s2 = {|
                currentPartition := currentPartition s1;
                memory :=
                  add (CPaddr (blockToDeleteInCurrPartAddr + sh1offset))
                    (SHE {| PDchild := nullAddr; PDflag := false; inChildLocation := nullAddr |})
                    (memory s1) beqAddr
              |}
      /\ lookup blockToDeleteInCurrPartAddr (memory s2) beqAddr = Some (BE bentryBTD)
      /\ lookup blockToDeleteInCurrPartAddr (memory s1) beqAddr = Some (BE bentryBTD)
      /\ lookup blockStartAddr (memory s1) beqAddr = None
      /\ In blockToDeleteInCurrPartAddr (getMappedBlocks currentPart s1)
      /\ sh1entryPDflag (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) true s1
      /\ bentryStartAddr blockToDeleteInCurrPartAddr blockStartAddr s1
      /\ In blockStartAddr (getPartitions multiplexer s1)
      /\ In currentPart (getPartitions multiplexer s1)
      /\ lookup currentPart (memory s1) beqAddr = Some (PDT pdentryCurr)
      /\ (forall kernBis idx,
           In kernBis (completeListOfKernels (structure pdentryCurr) s1)
           -> idx < kernelStructureEntriesNb
           -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockStartAddr s1)
      /\ (forall part block child,
           part <> currentPart
           -> In part (getPartitions multiplexer s1)
           -> In block (getMappedBlocks part s1)
           -> sh1entryPDchild (CPaddr (block + sh1offset)) child s1 -> child <> blockStartAddr)
      /\ (exists s0, True
           /\ deleteProps s0 s1 currentPart blockToDeleteInCurrPartAddr blockStartAddr
           /\ (forall sh1entryaddr child,
                child <> nullAddr -> sh1entryPDchild sh1entryaddr child s1 -> sh1entryPDchild sh1entryaddr child s0)
           /\ (forall kernBis idx, In kernBis (completeListOfKernels (structure pdentryCurr) s1)
                -> idx < kernelStructureEntriesNb
                -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockStartAddr s1)
           /\ (forall kernBis idx addr, In kernBis (completeListOfKernels (structure pdentryCurr) s1)
                -> idx < kernelStructureEntriesNb
                -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockStartAddr s0
                -> In addr (getAllPaddrAux [CPaddr (kernBis+idx)] s1) -> lookup addr (memory s1) beqAddr = None))).
  (* instantiate(1:= fun _ s =>
    exists s1 bentryBTD pdentryCurr,
      s = {|
            currentPartition := currentPartition s1;
            memory :=
              add blockToDeleteInCurrPartAddr
                (BE
                   (CBlockEntry (read bentryBTD) (write bentryBTD) (exec bentryBTD) (present bentryBTD) true
                      (blockindex bentryBTD) (blockrange bentryBTD)))
                (memory s1) beqAddr
          |}
      /\ lookup blockToDeleteInCurrPartAddr (memory s1) beqAddr = Some (BE bentryBTD)
      /\ lookup blockStartAddr (memory s1) beqAddr = None
      /\ In blockToDeleteInCurrPartAddr (getMappedBlocks currentPart s1)
      /\ bentryStartAddr blockToDeleteInCurrPartAddr blockStartAddr s1
      /\ In blockStartAddr (getPartitions multiplexer s1)
      /\ In currentPart (getPartitions multiplexer s1)
      /\ lookup currentPart (memory s1) beqAddr = Some (PDT pdentryCurr)
      /\ (forall kernBis idx,
           In kernBis (completeListOfKernels (structure pdentryCurr) s1)
           -> idx < kernelStructureEntriesNb
           -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockStartAddr s1)
      /\ (forall part block child,
           part <> currentPart
           -> In part (getPartitions multiplexer s1)
           -> In block (getMappedBlocks part s1)
           -> sh1entryPDchild (CPaddr (block + sh1offset)) child s1 -> child <> blockStartAddr)
      /\ (exists s0, True
           /\ deleteProps s0 s1 currentPart blockToDeleteInCurrPartAddr blockStartAddr
           /\ (forall sh1entryaddr child,
                child <> nullAddr -> sh1entryPDchild sh1entryaddr child s1 -> sh1entryPDchild sh1entryaddr child s0)
           /\ (forall kernBis idx, In kernBis (completeListOfKernels (structure pdentryCurr) s1)
                -> idx < kernelStructureEntriesNb
                -> ~sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockStartAddr s1)
           /\ (forall kernBis idx addr, In kernBis (completeListOfKernels (structure pdentryCurr) s1)
                -> idx < kernelStructureEntriesNb
                -> sh1entryPDchild (CPaddr (CPaddr (kernBis + idx) + sh1offset)) blockStartAddr s0
                -> In addr (getAllPaddrAux [CPaddr (kernBis+idx)] s1) -> lookup addr (memory s1) beqAddr = None))).*)
  split; trivial. exists s. exists s1. exists bentryBTD. exists pdentryCurr. intuition.
}
intro. eapply bindRev.
{ (** Internal.checkBlockCut **)
  eapply weaken. apply checkBlockCut. intros s Hprops.
  destruct Hprops as [s2 [s1 [bentryBTD [pdentryCurr (Hs & Hs2 & HlookupBTDs2 & HlookupBTDs1 & HlookupStarts1 &
    HBTDMappeds1 & HPDflagBTDs1 & Hstarts1 & HstartIsParts1 & HcurrIsParts1 & HlookupCurrs1 & HstartNotPDchilds1 &
    HstartNotInElses1 & [s0 (_ & Hcons & HPDchildImpls1s0 & _ & HremovedAddrs)])]]]].
  assert(HKSAreConfig: forall block, In block (filterOptionPaddr (getKSEntries currentPart s1))
    -> exists kernel idx, In kernel (completeListOfKernels (structure pdentryCurr) s1)
        /\ idx < kernelStructureEntriesNb /\ block = (CPaddr (kernel+idx))).
  {
    assert(Heq: getConfigBlocks currentPart s1 = completeListOfKernels (structure pdentryCurr) s1).
    { apply completeKernListIsConfig; trivial; unfold deleteProps in *; intuition. }
    rewrite <-Heq. intro block. apply KSEntriesAreRangeConfig; trivial; unfold deleteProps in *; intuition.
  }
  assert(HcurrEq: currentPartition s = currentPartition s1) by (rewrite Hs; simpl; rewrite Hs2; reflexivity).
  assert(Hsh1: sh1entryAddr blockToDeleteInCurrPartAddr (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)) s1).
  { unfold sh1entryAddr. rewrite HlookupBTDs1. reflexivity. }
  unfold CBlockEntry in Hs. assert(blockindex bentryBTD < kernelStructureEntriesNb) by (apply Hidx).
  destruct (Compare_dec.lt_dec (blockindex bentryBTD) kernelStructureEntriesNb); try(lia).
  assert(HgetPartsEqs2s1: exists leftList rightList,
    getPartitions multiplexer s1 = leftList ++ [blockStartAddr] ++ rightList
    /\ getPartitions multiplexer s2 = leftList ++ rightList).
  {
    rewrite Hs2. apply getPartitionsEqSHEFalseChange with currentPart sh1entry?; trivial.
    1-2,4-5: unfold deleteProps in *; intuition. (*TODO HERE propagate PDflag = true*)
  }
  assert(HgetPartsEqss2: getPartitions multiplexer s = getPartitions multiplexer s2).
  {
    rewrite Hs2. apply IL.getPartitionsEqBEPDflagNoChangePresentNoChangeStartNoChange with bentryBTD
      (CPaddr (blockToDeleteInCurrPartAddr+sh1offset)); trivial.
    1-2,4-5: unfold deleteProps in *; intuition. (*TODO HERE*)
  }
}
intro isCut. destruct isCut.
- eapply weaken. apply WP.ret. intros s Hprops. simpl.
  
- eapply bindRev.
  { (** Internal.writeAccessibleRec **)
    eapply weaken. apply ?. intros s Hprops.
    
  }
  eapply weaken. apply WP.ret. intros s Hprops. simpl.
  
Qed.
